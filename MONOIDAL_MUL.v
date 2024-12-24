Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONOIDAL_MUL_term_abbrevs.
Require Import INT_POS_spec.
Require Import monoidal_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032070_spec.
Require Import thm1032082_spec.
Require Import thm1032084_spec.
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
Require Import thm17045_spec.
Require Import thm17362_spec.
Require Import thm19018_spec.
Require Import thm19019_spec.
Require Import thm19024_spec.
Require Import thm19025_spec.
Require Import thm19030_spec.
Require Import thm19031_spec.
Require Import thm19158_spec.
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
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm6898643_spec.
Require Import thm6901231_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem6901233 {A : Type'} (op : type1400 A) : term0 A op.
Proof. exact (@lem5712802 A op). Qed.
Lemma lem6901234 {A : Type'} (op : type1400 A) : (term0 A op) = ((@monoidal A op) = (term1 A op)).
Proof. exact (eq_refl (term0 A op)). Qed.
Lemma lem6901237 {A : Type'} (op : type1400 A) : (@monoidal A op) = (term1 A op).
Proof. exact (EQ_MP (@lem6901234 A op) (@lem6901233 A op)). Qed.
Lemma lem6901238 (op : type1606) : (@monoidal nat op) = (term2 op).
Proof. exact (@lem6901237 nat op). Qed.
Lemma lem6901239 : (@monoidal nat Nat.mul) = term3.
Proof. exact (@lem6901238 Nat.mul). Qed.
Lemma lem6901275 : (@neutral nat Nat.mul) = term4.
Proof. exact (EQ_MP (@lem6898643) (@lem6901231)). Qed.
Lemma lem6901276 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem6901277 : term5 = term6.
Proof. exact (MK_COMB (@lem6901276) (@lem6901275)). Qed.
Lemma lem6901278 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6901279 (x : nat) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem6901277) (@lem6901278 x)). Qed.
Lemma lem6901280 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6901281 (x : nat) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem6901280) (@lem6901279 x)). Qed.
Lemma lem6901282 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6901283 (x : nat) : ((term7 x) = x) = ((term8 x) = x).
Proof. exact (MK_COMB (@lem6901281 x) (@lem6901282 x)). Qed.
Lemma lem6901286 : term11 = term12.
Proof. exact (fun_ext (fun x : nat => @lem6901283 x)). Qed.
Lemma lem6901287 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901288 : term13 = term14.
Proof. exact (MK_COMB (@lem6901287) (@lem6901286)). Qed.
Lemma lem6901293 : term15 = term15.
Proof. exact (eq_refl term15). Qed.
Lemma lem6901294 : term16 = term17.
Proof. exact (MK_COMB (@lem6901293) (@lem6901288)). Qed.
Lemma lem6901297 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem6901298 : term3 = term19.
Proof. exact (MK_COMB (@lem6901297) (@lem6901294)). Qed.
Lemma lem6901301 : (@monoidal nat Nat.mul) = term19.
Proof. exact (TRANS (@lem6901239) (@lem6901298)). Qed.
Lemma lem6901302 : term19 = (@monoidal nat Nat.mul).
Proof. exact (SYM (@lem6901301)). Qed.
Lemma lem6901338 (x : nat) : ((term8 x) = x) = ((term8 x) = x).
Proof. exact (eq_refl ((term8 x) = x)). Qed.
Lemma lem6901339 : term12 = term12.
Proof. exact (fun_ext (fun x : nat => @lem6901338 x)). Qed.
Lemma lem6901340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901341 : term14 = term14.
Proof. exact (MK_COMB (@lem6901340) (@lem6901339)). Qed.
Lemma lem6901342 (x : nat) (y : nat) (z : nat) : ((term20 x y z) = (term21 x y z)) = ((term20 x y z) = (term21 x y z)).
Proof. exact (eq_refl ((term20 x y z) = (term21 x y z))). Qed.
Lemma lem6901343 (x : nat) (y : nat) : (term22 x y) = (term22 x y).
Proof. exact (fun_ext (fun z : nat => @lem6901342 x y z)). Qed.
Lemma lem6901344 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901345 (x : nat) (y : nat) : (term23 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem6901344) (@lem6901343 x y)). Qed.
Lemma lem6901346 (x : nat) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : nat => @lem6901345 x y)). Qed.
Lemma lem6901347 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901348 (x : nat) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem6901347) (@lem6901346 x)). Qed.
Lemma lem6901349 : term26 = term26.
Proof. exact (fun_ext (fun x : nat => @lem6901348 x)). Qed.
Lemma lem6901350 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901351 : term27 = term27.
Proof. exact (MK_COMB (@lem6901350) (@lem6901349)). Qed.
Lemma lem6901352 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901353 : term15 = term15.
Proof. exact (MK_COMB (@lem6901352) (@lem6901351)). Qed.
Lemma lem6901354 : term17 = term17.
Proof. exact (MK_COMB (@lem6901353) (@lem6901341)). Qed.
Lemma lem6901355 (y : nat) (x : nat) : ((Nat.mul x y) = (Nat.mul y x)) = ((Nat.mul x y) = (Nat.mul y x)).
Proof. exact (eq_refl ((Nat.mul x y) = (Nat.mul y x))). Qed.
Lemma lem6901356 (x : nat) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : nat => @lem6901355 y x)). Qed.
Lemma lem6901357 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901358 (x : nat) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem6901357) (@lem6901356 x)). Qed.
Lemma lem6901359 : term30 = term30.
Proof. exact (fun_ext (fun x : nat => @lem6901358 x)). Qed.
Lemma lem6901360 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901361 : term31 = term31.
Proof. exact (MK_COMB (@lem6901360) (@lem6901359)). Qed.
Lemma lem6901362 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901363 : term18 = term18.
Proof. exact (MK_COMB (@lem6901362) (@lem6901361)). Qed.
Lemma lem6901365 : term19 = term19.
Proof. exact (MK_COMB (@lem6901363) (@lem6901354)). Qed.
Lemma lem6901366 (y : nat) (x : nat) : ((Nat.mul x y) = (Nat.mul y x)) = ((Nat.mul x y) = (Nat.mul y x)).
Proof. exact (eq_refl ((Nat.mul x y) = (Nat.mul y x))). Qed.
Lemma lem6901367 (x : nat) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : nat => @lem6901366 y x)). Qed.
Lemma lem6901368 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901369 (x : nat) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem6901368) (@lem6901367 x)). Qed.
Lemma lem6901370 : term30 = term30.
Proof. exact (fun_ext (fun x : nat => @lem6901369 x)). Qed.
Lemma lem6901371 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901372 : term31 = term31.
Proof. exact (MK_COMB (@lem6901371) (@lem6901370)). Qed.
Lemma lem6901373 (x : nat) (y : nat) (z : nat) : ((term20 x y z) = (term21 x y z)) = ((term20 x y z) = (term21 x y z)).
Proof. exact (eq_refl ((term20 x y z) = (term21 x y z))). Qed.
Lemma lem6901374 (x : nat) (y : nat) : (term22 x y) = (term22 x y).
Proof. exact (fun_ext (fun z : nat => @lem6901373 x y z)). Qed.
Lemma lem6901375 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901376 (x : nat) (y : nat) : (term23 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem6901375) (@lem6901374 x y)). Qed.
Lemma lem6901377 (x : nat) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : nat => @lem6901376 x y)). Qed.
Lemma lem6901378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901379 (x : nat) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem6901378) (@lem6901377 x)). Qed.
Lemma lem6901380 : term26 = term26.
Proof. exact (fun_ext (fun x : nat => @lem6901379 x)). Qed.
Lemma lem6901381 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901382 : term27 = term27.
Proof. exact (MK_COMB (@lem6901381) (@lem6901380)). Qed.
Lemma lem6901383 (x : nat) : ((term8 x) = x) = ((term8 x) = x).
Proof. exact (eq_refl ((term8 x) = x)). Qed.
Lemma lem6901384 : term12 = term12.
Proof. exact (fun_ext (fun x : nat => @lem6901383 x)). Qed.
Lemma lem6901385 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901386 : term14 = term14.
Proof. exact (MK_COMB (@lem6901385) (@lem6901384)). Qed.
Lemma lem6901387 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901388 : term15 = term15.
Proof. exact (MK_COMB (@lem6901387) (@lem6901382)). Qed.
Lemma lem6901389 : term17 = term17.
Proof. exact (MK_COMB (@lem6901388) (@lem6901386)). Qed.
Lemma lem6901390 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901391 : term18 = term18.
Proof. exact (MK_COMB (@lem6901390) (@lem6901372)). Qed.
Lemma lem6901392 : term19 = term19.
Proof. exact (MK_COMB (@lem6901391) (@lem6901389)). Qed.
Lemma lem6901393 : term19 = term19.
Proof. exact (TRANS (@lem6901365) (@lem6901392)). Qed.
Lemma lem6901394 (x : nat) : ((term8 x) = x) = ((term8 x) = x).
Proof. exact (eq_refl ((term8 x) = x)). Qed.
Lemma lem6901395 : term12 = term12.
Proof. exact (fun_ext (fun x : nat => @lem6901394 x)). Qed.
Lemma lem6901396 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901397 : term14 = term14.
Proof. exact (MK_COMB (@lem6901396) (@lem6901395)). Qed.
Lemma lem6901398 (x : nat) (y : nat) (z : nat) : ((term20 x y z) = (term21 x y z)) = ((term20 x y z) = (term21 x y z)).
Proof. exact (eq_refl ((term20 x y z) = (term21 x y z))). Qed.
Lemma lem6901399 (x : nat) (y : nat) : (term22 x y) = (term22 x y).
Proof. exact (fun_ext (fun z : nat => @lem6901398 x y z)). Qed.
Lemma lem6901400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901401 (x : nat) (y : nat) : (term23 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem6901400) (@lem6901399 x y)). Qed.
Lemma lem6901402 (x : nat) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : nat => @lem6901401 x y)). Qed.
Lemma lem6901403 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901404 (x : nat) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem6901403) (@lem6901402 x)). Qed.
Lemma lem6901405 : term26 = term26.
Proof. exact (fun_ext (fun x : nat => @lem6901404 x)). Qed.
Lemma lem6901406 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901407 : term27 = term27.
Proof. exact (MK_COMB (@lem6901406) (@lem6901405)). Qed.
Lemma lem6901408 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901409 : term15 = term15.
Proof. exact (MK_COMB (@lem6901408) (@lem6901407)). Qed.
Lemma lem6901410 : term17 = term17.
Proof. exact (MK_COMB (@lem6901409) (@lem6901397)). Qed.
Lemma lem6901411 (y : nat) (x : nat) : ((Nat.mul x y) = (Nat.mul y x)) = ((Nat.mul x y) = (Nat.mul y x)).
Proof. exact (eq_refl ((Nat.mul x y) = (Nat.mul y x))). Qed.
Lemma lem6901412 (x : nat) : (term28 x) = (term28 x).
Proof. exact (fun_ext (fun y : nat => @lem6901411 y x)). Qed.
Lemma lem6901413 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901414 (x : nat) : (term29 x) = (term29 x).
Proof. exact (MK_COMB (@lem6901413) (@lem6901412 x)). Qed.
Lemma lem6901415 : term30 = term30.
Proof. exact (fun_ext (fun x : nat => @lem6901414 x)). Qed.
Lemma lem6901416 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901417 : term31 = term31.
Proof. exact (MK_COMB (@lem6901416) (@lem6901415)). Qed.
Lemma lem6901418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901419 : term18 = term18.
Proof. exact (MK_COMB (@lem6901418) (@lem6901417)). Qed.
Lemma lem6901420 : term19 = term19.
Proof. exact (MK_COMB (@lem6901419) (@lem6901410)). Qed.
Lemma lem6901461 : term19 = term19.
Proof. exact (TRANS (@lem6901393) (@lem6901420)). Qed.
Lemma lem6901462 (x : nat) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem6901469 (x : nat) : (term8 x) = x.
Proof. exact (@lem1032070 x). Qed.
Lemma lem6901470 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem6901471 (x : nat) : (term10 x) = (@eq nat x).
Proof. exact (MK_COMB (@lem6901470) (@lem6901469 x)). Qed.
Lemma lem6901472 (x : nat) : ((term8 x) = x) = (x = x).
Proof. exact (MK_COMB (@lem6901471 x) (@lem6901462 x)). Qed.
Lemma lem6901473 : term12 = term32.
Proof. exact (fun_ext (fun x : nat => @lem6901472 x)). Qed.
Lemma lem6901474 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901475 : term14 = term33.
Proof. exact (MK_COMB (@lem6901474) (@lem6901473)). Qed.
Lemma lem6901492 (x : nat) (y : nat) (z : nat) : (term21 x y z) = (term20 x y z).
Proof. exact (@lem1032082 x y z). Qed.
Lemma lem6901507 (x : nat) (y : nat) (z : nat) : (term34 x y z) = (term34 x y z).
Proof. exact (eq_refl (term34 x y z)). Qed.
Lemma lem6901508 (x : nat) (y : nat) (z : nat) : ((term20 x y z) = (term21 x y z)) = ((term20 x y z) = (term20 x y z)).
Proof. exact (MK_COMB (@lem6901507 x y z) (@lem6901492 x y z)). Qed.
Lemma lem6901509 (x : nat) (y : nat) : (term22 x y) = (term35 x y).
Proof. exact (fun_ext (fun z : nat => @lem6901508 x y z)). Qed.
Lemma lem6901510 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901511 (x : nat) (y : nat) : (term23 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem6901510) (@lem6901509 x y)). Qed.
Lemma lem6901512 (x : nat) : (term24 x) = (term37 x).
Proof. exact (fun_ext (fun y : nat => @lem6901511 x y)). Qed.
Lemma lem6901513 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901514 (x : nat) : (term25 x) = (term38 x).
Proof. exact (MK_COMB (@lem6901513) (@lem6901512 x)). Qed.
Lemma lem6901515 : term26 = term39.
Proof. exact (fun_ext (fun x : nat => @lem6901514 x)). Qed.
Lemma lem6901516 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901517 : term27 = term40.
Proof. exact (MK_COMB (@lem6901516) (@lem6901515)). Qed.
Lemma lem6901518 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901519 : term15 = term41.
Proof. exact (MK_COMB (@lem6901518) (@lem6901517)). Qed.
Lemma lem6901520 : term17 = term42.
Proof. exact (MK_COMB (@lem6901519) (@lem6901475)). Qed.
Lemma lem6901527 (x : nat) (y : nat) : (Nat.mul y x) = (Nat.mul x y).
Proof. exact (@lem1032084 x y). Qed.
Lemma lem6901536 (x : nat) (y : nat) : (term43 x y) = (term43 x y).
Proof. exact (eq_refl (term43 x y)). Qed.
Lemma lem6901537 (x : nat) (y : nat) : ((Nat.mul x y) = (Nat.mul y x)) = ((Nat.mul x y) = (Nat.mul x y)).
Proof. exact (MK_COMB (@lem6901536 x y) (@lem6901527 x y)). Qed.
Lemma lem6901538 (x : nat) : (term28 x) = (term44 x).
Proof. exact (fun_ext (fun y : nat => @lem6901537 x y)). Qed.
Lemma lem6901539 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901540 (x : nat) : (term29 x) = (term45 x).
Proof. exact (MK_COMB (@lem6901539) (@lem6901538 x)). Qed.
Lemma lem6901541 : term30 = term46.
Proof. exact (fun_ext (fun x : nat => @lem6901540 x)). Qed.
Lemma lem6901542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901543 : term31 = term47.
Proof. exact (MK_COMB (@lem6901542) (@lem6901541)). Qed.
Lemma lem6901544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901545 : term18 = term48.
Proof. exact (MK_COMB (@lem6901544) (@lem6901543)). Qed.
Lemma lem6901546 : term19 = term49.
Proof. exact (MK_COMB (@lem6901545) (@lem6901520)). Qed.
Lemma lem6901547 : term19 = term49.
Proof. exact (TRANS (@lem6901461) (@lem6901546)). Qed.
Lemma lem6901549 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6901550 (P : nat -> Prop) (Q : nat -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem6901549 nat P Q). Qed.
Lemma lem6901551 : term54 = term55.
Proof. exact (@lem6901550 term39 term32). Qed.
Lemma lem6901552 (x : nat) : (term56 x) = (term38 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem6901553 : term57 = term39.
Proof. exact (fun_ext (fun x : nat => @lem6901552 x)). Qed.
Lemma lem6901554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901555 : term58 = term40.
Proof. exact (MK_COMB (@lem6901554) (@lem6901553)). Qed.
Lemma lem6901556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901557 : term59 = term41.
Proof. exact (MK_COMB (@lem6901556) (@lem6901555)). Qed.
Lemma lem6901558 (x : nat) : (term60 x) = (x = x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem6901559 : term61 = term32.
Proof. exact (fun_ext (fun x : nat => @lem6901558 x)). Qed.
Lemma lem6901560 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901561 : term62 = term33.
Proof. exact (MK_COMB (@lem6901560) (@lem6901559)). Qed.
Lemma lem6901562 : term54 = term42.
Proof. exact (MK_COMB (@lem6901557) (@lem6901561)). Qed.
Lemma lem6901563 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6901564 : term63 = term64.
Proof. exact (MK_COMB (@lem6901563) (@lem6901562)). Qed.
Lemma lem6901565 (x : nat) : (term56 x) = (term38 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem6901566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901567 (x : nat) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem6901566) (@lem6901565 x)). Qed.
Lemma lem6901568 (x : nat) : (term60 x) = (x = x).
Proof. exact (eq_refl (term60 x)). Qed.
Lemma lem6901569 (x : nat) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem6901567 x) (@lem6901568 x)). Qed.
Lemma lem6901570 : term69 = term70.
Proof. exact (fun_ext (fun x : nat => @lem6901569 x)). Qed.
Lemma lem6901571 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901572 : term55 = term71.
Proof. exact (MK_COMB (@lem6901571) (@lem6901570)). Qed.
Lemma lem6901573 : (term54 = term55) = (term42 = term71).
Proof. exact (MK_COMB (@lem6901564) (@lem6901572)). Qed.
Lemma lem6901574 : term42 = term71.
Proof. exact (EQ_MP (@lem6901573) (@lem6901551)). Qed.
Lemma lem6901576 {A : Type'} (P : A -> Prop) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6901577 (P : nat -> Prop) (Q : Prop) : (term74 P Q) = (term75 P Q).
Proof. exact (@lem6901576 nat P Q). Qed.
Lemma lem6901578 (x : nat) : (term76 x) = (term77 x).
Proof. exact (@lem6901577 (term37 x) (x = x)). Qed.
Lemma lem6901579 (x : nat) (y : nat) : (term78 x y) = (term36 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem6901580 (x : nat) : (term79 x) = (term37 x).
Proof. exact (fun_ext (fun y : nat => @lem6901579 x y)). Qed.
Lemma lem6901581 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901582 (x : nat) : (term80 x) = (term38 x).
Proof. exact (MK_COMB (@lem6901581) (@lem6901580 x)). Qed.
Lemma lem6901583 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901584 (x : nat) : (term81 x) = (term66 x).
Proof. exact (MK_COMB (@lem6901583) (@lem6901582 x)). Qed.
Lemma lem6901585 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6901586 (x : nat) : (term76 x) = (term68 x).
Proof. exact (MK_COMB (@lem6901584 x) (@lem6901585 x)). Qed.
Lemma lem6901587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6901588 (x : nat) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem6901587) (@lem6901586 x)). Qed.
Lemma lem6901589 (x : nat) (y : nat) : (term78 x y) = (term36 x y).
Proof. exact (eq_refl (term78 x y)). Qed.
Lemma lem6901590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901591 (x : nat) (y : nat) : (term84 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem6901590) (@lem6901589 x y)). Qed.
Lemma lem6901592 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6901593 (y : nat) (x : nat) : (term86 y x) = (term87 y x).
Proof. exact (MK_COMB (@lem6901591 x y) (@lem6901592 x)). Qed.
Lemma lem6901594 (x : nat) : (term88 x) = (term89 x).
Proof. exact (fun_ext (fun y : nat => @lem6901593 y x)). Qed.
Lemma lem6901595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901596 (x : nat) : (term77 x) = (term90 x).
Proof. exact (MK_COMB (@lem6901595) (@lem6901594 x)). Qed.
Lemma lem6901597 (x : nat) : ((term76 x) = (term77 x)) = ((term68 x) = (term90 x)).
Proof. exact (MK_COMB (@lem6901588 x) (@lem6901596 x)). Qed.
Lemma lem6901598 (x : nat) : (term68 x) = (term90 x).
Proof. exact (EQ_MP (@lem6901597 x) (@lem6901578 x)). Qed.
Lemma lem6901600 {A : Type'} (P : A -> Prop) (Q : Prop) : (term72 A P Q) = (term73 A P Q).
Proof. exact (EQ_MP (@lem19025 A P Q) (@lem19024 A P Q)). Qed.
Lemma lem6901601 (P : nat -> Prop) (Q : Prop) : (term74 P Q) = (term75 P Q).
Proof. exact (@lem6901600 nat P Q). Qed.
Lemma lem6901602 (y : nat) (x : nat) : (term91 y x) = (term92 y x).
Proof. exact (@lem6901601 (term35 x y) (x = x)). Qed.
Lemma lem6901603 (x : nat) (y : nat) (z : nat) : (term93 x y z) = ((term20 x y z) = (term20 x y z)).
Proof. exact (eq_refl (term93 x y z)). Qed.
Lemma lem6901604 (x : nat) (y : nat) : (term94 x y) = (term35 x y).
Proof. exact (fun_ext (fun z : nat => @lem6901603 x y z)). Qed.
Lemma lem6901605 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901606 (x : nat) (y : nat) : (term95 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem6901605) (@lem6901604 x y)). Qed.
Lemma lem6901607 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901608 (x : nat) (y : nat) : (term96 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem6901607) (@lem6901606 x y)). Qed.
Lemma lem6901609 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6901610 (y : nat) (x : nat) : (term91 y x) = (term87 y x).
Proof. exact (MK_COMB (@lem6901608 x y) (@lem6901609 x)). Qed.
Lemma lem6901611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6901612 (y : nat) (x : nat) : (term97 y x) = (term98 y x).
Proof. exact (MK_COMB (@lem6901611) (@lem6901610 y x)). Qed.
Lemma lem6901613 (x : nat) (y : nat) (z : nat) : (term93 x y z) = ((term20 x y z) = (term20 x y z)).
Proof. exact (eq_refl (term93 x y z)). Qed.
Lemma lem6901614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901615 (x : nat) (y : nat) (z : nat) : (term99 x y z) = (term100 x y z).
Proof. exact (MK_COMB (@lem6901614) (@lem6901613 x y z)). Qed.
Lemma lem6901616 (x : nat) : (x = x) = (x = x).
Proof. exact (eq_refl (x = x)). Qed.
Lemma lem6901617 (y : nat) (z : nat) (x : nat) : (term101 y z x) = (term102 y z x).
Proof. exact (MK_COMB (@lem6901615 x y z) (@lem6901616 x)). Qed.
Lemma lem6901618 (y : nat) (x : nat) : (term103 y x) = (term104 y x).
Proof. exact (fun_ext (fun z : nat => @lem6901617 y z x)). Qed.
Lemma lem6901619 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901620 (y : nat) (x : nat) : (term92 y x) = (term105 y x).
Proof. exact (MK_COMB (@lem6901619) (@lem6901618 y x)). Qed.
Lemma lem6901621 (y : nat) (x : nat) : ((term91 y x) = (term92 y x)) = ((term87 y x) = (term105 y x)).
Proof. exact (MK_COMB (@lem6901612 y x) (@lem6901620 y x)). Qed.
Lemma lem6901622 (y : nat) (x : nat) : (term87 y x) = (term105 y x).
Proof. exact (EQ_MP (@lem6901621 y x) (@lem6901602 y x)). Qed.
Lemma lem6901623 (x : nat) : (term89 x) = (term106 x).
Proof. exact (fun_ext (fun y : nat => @lem6901622 y x)). Qed.
Lemma lem6901624 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901625 (x : nat) : (term90 x) = (term107 x).
Proof. exact (MK_COMB (@lem6901624) (@lem6901623 x)). Qed.
Lemma lem6901626 (x : nat) : (term68 x) = (term107 x).
Proof. exact (TRANS (@lem6901598 x) (@lem6901625 x)). Qed.
Lemma lem6901627 : term70 = term108.
Proof. exact (fun_ext (fun x : nat => @lem6901626 x)). Qed.
Lemma lem6901628 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901629 : term71 = term109.
Proof. exact (MK_COMB (@lem6901628) (@lem6901627)). Qed.
Lemma lem6901630 : term42 = term109.
Proof. exact (TRANS (@lem6901574) (@lem6901629)). Qed.
Lemma lem6901631 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem6901632 : term49 = term110.
Proof. exact (MK_COMB (@lem6901631) (@lem6901630)). Qed.
Lemma lem6901634 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6901635 (P : nat -> Prop) (Q : nat -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem6901634 nat P Q). Qed.
Lemma lem6901636 : term111 = term112.
Proof. exact (@lem6901635 term46 term108). Qed.
Lemma lem6901637 (x : nat) : (term113 x) = (term45 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem6901638 : term114 = term46.
Proof. exact (fun_ext (fun x : nat => @lem6901637 x)). Qed.
Lemma lem6901639 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901640 : term115 = term47.
Proof. exact (MK_COMB (@lem6901639) (@lem6901638)). Qed.
Lemma lem6901641 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901642 : term116 = term48.
Proof. exact (MK_COMB (@lem6901641) (@lem6901640)). Qed.
Lemma lem6901643 (x : nat) : (term117 x) = (term107 x).
Proof. exact (eq_refl (term117 x)). Qed.
Lemma lem6901644 : term118 = term108.
Proof. exact (fun_ext (fun x : nat => @lem6901643 x)). Qed.
Lemma lem6901645 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901646 : term119 = term109.
Proof. exact (MK_COMB (@lem6901645) (@lem6901644)). Qed.
Lemma lem6901647 : term111 = term110.
Proof. exact (MK_COMB (@lem6901642) (@lem6901646)). Qed.
Lemma lem6901648 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6901649 : term120 = term121.
Proof. exact (MK_COMB (@lem6901648) (@lem6901647)). Qed.
Lemma lem6901650 (x : nat) : (term113 x) = (term45 x).
Proof. exact (eq_refl (term113 x)). Qed.
Lemma lem6901651 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901652 (x : nat) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem6901651) (@lem6901650 x)). Qed.
Lemma lem6901653 (x : nat) : (term117 x) = (term107 x).
Proof. exact (eq_refl (term117 x)). Qed.
Lemma lem6901654 (x : nat) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem6901652 x) (@lem6901653 x)). Qed.
Lemma lem6901655 : term126 = term127.
Proof. exact (fun_ext (fun x : nat => @lem6901654 x)). Qed.
Lemma lem6901656 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901657 : term112 = term128.
Proof. exact (MK_COMB (@lem6901656) (@lem6901655)). Qed.
Lemma lem6901658 : (term111 = term112) = (term110 = term128).
Proof. exact (MK_COMB (@lem6901649) (@lem6901657)). Qed.
Lemma lem6901659 : term110 = term128.
Proof. exact (EQ_MP (@lem6901658) (@lem6901636)). Qed.
Lemma lem6901661 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term50 A P Q) = (term51 A P Q).
Proof. exact (EQ_MP (@lem19031 A P Q) (@lem19030 A P Q)). Qed.
Lemma lem6901662 (P : nat -> Prop) (Q : nat -> Prop) : (term52 P Q) = (term53 P Q).
Proof. exact (@lem6901661 nat P Q). Qed.
Lemma lem6901663 (x : nat) : (term129 x) = (term130 x).
Proof. exact (@lem6901662 (term44 x) (term106 x)). Qed.
Lemma lem6901664 (x : nat) (y : nat) : (term131 x y) = ((Nat.mul x y) = (Nat.mul x y)).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem6901665 (x : nat) : (term132 x) = (term44 x).
Proof. exact (fun_ext (fun y : nat => @lem6901664 x y)). Qed.
Lemma lem6901666 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901667 (x : nat) : (term133 x) = (term45 x).
Proof. exact (MK_COMB (@lem6901666) (@lem6901665 x)). Qed.
Lemma lem6901668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901669 (x : nat) : (term134 x) = (term123 x).
Proof. exact (MK_COMB (@lem6901668) (@lem6901667 x)). Qed.
Lemma lem6901670 (y : nat) (x : nat) : (term135 x y) = (term105 y x).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem6901671 (x : nat) : (term136 x) = (term106 x).
Proof. exact (fun_ext (fun y : nat => @lem6901670 y x)). Qed.
Lemma lem6901672 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901673 (x : nat) : (term137 x) = (term107 x).
Proof. exact (MK_COMB (@lem6901672) (@lem6901671 x)). Qed.
Lemma lem6901674 (x : nat) : (term129 x) = (term125 x).
Proof. exact (MK_COMB (@lem6901669 x) (@lem6901673 x)). Qed.
Lemma lem6901675 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6901676 (x : nat) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem6901675) (@lem6901674 x)). Qed.
Lemma lem6901677 (x : nat) (y : nat) : (term131 x y) = ((Nat.mul x y) = (Nat.mul x y)).
Proof. exact (eq_refl (term131 x y)). Qed.
Lemma lem6901678 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901679 (x : nat) (y : nat) : (term140 x y) = (term141 x y).
Proof. exact (MK_COMB (@lem6901678) (@lem6901677 x y)). Qed.
Lemma lem6901680 (y : nat) (x : nat) : (term135 x y) = (term105 y x).
Proof. exact (eq_refl (term135 x y)). Qed.
Lemma lem6901681 (y : nat) (x : nat) : (term142 x y) = (term143 y x).
Proof. exact (MK_COMB (@lem6901679 x y) (@lem6901680 y x)). Qed.
Lemma lem6901682 (x : nat) : (term144 x) = (term145 x).
Proof. exact (fun_ext (fun y : nat => @lem6901681 y x)). Qed.
Lemma lem6901683 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901684 (x : nat) : (term130 x) = (term146 x).
Proof. exact (MK_COMB (@lem6901683) (@lem6901682 x)). Qed.
Lemma lem6901685 (x : nat) : ((term129 x) = (term130 x)) = ((term125 x) = (term146 x)).
Proof. exact (MK_COMB (@lem6901676 x) (@lem6901684 x)). Qed.
Lemma lem6901686 (x : nat) : (term125 x) = (term146 x).
Proof. exact (EQ_MP (@lem6901685 x) (@lem6901663 x)). Qed.
Lemma lem6901688 {A : Type'} (P : Prop) (Q : A -> Prop) : (term147 A P Q) = (term148 A P Q).
Proof. exact (EQ_MP (@lem19019 A P Q) (@lem19018 A P Q)). Qed.
Lemma lem6901689 (P : Prop) (Q : nat -> Prop) : (term149 P Q) = (term150 P Q).
Proof. exact (@lem6901688 nat P Q). Qed.
Lemma lem6901690 (y : nat) (x : nat) : (term151 y x) = (term152 y x).
Proof. exact (@lem6901689 ((Nat.mul x y) = (Nat.mul x y)) (term104 y x)). Qed.
Lemma lem6901691 (y : nat) (z : nat) (x : nat) : (term153 y x z) = (term102 y z x).
Proof. exact (eq_refl (term153 y x z)). Qed.
Lemma lem6901692 (y : nat) (x : nat) : (term154 y x) = (term104 y x).
Proof. exact (fun_ext (fun z : nat => @lem6901691 y z x)). Qed.
Lemma lem6901693 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901694 (y : nat) (x : nat) : (term155 y x) = (term105 y x).
Proof. exact (MK_COMB (@lem6901693) (@lem6901692 y x)). Qed.
Lemma lem6901695 (x : nat) (y : nat) : (term141 x y) = (term141 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem6901696 (y : nat) (x : nat) : (term151 y x) = (term143 y x).
Proof. exact (MK_COMB (@lem6901695 x y) (@lem6901694 y x)). Qed.
Lemma lem6901697 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem6901698 (y : nat) (x : nat) : (term156 y x) = (term157 y x).
Proof. exact (MK_COMB (@lem6901697) (@lem6901696 y x)). Qed.
Lemma lem6901699 (y : nat) (z : nat) (x : nat) : (term153 y x z) = (term102 y z x).
Proof. exact (eq_refl (term153 y x z)). Qed.
Lemma lem6901700 (x : nat) (y : nat) : (term141 x y) = (term141 x y).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem6901701 (y : nat) (z : nat) (x : nat) : (term158 y x z) = (term159 y z x).
Proof. exact (MK_COMB (@lem6901700 x y) (@lem6901699 y z x)). Qed.
Lemma lem6901702 (y : nat) (x : nat) : (term160 y x) = (term161 y x).
Proof. exact (fun_ext (fun z : nat => @lem6901701 y z x)). Qed.
Lemma lem6901703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901704 (y : nat) (x : nat) : (term152 y x) = (term162 y x).
Proof. exact (MK_COMB (@lem6901703) (@lem6901702 y x)). Qed.
Lemma lem6901705 (y : nat) (x : nat) : ((term151 y x) = (term152 y x)) = ((term143 y x) = (term162 y x)).
Proof. exact (MK_COMB (@lem6901698 y x) (@lem6901704 y x)). Qed.
Lemma lem6901706 (y : nat) (x : nat) : (term143 y x) = (term162 y x).
Proof. exact (EQ_MP (@lem6901705 y x) (@lem6901690 y x)). Qed.
Lemma lem6901707 (x : nat) : (term145 x) = (term163 x).
Proof. exact (fun_ext (fun y : nat => @lem6901706 y x)). Qed.
Lemma lem6901708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901709 (x : nat) : (term146 x) = (term164 x).
Proof. exact (MK_COMB (@lem6901708) (@lem6901707 x)). Qed.
Lemma lem6901710 (x : nat) : (term125 x) = (term164 x).
Proof. exact (TRANS (@lem6901686 x) (@lem6901709 x)). Qed.
Lemma lem6901711 : term127 = term165.
Proof. exact (fun_ext (fun x : nat => @lem6901710 x)). Qed.
Lemma lem6901712 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901713 : term128 = term166.
Proof. exact (MK_COMB (@lem6901712) (@lem6901711)). Qed.
Lemma lem6901714 : term110 = term166.
Proof. exact (TRANS (@lem6901659) (@lem6901713)). Qed.
Lemma lem6901715 : term49 = term166.
Proof. exact (TRANS (@lem6901632) (@lem6901714)). Qed.
Lemma lem6901716 : term19 = term166.
Proof. exact (TRANS (@lem6901547) (@lem6901715)). Qed.
Lemma lem6901718 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6901719 (x : nat) (y : nat) : ((Nat.mul x y) = (Nat.mul x y)) = ((term167 x y) = (term167 x y)).
Proof. exact (@lem6901718 (Nat.mul x y) (Nat.mul x y)). Qed.
Lemma lem6901722 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901723 (x : nat) (y : nat) : (term141 x y) = (term168 x y).
Proof. exact (MK_COMB (@lem6901722) (@lem6901719 x y)). Qed.
Lemma lem6901725 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6901726 (x : nat) (y : nat) (z : nat) : ((term20 x y z) = (term20 x y z)) = ((term169 x y z) = (term169 x y z)).
Proof. exact (@lem6901725 (term20 x y z) (term20 x y z)). Qed.
Lemma lem6901729 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6901730 (x : nat) (y : nat) (z : nat) : (term100 x y z) = (term170 x y z).
Proof. exact (MK_COMB (@lem6901729) (@lem6901726 x y z)). Qed.
Lemma lem6901732 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem6901733 (x : nat) : (x = x) = ((int_of_num x) = (int_of_num x)).
Proof. exact (@lem6901732 x x). Qed.
Lemma lem6901736 (y : nat) (z : nat) (x : nat) : (term102 y z x) = (term171 y z x).
Proof. exact (MK_COMB (@lem6901730 x y z) (@lem6901733 x)). Qed.
Lemma lem6901737 (y : nat) (z : nat) (x : nat) : (term159 y z x) = (term172 y z x).
Proof. exact (MK_COMB (@lem6901723 x y) (@lem6901736 y z x)). Qed.
Lemma lem6901738 (y : nat) (x : nat) : (term161 y x) = (term173 y x).
Proof. exact (fun_ext (fun z : nat => @lem6901737 y z x)). Qed.
Lemma lem6901739 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901740 (y : nat) (x : nat) : (term162 y x) = (term174 y x).
Proof. exact (MK_COMB (@lem6901739) (@lem6901738 y x)). Qed.
Lemma lem6901741 (x : nat) : (term163 x) = (term175 x).
Proof. exact (fun_ext (fun y : nat => @lem6901740 y x)). Qed.
Lemma lem6901742 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901743 (x : nat) : (term164 x) = (term176 x).
Proof. exact (MK_COMB (@lem6901742) (@lem6901741 x)). Qed.
Lemma lem6901744 : term165 = term177.
Proof. exact (fun_ext (fun x : nat => @lem6901743 x)). Qed.
Lemma lem6901745 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem6901746 : term166 = term178.
Proof. exact (MK_COMB (@lem6901745) (@lem6901744)). Qed.
Lemma lem6901747 : term19 = term178.
Proof. exact (TRANS (@lem6901716) (@lem6901746)). Qed.
Lemma lem6901748 (x : nat) : term179 x.
Proof. exact (@lem2307535 x). Qed.
Lemma lem6901749 (x : nat) : (term179 x) = (term180 x).
Proof. exact (eq_refl (term179 x)). Qed.
Lemma lem6901750 (x : nat) : term180 x.
Proof. exact (EQ_MP (@lem6901749 x) (@lem6901748 x)). Qed.
Lemma lem6901751 (x : nat) (y : nat) : term181 x y.
Proof. exact (@lem2307535 (Nat.mul x y)). Qed.
Lemma lem6901752 (x : nat) (y : nat) : (term181 x y) = (term182 x y).
Proof. exact (eq_refl (term181 x y)). Qed.
Lemma lem6901753 (x : nat) (y : nat) : term182 x y.
Proof. exact (EQ_MP (@lem6901752 x y) (@lem6901751 x y)). Qed.
Lemma lem6901754 (x : nat) (y : nat) (z : nat) : term183 x y z.
Proof. exact (@lem2307535 (term20 x y z)). Qed.
Lemma lem6901755 (x : nat) (y : nat) (z : nat) : (term183 x y z) = (term184 x y z).
Proof. exact (eq_refl (term183 x y z)). Qed.
Lemma lem6901756 (x : nat) (y : nat) (z : nat) : term184 x y z.
Proof. exact (EQ_MP (@lem6901755 x y z) (@lem6901754 x y z)). Qed.
Lemma lem6901757 (_92163 : int) (_92164 : int) (_92162 : int) : (term185 _92163 _92164 _92162) = (term186 _92163 _92164 _92162).
Proof. exact (@lem2318604 (term186 _92163 _92164 _92162)). Qed.
Lemma lem6901783 (_92164 : int) (_92162 : int) : (term187 _92164 _92162) = (term188 _92164 _92162).
Proof. exact (@lem17045 (_92164 = _92164) (_92162 = _92162)). Qed.
Lemma lem6901785 (_92163 : int) : (term189 _92163) = (term189 _92163).
Proof. exact (eq_refl (term189 _92163)). Qed.
Lemma lem6901786 (_92163 : int) (_92164 : int) (_92162 : int) : (term190 _92163 _92164 _92162) = (term191 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6901785 _92163) (@lem6901783 _92164 _92162)). Qed.
Lemma lem6901787 (_92163 : int) (_92164 : int) (_92162 : int) : (term192 _92163 _92164 _92162) = (term190 _92163 _92164 _92162).
Proof. exact (@lem17045 (_92163 = _92163) (term193 _92164 _92162)). Qed.
Lemma lem6901788 (_92163 : int) (_92164 : int) (_92162 : int) : (term192 _92163 _92164 _92162) = (term191 _92163 _92164 _92162).
Proof. exact (TRANS (@lem6901787 _92163 _92164 _92162) (@lem6901786 _92163 _92164 _92162)). Qed.
Lemma lem6901790 (_92164 : int) : (term194 _92164) = (term194 _92164).
Proof. exact (eq_refl (term194 _92164)). Qed.
Lemma lem6901791 (_92163 : int) (_92164 : int) (_92162 : int) : (term195 _92163 _92164 _92162) = (term196 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6901790 _92164) (@lem6901788 _92163 _92164 _92162)). Qed.
Lemma lem6901792 (_92163 : int) (_92164 : int) (_92162 : int) : (term197 _92163 _92164 _92162) = (term195 _92163 _92164 _92162).
Proof. exact (@lem17362 (term198 _92164) (term199 _92163 _92164 _92162)). Qed.
Lemma lem6901793 (_92163 : int) (_92164 : int) (_92162 : int) : (term197 _92163 _92164 _92162) = (term196 _92163 _92164 _92162).
Proof. exact (TRANS (@lem6901792 _92163 _92164 _92162) (@lem6901791 _92163 _92164 _92162)). Qed.
Lemma lem6901795 (_92163 : int) : (term194 _92163) = (term194 _92163).
Proof. exact (eq_refl (term194 _92163)). Qed.
Lemma lem6901796 (_92163 : int) (_92164 : int) (_92162 : int) : (term200 _92163 _92164 _92162) = (term201 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6901795 _92163) (@lem6901793 _92163 _92164 _92162)). Qed.
Lemma lem6901797 (_92163 : int) (_92164 : int) (_92162 : int) : (term202 _92163 _92164 _92162) = (term200 _92163 _92164 _92162).
Proof. exact (@lem17362 (term198 _92163) (term203 _92163 _92164 _92162)). Qed.
Lemma lem6901798 (_92163 : int) (_92164 : int) (_92162 : int) : (term202 _92163 _92164 _92162) = (term201 _92163 _92164 _92162).
Proof. exact (TRANS (@lem6901797 _92163 _92164 _92162) (@lem6901796 _92163 _92164 _92162)). Qed.
Lemma lem6901800 (_92162 : int) : (term194 _92162) = (term194 _92162).
Proof. exact (eq_refl (term194 _92162)). Qed.
Lemma lem6901801 (_92163 : int) (_92164 : int) (_92162 : int) : (term204 _92163 _92164 _92162) = (term205 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6901800 _92162) (@lem6901798 _92163 _92164 _92162)). Qed.
Lemma lem6901802 (_92163 : int) (_92164 : int) (_92162 : int) : (term206 _92163 _92164 _92162) = (term204 _92163 _92164 _92162).
Proof. exact (@lem17362 (term198 _92162) (term207 _92163 _92164 _92162)). Qed.
Lemma lem6901832 (_92163 : int) (_92164 : int) (_92162 : int) : (term206 _92163 _92164 _92162) = (term205 _92163 _92164 _92162).
Proof. exact (TRANS (@lem6901802 _92163 _92164 _92162) (@lem6901801 _92163 _92164 _92162)). Qed.
Lemma lem6901835 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901836 (_92162 : int) : (term198 _92162) = (term209 _92162).
Proof. exact (@lem6901835 term210 _92162). Qed.
Lemma lem6901838 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901839 : term212 = term213.
Proof. exact (@lem6901838 (NUMERAL 0)). Qed.
Lemma lem6901840 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901841 : term214 = term215.
Proof. exact (MK_COMB (@lem6901840) (@lem6901839)). Qed.
Lemma lem6901842 (_92162 : int) : (real_of_int _92162) = (real_of_int _92162).
Proof. exact (eq_refl (real_of_int _92162)). Qed.
Lemma lem6901843 (_92162 : int) : (term209 _92162) = (term216 _92162).
Proof. exact (MK_COMB (@lem6901841) (@lem6901842 _92162)). Qed.
Lemma lem6901845 (_92162 : int) : (term198 _92162) = (term216 _92162).
Proof. exact (TRANS (@lem6901836 _92162) (@lem6901843 _92162)). Qed.
Lemma lem6901848 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901849 (_92163 : int) : (term198 _92163) = (term209 _92163).
Proof. exact (@lem6901848 term210 _92163). Qed.
Lemma lem6901851 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901852 : term212 = term213.
Proof. exact (@lem6901851 (NUMERAL 0)). Qed.
Lemma lem6901853 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901854 : term214 = term215.
Proof. exact (MK_COMB (@lem6901853) (@lem6901852)). Qed.
Lemma lem6901855 (_92163 : int) : (real_of_int _92163) = (real_of_int _92163).
Proof. exact (eq_refl (real_of_int _92163)). Qed.
Lemma lem6901856 (_92163 : int) : (term209 _92163) = (term216 _92163).
Proof. exact (MK_COMB (@lem6901854) (@lem6901855 _92163)). Qed.
Lemma lem6901858 (_92163 : int) : (term198 _92163) = (term216 _92163).
Proof. exact (TRANS (@lem6901849 _92163) (@lem6901856 _92163)). Qed.
Lemma lem6901861 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901862 (_92164 : int) : (term198 _92164) = (term209 _92164).
Proof. exact (@lem6901861 term210 _92164). Qed.
Lemma lem6901864 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901865 : term212 = term213.
Proof. exact (@lem6901864 (NUMERAL 0)). Qed.
Lemma lem6901866 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901867 : term214 = term215.
Proof. exact (MK_COMB (@lem6901866) (@lem6901865)). Qed.
Lemma lem6901868 (_92164 : int) : (real_of_int _92164) = (real_of_int _92164).
Proof. exact (eq_refl (real_of_int _92164)). Qed.
Lemma lem6901869 (_92164 : int) : (term209 _92164) = (term216 _92164).
Proof. exact (MK_COMB (@lem6901867) (@lem6901868 _92164)). Qed.
Lemma lem6901871 (_92164 : int) : (term198 _92164) = (term216 _92164).
Proof. exact (TRANS (@lem6901862 _92164) (@lem6901869 _92164)). Qed.
Lemma lem6901873 (y : int) (x : int) : (term217 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6901874 (_92163 : int) : (term219 _92163) = (term220 _92163).
Proof. exact (@lem6901873 _92163 _92163). Qed.
Lemma lem6901876 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901877 (_92163 : int) : (term221 _92163) = (term222 _92163).
Proof. exact (@lem6901876 (term223 _92163) _92163). Qed.
Lemma lem6901879 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6901880 (_92163 : int) : (term226 _92163) = (term227 _92163).
Proof. exact (@lem6901879 _92163 term228). Qed.
Lemma lem6901882 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901883 : term229 = term230.
Proof. exact (@lem6901882 term4). Qed.
Lemma lem6901884 (_92163 : int) : (term231 _92163) = (term231 _92163).
Proof. exact (eq_refl (term231 _92163)). Qed.
Lemma lem6901885 (_92163 : int) : (term227 _92163) = (term232 _92163).
Proof. exact (MK_COMB (@lem6901884 _92163) (@lem6901883)). Qed.
Lemma lem6901886 (_92163 : int) : (term226 _92163) = (term232 _92163).
Proof. exact (TRANS (@lem6901880 _92163) (@lem6901885 _92163)). Qed.
Lemma lem6901887 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901888 (_92163 : int) : (term233 _92163) = (term234 _92163).
Proof. exact (MK_COMB (@lem6901887) (@lem6901886 _92163)). Qed.
Lemma lem6901889 (_92163 : int) : (real_of_int _92163) = (real_of_int _92163).
Proof. exact (eq_refl (real_of_int _92163)). Qed.
Lemma lem6901890 (_92163 : int) : (term222 _92163) = (term235 _92163).
Proof. exact (MK_COMB (@lem6901888 _92163) (@lem6901889 _92163)). Qed.
Lemma lem6901891 (_92163 : int) : (term221 _92163) = (term235 _92163).
Proof. exact (TRANS (@lem6901877 _92163) (@lem6901890 _92163)). Qed.
Lemma lem6901892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6901893 (_92163 : int) : (term236 _92163) = (term237 _92163).
Proof. exact (MK_COMB (@lem6901892) (@lem6901891 _92163)). Qed.
Lemma lem6901895 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901896 (_92163 : int) : (term221 _92163) = (term222 _92163).
Proof. exact (@lem6901895 (term223 _92163) _92163). Qed.
Lemma lem6901898 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6901899 (_92163 : int) : (term226 _92163) = (term227 _92163).
Proof. exact (@lem6901898 _92163 term228). Qed.
Lemma lem6901901 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901902 : term229 = term230.
Proof. exact (@lem6901901 term4). Qed.
Lemma lem6901903 (_92163 : int) : (term231 _92163) = (term231 _92163).
Proof. exact (eq_refl (term231 _92163)). Qed.
Lemma lem6901904 (_92163 : int) : (term227 _92163) = (term232 _92163).
Proof. exact (MK_COMB (@lem6901903 _92163) (@lem6901902)). Qed.
Lemma lem6901905 (_92163 : int) : (term226 _92163) = (term232 _92163).
Proof. exact (TRANS (@lem6901899 _92163) (@lem6901904 _92163)). Qed.
Lemma lem6901906 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901907 (_92163 : int) : (term233 _92163) = (term234 _92163).
Proof. exact (MK_COMB (@lem6901906) (@lem6901905 _92163)). Qed.
Lemma lem6901908 (_92163 : int) : (real_of_int _92163) = (real_of_int _92163).
Proof. exact (eq_refl (real_of_int _92163)). Qed.
Lemma lem6901909 (_92163 : int) : (term222 _92163) = (term235 _92163).
Proof. exact (MK_COMB (@lem6901907 _92163) (@lem6901908 _92163)). Qed.
Lemma lem6901910 (_92163 : int) : (term221 _92163) = (term235 _92163).
Proof. exact (TRANS (@lem6901896 _92163) (@lem6901909 _92163)). Qed.
Lemma lem6901911 (_92163 : int) : (term220 _92163) = (term238 _92163).
Proof. exact (MK_COMB (@lem6901893 _92163) (@lem6901910 _92163)). Qed.
Lemma lem6901912 (_92163 : int) : (term219 _92163) = (term238 _92163).
Proof. exact (TRANS (@lem6901874 _92163) (@lem6901911 _92163)). Qed.
Lemma lem6901914 (y : int) (x : int) : (term217 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6901915 (_92164 : int) : (term219 _92164) = (term220 _92164).
Proof. exact (@lem6901914 _92164 _92164). Qed.
Lemma lem6901917 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901918 (_92164 : int) : (term221 _92164) = (term222 _92164).
Proof. exact (@lem6901917 (term223 _92164) _92164). Qed.
Lemma lem6901920 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6901921 (_92164 : int) : (term226 _92164) = (term227 _92164).
Proof. exact (@lem6901920 _92164 term228). Qed.
Lemma lem6901923 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901924 : term229 = term230.
Proof. exact (@lem6901923 term4). Qed.
Lemma lem6901925 (_92164 : int) : (term231 _92164) = (term231 _92164).
Proof. exact (eq_refl (term231 _92164)). Qed.
Lemma lem6901926 (_92164 : int) : (term227 _92164) = (term232 _92164).
Proof. exact (MK_COMB (@lem6901925 _92164) (@lem6901924)). Qed.
Lemma lem6901927 (_92164 : int) : (term226 _92164) = (term232 _92164).
Proof. exact (TRANS (@lem6901921 _92164) (@lem6901926 _92164)). Qed.
Lemma lem6901928 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901929 (_92164 : int) : (term233 _92164) = (term234 _92164).
Proof. exact (MK_COMB (@lem6901928) (@lem6901927 _92164)). Qed.
Lemma lem6901930 (_92164 : int) : (real_of_int _92164) = (real_of_int _92164).
Proof. exact (eq_refl (real_of_int _92164)). Qed.
Lemma lem6901931 (_92164 : int) : (term222 _92164) = (term235 _92164).
Proof. exact (MK_COMB (@lem6901929 _92164) (@lem6901930 _92164)). Qed.
Lemma lem6901932 (_92164 : int) : (term221 _92164) = (term235 _92164).
Proof. exact (TRANS (@lem6901918 _92164) (@lem6901931 _92164)). Qed.
Lemma lem6901933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6901934 (_92164 : int) : (term236 _92164) = (term237 _92164).
Proof. exact (MK_COMB (@lem6901933) (@lem6901932 _92164)). Qed.
Lemma lem6901936 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901937 (_92164 : int) : (term221 _92164) = (term222 _92164).
Proof. exact (@lem6901936 (term223 _92164) _92164). Qed.
Lemma lem6901939 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6901940 (_92164 : int) : (term226 _92164) = (term227 _92164).
Proof. exact (@lem6901939 _92164 term228). Qed.
Lemma lem6901942 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901943 : term229 = term230.
Proof. exact (@lem6901942 term4). Qed.
Lemma lem6901944 (_92164 : int) : (term231 _92164) = (term231 _92164).
Proof. exact (eq_refl (term231 _92164)). Qed.
Lemma lem6901945 (_92164 : int) : (term227 _92164) = (term232 _92164).
Proof. exact (MK_COMB (@lem6901944 _92164) (@lem6901943)). Qed.
Lemma lem6901946 (_92164 : int) : (term226 _92164) = (term232 _92164).
Proof. exact (TRANS (@lem6901940 _92164) (@lem6901945 _92164)). Qed.
Lemma lem6901947 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901948 (_92164 : int) : (term233 _92164) = (term234 _92164).
Proof. exact (MK_COMB (@lem6901947) (@lem6901946 _92164)). Qed.
Lemma lem6901949 (_92164 : int) : (real_of_int _92164) = (real_of_int _92164).
Proof. exact (eq_refl (real_of_int _92164)). Qed.
Lemma lem6901950 (_92164 : int) : (term222 _92164) = (term235 _92164).
Proof. exact (MK_COMB (@lem6901948 _92164) (@lem6901949 _92164)). Qed.
Lemma lem6901951 (_92164 : int) : (term221 _92164) = (term235 _92164).
Proof. exact (TRANS (@lem6901937 _92164) (@lem6901950 _92164)). Qed.
Lemma lem6901952 (_92164 : int) : (term220 _92164) = (term238 _92164).
Proof. exact (MK_COMB (@lem6901934 _92164) (@lem6901951 _92164)). Qed.
Lemma lem6901953 (_92164 : int) : (term219 _92164) = (term238 _92164).
Proof. exact (TRANS (@lem6901915 _92164) (@lem6901952 _92164)). Qed.
Lemma lem6901955 (y : int) (x : int) : (term217 x y) = (term218 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem6901956 (_92162 : int) : (term219 _92162) = (term220 _92162).
Proof. exact (@lem6901955 _92162 _92162). Qed.
Lemma lem6901958 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901959 (_92162 : int) : (term221 _92162) = (term222 _92162).
Proof. exact (@lem6901958 (term223 _92162) _92162). Qed.
Lemma lem6901961 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6901962 (_92162 : int) : (term226 _92162) = (term227 _92162).
Proof. exact (@lem6901961 _92162 term228). Qed.
Lemma lem6901964 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901965 : term229 = term230.
Proof. exact (@lem6901964 term4). Qed.
Lemma lem6901966 (_92162 : int) : (term231 _92162) = (term231 _92162).
Proof. exact (eq_refl (term231 _92162)). Qed.
Lemma lem6901967 (_92162 : int) : (term227 _92162) = (term232 _92162).
Proof. exact (MK_COMB (@lem6901966 _92162) (@lem6901965)). Qed.
Lemma lem6901968 (_92162 : int) : (term226 _92162) = (term232 _92162).
Proof. exact (TRANS (@lem6901962 _92162) (@lem6901967 _92162)). Qed.
Lemma lem6901969 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901970 (_92162 : int) : (term233 _92162) = (term234 _92162).
Proof. exact (MK_COMB (@lem6901969) (@lem6901968 _92162)). Qed.
Lemma lem6901971 (_92162 : int) : (real_of_int _92162) = (real_of_int _92162).
Proof. exact (eq_refl (real_of_int _92162)). Qed.
Lemma lem6901972 (_92162 : int) : (term222 _92162) = (term235 _92162).
Proof. exact (MK_COMB (@lem6901970 _92162) (@lem6901971 _92162)). Qed.
Lemma lem6901973 (_92162 : int) : (term221 _92162) = (term235 _92162).
Proof. exact (TRANS (@lem6901959 _92162) (@lem6901972 _92162)). Qed.
Lemma lem6901974 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6901975 (_92162 : int) : (term236 _92162) = (term237 _92162).
Proof. exact (MK_COMB (@lem6901974) (@lem6901973 _92162)). Qed.
Lemma lem6901977 (x : int) (y : int) : (int_le x y) = (term208 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem6901978 (_92162 : int) : (term221 _92162) = (term222 _92162).
Proof. exact (@lem6901977 (term223 _92162) _92162). Qed.
Lemma lem6901980 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem6901981 (_92162 : int) : (term226 _92162) = (term227 _92162).
Proof. exact (@lem6901980 _92162 term228). Qed.
Lemma lem6901983 (n : nat) : (term211 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem6901984 : term229 = term230.
Proof. exact (@lem6901983 term4). Qed.
Lemma lem6901985 (_92162 : int) : (term231 _92162) = (term231 _92162).
Proof. exact (eq_refl (term231 _92162)). Qed.
Lemma lem6901986 (_92162 : int) : (term227 _92162) = (term232 _92162).
Proof. exact (MK_COMB (@lem6901985 _92162) (@lem6901984)). Qed.
Lemma lem6901987 (_92162 : int) : (term226 _92162) = (term232 _92162).
Proof. exact (TRANS (@lem6901981 _92162) (@lem6901986 _92162)). Qed.
Lemma lem6901988 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6901989 (_92162 : int) : (term233 _92162) = (term234 _92162).
Proof. exact (MK_COMB (@lem6901988) (@lem6901987 _92162)). Qed.
Lemma lem6901990 (_92162 : int) : (real_of_int _92162) = (real_of_int _92162).
Proof. exact (eq_refl (real_of_int _92162)). Qed.
Lemma lem6901991 (_92162 : int) : (term222 _92162) = (term235 _92162).
Proof. exact (MK_COMB (@lem6901989 _92162) (@lem6901990 _92162)). Qed.
Lemma lem6901992 (_92162 : int) : (term221 _92162) = (term235 _92162).
Proof. exact (TRANS (@lem6901978 _92162) (@lem6901991 _92162)). Qed.
Lemma lem6901993 (_92162 : int) : (term220 _92162) = (term238 _92162).
Proof. exact (MK_COMB (@lem6901975 _92162) (@lem6901992 _92162)). Qed.
Lemma lem6901994 (_92162 : int) : (term219 _92162) = (term238 _92162).
Proof. exact (TRANS (@lem6901956 _92162) (@lem6901993 _92162)). Qed.
Lemma lem6901995 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6901996 (_92164 : int) : (term189 _92164) = (term239 _92164).
Proof. exact (MK_COMB (@lem6901995) (@lem6901953 _92164)). Qed.
Lemma lem6901997 (_92164 : int) (_92162 : int) : (term188 _92164 _92162) = (term240 _92164 _92162).
Proof. exact (MK_COMB (@lem6901996 _92164) (@lem6901994 _92162)). Qed.
Lemma lem6901998 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6901999 (_92163 : int) : (term189 _92163) = (term239 _92163).
Proof. exact (MK_COMB (@lem6901998) (@lem6901912 _92163)). Qed.
Lemma lem6902000 (_92163 : int) (_92164 : int) (_92162 : int) : (term191 _92163 _92164 _92162) = (term241 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6901999 _92163) (@lem6901997 _92164 _92162)). Qed.
Lemma lem6902001 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6902002 (_92164 : int) : (term194 _92164) = (term242 _92164).
Proof. exact (MK_COMB (@lem6902001) (@lem6901871 _92164)). Qed.
Lemma lem6902003 (_92163 : int) (_92164 : int) (_92162 : int) : (term196 _92163 _92164 _92162) = (term243 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6902002 _92164) (@lem6902000 _92163 _92164 _92162)). Qed.
Lemma lem6902004 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6902005 (_92163 : int) : (term194 _92163) = (term242 _92163).
Proof. exact (MK_COMB (@lem6902004) (@lem6901858 _92163)). Qed.
Lemma lem6902006 (_92163 : int) (_92164 : int) (_92162 : int) : (term201 _92163 _92164 _92162) = (term244 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6902005 _92163) (@lem6902003 _92163 _92164 _92162)). Qed.
Lemma lem6902007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6902008 (_92162 : int) : (term194 _92162) = (term242 _92162).
Proof. exact (MK_COMB (@lem6902007) (@lem6901845 _92162)). Qed.
Lemma lem6902009 (_92163 : int) (_92164 : int) (_92162 : int) : (term205 _92163 _92164 _92162) = (term245 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6902008 _92162) (@lem6902006 _92163 _92164 _92162)). Qed.
Lemma lem6902010 (_92163 : int) (_92164 : int) (_92162 : int) : (term206 _92163 _92164 _92162) = (term245 _92163 _92164 _92162).
Proof. exact (TRANS (@lem6901832 _92163 _92164 _92162) (@lem6902009 _92163 _92164 _92162)). Qed.
Lemma lem6902014 (t : Prop) : (term246 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem6902015 (_92163 : int) (_92164 : int) (_92162 : int) : (term247 _92163 _92164 _92162) = (term245 _92163 _92164 _92162).
Proof. exact (@lem6902014 (term245 _92163 _92164 _92162)). Qed.
Lemma lem6902025 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6902026 (_92163 : int) : (term238 _92163) = (term235 _92163).
Proof. exact (@lem6902025 (term235 _92163)). Qed.
Lemma lem6902027 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6902028 (_92163 : int) : (term239 _92163) = (term237 _92163).
Proof. exact (MK_COMB (@lem6902027) (@lem6902026 _92163)). Qed.
Lemma lem6902032 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6902033 (_92164 : int) : (term238 _92164) = (term235 _92164).
Proof. exact (@lem6902032 (term235 _92164)). Qed.
Lemma lem6902034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6902035 (_92164 : int) : (term239 _92164) = (term237 _92164).
Proof. exact (MK_COMB (@lem6902034) (@lem6902033 _92164)). Qed.
Lemma lem6902037 (t : Prop) : (t \/ t) = t.
Proof. exact (proj2 (@lem16485 t)). Qed.
Lemma lem6902038 (_92162 : int) : (term238 _92162) = (term235 _92162).
Proof. exact (@lem6902037 (term235 _92162)). Qed.
Lemma lem6902039 (_92164 : int) (_92162 : int) : (term240 _92164 _92162) = (term248 _92164 _92162).
Proof. exact (MK_COMB (@lem6902035 _92164) (@lem6902038 _92162)). Qed.
Lemma lem6902042 (_92163 : int) (_92164 : int) (_92162 : int) : (term241 _92163 _92164 _92162) = (term249 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6902028 _92163) (@lem6902039 _92164 _92162)). Qed.
Lemma lem6902045 (_92164 : int) : (term242 _92164) = (term242 _92164).
Proof. exact (eq_refl (term242 _92164)). Qed.
Lemma lem6902046 (_92163 : int) (_92164 : int) (_92162 : int) : (term243 _92163 _92164 _92162) = (term250 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6902045 _92164) (@lem6902042 _92163 _92164 _92162)). Qed.
Lemma lem6902049 (_92163 : int) : (term242 _92163) = (term242 _92163).
Proof. exact (eq_refl (term242 _92163)). Qed.
Lemma lem6902050 (_92163 : int) (_92164 : int) (_92162 : int) : (term244 _92163 _92164 _92162) = (term251 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6902049 _92163) (@lem6902046 _92163 _92164 _92162)). Qed.
Lemma lem6902053 (_92162 : int) : (term242 _92162) = (term242 _92162).
Proof. exact (eq_refl (term242 _92162)). Qed.
Lemma lem6902054 (_92163 : int) (_92164 : int) (_92162 : int) : (term245 _92163 _92164 _92162) = (term252 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6902053 _92162) (@lem6902050 _92163 _92164 _92162)). Qed.
Lemma lem6902102 (_92163 : int) (_92164 : int) (_92162 : int) : (term247 _92163 _92164 _92162) = (term252 _92163 _92164 _92162).
Proof. exact (TRANS (@lem6902015 _92163 _92164 _92162) (@lem6902054 _92163 _92164 _92162)). Qed.
Lemma lem6902103 (_92162 : int) : (term216 _92162) = (term253 _92162).
Proof. exact (@lem1988287 (real_of_int _92162) term213). Qed.
Lemma lem6902109 (_92162 : int) : (term254 _92162) = (term255 _92162).
Proof. exact (@lem1982792 (real_of_int _92162) term213). Qed.
Lemma lem6902111 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902112 : term213 = term257.
Proof. exact (@lem6902111 (NUMERAL 0)). Qed.
Lemma lem6902114 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902115 : term260 = term261.
Proof. exact (@lem6902114 term4). Qed.
Lemma lem6902116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902117 : term262 = term263.
Proof. exact (MK_COMB (@lem6902116) (@lem6902115)). Qed.
Lemma lem6902118 : term264 = term265.
Proof. exact (MK_COMB (@lem6902117) (@lem6902112)). Qed.
Lemma lem6902119 : term265 = term266.
Proof. exact (@lem1981613 term260 term213 term230 term230). Qed.
Lemma lem6902121 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902122 : term269 = term270.
Proof. exact (@lem6902121 term4 term4). Qed.
Lemma lem6902123 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902124 : term272 = term4.
Proof. exact (EQ_MP (@lem6902123) (@lem940073)). Qed.
Lemma lem6902125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902126 : term270 = term230.
Proof. exact (MK_COMB (@lem6902125) (@lem6902124)). Qed.
Lemma lem6902127 : term269 = term230.
Proof. exact (TRANS (@lem6902122) (@lem6902126)). Qed.
Lemma lem6902129 (x : nat) : (term273 x) = term213.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6902130 : term264 = term213.
Proof. exact (@lem6902129 term4). Qed.
Lemma lem6902131 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6902132 : term274 = term275.
Proof. exact (MK_COMB (@lem6902131) (@lem6902130)). Qed.
Lemma lem6902133 : term266 = term257.
Proof. exact (MK_COMB (@lem6902132) (@lem6902127)). Qed.
Lemma lem6902134 : term265 = term257.
Proof. exact (TRANS (@lem6902119) (@lem6902133)). Qed.
Lemma lem6902135 : term264 = term257.
Proof. exact (TRANS (@lem6902118) (@lem6902134)). Qed.
Lemma lem6902137 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6902138 : term257 = term213.
Proof. exact (@lem6902137 term213). Qed.
Lemma lem6902139 : term264 = term213.
Proof. exact (TRANS (@lem6902135) (@lem6902138)). Qed.
Lemma lem6902140 (_92162 : int) : (term231 _92162) = (term231 _92162).
Proof. exact (eq_refl (term231 _92162)). Qed.
Lemma lem6902141 (_92162 : int) : (term255 _92162) = (term277 _92162).
Proof. exact (MK_COMB (@lem6902140 _92162) (@lem6902139)). Qed.
Lemma lem6902142 (_92162 : int) : (term277 _92162) = (real_of_int _92162).
Proof. exact (@lem1982723 (real_of_int _92162)). Qed.
Lemma lem6902143 (_92162 : int) : (term255 _92162) = (real_of_int _92162).
Proof. exact (TRANS (@lem6902141 _92162) (@lem6902142 _92162)). Qed.
Lemma lem6902145 (_92162 : int) : (term254 _92162) = (real_of_int _92162).
Proof. exact (TRANS (@lem6902109 _92162) (@lem6902143 _92162)). Qed.
Lemma lem6902146 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6902147 (_92162 : int) : (term278 _92162) = (term279 _92162).
Proof. exact (MK_COMB (@lem6902146) (@lem6902145 _92162)). Qed.
Lemma lem6902148 : term213 = term213.
Proof. exact (eq_refl term213). Qed.
Lemma lem6902149 (_92162 : int) : (term253 _92162) = (term280 _92162).
Proof. exact (MK_COMB (@lem6902147 _92162) (@lem6902148)). Qed.
Lemma lem6902150 (_92162 : int) : (term216 _92162) = (term280 _92162).
Proof. exact (TRANS (@lem6902103 _92162) (@lem6902149 _92162)). Qed.
Lemma lem6902151 (_92163 : int) : (term216 _92163) = (term253 _92163).
Proof. exact (@lem1988287 (real_of_int _92163) term213). Qed.
Lemma lem6902157 (_92163 : int) : (term254 _92163) = (term255 _92163).
Proof. exact (@lem1982792 (real_of_int _92163) term213). Qed.
Lemma lem6902159 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902160 : term213 = term257.
Proof. exact (@lem6902159 (NUMERAL 0)). Qed.
Lemma lem6902162 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902163 : term260 = term261.
Proof. exact (@lem6902162 term4). Qed.
Lemma lem6902164 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902165 : term262 = term263.
Proof. exact (MK_COMB (@lem6902164) (@lem6902163)). Qed.
Lemma lem6902166 : term264 = term265.
Proof. exact (MK_COMB (@lem6902165) (@lem6902160)). Qed.
Lemma lem6902167 : term265 = term266.
Proof. exact (@lem1981613 term260 term213 term230 term230). Qed.
Lemma lem6902169 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902170 : term269 = term270.
Proof. exact (@lem6902169 term4 term4). Qed.
Lemma lem6902171 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902172 : term272 = term4.
Proof. exact (EQ_MP (@lem6902171) (@lem940073)). Qed.
Lemma lem6902173 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902174 : term270 = term230.
Proof. exact (MK_COMB (@lem6902173) (@lem6902172)). Qed.
Lemma lem6902175 : term269 = term230.
Proof. exact (TRANS (@lem6902170) (@lem6902174)). Qed.
Lemma lem6902177 (x : nat) : (term273 x) = term213.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6902178 : term264 = term213.
Proof. exact (@lem6902177 term4). Qed.
Lemma lem6902179 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6902180 : term274 = term275.
Proof. exact (MK_COMB (@lem6902179) (@lem6902178)). Qed.
Lemma lem6902181 : term266 = term257.
Proof. exact (MK_COMB (@lem6902180) (@lem6902175)). Qed.
Lemma lem6902182 : term265 = term257.
Proof. exact (TRANS (@lem6902167) (@lem6902181)). Qed.
Lemma lem6902183 : term264 = term257.
Proof. exact (TRANS (@lem6902166) (@lem6902182)). Qed.
Lemma lem6902185 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6902186 : term257 = term213.
Proof. exact (@lem6902185 term213). Qed.
Lemma lem6902187 : term264 = term213.
Proof. exact (TRANS (@lem6902183) (@lem6902186)). Qed.
Lemma lem6902188 (_92163 : int) : (term231 _92163) = (term231 _92163).
Proof. exact (eq_refl (term231 _92163)). Qed.
Lemma lem6902189 (_92163 : int) : (term255 _92163) = (term277 _92163).
Proof. exact (MK_COMB (@lem6902188 _92163) (@lem6902187)). Qed.
Lemma lem6902190 (_92163 : int) : (term277 _92163) = (real_of_int _92163).
Proof. exact (@lem1982723 (real_of_int _92163)). Qed.
Lemma lem6902191 (_92163 : int) : (term255 _92163) = (real_of_int _92163).
Proof. exact (TRANS (@lem6902189 _92163) (@lem6902190 _92163)). Qed.
Lemma lem6902193 (_92163 : int) : (term254 _92163) = (real_of_int _92163).
Proof. exact (TRANS (@lem6902157 _92163) (@lem6902191 _92163)). Qed.
Lemma lem6902194 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6902195 (_92163 : int) : (term278 _92163) = (term279 _92163).
Proof. exact (MK_COMB (@lem6902194) (@lem6902193 _92163)). Qed.
Lemma lem6902196 : term213 = term213.
Proof. exact (eq_refl term213). Qed.
Lemma lem6902197 (_92163 : int) : (term253 _92163) = (term280 _92163).
Proof. exact (MK_COMB (@lem6902195 _92163) (@lem6902196)). Qed.
Lemma lem6902198 (_92163 : int) : (term216 _92163) = (term280 _92163).
Proof. exact (TRANS (@lem6902151 _92163) (@lem6902197 _92163)). Qed.
Lemma lem6902199 (_92164 : int) : (term216 _92164) = (term253 _92164).
Proof. exact (@lem1988287 (real_of_int _92164) term213). Qed.
Lemma lem6902205 (_92164 : int) : (term254 _92164) = (term255 _92164).
Proof. exact (@lem1982792 (real_of_int _92164) term213). Qed.
Lemma lem6902207 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902208 : term213 = term257.
Proof. exact (@lem6902207 (NUMERAL 0)). Qed.
Lemma lem6902210 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902211 : term260 = term261.
Proof. exact (@lem6902210 term4). Qed.
Lemma lem6902212 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902213 : term262 = term263.
Proof. exact (MK_COMB (@lem6902212) (@lem6902211)). Qed.
Lemma lem6902214 : term264 = term265.
Proof. exact (MK_COMB (@lem6902213) (@lem6902208)). Qed.
Lemma lem6902215 : term265 = term266.
Proof. exact (@lem1981613 term260 term213 term230 term230). Qed.
Lemma lem6902217 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902218 : term269 = term270.
Proof. exact (@lem6902217 term4 term4). Qed.
Lemma lem6902219 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902220 : term272 = term4.
Proof. exact (EQ_MP (@lem6902219) (@lem940073)). Qed.
Lemma lem6902221 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902222 : term270 = term230.
Proof. exact (MK_COMB (@lem6902221) (@lem6902220)). Qed.
Lemma lem6902223 : term269 = term230.
Proof. exact (TRANS (@lem6902218) (@lem6902222)). Qed.
Lemma lem6902225 (x : nat) : (term273 x) = term213.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem6902226 : term264 = term213.
Proof. exact (@lem6902225 term4). Qed.
Lemma lem6902227 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6902228 : term274 = term275.
Proof. exact (MK_COMB (@lem6902227) (@lem6902226)). Qed.
Lemma lem6902229 : term266 = term257.
Proof. exact (MK_COMB (@lem6902228) (@lem6902223)). Qed.
Lemma lem6902230 : term265 = term257.
Proof. exact (TRANS (@lem6902215) (@lem6902229)). Qed.
Lemma lem6902231 : term264 = term257.
Proof. exact (TRANS (@lem6902214) (@lem6902230)). Qed.
Lemma lem6902233 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6902234 : term257 = term213.
Proof. exact (@lem6902233 term213). Qed.
Lemma lem6902235 : term264 = term213.
Proof. exact (TRANS (@lem6902231) (@lem6902234)). Qed.
Lemma lem6902236 (_92164 : int) : (term231 _92164) = (term231 _92164).
Proof. exact (eq_refl (term231 _92164)). Qed.
Lemma lem6902237 (_92164 : int) : (term255 _92164) = (term277 _92164).
Proof. exact (MK_COMB (@lem6902236 _92164) (@lem6902235)). Qed.
Lemma lem6902238 (_92164 : int) : (term277 _92164) = (real_of_int _92164).
Proof. exact (@lem1982723 (real_of_int _92164)). Qed.
Lemma lem6902239 (_92164 : int) : (term255 _92164) = (real_of_int _92164).
Proof. exact (TRANS (@lem6902237 _92164) (@lem6902238 _92164)). Qed.
Lemma lem6902241 (_92164 : int) : (term254 _92164) = (real_of_int _92164).
Proof. exact (TRANS (@lem6902205 _92164) (@lem6902239 _92164)). Qed.
Lemma lem6902242 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6902243 (_92164 : int) : (term278 _92164) = (term279 _92164).
Proof. exact (MK_COMB (@lem6902242) (@lem6902241 _92164)). Qed.
Lemma lem6902244 : term213 = term213.
Proof. exact (eq_refl term213). Qed.
Lemma lem6902245 (_92164 : int) : (term253 _92164) = (term280 _92164).
Proof. exact (MK_COMB (@lem6902243 _92164) (@lem6902244)). Qed.
Lemma lem6902246 (_92164 : int) : (term216 _92164) = (term280 _92164).
Proof. exact (TRANS (@lem6902199 _92164) (@lem6902245 _92164)). Qed.
Lemma lem6902247 (_92163 : int) : (term235 _92163) = (term281 _92163).
Proof. exact (@lem1988287 (real_of_int _92163) (term232 _92163)). Qed.
Lemma lem6902259 (_92163 : int) : (term282 _92163) = (term283 _92163).
Proof. exact (@lem1982792 (real_of_int _92163) (term232 _92163)). Qed.
Lemma lem6902260 (_92163 : int) : (term284 _92163) = (term285 _92163).
Proof. exact (@lem1982781 (real_of_int _92163) term260 term230). Qed.
Lemma lem6902262 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902263 : term230 = term286.
Proof. exact (@lem6902262 term4). Qed.
Lemma lem6902265 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902266 : term260 = term261.
Proof. exact (@lem6902265 term4). Qed.
Lemma lem6902267 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902268 : term262 = term263.
Proof. exact (MK_COMB (@lem6902267) (@lem6902266)). Qed.
Lemma lem6902269 : term287 = term288.
Proof. exact (MK_COMB (@lem6902268) (@lem6902263)). Qed.
Lemma lem6902270 : term288 = term289.
Proof. exact (@lem1981613 term260 term230 term230 term230). Qed.
Lemma lem6902272 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902273 : term269 = term270.
Proof. exact (@lem6902272 term4 term4). Qed.
Lemma lem6902274 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902275 : term272 = term4.
Proof. exact (EQ_MP (@lem6902274) (@lem940073)). Qed.
Lemma lem6902276 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902277 : term270 = term230.
Proof. exact (MK_COMB (@lem6902276) (@lem6902275)). Qed.
Lemma lem6902278 : term269 = term230.
Proof. exact (TRANS (@lem6902273) (@lem6902277)). Qed.
Lemma lem6902280 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6902281 : term287 = term292.
Proof. exact (@lem6902280 term4 term4). Qed.
Lemma lem6902282 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902283 : term272 = term4.
Proof. exact (EQ_MP (@lem6902282) (@lem940073)). Qed.
Lemma lem6902284 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902285 : term270 = term230.
Proof. exact (MK_COMB (@lem6902284) (@lem6902283)). Qed.
Lemma lem6902286 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6902287 : term292 = term260.
Proof. exact (MK_COMB (@lem6902286) (@lem6902285)). Qed.
Lemma lem6902288 : term287 = term260.
Proof. exact (TRANS (@lem6902281) (@lem6902287)). Qed.
Lemma lem6902289 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6902290 : term293 = term294.
Proof. exact (MK_COMB (@lem6902289) (@lem6902288)). Qed.
Lemma lem6902291 : term289 = term261.
Proof. exact (MK_COMB (@lem6902290) (@lem6902278)). Qed.
Lemma lem6902292 : term288 = term261.
Proof. exact (TRANS (@lem6902270) (@lem6902291)). Qed.
Lemma lem6902293 : term287 = term261.
Proof. exact (TRANS (@lem6902269) (@lem6902292)). Qed.
Lemma lem6902295 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6902296 : term261 = term260.
Proof. exact (@lem6902295 term260). Qed.
Lemma lem6902297 : term287 = term260.
Proof. exact (TRANS (@lem6902293) (@lem6902296)). Qed.
Lemma lem6902300 (_92163 : int) : (term295 _92163) = (term295 _92163).
Proof. exact (eq_refl (term295 _92163)). Qed.
Lemma lem6902301 (_92163 : int) : (term285 _92163) = (term296 _92163).
Proof. exact (MK_COMB (@lem6902300 _92163) (@lem6902297)). Qed.
Lemma lem6902302 (_92163 : int) : (term284 _92163) = (term296 _92163).
Proof. exact (TRANS (@lem6902260 _92163) (@lem6902301 _92163)). Qed.
Lemma lem6902303 (_92163 : int) : (term231 _92163) = (term231 _92163).
Proof. exact (eq_refl (term231 _92163)). Qed.
Lemma lem6902304 (_92163 : int) : (term283 _92163) = (term297 _92163).
Proof. exact (MK_COMB (@lem6902303 _92163) (@lem6902302 _92163)). Qed.
Lemma lem6902305 (_92163 : int) : (term297 _92163) = (term298 _92163).
Proof. exact (@lem1982763 (real_of_int _92163) (term299 _92163) term260). Qed.
Lemma lem6902306 (_92163 : int) : (term300 _92163) = (term301 _92163).
Proof. exact (@lem1982715 term260 (real_of_int _92163)). Qed.
Lemma lem6902308 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902309 : term230 = term286.
Proof. exact (@lem6902308 term4). Qed.
Lemma lem6902311 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902312 : term260 = term261.
Proof. exact (@lem6902311 term4). Qed.
Lemma lem6902313 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902314 : term302 = term303.
Proof. exact (MK_COMB (@lem6902313) (@lem6902312)). Qed.
Lemma lem6902315 : term304 = term305.
Proof. exact (MK_COMB (@lem6902314) (@lem6902309)). Qed.
Lemma lem6902316 : term306.
Proof. exact (@lem1981473 term260 term230 term230 term230 term213 term230). Qed.
Lemma lem6902318 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902319 : term308 = term309.
Proof. exact (@lem6902318 (NUMERAL 0) term4). Qed.
Lemma lem6902320 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902321 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902322 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902321 h1) (fun h1 : term309 = True => @lem6902320)). Qed.
Lemma lem6902323 : term309 = True.
Proof. exact (EQ_MP (@lem6902322) (@lem6902320)). Qed.
Lemma lem6902324 : term308 = True.
Proof. exact (TRANS (@lem6902319) (@lem6902323)). Qed.
Lemma lem6902325 : True = term308.
Proof. exact (SYM (@lem6902324)). Qed.
Lemma lem6902326 : term308.
Proof. exact (EQ_MP (@lem6902325) (@lem0)). Qed.
Lemma lem6902327 : term311.
Proof. exact (@lem6902316 (@lem6902326)). Qed.
Lemma lem6902329 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902330 : term308 = term309.
Proof. exact (@lem6902329 (NUMERAL 0) term4). Qed.
Lemma lem6902331 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902332 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902333 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902332 h1) (fun h1 : term309 = True => @lem6902331)). Qed.
Lemma lem6902334 : term309 = True.
Proof. exact (EQ_MP (@lem6902333) (@lem6902331)). Qed.
Lemma lem6902335 : term308 = True.
Proof. exact (TRANS (@lem6902330) (@lem6902334)). Qed.
Lemma lem6902336 : True = term308.
Proof. exact (SYM (@lem6902335)). Qed.
Lemma lem6902337 : term308.
Proof. exact (EQ_MP (@lem6902336) (@lem0)). Qed.
Lemma lem6902338 : term312.
Proof. exact (@lem6902327 (@lem6902337)). Qed.
Lemma lem6902340 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902341 : term308 = term309.
Proof. exact (@lem6902340 (NUMERAL 0) term4). Qed.
Lemma lem6902342 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902343 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902344 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902343 h1) (fun h1 : term309 = True => @lem6902342)). Qed.
Lemma lem6902345 : term309 = True.
Proof. exact (EQ_MP (@lem6902344) (@lem6902342)). Qed.
Lemma lem6902346 : term308 = True.
Proof. exact (TRANS (@lem6902341) (@lem6902345)). Qed.
Lemma lem6902347 : True = term308.
Proof. exact (SYM (@lem6902346)). Qed.
Lemma lem6902348 : term308.
Proof. exact (EQ_MP (@lem6902347) (@lem0)). Qed.
Lemma lem6902349 : term313.
Proof. exact (@lem6902338 (@lem6902348)). Qed.
Lemma lem6902351 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902352 : term269 = term270.
Proof. exact (@lem6902351 term4 term4). Qed.
Lemma lem6902353 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902354 : term272 = term4.
Proof. exact (EQ_MP (@lem6902353) (@lem940073)). Qed.
Lemma lem6902355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902356 : term270 = term230.
Proof. exact (MK_COMB (@lem6902355) (@lem6902354)). Qed.
Lemma lem6902357 : term269 = term230.
Proof. exact (TRANS (@lem6902352) (@lem6902356)). Qed.
Lemma lem6902359 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6902360 : term287 = term292.
Proof. exact (@lem6902359 term4 term4). Qed.
Lemma lem6902361 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902362 : term272 = term4.
Proof. exact (EQ_MP (@lem6902361) (@lem940073)). Qed.
Lemma lem6902363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902364 : term270 = term230.
Proof. exact (MK_COMB (@lem6902363) (@lem6902362)). Qed.
Lemma lem6902365 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6902366 : term292 = term260.
Proof. exact (MK_COMB (@lem6902365) (@lem6902364)). Qed.
Lemma lem6902367 : term287 = term260.
Proof. exact (TRANS (@lem6902360) (@lem6902366)). Qed.
Lemma lem6902368 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902369 : term314 = term302.
Proof. exact (MK_COMB (@lem6902368) (@lem6902367)). Qed.
Lemma lem6902370 : term315 = term304.
Proof. exact (MK_COMB (@lem6902369) (@lem6902357)). Qed.
Lemma lem6902372 (m : nat) : (term316 m) = term213.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6902373 : term304 = term213.
Proof. exact (@lem6902372 term4). Qed.
Lemma lem6902374 : term315 = term213.
Proof. exact (TRANS (@lem6902370) (@lem6902373)). Qed.
Lemma lem6902375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902376 : term317 = term318.
Proof. exact (MK_COMB (@lem6902375) (@lem6902374)). Qed.
Lemma lem6902377 : term230 = term230.
Proof. exact (eq_refl term230). Qed.
Lemma lem6902378 : term319 = term320.
Proof. exact (MK_COMB (@lem6902376) (@lem6902377)). Qed.
Lemma lem6902380 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6902381 : term320 = term213.
Proof. exact (@lem6902380 term4). Qed.
Lemma lem6902382 : term319 = term213.
Proof. exact (TRANS (@lem6902378) (@lem6902381)). Qed.
Lemma lem6902384 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902385 : term269 = term270.
Proof. exact (@lem6902384 term4 term4). Qed.
Lemma lem6902386 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902387 : term272 = term4.
Proof. exact (EQ_MP (@lem6902386) (@lem940073)). Qed.
Lemma lem6902388 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902389 : term270 = term230.
Proof. exact (MK_COMB (@lem6902388) (@lem6902387)). Qed.
Lemma lem6902390 : term269 = term230.
Proof. exact (TRANS (@lem6902385) (@lem6902389)). Qed.
Lemma lem6902391 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem6902392 : term322 = term320.
Proof. exact (MK_COMB (@lem6902391) (@lem6902390)). Qed.
Lemma lem6902394 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6902395 : term320 = term213.
Proof. exact (@lem6902394 term4). Qed.
Lemma lem6902396 : term322 = term213.
Proof. exact (TRANS (@lem6902392) (@lem6902395)). Qed.
Lemma lem6902397 : term213 = term322.
Proof. exact (SYM (@lem6902396)). Qed.
Lemma lem6902398 : term319 = term322.
Proof. exact (TRANS (@lem6902382) (@lem6902397)). Qed.
Lemma lem6902399 : term305 = term257.
Proof. exact (@lem6902349 (@lem6902398)). Qed.
Lemma lem6902400 : term304 = term257.
Proof. exact (TRANS (@lem6902315) (@lem6902399)). Qed.
Lemma lem6902402 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6902403 : term257 = term213.
Proof. exact (@lem6902402 term213). Qed.
Lemma lem6902404 : term304 = term213.
Proof. exact (TRANS (@lem6902400) (@lem6902403)). Qed.
Lemma lem6902405 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902406 : term323 = term318.
Proof. exact (MK_COMB (@lem6902405) (@lem6902404)). Qed.
Lemma lem6902407 (_92163 : int) : (real_of_int _92163) = (real_of_int _92163).
Proof. exact (eq_refl (real_of_int _92163)). Qed.
Lemma lem6902408 (_92163 : int) : (term301 _92163) = (term324 _92163).
Proof. exact (MK_COMB (@lem6902406) (@lem6902407 _92163)). Qed.
Lemma lem6902409 (_92163 : int) : (term300 _92163) = (term324 _92163).
Proof. exact (TRANS (@lem6902306 _92163) (@lem6902408 _92163)). Qed.
Lemma lem6902410 (_92163 : int) : (term324 _92163) = term213.
Proof. exact (@lem1982719 (real_of_int _92163)). Qed.
Lemma lem6902411 (_92163 : int) : (term300 _92163) = term213.
Proof. exact (TRANS (@lem6902409 _92163) (@lem6902410 _92163)). Qed.
Lemma lem6902412 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902413 (_92163 : int) : (term325 _92163) = term326.
Proof. exact (MK_COMB (@lem6902412) (@lem6902411 _92163)). Qed.
Lemma lem6902414 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem6902415 (_92163 : int) : (term298 _92163) = term327.
Proof. exact (MK_COMB (@lem6902413 _92163) (@lem6902414)). Qed.
Lemma lem6902416 (_92163 : int) : (term297 _92163) = term327.
Proof. exact (TRANS (@lem6902305 _92163) (@lem6902415 _92163)). Qed.
Lemma lem6902417 : term327 = term260.
Proof. exact (@lem1982721 term260). Qed.
Lemma lem6902418 (_92163 : int) : (term297 _92163) = term260.
Proof. exact (TRANS (@lem6902416 _92163) (@lem6902417)). Qed.
Lemma lem6902419 (_92163 : int) : (term283 _92163) = term260.
Proof. exact (TRANS (@lem6902304 _92163) (@lem6902418 _92163)). Qed.
Lemma lem6902421 (_92163 : int) : (term282 _92163) = term260.
Proof. exact (TRANS (@lem6902259 _92163) (@lem6902419 _92163)). Qed.
Lemma lem6902422 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6902423 (_92163 : int) : (term328 _92163) = term329.
Proof. exact (MK_COMB (@lem6902422) (@lem6902421 _92163)). Qed.
Lemma lem6902424 : term213 = term213.
Proof. exact (eq_refl term213). Qed.
Lemma lem6902425 (_92163 : int) : (term281 _92163) = term330.
Proof. exact (MK_COMB (@lem6902423 _92163) (@lem6902424)). Qed.
Lemma lem6902426 (_92163 : int) : (term235 _92163) = term330.
Proof. exact (TRANS (@lem6902247 _92163) (@lem6902425 _92163)). Qed.
Lemma lem6902427 (_92164 : int) : (term235 _92164) = (term281 _92164).
Proof. exact (@lem1988287 (real_of_int _92164) (term232 _92164)). Qed.
Lemma lem6902439 (_92164 : int) : (term282 _92164) = (term283 _92164).
Proof. exact (@lem1982792 (real_of_int _92164) (term232 _92164)). Qed.
Lemma lem6902440 (_92164 : int) : (term284 _92164) = (term285 _92164).
Proof. exact (@lem1982781 (real_of_int _92164) term260 term230). Qed.
Lemma lem6902442 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902443 : term230 = term286.
Proof. exact (@lem6902442 term4). Qed.
Lemma lem6902445 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902446 : term260 = term261.
Proof. exact (@lem6902445 term4). Qed.
Lemma lem6902447 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902448 : term262 = term263.
Proof. exact (MK_COMB (@lem6902447) (@lem6902446)). Qed.
Lemma lem6902449 : term287 = term288.
Proof. exact (MK_COMB (@lem6902448) (@lem6902443)). Qed.
Lemma lem6902450 : term288 = term289.
Proof. exact (@lem1981613 term260 term230 term230 term230). Qed.
Lemma lem6902452 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902453 : term269 = term270.
Proof. exact (@lem6902452 term4 term4). Qed.
Lemma lem6902454 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902455 : term272 = term4.
Proof. exact (EQ_MP (@lem6902454) (@lem940073)). Qed.
Lemma lem6902456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902457 : term270 = term230.
Proof. exact (MK_COMB (@lem6902456) (@lem6902455)). Qed.
Lemma lem6902458 : term269 = term230.
Proof. exact (TRANS (@lem6902453) (@lem6902457)). Qed.
Lemma lem6902460 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6902461 : term287 = term292.
Proof. exact (@lem6902460 term4 term4). Qed.
Lemma lem6902462 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902463 : term272 = term4.
Proof. exact (EQ_MP (@lem6902462) (@lem940073)). Qed.
Lemma lem6902464 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902465 : term270 = term230.
Proof. exact (MK_COMB (@lem6902464) (@lem6902463)). Qed.
Lemma lem6902466 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6902467 : term292 = term260.
Proof. exact (MK_COMB (@lem6902466) (@lem6902465)). Qed.
Lemma lem6902468 : term287 = term260.
Proof. exact (TRANS (@lem6902461) (@lem6902467)). Qed.
Lemma lem6902469 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6902470 : term293 = term294.
Proof. exact (MK_COMB (@lem6902469) (@lem6902468)). Qed.
Lemma lem6902471 : term289 = term261.
Proof. exact (MK_COMB (@lem6902470) (@lem6902458)). Qed.
Lemma lem6902472 : term288 = term261.
Proof. exact (TRANS (@lem6902450) (@lem6902471)). Qed.
Lemma lem6902473 : term287 = term261.
Proof. exact (TRANS (@lem6902449) (@lem6902472)). Qed.
Lemma lem6902475 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6902476 : term261 = term260.
Proof. exact (@lem6902475 term260). Qed.
Lemma lem6902477 : term287 = term260.
Proof. exact (TRANS (@lem6902473) (@lem6902476)). Qed.
Lemma lem6902480 (_92164 : int) : (term295 _92164) = (term295 _92164).
Proof. exact (eq_refl (term295 _92164)). Qed.
Lemma lem6902481 (_92164 : int) : (term285 _92164) = (term296 _92164).
Proof. exact (MK_COMB (@lem6902480 _92164) (@lem6902477)). Qed.
Lemma lem6902482 (_92164 : int) : (term284 _92164) = (term296 _92164).
Proof. exact (TRANS (@lem6902440 _92164) (@lem6902481 _92164)). Qed.
Lemma lem6902483 (_92164 : int) : (term231 _92164) = (term231 _92164).
Proof. exact (eq_refl (term231 _92164)). Qed.
Lemma lem6902484 (_92164 : int) : (term283 _92164) = (term297 _92164).
Proof. exact (MK_COMB (@lem6902483 _92164) (@lem6902482 _92164)). Qed.
Lemma lem6902485 (_92164 : int) : (term297 _92164) = (term298 _92164).
Proof. exact (@lem1982763 (real_of_int _92164) (term299 _92164) term260). Qed.
Lemma lem6902486 (_92164 : int) : (term300 _92164) = (term301 _92164).
Proof. exact (@lem1982715 term260 (real_of_int _92164)). Qed.
Lemma lem6902488 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902489 : term230 = term286.
Proof. exact (@lem6902488 term4). Qed.
Lemma lem6902491 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902492 : term260 = term261.
Proof. exact (@lem6902491 term4). Qed.
Lemma lem6902493 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902494 : term302 = term303.
Proof. exact (MK_COMB (@lem6902493) (@lem6902492)). Qed.
Lemma lem6902495 : term304 = term305.
Proof. exact (MK_COMB (@lem6902494) (@lem6902489)). Qed.
Lemma lem6902496 : term306.
Proof. exact (@lem1981473 term260 term230 term230 term230 term213 term230). Qed.
Lemma lem6902498 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902499 : term308 = term309.
Proof. exact (@lem6902498 (NUMERAL 0) term4). Qed.
Lemma lem6902500 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902501 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902502 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902501 h1) (fun h1 : term309 = True => @lem6902500)). Qed.
Lemma lem6902503 : term309 = True.
Proof. exact (EQ_MP (@lem6902502) (@lem6902500)). Qed.
Lemma lem6902504 : term308 = True.
Proof. exact (TRANS (@lem6902499) (@lem6902503)). Qed.
Lemma lem6902505 : True = term308.
Proof. exact (SYM (@lem6902504)). Qed.
Lemma lem6902506 : term308.
Proof. exact (EQ_MP (@lem6902505) (@lem0)). Qed.
Lemma lem6902507 : term311.
Proof. exact (@lem6902496 (@lem6902506)). Qed.
Lemma lem6902509 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902510 : term308 = term309.
Proof. exact (@lem6902509 (NUMERAL 0) term4). Qed.
Lemma lem6902511 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902512 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902513 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902512 h1) (fun h1 : term309 = True => @lem6902511)). Qed.
Lemma lem6902514 : term309 = True.
Proof. exact (EQ_MP (@lem6902513) (@lem6902511)). Qed.
Lemma lem6902515 : term308 = True.
Proof. exact (TRANS (@lem6902510) (@lem6902514)). Qed.
Lemma lem6902516 : True = term308.
Proof. exact (SYM (@lem6902515)). Qed.
Lemma lem6902517 : term308.
Proof. exact (EQ_MP (@lem6902516) (@lem0)). Qed.
Lemma lem6902518 : term312.
Proof. exact (@lem6902507 (@lem6902517)). Qed.
Lemma lem6902520 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902521 : term308 = term309.
Proof. exact (@lem6902520 (NUMERAL 0) term4). Qed.
Lemma lem6902522 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902523 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902524 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902523 h1) (fun h1 : term309 = True => @lem6902522)). Qed.
Lemma lem6902525 : term309 = True.
Proof. exact (EQ_MP (@lem6902524) (@lem6902522)). Qed.
Lemma lem6902526 : term308 = True.
Proof. exact (TRANS (@lem6902521) (@lem6902525)). Qed.
Lemma lem6902527 : True = term308.
Proof. exact (SYM (@lem6902526)). Qed.
Lemma lem6902528 : term308.
Proof. exact (EQ_MP (@lem6902527) (@lem0)). Qed.
Lemma lem6902529 : term313.
Proof. exact (@lem6902518 (@lem6902528)). Qed.
Lemma lem6902531 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902532 : term269 = term270.
Proof. exact (@lem6902531 term4 term4). Qed.
Lemma lem6902533 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902534 : term272 = term4.
Proof. exact (EQ_MP (@lem6902533) (@lem940073)). Qed.
Lemma lem6902535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902536 : term270 = term230.
Proof. exact (MK_COMB (@lem6902535) (@lem6902534)). Qed.
Lemma lem6902537 : term269 = term230.
Proof. exact (TRANS (@lem6902532) (@lem6902536)). Qed.
Lemma lem6902539 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6902540 : term287 = term292.
Proof. exact (@lem6902539 term4 term4). Qed.
Lemma lem6902541 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902542 : term272 = term4.
Proof. exact (EQ_MP (@lem6902541) (@lem940073)). Qed.
Lemma lem6902543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902544 : term270 = term230.
Proof. exact (MK_COMB (@lem6902543) (@lem6902542)). Qed.
Lemma lem6902545 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6902546 : term292 = term260.
Proof. exact (MK_COMB (@lem6902545) (@lem6902544)). Qed.
Lemma lem6902547 : term287 = term260.
Proof. exact (TRANS (@lem6902540) (@lem6902546)). Qed.
Lemma lem6902548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902549 : term314 = term302.
Proof. exact (MK_COMB (@lem6902548) (@lem6902547)). Qed.
Lemma lem6902550 : term315 = term304.
Proof. exact (MK_COMB (@lem6902549) (@lem6902537)). Qed.
Lemma lem6902552 (m : nat) : (term316 m) = term213.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6902553 : term304 = term213.
Proof. exact (@lem6902552 term4). Qed.
Lemma lem6902554 : term315 = term213.
Proof. exact (TRANS (@lem6902550) (@lem6902553)). Qed.
Lemma lem6902555 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902556 : term317 = term318.
Proof. exact (MK_COMB (@lem6902555) (@lem6902554)). Qed.
Lemma lem6902557 : term230 = term230.
Proof. exact (eq_refl term230). Qed.
Lemma lem6902558 : term319 = term320.
Proof. exact (MK_COMB (@lem6902556) (@lem6902557)). Qed.
Lemma lem6902560 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6902561 : term320 = term213.
Proof. exact (@lem6902560 term4). Qed.
Lemma lem6902562 : term319 = term213.
Proof. exact (TRANS (@lem6902558) (@lem6902561)). Qed.
Lemma lem6902564 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902565 : term269 = term270.
Proof. exact (@lem6902564 term4 term4). Qed.
Lemma lem6902566 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902567 : term272 = term4.
Proof. exact (EQ_MP (@lem6902566) (@lem940073)). Qed.
Lemma lem6902568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902569 : term270 = term230.
Proof. exact (MK_COMB (@lem6902568) (@lem6902567)). Qed.
Lemma lem6902570 : term269 = term230.
Proof. exact (TRANS (@lem6902565) (@lem6902569)). Qed.
Lemma lem6902571 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem6902572 : term322 = term320.
Proof. exact (MK_COMB (@lem6902571) (@lem6902570)). Qed.
Lemma lem6902574 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6902575 : term320 = term213.
Proof. exact (@lem6902574 term4). Qed.
Lemma lem6902576 : term322 = term213.
Proof. exact (TRANS (@lem6902572) (@lem6902575)). Qed.
Lemma lem6902577 : term213 = term322.
Proof. exact (SYM (@lem6902576)). Qed.
Lemma lem6902578 : term319 = term322.
Proof. exact (TRANS (@lem6902562) (@lem6902577)). Qed.
Lemma lem6902579 : term305 = term257.
Proof. exact (@lem6902529 (@lem6902578)). Qed.
Lemma lem6902580 : term304 = term257.
Proof. exact (TRANS (@lem6902495) (@lem6902579)). Qed.
Lemma lem6902582 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6902583 : term257 = term213.
Proof. exact (@lem6902582 term213). Qed.
Lemma lem6902584 : term304 = term213.
Proof. exact (TRANS (@lem6902580) (@lem6902583)). Qed.
Lemma lem6902585 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902586 : term323 = term318.
Proof. exact (MK_COMB (@lem6902585) (@lem6902584)). Qed.
Lemma lem6902587 (_92164 : int) : (real_of_int _92164) = (real_of_int _92164).
Proof. exact (eq_refl (real_of_int _92164)). Qed.
Lemma lem6902588 (_92164 : int) : (term301 _92164) = (term324 _92164).
Proof. exact (MK_COMB (@lem6902586) (@lem6902587 _92164)). Qed.
Lemma lem6902589 (_92164 : int) : (term300 _92164) = (term324 _92164).
Proof. exact (TRANS (@lem6902486 _92164) (@lem6902588 _92164)). Qed.
Lemma lem6902590 (_92164 : int) : (term324 _92164) = term213.
Proof. exact (@lem1982719 (real_of_int _92164)). Qed.
Lemma lem6902591 (_92164 : int) : (term300 _92164) = term213.
Proof. exact (TRANS (@lem6902589 _92164) (@lem6902590 _92164)). Qed.
Lemma lem6902592 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902593 (_92164 : int) : (term325 _92164) = term326.
Proof. exact (MK_COMB (@lem6902592) (@lem6902591 _92164)). Qed.
Lemma lem6902594 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem6902595 (_92164 : int) : (term298 _92164) = term327.
Proof. exact (MK_COMB (@lem6902593 _92164) (@lem6902594)). Qed.
Lemma lem6902596 (_92164 : int) : (term297 _92164) = term327.
Proof. exact (TRANS (@lem6902485 _92164) (@lem6902595 _92164)). Qed.
Lemma lem6902597 : term327 = term260.
Proof. exact (@lem1982721 term260). Qed.
Lemma lem6902598 (_92164 : int) : (term297 _92164) = term260.
Proof. exact (TRANS (@lem6902596 _92164) (@lem6902597)). Qed.
Lemma lem6902599 (_92164 : int) : (term283 _92164) = term260.
Proof. exact (TRANS (@lem6902484 _92164) (@lem6902598 _92164)). Qed.
Lemma lem6902601 (_92164 : int) : (term282 _92164) = term260.
Proof. exact (TRANS (@lem6902439 _92164) (@lem6902599 _92164)). Qed.
Lemma lem6902602 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6902603 (_92164 : int) : (term328 _92164) = term329.
Proof. exact (MK_COMB (@lem6902602) (@lem6902601 _92164)). Qed.
Lemma lem6902604 : term213 = term213.
Proof. exact (eq_refl term213). Qed.
Lemma lem6902605 (_92164 : int) : (term281 _92164) = term330.
Proof. exact (MK_COMB (@lem6902603 _92164) (@lem6902604)). Qed.
Lemma lem6902606 (_92164 : int) : (term235 _92164) = term330.
Proof. exact (TRANS (@lem6902427 _92164) (@lem6902605 _92164)). Qed.
Lemma lem6902607 (_92162 : int) : (term235 _92162) = (term281 _92162).
Proof. exact (@lem1988287 (real_of_int _92162) (term232 _92162)). Qed.
Lemma lem6902619 (_92162 : int) : (term282 _92162) = (term283 _92162).
Proof. exact (@lem1982792 (real_of_int _92162) (term232 _92162)). Qed.
Lemma lem6902620 (_92162 : int) : (term284 _92162) = (term285 _92162).
Proof. exact (@lem1982781 (real_of_int _92162) term260 term230). Qed.
Lemma lem6902622 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902623 : term230 = term286.
Proof. exact (@lem6902622 term4). Qed.
Lemma lem6902625 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902626 : term260 = term261.
Proof. exact (@lem6902625 term4). Qed.
Lemma lem6902627 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902628 : term262 = term263.
Proof. exact (MK_COMB (@lem6902627) (@lem6902626)). Qed.
Lemma lem6902629 : term287 = term288.
Proof. exact (MK_COMB (@lem6902628) (@lem6902623)). Qed.
Lemma lem6902630 : term288 = term289.
Proof. exact (@lem1981613 term260 term230 term230 term230). Qed.
Lemma lem6902632 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902633 : term269 = term270.
Proof. exact (@lem6902632 term4 term4). Qed.
Lemma lem6902634 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902635 : term272 = term4.
Proof. exact (EQ_MP (@lem6902634) (@lem940073)). Qed.
Lemma lem6902636 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902637 : term270 = term230.
Proof. exact (MK_COMB (@lem6902636) (@lem6902635)). Qed.
Lemma lem6902638 : term269 = term230.
Proof. exact (TRANS (@lem6902633) (@lem6902637)). Qed.
Lemma lem6902640 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6902641 : term287 = term292.
Proof. exact (@lem6902640 term4 term4). Qed.
Lemma lem6902642 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902643 : term272 = term4.
Proof. exact (EQ_MP (@lem6902642) (@lem940073)). Qed.
Lemma lem6902644 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902645 : term270 = term230.
Proof. exact (MK_COMB (@lem6902644) (@lem6902643)). Qed.
Lemma lem6902646 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6902647 : term292 = term260.
Proof. exact (MK_COMB (@lem6902646) (@lem6902645)). Qed.
Lemma lem6902648 : term287 = term260.
Proof. exact (TRANS (@lem6902641) (@lem6902647)). Qed.
Lemma lem6902649 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem6902650 : term293 = term294.
Proof. exact (MK_COMB (@lem6902649) (@lem6902648)). Qed.
Lemma lem6902651 : term289 = term261.
Proof. exact (MK_COMB (@lem6902650) (@lem6902638)). Qed.
Lemma lem6902652 : term288 = term261.
Proof. exact (TRANS (@lem6902630) (@lem6902651)). Qed.
Lemma lem6902653 : term287 = term261.
Proof. exact (TRANS (@lem6902629) (@lem6902652)). Qed.
Lemma lem6902655 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem6902656 : term261 = term260.
Proof. exact (@lem6902655 term260). Qed.
Lemma lem6902657 : term287 = term260.
Proof. exact (TRANS (@lem6902653) (@lem6902656)). Qed.
Lemma lem6902660 (_92162 : int) : (term295 _92162) = (term295 _92162).
Proof. exact (eq_refl (term295 _92162)). Qed.
Lemma lem6902661 (_92162 : int) : (term285 _92162) = (term296 _92162).
Proof. exact (MK_COMB (@lem6902660 _92162) (@lem6902657)). Qed.
Lemma lem6902662 (_92162 : int) : (term284 _92162) = (term296 _92162).
Proof. exact (TRANS (@lem6902620 _92162) (@lem6902661 _92162)). Qed.
Lemma lem6902663 (_92162 : int) : (term231 _92162) = (term231 _92162).
Proof. exact (eq_refl (term231 _92162)). Qed.
Lemma lem6902664 (_92162 : int) : (term283 _92162) = (term297 _92162).
Proof. exact (MK_COMB (@lem6902663 _92162) (@lem6902662 _92162)). Qed.
Lemma lem6902665 (_92162 : int) : (term297 _92162) = (term298 _92162).
Proof. exact (@lem1982763 (real_of_int _92162) (term299 _92162) term260). Qed.
Lemma lem6902666 (_92162 : int) : (term300 _92162) = (term301 _92162).
Proof. exact (@lem1982715 term260 (real_of_int _92162)). Qed.
Lemma lem6902668 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902669 : term230 = term286.
Proof. exact (@lem6902668 term4). Qed.
Lemma lem6902671 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902672 : term260 = term261.
Proof. exact (@lem6902671 term4). Qed.
Lemma lem6902673 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902674 : term302 = term303.
Proof. exact (MK_COMB (@lem6902673) (@lem6902672)). Qed.
Lemma lem6902675 : term304 = term305.
Proof. exact (MK_COMB (@lem6902674) (@lem6902669)). Qed.
Lemma lem6902676 : term306.
Proof. exact (@lem1981473 term260 term230 term230 term230 term213 term230). Qed.
Lemma lem6902678 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902679 : term308 = term309.
Proof. exact (@lem6902678 (NUMERAL 0) term4). Qed.
Lemma lem6902680 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902681 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902682 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902681 h1) (fun h1 : term309 = True => @lem6902680)). Qed.
Lemma lem6902683 : term309 = True.
Proof. exact (EQ_MP (@lem6902682) (@lem6902680)). Qed.
Lemma lem6902684 : term308 = True.
Proof. exact (TRANS (@lem6902679) (@lem6902683)). Qed.
Lemma lem6902685 : True = term308.
Proof. exact (SYM (@lem6902684)). Qed.
Lemma lem6902686 : term308.
Proof. exact (EQ_MP (@lem6902685) (@lem0)). Qed.
Lemma lem6902687 : term311.
Proof. exact (@lem6902676 (@lem6902686)). Qed.
Lemma lem6902689 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902690 : term308 = term309.
Proof. exact (@lem6902689 (NUMERAL 0) term4). Qed.
Lemma lem6902691 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902692 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902693 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902692 h1) (fun h1 : term309 = True => @lem6902691)). Qed.
Lemma lem6902694 : term309 = True.
Proof. exact (EQ_MP (@lem6902693) (@lem6902691)). Qed.
Lemma lem6902695 : term308 = True.
Proof. exact (TRANS (@lem6902690) (@lem6902694)). Qed.
Lemma lem6902696 : True = term308.
Proof. exact (SYM (@lem6902695)). Qed.
Lemma lem6902697 : term308.
Proof. exact (EQ_MP (@lem6902696) (@lem0)). Qed.
Lemma lem6902698 : term312.
Proof. exact (@lem6902687 (@lem6902697)). Qed.
Lemma lem6902700 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902701 : term308 = term309.
Proof. exact (@lem6902700 (NUMERAL 0) term4). Qed.
Lemma lem6902702 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902703 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902704 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902703 h1) (fun h1 : term309 = True => @lem6902702)). Qed.
Lemma lem6902705 : term309 = True.
Proof. exact (EQ_MP (@lem6902704) (@lem6902702)). Qed.
Lemma lem6902706 : term308 = True.
Proof. exact (TRANS (@lem6902701) (@lem6902705)). Qed.
Lemma lem6902707 : True = term308.
Proof. exact (SYM (@lem6902706)). Qed.
Lemma lem6902708 : term308.
Proof. exact (EQ_MP (@lem6902707) (@lem0)). Qed.
Lemma lem6902709 : term313.
Proof. exact (@lem6902698 (@lem6902708)). Qed.
Lemma lem6902711 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902712 : term269 = term270.
Proof. exact (@lem6902711 term4 term4). Qed.
Lemma lem6902713 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902714 : term272 = term4.
Proof. exact (EQ_MP (@lem6902713) (@lem940073)). Qed.
Lemma lem6902715 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902716 : term270 = term230.
Proof. exact (MK_COMB (@lem6902715) (@lem6902714)). Qed.
Lemma lem6902717 : term269 = term230.
Proof. exact (TRANS (@lem6902712) (@lem6902716)). Qed.
Lemma lem6902719 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6902720 : term287 = term292.
Proof. exact (@lem6902719 term4 term4). Qed.
Lemma lem6902721 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902722 : term272 = term4.
Proof. exact (EQ_MP (@lem6902721) (@lem940073)). Qed.
Lemma lem6902723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902724 : term270 = term230.
Proof. exact (MK_COMB (@lem6902723) (@lem6902722)). Qed.
Lemma lem6902725 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6902726 : term292 = term260.
Proof. exact (MK_COMB (@lem6902725) (@lem6902724)). Qed.
Lemma lem6902727 : term287 = term260.
Proof. exact (TRANS (@lem6902720) (@lem6902726)). Qed.
Lemma lem6902728 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902729 : term314 = term302.
Proof. exact (MK_COMB (@lem6902728) (@lem6902727)). Qed.
Lemma lem6902730 : term315 = term304.
Proof. exact (MK_COMB (@lem6902729) (@lem6902717)). Qed.
Lemma lem6902732 (m : nat) : (term316 m) = term213.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem6902733 : term304 = term213.
Proof. exact (@lem6902732 term4). Qed.
Lemma lem6902734 : term315 = term213.
Proof. exact (TRANS (@lem6902730) (@lem6902733)). Qed.
Lemma lem6902735 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902736 : term317 = term318.
Proof. exact (MK_COMB (@lem6902735) (@lem6902734)). Qed.
Lemma lem6902737 : term230 = term230.
Proof. exact (eq_refl term230). Qed.
Lemma lem6902738 : term319 = term320.
Proof. exact (MK_COMB (@lem6902736) (@lem6902737)). Qed.
Lemma lem6902740 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6902741 : term320 = term213.
Proof. exact (@lem6902740 term4). Qed.
Lemma lem6902742 : term319 = term213.
Proof. exact (TRANS (@lem6902738) (@lem6902741)). Qed.
Lemma lem6902744 (m : nat) (n : nat) : (term267 m n) = (term268 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem6902745 : term269 = term270.
Proof. exact (@lem6902744 term4 term4). Qed.
Lemma lem6902746 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902747 : term272 = term4.
Proof. exact (EQ_MP (@lem6902746) (@lem940073)). Qed.
Lemma lem6902748 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902749 : term270 = term230.
Proof. exact (MK_COMB (@lem6902748) (@lem6902747)). Qed.
Lemma lem6902750 : term269 = term230.
Proof. exact (TRANS (@lem6902745) (@lem6902749)). Qed.
Lemma lem6902751 : term318 = term318.
Proof. exact (eq_refl term318). Qed.
Lemma lem6902752 : term322 = term320.
Proof. exact (MK_COMB (@lem6902751) (@lem6902750)). Qed.
Lemma lem6902754 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6902755 : term320 = term213.
Proof. exact (@lem6902754 term4). Qed.
Lemma lem6902756 : term322 = term213.
Proof. exact (TRANS (@lem6902752) (@lem6902755)). Qed.
Lemma lem6902757 : term213 = term322.
Proof. exact (SYM (@lem6902756)). Qed.
Lemma lem6902758 : term319 = term322.
Proof. exact (TRANS (@lem6902742) (@lem6902757)). Qed.
Lemma lem6902759 : term305 = term257.
Proof. exact (@lem6902709 (@lem6902758)). Qed.
Lemma lem6902760 : term304 = term257.
Proof. exact (TRANS (@lem6902675) (@lem6902759)). Qed.
Lemma lem6902762 (x : real) : (term276 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem6902763 : term257 = term213.
Proof. exact (@lem6902762 term213). Qed.
Lemma lem6902764 : term304 = term213.
Proof. exact (TRANS (@lem6902760) (@lem6902763)). Qed.
Lemma lem6902765 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem6902766 : term323 = term318.
Proof. exact (MK_COMB (@lem6902765) (@lem6902764)). Qed.
Lemma lem6902767 (_92162 : int) : (real_of_int _92162) = (real_of_int _92162).
Proof. exact (eq_refl (real_of_int _92162)). Qed.
Lemma lem6902768 (_92162 : int) : (term301 _92162) = (term324 _92162).
Proof. exact (MK_COMB (@lem6902766) (@lem6902767 _92162)). Qed.
Lemma lem6902769 (_92162 : int) : (term300 _92162) = (term324 _92162).
Proof. exact (TRANS (@lem6902666 _92162) (@lem6902768 _92162)). Qed.
Lemma lem6902770 (_92162 : int) : (term324 _92162) = term213.
Proof. exact (@lem1982719 (real_of_int _92162)). Qed.
Lemma lem6902771 (_92162 : int) : (term300 _92162) = term213.
Proof. exact (TRANS (@lem6902769 _92162) (@lem6902770 _92162)). Qed.
Lemma lem6902772 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem6902773 (_92162 : int) : (term325 _92162) = term326.
Proof. exact (MK_COMB (@lem6902772) (@lem6902771 _92162)). Qed.
Lemma lem6902774 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem6902775 (_92162 : int) : (term298 _92162) = term327.
Proof. exact (MK_COMB (@lem6902773 _92162) (@lem6902774)). Qed.
Lemma lem6902776 (_92162 : int) : (term297 _92162) = term327.
Proof. exact (TRANS (@lem6902665 _92162) (@lem6902775 _92162)). Qed.
Lemma lem6902777 : term327 = term260.
Proof. exact (@lem1982721 term260). Qed.
Lemma lem6902778 (_92162 : int) : (term297 _92162) = term260.
Proof. exact (TRANS (@lem6902776 _92162) (@lem6902777)). Qed.
Lemma lem6902779 (_92162 : int) : (term283 _92162) = term260.
Proof. exact (TRANS (@lem6902664 _92162) (@lem6902778 _92162)). Qed.
Lemma lem6902781 (_92162 : int) : (term282 _92162) = term260.
Proof. exact (TRANS (@lem6902619 _92162) (@lem6902779 _92162)). Qed.
Lemma lem6902782 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem6902783 (_92162 : int) : (term328 _92162) = term329.
Proof. exact (MK_COMB (@lem6902782) (@lem6902781 _92162)). Qed.
Lemma lem6902784 : term213 = term213.
Proof. exact (eq_refl term213). Qed.
Lemma lem6902785 (_92162 : int) : (term281 _92162) = term330.
Proof. exact (MK_COMB (@lem6902783 _92162) (@lem6902784)). Qed.
Lemma lem6902786 (_92162 : int) : (term235 _92162) = term330.
Proof. exact (TRANS (@lem6902607 _92162) (@lem6902785 _92162)). Qed.
Lemma lem6902787 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6902788 (_92164 : int) : (term237 _92164) = term331.
Proof. exact (MK_COMB (@lem6902787) (@lem6902606 _92164)). Qed.
Lemma lem6902789 (_92164 : int) (_92162 : int) : (term248 _92164 _92162) = term332.
Proof. exact (MK_COMB (@lem6902788 _92164) (@lem6902786 _92162)). Qed.
Lemma lem6902790 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem6902791 (_92163 : int) : (term237 _92163) = term331.
Proof. exact (MK_COMB (@lem6902790) (@lem6902426 _92163)). Qed.
Lemma lem6902792 (_92163 : int) (_92164 : int) (_92162 : int) : (term249 _92163 _92164 _92162) = term333.
Proof. exact (MK_COMB (@lem6902791 _92163) (@lem6902789 _92164 _92162)). Qed.
Lemma lem6902793 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6902794 (_92164 : int) : (term242 _92164) = (term334 _92164).
Proof. exact (MK_COMB (@lem6902793) (@lem6902246 _92164)). Qed.
Lemma lem6902795 (_92163 : int) (_92162 : int) (_92164 : int) : (term250 _92163 _92164 _92162) = (term335 _92164).
Proof. exact (MK_COMB (@lem6902794 _92164) (@lem6902792 _92163 _92164 _92162)). Qed.
Lemma lem6902796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6902797 (_92163 : int) : (term242 _92163) = (term334 _92163).
Proof. exact (MK_COMB (@lem6902796) (@lem6902198 _92163)). Qed.
Lemma lem6902798 (_92162 : int) (_92163 : int) (_92164 : int) : (term251 _92163 _92164 _92162) = (term336 _92163 _92164).
Proof. exact (MK_COMB (@lem6902797 _92163) (@lem6902795 _92163 _92162 _92164)). Qed.
Lemma lem6902799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6902800 (_92162 : int) : (term242 _92162) = (term334 _92162).
Proof. exact (MK_COMB (@lem6902799) (@lem6902150 _92162)). Qed.
Lemma lem6902801 (_92162 : int) (_92163 : int) (_92164 : int) : (term252 _92163 _92164 _92162) = (term337 _92162 _92163 _92164).
Proof. exact (MK_COMB (@lem6902800 _92162) (@lem6902798 _92162 _92163 _92164)). Qed.
Lemma lem6902808 (_92162 : int) (_92163 : int) (_92164 : int) : (term247 _92163 _92164 _92162) = (term337 _92162 _92163 _92164).
Proof. exact (TRANS (@lem6902102 _92163 _92164 _92162) (@lem6902801 _92162 _92163 _92164)). Qed.
Lemma lem6902822 (_92164 : int) : (term335 _92164) = (term338 _92164).
Proof. exact (@lem19158 term330 (term280 _92164) term332). Qed.
Lemma lem6902829 (_92164 : int) : (term339 _92164) = (term340 _92164).
Proof. exact (@lem19158 term330 (term280 _92164) term330). Qed.
Lemma lem6902832 (_92164 : int) : (term341 _92164) = (term341 _92164).
Proof. exact (eq_refl (term341 _92164)). Qed.
Lemma lem6902833 (_92164 : int) : (term338 _92164) = (term342 _92164).
Proof. exact (MK_COMB (@lem6902832 _92164) (@lem6902829 _92164)). Qed.
Lemma lem6902835 (_92164 : int) : (term335 _92164) = (term342 _92164).
Proof. exact (TRANS (@lem6902822 _92164) (@lem6902833 _92164)). Qed.
Lemma lem6902838 (_92163 : int) : (term334 _92163) = (term334 _92163).
Proof. exact (eq_refl (term334 _92163)). Qed.
Lemma lem6902839 (_92163 : int) (_92164 : int) : (term336 _92163 _92164) = (term343 _92163 _92164).
Proof. exact (MK_COMB (@lem6902838 _92163) (@lem6902835 _92164)). Qed.
Lemma lem6902840 (_92163 : int) (_92164 : int) : (term343 _92163 _92164) = (term344 _92163 _92164).
Proof. exact (@lem19158 (term345 _92164) (term280 _92163) (term340 _92164)). Qed.
Lemma lem6902847 (_92163 : int) (_92164 : int) : (term346 _92163 _92164) = (term347 _92163 _92164).
Proof. exact (@lem19158 (term345 _92164) (term280 _92163) (term345 _92164)). Qed.
Lemma lem6902850 (_92163 : int) (_92164 : int) : (term348 _92163 _92164) = (term348 _92163 _92164).
Proof. exact (eq_refl (term348 _92163 _92164)). Qed.
Lemma lem6902851 (_92163 : int) (_92164 : int) : (term344 _92163 _92164) = (term349 _92163 _92164).
Proof. exact (MK_COMB (@lem6902850 _92163 _92164) (@lem6902847 _92163 _92164)). Qed.
Lemma lem6902852 (_92163 : int) (_92164 : int) : (term343 _92163 _92164) = (term349 _92163 _92164).
Proof. exact (TRANS (@lem6902840 _92163 _92164) (@lem6902851 _92163 _92164)). Qed.
Lemma lem6902853 (_92163 : int) (_92164 : int) : (term336 _92163 _92164) = (term349 _92163 _92164).
Proof. exact (TRANS (@lem6902839 _92163 _92164) (@lem6902852 _92163 _92164)). Qed.
Lemma lem6902856 (_92162 : int) : (term334 _92162) = (term334 _92162).
Proof. exact (eq_refl (term334 _92162)). Qed.
Lemma lem6902857 (_92162 : int) (_92163 : int) (_92164 : int) : (term337 _92162 _92163 _92164) = (term350 _92162 _92163 _92164).
Proof. exact (MK_COMB (@lem6902856 _92162) (@lem6902853 _92163 _92164)). Qed.
Lemma lem6902858 (_92162 : int) (_92163 : int) (_92164 : int) : (term350 _92162 _92163 _92164) = (term351 _92162 _92163 _92164).
Proof. exact (@lem19158 (term352 _92163 _92164) (term280 _92162) (term347 _92163 _92164)). Qed.
Lemma lem6902865 (_92162 : int) (_92163 : int) (_92164 : int) : (term353 _92162 _92163 _92164) = (term354 _92162 _92163 _92164).
Proof. exact (@lem19158 (term352 _92163 _92164) (term280 _92162) (term352 _92163 _92164)). Qed.
Lemma lem6902868 (_92162 : int) (_92163 : int) (_92164 : int) : (term355 _92162 _92163 _92164) = (term355 _92162 _92163 _92164).
Proof. exact (eq_refl (term355 _92162 _92163 _92164)). Qed.
Lemma lem6902869 (_92162 : int) (_92163 : int) (_92164 : int) : (term351 _92162 _92163 _92164) = (term356 _92162 _92163 _92164).
Proof. exact (MK_COMB (@lem6902868 _92162 _92163 _92164) (@lem6902865 _92162 _92163 _92164)). Qed.
Lemma lem6902870 (_92162 : int) (_92163 : int) (_92164 : int) : (term350 _92162 _92163 _92164) = (term356 _92162 _92163 _92164).
Proof. exact (TRANS (@lem6902858 _92162 _92163 _92164) (@lem6902869 _92162 _92163 _92164)). Qed.
Lemma lem6902871 (_92162 : int) (_92163 : int) (_92164 : int) : (term337 _92162 _92163 _92164) = (term356 _92162 _92163 _92164).
Proof. exact (TRANS (@lem6902857 _92162 _92163 _92164) (@lem6902870 _92162 _92163 _92164)). Qed.
Lemma lem6902872 (_92162 : int) (_92163 : int) (_92164 : int) : (term247 _92163 _92164 _92162) = (term356 _92162 _92163 _92164).
Proof. exact (TRANS (@lem6902808 _92162 _92163 _92164) (@lem6902871 _92162 _92163 _92164)). Qed.
Lemma lem6902888 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term356 _92162 _92163 _92164) : term356 _92162 _92163 _92164.
Proof. exact (h1). Qed.
Lemma lem6902889 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term357 _92162 _92163 _92164.
Proof. exact (h1). Qed.
Lemma lem6902890 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term352 _92163 _92164.
Proof. exact (proj2 (@lem6902889 _92162 _92163 _92164 h1)). Qed.
Lemma lem6902892 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term345 _92164.
Proof. exact (proj2 (@lem6902890 _92162 _92163 _92164 h1)). Qed.
Lemma lem6902894 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term330.
Proof. exact (proj2 (@lem6902892 _92162 _92163 _92164 h1)). Qed.
Lemma lem6902897 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6902898 : term330 = term358.
Proof. exact (@lem6902897 term213 term260). Qed.
Lemma lem6902900 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902901 : term260 = term261.
Proof. exact (@lem6902900 term4). Qed.
Lemma lem6902903 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902904 : term213 = term257.
Proof. exact (@lem6902903 (NUMERAL 0)). Qed.
Lemma lem6902905 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6902906 : term215 = term359.
Proof. exact (MK_COMB (@lem6902905) (@lem6902904)). Qed.
Lemma lem6902907 : term358 = term360.
Proof. exact (MK_COMB (@lem6902906) (@lem6902901)). Qed.
Lemma lem6902908 : term361.
Proof. exact (@lem1980026 term213 term230 term260 term230). Qed.
Lemma lem6902910 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902911 : term308 = term309.
Proof. exact (@lem6902910 (NUMERAL 0) term4). Qed.
Lemma lem6902912 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902913 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902914 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902913 h1) (fun h1 : term309 = True => @lem6902912)). Qed.
Lemma lem6902915 : term309 = True.
Proof. exact (EQ_MP (@lem6902914) (@lem6902912)). Qed.
Lemma lem6902916 : term308 = True.
Proof. exact (TRANS (@lem6902911) (@lem6902915)). Qed.
Lemma lem6902917 : True = term308.
Proof. exact (SYM (@lem6902916)). Qed.
Lemma lem6902918 : term308.
Proof. exact (EQ_MP (@lem6902917) (@lem0)). Qed.
Lemma lem6902919 : term362.
Proof. exact (@lem6902908 (@lem6902918)). Qed.
Lemma lem6902921 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902922 : term308 = term309.
Proof. exact (@lem6902921 (NUMERAL 0) term4). Qed.
Lemma lem6902923 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902924 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902925 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902924 h1) (fun h1 : term309 = True => @lem6902923)). Qed.
Lemma lem6902926 : term309 = True.
Proof. exact (EQ_MP (@lem6902925) (@lem6902923)). Qed.
Lemma lem6902927 : term308 = True.
Proof. exact (TRANS (@lem6902922) (@lem6902926)). Qed.
Lemma lem6902928 : True = term308.
Proof. exact (SYM (@lem6902927)). Qed.
Lemma lem6902929 : term308.
Proof. exact (EQ_MP (@lem6902928) (@lem0)). Qed.
Lemma lem6902930 : term360 = term363.
Proof. exact (@lem6902919 (@lem6902929)). Qed.
Lemma lem6902932 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6902933 : term287 = term292.
Proof. exact (@lem6902932 term4 term4). Qed.
Lemma lem6902934 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6902935 : term272 = term4.
Proof. exact (EQ_MP (@lem6902934) (@lem940073)). Qed.
Lemma lem6902936 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6902937 : term270 = term230.
Proof. exact (MK_COMB (@lem6902936) (@lem6902935)). Qed.
Lemma lem6902938 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6902939 : term292 = term260.
Proof. exact (MK_COMB (@lem6902938) (@lem6902937)). Qed.
Lemma lem6902940 : term287 = term260.
Proof. exact (TRANS (@lem6902933) (@lem6902939)). Qed.
Lemma lem6902942 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6902943 : term320 = term213.
Proof. exact (@lem6902942 term4). Qed.
Lemma lem6902944 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6902945 : term364 = term215.
Proof. exact (MK_COMB (@lem6902944) (@lem6902943)). Qed.
Lemma lem6902946 : term363 = term358.
Proof. exact (MK_COMB (@lem6902945) (@lem6902940)). Qed.
Lemma lem6902948 (m : nat) (n : nat) : (term365 m n) = (term366 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6902949 : term358 = term367.
Proof. exact (@lem6902948 (NUMERAL 0) term4). Qed.
Lemma lem6902950 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902951 (h1 : term310 = (BIT1 0)) : (term4 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6902952 : (term310 = (BIT1 0)) = ((term4 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902951 h1) (fun h1 : (term4 = (NUMERAL 0)) = False => @lem6902950)). Qed.
Lemma lem6902953 : (term4 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6902952) (@lem6902950)). Qed.
Lemma lem6902954 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6902955 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6902956 : term368 = (and True).
Proof. exact (MK_COMB (@lem6902955) (@lem6902954)). Qed.
Lemma lem6902957 : term367 = (True /\ False).
Proof. exact (MK_COMB (@lem6902956) (@lem6902953)). Qed.
Lemma lem6902959 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6902960 : term367 = False.
Proof. exact (TRANS (@lem6902957) (@lem6902959)). Qed.
Lemma lem6902961 : term358 = False.
Proof. exact (TRANS (@lem6902949) (@lem6902960)). Qed.
Lemma lem6902962 : term363 = False.
Proof. exact (TRANS (@lem6902946) (@lem6902961)). Qed.
Lemma lem6902963 : term360 = False.
Proof. exact (TRANS (@lem6902930) (@lem6902962)). Qed.
Lemma lem6902964 : term358 = False.
Proof. exact (TRANS (@lem6902907) (@lem6902963)). Qed.
Lemma lem6902965 : term330 = False.
Proof. exact (TRANS (@lem6902898) (@lem6902964)). Qed.
Lemma lem6902966 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : False.
Proof. exact (EQ_MP (@lem6902965) (@lem6902894 _92162 _92163 _92164 h1)). Qed.
Lemma lem6902967 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term354 _92162 _92163 _92164) : term354 _92162 _92163 _92164.
Proof. exact (h1). Qed.
Lemma lem6902968 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term357 _92162 _92163 _92164.
Proof. exact (h1). Qed.
Lemma lem6902969 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term352 _92163 _92164.
Proof. exact (proj2 (@lem6902968 _92162 _92163 _92164 h1)). Qed.
Lemma lem6902971 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term345 _92164.
Proof. exact (proj2 (@lem6902969 _92162 _92163 _92164 h1)). Qed.
Lemma lem6902973 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term330.
Proof. exact (proj2 (@lem6902971 _92162 _92163 _92164 h1)). Qed.
Lemma lem6902976 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6902977 : term330 = term358.
Proof. exact (@lem6902976 term213 term260). Qed.
Lemma lem6902979 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6902980 : term260 = term261.
Proof. exact (@lem6902979 term4). Qed.
Lemma lem6902982 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6902983 : term213 = term257.
Proof. exact (@lem6902982 (NUMERAL 0)). Qed.
Lemma lem6902984 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6902985 : term215 = term359.
Proof. exact (MK_COMB (@lem6902984) (@lem6902983)). Qed.
Lemma lem6902986 : term358 = term360.
Proof. exact (MK_COMB (@lem6902985) (@lem6902980)). Qed.
Lemma lem6902987 : term361.
Proof. exact (@lem1980026 term213 term230 term260 term230). Qed.
Lemma lem6902989 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6902990 : term308 = term309.
Proof. exact (@lem6902989 (NUMERAL 0) term4). Qed.
Lemma lem6902991 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6902992 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6902993 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6902992 h1) (fun h1 : term309 = True => @lem6902991)). Qed.
Lemma lem6902994 : term309 = True.
Proof. exact (EQ_MP (@lem6902993) (@lem6902991)). Qed.
Lemma lem6902995 : term308 = True.
Proof. exact (TRANS (@lem6902990) (@lem6902994)). Qed.
Lemma lem6902996 : True = term308.
Proof. exact (SYM (@lem6902995)). Qed.
Lemma lem6902997 : term308.
Proof. exact (EQ_MP (@lem6902996) (@lem0)). Qed.
Lemma lem6902998 : term362.
Proof. exact (@lem6902987 (@lem6902997)). Qed.
Lemma lem6903000 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6903001 : term308 = term309.
Proof. exact (@lem6903000 (NUMERAL 0) term4). Qed.
Lemma lem6903002 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6903003 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6903004 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6903003 h1) (fun h1 : term309 = True => @lem6903002)). Qed.
Lemma lem6903005 : term309 = True.
Proof. exact (EQ_MP (@lem6903004) (@lem6903002)). Qed.
Lemma lem6903006 : term308 = True.
Proof. exact (TRANS (@lem6903001) (@lem6903005)). Qed.
Lemma lem6903007 : True = term308.
Proof. exact (SYM (@lem6903006)). Qed.
Lemma lem6903008 : term308.
Proof. exact (EQ_MP (@lem6903007) (@lem0)). Qed.
Lemma lem6903009 : term360 = term363.
Proof. exact (@lem6902998 (@lem6903008)). Qed.
Lemma lem6903011 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6903012 : term287 = term292.
Proof. exact (@lem6903011 term4 term4). Qed.
Lemma lem6903013 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6903014 : term272 = term4.
Proof. exact (EQ_MP (@lem6903013) (@lem940073)). Qed.
Lemma lem6903015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6903016 : term270 = term230.
Proof. exact (MK_COMB (@lem6903015) (@lem6903014)). Qed.
Lemma lem6903017 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6903018 : term292 = term260.
Proof. exact (MK_COMB (@lem6903017) (@lem6903016)). Qed.
Lemma lem6903019 : term287 = term260.
Proof. exact (TRANS (@lem6903012) (@lem6903018)). Qed.
Lemma lem6903021 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6903022 : term320 = term213.
Proof. exact (@lem6903021 term4). Qed.
Lemma lem6903023 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6903024 : term364 = term215.
Proof. exact (MK_COMB (@lem6903023) (@lem6903022)). Qed.
Lemma lem6903025 : term363 = term358.
Proof. exact (MK_COMB (@lem6903024) (@lem6903019)). Qed.
Lemma lem6903027 (m : nat) (n : nat) : (term365 m n) = (term366 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6903028 : term358 = term367.
Proof. exact (@lem6903027 (NUMERAL 0) term4). Qed.
Lemma lem6903029 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6903030 (h1 : term310 = (BIT1 0)) : (term4 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6903031 : (term310 = (BIT1 0)) = ((term4 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6903030 h1) (fun h1 : (term4 = (NUMERAL 0)) = False => @lem6903029)). Qed.
Lemma lem6903032 : (term4 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6903031) (@lem6903029)). Qed.
Lemma lem6903033 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6903034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6903035 : term368 = (and True).
Proof. exact (MK_COMB (@lem6903034) (@lem6903033)). Qed.
Lemma lem6903036 : term367 = (True /\ False).
Proof. exact (MK_COMB (@lem6903035) (@lem6903032)). Qed.
Lemma lem6903038 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6903039 : term367 = False.
Proof. exact (TRANS (@lem6903036) (@lem6903038)). Qed.
Lemma lem6903040 : term358 = False.
Proof. exact (TRANS (@lem6903028) (@lem6903039)). Qed.
Lemma lem6903041 : term363 = False.
Proof. exact (TRANS (@lem6903025) (@lem6903040)). Qed.
Lemma lem6903042 : term360 = False.
Proof. exact (TRANS (@lem6903009) (@lem6903041)). Qed.
Lemma lem6903043 : term358 = False.
Proof. exact (TRANS (@lem6902986) (@lem6903042)). Qed.
Lemma lem6903044 : term330 = False.
Proof. exact (TRANS (@lem6902977) (@lem6903043)). Qed.
Lemma lem6903045 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : False.
Proof. exact (EQ_MP (@lem6903044) (@lem6902973 _92162 _92163 _92164 h1)). Qed.
Lemma lem6903046 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term357 _92162 _92163 _92164.
Proof. exact (h1). Qed.
Lemma lem6903047 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term352 _92163 _92164.
Proof. exact (proj2 (@lem6903046 _92162 _92163 _92164 h1)). Qed.
Lemma lem6903049 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term345 _92164.
Proof. exact (proj2 (@lem6903047 _92162 _92163 _92164 h1)). Qed.
Lemma lem6903051 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : term330.
Proof. exact (proj2 (@lem6903049 _92162 _92163 _92164 h1)). Qed.
Lemma lem6903054 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem6903055 : term330 = term358.
Proof. exact (@lem6903054 term213 term260). Qed.
Lemma lem6903057 (x : nat) : (term258 x) = (term259 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem6903058 : term260 = term261.
Proof. exact (@lem6903057 term4). Qed.
Lemma lem6903060 (x : nat) : (real_of_num x) = (term256 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem6903061 : term213 = term257.
Proof. exact (@lem6903060 (NUMERAL 0)). Qed.
Lemma lem6903062 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6903063 : term215 = term359.
Proof. exact (MK_COMB (@lem6903062) (@lem6903061)). Qed.
Lemma lem6903064 : term358 = term360.
Proof. exact (MK_COMB (@lem6903063) (@lem6903058)). Qed.
Lemma lem6903065 : term361.
Proof. exact (@lem1980026 term213 term230 term260 term230). Qed.
Lemma lem6903067 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6903068 : term308 = term309.
Proof. exact (@lem6903067 (NUMERAL 0) term4). Qed.
Lemma lem6903069 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6903070 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6903071 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6903070 h1) (fun h1 : term309 = True => @lem6903069)). Qed.
Lemma lem6903072 : term309 = True.
Proof. exact (EQ_MP (@lem6903071) (@lem6903069)). Qed.
Lemma lem6903073 : term308 = True.
Proof. exact (TRANS (@lem6903068) (@lem6903072)). Qed.
Lemma lem6903074 : True = term308.
Proof. exact (SYM (@lem6903073)). Qed.
Lemma lem6903075 : term308.
Proof. exact (EQ_MP (@lem6903074) (@lem0)). Qed.
Lemma lem6903076 : term362.
Proof. exact (@lem6903065 (@lem6903075)). Qed.
Lemma lem6903078 (m : nat) (n : nat) : (term307 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem6903079 : term308 = term309.
Proof. exact (@lem6903078 (NUMERAL 0) term4). Qed.
Lemma lem6903080 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6903081 (h1 : term310 = (BIT1 0)) : term309 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem6903082 : (term310 = (BIT1 0)) = (term309 = True).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6903081 h1) (fun h1 : term309 = True => @lem6903080)). Qed.
Lemma lem6903083 : term309 = True.
Proof. exact (EQ_MP (@lem6903082) (@lem6903080)). Qed.
Lemma lem6903084 : term308 = True.
Proof. exact (TRANS (@lem6903079) (@lem6903083)). Qed.
Lemma lem6903085 : True = term308.
Proof. exact (SYM (@lem6903084)). Qed.
Lemma lem6903086 : term308.
Proof. exact (EQ_MP (@lem6903085) (@lem0)). Qed.
Lemma lem6903087 : term360 = term363.
Proof. exact (@lem6903076 (@lem6903086)). Qed.
Lemma lem6903089 (m : nat) (n : nat) : (term290 m n) = (term291 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem6903090 : term287 = term292.
Proof. exact (@lem6903089 term4 term4). Qed.
Lemma lem6903091 : (term271 = (BIT1 0)) = (term272 = term4).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem6903092 : term272 = term4.
Proof. exact (EQ_MP (@lem6903091) (@lem940073)). Qed.
Lemma lem6903093 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem6903094 : term270 = term230.
Proof. exact (MK_COMB (@lem6903093) (@lem6903092)). Qed.
Lemma lem6903095 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem6903096 : term292 = term260.
Proof. exact (MK_COMB (@lem6903095) (@lem6903094)). Qed.
Lemma lem6903097 : term287 = term260.
Proof. exact (TRANS (@lem6903090) (@lem6903096)). Qed.
Lemma lem6903099 (x : nat) : (term321 x) = term213.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem6903100 : term320 = term213.
Proof. exact (@lem6903099 term4). Qed.
Lemma lem6903101 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem6903102 : term364 = term215.
Proof. exact (MK_COMB (@lem6903101) (@lem6903100)). Qed.
Lemma lem6903103 : term363 = term358.
Proof. exact (MK_COMB (@lem6903102) (@lem6903097)). Qed.
Lemma lem6903105 (m : nat) (n : nat) : (term365 m n) = (term366 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem6903106 : term358 = term367.
Proof. exact (@lem6903105 (NUMERAL 0) term4). Qed.
Lemma lem6903107 : term310 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem6903108 (h1 : term310 = (BIT1 0)) : (term4 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem6903109 : (term310 = (BIT1 0)) = ((term4 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term310 = (BIT1 0) => @lem6903108 h1) (fun h1 : (term4 = (NUMERAL 0)) = False => @lem6903107)). Qed.
Lemma lem6903110 : (term4 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem6903109) (@lem6903107)). Qed.
Lemma lem6903111 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem6903112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem6903113 : term368 = (and True).
Proof. exact (MK_COMB (@lem6903112) (@lem6903111)). Qed.
Lemma lem6903114 : term367 = (True /\ False).
Proof. exact (MK_COMB (@lem6903113) (@lem6903110)). Qed.
Lemma lem6903116 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem6903117 : term367 = False.
Proof. exact (TRANS (@lem6903114) (@lem6903116)). Qed.
Lemma lem6903118 : term358 = False.
Proof. exact (TRANS (@lem6903106) (@lem6903117)). Qed.
Lemma lem6903119 : term363 = False.
Proof. exact (TRANS (@lem6903103) (@lem6903118)). Qed.
Lemma lem6903120 : term360 = False.
Proof. exact (TRANS (@lem6903087) (@lem6903119)). Qed.
Lemma lem6903121 : term358 = False.
Proof. exact (TRANS (@lem6903064) (@lem6903120)). Qed.
Lemma lem6903122 : term330 = False.
Proof. exact (TRANS (@lem6903055) (@lem6903121)). Qed.
Lemma lem6903123 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term357 _92162 _92163 _92164) : False.
Proof. exact (EQ_MP (@lem6903122) (@lem6903051 _92162 _92163 _92164 h1)). Qed.
Lemma lem6903124 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term354 _92162 _92163 _92164) : False.
Proof. exact (or_elim (@lem6902967 _92162 _92163 _92164 h1) (fun h0 : term357 _92162 _92163 _92164 => @lem6903045 _92162 _92163 _92164 h0) (fun h0 : term357 _92162 _92163 _92164 => @lem6903123 _92162 _92163 _92164 h0)). Qed.
Lemma lem6903125 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term356 _92162 _92163 _92164) : False.
Proof. exact (or_elim (@lem6902888 _92162 _92163 _92164 h1) (fun h0 : term357 _92162 _92163 _92164 => @lem6902966 _92162 _92163 _92164 h0) (fun h0 : term354 _92162 _92163 _92164 => @lem6903124 _92162 _92163 _92164 h0)). Qed.
Lemma lem6903127 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term356 _92162 _92163 _92164) : term356 _92162 _92163 _92164.
Proof. exact (h1). Qed.
Lemma lem6903128 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term356 _92162 _92163 _92164) : (term356 _92162 _92163 _92164) = False.
Proof. exact (prop_ext (fun h2 : term356 _92162 _92163 _92164 => @lem6903125 _92162 _92163 _92164 h1) (fun h2 : False => @lem6903127 _92162 _92163 _92164 h1)). Qed.
Lemma lem6903129 (_92162 : int) (_92163 : int) (_92164 : int) (h1 : term356 _92162 _92163 _92164) : False.
Proof. exact (EQ_MP (@lem6903128 _92162 _92163 _92164 h1) (@lem6903127 _92162 _92163 _92164 h1)). Qed.
Lemma lem6903130 (_92163 : int) (_92164 : int) (_92162 : int) (h1 : term247 _92163 _92164 _92162) : term247 _92163 _92164 _92162.
Proof. exact (h1). Qed.
Lemma lem6903131 (_92163 : int) (_92164 : int) (_92162 : int) (h1 : term247 _92163 _92164 _92162) : term356 _92162 _92163 _92164.
Proof. exact (EQ_MP (@lem6902872 _92162 _92163 _92164) (@lem6903130 _92163 _92164 _92162 h1)). Qed.
Lemma lem6903132 (_92163 : int) (_92164 : int) (_92162 : int) (h1 : term247 _92163 _92164 _92162) : (term356 _92162 _92163 _92164) = False.
Proof. exact (prop_ext (fun h2 : term356 _92162 _92163 _92164 => @lem6903129 _92162 _92163 _92164 h2) (fun h2 : False => @lem6903131 _92163 _92164 _92162 h1)). Qed.
Lemma lem6903133 (_92163 : int) (_92164 : int) (_92162 : int) (h1 : term247 _92163 _92164 _92162) : False.
Proof. exact (EQ_MP (@lem6903132 _92163 _92164 _92162 h1) (@lem6903131 _92163 _92164 _92162 h1)). Qed.
Lemma lem6903134 (_92163 : int) (_92164 : int) (_92162 : int) : term369 _92163 _92164 _92162.
Proof. exact (fun h0 : term247 _92163 _92164 _92162 => @lem6903133 _92163 _92164 _92162 h0). Qed.
Lemma lem6903135 (_92163 : int) (_92164 : int) (_92162 : int) : term370 _92163 _92164 _92162.
Proof. exact (@lem1386578 (term371 _92163 _92164 _92162)). Qed.
Lemma lem6903138 (_92163 : int) (_92164 : int) (_92162 : int) : term371 _92163 _92164 _92162.
Proof. exact (@lem6903135 _92163 _92164 _92162 (@lem6903134 _92163 _92164 _92162)). Qed.
Lemma lem6903139 (_92163 : int) (_92164 : int) (_92162 : int) : (term245 _92163 _92164 _92162) = (term206 _92163 _92164 _92162).
Proof. exact (SYM (@lem6902010 _92163 _92164 _92162)). Qed.
Lemma lem6903140 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem6903141 (_92163 : int) (_92164 : int) (_92162 : int) : (term371 _92163 _92164 _92162) = (term185 _92163 _92164 _92162).
Proof. exact (MK_COMB (@lem6903140) (@lem6903139 _92163 _92164 _92162)). Qed.
Lemma lem6903142 (_92163 : int) (_92164 : int) (_92162 : int) : term185 _92163 _92164 _92162.
Proof. exact (EQ_MP (@lem6903141 _92163 _92164 _92162) (@lem6903138 _92163 _92164 _92162)). Qed.
Lemma lem6903143 (_92163 : int) (_92164 : int) (_92162 : int) : term186 _92163 _92164 _92162.
Proof. exact (EQ_MP (@lem6901757 _92163 _92164 _92162) (@lem6903142 _92163 _92164 _92162)). Qed.
Lemma lem6903144 (y : nat) (z : nat) (x : nat) : term372 y z x.
Proof. exact (@lem6903143 (term167 x y) (term169 x y z) (int_of_num x)). Qed.
Lemma lem6903145 (y : nat) (z : nat) (x : nat) : term373 y z x.
Proof. exact (@lem6903144 y z x (@lem6901750 x)). Qed.
Lemma lem6903146 (y : nat) (z : nat) (x : nat) : term374 y z x.
Proof. exact (@lem6903145 y z x (@lem6901753 x y)). Qed.
Lemma lem6903147 (y : nat) (z : nat) (x : nat) : term172 y z x.
Proof. exact (@lem6903146 y z x (@lem6901756 x y z)). Qed.
Lemma lem6903148 (y : nat) (x : nat) : term174 y x.
Proof. exact (fun z : nat => @lem6903147 y z x). Qed.
Lemma lem6903149 (x : nat) : term176 x.
Proof. exact (fun y : nat => @lem6903148 y x). Qed.
Lemma lem6903150 : term178.
Proof. exact (fun x : nat => @lem6903149 x). Qed.
Lemma lem6903151 : term178 = term19.
Proof. exact (SYM (@lem6901747)). Qed.
Lemma lem6903152 : term19.
Proof. exact (EQ_MP (@lem6903151) (@lem6903150)). Qed.
Lemma lem6903153 : term19 = (term19 = True).
Proof. exact (@lem7 term19). Qed.
Lemma lem6903154 : term19 = True.
Proof. exact (EQ_MP (@lem6903153) (@lem6903152)). Qed.
Lemma lem6903155 : True = term19.
Proof. exact (SYM (@lem6903154)). Qed.
Lemma lem6903156 : term19.
Proof. exact (EQ_MP (@lem6903155) (@lem0)). Qed.
Lemma lem6903157 : @monoidal nat Nat.mul.
Proof. exact (EQ_MP (@lem6901302) (@lem6903156)). Qed.
