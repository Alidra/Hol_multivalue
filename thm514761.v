Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm514761_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import MULT_CLAUSES_spec.
Require Import SUC_INJ_spec.
Require Import thm512704_spec.
Require Import thm512705_spec.
Require Import thm75543_spec.
Lemma lem514315 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514316 : (NUMERAL 0) = 0.
Proof. exact (@lem514315 0). Qed.
Lemma lem514317 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514318 : term0 = (Nat.add 0).
Proof. exact (MK_COMB (@lem514317) (@lem514316)). Qed.
Lemma lem514319 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem514320 (n : nat) : (term1 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem514318) (@lem514319 n)). Qed.
Lemma lem514321 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514322 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem514321) (@lem514320 n)). Qed.
Lemma lem514323 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem514324 (n : nat) : ((term1 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem514322 n) (@lem514323 n)). Qed.
Lemma lem514325 : term4 = term5.
Proof. exact (fun_ext (fun n : nat => @lem514324 n)). Qed.
Lemma lem514326 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514327 : term6 = term7.
Proof. exact (MK_COMB (@lem514326) (@lem514325)). Qed.
Lemma lem514328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514329 : term8 = term9.
Proof. exact (MK_COMB (@lem514328) (@lem514327)). Qed.
Lemma lem514331 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514332 : (NUMERAL 0) = 0.
Proof. exact (@lem514331 0). Qed.
Lemma lem514333 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem514334 (m : nat) : (term10 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem514333 m) (@lem514332)). Qed.
Lemma lem514335 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514336 (m : nat) : (term11 m) = (term12 m).
Proof. exact (MK_COMB (@lem514335) (@lem514334 m)). Qed.
Lemma lem514337 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem514338 (m : nat) : ((term10 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem514336 m) (@lem514337 m)). Qed.
Lemma lem514339 : term13 = term14.
Proof. exact (fun_ext (fun m : nat => @lem514338 m)). Qed.
Lemma lem514340 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514341 : term15 = term16.
Proof. exact (MK_COMB (@lem514340) (@lem514339)). Qed.
Lemma lem514342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514343 : term17 = term18.
Proof. exact (MK_COMB (@lem514342) (@lem514341)). Qed.
Lemma lem514344 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem514345 : term20 = term21.
Proof. exact (MK_COMB (@lem514343) (@lem514344)). Qed.
Lemma lem514346 : term22 = term23.
Proof. exact (MK_COMB (@lem514329) (@lem514345)). Qed.
Lemma lem514347 : term23.
Proof. exact (EQ_MP (@lem514346) (@lem77629)). Qed.
Lemma lem514349 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514350 : (NUMERAL 0) = 0.
Proof. exact (@lem514349 0). Qed.
Lemma lem514351 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem514352 : term24 = (Nat.mul 0).
Proof. exact (MK_COMB (@lem514351) (@lem514350)). Qed.
Lemma lem514353 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem514354 (n : nat) : (term25 n) = (Nat.mul 0 n).
Proof. exact (MK_COMB (@lem514352) (@lem514353 n)). Qed.
Lemma lem514355 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514356 (n : nat) : (term26 n) = (term27 n).
Proof. exact (MK_COMB (@lem514355) (@lem514354 n)). Qed.
Lemma lem514358 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514359 : (NUMERAL 0) = 0.
Proof. exact (@lem514358 0). Qed.
Lemma lem514360 (n : nat) : ((term25 n) = (NUMERAL 0)) = ((Nat.mul 0 n) = 0).
Proof. exact (MK_COMB (@lem514356 n) (@lem514359)). Qed.
Lemma lem514361 : term28 = term29.
Proof. exact (fun_ext (fun n : nat => @lem514360 n)). Qed.
Lemma lem514362 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514363 : term30 = term31.
Proof. exact (MK_COMB (@lem514362) (@lem514361)). Qed.
Lemma lem514364 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514365 : term32 = term33.
Proof. exact (MK_COMB (@lem514364) (@lem514363)). Qed.
Lemma lem514367 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514368 : (NUMERAL 0) = 0.
Proof. exact (@lem514367 0). Qed.
Lemma lem514369 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem514370 (m : nat) : (term34 m) = (Nat.mul m 0).
Proof. exact (MK_COMB (@lem514369 m) (@lem514368)). Qed.
Lemma lem514371 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514372 (m : nat) : (term35 m) = (term36 m).
Proof. exact (MK_COMB (@lem514371) (@lem514370 m)). Qed.
Lemma lem514374 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514375 : (NUMERAL 0) = 0.
Proof. exact (@lem514374 0). Qed.
Lemma lem514376 (m : nat) : ((term34 m) = (NUMERAL 0)) = ((Nat.mul m 0) = 0).
Proof. exact (MK_COMB (@lem514372 m) (@lem514375)). Qed.
Lemma lem514377 : term37 = term38.
Proof. exact (fun_ext (fun m : nat => @lem514376 m)). Qed.
Lemma lem514378 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514379 : term39 = term40.
Proof. exact (MK_COMB (@lem514378) (@lem514377)). Qed.
Lemma lem514380 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514381 : term41 = term42.
Proof. exact (MK_COMB (@lem514380) (@lem514379)). Qed.
Lemma lem514383 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514384 : term43 = (BIT1 0).
Proof. exact (@lem514383 (BIT1 0)). Qed.
Lemma lem514385 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem514386 : term44 = term45.
Proof. exact (MK_COMB (@lem514385) (@lem514384)). Qed.
Lemma lem514387 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem514388 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem514386) (@lem514387 n)). Qed.
Lemma lem514389 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514390 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem514389) (@lem514388 n)). Qed.
Lemma lem514391 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem514392 (n : nat) : ((term46 n) = n) = ((term47 n) = n).
Proof. exact (MK_COMB (@lem514390 n) (@lem514391 n)). Qed.
Lemma lem514393 : term50 = term51.
Proof. exact (fun_ext (fun n : nat => @lem514392 n)). Qed.
Lemma lem514394 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514395 : term52 = term53.
Proof. exact (MK_COMB (@lem514394) (@lem514393)). Qed.
Lemma lem514396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514397 : term54 = term55.
Proof. exact (MK_COMB (@lem514396) (@lem514395)). Qed.
Lemma lem514399 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem512705 n) (@lem512704 n)). Qed.
Lemma lem514400 : term43 = (BIT1 0).
Proof. exact (@lem514399 (BIT1 0)). Qed.
Lemma lem514401 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem514402 (m : nat) : (term56 m) = (term57 m).
Proof. exact (MK_COMB (@lem514401 m) (@lem514400)). Qed.
Lemma lem514403 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514404 (m : nat) : (term58 m) = (term59 m).
Proof. exact (MK_COMB (@lem514403) (@lem514402 m)). Qed.
Lemma lem514405 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem514406 (m : nat) : ((term56 m) = m) = ((term57 m) = m).
Proof. exact (MK_COMB (@lem514404 m) (@lem514405 m)). Qed.
Lemma lem514407 : term60 = term61.
Proof. exact (fun_ext (fun m : nat => @lem514406 m)). Qed.
Lemma lem514408 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514409 : term62 = term63.
Proof. exact (MK_COMB (@lem514408) (@lem514407)). Qed.
Lemma lem514410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514411 : term64 = term65.
Proof. exact (MK_COMB (@lem514410) (@lem514409)). Qed.
Lemma lem514412 : term66 = term66.
Proof. exact (eq_refl term66). Qed.
Lemma lem514413 : term67 = term68.
Proof. exact (MK_COMB (@lem514411) (@lem514412)). Qed.
Lemma lem514414 : term69 = term70.
Proof. exact (MK_COMB (@lem514397) (@lem514413)). Qed.
Lemma lem514415 : term71 = term72.
Proof. exact (MK_COMB (@lem514381) (@lem514414)). Qed.
Lemma lem514416 : term73 = term74.
Proof. exact (MK_COMB (@lem514365) (@lem514415)). Qed.
Lemma lem514417 : term74.
Proof. exact (EQ_MP (@lem514416) (@lem81645)). Qed.
Lemma lem514418 (m : nat) : term75 m.
Proof. exact (@lem72973 m). Qed.
Lemma lem514419 (m : nat) : (term75 m) = (term76 m).
Proof. exact (eq_refl (term75 m)). Qed.
Lemma lem514420 (m : nat) : term76 m.
Proof. exact (EQ_MP (@lem514419 m) (@lem514418 m)). Qed.
Lemma lem514421 (m : nat) (n : nat) : term77 m n.
Proof. exact (@lem514420 m n). Qed.
Lemma lem514422 (m : nat) (n : nat) : (term77 m n) = (((S m) = (S n)) = (m = n)).
Proof. exact (eq_refl (term77 m n)). Qed.
Lemma lem514424 : term21.
Proof. exact (proj2 (@lem514347)). Qed.
Lemma lem514425 : term19.
Proof. exact (proj2 (@lem514424)). Qed.
Lemma lem514426 : term78.
Proof. exact (proj2 (@lem514425)). Qed.
Lemma lem514427 (m : nat) : term79 m.
Proof. exact (@lem514426 m). Qed.
Lemma lem514428 (m : nat) : (term79 m) = (term80 m).
Proof. exact (eq_refl (term79 m)). Qed.
Lemma lem514429 (m : nat) : term80 m.
Proof. exact (EQ_MP (@lem514428 m) (@lem514427 m)). Qed.
Lemma lem514430 (m : nat) (n : nat) : term81 m n.
Proof. exact (@lem514429 m n). Qed.
Lemma lem514431 (m : nat) (n : nat) : (term81 m n) = ((term82 m n) = (term83 m n)).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem514433 : term84.
Proof. exact (proj1 (@lem514425)). Qed.
Lemma lem514434 (m : nat) : term85 m.
Proof. exact (@lem514433 m). Qed.
Lemma lem514435 (m : nat) : (term85 m) = (term86 m).
Proof. exact (eq_refl (term85 m)). Qed.
Lemma lem514436 (m : nat) : term86 m.
Proof. exact (EQ_MP (@lem514435 m) (@lem514434 m)). Qed.
Lemma lem514437 (m : nat) (n : nat) : term87 m n.
Proof. exact (@lem514436 m n). Qed.
Lemma lem514438 (m : nat) (n : nat) : (term87 m n) = ((term88 m n) = (term83 m n)).
Proof. exact (eq_refl (term87 m n)). Qed.
Lemma lem514448 : term72.
Proof. exact (proj2 (@lem514417)). Qed.
Lemma lem514449 : term70.
Proof. exact (proj2 (@lem514448)). Qed.
Lemma lem514450 : term68.
Proof. exact (proj2 (@lem514449)). Qed.
Lemma lem514451 : term66.
Proof. exact (proj2 (@lem514450)). Qed.
Lemma lem514452 : term89.
Proof. exact (proj2 (@lem514451)). Qed.
Lemma lem514453 (m : nat) : term90 m.
Proof. exact (@lem514452 m). Qed.
Lemma lem514454 (m : nat) : (term90 m) = (term91 m).
Proof. exact (eq_refl (term90 m)). Qed.
Lemma lem514455 (m : nat) : term91 m.
Proof. exact (EQ_MP (@lem514454 m) (@lem514453 m)). Qed.
Lemma lem514456 (m : nat) (n : nat) : term92 m n.
Proof. exact (@lem514455 m n). Qed.
Lemma lem514457 (m : nat) (n : nat) : (term92 m n) = ((term93 m n) = (term94 m n)).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem514459 : term95.
Proof. exact (proj1 (@lem514451)). Qed.
Lemma lem514460 (m : nat) : term96 m.
Proof. exact (@lem514459 m). Qed.
Lemma lem514461 (m : nat) : (term96 m) = (term97 m).
Proof. exact (eq_refl (term96 m)). Qed.
Lemma lem514462 (m : nat) : term97 m.
Proof. exact (EQ_MP (@lem514461 m) (@lem514460 m)). Qed.
Lemma lem514463 (m : nat) (n : nat) : term98 m n.
Proof. exact (@lem514462 m n). Qed.
Lemma lem514464 (m : nat) (n : nat) : (term98 m n) = ((term99 m n) = (term100 m n)).
Proof. exact (eq_refl (term98 m n)). Qed.
Lemma lem514474 : term40.
Proof. exact (proj1 (@lem514448)). Qed.
Lemma lem514475 (m : nat) : term101 m.
Proof. exact (@lem514474 m). Qed.
Lemma lem514476 (m : nat) : (term101 m) = ((Nat.mul m 0) = 0).
Proof. exact (eq_refl (term101 m)). Qed.
Lemma lem514478 : term31.
Proof. exact (proj1 (@lem514417)). Qed.
Lemma lem514479 (n : nat) : term102 n.
Proof. exact (@lem514478 n). Qed.
Lemma lem514480 (n : nat) : (term102 n) = ((Nat.mul 0 n) = 0).
Proof. exact (eq_refl (term102 n)). Qed.
Lemma lem514482 (n : nat) : term103 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem514483 (n : nat) : (term103 n) = ((BIT1 n) = (term104 n)).
Proof. exact (eq_refl (term103 n)). Qed.
Lemma lem514485 (n : nat) : term105 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem514486 (n : nat) : (term105 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term105 n)). Qed.
Lemma lem514488 (n : nat) : term106 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem514489 (n : nat) : (term106 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term106 n)). Qed.
Lemma lem514492 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem514489 n) (@lem514488 n)). Qed.
Lemma lem514493 (m : nat) : (NUMERAL m) = m.
Proof. exact (@lem514492 m). Qed.
Lemma lem514494 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem514495 (m : nat) : (term107 m) = (Nat.mul m).
Proof. exact (MK_COMB (@lem514494) (@lem514493 m)). Qed.
Lemma lem514497 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem514489 n) (@lem514488 n)). Qed.
Lemma lem514498 (m : nat) (n : nat) : (term108 m n) = (Nat.mul m n).
Proof. exact (MK_COMB (@lem514495 m) (@lem514497 n)). Qed.
Lemma lem514499 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514500 (m : nat) (n : nat) : (term109 m n) = (term110 m n).
Proof. exact (MK_COMB (@lem514499) (@lem514498 m n)). Qed.
Lemma lem514502 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem514489 n) (@lem514488 n)). Qed.
Lemma lem514503 (m : nat) (n : nat) : (term111 m n) = (Nat.mul m n).
Proof. exact (@lem514502 (Nat.mul m n)). Qed.
Lemma lem514504 (m : nat) (n : nat) : ((term108 m n) = (term111 m n)) = ((Nat.mul m n) = (Nat.mul m n)).
Proof. exact (MK_COMB (@lem514500 m n) (@lem514503 m n)). Qed.
Lemma lem514505 (m : nat) : (term112 m) = (term113 m).
Proof. exact (fun_ext (fun n : nat => @lem514504 m n)). Qed.
Lemma lem514506 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514507 (m : nat) : (term114 m) = (term115 m).
Proof. exact (MK_COMB (@lem514506) (@lem514505 m)). Qed.
Lemma lem514508 : term116 = term117.
Proof. exact (fun_ext (fun m : nat => @lem514507 m)). Qed.
Lemma lem514509 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514510 : term118 = term119.
Proof. exact (MK_COMB (@lem514509) (@lem514508)). Qed.
Lemma lem514511 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514512 : term120 = term121.
Proof. exact (MK_COMB (@lem514511) (@lem514510)). Qed.
Lemma lem514514 (n : nat) : (Nat.mul 0 n) = 0.
Proof. exact (EQ_MP (@lem514480 n) (@lem514479 n)). Qed.
Lemma lem514515 : (Nat.mul 0 0) = 0.
Proof. exact (@lem514514 0). Qed.
Lemma lem514516 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514517 : term122 = (@eq nat 0).
Proof. exact (MK_COMB (@lem514516) (@lem514515)). Qed.
Lemma lem514518 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem514519 : ((Nat.mul 0 0) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem514517) (@lem514518)). Qed.
Lemma lem514520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514521 : term123 = term124.
Proof. exact (MK_COMB (@lem514520) (@lem514519)). Qed.
Lemma lem514523 (n : nat) : (Nat.mul 0 n) = 0.
Proof. exact (EQ_MP (@lem514480 n) (@lem514479 n)). Qed.
Lemma lem514524 (n : nat) : (term125 n) = 0.
Proof. exact (@lem514523 (BIT0 n)). Qed.
Lemma lem514525 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514526 (n : nat) : (term126 n) = (@eq nat 0).
Proof. exact (MK_COMB (@lem514525) (@lem514524 n)). Qed.
Lemma lem514527 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem514528 (n : nat) : ((term125 n) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem514526 n) (@lem514527)). Qed.
Lemma lem514529 : term127 = term128.
Proof. exact (fun_ext (fun n : nat => @lem514528 n)). Qed.
Lemma lem514530 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514531 : term129 = term130.
Proof. exact (MK_COMB (@lem514530) (@lem514529)). Qed.
Lemma lem514532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514533 : term131 = term132.
Proof. exact (MK_COMB (@lem514532) (@lem514531)). Qed.
Lemma lem514535 (n : nat) : (Nat.mul 0 n) = 0.
Proof. exact (EQ_MP (@lem514480 n) (@lem514479 n)). Qed.
Lemma lem514536 (n : nat) : (term133 n) = 0.
Proof. exact (@lem514535 (BIT1 n)). Qed.
Lemma lem514537 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514538 (n : nat) : (term134 n) = (@eq nat 0).
Proof. exact (MK_COMB (@lem514537) (@lem514536 n)). Qed.
Lemma lem514539 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem514540 (n : nat) : ((term133 n) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem514538 n) (@lem514539)). Qed.
Lemma lem514541 : term135 = term128.
Proof. exact (fun_ext (fun n : nat => @lem514540 n)). Qed.
Lemma lem514542 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514543 : term136 = term130.
Proof. exact (MK_COMB (@lem514542) (@lem514541)). Qed.
Lemma lem514544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514545 : term137 = term132.
Proof. exact (MK_COMB (@lem514544) (@lem514543)). Qed.
Lemma lem514547 (m : nat) : (Nat.mul m 0) = 0.
Proof. exact (EQ_MP (@lem514476 m) (@lem514475 m)). Qed.
Lemma lem514548 (n : nat) : (term138 n) = 0.
Proof. exact (@lem514547 (BIT0 n)). Qed.
Lemma lem514549 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514550 (n : nat) : (term139 n) = (@eq nat 0).
Proof. exact (MK_COMB (@lem514549) (@lem514548 n)). Qed.
Lemma lem514551 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem514552 (n : nat) : ((term138 n) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem514550 n) (@lem514551)). Qed.
Lemma lem514553 : term140 = term128.
Proof. exact (fun_ext (fun n : nat => @lem514552 n)). Qed.
Lemma lem514554 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514555 : term141 = term130.
Proof. exact (MK_COMB (@lem514554) (@lem514553)). Qed.
Lemma lem514556 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514557 : term142 = term132.
Proof. exact (MK_COMB (@lem514556) (@lem514555)). Qed.
Lemma lem514559 (m : nat) : (Nat.mul m 0) = 0.
Proof. exact (EQ_MP (@lem514476 m) (@lem514475 m)). Qed.
Lemma lem514560 (n : nat) : (term143 n) = 0.
Proof. exact (@lem514559 (BIT1 n)). Qed.
Lemma lem514561 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514562 (n : nat) : (term144 n) = (@eq nat 0).
Proof. exact (MK_COMB (@lem514561) (@lem514560 n)). Qed.
Lemma lem514563 : 0 = 0.
Proof. exact (eq_refl 0). Qed.
Lemma lem514564 (n : nat) : ((term143 n) = 0) = (0 = 0).
Proof. exact (MK_COMB (@lem514562 n) (@lem514563)). Qed.
Lemma lem514565 : term145 = term128.
Proof. exact (fun_ext (fun n : nat => @lem514564 n)). Qed.
Lemma lem514566 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514567 : term146 = term130.
Proof. exact (MK_COMB (@lem514566) (@lem514565)). Qed.
Lemma lem514568 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514569 : term147 = term132.
Proof. exact (MK_COMB (@lem514568) (@lem514567)). Qed.
Lemma lem514571 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514572 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem514571 m). Qed.
Lemma lem514573 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem514574 (m : nat) : (term148 m) = (term149 m).
Proof. exact (MK_COMB (@lem514573) (@lem514572 m)). Qed.
Lemma lem514576 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514577 (m : nat) (n : nat) : (term150 m n) = (term151 m n).
Proof. exact (MK_COMB (@lem514574 m) (@lem514576 n)). Qed.
Lemma lem514578 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514579 (m : nat) (n : nat) : (term152 m n) = (term153 m n).
Proof. exact (MK_COMB (@lem514578) (@lem514577 m n)). Qed.
Lemma lem514581 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514582 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (@lem514581 (term156 m n)). Qed.
Lemma lem514584 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514585 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514584 (Nat.mul m n)). Qed.
Lemma lem514586 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514587 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (MK_COMB (@lem514586) (@lem514585 m n)). Qed.
Lemma lem514589 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514590 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514589 (Nat.mul m n)). Qed.
Lemma lem514591 (m : nat) (n : nat) : (term155 m n) = (term160 m n).
Proof. exact (MK_COMB (@lem514587 m n) (@lem514590 m n)). Qed.
Lemma lem514592 (m : nat) (n : nat) : (term154 m n) = (term160 m n).
Proof. exact (TRANS (@lem514582 m n) (@lem514591 m n)). Qed.
Lemma lem514593 (m : nat) (n : nat) : ((term150 m n) = (term154 m n)) = ((term151 m n) = (term160 m n)).
Proof. exact (MK_COMB (@lem514579 m n) (@lem514592 m n)). Qed.
Lemma lem514594 (m : nat) : (term161 m) = (term162 m).
Proof. exact (fun_ext (fun n : nat => @lem514593 m n)). Qed.
Lemma lem514595 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514596 (m : nat) : (term163 m) = (term164 m).
Proof. exact (MK_COMB (@lem514595) (@lem514594 m)). Qed.
Lemma lem514597 : term165 = term166.
Proof. exact (fun_ext (fun m : nat => @lem514596 m)). Qed.
Lemma lem514598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514599 : term167 = term168.
Proof. exact (MK_COMB (@lem514598) (@lem514597)). Qed.
Lemma lem514600 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514601 : term169 = term170.
Proof. exact (MK_COMB (@lem514600) (@lem514599)). Qed.
Lemma lem514603 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514604 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem514603 m). Qed.
Lemma lem514605 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem514606 (m : nat) : (term148 m) = (term149 m).
Proof. exact (MK_COMB (@lem514605) (@lem514604 m)). Qed.
Lemma lem514608 (n : nat) : (BIT1 n) = (term104 n).
Proof. exact (EQ_MP (@lem514483 n) (@lem514482 n)). Qed.
Lemma lem514609 (m : nat) (n : nat) : (term171 m n) = (term172 m n).
Proof. exact (MK_COMB (@lem514606 m) (@lem514608 n)). Qed.
Lemma lem514611 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (EQ_MP (@lem514457 m n) (@lem514456 m n)). Qed.
Lemma lem514612 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (@lem514611 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem514613 (m : nat) (n : nat) : (term171 m n) = (term173 m n).
Proof. exact (TRANS (@lem514609 m n) (@lem514612 m n)). Qed.
Lemma lem514614 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514615 (m : nat) (n : nat) : (term174 m n) = (term175 m n).
Proof. exact (MK_COMB (@lem514614) (@lem514613 m n)). Qed.
Lemma lem514617 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514618 (m : nat) : (BIT0 m) = (Nat.add m m).
Proof. exact (@lem514617 m). Qed.
Lemma lem514619 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514620 (m : nat) : (term176 m) = (term177 m).
Proof. exact (MK_COMB (@lem514619) (@lem514618 m)). Qed.
Lemma lem514622 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514623 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (@lem514622 (term156 m n)). Qed.
Lemma lem514625 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514626 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514625 (Nat.mul m n)). Qed.
Lemma lem514627 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514628 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (MK_COMB (@lem514627) (@lem514626 m n)). Qed.
Lemma lem514630 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514631 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514630 (Nat.mul m n)). Qed.
Lemma lem514632 (m : nat) (n : nat) : (term155 m n) = (term160 m n).
Proof. exact (MK_COMB (@lem514628 m n) (@lem514631 m n)). Qed.
Lemma lem514633 (m : nat) (n : nat) : (term154 m n) = (term160 m n).
Proof. exact (TRANS (@lem514623 m n) (@lem514632 m n)). Qed.
Lemma lem514634 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (MK_COMB (@lem514620 m) (@lem514633 m n)). Qed.
Lemma lem514635 (m : nat) (n : nat) : ((term171 m n) = (term178 m n)) = ((term173 m n) = (term179 m n)).
Proof. exact (MK_COMB (@lem514615 m n) (@lem514634 m n)). Qed.
Lemma lem514636 (m : nat) : (term180 m) = (term181 m).
Proof. exact (fun_ext (fun n : nat => @lem514635 m n)). Qed.
Lemma lem514637 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514638 (m : nat) : (term182 m) = (term183 m).
Proof. exact (MK_COMB (@lem514637) (@lem514636 m)). Qed.
Lemma lem514639 : term184 = term185.
Proof. exact (fun_ext (fun m : nat => @lem514638 m)). Qed.
Lemma lem514640 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514641 : term186 = term187.
Proof. exact (MK_COMB (@lem514640) (@lem514639)). Qed.
Lemma lem514642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514643 : term188 = term189.
Proof. exact (MK_COMB (@lem514642) (@lem514641)). Qed.
Lemma lem514645 (n : nat) : (BIT1 n) = (term104 n).
Proof. exact (EQ_MP (@lem514483 n) (@lem514482 n)). Qed.
Lemma lem514646 (m : nat) : (BIT1 m) = (term104 m).
Proof. exact (@lem514645 m). Qed.
Lemma lem514647 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem514648 (m : nat) : (term190 m) = (term191 m).
Proof. exact (MK_COMB (@lem514647) (@lem514646 m)). Qed.
Lemma lem514650 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514651 (m : nat) (n : nat) : (term192 m n) = (term193 m n).
Proof. exact (MK_COMB (@lem514648 m) (@lem514650 n)). Qed.
Lemma lem514653 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (EQ_MP (@lem514464 m n) (@lem514463 m n)). Qed.
Lemma lem514654 (m : nat) (n : nat) : (term193 m n) = (term194 m n).
Proof. exact (@lem514653 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem514655 (m : nat) (n : nat) : (term192 m n) = (term194 m n).
Proof. exact (TRANS (@lem514651 m n) (@lem514654 m n)). Qed.
Lemma lem514656 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514657 (m : nat) (n : nat) : (term195 m n) = (term196 m n).
Proof. exact (MK_COMB (@lem514656) (@lem514655 m n)). Qed.
Lemma lem514659 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514660 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514661 (n : nat) : (term176 n) = (term177 n).
Proof. exact (MK_COMB (@lem514660) (@lem514659 n)). Qed.
Lemma lem514663 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514664 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (@lem514663 (term156 m n)). Qed.
Lemma lem514666 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514667 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514666 (Nat.mul m n)). Qed.
Lemma lem514668 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514669 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (MK_COMB (@lem514668) (@lem514667 m n)). Qed.
Lemma lem514671 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514672 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514671 (Nat.mul m n)). Qed.
Lemma lem514673 (m : nat) (n : nat) : (term155 m n) = (term160 m n).
Proof. exact (MK_COMB (@lem514669 m n) (@lem514672 m n)). Qed.
Lemma lem514674 (m : nat) (n : nat) : (term154 m n) = (term160 m n).
Proof. exact (TRANS (@lem514664 m n) (@lem514673 m n)). Qed.
Lemma lem514675 (m : nat) (n : nat) : (term197 m n) = (term198 m n).
Proof. exact (MK_COMB (@lem514661 n) (@lem514674 m n)). Qed.
Lemma lem514676 (m : nat) (n : nat) : ((term192 m n) = (term197 m n)) = ((term194 m n) = (term198 m n)).
Proof. exact (MK_COMB (@lem514657 m n) (@lem514675 m n)). Qed.
Lemma lem514677 (m : nat) : (term199 m) = (term200 m).
Proof. exact (fun_ext (fun n : nat => @lem514676 m n)). Qed.
Lemma lem514678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514679 (m : nat) : (term201 m) = (term202 m).
Proof. exact (MK_COMB (@lem514678) (@lem514677 m)). Qed.
Lemma lem514680 : term203 = term204.
Proof. exact (fun_ext (fun m : nat => @lem514679 m)). Qed.
Lemma lem514681 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514682 : term205 = term206.
Proof. exact (MK_COMB (@lem514681) (@lem514680)). Qed.
Lemma lem514683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem514684 : term207 = term208.
Proof. exact (MK_COMB (@lem514683) (@lem514682)). Qed.
Lemma lem514686 (n : nat) : (BIT1 n) = (term104 n).
Proof. exact (EQ_MP (@lem514483 n) (@lem514482 n)). Qed.
Lemma lem514687 (m : nat) : (BIT1 m) = (term104 m).
Proof. exact (@lem514686 m). Qed.
Lemma lem514688 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem514689 (m : nat) : (term190 m) = (term191 m).
Proof. exact (MK_COMB (@lem514688) (@lem514687 m)). Qed.
Lemma lem514691 (n : nat) : (BIT1 n) = (term104 n).
Proof. exact (EQ_MP (@lem514483 n) (@lem514482 n)). Qed.
Lemma lem514692 (m : nat) (n : nat) : (term209 m n) = (term210 m n).
Proof. exact (MK_COMB (@lem514689 m) (@lem514691 n)). Qed.
Lemma lem514694 (m : nat) (n : nat) : (term99 m n) = (term100 m n).
Proof. exact (EQ_MP (@lem514464 m n) (@lem514463 m n)). Qed.
Lemma lem514695 (m : nat) (n : nat) : (term210 m n) = (term211 m n).
Proof. exact (@lem514694 (Nat.add m m) (term104 n)). Qed.
Lemma lem514697 (m : nat) (n : nat) : (term82 m n) = (term83 m n).
Proof. exact (EQ_MP (@lem514431 m n) (@lem514430 m n)). Qed.
Lemma lem514698 (m : nat) (n : nat) : (term211 m n) = (term212 m n).
Proof. exact (@lem514697 (term172 m n) (Nat.add n n)). Qed.
Lemma lem514700 (m : nat) (n : nat) : (term93 m n) = (term94 m n).
Proof. exact (EQ_MP (@lem514457 m n) (@lem514456 m n)). Qed.
Lemma lem514701 (m : nat) (n : nat) : (term172 m n) = (term173 m n).
Proof. exact (@lem514700 (Nat.add m m) (Nat.add n n)). Qed.
Lemma lem514702 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514703 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (MK_COMB (@lem514702) (@lem514701 m n)). Qed.
Lemma lem514704 (n : nat) : (Nat.add n n) = (Nat.add n n).
Proof. exact (eq_refl (Nat.add n n)). Qed.
Lemma lem514705 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (MK_COMB (@lem514703 m n) (@lem514704 n)). Qed.
Lemma lem514706 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem514707 (m : nat) (n : nat) : (term212 m n) = (term217 m n).
Proof. exact (MK_COMB (@lem514706) (@lem514705 m n)). Qed.
Lemma lem514708 (m : nat) (n : nat) : (term211 m n) = (term217 m n).
Proof. exact (TRANS (@lem514698 m n) (@lem514707 m n)). Qed.
Lemma lem514709 (m : nat) (n : nat) : (term210 m n) = (term217 m n).
Proof. exact (TRANS (@lem514695 m n) (@lem514708 m n)). Qed.
Lemma lem514710 (m : nat) (n : nat) : (term209 m n) = (term217 m n).
Proof. exact (TRANS (@lem514692 m n) (@lem514709 m n)). Qed.
Lemma lem514711 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem514712 (m : nat) (n : nat) : (term218 m n) = (term219 m n).
Proof. exact (MK_COMB (@lem514711) (@lem514710 m n)). Qed.
Lemma lem514714 (n : nat) : (BIT1 n) = (term104 n).
Proof. exact (EQ_MP (@lem514483 n) (@lem514482 n)). Qed.
Lemma lem514715 (m : nat) : (BIT1 m) = (term104 m).
Proof. exact (@lem514714 m). Qed.
Lemma lem514716 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514717 (m : nat) : (term220 m) = (term221 m).
Proof. exact (MK_COMB (@lem514716) (@lem514715 m)). Qed.
Lemma lem514719 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514720 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514721 (n : nat) : (term176 n) = (term177 n).
Proof. exact (MK_COMB (@lem514720) (@lem514719 n)). Qed.
Lemma lem514723 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514724 (m : nat) (n : nat) : (term154 m n) = (term155 m n).
Proof. exact (@lem514723 (term156 m n)). Qed.
Lemma lem514726 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514727 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514726 (Nat.mul m n)). Qed.
Lemma lem514728 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem514729 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (MK_COMB (@lem514728) (@lem514727 m n)). Qed.
Lemma lem514731 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem514486 n) (@lem514485 n)). Qed.
Lemma lem514732 (m : nat) (n : nat) : (term156 m n) = (term157 m n).
Proof. exact (@lem514731 (Nat.mul m n)). Qed.
Lemma lem514733 (m : nat) (n : nat) : (term155 m n) = (term160 m n).
Proof. exact (MK_COMB (@lem514729 m n) (@lem514732 m n)). Qed.
Lemma lem514734 (m : nat) (n : nat) : (term154 m n) = (term160 m n).
Proof. exact (TRANS (@lem514724 m n) (@lem514733 m n)). Qed.
Lemma lem514735 (m : nat) (n : nat) : (term197 m n) = (term198 m n).
Proof. exact (MK_COMB (@lem514721 n) (@lem514734 m n)). Qed.
Lemma lem514736 (m : nat) (n : nat) : (term222 m n) = (term223 m n).
Proof. exact (MK_COMB (@lem514717 m) (@lem514735 m n)). Qed.
Lemma lem514738 (m : nat) (n : nat) : (term88 m n) = (term83 m n).
Proof. exact (EQ_MP (@lem514438 m n) (@lem514437 m n)). Qed.
Lemma lem514739 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (@lem514738 (Nat.add m m) (term198 m n)). Qed.
Lemma lem514740 (m : nat) (n : nat) : (term222 m n) = (term224 m n).
Proof. exact (TRANS (@lem514736 m n) (@lem514739 m n)). Qed.
Lemma lem514741 (m : nat) (n : nat) : ((term209 m n) = (term222 m n)) = ((term217 m n) = (term224 m n)).
Proof. exact (MK_COMB (@lem514712 m n) (@lem514740 m n)). Qed.
Lemma lem514743 (m : nat) (n : nat) : ((S m) = (S n)) = (m = n).
Proof. exact (EQ_MP (@lem514422 m n) (@lem514421 m n)). Qed.
Lemma lem514744 (m : nat) (n : nat) : ((term217 m n) = (term224 m n)) = ((term216 m n) = (term225 m n)).
Proof. exact (@lem514743 (term216 m n) (term225 m n)). Qed.
Lemma lem514745 (m : nat) (n : nat) : ((term209 m n) = (term222 m n)) = ((term216 m n) = (term225 m n)).
Proof. exact (TRANS (@lem514741 m n) (@lem514744 m n)). Qed.
Lemma lem514746 (m : nat) : (term226 m) = (term227 m).
Proof. exact (fun_ext (fun n : nat => @lem514745 m n)). Qed.
Lemma lem514747 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514748 (m : nat) : (term228 m) = (term229 m).
Proof. exact (MK_COMB (@lem514747) (@lem514746 m)). Qed.
Lemma lem514749 : term230 = term231.
Proof. exact (fun_ext (fun m : nat => @lem514748 m)). Qed.
Lemma lem514750 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem514751 : term232 = term233.
Proof. exact (MK_COMB (@lem514750) (@lem514749)). Qed.
Lemma lem514752 : term234 = term235.
Proof. exact (MK_COMB (@lem514684) (@lem514751)). Qed.
Lemma lem514753 : term236 = term237.
Proof. exact (MK_COMB (@lem514643) (@lem514752)). Qed.
Lemma lem514754 : term238 = term239.
Proof. exact (MK_COMB (@lem514601) (@lem514753)). Qed.
Lemma lem514755 : term240 = term241.
Proof. exact (MK_COMB (@lem514569) (@lem514754)). Qed.
Lemma lem514756 : term242 = term243.
Proof. exact (MK_COMB (@lem514557) (@lem514755)). Qed.
Lemma lem514757 : term244 = term245.
Proof. exact (MK_COMB (@lem514545) (@lem514756)). Qed.
Lemma lem514758 : term246 = term247.
Proof. exact (MK_COMB (@lem514533) (@lem514757)). Qed.
Lemma lem514759 : term248 = term249.
Proof. exact (MK_COMB (@lem514521) (@lem514758)). Qed.
Lemma lem514760 : term250 = term251.
Proof. exact (MK_COMB (@lem514512) (@lem514759)). Qed.
Lemma lem514761 : term251 = term250.
Proof. exact (SYM (@lem514760)). Qed.
