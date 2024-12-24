Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUB_SUC_term_abbrevs.
Require Import SUB_PRESUC_spec.
Require Import thm0_spec.
Require Import thm135075_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem135347 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135348 : term1.
Proof. exact (@lem135347 term2). Qed.
Lemma lem135349 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem135350 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135351 : term5 = term6.
Proof. exact (MK_COMB (@lem135350) (@lem135349)). Qed.
Lemma lem135352 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem135353 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135354 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem135353) (@lem135352 m)). Qed.
Lemma lem135355 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem135356 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem135354 m) (@lem135355 m)). Qed.
Lemma lem135357 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem135356 m)). Qed.
Lemma lem135358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135359 : term17 = term18.
Proof. exact (MK_COMB (@lem135358) (@lem135357)). Qed.
Lemma lem135360 : term19 = term20.
Proof. exact (MK_COMB (@lem135351) (@lem135359)). Qed.
Lemma lem135361 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135362 : term21 = term22.
Proof. exact (MK_COMB (@lem135361) (@lem135360)). Qed.
Lemma lem135363 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem135364 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem135363 m)). Qed.
Lemma lem135365 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135366 : term24 = term25.
Proof. exact (MK_COMB (@lem135365) (@lem135364)). Qed.
Lemma lem135367 : term1 = term26.
Proof. exact (MK_COMB (@lem135362) (@lem135366)). Qed.
Lemma lem135368 : term26.
Proof. exact (EQ_MP (@lem135367) (@lem135348)). Qed.
Lemma lem135369 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem135371 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135372 : term27.
Proof. exact (@lem135371 term28). Qed.
Lemma lem135373 : term29 = (term30 = term31).
Proof. exact (eq_refl term29). Qed.
Lemma lem135374 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135375 : term32 = term33.
Proof. exact (MK_COMB (@lem135374) (@lem135373)). Qed.
Lemma lem135376 (n : nat) : (term34 n) = ((term35 n) = (term36 n)).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem135377 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135378 (n : nat) : (term37 n) = (term38 n).
Proof. exact (MK_COMB (@lem135377) (@lem135376 n)). Qed.
Lemma lem135379 (n : nat) : (term39 n) = ((term40 n) = (term41 n)).
Proof. exact (eq_refl (term39 n)). Qed.
Lemma lem135380 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem135378 n) (@lem135379 n)). Qed.
Lemma lem135381 : term44 = term45.
Proof. exact (fun_ext (fun n : nat => @lem135380 n)). Qed.
Lemma lem135382 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135383 : term46 = term47.
Proof. exact (MK_COMB (@lem135382) (@lem135381)). Qed.
Lemma lem135384 : term48 = term49.
Proof. exact (MK_COMB (@lem135375) (@lem135383)). Qed.
Lemma lem135385 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135386 : term50 = term51.
Proof. exact (MK_COMB (@lem135385) (@lem135384)). Qed.
Lemma lem135387 (n : nat) : (term34 n) = ((term35 n) = (term36 n)).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem135388 : term52 = term28.
Proof. exact (fun_ext (fun n : nat => @lem135387 n)). Qed.
Lemma lem135389 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135390 : term53 = term4.
Proof. exact (MK_COMB (@lem135389) (@lem135388)). Qed.
Lemma lem135391 : term27 = term54.
Proof. exact (MK_COMB (@lem135386) (@lem135390)). Qed.
Lemma lem135392 : term54.
Proof. exact (EQ_MP (@lem135391) (@lem135372)). Qed.
Lemma lem135399 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem135400 (m : nat) : term55 m.
Proof. exact (@lem135399 (term56 m)). Qed.
Lemma lem135401 (m : nat) : (term57 m) = ((term58 m) = (term59 m)).
Proof. exact (eq_refl (term57 m)). Qed.
Lemma lem135402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem135403 (m : nat) : (term60 m) = (term61 m).
Proof. exact (MK_COMB (@lem135402) (@lem135401 m)). Qed.
Lemma lem135404 (m : nat) (n : nat) : (term62 m n) = ((term63 m n) = (term64 m n)).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem135405 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135406 (m : nat) (n : nat) : (term65 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem135405) (@lem135404 m n)). Qed.
Lemma lem135407 (m : nat) (n : nat) : (term67 m n) = ((term68 m n) = (term69 m n)).
Proof. exact (eq_refl (term67 m n)). Qed.
Lemma lem135408 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem135406 m n) (@lem135407 m n)). Qed.
Lemma lem135409 (m : nat) : (term72 m) = (term73 m).
Proof. exact (fun_ext (fun n : nat => @lem135408 m n)). Qed.
Lemma lem135410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135411 (m : nat) : (term74 m) = (term75 m).
Proof. exact (MK_COMB (@lem135410) (@lem135409 m)). Qed.
Lemma lem135412 (m : nat) : (term76 m) = (term77 m).
Proof. exact (MK_COMB (@lem135403 m) (@lem135411 m)). Qed.
Lemma lem135413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem135414 (m : nat) : (term78 m) = (term79 m).
Proof. exact (MK_COMB (@lem135413) (@lem135412 m)). Qed.
Lemma lem135415 (m : nat) (n : nat) : (term62 m n) = ((term63 m n) = (term64 m n)).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem135416 (m : nat) : (term80 m) = (term56 m).
Proof. exact (fun_ext (fun n : nat => @lem135415 m n)). Qed.
Lemma lem135417 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem135418 (m : nat) : (term81 m) = (term12 m).
Proof. exact (MK_COMB (@lem135417) (@lem135416 m)). Qed.
Lemma lem135419 (m : nat) : (term55 m) = (term82 m).
Proof. exact (MK_COMB (@lem135414 m) (@lem135418 m)). Qed.
Lemma lem135420 (m : nat) : term82 m.
Proof. exact (EQ_MP (@lem135419 m) (@lem135400 m)). Qed.
Lemma lem135426 (m : nat) : term83 m.
Proof. exact (@lem135345 m). Qed.
Lemma lem135427 (m : nat) : (term83 m) = (term84 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem135428 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem135427 m) (@lem135426 m)). Qed.
Lemma lem135429 (m : nat) (n : nat) : term85 m n.
Proof. exact (@lem135428 m n). Qed.
Lemma lem135430 (m : nat) (n : nat) : (term85 m n) = ((term86 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem135437 : term87.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem135438 (m : nat) : term88 m.
Proof. exact (@lem135437 m). Qed.
Lemma lem135439 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem135440 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem135439 m) (@lem135438 m)). Qed.
Lemma lem135441 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem135440 m n). Qed.
Lemma lem135442 (m : nat) (n : nat) : (term90 m n) = ((term91 m n) = (term92 m n)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem135444 : term93.
Proof. exact (proj1 (@lem135075)). Qed.
Lemma lem135445 (m : nat) : term94 m.
Proof. exact (@lem135444 m). Qed.
Lemma lem135446 (m : nat) : (term94 m) = ((term95 m) = m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem135451 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (EQ_MP (@lem135442 m n) (@lem135441 m n)). Qed.
Lemma lem135452 : term30 = term96.
Proof. exact (@lem135451 term97 (NUMERAL 0)). Qed.
Lemma lem135454 (m : nat) (n : nat) : (term86 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135430 m n) (@lem135429 m n)). Qed.
Lemma lem135455 : term96 = term31.
Proof. exact (@lem135454 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem135457 (m : nat) : (term95 m) = m.
Proof. exact (EQ_MP (@lem135446 m) (@lem135445 m)). Qed.
Lemma lem135458 : term31 = (NUMERAL 0).
Proof. exact (@lem135457 (NUMERAL 0)). Qed.
Lemma lem135459 : term96 = (NUMERAL 0).
Proof. exact (TRANS (@lem135455) (@lem135458)). Qed.
Lemma lem135460 : term30 = (NUMERAL 0).
Proof. exact (TRANS (@lem135452) (@lem135459)). Qed.
Lemma lem135461 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135462 : term98 = term99.
Proof. exact (MK_COMB (@lem135461) (@lem135460)). Qed.
Lemma lem135464 (m : nat) : (term95 m) = m.
Proof. exact (EQ_MP (@lem135446 m) (@lem135445 m)). Qed.
Lemma lem135465 : term31 = (NUMERAL 0).
Proof. exact (@lem135464 (NUMERAL 0)). Qed.
Lemma lem135466 : (term30 = term31) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem135462) (@lem135465)). Qed.
Lemma lem135468 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135469 (x : nat) : (x = x) = True.
Proof. exact (@lem135468 nat x). Qed.
Lemma lem135470 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem135469 (NUMERAL 0)). Qed.
Lemma lem135471 : (term30 = term31) = True.
Proof. exact (TRANS (@lem135466) (@lem135470)). Qed.
Lemma lem135472 : True = (term30 = term31).
Proof. exact (SYM (@lem135471)). Qed.
Lemma lem135473 : term30 = term31.
Proof. exact (EQ_MP (@lem135472) (@lem0)). Qed.
Lemma lem135474 (m : nat) : term83 m.
Proof. exact (@lem135345 m). Qed.
Lemma lem135475 (m : nat) : (term83 m) = (term84 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem135476 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem135475 m) (@lem135474 m)). Qed.
Lemma lem135477 (m : nat) (n : nat) : term85 m n.
Proof. exact (@lem135476 m n). Qed.
Lemma lem135478 (m : nat) (n : nat) : (term85 m n) = ((term86 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem135485 : term87.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem135486 (m : nat) : term88 m.
Proof. exact (@lem135485 m). Qed.
Lemma lem135487 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem135488 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem135487 m) (@lem135486 m)). Qed.
Lemma lem135489 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem135488 m n). Qed.
Lemma lem135490 (m : nat) (n : nat) : (term90 m n) = ((term91 m n) = (term92 m n)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem135499 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (EQ_MP (@lem135490 m n) (@lem135489 m n)). Qed.
Lemma lem135500 (n : nat) : (term40 n) = (term100 n).
Proof. exact (@lem135499 term97 (S n)). Qed.
Lemma lem135502 (m : nat) (n : nat) : (term86 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135478 m n) (@lem135477 m n)). Qed.
Lemma lem135503 (n : nat) : (term100 n) = (term41 n).
Proof. exact (@lem135502 (NUMERAL 0) (S n)). Qed.
Lemma lem135505 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (EQ_MP (@lem135490 m n) (@lem135489 m n)). Qed.
Lemma lem135506 (n : nat) : (term41 n) = (term101 n).
Proof. exact (@lem135505 (NUMERAL 0) n). Qed.
Lemma lem135507 (n : nat) : (term100 n) = (term101 n).
Proof. exact (TRANS (@lem135503 n) (@lem135506 n)). Qed.
Lemma lem135508 (n : nat) : (term40 n) = (term101 n).
Proof. exact (TRANS (@lem135500 n) (@lem135507 n)). Qed.
Lemma lem135509 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135510 (n : nat) : (term102 n) = (term103 n).
Proof. exact (MK_COMB (@lem135509) (@lem135508 n)). Qed.
Lemma lem135512 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (EQ_MP (@lem135490 m n) (@lem135489 m n)). Qed.
Lemma lem135513 (n : nat) : (term41 n) = (term101 n).
Proof. exact (@lem135512 (NUMERAL 0) n). Qed.
Lemma lem135514 (n : nat) : ((term40 n) = (term41 n)) = ((term101 n) = (term101 n)).
Proof. exact (MK_COMB (@lem135510 n) (@lem135513 n)). Qed.
Lemma lem135516 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135517 (x : nat) : (x = x) = True.
Proof. exact (@lem135516 nat x). Qed.
Lemma lem135518 (n : nat) : ((term101 n) = (term101 n)) = True.
Proof. exact (@lem135517 (term101 n)). Qed.
Lemma lem135519 (n : nat) : ((term40 n) = (term41 n)) = True.
Proof. exact (TRANS (@lem135514 n) (@lem135518 n)). Qed.
Lemma lem135520 (n : nat) : True = ((term40 n) = (term41 n)).
Proof. exact (SYM (@lem135519 n)). Qed.
Lemma lem135521 (n : nat) : (term40 n) = (term41 n).
Proof. exact (EQ_MP (@lem135520 n) (@lem0)). Qed.
Lemma lem135522 (m : nat) : term83 m.
Proof. exact (@lem135345 m). Qed.
Lemma lem135523 (m : nat) : (term83 m) = (term84 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem135524 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem135523 m) (@lem135522 m)). Qed.
Lemma lem135525 (m : nat) (n : nat) : term85 m n.
Proof. exact (@lem135524 m n). Qed.
Lemma lem135526 (m : nat) (n : nat) : (term85 m n) = ((term86 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem135533 : term87.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem135534 (m : nat) : term88 m.
Proof. exact (@lem135533 m). Qed.
Lemma lem135535 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem135536 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem135535 m) (@lem135534 m)). Qed.
Lemma lem135537 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem135536 m n). Qed.
Lemma lem135538 (m : nat) (n : nat) : (term90 m n) = ((term91 m n) = (term92 m n)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem135540 : term93.
Proof. exact (proj1 (@lem135075)). Qed.
Lemma lem135541 (m : nat) : term94 m.
Proof. exact (@lem135540 m). Qed.
Lemma lem135542 (m : nat) : (term94 m) = ((term95 m) = m).
Proof. exact (eq_refl (term94 m)). Qed.
Lemma lem135550 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (EQ_MP (@lem135538 m n) (@lem135537 m n)). Qed.
Lemma lem135551 (m : nat) : (term58 m) = (term104 m).
Proof. exact (@lem135550 (term105 m) (NUMERAL 0)). Qed.
Lemma lem135553 (m : nat) (n : nat) : (term86 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135526 m n) (@lem135525 m n)). Qed.
Lemma lem135554 (m : nat) : (term104 m) = (term59 m).
Proof. exact (@lem135553 (S m) (NUMERAL 0)). Qed.
Lemma lem135556 (m : nat) : (term95 m) = m.
Proof. exact (EQ_MP (@lem135542 m) (@lem135541 m)). Qed.
Lemma lem135557 (m : nat) : (term59 m) = (S m).
Proof. exact (@lem135556 (S m)). Qed.
Lemma lem135558 (m : nat) : (term104 m) = (S m).
Proof. exact (TRANS (@lem135554 m) (@lem135557 m)). Qed.
Lemma lem135559 (m : nat) : (term58 m) = (S m).
Proof. exact (TRANS (@lem135551 m) (@lem135558 m)). Qed.
Lemma lem135560 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135561 (m : nat) : (term106 m) = (term107 m).
Proof. exact (MK_COMB (@lem135560) (@lem135559 m)). Qed.
Lemma lem135563 (m : nat) : (term95 m) = m.
Proof. exact (EQ_MP (@lem135542 m) (@lem135541 m)). Qed.
Lemma lem135564 (m : nat) : (term59 m) = (S m).
Proof. exact (@lem135563 (S m)). Qed.
Lemma lem135565 (m : nat) : ((term58 m) = (term59 m)) = ((S m) = (S m)).
Proof. exact (MK_COMB (@lem135561 m) (@lem135564 m)). Qed.
Lemma lem135567 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135568 (x : nat) : (x = x) = True.
Proof. exact (@lem135567 nat x). Qed.
Lemma lem135569 (m : nat) : ((S m) = (S m)) = True.
Proof. exact (@lem135568 (S m)). Qed.
Lemma lem135570 (m : nat) : ((term58 m) = (term59 m)) = True.
Proof. exact (TRANS (@lem135565 m) (@lem135569 m)). Qed.
Lemma lem135571 (m : nat) : True = ((term58 m) = (term59 m)).
Proof. exact (SYM (@lem135570 m)). Qed.
Lemma lem135572 (m : nat) : (term58 m) = (term59 m).
Proof. exact (EQ_MP (@lem135571 m) (@lem0)). Qed.
Lemma lem135573 (m : nat) : term83 m.
Proof. exact (@lem135345 m). Qed.
Lemma lem135574 (m : nat) : (term83 m) = (term84 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem135575 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem135574 m) (@lem135573 m)). Qed.
Lemma lem135576 (m : nat) (n : nat) : term85 m n.
Proof. exact (@lem135575 m n). Qed.
Lemma lem135577 (m : nat) (n : nat) : (term85 m n) = ((term86 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem135584 : term87.
Proof. exact (proj2 (@lem135075)). Qed.
Lemma lem135585 (m : nat) : term88 m.
Proof. exact (@lem135584 m). Qed.
Lemma lem135586 (m : nat) : (term88 m) = (term89 m).
Proof. exact (eq_refl (term88 m)). Qed.
Lemma lem135587 (m : nat) : term89 m.
Proof. exact (EQ_MP (@lem135586 m) (@lem135585 m)). Qed.
Lemma lem135588 (m : nat) (n : nat) : term90 m n.
Proof. exact (@lem135587 m n). Qed.
Lemma lem135589 (m : nat) (n : nat) : (term90 m n) = ((term91 m n) = (term92 m n)).
Proof. exact (eq_refl (term90 m n)). Qed.
Lemma lem135595 (n : nat) (m : nat) (h1 : term8 m) : term108 m n.
Proof. exact (@lem135369 m h1 n). Qed.
Lemma lem135596 (m : nat) (n : nat) : (term108 m n) = ((term69 m n) = (Nat.sub m n)).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem135601 (m : nat) (n : nat) : (term91 m n) = (term92 m n).
Proof. exact (EQ_MP (@lem135589 m n) (@lem135588 m n)). Qed.
Lemma lem135602 (m : nat) (n : nat) : (term68 m n) = (term109 m n).
Proof. exact (@lem135601 (term105 m) (S n)). Qed.
Lemma lem135604 (m : nat) (n : nat) : (term86 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135577 m n) (@lem135576 m n)). Qed.
Lemma lem135605 (m : nat) (n : nat) : (term109 m n) = (term69 m n).
Proof. exact (@lem135604 (S m) (S n)). Qed.
Lemma lem135607 (n : nat) (m : nat) (h1 : term8 m) : (term69 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135596 m n) (@lem135595 n m h1)). Qed.
Lemma lem135608 (n : nat) (m : nat) (h1 : term8 m) : (term109 m n) = (Nat.sub m n).
Proof. exact (TRANS (@lem135605 m n) (@lem135607 n m h1)). Qed.
Lemma lem135609 (n : nat) (m : nat) (h1 : term8 m) : (term68 m n) = (Nat.sub m n).
Proof. exact (TRANS (@lem135602 m n) (@lem135608 n m h1)). Qed.
Lemma lem135610 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem135611 (n : nat) (m : nat) (h1 : term8 m) : (term110 m n) = (term111 m n).
Proof. exact (MK_COMB (@lem135610) (@lem135609 n m h1)). Qed.
Lemma lem135613 (n : nat) (m : nat) (h1 : term8 m) : (term69 m n) = (Nat.sub m n).
Proof. exact (EQ_MP (@lem135596 m n) (@lem135595 n m h1)). Qed.
Lemma lem135614 (n : nat) (m : nat) (h1 : term8 m) : ((term68 m n) = (term69 m n)) = ((Nat.sub m n) = (Nat.sub m n)).
Proof. exact (MK_COMB (@lem135611 n m h1) (@lem135613 n m h1)). Qed.
Lemma lem135616 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem135617 (x : nat) : (x = x) = True.
Proof. exact (@lem135616 nat x). Qed.
Lemma lem135618 (m : nat) (n : nat) : ((Nat.sub m n) = (Nat.sub m n)) = True.
Proof. exact (@lem135617 (Nat.sub m n)). Qed.
Lemma lem135619 (n : nat) (m : nat) (h1 : term8 m) : ((term68 m n) = (term69 m n)) = True.
Proof. exact (TRANS (@lem135614 n m h1) (@lem135618 m n)). Qed.
Lemma lem135620 (n : nat) (m : nat) (h1 : term8 m) : True = ((term68 m n) = (term69 m n)).
Proof. exact (SYM (@lem135619 n m h1)). Qed.
Lemma lem135621 (n : nat) (m : nat) (h1 : term8 m) : (term68 m n) = (term69 m n).
Proof. exact (EQ_MP (@lem135620 n m h1) (@lem0)). Qed.
Lemma lem135622 (n : nat) (m : nat) (h1 : term8 m) : term71 m n.
Proof. exact (fun h0 : (term63 m n) = (term64 m n) => @lem135621 n m h1). Qed.
Lemma lem135627 (m : nat) (h1 : term8 m) : term75 m.
Proof. exact (fun n : nat => @lem135622 n m h1). Qed.
Lemma lem135628 (m : nat) (h1 : term8 m) : term77 m.
Proof. exact (conj (@lem135572 m) (@lem135627 m h1)). Qed.
Lemma lem135629 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (@lem135420 m (@lem135628 m h1)). Qed.
Lemma lem135630 (n : nat) : term43 n.
Proof. exact (fun h0 : (term35 n) = (term36 n) => @lem135521 n). Qed.
Lemma lem135635 : term47.
Proof. exact (fun n : nat => @lem135630 n). Qed.
Lemma lem135636 : term49.
Proof. exact (conj (@lem135473) (@lem135635)). Qed.
Lemma lem135637 : term4.
Proof. exact (@lem135392 (@lem135636)). Qed.
Lemma lem135638 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem135629 m h0). Qed.
Lemma lem135643 : term18.
Proof. exact (fun m : nat => @lem135638 m). Qed.
Lemma lem135644 : term20.
Proof. exact (conj (@lem135637) (@lem135643)). Qed.
Lemma lem135645 : term25.
Proof. exact (@lem135368 (@lem135644)). Qed.
