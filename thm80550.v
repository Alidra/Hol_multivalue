Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm80550_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import BIT0_spec.
Require Import BIT1_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75543_spec.
Lemma lem80362 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem80363 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem80374 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80363 n) (@lem80362 n)). Qed.
Lemma lem80375 : (NUMERAL 0) = 0.
Proof. exact (@lem80374 0). Qed.
Lemma lem80376 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem80377 : term1 = (Nat.add 0).
Proof. exact (MK_COMB (@lem80376) (@lem80375)). Qed.
Lemma lem80378 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80379 (n : nat) : (term2 n) = (Nat.add 0 n).
Proof. exact (MK_COMB (@lem80377) (@lem80378 n)). Qed.
Lemma lem80380 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80381 (n : nat) : (term3 n) = (term4 n).
Proof. exact (MK_COMB (@lem80380) (@lem80379 n)). Qed.
Lemma lem80382 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem80383 (n : nat) : ((term2 n) = n) = ((Nat.add 0 n) = n).
Proof. exact (MK_COMB (@lem80381 n) (@lem80382 n)). Qed.
Lemma lem80386 : term5 = term6.
Proof. exact (fun_ext (fun n : nat => @lem80383 n)). Qed.
Lemma lem80387 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80388 : term7 = term8.
Proof. exact (MK_COMB (@lem80387) (@lem80386)). Qed.
Lemma lem80393 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem80394 : term9 = term10.
Proof. exact (MK_COMB (@lem80393) (@lem80388)). Qed.
Lemma lem80404 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80363 n) (@lem80362 n)). Qed.
Lemma lem80405 : (NUMERAL 0) = 0.
Proof. exact (@lem80404 0). Qed.
Lemma lem80406 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem80407 (m : nat) : (term11 m) = (Nat.add m 0).
Proof. exact (MK_COMB (@lem80406 m) (@lem80405)). Qed.
Lemma lem80408 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80409 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem80408) (@lem80407 m)). Qed.
Lemma lem80410 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem80411 (m : nat) : ((term11 m) = m) = ((Nat.add m 0) = m).
Proof. exact (MK_COMB (@lem80409 m) (@lem80410 m)). Qed.
Lemma lem80414 : term14 = term15.
Proof. exact (fun_ext (fun m : nat => @lem80411 m)). Qed.
Lemma lem80415 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem80416 : term16 = term17.
Proof. exact (MK_COMB (@lem80415) (@lem80414)). Qed.
Lemma lem80421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem80422 : term18 = term19.
Proof. exact (MK_COMB (@lem80421) (@lem80416)). Qed.
Lemma lem80445 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem80446 : term21 = term22.
Proof. exact (MK_COMB (@lem80422) (@lem80445)). Qed.
Lemma lem80449 : term23 = term24.
Proof. exact (MK_COMB (@lem80394) (@lem80446)). Qed.
Lemma lem80452 : term24.
Proof. exact (EQ_MP (@lem80449) (@lem77629)). Qed.
Lemma lem80453 (n : nat) : term0 n.
Proof. exact (@lem75543 n). Qed.
Lemma lem80454 (n : nat) : (term0 n) = ((NUMERAL n) = n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem80456 : term22.
Proof. exact (proj2 (@lem80452)). Qed.
Lemma lem80457 : term20.
Proof. exact (proj2 (@lem80456)). Qed.
Lemma lem80465 : term25.
Proof. exact (proj1 (@lem80457)). Qed.
Lemma lem80466 (m : nat) : term26 m.
Proof. exact (@lem80465 m). Qed.
Lemma lem80467 (m : nat) : (term26 m) = (term27 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem80468 (m : nat) : term27 m.
Proof. exact (EQ_MP (@lem80467 m) (@lem80466 m)). Qed.
Lemma lem80469 (m : nat) (n : nat) : term28 m n.
Proof. exact (@lem80468 m n). Qed.
Lemma lem80470 (m : nat) (n : nat) : (term28 m n) = ((term29 m n) = (term30 m n)).
Proof. exact (eq_refl (term28 m n)). Qed.
Lemma lem80476 : term8.
Proof. exact (proj1 (@lem80452)). Qed.
Lemma lem80477 (n : nat) : term31 n.
Proof. exact (@lem80476 n). Qed.
Lemma lem80478 (n : nat) : (term31 n) = ((Nat.add 0 n) = n).
Proof. exact (eq_refl (term31 n)). Qed.
Lemma lem80480 (n : nat) : term32 n.
Proof. exact (@lem80122 n). Qed.
Lemma lem80481 (n : nat) : (term32 n) = ((BIT1 n) = (term33 n)).
Proof. exact (eq_refl (term32 n)). Qed.
Lemma lem80483 (n : nat) : term34 n.
Proof. exact (@lem80084 n). Qed.
Lemma lem80484 (n : nat) : (term34 n) = ((BIT0 n) = (Nat.add n n)).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem80489 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80454 n) (@lem80453 n)). Qed.
Lemma lem80490 : term35 = term36.
Proof. exact (@lem80489 term36). Qed.
Lemma lem80492 (n : nat) : (BIT0 n) = (Nat.add n n).
Proof. exact (EQ_MP (@lem80484 n) (@lem80483 n)). Qed.
Lemma lem80493 : term36 = term37.
Proof. exact (@lem80492 (BIT1 0)). Qed.
Lemma lem80494 : term35 = term37.
Proof. exact (TRANS (@lem80490) (@lem80493)). Qed.
Lemma lem80496 (n : nat) : (BIT1 n) = (term33 n).
Proof. exact (EQ_MP (@lem80481 n) (@lem80480 n)). Qed.
Lemma lem80497 : (BIT1 0) = term38.
Proof. exact (@lem80496 0). Qed.
Lemma lem80499 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem80478 n) (@lem80477 n)). Qed.
Lemma lem80500 : (Nat.add 0 0) = 0.
Proof. exact (@lem80499 0). Qed.
Lemma lem80501 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80502 : term38 = (S 0).
Proof. exact (MK_COMB (@lem80501) (@lem80500)). Qed.
Lemma lem80503 : (BIT1 0) = (S 0).
Proof. exact (TRANS (@lem80497) (@lem80502)). Qed.
Lemma lem80504 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem80505 : term39 = term40.
Proof. exact (MK_COMB (@lem80504) (@lem80503)). Qed.
Lemma lem80507 (n : nat) : (BIT1 n) = (term33 n).
Proof. exact (EQ_MP (@lem80481 n) (@lem80480 n)). Qed.
Lemma lem80508 : (BIT1 0) = term38.
Proof. exact (@lem80507 0). Qed.
Lemma lem80510 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem80478 n) (@lem80477 n)). Qed.
Lemma lem80511 : (Nat.add 0 0) = 0.
Proof. exact (@lem80510 0). Qed.
Lemma lem80512 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80513 : term38 = (S 0).
Proof. exact (MK_COMB (@lem80512) (@lem80511)). Qed.
Lemma lem80514 : (BIT1 0) = (S 0).
Proof. exact (TRANS (@lem80508) (@lem80513)). Qed.
Lemma lem80515 : term37 = term41.
Proof. exact (MK_COMB (@lem80505) (@lem80514)). Qed.
Lemma lem80517 (m : nat) (n : nat) : (term29 m n) = (term30 m n).
Proof. exact (EQ_MP (@lem80470 m n) (@lem80469 m n)). Qed.
Lemma lem80518 : term41 = term42.
Proof. exact (@lem80517 0 (S 0)). Qed.
Lemma lem80520 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem80478 n) (@lem80477 n)). Qed.
Lemma lem80521 : term43 = (S 0).
Proof. exact (@lem80520 (S 0)). Qed.
Lemma lem80522 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80523 : term42 = term44.
Proof. exact (MK_COMB (@lem80522) (@lem80521)). Qed.
Lemma lem80524 : term41 = term44.
Proof. exact (TRANS (@lem80518) (@lem80523)). Qed.
Lemma lem80525 : term37 = term44.
Proof. exact (TRANS (@lem80515) (@lem80524)). Qed.
Lemma lem80526 : term35 = term44.
Proof. exact (TRANS (@lem80494) (@lem80525)). Qed.
Lemma lem80527 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem80528 : term45 = term46.
Proof. exact (MK_COMB (@lem80527) (@lem80526)). Qed.
Lemma lem80530 (n : nat) : (NUMERAL n) = n.
Proof. exact (EQ_MP (@lem80454 n) (@lem80453 n)). Qed.
Lemma lem80531 : term47 = (BIT1 0).
Proof. exact (@lem80530 (BIT1 0)). Qed.
Lemma lem80533 (n : nat) : (BIT1 n) = (term33 n).
Proof. exact (EQ_MP (@lem80481 n) (@lem80480 n)). Qed.
Lemma lem80534 : (BIT1 0) = term38.
Proof. exact (@lem80533 0). Qed.
Lemma lem80535 : term47 = term38.
Proof. exact (TRANS (@lem80531) (@lem80534)). Qed.
Lemma lem80537 (n : nat) : (Nat.add 0 n) = n.
Proof. exact (EQ_MP (@lem80478 n) (@lem80477 n)). Qed.
Lemma lem80538 : (Nat.add 0 0) = 0.
Proof. exact (@lem80537 0). Qed.
Lemma lem80539 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80540 : term38 = (S 0).
Proof. exact (MK_COMB (@lem80539) (@lem80538)). Qed.
Lemma lem80541 : term47 = (S 0).
Proof. exact (TRANS (@lem80535) (@lem80540)). Qed.
Lemma lem80542 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem80543 : term48 = term44.
Proof. exact (MK_COMB (@lem80542) (@lem80541)). Qed.
Lemma lem80544 : (term35 = term48) = (term44 = term44).
Proof. exact (MK_COMB (@lem80528) (@lem80543)). Qed.
Lemma lem80546 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem80547 (x : nat) : (x = x) = True.
Proof. exact (@lem80546 nat x). Qed.
Lemma lem80548 : (term44 = term44) = True.
Proof. exact (@lem80547 term44). Qed.
Lemma lem80549 : (term35 = term48) = True.
Proof. exact (TRANS (@lem80544) (@lem80548)). Qed.
Lemma lem80550 : True = (term35 = term48).
Proof. exact (SYM (@lem80549)). Qed.
