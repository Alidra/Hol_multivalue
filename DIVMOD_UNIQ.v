Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIVMOD_UNIQ_term_abbrevs.
Require Import DIVISION_spec.
Require Import DIVMOD_UNIQ_LEMMA_spec.
Require Import LE_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Lemma lem169427 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (term0 m n) = (Peano.lt n m).
Proof. exact (h1). Qed.
Lemma lem169428 (n : nat) (m : nat) (h1 : (term0 m n) = (Peano.lt n m)) : (Peano.lt n m) = (term0 m n).
Proof. exact (SYM (@lem169427 n m h1)). Qed.
Lemma lem169429 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (Peano.lt n m) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem169430 (m : nat) (n : nat) (h1 : (Peano.lt n m) = (term0 m n)) : (term0 m n) = (Peano.lt n m).
Proof. exact (SYM (@lem169429 m n h1)). Qed.
Lemma lem169431 (m : nat) (n : nat) : ((term0 m n) = (Peano.lt n m)) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (Peano.lt n m) => @lem169428 n m h1) (fun h1 : (Peano.lt n m) = (term0 m n) => @lem169430 m n h1)). Qed.
Lemma lem169432 (m : nat) : (term1 m) = (term2 m).
Proof. exact (fun_ext (fun n : nat => @lem169431 m n)). Qed.
Lemma lem169433 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem169434 (m : nat) : (term3 m) = (term4 m).
Proof. exact (MK_COMB (@lem169433) (@lem169432 m)). Qed.
Lemma lem169435 : term5 = term6.
Proof. exact (fun_ext (fun m : nat => @lem169434 m)). Qed.
Lemma lem169436 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem169437 : term7 = term8.
Proof. exact (MK_COMB (@lem169436) (@lem169435)). Qed.
Lemma lem169438 : term8.
Proof. exact (EQ_MP (@lem169437) (@lem97961)). Qed.
Lemma lem169439 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem169440 (m : nat) (h1 : term9) : term10 m.
Proof. exact (@lem169439 h1 m). Qed.
Lemma lem169441 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem169442 (m : nat) (h1 : term9) : term11 m.
Proof. exact (EQ_MP (@lem169441 m) (@lem169440 m h1)). Qed.
Lemma lem169443 (m : nat) (n : nat) (h1 : term9) : term12 m n.
Proof. exact (@lem169442 m h1 n). Qed.
Lemma lem169444 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem169445 (m : nat) (n : nat) (h1 : term9) : term13 m n.
Proof. exact (EQ_MP (@lem169444 m n) (@lem169443 m n h1)). Qed.
Lemma lem169446 (n : nat) (h1 : term14 n) : term14 n.
Proof. exact (h1). Qed.
Lemma lem169447 (m : nat) (n : nat) (h1 : term9) (h2 : term14 n) : term15 m n.
Proof. exact (@lem169445 m n h1 (@lem169446 n h2)). Qed.
Lemma lem169448 (m : nat) (n : nat) (h1 : term14 n) : term16 m n.
Proof. exact (fun h0 : term9 => @lem169447 m n h0 h1). Qed.
Lemma lem169449 (h1 : term9) : term9.
Proof. exact (h1). Qed.
Lemma lem169450 (m : nat) (n : nat) (h1 : term9) (h2 : term14 n) : term15 m n.
Proof. exact (@lem169448 m n h2 (@lem169449 h1)). Qed.
Lemma lem169451 (m : nat) (n : nat) (h1 : term9) : term13 m n.
Proof. exact (fun h0 : term14 n => @lem169450 m n h1 h0). Qed.
Lemma lem169452 (m : nat) (h1 : term9) : term11 m.
Proof. exact (fun n : nat => @lem169451 m n h1). Qed.
Lemma lem169453 (h1 : term9) : term9.
Proof. exact (fun m : nat => @lem169452 m h1). Qed.
Lemma lem169454 : term17.
Proof. exact (fun h0 : term9 => @lem169453 h0). Qed.
Lemma lem169455 : term9.
Proof. exact (@lem169454 (@lem157261)). Qed.
Lemma lem169456 (m : nat) : term10 m.
Proof. exact (@lem169455 m). Qed.
Lemma lem169457 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem169458 (m : nat) : term11 m.
Proof. exact (EQ_MP (@lem169457 m) (@lem169456 m)). Qed.
Lemma lem169459 (m : nat) (n : nat) : term12 m n.
Proof. exact (@lem169458 m n). Qed.
Lemma lem169460 (m : nat) (n : nat) : (term12 m n) = (term13 m n).
Proof. exact (eq_refl (term12 m n)). Qed.
Lemma lem169462 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem169463 (m : nat) (h1 : term18) : term19 m.
Proof. exact (@lem169462 h1 m). Qed.
Lemma lem169464 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem169465 (m : nat) (h1 : term18) : term20 m.
Proof. exact (EQ_MP (@lem169464 m) (@lem169463 m h1)). Qed.
Lemma lem169466 (m : nat) (n : nat) (h1 : term18) : term21 m n.
Proof. exact (@lem169465 m h1 n). Qed.
Lemma lem169467 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem169468 (m : nat) (n : nat) (h1 : term18) : term22 m n.
Proof. exact (EQ_MP (@lem169467 m n) (@lem169466 m n h1)). Qed.
Lemma lem169469 (m : nat) (n : nat) (q1 : nat) (h1 : term18) : term23 m n q1.
Proof. exact (@lem169468 m n h1 q1). Qed.
Lemma lem169470 (m : nat) (n : nat) (q1 : nat) : (term23 m n q1) = (term24 m n q1).
Proof. exact (eq_refl (term23 m n q1)). Qed.
Lemma lem169471 (m : nat) (n : nat) (q1 : nat) (h1 : term18) : term24 m n q1.
Proof. exact (EQ_MP (@lem169470 m n q1) (@lem169469 m n q1 h1)). Qed.
Lemma lem169472 (m : nat) (n : nat) (q1 : nat) (r1 : nat) (h1 : term18) : term25 m n q1 r1.
Proof. exact (@lem169471 m n q1 h1 r1). Qed.
Lemma lem169473 (m : nat) (n : nat) (q1 : nat) (r1 : nat) : (term25 m n q1 r1) = (term26 m n q1 r1).
Proof. exact (eq_refl (term25 m n q1 r1)). Qed.
Lemma lem169474 (m : nat) (n : nat) (q1 : nat) (r1 : nat) (h1 : term18) : term26 m n q1 r1.
Proof. exact (EQ_MP (@lem169473 m n q1 r1) (@lem169472 m n q1 r1 h1)). Qed.
Lemma lem169475 (m : nat) (n : nat) (q1 : nat) (r1 : nat) (q2 : nat) (h1 : term18) : term27 m n q1 r1 q2.
Proof. exact (@lem169474 m n q1 r1 h1 q2). Qed.
Lemma lem169476 (m : nat) (n : nat) (q1 : nat) (q2 : nat) (r1 : nat) : (term27 m n q1 r1 q2) = (term28 m n q1 q2 r1).
Proof. exact (eq_refl (term27 m n q1 r1 q2)). Qed.
Lemma lem169477 (m : nat) (n : nat) (q1 : nat) (q2 : nat) (r1 : nat) (h1 : term18) : term28 m n q1 q2 r1.
Proof. exact (EQ_MP (@lem169476 m n q1 q2 r1) (@lem169475 m n q1 r1 q2 h1)). Qed.
Lemma lem169478 (m : nat) (n : nat) (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (h1 : term18) : term29 m n q1 q2 r1 r2.
Proof. exact (@lem169477 m n q1 q2 r1 h1 r2). Qed.
Lemma lem169479 (m : nat) (n : nat) (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) : (term29 m n q1 q2 r1 r2) = (term30 m n q1 q2 r1 r2).
Proof. exact (eq_refl (term29 m n q1 q2 r1 r2)). Qed.
Lemma lem169480 (m : nat) (n : nat) (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (h1 : term18) : term30 m n q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169479 m n q1 q2 r1 r2) (@lem169478 m n q1 q2 r1 r2 h1)). Qed.
Lemma lem169481 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term31 q1 r1 m q2 r2 n) : term31 q1 r1 m q2 r2 n.
Proof. exact (h1). Qed.
Lemma lem169482 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term18) (h2 : term31 q1 r1 m q2 r2 n) : term32 q1 q2 r1 r2.
Proof. exact (@lem169480 m n q1 q2 r1 r2 h1 (@lem169481 q1 r1 m q2 r2 n h2)). Qed.
Lemma lem169483 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (n : nat) (h1 : term31 q1 r1 m q2 r2 n) : term33 q1 q2 r1 r2.
Proof. exact (fun h0 : term18 => @lem169482 q1 r1 m q2 r2 n h0 h1). Qed.
Lemma lem169484 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (h1 : term34 q1 r1 m q2 r2) : term34 q1 r1 m q2 r2.
Proof. exact (h1). Qed.
Lemma lem169485 (q1 : nat) (r1 : nat) (m : nat) (q2 : nat) (r2 : nat) (h1 : term34 q1 r1 m q2 r2) : term33 q1 q2 r1 r2.
Proof. exact (ex_elim (@lem169484 q1 r1 m q2 r2 h1) (fun n : nat => fun h0 : term35 q1 r1 m q2 r2 n => @lem169483 q1 r1 m q2 r2 n h0)). Qed.
Lemma lem169486 (q1 : nat) (r1 : nat) (q2 : nat) (r2 : nat) (h1 : term36 q1 r1 q2 r2) : term36 q1 r1 q2 r2.
Proof. exact (h1). Qed.
Lemma lem169487 (q1 : nat) (r1 : nat) (q2 : nat) (r2 : nat) (h1 : term36 q1 r1 q2 r2) : term33 q1 q2 r1 r2.
Proof. exact (ex_elim (@lem169486 q1 r1 q2 r2 h1) (fun m : nat => fun h0 : term37 q1 r1 q2 r2 m => @lem169485 q1 r1 m q2 r2 h0)). Qed.
Lemma lem169488 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem169489 (q1 : nat) (r1 : nat) (q2 : nat) (r2 : nat) (h1 : term18) (h2 : term36 q1 r1 q2 r2) : term32 q1 q2 r1 r2.
Proof. exact (@lem169487 q1 r1 q2 r2 h2 (@lem169488 h1)). Qed.
Lemma lem169490 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) (h1 : term18) : term38 q1 q2 r1 r2.
Proof. exact (fun h0 : term36 q1 r1 q2 r2 => @lem169489 q1 r1 q2 r2 h1 h0). Qed.
Lemma lem169491 (q1 : nat) (q2 : nat) (r1 : nat) (h1 : term18) : term39 q1 q2 r1.
Proof. exact (fun r2 : nat => @lem169490 q1 q2 r1 r2 h1). Qed.
Lemma lem169492 (q1 : nat) (q2 : nat) (h1 : term18) : term40 q1 q2.
Proof. exact (fun r1 : nat => @lem169491 q1 q2 r1 h1). Qed.
Lemma lem169493 (q1 : nat) (h1 : term18) : term41 q1.
Proof. exact (fun q2 : nat => @lem169492 q1 q2 h1). Qed.
Lemma lem169494 (h1 : term18) : term42.
Proof. exact (fun q1 : nat => @lem169493 q1 h1). Qed.
Lemma lem169495 : term43.
Proof. exact (fun h0 : term18 => @lem169494 h0). Qed.
Lemma lem169496 : term42.
Proof. exact (@lem169495 (@lem169424)). Qed.
Lemma lem169497 (q1 : nat) : term44 q1.
Proof. exact (@lem169496 q1). Qed.
Lemma lem169498 (q1 : nat) : (term44 q1) = (term41 q1).
Proof. exact (eq_refl (term44 q1)). Qed.
Lemma lem169499 (q1 : nat) : term41 q1.
Proof. exact (EQ_MP (@lem169498 q1) (@lem169497 q1)). Qed.
Lemma lem169500 (q1 : nat) (q2 : nat) : term45 q1 q2.
Proof. exact (@lem169499 q1 q2). Qed.
Lemma lem169501 (q1 : nat) (q2 : nat) : (term45 q1 q2) = (term40 q1 q2).
Proof. exact (eq_refl (term45 q1 q2)). Qed.
Lemma lem169502 (q1 : nat) (q2 : nat) : term40 q1 q2.
Proof. exact (EQ_MP (@lem169501 q1 q2) (@lem169500 q1 q2)). Qed.
Lemma lem169503 (q1 : nat) (q2 : nat) (r1 : nat) : term46 q1 q2 r1.
Proof. exact (@lem169502 q1 q2 r1). Qed.
Lemma lem169504 (q1 : nat) (q2 : nat) (r1 : nat) : (term46 q1 q2 r1) = (term39 q1 q2 r1).
Proof. exact (eq_refl (term46 q1 q2 r1)). Qed.
Lemma lem169505 (q1 : nat) (q2 : nat) (r1 : nat) : term39 q1 q2 r1.
Proof. exact (EQ_MP (@lem169504 q1 q2 r1) (@lem169503 q1 q2 r1)). Qed.
Lemma lem169506 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) : term47 q1 q2 r1 r2.
Proof. exact (@lem169505 q1 q2 r1 r2). Qed.
Lemma lem169507 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) : (term47 q1 q2 r1 r2) = (term38 q1 q2 r1 r2).
Proof. exact (eq_refl (term47 q1 q2 r1 r2)). Qed.
Lemma lem169509 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term48 m q r n) : term48 m q r n.
Proof. exact (h1). Qed.
Lemma lem169511 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term49 q n r)) : m = (term49 q n r).
Proof. exact (h1). Qed.
Lemma lem169512 (m : nat) (q : nat) (n : nat) (r : nat) (h1 : m = (term49 q n r)) : (term49 q n r) = m.
Proof. exact (SYM (@lem169511 m q n r h1)). Qed.
Lemma lem169513 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : (term49 q n r) = m) : (term49 q n r) = m.
Proof. exact (h1). Qed.
Lemma lem169514 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : (term49 q n r) = m) : m = (term49 q n r).
Proof. exact (SYM (@lem169513 q n r m h1)). Qed.
Lemma lem169515 (q : nat) (n : nat) (r : nat) (m : nat) : (m = (term49 q n r)) = ((term49 q n r) = m).
Proof. exact (prop_ext (fun h1 : m = (term49 q n r) => @lem169512 m q n r h1) (fun h1 : (term49 q n r) = m => @lem169514 q n r m h1)). Qed.
Lemma lem169516 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem169517 (q : nat) (n : nat) (r : nat) (m : nat) : (term50 m q n r) = (term51 q n r m).
Proof. exact (MK_COMB (@lem169516) (@lem169515 q n r m)). Qed.
Lemma lem169519 (r : nat) (n : nat) : (Peano.lt r n) = (Peano.lt r n).
Proof. exact (eq_refl (Peano.lt r n)). Qed.
Lemma lem169520 (q : nat) (m : nat) (r : nat) (n : nat) : (term48 m q r n) = (term52 q m r n).
Proof. exact (MK_COMB (@lem169517 q n r m) (@lem169519 r n)). Qed.
Lemma lem169521 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term48 m q r n) : term52 q m r n.
Proof. exact (EQ_MP (@lem169520 q m r n) (@lem169509 m q r n h1)). Qed.
Lemma lem169522 (r : nat) (n : nat) (h1 : Peano.lt r n) : Peano.lt r n.
Proof. exact (h1). Qed.
Lemma lem169523 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : (term49 q n r) = m) : (term49 q n r) = m.
Proof. exact (h1). Qed.
Lemma lem169525 (q1 : nat) (q2 : nat) (r1 : nat) (r2 : nat) : term38 q1 q2 r1 r2.
Proof. exact (EQ_MP (@lem169507 q1 q2 r1 r2) (@lem169506 q1 q2 r1 r2)). Qed.
Lemma lem169526 (q : nat) (m : nat) (n : nat) (r : nat) : term53 q m n r.
Proof. exact (@lem169525 (Nat.div m n) q (Nat.modulo m n) r). Qed.
Lemma lem169527 (r : nat) (n : nat) : (Peano.lt r n) = ((Peano.lt r n) = True).
Proof. exact (@lem7 (Peano.lt r n)). Qed.
Lemma lem169540 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : (term49 q n r) = m) : (term49 q n r) = m.
Proof. exact (h1). Qed.
Lemma lem169541 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem169542 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : (term49 q n r) = m) : (m = (term49 q n r)) = (m = m).
Proof. exact (MK_COMB (@lem169541 m) (@lem169540 q n r m h1)). Qed.
Lemma lem169544 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem169545 (x : nat) : (x = x) = True.
Proof. exact (@lem169544 nat x). Qed.
Lemma lem169546 (m : nat) : (m = m) = True.
Proof. exact (@lem169545 m). Qed.
Lemma lem169547 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : (term49 q n r) = m) : (m = (term49 q n r)) = True.
Proof. exact (TRANS (@lem169542 q n r m h1) (@lem169546 m)). Qed.
Lemma lem169548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem169549 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : (term49 q n r) = m) : (term50 m q n r) = (and True).
Proof. exact (MK_COMB (@lem169548) (@lem169547 q n r m h1)). Qed.
Lemma lem169551 (r : nat) (n : nat) (h1 : Peano.lt r n) : (Peano.lt r n) = True.
Proof. exact (EQ_MP (@lem169527 r n) (@lem169522 r n h1)). Qed.
Lemma lem169552 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : (term48 m q r n) = (True /\ True).
Proof. exact (MK_COMB (@lem169549 q n r m h2) (@lem169551 r n h1)). Qed.
Lemma lem169554 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem169555 : (True /\ True) = True.
Proof. exact (@lem169554 True). Qed.
Lemma lem169556 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : (term48 m q r n) = True.
Proof. exact (TRANS (@lem169552 q n r m h1 h2) (@lem169555)). Qed.
Lemma lem169557 (m : nat) (n : nat) : (term54 m n) = (term54 m n).
Proof. exact (eq_refl (term54 m n)). Qed.
Lemma lem169558 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : (term55 m q r n) = (term56 m n).
Proof. exact (MK_COMB (@lem169557 m n) (@lem169556 q n r m h1 h2)). Qed.
Lemma lem169560 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem169561 (m : nat) (n : nat) : (term56 m n) = (term15 m n).
Proof. exact (@lem169560 (term15 m n)). Qed.
Lemma lem169566 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : (term55 m q r n) = (term15 m n).
Proof. exact (TRANS (@lem169558 q n r m h1 h2) (@lem169561 m n)). Qed.
Lemma lem169567 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : (term15 m n) = (term55 m q r n).
Proof. exact (SYM (@lem169566 q n r m h1 h2)). Qed.
Lemma lem169569 (m : nat) (n : nat) : term13 m n.
Proof. exact (EQ_MP (@lem169460 m n) (@lem169459 m n)). Qed.
Lemma lem169571 (n : nat) : term57 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem169572 (n : nat) : (term57 n) = (term58 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem169573 (n : nat) : term58 n.
Proof. exact (EQ_MP (@lem169572 n) (@lem169571 n)). Qed.
Lemma lem169574 (n : nat) : (term58 n) = ((term58 n) = True).
Proof. exact (@lem7 (term58 n)). Qed.
Lemma lem169576 (m : nat) : term59 m.
Proof. exact (@lem169438 m). Qed.
Lemma lem169577 (m : nat) : (term59 m) = (term4 m).
Proof. exact (eq_refl (term59 m)). Qed.
Lemma lem169578 (m : nat) : term4 m.
Proof. exact (EQ_MP (@lem169577 m) (@lem169576 m)). Qed.
Lemma lem169579 (m : nat) (n : nat) : term60 m n.
Proof. exact (@lem169578 m n). Qed.
Lemma lem169580 (m : nat) (n : nat) : (term60 m n) = ((Peano.lt n m) = (term0 m n)).
Proof. exact (eq_refl (term60 m n)). Qed.
Lemma lem169583 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem169584 (r : nat) (n : nat) : (term61 r n) = (term62 r n).
Proof. exact (@lem169583 (Peano.lt r n)). Qed.
Lemma lem169586 (m : nat) (n : nat) : (Peano.lt n m) = (term0 m n).
Proof. exact (EQ_MP (@lem169580 m n) (@lem169579 m n)). Qed.
Lemma lem169587 (n : nat) (r : nat) : (Peano.lt r n) = (term0 n r).
Proof. exact (@lem169586 n r). Qed.
Lemma lem169589 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem169590 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem169591 (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n) = term63.
Proof. exact (MK_COMB (@lem169590) (@lem169589 n h1)). Qed.
Lemma lem169592 (r : nat) : r = r.
Proof. exact (eq_refl r). Qed.
Lemma lem169593 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n r) = (term58 r).
Proof. exact (MK_COMB (@lem169591 n h1) (@lem169592 r)). Qed.
Lemma lem169595 (n : nat) : (term58 n) = True.
Proof. exact (EQ_MP (@lem169574 n) (@lem169573 n)). Qed.
Lemma lem169596 (r : nat) : (term58 r) = True.
Proof. exact (@lem169595 r). Qed.
Lemma lem169597 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.le n r) = True.
Proof. exact (TRANS (@lem169593 r n h1) (@lem169596 r)). Qed.
Lemma lem169598 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem169599 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term0 n r) = (~ True).
Proof. exact (MK_COMB (@lem169598) (@lem169597 r n h1)). Qed.
Lemma lem169601 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem169602 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term0 n r) = False.
Proof. exact (TRANS (@lem169599 r n h1) (@lem169601)). Qed.
Lemma lem169603 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Peano.lt r n) = False.
Proof. exact (TRANS (@lem169587 n r) (@lem169602 r n h1)). Qed.
Lemma lem169604 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem169605 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term62 r n) = (~ False).
Proof. exact (MK_COMB (@lem169604) (@lem169603 r n h1)). Qed.
Lemma lem169607 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem169608 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term62 r n) = True.
Proof. exact (TRANS (@lem169605 r n h1) (@lem169607)). Qed.
Lemma lem169609 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term61 r n) = True.
Proof. exact (TRANS (@lem169584 r n) (@lem169608 r n h1)). Qed.
Lemma lem169610 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term61 r n).
Proof. exact (SYM (@lem169609 r n h1)). Qed.
Lemma lem169611 (r : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term61 r n.
Proof. exact (EQ_MP (@lem169610 r n h1) (@lem0)). Qed.
Lemma lem169612 (r : nat) (n : nat) (h1 : Peano.lt r n) (h2 : n = (NUMERAL 0)) : False.
Proof. exact (@lem169611 r n h2 (@lem169522 r n h1)). Qed.
Lemma lem169613 (r : nat) (n : nat) (h1 : Peano.lt r n) : term64 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem169612 r n h1 h0). Qed.
Lemma lem169614 (n : nat) : (term64 n) = (term14 n).
Proof. exact (@lem69 (n = (NUMERAL 0))). Qed.
Lemma lem169615 (r : nat) (n : nat) (h1 : Peano.lt r n) : term14 n.
Proof. exact (EQ_MP (@lem169614 n) (@lem169613 r n h1)). Qed.
Lemma lem169616 (m : nat) (r : nat) (n : nat) (h1 : Peano.lt r n) : term15 m n.
Proof. exact (@lem169569 m n (@lem169615 r n h1)). Qed.
Lemma lem169617 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : term55 m q r n.
Proof. exact (EQ_MP (@lem169567 q n r m h1 h2) (@lem169616 m r n h1)). Qed.
Lemma lem169618 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : term65 n m q r.
Proof. exact (ex_intro (term66 n m q r) n (@lem169617 q n r m h1 h2)). Qed.
Lemma lem169619 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : term67 m n q r.
Proof. exact (ex_intro (term68 m n q r) m (@lem169618 q n r m h1 h2)). Qed.
Lemma lem169620 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : term69 q m n r.
Proof. exact (@lem169526 q m n r (@lem169619 q n r m h1 h2)). Qed.
Lemma lem169621 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term48 m q r n) : Peano.lt r n.
Proof. exact (proj2 (@lem169521 m q r n h1)). Qed.
Lemma lem169622 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term48 m q r n) : (term49 q n r) = m.
Proof. exact (proj1 (@lem169521 m q r n h1)). Qed.
Lemma lem169623 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : (Peano.lt r n) = (term69 q m n r).
Proof. exact (prop_ext (fun h3 : Peano.lt r n => @lem169620 q n r m h1 h2) (fun h3 : term69 q m n r => @lem169522 r n h1)). Qed.
Lemma lem169624 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : term69 q m n r.
Proof. exact (EQ_MP (@lem169623 q n r m h1 h2) (@lem169522 r n h1)). Qed.
Lemma lem169625 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : ((term49 q n r) = m) = (term69 q m n r).
Proof. exact (prop_ext (fun h3 : (term49 q n r) = m => @lem169624 q n r m h1 h2) (fun h3 : term69 q m n r => @lem169523 q n r m h2)). Qed.
Lemma lem169626 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : Peano.lt r n) (h2 : (term49 q n r) = m) : term69 q m n r.
Proof. exact (EQ_MP (@lem169625 q n r m h1 h2) (@lem169523 q n r m h2)). Qed.
Lemma lem169627 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : term48 m q r n) (h2 : (term49 q n r) = m) : (Peano.lt r n) = (term69 q m n r).
Proof. exact (prop_ext (fun h3 : Peano.lt r n => @lem169626 q n r m h3 h2) (fun h3 : term69 q m n r => @lem169621 m q r n h1)). Qed.
Lemma lem169628 (q : nat) (n : nat) (r : nat) (m : nat) (h1 : term48 m q r n) (h2 : (term49 q n r) = m) : term69 q m n r.
Proof. exact (EQ_MP (@lem169627 q n r m h1 h2) (@lem169621 m q r n h1)). Qed.
Lemma lem169629 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term48 m q r n) : ((term49 q n r) = m) = (term69 q m n r).
Proof. exact (prop_ext (fun h2 : (term49 q n r) = m => @lem169628 q n r m h1 h2) (fun h2 : term69 q m n r => @lem169622 m q r n h1)). Qed.
Lemma lem169630 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term48 m q r n) : term69 q m n r.
Proof. exact (EQ_MP (@lem169629 m q r n h1) (@lem169622 m q r n h1)). Qed.
Lemma lem169631 (q : nat) (m : nat) (n : nat) (r : nat) : term70 q m n r.
Proof. exact (fun h0 : term48 m q r n => @lem169630 m q r n h0). Qed.
Lemma lem169636 (q : nat) (m : nat) (n : nat) : term71 q m n.
Proof. exact (fun r : nat => @lem169631 q m n r). Qed.
Lemma lem169641 (m : nat) (n : nat) : term72 m n.
Proof. exact (fun q : nat => @lem169636 q m n). Qed.
Lemma lem169646 (m : nat) : term73 m.
Proof. exact (fun n : nat => @lem169641 m n). Qed.
Lemma lem169651 : term74.
Proof. exact (fun m : nat => @lem169646 m). Qed.
