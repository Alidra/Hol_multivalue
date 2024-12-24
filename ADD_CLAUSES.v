Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ADD_CLAUSES_term_abbrevs.
Require Import ADD_0_spec.
Require Import ADD_SUC_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm77238_spec.
Lemma lem77457 (m : nat) : term0 m.
Proof. exact (@lem77456 m). Qed.
Lemma lem77458 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem77459 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem77458 m) (@lem77457 m)). Qed.
Lemma lem77460 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem77459 m n). Qed.
Lemma lem77461 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (term4 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem77463 (m : nat) : term5 m.
Proof. exact (@lem77332 m). Qed.
Lemma lem77464 (m : nat) : (term5 m) = ((term6 m) = m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem77466 : term7.
Proof. exact (proj2 (@lem77238)). Qed.
Lemma lem77467 (m : nat) : term8 m.
Proof. exact (@lem77466 m). Qed.
Lemma lem77468 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem77469 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem77468 m) (@lem77467 m)). Qed.
Lemma lem77470 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem77469 m n). Qed.
Lemma lem77471 (m : nat) (n : nat) : (term10 m n) = ((term11 m n) = (term4 m n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem77473 : term12.
Proof. exact (proj1 (@lem77238)). Qed.
Lemma lem77474 (n : nat) : term13 n.
Proof. exact (@lem77473 n). Qed.
Lemma lem77475 (n : nat) : (term13 n) = ((term14 n) = n).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem77486 (n : nat) : (term14 n) = n.
Proof. exact (EQ_MP (@lem77475 n) (@lem77474 n)). Qed.
Lemma lem77487 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77488 (n : nat) : (term15 n) = (@eq nat n).
Proof. exact (MK_COMB (@lem77487) (@lem77486 n)). Qed.
Lemma lem77489 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem77490 (n : nat) : ((term14 n) = n) = (n = n).
Proof. exact (MK_COMB (@lem77488 n) (@lem77489 n)). Qed.
Lemma lem77492 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77493 (x : nat) : (x = x) = True.
Proof. exact (@lem77492 nat x). Qed.
Lemma lem77494 (n : nat) : (n = n) = True.
Proof. exact (@lem77493 n). Qed.
Lemma lem77495 (n : nat) : ((term14 n) = n) = True.
Proof. exact (TRANS (@lem77490 n) (@lem77494 n)). Qed.
Lemma lem77496 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem77495 n)). Qed.
Lemma lem77497 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77498 : term12 = term18.
Proof. exact (MK_COMB (@lem77497) (@lem77496)). Qed.
Lemma lem77500 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77501 (t : Prop) : (term20 t) = t.
Proof. exact (@lem77500 nat t). Qed.
Lemma lem77502 : term18 = True.
Proof. exact (@lem77501 True). Qed.
Lemma lem77503 : term12 = True.
Proof. exact (TRANS (@lem77498) (@lem77502)). Qed.
Lemma lem77504 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77505 : term21 = (and True).
Proof. exact (MK_COMB (@lem77504) (@lem77503)). Qed.
Lemma lem77515 (m : nat) : (term6 m) = m.
Proof. exact (EQ_MP (@lem77464 m) (@lem77463 m)). Qed.
Lemma lem77516 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77517 (m : nat) : (term22 m) = (@eq nat m).
Proof. exact (MK_COMB (@lem77516) (@lem77515 m)). Qed.
Lemma lem77518 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem77519 (m : nat) : ((term6 m) = m) = (m = m).
Proof. exact (MK_COMB (@lem77517 m) (@lem77518 m)). Qed.
Lemma lem77521 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77522 (x : nat) : (x = x) = True.
Proof. exact (@lem77521 nat x). Qed.
Lemma lem77523 (m : nat) : (m = m) = True.
Proof. exact (@lem77522 m). Qed.
Lemma lem77524 (m : nat) : ((term6 m) = m) = True.
Proof. exact (TRANS (@lem77519 m) (@lem77523 m)). Qed.
Lemma lem77525 : term23 = term17.
Proof. exact (fun_ext (fun m : nat => @lem77524 m)). Qed.
Lemma lem77526 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77527 : term24 = term18.
Proof. exact (MK_COMB (@lem77526) (@lem77525)). Qed.
Lemma lem77529 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77530 (t : Prop) : (term20 t) = t.
Proof. exact (@lem77529 nat t). Qed.
Lemma lem77531 : term18 = True.
Proof. exact (@lem77530 True). Qed.
Lemma lem77532 : term24 = True.
Proof. exact (TRANS (@lem77527) (@lem77531)). Qed.
Lemma lem77533 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77534 : term25 = (and True).
Proof. exact (MK_COMB (@lem77533) (@lem77532)). Qed.
Lemma lem77548 (m : nat) (n : nat) : (term11 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem77471 m n) (@lem77470 m n)). Qed.
Lemma lem77549 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77550 (m : nat) (n : nat) : (term26 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem77549) (@lem77548 m n)). Qed.
Lemma lem77551 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem77552 (m : nat) (n : nat) : ((term11 m n) = (term4 m n)) = ((term4 m n) = (term4 m n)).
Proof. exact (MK_COMB (@lem77550 m n) (@lem77551 m n)). Qed.
Lemma lem77554 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77555 (x : nat) : (x = x) = True.
Proof. exact (@lem77554 nat x). Qed.
Lemma lem77556 (m : nat) (n : nat) : ((term4 m n) = (term4 m n)) = True.
Proof. exact (@lem77555 (term4 m n)). Qed.
Lemma lem77557 (m : nat) (n : nat) : ((term11 m n) = (term4 m n)) = True.
Proof. exact (TRANS (@lem77552 m n) (@lem77556 m n)). Qed.
Lemma lem77558 (m : nat) : (term28 m) = term17.
Proof. exact (fun_ext (fun n : nat => @lem77557 m n)). Qed.
Lemma lem77559 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77560 (m : nat) : (term9 m) = term18.
Proof. exact (MK_COMB (@lem77559) (@lem77558 m)). Qed.
Lemma lem77562 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77563 (t : Prop) : (term20 t) = t.
Proof. exact (@lem77562 nat t). Qed.
Lemma lem77564 : term18 = True.
Proof. exact (@lem77563 True). Qed.
Lemma lem77565 (m : nat) : (term9 m) = True.
Proof. exact (TRANS (@lem77560 m) (@lem77564)). Qed.
Lemma lem77566 : term29 = term17.
Proof. exact (fun_ext (fun m : nat => @lem77565 m)). Qed.
Lemma lem77567 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77568 : term7 = term18.
Proof. exact (MK_COMB (@lem77567) (@lem77566)). Qed.
Lemma lem77570 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77571 (t : Prop) : (term20 t) = t.
Proof. exact (@lem77570 nat t). Qed.
Lemma lem77572 : term18 = True.
Proof. exact (@lem77571 True). Qed.
Lemma lem77573 : term7 = True.
Proof. exact (TRANS (@lem77568) (@lem77572)). Qed.
Lemma lem77574 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem77575 : term30 = (and True).
Proof. exact (MK_COMB (@lem77574) (@lem77573)). Qed.
Lemma lem77587 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (EQ_MP (@lem77461 m n) (@lem77460 m n)). Qed.
Lemma lem77588 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem77589 (m : nat) (n : nat) : (term31 m n) = (term27 m n).
Proof. exact (MK_COMB (@lem77588) (@lem77587 m n)). Qed.
Lemma lem77590 (m : nat) (n : nat) : (term4 m n) = (term4 m n).
Proof. exact (eq_refl (term4 m n)). Qed.
Lemma lem77591 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = ((term4 m n) = (term4 m n)).
Proof. exact (MK_COMB (@lem77589 m n) (@lem77590 m n)). Qed.
Lemma lem77593 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem77594 (x : nat) : (x = x) = True.
Proof. exact (@lem77593 nat x). Qed.
Lemma lem77595 (m : nat) (n : nat) : ((term4 m n) = (term4 m n)) = True.
Proof. exact (@lem77594 (term4 m n)). Qed.
Lemma lem77596 (m : nat) (n : nat) : ((term3 m n) = (term4 m n)) = True.
Proof. exact (TRANS (@lem77591 m n) (@lem77595 m n)). Qed.
Lemma lem77597 (m : nat) : (term32 m) = term17.
Proof. exact (fun_ext (fun n : nat => @lem77596 m n)). Qed.
Lemma lem77598 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77599 (m : nat) : (term1 m) = term18.
Proof. exact (MK_COMB (@lem77598) (@lem77597 m)). Qed.
Lemma lem77601 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77602 (t : Prop) : (term20 t) = t.
Proof. exact (@lem77601 nat t). Qed.
Lemma lem77603 : term18 = True.
Proof. exact (@lem77602 True). Qed.
Lemma lem77604 (m : nat) : (term1 m) = True.
Proof. exact (TRANS (@lem77599 m) (@lem77603)). Qed.
Lemma lem77605 : term33 = term17.
Proof. exact (fun_ext (fun m : nat => @lem77604 m)). Qed.
Lemma lem77606 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem77607 : term34 = term18.
Proof. exact (MK_COMB (@lem77606) (@lem77605)). Qed.
Lemma lem77609 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem77610 (t : Prop) : (term20 t) = t.
Proof. exact (@lem77609 nat t). Qed.
Lemma lem77611 : term18 = True.
Proof. exact (@lem77610 True). Qed.
Lemma lem77612 : term34 = True.
Proof. exact (TRANS (@lem77607) (@lem77611)). Qed.
Lemma lem77613 : term35 = (True /\ True).
Proof. exact (MK_COMB (@lem77575) (@lem77612)). Qed.
Lemma lem77615 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem77616 : (True /\ True) = True.
Proof. exact (@lem77615 True). Qed.
Lemma lem77617 : term35 = True.
Proof. exact (TRANS (@lem77613) (@lem77616)). Qed.
Lemma lem77618 : term36 = (True /\ True).
Proof. exact (MK_COMB (@lem77534) (@lem77617)). Qed.
Lemma lem77620 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem77621 : (True /\ True) = True.
Proof. exact (@lem77620 True). Qed.
Lemma lem77622 : term36 = True.
Proof. exact (TRANS (@lem77618) (@lem77621)). Qed.
Lemma lem77623 : term37 = (True /\ True).
Proof. exact (MK_COMB (@lem77505) (@lem77622)). Qed.
Lemma lem77625 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem77626 : (True /\ True) = True.
Proof. exact (@lem77625 True). Qed.
Lemma lem77627 : term37 = True.
Proof. exact (TRANS (@lem77623) (@lem77626)). Qed.
Lemma lem77628 : True = term37.
Proof. exact (SYM (@lem77627)). Qed.
Lemma lem77629 : term37.
Proof. exact (EQ_MP (@lem77628) (@lem0)). Qed.
