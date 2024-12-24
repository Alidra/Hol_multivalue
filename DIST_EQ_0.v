Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIST_EQ_0_term_abbrevs.
Require Import ADD_EQ_0_spec.
Require Import LE_ANTISYM_spec.
Require Import SUB_EQ_0_spec.
Require Import dist_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1245483 (m : nat) : term0 m.
Proof. exact (@lem92426 m). Qed.
Lemma lem1245484 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1245485 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1245484 m) (@lem1245483 m)). Qed.
Lemma lem1245486 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1245485 m n). Qed.
Lemma lem1245487 (m : nat) (n : nat) : (term2 m n) = ((term3 n m) = (m = n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1245489 (m : nat) : term4 m.
Proof. exact (@lem136259 m). Qed.
Lemma lem1245490 (m : nat) : (term4 m) = (term5 m).
Proof. exact (eq_refl (term4 m)). Qed.
Lemma lem1245491 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem1245490 m) (@lem1245489 m)). Qed.
Lemma lem1245492 (m : nat) (n : nat) : term6 m n.
Proof. exact (@lem1245491 m n). Qed.
Lemma lem1245493 (m : nat) (n : nat) : (term6 m n) = (((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n)).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1245495 (m : nat) : term7 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem1245496 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem1245497 (m : nat) : term8 m.
Proof. exact (EQ_MP (@lem1245496 m) (@lem1245495 m)). Qed.
Lemma lem1245498 (m : nat) (n : nat) : term9 m n.
Proof. exact (@lem1245497 m n). Qed.
Lemma lem1245499 (m : nat) (n : nat) : (term9 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term10 m n)).
Proof. exact (eq_refl (term9 m n)). Qed.
Lemma lem1245501 (n : nat) : term11 n.
Proof. exact (@lem1244710 n). Qed.
Lemma lem1245502 (n : nat) : (term11 n) = (term12 n).
Proof. exact (eq_refl (term11 n)). Qed.
Lemma lem1245503 (n : nat) : term12 n.
Proof. exact (EQ_MP (@lem1245502 n) (@lem1245501 n)). Qed.
Lemma lem1245504 (n : nat) (m : nat) : term13 n m.
Proof. exact (@lem1245503 n m). Qed.
Lemma lem1245505 (n : nat) (m : nat) : (term13 n m) = ((term14 m n) = (term15 n m)).
Proof. exact (eq_refl (term13 n m)). Qed.
Lemma lem1245520 (n : nat) (m : nat) : (term14 m n) = (term15 n m).
Proof. exact (EQ_MP (@lem1245505 n m) (@lem1245504 n m)). Qed.
Lemma lem1245521 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1245522 (n : nat) (m : nat) : (term16 m n) = (term17 n m).
Proof. exact (MK_COMB (@lem1245521) (@lem1245520 n m)). Qed.
Lemma lem1245523 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1245524 (n : nat) (m : nat) : ((term14 m n) = (NUMERAL 0)) = ((term15 n m) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1245522 n m) (@lem1245523)). Qed.
Lemma lem1245526 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term10 m n).
Proof. exact (EQ_MP (@lem1245499 m n) (@lem1245498 m n)). Qed.
Lemma lem1245527 (n : nat) (m : nat) : ((term15 n m) = (NUMERAL 0)) = (term18 n m).
Proof. exact (@lem1245526 (Nat.sub m n) (Nat.sub n m)). Qed.
Lemma lem1245531 (m : nat) (n : nat) : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1245493 m n) (@lem1245492 m n)). Qed.
Lemma lem1245532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1245533 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (MK_COMB (@lem1245532) (@lem1245531 m n)). Qed.
Lemma lem1245535 (m : nat) (n : nat) : ((Nat.sub m n) = (NUMERAL 0)) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1245493 m n) (@lem1245492 m n)). Qed.
Lemma lem1245536 (n : nat) (m : nat) : ((Nat.sub n m) = (NUMERAL 0)) = (Peano.le n m).
Proof. exact (@lem1245535 n m). Qed.
Lemma lem1245537 (n : nat) (m : nat) : (term18 n m) = (term3 n m).
Proof. exact (MK_COMB (@lem1245533 m n) (@lem1245536 n m)). Qed.
Lemma lem1245539 (m : nat) (n : nat) : (term3 n m) = (m = n).
Proof. exact (EQ_MP (@lem1245487 m n) (@lem1245486 m n)). Qed.
Lemma lem1245542 (m : nat) (n : nat) : (term18 n m) = (m = n).
Proof. exact (TRANS (@lem1245537 n m) (@lem1245539 m n)). Qed.
Lemma lem1245543 (m : nat) (n : nat) : ((term15 n m) = (NUMERAL 0)) = (m = n).
Proof. exact (TRANS (@lem1245527 n m) (@lem1245542 m n)). Qed.
Lemma lem1245544 (m : nat) (n : nat) : ((term14 m n) = (NUMERAL 0)) = (m = n).
Proof. exact (TRANS (@lem1245524 n m) (@lem1245543 m n)). Qed.
Lemma lem1245545 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1245546 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (MK_COMB (@lem1245545) (@lem1245544 m n)). Qed.
Lemma lem1245549 (m : nat) (n : nat) : (m = n) = (m = n).
Proof. exact (eq_refl (m = n)). Qed.
Lemma lem1245550 (m : nat) (n : nat) : (((term14 m n) = (NUMERAL 0)) = (m = n)) = ((m = n) = (m = n)).
Proof. exact (MK_COMB (@lem1245546 m n) (@lem1245549 m n)). Qed.
Lemma lem1245552 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1245553 (x : Prop) : (x = x) = True.
Proof. exact (@lem1245552 Prop x). Qed.
Lemma lem1245554 (m : nat) (n : nat) : ((m = n) = (m = n)) = True.
Proof. exact (@lem1245553 (m = n)). Qed.
Lemma lem1245555 (m : nat) (n : nat) : (((term14 m n) = (NUMERAL 0)) = (m = n)) = True.
Proof. exact (TRANS (@lem1245550 m n) (@lem1245554 m n)). Qed.
Lemma lem1245556 (m : nat) : (term23 m) = term24.
Proof. exact (fun_ext (fun n : nat => @lem1245555 m n)). Qed.
Lemma lem1245557 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245558 (m : nat) : (term25 m) = term26.
Proof. exact (MK_COMB (@lem1245557) (@lem1245556 m)). Qed.
Lemma lem1245560 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245561 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1245560 nat t). Qed.
Lemma lem1245562 : term26 = True.
Proof. exact (@lem1245561 True). Qed.
Lemma lem1245563 (m : nat) : (term25 m) = True.
Proof. exact (TRANS (@lem1245558 m) (@lem1245562)). Qed.
Lemma lem1245564 : term29 = term24.
Proof. exact (fun_ext (fun m : nat => @lem1245563 m)). Qed.
Lemma lem1245565 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1245566 : term30 = term26.
Proof. exact (MK_COMB (@lem1245565) (@lem1245564)). Qed.
Lemma lem1245568 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1245569 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1245568 nat t). Qed.
Lemma lem1245570 : term26 = True.
Proof. exact (@lem1245569 True). Qed.
Lemma lem1245571 : term30 = True.
Proof. exact (TRANS (@lem1245566) (@lem1245570)). Qed.
Lemma lem1245572 : True = term30.
Proof. exact (SYM (@lem1245571)). Qed.
Lemma lem1245573 : term30.
Proof. exact (EQ_MP (@lem1245572) (@lem0)). Qed.
