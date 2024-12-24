Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_LT_term_abbrevs.
Require Import ADD_CLAUSES_spec.
Require Import MOD_UNIQ_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem170528 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem170529 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem170528 h1 m). Qed.
Lemma lem170530 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem170531 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem170530 m) (@lem170529 m h1)). Qed.
Lemma lem170532 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem170531 m h1 n). Qed.
Lemma lem170533 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem170534 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem170533 m n) (@lem170532 m n h1)). Qed.
Lemma lem170535 (m : nat) (n : nat) (q : nat) (h1 : term0) : term5 m n q.
Proof. exact (@lem170534 m n h1 q). Qed.
Lemma lem170536 (q : nat) (m : nat) (n : nat) : (term5 m n q) = (term6 q m n).
Proof. exact (eq_refl (term5 m n q)). Qed.
Lemma lem170537 (q : nat) (m : nat) (n : nat) (h1 : term0) : term6 q m n.
Proof. exact (EQ_MP (@lem170536 q m n) (@lem170535 m n q h1)). Qed.
Lemma lem170538 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term7 q m n r.
Proof. exact (@lem170537 q m n h1 r). Qed.
Lemma lem170539 (q : nat) (m : nat) (n : nat) (r : nat) : (term7 q m n r) = (term8 q m n r).
Proof. exact (eq_refl (term7 q m n r)). Qed.
Lemma lem170540 (q : nat) (m : nat) (n : nat) (r : nat) (h1 : term0) : term8 q m n r.
Proof. exact (EQ_MP (@lem170539 q m n r) (@lem170538 q m n r h1)). Qed.
Lemma lem170541 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term9 m q r n.
Proof. exact (h1). Qed.
Lemma lem170542 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term9 m q r n) : (Nat.modulo m n) = r.
Proof. exact (@lem170540 q m n r h1 (@lem170541 m q r n h2)). Qed.
Lemma lem170543 (m : nat) (q : nat) (r : nat) (n : nat) (h1 : term9 m q r n) : term10 m n r.
Proof. exact (fun h0 : term0 => @lem170542 m q r n h0 h1). Qed.
Lemma lem170544 (m : nat) (r : nat) (n : nat) (h1 : term11 m r n) : term11 m r n.
Proof. exact (h1). Qed.
Lemma lem170545 (m : nat) (r : nat) (n : nat) (h1 : term11 m r n) : term10 m n r.
Proof. exact (ex_elim (@lem170544 m r n h1) (fun q : nat => fun h0 : term12 m r n q => @lem170543 m q r n h0)). Qed.
Lemma lem170546 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem170547 (m : nat) (r : nat) (n : nat) (h1 : term0) (h2 : term11 m r n) : (Nat.modulo m n) = r.
Proof. exact (@lem170545 m r n h2 (@lem170546 h1)). Qed.
Lemma lem170548 (m : nat) (n : nat) (r : nat) (h1 : term0) : term13 m n r.
Proof. exact (fun h0 : term11 m r n => @lem170547 m r n h1 h0). Qed.
Lemma lem170549 (m : nat) (n : nat) (h1 : term0) : term14 m n.
Proof. exact (fun r : nat => @lem170548 m n r h1). Qed.
Lemma lem170550 (m : nat) (h1 : term0) : term15 m.
Proof. exact (fun n : nat => @lem170549 m n h1). Qed.
Lemma lem170551 (h1 : term0) : term16.
Proof. exact (fun m : nat => @lem170550 m h1). Qed.
Lemma lem170552 : term17.
Proof. exact (fun h0 : term0 => @lem170551 h0). Qed.
Lemma lem170553 : term16.
Proof. exact (@lem170552 (@lem169705)). Qed.
Lemma lem170554 (m : nat) : term18 m.
Proof. exact (@lem170553 m). Qed.
Lemma lem170555 (m : nat) : (term18 m) = (term15 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem170556 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem170555 m) (@lem170554 m)). Qed.
Lemma lem170557 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem170556 m n). Qed.
Lemma lem170558 (m : nat) (n : nat) : (term19 m n) = (term14 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem170559 (m : nat) (n : nat) : term14 m n.
Proof. exact (EQ_MP (@lem170558 m n) (@lem170557 m n)). Qed.
Lemma lem170560 (m : nat) (n : nat) (r : nat) : term20 m n r.
Proof. exact (@lem170559 m n r). Qed.
Lemma lem170561 (m : nat) (n : nat) (r : nat) : (term20 m n r) = (term13 m n r).
Proof. exact (eq_refl (term20 m n r)). Qed.
Lemma lem170563 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem170565 (m : nat) (n : nat) (r : nat) : term13 m n r.
Proof. exact (EQ_MP (@lem170561 m n r) (@lem170560 m n r)). Qed.
Lemma lem170566 (n : nat) (m : nat) : term21 n m.
Proof. exact (@lem170565 m n m). Qed.
Lemma lem170587 : term22.
Proof. exact (proj1 (@lem77629)). Qed.
Lemma lem170588 (n : nat) : term23 n.
Proof. exact (@lem170587 n). Qed.
Lemma lem170589 (n : nat) : (term23 n) = ((term24 n) = n).
Proof. exact (eq_refl (term23 n)). Qed.
Lemma lem170621 : term25.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem170622 (n : nat) : term26 n.
Proof. exact (@lem170621 n). Qed.
Lemma lem170623 (n : nat) : (term26 n) = ((term27 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem170625 (m : nat) (n : nat) : (Peano.lt m n) = ((Peano.lt m n) = True).
Proof. exact (@lem7 (Peano.lt m n)). Qed.
Lemma lem170632 (n : nat) : (term27 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem170623 n) (@lem170622 n)). Qed.
Lemma lem170633 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem170634 (n : nat) : (term28 n) = term29.
Proof. exact (MK_COMB (@lem170633) (@lem170632 n)). Qed.
Lemma lem170635 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem170636 (n : nat) (m : nat) : (term30 n m) = (term24 m).
Proof. exact (MK_COMB (@lem170634 n) (@lem170635 m)). Qed.
Lemma lem170638 (n : nat) : (term24 n) = n.
Proof. exact (EQ_MP (@lem170589 n) (@lem170588 n)). Qed.
Lemma lem170639 (m : nat) : (term24 m) = m.
Proof. exact (@lem170638 m). Qed.
Lemma lem170640 (n : nat) (m : nat) : (term30 n m) = m.
Proof. exact (TRANS (@lem170636 n m) (@lem170639 m)). Qed.
Lemma lem170641 (m : nat) : (@eq nat m) = (@eq nat m).
Proof. exact (eq_refl (@eq nat m)). Qed.
Lemma lem170642 (n : nat) (m : nat) : (m = (term30 n m)) = (m = m).
Proof. exact (MK_COMB (@lem170641 m) (@lem170640 n m)). Qed.
Lemma lem170644 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem170645 (x : nat) : (x = x) = True.
Proof. exact (@lem170644 nat x). Qed.
Lemma lem170646 (m : nat) : (m = m) = True.
Proof. exact (@lem170645 m). Qed.
Lemma lem170647 (n : nat) (m : nat) : (m = (term30 n m)) = True.
Proof. exact (TRANS (@lem170642 n m) (@lem170646 m)). Qed.
Lemma lem170648 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170649 (n : nat) (m : nat) : (term31 n m) = (and True).
Proof. exact (MK_COMB (@lem170648) (@lem170647 n m)). Qed.
Lemma lem170651 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = True.
Proof. exact (EQ_MP (@lem170625 m n) (@lem170563 m n h1)). Qed.
Lemma lem170652 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term32 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem170649 n m) (@lem170651 m n h1)). Qed.
Lemma lem170654 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem170655 : (True /\ True) = True.
Proof. exact (@lem170654 True). Qed.
Lemma lem170656 (m : nat) (n : nat) (h1 : Peano.lt m n) : (term32 m n) = True.
Proof. exact (TRANS (@lem170652 m n h1) (@lem170655)). Qed.
Lemma lem170657 (m : nat) (n : nat) (h1 : Peano.lt m n) : True = (term32 m n).
Proof. exact (SYM (@lem170656 m n h1)). Qed.
Lemma lem170658 (m : nat) (n : nat) (h1 : Peano.lt m n) : term32 m n.
Proof. exact (EQ_MP (@lem170657 m n h1) (@lem0)). Qed.
Lemma lem170659 (m : nat) (n : nat) (h1 : Peano.lt m n) : term33 m n.
Proof. exact (ex_intro (term34 m n) (NUMERAL 0) (@lem170658 m n h1)). Qed.
Lemma lem170660 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (@lem170566 n m (@lem170659 m n h1)). Qed.
Lemma lem170661 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Peano.lt m n) = ((Nat.modulo m n) = m).
Proof. exact (prop_ext (fun h2 : Peano.lt m n => @lem170660 m n h1) (fun h2 : (Nat.modulo m n) = m => @lem170563 m n h1)). Qed.
Lemma lem170662 (m : nat) (n : nat) (h1 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (EQ_MP (@lem170661 m n h1) (@lem170563 m n h1)). Qed.
Lemma lem170663 (n : nat) (m : nat) : term35 n m.
Proof. exact (fun h0 : Peano.lt m n => @lem170662 m n h0). Qed.
Lemma lem170668 (m : nat) : term36 m.
Proof. exact (fun n : nat => @lem170663 n m). Qed.
Lemma lem170673 : term37.
Proof. exact (fun m : nat => @lem170668 m). Qed.
