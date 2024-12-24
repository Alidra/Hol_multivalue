Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_0_term_abbrevs.
Require Import LE_0_spec.
Require Import MULT_CLAUSES_spec.
Require Import NADD_OF_NUM_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1279540 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1279541 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1279542 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1279541 n) (@lem1279540 n)). Qed.
Lemma lem1279543 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1279575 : term2.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem1279576 (n : nat) : term3 n.
Proof. exact (@lem1279575 n). Qed.
Lemma lem1279577 (n : nat) : (term3 n) = ((term4 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term3 n)). Qed.
Lemma lem1279579 (k : nat) : term5 k.
Proof. exact (@lem1268972 k). Qed.
Lemma lem1279580 (k : nat) : (term5 k) = ((term6 k) = (term7 k)).
Proof. exact (eq_refl (term5 k)). Qed.
Lemma lem1279582 (x : nadd) : term8 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1279583 (x : nadd) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1279584 (x : nadd) : term9 x.
Proof. exact (EQ_MP (@lem1279583 x) (@lem1279582 x)). Qed.
Lemma lem1279585 (x : nadd) (y : nadd) : term10 x y.
Proof. exact (@lem1279584 x y). Qed.
Lemma lem1279586 (x : nadd) (y : nadd) : (term10 x y) = ((nadd_le x y) = (term11 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem1279589 (x : nadd) (y : nadd) : (nadd_le x y) = (term11 x y).
Proof. exact (EQ_MP (@lem1279586 x y) (@lem1279585 x y)). Qed.
Lemma lem1279590 (x : nadd) : (term12 x) = (term13 x).
Proof. exact (@lem1279589 term14 x). Qed.
Lemma lem1279600 (k : nat) : (term6 k) = (term7 k).
Proof. exact (EQ_MP (@lem1279580 k) (@lem1279579 k)). Qed.
Lemma lem1279601 : term15 = term16.
Proof. exact (@lem1279600 (NUMERAL 0)). Qed.
Lemma lem1279603 (n : nat) : (term4 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1279577 n) (@lem1279576 n)). Qed.
Lemma lem1279604 : term16 = term17.
Proof. exact (fun_ext (fun n : nat => @lem1279603 n)). Qed.
Lemma lem1279605 : term15 = term17.
Proof. exact (TRANS (@lem1279601) (@lem1279604)). Qed.
Lemma lem1279606 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1279607 (n : nat) : (term18 n) = (term19 n).
Proof. exact (MK_COMB (@lem1279605) (@lem1279606 n)). Qed.
Lemma lem1279609 {A B : Type'} (f : A -> B) (y : A) : (term20 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1279610 (f : nat -> nat) (y : nat) : (term21 f y) = (f y).
Proof. exact (@lem1279609 nat nat f y). Qed.
Lemma lem1279611 (n : nat) : (term22 n) = (term19 n).
Proof. exact (@lem1279610 term17 n). Qed.
Lemma lem1279612 (n : nat) : (term19 n) = (NUMERAL 0).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem1279613 : term23 = term17.
Proof. exact (fun_ext (fun n : nat => @lem1279612 n)). Qed.
Lemma lem1279614 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1279615 (n : nat) : (term22 n) = (term19 n).
Proof. exact (MK_COMB (@lem1279613) (@lem1279614 n)). Qed.
Lemma lem1279616 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1279617 (n : nat) : (term24 n) = (term25 n).
Proof. exact (MK_COMB (@lem1279616) (@lem1279615 n)). Qed.
Lemma lem1279618 (n : nat) : (term19 n) = (NUMERAL 0).
Proof. exact (eq_refl (term19 n)). Qed.
Lemma lem1279619 (n : nat) : ((term22 n) = (term19 n)) = ((term19 n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1279617 n) (@lem1279618 n)). Qed.
Lemma lem1279620 (n : nat) : (term19 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1279619 n) (@lem1279611 n)). Qed.
Lemma lem1279621 (n : nat) : (term18 n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1279607 n) (@lem1279620 n)). Qed.
Lemma lem1279622 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1279623 (n : nat) : (term26 n) = term27.
Proof. exact (MK_COMB (@lem1279622) (@lem1279621 n)). Qed.
Lemma lem1279624 (x : nadd) (n : nat) (B : nat) : (term28 x n B) = (term28 x n B).
Proof. exact (eq_refl (term28 x n B)). Qed.
Lemma lem1279625 (x : nadd) (n : nat) (B : nat) : (term29 x n B) = (term30 x n B).
Proof. exact (MK_COMB (@lem1279623 n) (@lem1279624 x n B)). Qed.
Lemma lem1279627 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1279543 n) (@lem1279542 n)). Qed.
Lemma lem1279628 (x : nadd) (n : nat) (B : nat) : (term30 x n B) = True.
Proof. exact (@lem1279627 (term28 x n B)). Qed.
Lemma lem1279629 (x : nadd) (n : nat) (B : nat) : (term29 x n B) = True.
Proof. exact (TRANS (@lem1279625 x n B) (@lem1279628 x n B)). Qed.
Lemma lem1279630 (x : nadd) (B : nat) : (term31 x B) = term32.
Proof. exact (fun_ext (fun n : nat => @lem1279629 x n B)). Qed.
Lemma lem1279631 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1279632 (x : nadd) (B : nat) : (term33 x B) = term34.
Proof. exact (MK_COMB (@lem1279631) (@lem1279630 x B)). Qed.
Lemma lem1279634 {A : Type'} (t : Prop) : (term35 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1279635 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1279634 nat t). Qed.
Lemma lem1279636 : term34 = True.
Proof. exact (@lem1279635 True). Qed.
Lemma lem1279637 (x : nadd) (B : nat) : (term33 x B) = True.
Proof. exact (TRANS (@lem1279632 x B) (@lem1279636)). Qed.
Lemma lem1279638 (x : nadd) : (term37 x) = term32.
Proof. exact (fun_ext (fun B : nat => @lem1279637 x B)). Qed.
Lemma lem1279639 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1279640 (x : nadd) : (term13 x) = term38.
Proof. exact (MK_COMB (@lem1279639) (@lem1279638 x)). Qed.
Lemma lem1279642 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1279643 (t : Prop) : (term40 t) = t.
Proof. exact (@lem1279642 nat t). Qed.
Lemma lem1279644 : term38 = True.
Proof. exact (@lem1279643 True). Qed.
Lemma lem1279645 (x : nadd) : (term13 x) = True.
Proof. exact (TRANS (@lem1279640 x) (@lem1279644)). Qed.
Lemma lem1279646 (x : nadd) : (term12 x) = True.
Proof. exact (TRANS (@lem1279590 x) (@lem1279645 x)). Qed.
Lemma lem1279647 (x : nadd) : True = (term12 x).
Proof. exact (SYM (@lem1279646 x)). Qed.
Lemma lem1279648 (x : nadd) : term12 x.
Proof. exact (EQ_MP (@lem1279647 x) (@lem0)). Qed.
Lemma lem1279653 : term41.
Proof. exact (fun x : nadd => @lem1279648 x). Qed.
