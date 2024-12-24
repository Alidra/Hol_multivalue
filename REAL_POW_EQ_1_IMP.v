Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_EQ_1_IMP_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import REAL_ABS_NUM_spec.
Require Import REAL_POW_EQ_ABS_spec.
Require Import REAL_POW_ONE_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm82_spec.
Lemma lem1653545 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1653546 (n : nat) (h1 : term0) : term1 n.
Proof. exact (@lem1653545 h1 n). Qed.
Lemma lem1653547 (n : nat) : (term1 n) = (term2 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem1653548 (n : nat) (h1 : term0) : term2 n.
Proof. exact (EQ_MP (@lem1653547 n) (@lem1653546 n h1)). Qed.
Lemma lem1653549 (n : nat) (x : real) (h1 : term0) : term3 n x.
Proof. exact (@lem1653548 n h1 x). Qed.
Lemma lem1653550 (n : nat) (x : real) : (term3 n x) = (term4 n x).
Proof. exact (eq_refl (term3 n x)). Qed.
Lemma lem1653551 (n : nat) (x : real) (h1 : term0) : term4 n x.
Proof. exact (EQ_MP (@lem1653550 n x) (@lem1653549 n x h1)). Qed.
Lemma lem1653552 (n : nat) (x : real) (y : real) (h1 : term0) : term5 n x y.
Proof. exact (@lem1653551 n x h1 y). Qed.
Lemma lem1653553 (n : nat) (x : real) (y : real) : (term5 n x y) = (term6 n x y).
Proof. exact (eq_refl (term5 n x y)). Qed.
Lemma lem1653554 (n : nat) (x : real) (y : real) (h1 : term0) : term6 n x y.
Proof. exact (EQ_MP (@lem1653553 n x y) (@lem1653552 n x y h1)). Qed.
Lemma lem1653555 (x : real) (y : real) (n : nat) (h1 : term7 x y n) : term7 x y n.
Proof. exact (h1). Qed.
Lemma lem1653556 (x : real) (y : real) (n : nat) (h1 : term0) (h2 : term7 x y n) : (real_abs x) = (real_abs y).
Proof. exact (@lem1653554 n x y h1 (@lem1653555 x y n h2)). Qed.
Lemma lem1653557 (x : real) (y : real) (n : nat) (h1 : term7 x y n) : term8 x y.
Proof. exact (fun h0 : term0 => @lem1653556 x y n h0 h1). Qed.
Lemma lem1653558 (x : real) (y : real) (h1 : term9 x y) : term9 x y.
Proof. exact (h1). Qed.
Lemma lem1653559 (x : real) (y : real) (h1 : term9 x y) : term8 x y.
Proof. exact (ex_elim (@lem1653558 x y h1) (fun n : nat => fun h0 : term10 x y n => @lem1653557 x y n h0)). Qed.
Lemma lem1653560 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1653561 (x : real) (y : real) (h1 : term0) (h2 : term9 x y) : (real_abs x) = (real_abs y).
Proof. exact (@lem1653559 x y h2 (@lem1653560 h1)). Qed.
Lemma lem1653562 (x : real) (y : real) (h1 : term0) : term11 x y.
Proof. exact (fun h0 : term9 x y => @lem1653561 x y h1 h0). Qed.
Lemma lem1653563 (x : real) (h1 : term0) : term12 x.
Proof. exact (fun y : real => @lem1653562 x y h1). Qed.
Lemma lem1653564 (h1 : term0) : term13.
Proof. exact (fun x : real => @lem1653563 x h1). Qed.
Lemma lem1653565 : term14.
Proof. exact (fun h0 : term0 => @lem1653564 h0). Qed.
Lemma lem1653566 : term13.
Proof. exact (@lem1653565 (@lem1653544)). Qed.
Lemma lem1653567 (x : real) : term15 x.
Proof. exact (@lem1653566 x). Qed.
Lemma lem1653568 (x : real) : (term15 x) = (term12 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1653569 (x : real) : term12 x.
Proof. exact (EQ_MP (@lem1653568 x) (@lem1653567 x)). Qed.
Lemma lem1653570 (x : real) (y : real) : term16 x y.
Proof. exact (@lem1653569 x y). Qed.
Lemma lem1653571 (x : real) (y : real) : (term16 x y) = (term11 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1653574 (n : nat) (h1 : (term17 n) = (real_of_num n)) : (term17 n) = (real_of_num n).
Proof. exact (h1). Qed.
Lemma lem1653575 (n : nat) (h1 : (term17 n) = (real_of_num n)) : (real_of_num n) = (term17 n).
Proof. exact (SYM (@lem1653574 n h1)). Qed.
Lemma lem1653576 (n : nat) (h1 : (real_of_num n) = (term17 n)) : (real_of_num n) = (term17 n).
Proof. exact (h1). Qed.
Lemma lem1653577 (n : nat) (h1 : (real_of_num n) = (term17 n)) : (term17 n) = (real_of_num n).
Proof. exact (SYM (@lem1653576 n h1)). Qed.
Lemma lem1653578 (n : nat) : ((term17 n) = (real_of_num n)) = ((real_of_num n) = (term17 n)).
Proof. exact (prop_ext (fun h1 : (term17 n) = (real_of_num n) => @lem1653575 n h1) (fun h1 : (real_of_num n) = (term17 n) => @lem1653577 n h1)). Qed.
Lemma lem1653579 : term18 = term19.
Proof. exact (fun_ext (fun n : nat => @lem1653578 n)). Qed.
Lemma lem1653580 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1653581 : term20 = term21.
Proof. exact (MK_COMB (@lem1653580) (@lem1653579)). Qed.
Lemma lem1653582 : term21.
Proof. exact (EQ_MP (@lem1653581) (@lem1362923)). Qed.
Lemma lem1653583 (n : nat) : term22 n.
Proof. exact (@lem1653582 n). Qed.
Lemma lem1653584 (n : nat) : (term22 n) = ((real_of_num n) = (term17 n)).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem1653586 (x : real) (n : nat) (h1 : term23 x n) : term23 x n.
Proof. exact (h1). Qed.
Lemma lem1653587 (x : real) (n : nat) (h1 : (real_pow x n) = term24) : (real_pow x n) = term24.
Proof. exact (h1). Qed.
Lemma lem1653588 (n : nat) (h1 : term25 n) : term25 n.
Proof. exact (h1). Qed.
Lemma lem1653590 (n : nat) : (real_of_num n) = (term17 n).
Proof. exact (EQ_MP (@lem1653584 n) (@lem1653583 n)). Qed.
Lemma lem1653591 : term24 = term26.
Proof. exact (@lem1653590 term27). Qed.
Lemma lem1653592 (x : real) : (term28 x) = (term28 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1653593 (x : real) : ((real_abs x) = term24) = ((real_abs x) = term26).
Proof. exact (MK_COMB (@lem1653592 x) (@lem1653591)). Qed.
Lemma lem1653594 (x : real) : ((real_abs x) = term26) = ((real_abs x) = term24).
Proof. exact (SYM (@lem1653593 x)). Qed.
Lemma lem1653596 (x : real) (y : real) : term11 x y.
Proof. exact (EQ_MP (@lem1653571 x y) (@lem1653570 x y)). Qed.
Lemma lem1653597 (x : real) : term29 x.
Proof. exact (@lem1653596 x term24). Qed.
Lemma lem1653598 (n : nat) : term30 n.
Proof. exact (@lem1631092 n). Qed.
Lemma lem1653599 (n : nat) : (term30 n) = ((term31 n) = term24).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem1653601 (n : nat) : term32 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem1653617 (n : nat) (h1 : term25 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem1653601 n (@lem1653588 n h1)). Qed.
Lemma lem1653618 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1653619 (n : nat) (h1 : term25 n) : (term25 n) = (~ False).
Proof. exact (MK_COMB (@lem1653618) (@lem1653617 n h1)). Qed.
Lemma lem1653621 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1653622 (n : nat) (h1 : term25 n) : (term25 n) = True.
Proof. exact (TRANS (@lem1653619 n h1) (@lem1653621)). Qed.
Lemma lem1653623 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1653624 (n : nat) (h1 : term25 n) : (term33 n) = (and True).
Proof. exact (MK_COMB (@lem1653623) (@lem1653622 n h1)). Qed.
Lemma lem1653628 (x : real) (n : nat) (h1 : (real_pow x n) = term24) : (real_pow x n) = term24.
Proof. exact (h1). Qed.
Lemma lem1653629 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1653630 (x : real) (n : nat) (h1 : (real_pow x n) = term24) : (term34 x n) = term35.
Proof. exact (MK_COMB (@lem1653629) (@lem1653628 x n h1)). Qed.
Lemma lem1653632 (n : nat) : (term31 n) = term24.
Proof. exact (EQ_MP (@lem1653599 n) (@lem1653598 n)). Qed.
Lemma lem1653633 (x : real) (n : nat) (h1 : (real_pow x n) = term24) : ((real_pow x n) = (term31 n)) = (term24 = term24).
Proof. exact (MK_COMB (@lem1653630 x n h1) (@lem1653632 n)). Qed.
Lemma lem1653635 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1653636 (x : real) : (x = x) = True.
Proof. exact (@lem1653635 real x). Qed.
Lemma lem1653637 : (term24 = term24) = True.
Proof. exact (@lem1653636 term24). Qed.
Lemma lem1653638 (x : real) (n : nat) (h1 : (real_pow x n) = term24) : ((real_pow x n) = (term31 n)) = True.
Proof. exact (TRANS (@lem1653633 x n h1) (@lem1653637)). Qed.
Lemma lem1653639 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : (term36 x n) = (True /\ True).
Proof. exact (MK_COMB (@lem1653624 n h1) (@lem1653638 x n h2)). Qed.
Lemma lem1653641 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1653642 : (True /\ True) = True.
Proof. exact (@lem1653641 True). Qed.
Lemma lem1653643 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : (term36 x n) = True.
Proof. exact (TRANS (@lem1653639 x n h1 h2) (@lem1653642)). Qed.
Lemma lem1653644 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : True = (term36 x n).
Proof. exact (SYM (@lem1653643 x n h1 h2)). Qed.
Lemma lem1653645 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : term36 x n.
Proof. exact (EQ_MP (@lem1653644 x n h1 h2) (@lem0)). Qed.
Lemma lem1653646 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : term37 x.
Proof. exact (ex_intro (term38 x) n (@lem1653645 x n h1 h2)). Qed.
Lemma lem1653647 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : (real_abs x) = term26.
Proof. exact (@lem1653597 x (@lem1653646 x n h1 h2)). Qed.
Lemma lem1653648 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : (real_abs x) = term24.
Proof. exact (EQ_MP (@lem1653594 x) (@lem1653647 x n h1 h2)). Qed.
Lemma lem1653649 (x : real) (n : nat) (h1 : term23 x n) : (real_pow x n) = term24.
Proof. exact (proj2 (@lem1653586 x n h1)). Qed.
Lemma lem1653650 (x : real) (n : nat) (h1 : term23 x n) : term25 n.
Proof. exact (proj1 (@lem1653586 x n h1)). Qed.
Lemma lem1653651 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : ((real_pow x n) = term24) = ((real_abs x) = term24).
Proof. exact (prop_ext (fun h3 : (real_pow x n) = term24 => @lem1653648 x n h1 h2) (fun h3 : (real_abs x) = term24 => @lem1653587 x n h2)). Qed.
Lemma lem1653652 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : (real_abs x) = term24.
Proof. exact (EQ_MP (@lem1653651 x n h1 h2) (@lem1653587 x n h2)). Qed.
Lemma lem1653653 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : (term25 n) = ((real_abs x) = term24).
Proof. exact (prop_ext (fun h3 : term25 n => @lem1653652 x n h1 h2) (fun h3 : (real_abs x) = term24 => @lem1653588 n h1)). Qed.
Lemma lem1653654 (x : real) (n : nat) (h1 : term25 n) (h2 : (real_pow x n) = term24) : (real_abs x) = term24.
Proof. exact (EQ_MP (@lem1653653 x n h1 h2) (@lem1653588 n h1)). Qed.
Lemma lem1653655 (x : real) (n : nat) (h1 : term25 n) (h2 : term23 x n) : ((real_pow x n) = term24) = ((real_abs x) = term24).
Proof. exact (prop_ext (fun h3 : (real_pow x n) = term24 => @lem1653654 x n h1 h3) (fun h3 : (real_abs x) = term24 => @lem1653649 x n h2)). Qed.
Lemma lem1653656 (x : real) (n : nat) (h1 : term25 n) (h2 : term23 x n) : (real_abs x) = term24.
Proof. exact (EQ_MP (@lem1653655 x n h1 h2) (@lem1653649 x n h2)). Qed.
Lemma lem1653657 (x : real) (n : nat) (h1 : term23 x n) : (term25 n) = ((real_abs x) = term24).
Proof. exact (prop_ext (fun h2 : term25 n => @lem1653656 x n h2 h1) (fun h2 : (real_abs x) = term24 => @lem1653650 x n h1)). Qed.
Lemma lem1653658 (x : real) (n : nat) (h1 : term23 x n) : (real_abs x) = term24.
Proof. exact (EQ_MP (@lem1653657 x n h1) (@lem1653650 x n h1)). Qed.
Lemma lem1653659 (n : nat) (x : real) : term39 n x.
Proof. exact (fun h0 : term23 x n => @lem1653658 x n h0). Qed.
Lemma lem1653664 (x : real) : term40 x.
Proof. exact (fun n : nat => @lem1653659 n x). Qed.
Lemma lem1653669 : term41.
Proof. exact (fun x : real => @lem1653664 x). Qed.
