Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import DIV_BY_DIV_term_abbrevs.
Require Import INT_DIV_BY_DIV_spec.
Require Import INT_OF_NUM_DIV_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import num_divides_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem3112552 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term0 m n) = (term1 m n).
Proof. exact (h1). Qed.
Lemma lem3112553 (m : nat) (n : nat) (h1 : (term0 m n) = (term1 m n)) : (term1 m n) = (term0 m n).
Proof. exact (SYM (@lem3112552 m n h1)). Qed.
Lemma lem3112554 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term1 m n) = (term0 m n).
Proof. exact (h1). Qed.
Lemma lem3112555 (m : nat) (n : nat) (h1 : (term1 m n) = (term0 m n)) : (term0 m n) = (term1 m n).
Proof. exact (SYM (@lem3112554 m n h1)). Qed.
Lemma lem3112556 (m : nat) (n : nat) : ((term0 m n) = (term1 m n)) = ((term1 m n) = (term0 m n)).
Proof. exact (prop_ext (fun h1 : (term0 m n) = (term1 m n) => @lem3112553 m n h1) (fun h1 : (term1 m n) = (term0 m n) => @lem3112555 m n h1)). Qed.
Lemma lem3112557 (m : nat) : (term2 m) = (term3 m).
Proof. exact (fun_ext (fun n : nat => @lem3112556 m n)). Qed.
Lemma lem3112558 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112559 (m : nat) : (term4 m) = (term5 m).
Proof. exact (MK_COMB (@lem3112558) (@lem3112557 m)). Qed.
Lemma lem3112560 : term6 = term7.
Proof. exact (fun_ext (fun m : nat => @lem3112559 m)). Qed.
Lemma lem3112561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112562 : term8 = term9.
Proof. exact (MK_COMB (@lem3112561) (@lem3112560)). Qed.
Lemma lem3112563 : term9.
Proof. exact (EQ_MP (@lem3112562) (@lem2538105)). Qed.
Lemma lem3112566 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (h1). Qed.
Lemma lem3112567 (m : nat) (n : nat) (h1 : ((int_of_num m) = (int_of_num n)) = (m = n)) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (SYM (@lem3112566 m n h1)). Qed.
Lemma lem3112568 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (h1). Qed.
Lemma lem3112569 (m : nat) (n : nat) (h1 : (m = n) = ((int_of_num m) = (int_of_num n))) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (SYM (@lem3112568 m n h1)). Qed.
Lemma lem3112570 (m : nat) (n : nat) : (((int_of_num m) = (int_of_num n)) = (m = n)) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (prop_ext (fun h1 : ((int_of_num m) = (int_of_num n)) = (m = n) => @lem3112567 m n h1) (fun h1 : (m = n) = ((int_of_num m) = (int_of_num n)) => @lem3112569 m n h1)). Qed.
Lemma lem3112571 (m : nat) : (term10 m) = (term11 m).
Proof. exact (fun_ext (fun n : nat => @lem3112570 m n)). Qed.
Lemma lem3112572 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112573 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem3112572) (@lem3112571 m)). Qed.
Lemma lem3112574 : term14 = term15.
Proof. exact (fun_ext (fun m : nat => @lem3112573 m)). Qed.
Lemma lem3112575 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112576 : term16 = term17.
Proof. exact (MK_COMB (@lem3112575) (@lem3112574)). Qed.
Lemma lem3112577 : term17.
Proof. exact (EQ_MP (@lem3112576) (@lem2307147)). Qed.
Lemma lem3112578 (m : int) : term18 m.
Proof. exact (@lem2732856 m). Qed.
Lemma lem3112579 (m : int) : (term18 m) = (term19 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem3112580 (m : int) : term19 m.
Proof. exact (EQ_MP (@lem3112579 m) (@lem3112578 m)). Qed.
Lemma lem3112581 (m : int) (n : int) : term20 m n.
Proof. exact (@lem3112580 m n). Qed.
Lemma lem3112582 (n : int) (m : int) : (term20 m n) = (term21 n m).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem3112583 (n : int) (m : int) : term21 n m.
Proof. exact (EQ_MP (@lem3112582 n m) (@lem3112581 m n)). Qed.
Lemma lem3112584 (n : int) (m : int) : (term21 n m) = ((term21 n m) = True).
Proof. exact (@lem7 (term21 n m)). Qed.
Lemma lem3112586 (a : nat) : term22 a.
Proof. exact (@lem2836659 a). Qed.
Lemma lem3112587 (a : nat) : (term22 a) = (term23 a).
Proof. exact (eq_refl (term22 a)). Qed.
Lemma lem3112588 (a : nat) : term23 a.
Proof. exact (EQ_MP (@lem3112587 a) (@lem3112586 a)). Qed.
Lemma lem3112589 (a : nat) (b : nat) : term24 a b.
Proof. exact (@lem3112588 a b). Qed.
Lemma lem3112590 (a : nat) (b : nat) : (term24 a b) = ((num_divides a b) = (term25 a b)).
Proof. exact (eq_refl (term24 a b)). Qed.
Lemma lem3112592 (m : nat) : term26 m.
Proof. exact (@lem3112563 m). Qed.
Lemma lem3112593 (m : nat) : (term26 m) = (term5 m).
Proof. exact (eq_refl (term26 m)). Qed.
Lemma lem3112594 (m : nat) : term5 m.
Proof. exact (EQ_MP (@lem3112593 m) (@lem3112592 m)). Qed.
Lemma lem3112595 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem3112594 m n). Qed.
Lemma lem3112596 (m : nat) (n : nat) : (term27 m n) = ((term1 m n) = (term0 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem3112598 (m : nat) : term28 m.
Proof. exact (@lem3112577 m). Qed.
Lemma lem3112599 (m : nat) : (term28 m) = (term13 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem3112600 (m : nat) : term13 m.
Proof. exact (EQ_MP (@lem3112599 m) (@lem3112598 m)). Qed.
Lemma lem3112601 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem3112600 m n). Qed.
Lemma lem3112602 (m : nat) (n : nat) : (term29 m n) = ((m = n) = ((int_of_num m) = (int_of_num n))).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem3112619 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem3112602 m n) (@lem3112601 m n)). Qed.
Lemma lem3112620 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term30).
Proof. exact (@lem3112619 n (NUMERAL 0)). Qed.
Lemma lem3112625 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3112626 (n : nat) : (term31 n) = (term32 n).
Proof. exact (MK_COMB (@lem3112625) (@lem3112620 n)). Qed.
Lemma lem3112627 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3112628 (n : nat) : (term33 n) = (term34 n).
Proof. exact (MK_COMB (@lem3112627) (@lem3112626 n)). Qed.
Lemma lem3112630 (a : nat) (b : nat) : (num_divides a b) = (term25 a b).
Proof. exact (EQ_MP (@lem3112590 a b) (@lem3112589 a b)). Qed.
Lemma lem3112631 (m : nat) (n : nat) : (num_divides m n) = (term25 m n).
Proof. exact (@lem3112630 m n). Qed.
Lemma lem3112632 (m : nat) (n : nat) : (term35 m n) = (term36 m n).
Proof. exact (MK_COMB (@lem3112628 n) (@lem3112631 m n)). Qed.
Lemma lem3112635 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3112636 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (MK_COMB (@lem3112635) (@lem3112632 m n)). Qed.
Lemma lem3112640 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem3112602 m n) (@lem3112601 m n)). Qed.
Lemma lem3112641 (n : nat) (m : nat) : ((term39 n m) = m) = ((term40 n m) = (int_of_num m)).
Proof. exact (@lem3112640 (term39 n m) m). Qed.
Lemma lem3112647 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (EQ_MP (@lem3112596 m n) (@lem3112595 m n)). Qed.
Lemma lem3112648 (n : nat) (m : nat) : (term40 n m) = (term41 n m).
Proof. exact (@lem3112647 n (Nat.div n m)). Qed.
Lemma lem3112650 (m : nat) (n : nat) : (term1 m n) = (term0 m n).
Proof. exact (EQ_MP (@lem3112596 m n) (@lem3112595 m n)). Qed.
Lemma lem3112651 (n : nat) (m : nat) : (term1 n m) = (term0 n m).
Proof. exact (@lem3112650 n m). Qed.
Lemma lem3112652 (n : nat) : (term42 n) = (term42 n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem3112653 (n : nat) (m : nat) : (term41 n m) = (term43 n m).
Proof. exact (MK_COMB (@lem3112652 n) (@lem3112651 n m)). Qed.
Lemma lem3112654 (n : nat) (m : nat) : (term40 n m) = (term43 n m).
Proof. exact (TRANS (@lem3112648 n m) (@lem3112653 n m)). Qed.
Lemma lem3112655 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem3112656 (n : nat) (m : nat) : (term44 n m) = (term45 n m).
Proof. exact (MK_COMB (@lem3112655) (@lem3112654 n m)). Qed.
Lemma lem3112657 (m : nat) : (int_of_num m) = (int_of_num m).
Proof. exact (eq_refl (int_of_num m)). Qed.
Lemma lem3112658 (n : nat) (m : nat) : ((term40 n m) = (int_of_num m)) = ((term43 n m) = (int_of_num m)).
Proof. exact (MK_COMB (@lem3112656 n m) (@lem3112657 m)). Qed.
Lemma lem3112663 (n : nat) (m : nat) : ((term39 n m) = m) = ((term43 n m) = (int_of_num m)).
Proof. exact (TRANS (@lem3112641 n m) (@lem3112658 n m)). Qed.
Lemma lem3112664 (n : nat) (m : nat) : (term46 n m) = (term47 n m).
Proof. exact (MK_COMB (@lem3112636 m n) (@lem3112663 n m)). Qed.
Lemma lem3112666 (n : int) (m : int) : (term21 n m) = True.
Proof. exact (EQ_MP (@lem3112584 n m) (@lem3112583 n m)). Qed.
Lemma lem3112667 (n : nat) (m : nat) : (term47 n m) = True.
Proof. exact (@lem3112666 (int_of_num n) (int_of_num m)). Qed.
Lemma lem3112668 (n : nat) (m : nat) : (term46 n m) = True.
Proof. exact (TRANS (@lem3112664 n m) (@lem3112667 n m)). Qed.
Lemma lem3112669 (m : nat) : (term48 m) = term49.
Proof. exact (fun_ext (fun n : nat => @lem3112668 n m)). Qed.
Lemma lem3112670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112671 (m : nat) : (term50 m) = term51.
Proof. exact (MK_COMB (@lem3112670) (@lem3112669 m)). Qed.
Lemma lem3112673 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112674 (t : Prop) : (term53 t) = t.
Proof. exact (@lem3112673 nat t). Qed.
Lemma lem3112675 : term51 = True.
Proof. exact (@lem3112674 True). Qed.
Lemma lem3112676 (m : nat) : (term50 m) = True.
Proof. exact (TRANS (@lem3112671 m) (@lem3112675)). Qed.
Lemma lem3112677 : term54 = term49.
Proof. exact (fun_ext (fun m : nat => @lem3112676 m)). Qed.
Lemma lem3112678 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3112679 : term55 = term51.
Proof. exact (MK_COMB (@lem3112678) (@lem3112677)). Qed.
Lemma lem3112681 {A : Type'} (t : Prop) : (term52 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3112682 (t : Prop) : (term53 t) = t.
Proof. exact (@lem3112681 nat t). Qed.
Lemma lem3112683 : term51 = True.
Proof. exact (@lem3112682 True). Qed.
Lemma lem3112684 : term55 = True.
Proof. exact (TRANS (@lem3112679) (@lem3112683)). Qed.
Lemma lem3112685 : True = term55.
Proof. exact (SYM (@lem3112684)). Qed.
Lemma lem3112686 : term55.
Proof. exact (EQ_MP (@lem3112685) (@lem0)). Qed.
