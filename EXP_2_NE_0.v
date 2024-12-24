Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXP_2_NE_0_term_abbrevs.
Require Import ARITH_EQ_spec.
Require Import EXP_EQ_0_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1844_spec.
Lemma lem523604 : term0.
Proof. exact (proj2 (@lem522076)). Qed.
Lemma lem523605 : term1.
Proof. exact (proj2 (@lem523604)). Qed.
Lemma lem523606 : term2.
Proof. exact (proj2 (@lem523605)). Qed.
Lemma lem523648 : term3.
Proof. exact (proj1 (@lem523606)). Qed.
Lemma lem523649 (n : nat) : term4 n.
Proof. exact (@lem523648 n). Qed.
Lemma lem523650 (n : nat) : (term4 n) = (((BIT1 n) = 0) = False).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem523652 : term5.
Proof. exact (proj1 (@lem523605)). Qed.
Lemma lem523653 (n : nat) : term6 n.
Proof. exact (@lem523652 n). Qed.
Lemma lem523654 (n : nat) : (term6 n) = (((BIT0 n) = 0) = (n = 0)).
Proof. exact (eq_refl (term6 n)). Qed.
Lemma lem523657 : term7.
Proof. exact (proj1 (@lem522076)). Qed.
Lemma lem523658 (m : nat) : term8 m.
Proof. exact (@lem523657 m). Qed.
Lemma lem523659 (m : nat) : (term8 m) = (term9 m).
Proof. exact (eq_refl (term8 m)). Qed.
Lemma lem523660 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem523659 m) (@lem523658 m)). Qed.
Lemma lem523661 (m : nat) (n : nat) : term10 m n.
Proof. exact (@lem523660 m n). Qed.
Lemma lem523662 (m : nat) (n : nat) : (term10 m n) = (((NUMERAL m) = (NUMERAL n)) = (m = n)).
Proof. exact (eq_refl (term10 m n)). Qed.
Lemma lem523664 (m : nat) : term11 m.
Proof. exact (@lem86997 m). Qed.
Lemma lem523665 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem523666 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem523665 m) (@lem523664 m)). Qed.
Lemma lem523667 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem523666 m n). Qed.
Lemma lem523668 (m : nat) (n : nat) : (term13 m n) = (((Nat.pow m n) = (NUMERAL 0)) = (term14 m n)).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem523675 (m : nat) (n : nat) : ((Nat.pow m n) = (NUMERAL 0)) = (term14 m n).
Proof. exact (EQ_MP (@lem523668 m n) (@lem523667 m n)). Qed.
Lemma lem523676 (n : nat) : ((term15 n) = (NUMERAL 0)) = (term16 n).
Proof. exact (@lem523675 term17 n). Qed.
Lemma lem523680 (m : nat) (n : nat) : ((NUMERAL m) = (NUMERAL n)) = (m = n).
Proof. exact (EQ_MP (@lem523662 m n) (@lem523661 m n)). Qed.
Lemma lem523681 : (term17 = (NUMERAL 0)) = (term18 = 0).
Proof. exact (@lem523680 term18 0). Qed.
Lemma lem523683 (n : nat) : ((BIT0 n) = 0) = (n = 0).
Proof. exact (EQ_MP (@lem523654 n) (@lem523653 n)). Qed.
Lemma lem523684 : (term18 = 0) = ((BIT1 0) = 0).
Proof. exact (@lem523683 (BIT1 0)). Qed.
Lemma lem523686 (n : nat) : ((BIT1 n) = 0) = False.
Proof. exact (EQ_MP (@lem523650 n) (@lem523649 n)). Qed.
Lemma lem523687 : ((BIT1 0) = 0) = False.
Proof. exact (@lem523686 0). Qed.
Lemma lem523688 : (term18 = 0) = False.
Proof. exact (TRANS (@lem523684) (@lem523687)). Qed.
Lemma lem523689 : (term17 = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem523681) (@lem523688)). Qed.
Lemma lem523690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem523691 : term19 = (and False).
Proof. exact (MK_COMB (@lem523690) (@lem523689)). Qed.
Lemma lem523694 (n : nat) : (term20 n) = (term20 n).
Proof. exact (eq_refl (term20 n)). Qed.
Lemma lem523695 (n : nat) : (term16 n) = (term21 n).
Proof. exact (MK_COMB (@lem523691) (@lem523694 n)). Qed.
Lemma lem523697 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem523698 (n : nat) : (term21 n) = False.
Proof. exact (@lem523697 (term20 n)). Qed.
Lemma lem523699 (n : nat) : (term16 n) = False.
Proof. exact (TRANS (@lem523695 n) (@lem523698 n)). Qed.
Lemma lem523700 (n : nat) : ((term15 n) = (NUMERAL 0)) = False.
Proof. exact (TRANS (@lem523676 n) (@lem523699 n)). Qed.
Lemma lem523701 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem523702 (n : nat) : (term22 n) = (~ False).
Proof. exact (MK_COMB (@lem523701) (@lem523700 n)). Qed.
Lemma lem523704 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem523705 (n : nat) : (term22 n) = True.
Proof. exact (TRANS (@lem523702 n) (@lem523704)). Qed.
Lemma lem523706 : term23 = term24.
Proof. exact (fun_ext (fun n : nat => @lem523705 n)). Qed.
Lemma lem523707 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem523708 : term25 = term26.
Proof. exact (MK_COMB (@lem523707) (@lem523706)). Qed.
Lemma lem523710 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem523711 (t : Prop) : (term28 t) = t.
Proof. exact (@lem523710 nat t). Qed.
Lemma lem523712 : term26 = True.
Proof. exact (@lem523711 True). Qed.
Lemma lem523713 : term25 = True.
Proof. exact (TRANS (@lem523708) (@lem523712)). Qed.
Lemma lem523714 : True = term25.
Proof. exact (SYM (@lem523713)). Qed.
Lemma lem523715 : term25.
Proof. exact (EQ_MP (@lem523714) (@lem0)). Qed.
