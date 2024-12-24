Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import is_nadd_0_term_abbrevs.
Require Import DIST_REFL_spec.
Require Import LE_0_spec.
Require Import MULT_CLAUSES_spec.
Require Import is_nadd_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1262616 (n : nat) : term0 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem1262617 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem1262618 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem1262617 n) (@lem1262616 n)). Qed.
Lemma lem1262619 (n : nat) : (term1 n) = ((term1 n) = True).
Proof. exact (@lem7 (term1 n)). Qed.
Lemma lem1262621 (n : nat) : term2 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1262622 (n : nat) : (term2 n) = ((term3 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem1262624 : term4.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem1262650 : term5.
Proof. exact (proj1 (@lem1262624)). Qed.
Lemma lem1262651 (m : nat) : term6 m.
Proof. exact (@lem1262650 m). Qed.
Lemma lem1262652 (m : nat) : (term6 m) = ((term7 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem1262658 (x : nat -> nat) : term8 x.
Proof. exact (@lem1262615 x). Qed.
Lemma lem1262659 (x : nat -> nat) : (term8 x) = ((is_nadd x) = (term9 x)).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem1262662 (x : nat -> nat) : (is_nadd x) = (term9 x).
Proof. exact (EQ_MP (@lem1262659 x) (@lem1262658 x)). Qed.
Lemma lem1262663 : term10 = term11.
Proof. exact (@lem1262662 term12). Qed.
Lemma lem1262679 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1262680 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem1262679 nat nat f y). Qed.
Lemma lem1262681 (n : nat) : (term15 n) = (term16 n).
Proof. exact (@lem1262680 term12 n). Qed.
Lemma lem1262682 (n : nat) : (term16 n) = (NUMERAL 0).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem1262683 : term17 = term12.
Proof. exact (fun_ext (fun n : nat => @lem1262682 n)). Qed.
Lemma lem1262684 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1262685 (n : nat) : (term15 n) = (term16 n).
Proof. exact (MK_COMB (@lem1262683) (@lem1262684 n)). Qed.
Lemma lem1262686 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1262687 (n : nat) : (term18 n) = (term19 n).
Proof. exact (MK_COMB (@lem1262686) (@lem1262685 n)). Qed.
Lemma lem1262688 (n : nat) : (term16 n) = (NUMERAL 0).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem1262689 (n : nat) : ((term15 n) = (term16 n)) = ((term16 n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1262687 n) (@lem1262688 n)). Qed.
Lemma lem1262690 (n : nat) : (term16 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1262689 n) (@lem1262681 n)). Qed.
Lemma lem1262691 (m : nat) : (Nat.mul m) = (Nat.mul m).
Proof. exact (eq_refl (Nat.mul m)). Qed.
Lemma lem1262692 (n : nat) (m : nat) : (term20 m n) = (term7 m).
Proof. exact (MK_COMB (@lem1262691 m) (@lem1262690 n)). Qed.
Lemma lem1262694 (m : nat) : (term7 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1262652 m) (@lem1262651 m)). Qed.
Lemma lem1262695 (m : nat) (n : nat) : (term20 m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem1262692 n m) (@lem1262694 m)). Qed.
Lemma lem1262696 : (@pair nat nat) = (@pair nat nat).
Proof. exact (eq_refl (@pair nat nat)). Qed.
Lemma lem1262697 (m : nat) (n : nat) : (term21 m n) = term22.
Proof. exact (MK_COMB (@lem1262696) (@lem1262695 m n)). Qed.
Lemma lem1262699 {A B : Type'} (f : A -> B) (y : A) : (term13 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1262700 (f : nat -> nat) (y : nat) : (term14 f y) = (f y).
Proof. exact (@lem1262699 nat nat f y). Qed.
Lemma lem1262701 (m : nat) : (term15 m) = (term16 m).
Proof. exact (@lem1262700 term12 m). Qed.
Lemma lem1262702 (n : nat) : (term16 n) = (NUMERAL 0).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem1262703 : term17 = term12.
Proof. exact (fun_ext (fun n : nat => @lem1262702 n)). Qed.
Lemma lem1262704 (m : nat) : m = m.
Proof. exact (eq_refl m). Qed.
Lemma lem1262705 (m : nat) : (term15 m) = (term16 m).
Proof. exact (MK_COMB (@lem1262703) (@lem1262704 m)). Qed.
Lemma lem1262706 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1262707 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem1262706) (@lem1262705 m)). Qed.
Lemma lem1262708 (m : nat) : (term16 m) = (NUMERAL 0).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1262709 (m : nat) : ((term15 m) = (term16 m)) = ((term16 m) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1262707 m) (@lem1262708 m)). Qed.
Lemma lem1262710 (m : nat) : (term16 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1262709 m) (@lem1262701 m)). Qed.
Lemma lem1262711 (n : nat) : (Nat.mul n) = (Nat.mul n).
Proof. exact (eq_refl (Nat.mul n)). Qed.
Lemma lem1262712 (m : nat) (n : nat) : (term20 n m) = (term7 n).
Proof. exact (MK_COMB (@lem1262711 n) (@lem1262710 m)). Qed.
Lemma lem1262714 (m : nat) : (term7 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1262652 m) (@lem1262651 m)). Qed.
Lemma lem1262715 (n : nat) : (term7 n) = (NUMERAL 0).
Proof. exact (@lem1262714 n). Qed.
Lemma lem1262716 (n : nat) (m : nat) : (term20 n m) = (NUMERAL 0).
Proof. exact (TRANS (@lem1262712 m n) (@lem1262715 n)). Qed.
Lemma lem1262717 (n : nat) (m : nat) : (term23 n m) = term24.
Proof. exact (MK_COMB (@lem1262697 m n) (@lem1262716 n m)). Qed.
Lemma lem1262718 : dist = dist.
Proof. exact (eq_refl dist). Qed.
Lemma lem1262719 (n : nat) (m : nat) : (term25 n m) = term26.
Proof. exact (MK_COMB (@lem1262718) (@lem1262717 n m)). Qed.
Lemma lem1262721 (n : nat) : (term3 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1262622 n) (@lem1262621 n)). Qed.
Lemma lem1262722 : term26 = (NUMERAL 0).
Proof. exact (@lem1262721 (NUMERAL 0)). Qed.
Lemma lem1262723 (n : nat) (m : nat) : (term25 n m) = (NUMERAL 0).
Proof. exact (TRANS (@lem1262719 n m) (@lem1262722)). Qed.
Lemma lem1262724 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1262725 (n : nat) (m : nat) : (term27 n m) = term28.
Proof. exact (MK_COMB (@lem1262724) (@lem1262723 n m)). Qed.
Lemma lem1262726 (B : nat) (m : nat) (n : nat) : (term29 B m n) = (term29 B m n).
Proof. exact (eq_refl (term29 B m n)). Qed.
Lemma lem1262727 (B : nat) (m : nat) (n : nat) : (term30 B m n) = (term31 B m n).
Proof. exact (MK_COMB (@lem1262725 n m) (@lem1262726 B m n)). Qed.
Lemma lem1262729 (n : nat) : (term1 n) = True.
Proof. exact (EQ_MP (@lem1262619 n) (@lem1262618 n)). Qed.
Lemma lem1262730 (B : nat) (m : nat) (n : nat) : (term31 B m n) = True.
Proof. exact (@lem1262729 (term29 B m n)). Qed.
Lemma lem1262731 (B : nat) (m : nat) (n : nat) : (term30 B m n) = True.
Proof. exact (TRANS (@lem1262727 B m n) (@lem1262730 B m n)). Qed.
Lemma lem1262732 (B : nat) (m : nat) : (term32 B m) = term33.
Proof. exact (fun_ext (fun n : nat => @lem1262731 B m n)). Qed.
Lemma lem1262733 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1262734 (B : nat) (m : nat) : (term34 B m) = term35.
Proof. exact (MK_COMB (@lem1262733) (@lem1262732 B m)). Qed.
Lemma lem1262736 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1262737 (t : Prop) : (term37 t) = t.
Proof. exact (@lem1262736 nat t). Qed.
Lemma lem1262738 : term35 = True.
Proof. exact (@lem1262737 True). Qed.
Lemma lem1262739 (B : nat) (m : nat) : (term34 B m) = True.
Proof. exact (TRANS (@lem1262734 B m) (@lem1262738)). Qed.
Lemma lem1262740 (B : nat) : (term38 B) = term33.
Proof. exact (fun_ext (fun m : nat => @lem1262739 B m)). Qed.
Lemma lem1262741 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1262742 (B : nat) : (term39 B) = term35.
Proof. exact (MK_COMB (@lem1262741) (@lem1262740 B)). Qed.
Lemma lem1262744 {A : Type'} (t : Prop) : (term36 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1262745 (t : Prop) : (term37 t) = t.
Proof. exact (@lem1262744 nat t). Qed.
Lemma lem1262746 : term35 = True.
Proof. exact (@lem1262745 True). Qed.
Lemma lem1262747 (B : nat) : (term39 B) = True.
Proof. exact (TRANS (@lem1262742 B) (@lem1262746)). Qed.
Lemma lem1262748 : term40 = term33.
Proof. exact (fun_ext (fun B : nat => @lem1262747 B)). Qed.
Lemma lem1262749 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1262750 : term11 = term41.
Proof. exact (MK_COMB (@lem1262749) (@lem1262748)). Qed.
Lemma lem1262752 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1262753 (t : Prop) : (term43 t) = t.
Proof. exact (@lem1262752 nat t). Qed.
Lemma lem1262754 : term41 = True.
Proof. exact (@lem1262753 True). Qed.
Lemma lem1262755 : term11 = True.
Proof. exact (TRANS (@lem1262750) (@lem1262754)). Qed.
Lemma lem1262756 : term10 = True.
Proof. exact (TRANS (@lem1262663) (@lem1262755)). Qed.
Lemma lem1262757 : True = term10.
Proof. exact (SYM (@lem1262756)). Qed.
Lemma lem1262758 : term10.
Proof. exact (EQ_MP (@lem1262757) (@lem0)). Qed.
