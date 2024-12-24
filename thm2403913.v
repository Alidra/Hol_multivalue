Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2403913_term_abbrevs.
Require Import ADD_EQ_0_spec.
Require Import INT_LE_LNEG_spec.
Require Import INT_LE_NEG2_spec.
Require Import INT_LE_RNEG_spec.
Require Import INT_OF_NUM_ADD_spec.
Require Import INT_OF_NUM_LE_spec.
Require Import LE_0_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1856_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm89498_spec.
Lemma lem2403623 (m : nat) : term0 m.
Proof. exact (@lem79432 m). Qed.
Lemma lem2403624 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem2403625 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem2403624 m) (@lem2403623 m)). Qed.
Lemma lem2403626 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem2403625 m n). Qed.
Lemma lem2403627 (m : nat) (n : nat) : (term2 m n) = (((Nat.add m n) = (NUMERAL 0)) = (term3 m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem2403636 : term4.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem2403637 (m : nat) : term5 m.
Proof. exact (@lem2403636 m). Qed.
Lemma lem2403638 (m : nat) : (term5 m) = ((term6 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem2403640 (n : nat) : term7 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem2403641 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem2403642 (n : nat) : term8 n.
Proof. exact (EQ_MP (@lem2403641 n) (@lem2403640 n)). Qed.
Lemma lem2403643 (n : nat) : (term8 n) = ((term8 n) = True).
Proof. exact (@lem7 (term8 n)). Qed.
Lemma lem2403645 (m : nat) : term9 m.
Proof. exact (@lem2307222 m). Qed.
Lemma lem2403646 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem2403647 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem2403646 m) (@lem2403645 m)). Qed.
Lemma lem2403648 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem2403647 m n). Qed.
Lemma lem2403649 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem2403651 (m : nat) : term13 m.
Proof. exact (@lem2306816 m). Qed.
Lemma lem2403652 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem2403653 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem2403652 m) (@lem2403651 m)). Qed.
Lemma lem2403654 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem2403653 m n). Qed.
Lemma lem2403655 (m : nat) (n : nat) : (term15 m n) = ((term16 m n) = (term17 m n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem2403657 (x : int) : term18 x.
Proof. exact (@lem2303280 x). Qed.
Lemma lem2403658 (x : int) : (term18 x) = (term19 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2403659 (x : int) : term19 x.
Proof. exact (EQ_MP (@lem2403658 x) (@lem2403657 x)). Qed.
Lemma lem2403660 (x : int) (y : int) : term20 x y.
Proof. exact (@lem2403659 x y). Qed.
Lemma lem2403661 (x : int) (y : int) : (term20 x y) = ((term21 x y) = (term22 x y)).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem2403663 (x : int) : term23 x.
Proof. exact (@lem2302610 x). Qed.
Lemma lem2403664 (x : int) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2403665 (x : int) : term24 x.
Proof. exact (EQ_MP (@lem2403664 x) (@lem2403663 x)). Qed.
Lemma lem2403666 (x : int) (y : int) : term25 x y.
Proof. exact (@lem2403665 x y). Qed.
Lemma lem2403667 (x : int) (y : int) : (term25 x y) = ((term26 x y) = (term27 x y)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2403669 (x : int) : term28 x.
Proof. exact (@lem2302944 x). Qed.
Lemma lem2403670 (x : int) : (term28 x) = (term29 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem2403671 (x : int) : term29 x.
Proof. exact (EQ_MP (@lem2403670 x) (@lem2403669 x)). Qed.
Lemma lem2403672 (x : int) (y : int) : term30 x y.
Proof. exact (@lem2403671 x y). Qed.
Lemma lem2403673 (y : int) (x : int) : (term30 x y) = ((term31 x y) = (int_le y x)).
Proof. exact (eq_refl (term30 x y)). Qed.
Lemma lem2403678 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem2403679 (m : nat) (n : nat) : ((term32 m n) = True) = (term32 m n).
Proof. exact (@lem2403678 (term32 m n)). Qed.
Lemma lem2403680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403681 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (MK_COMB (@lem2403680) (@lem2403679 m n)). Qed.
Lemma lem2403691 (y : int) (x : int) : (term31 x y) = (int_le y x).
Proof. exact (EQ_MP (@lem2403673 y x) (@lem2403672 x y)). Qed.
Lemma lem2403692 (n : nat) (m : nat) : (term35 m n) = (term12 n m).
Proof. exact (@lem2403691 (int_of_num n) (int_of_num m)). Qed.
Lemma lem2403693 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403694 (n : nat) (m : nat) : (term36 m n) = (term37 n m).
Proof. exact (MK_COMB (@lem2403693) (@lem2403692 n m)). Qed.
Lemma lem2403695 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem2403696 (n : nat) (m : nat) : ((term35 m n) = (Peano.le n m)) = ((term12 n m) = (Peano.le n m)).
Proof. exact (MK_COMB (@lem2403694 n m) (@lem2403695 n m)). Qed.
Lemma lem2403699 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403700 (n : nat) (m : nat) : (term38 n m) = (term39 n m).
Proof. exact (MK_COMB (@lem2403699) (@lem2403696 n m)). Qed.
Lemma lem2403709 (m : nat) (n : nat) : ((term40 m n) = (term3 m n)) = ((term40 m n) = (term3 m n)).
Proof. exact (eq_refl ((term40 m n) = (term3 m n))). Qed.
Lemma lem2403710 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (MK_COMB (@lem2403700 n m) (@lem2403709 m n)). Qed.
Lemma lem2403713 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem2403714 (m : nat) (n : nat) : (term43 m n) = (term44 m n).
Proof. exact (MK_COMB (@lem2403713 m n) (@lem2403710 m n)). Qed.
Lemma lem2403717 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (MK_COMB (@lem2403681 m n) (@lem2403714 m n)). Qed.
Lemma lem2403720 (m : nat) (n : nat) : (term46 m n) = (term45 m n).
Proof. exact (SYM (@lem2403717 m n)). Qed.
Lemma lem2403724 (x : int) (y : int) : (term26 x y) = (term27 x y).
Proof. exact (EQ_MP (@lem2403667 x y) (@lem2403666 x y)). Qed.
Lemma lem2403725 (m : nat) (n : nat) : (term32 m n) = (term47 m n).
Proof. exact (@lem2403724 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2403726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403727 (m : nat) (n : nat) : (term34 m n) = (term48 m n).
Proof. exact (MK_COMB (@lem2403726) (@lem2403725 m n)). Qed.
Lemma lem2403739 (x : int) (y : int) : (term21 x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2403661 x y) (@lem2403660 x y)). Qed.
Lemma lem2403740 (m : nat) (n : nat) : (term40 m n) = (term49 m n).
Proof. exact (@lem2403739 (int_of_num m) (int_of_num n)). Qed.
Lemma lem2403741 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403742 (m : nat) (n : nat) : (term50 m n) = (term51 m n).
Proof. exact (MK_COMB (@lem2403741) (@lem2403740 m n)). Qed.
Lemma lem2403749 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2403750 (m : nat) (n : nat) : ((term40 m n) = (term3 m n)) = ((term49 m n) = (term3 m n)).
Proof. exact (MK_COMB (@lem2403742 m n) (@lem2403749 m n)). Qed.
Lemma lem2403753 (n : nat) (m : nat) : (term39 n m) = (term39 n m).
Proof. exact (eq_refl (term39 n m)). Qed.
Lemma lem2403754 (m : nat) (n : nat) : (term42 m n) = (term52 m n).
Proof. exact (MK_COMB (@lem2403753 n m) (@lem2403750 m n)). Qed.
Lemma lem2403757 (m : nat) (n : nat) : (term39 m n) = (term39 m n).
Proof. exact (eq_refl (term39 m n)). Qed.
Lemma lem2403758 (m : nat) (n : nat) : (term44 m n) = (term53 m n).
Proof. exact (MK_COMB (@lem2403757 m n) (@lem2403754 m n)). Qed.
Lemma lem2403761 (m : nat) (n : nat) : (term46 m n) = (term54 m n).
Proof. exact (MK_COMB (@lem2403727 m n) (@lem2403758 m n)). Qed.
Lemma lem2403764 (m : nat) (n : nat) : (term54 m n) = (term46 m n).
Proof. exact (SYM (@lem2403761 m n)). Qed.
Lemma lem2403768 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2403655 m n) (@lem2403654 m n)). Qed.
Lemma lem2403769 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2403770 (m : nat) (n : nat) : (term47 m n) = (term56 m n).
Proof. exact (MK_COMB (@lem2403769) (@lem2403768 m n)). Qed.
Lemma lem2403772 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2403649 m n) (@lem2403648 m n)). Qed.
Lemma lem2403773 (m : nat) (n : nat) : (term56 m n) = (term57 m n).
Proof. exact (@lem2403772 (NUMERAL 0) (Nat.add m n)). Qed.
Lemma lem2403775 (n : nat) : (term8 n) = True.
Proof. exact (EQ_MP (@lem2403643 n) (@lem2403642 n)). Qed.
Lemma lem2403776 (m : nat) (n : nat) : (term57 m n) = True.
Proof. exact (@lem2403775 (Nat.add m n)). Qed.
Lemma lem2403777 (m : nat) (n : nat) : (term56 m n) = True.
Proof. exact (TRANS (@lem2403773 m n) (@lem2403776 m n)). Qed.
Lemma lem2403778 (m : nat) (n : nat) : (term47 m n) = True.
Proof. exact (TRANS (@lem2403770 m n) (@lem2403777 m n)). Qed.
Lemma lem2403779 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403780 (m : nat) (n : nat) : (term48 m n) = (and True).
Proof. exact (MK_COMB (@lem2403779) (@lem2403778 m n)). Qed.
Lemma lem2403786 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2403649 m n) (@lem2403648 m n)). Qed.
Lemma lem2403787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403788 (m : nat) (n : nat) : (term37 m n) = (term58 m n).
Proof. exact (MK_COMB (@lem2403787) (@lem2403786 m n)). Qed.
Lemma lem2403789 (m : nat) (n : nat) : (Peano.le m n) = (Peano.le m n).
Proof. exact (eq_refl (Peano.le m n)). Qed.
Lemma lem2403790 (m : nat) (n : nat) : ((term12 m n) = (Peano.le m n)) = ((Peano.le m n) = (Peano.le m n)).
Proof. exact (MK_COMB (@lem2403788 m n) (@lem2403789 m n)). Qed.
Lemma lem2403792 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2403793 (x : Prop) : (x = x) = True.
Proof. exact (@lem2403792 Prop x). Qed.
Lemma lem2403794 (m : nat) (n : nat) : ((Peano.le m n) = (Peano.le m n)) = True.
Proof. exact (@lem2403793 (Peano.le m n)). Qed.
Lemma lem2403795 (m : nat) (n : nat) : ((term12 m n) = (Peano.le m n)) = True.
Proof. exact (TRANS (@lem2403790 m n) (@lem2403794 m n)). Qed.
Lemma lem2403796 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403797 (m : nat) (n : nat) : (term39 m n) = (and True).
Proof. exact (MK_COMB (@lem2403796) (@lem2403795 m n)). Qed.
Lemma lem2403803 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2403649 m n) (@lem2403648 m n)). Qed.
Lemma lem2403804 (n : nat) (m : nat) : (term12 n m) = (Peano.le n m).
Proof. exact (@lem2403803 n m). Qed.
Lemma lem2403805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403806 (n : nat) (m : nat) : (term37 n m) = (term58 n m).
Proof. exact (MK_COMB (@lem2403805) (@lem2403804 n m)). Qed.
Lemma lem2403807 (n : nat) (m : nat) : (Peano.le n m) = (Peano.le n m).
Proof. exact (eq_refl (Peano.le n m)). Qed.
Lemma lem2403808 (n : nat) (m : nat) : ((term12 n m) = (Peano.le n m)) = ((Peano.le n m) = (Peano.le n m)).
Proof. exact (MK_COMB (@lem2403806 n m) (@lem2403807 n m)). Qed.
Lemma lem2403810 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2403811 (x : Prop) : (x = x) = True.
Proof. exact (@lem2403810 Prop x). Qed.
Lemma lem2403812 (n : nat) (m : nat) : ((Peano.le n m) = (Peano.le n m)) = True.
Proof. exact (@lem2403811 (Peano.le n m)). Qed.
Lemma lem2403813 (n : nat) (m : nat) : ((term12 n m) = (Peano.le n m)) = True.
Proof. exact (TRANS (@lem2403808 n m) (@lem2403812 n m)). Qed.
Lemma lem2403814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2403815 (n : nat) (m : nat) : (term39 n m) = (and True).
Proof. exact (MK_COMB (@lem2403814) (@lem2403813 n m)). Qed.
Lemma lem2403819 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (EQ_MP (@lem2403655 m n) (@lem2403654 m n)). Qed.
Lemma lem2403820 : int_le = int_le.
Proof. exact (eq_refl int_le). Qed.
Lemma lem2403821 (m : nat) (n : nat) : (term59 m n) = (term60 m n).
Proof. exact (MK_COMB (@lem2403820) (@lem2403819 m n)). Qed.
Lemma lem2403822 : term61 = term61.
Proof. exact (eq_refl term61). Qed.
Lemma lem2403823 (m : nat) (n : nat) : (term49 m n) = (term62 m n).
Proof. exact (MK_COMB (@lem2403821 m n) (@lem2403822)). Qed.
Lemma lem2403825 (m : nat) (n : nat) : (term12 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem2403649 m n) (@lem2403648 m n)). Qed.
Lemma lem2403826 (m : nat) (n : nat) : (term62 m n) = (term63 m n).
Proof. exact (@lem2403825 (Nat.add m n) (NUMERAL 0)). Qed.
Lemma lem2403827 (m : nat) (n : nat) : (term49 m n) = (term63 m n).
Proof. exact (TRANS (@lem2403823 m n) (@lem2403826 m n)). Qed.
Lemma lem2403828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403829 (m : nat) (n : nat) : (term51 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem2403828) (@lem2403827 m n)). Qed.
Lemma lem2403836 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2403837 (m : nat) (n : nat) : ((term49 m n) = (term3 m n)) = ((term63 m n) = (term3 m n)).
Proof. exact (MK_COMB (@lem2403829 m n) (@lem2403836 m n)). Qed.
Lemma lem2403840 (m : nat) (n : nat) : (term52 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem2403815 n m) (@lem2403837 m n)). Qed.
Lemma lem2403842 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2403843 (m : nat) (n : nat) : (term65 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (@lem2403842 ((term63 m n) = (term3 m n))). Qed.
Lemma lem2403852 (m : nat) (n : nat) : (term52 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (TRANS (@lem2403840 m n) (@lem2403843 m n)). Qed.
Lemma lem2403853 (m : nat) (n : nat) : (term53 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem2403797 m n) (@lem2403852 m n)). Qed.
Lemma lem2403855 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2403856 (m : nat) (n : nat) : (term65 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (@lem2403855 ((term63 m n) = (term3 m n))). Qed.
Lemma lem2403865 (m : nat) (n : nat) : (term53 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (TRANS (@lem2403853 m n) (@lem2403856 m n)). Qed.
Lemma lem2403866 (m : nat) (n : nat) : (term54 m n) = (term65 m n).
Proof. exact (MK_COMB (@lem2403780 m n) (@lem2403865 m n)). Qed.
Lemma lem2403868 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2403869 (m : nat) (n : nat) : (term65 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (@lem2403868 ((term63 m n) = (term3 m n))). Qed.
Lemma lem2403878 (m : nat) (n : nat) : (term54 m n) = ((term63 m n) = (term3 m n)).
Proof. exact (TRANS (@lem2403866 m n) (@lem2403869 m n)). Qed.
Lemma lem2403879 (m : nat) (n : nat) : ((term63 m n) = (term3 m n)) = (term54 m n).
Proof. exact (SYM (@lem2403878 m n)). Qed.
Lemma lem2403883 (m : nat) : (term6 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem2403638 m) (@lem2403637 m)). Qed.
Lemma lem2403884 (m : nat) (n : nat) : (term63 m n) = ((Nat.add m n) = (NUMERAL 0)).
Proof. exact (@lem2403883 (Nat.add m n)). Qed.
Lemma lem2403886 (m : nat) (n : nat) : ((Nat.add m n) = (NUMERAL 0)) = (term3 m n).
Proof. exact (EQ_MP (@lem2403627 m n) (@lem2403626 m n)). Qed.
Lemma lem2403889 (m : nat) (n : nat) : (term63 m n) = (term3 m n).
Proof. exact (TRANS (@lem2403884 m n) (@lem2403886 m n)). Qed.
Lemma lem2403894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2403895 (m : nat) (n : nat) : (term64 m n) = (term66 m n).
Proof. exact (MK_COMB (@lem2403894) (@lem2403889 m n)). Qed.
Lemma lem2403902 (m : nat) (n : nat) : (term3 m n) = (term3 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2403903 (m : nat) (n : nat) : ((term63 m n) = (term3 m n)) = ((term3 m n) = (term3 m n)).
Proof. exact (MK_COMB (@lem2403895 m n) (@lem2403902 m n)). Qed.
Lemma lem2403905 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2403906 (x : Prop) : (x = x) = True.
Proof. exact (@lem2403905 Prop x). Qed.
Lemma lem2403907 (m : nat) (n : nat) : ((term3 m n) = (term3 m n)) = True.
Proof. exact (@lem2403906 (term3 m n)). Qed.
Lemma lem2403908 (m : nat) (n : nat) : ((term63 m n) = (term3 m n)) = True.
Proof. exact (TRANS (@lem2403903 m n) (@lem2403907 m n)). Qed.
Lemma lem2403909 (m : nat) (n : nat) : True = ((term63 m n) = (term3 m n)).
Proof. exact (SYM (@lem2403908 m n)). Qed.
Lemma lem2403910 (m : nat) (n : nat) : (term63 m n) = (term3 m n).
Proof. exact (EQ_MP (@lem2403909 m n) (@lem0)). Qed.
Lemma lem2403911 (m : nat) (n : nat) : term54 m n.
Proof. exact (EQ_MP (@lem2403879 m n) (@lem2403910 m n)). Qed.
Lemma lem2403912 (m : nat) (n : nat) : term46 m n.
Proof. exact (EQ_MP (@lem2403764 m n) (@lem2403911 m n)). Qed.
Lemma lem2403913 (m : nat) (n : nat) : term45 m n.
Proof. exact (EQ_MP (@lem2403720 m n) (@lem2403912 m n)). Qed.
