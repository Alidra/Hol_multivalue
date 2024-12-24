Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_TRANS_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import nadd_le_spec.
Require Import thm0_spec.
Require Import thm272809_spec.
Require Import thm7_spec.
Lemma lem1270629 (x : nadd) : term0 x.
Proof. exact (@lem1269692 x). Qed.
Lemma lem1270630 (x : nadd) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1270631 (x : nadd) : term1 x.
Proof. exact (EQ_MP (@lem1270630 x) (@lem1270629 x)). Qed.
Lemma lem1270632 (x : nadd) (y : nadd) : term2 x y.
Proof. exact (@lem1270631 x y). Qed.
Lemma lem1270633 (x : nadd) (y : nadd) : (term2 x y) = ((nadd_le x y) = (term3 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1270640 (x : nadd) (y : nadd) : (nadd_le x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1270633 x y) (@lem1270632 x y)). Qed.
Lemma lem1270649 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1270650 (x : nadd) (y : nadd) : (term4 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1270649) (@lem1270640 x y)). Qed.
Lemma lem1270652 (x : nadd) (y : nadd) : (nadd_le x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1270633 x y) (@lem1270632 x y)). Qed.
Lemma lem1270653 (y : nadd) (z : nadd) : (nadd_le y z) = (term3 y z).
Proof. exact (@lem1270652 y z). Qed.
Lemma lem1270662 (x : nadd) (y : nadd) (z : nadd) : (term6 x y z) = (term7 x y z).
Proof. exact (MK_COMB (@lem1270650 x y) (@lem1270653 y z)). Qed.
Lemma lem1270665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1270666 (x : nadd) (y : nadd) (z : nadd) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1270665) (@lem1270662 x y z)). Qed.
Lemma lem1270668 (x : nadd) (y : nadd) : (nadd_le x y) = (term3 x y).
Proof. exact (EQ_MP (@lem1270633 x y) (@lem1270632 x y)). Qed.
Lemma lem1270669 (x : nadd) (z : nadd) : (nadd_le x z) = (term3 x z).
Proof. exact (@lem1270668 x z). Qed.
Lemma lem1270678 (y : nadd) (x : nadd) (z : nadd) : (term10 y x z) = (term11 y x z).
Proof. exact (MK_COMB (@lem1270666 x y z) (@lem1270669 x z)). Qed.
Lemma lem1270681 (y : nadd) (x : nadd) (z : nadd) : (term11 y x z) = (term10 y x z).
Proof. exact (SYM (@lem1270678 y x z)). Qed.
Lemma lem1270682 (x : nadd) (y : nadd) (z : nadd) (h1 : term7 x y z) : term7 x y z.
Proof. exact (h1). Qed.
Lemma lem1270683 (y : nadd) (z : nadd) (h1 : term3 y z) : term3 y z.
Proof. exact (h1). Qed.
Lemma lem1270684 (x : nadd) (y : nadd) (h1 : term3 x y) : term3 x y.
Proof. exact (h1). Qed.
Lemma lem1270685 (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term12 x y B1.
Proof. exact (h1). Qed.
Lemma lem1270686 (y : nadd) (z : nadd) (h1 : term3 y z) : term3 y z.
Proof. exact (h1). Qed.
Lemma lem1270687 (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : term12 y z B2.
Proof. exact (h1). Qed.
Lemma lem1270745 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term13 x y B1 n.
Proof. exact (@lem1270685 x y B1 h1 n). Qed.
Lemma lem1270746 (x : nadd) (y : nadd) (n : nat) (B1 : nat) : (term13 x y B1 n) = (term14 x y n B1).
Proof. exact (eq_refl (term13 x y B1 n)). Qed.
Lemma lem1270747 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term14 x y n B1.
Proof. exact (EQ_MP (@lem1270746 x y n B1) (@lem1270745 n x y B1 h1)). Qed.
Lemma lem1270748 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem1270749 (m : nat) (h1 : term15) : term16 m.
Proof. exact (@lem1270748 h1 m). Qed.
Lemma lem1270750 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1270751 (m : nat) (h1 : term15) : term17 m.
Proof. exact (EQ_MP (@lem1270750 m) (@lem1270749 m h1)). Qed.
Lemma lem1270752 (m : nat) (n : nat) (h1 : term15) : term18 m n.
Proof. exact (@lem1270751 m h1 n). Qed.
Lemma lem1270753 (n : nat) (m : nat) : (term18 m n) = (term19 n m).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1270754 (n : nat) (m : nat) (h1 : term15) : term19 n m.
Proof. exact (EQ_MP (@lem1270753 n m) (@lem1270752 m n h1)). Qed.
Lemma lem1270755 (n : nat) (m : nat) (p : nat) (h1 : term15) : term20 n m p.
Proof. exact (@lem1270754 n m h1 p). Qed.
Lemma lem1270756 (n : nat) (m : nat) (p : nat) : (term20 n m p) = (term21 n m p).
Proof. exact (eq_refl (term20 n m p)). Qed.
Lemma lem1270757 (n : nat) (m : nat) (p : nat) (h1 : term15) : term21 n m p.
Proof. exact (EQ_MP (@lem1270756 n m p) (@lem1270755 n m p h1)). Qed.
Lemma lem1270758 (m : nat) (n : nat) (h1 : Peano.le m n) : Peano.le m n.
Proof. exact (h1). Qed.
Lemma lem1270759 (p : nat) (m : nat) (n : nat) (h1 : term15) (h2 : Peano.le m n) : term22 n m p.
Proof. exact (@lem1270757 n m p h1 (@lem1270758 m n h2)). Qed.
Lemma lem1270760 (m : nat) (n : nat) (h1 : term15) (h2 : Peano.le m n) : term23 n m.
Proof. exact (fun p : nat => @lem1270759 p m n h1 h2). Qed.
Lemma lem1270761 (n : nat) (m : nat) (h1 : term15) : term24 n m.
Proof. exact (fun h0 : Peano.le m n => @lem1270760 m n h1 h0). Qed.
Lemma lem1270762 (m : nat) (h1 : term15) : term25 m.
Proof. exact (fun n : nat => @lem1270761 n m h1). Qed.
Lemma lem1270763 (h1 : term15) : term26.
Proof. exact (fun m : nat => @lem1270762 m h1). Qed.
Lemma lem1270764 : term27.
Proof. exact (fun h0 : term15 => @lem1270763 h0). Qed.
Lemma lem1270765 : term26.
Proof. exact (@lem1270764 (@lem272809)). Qed.
Lemma lem1270766 (m : nat) : term28 m.
Proof. exact (@lem1270765 m). Qed.
Lemma lem1270767 (m : nat) : (term28 m) = (term25 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1270768 (m : nat) : term25 m.
Proof. exact (EQ_MP (@lem1270767 m) (@lem1270766 m)). Qed.
Lemma lem1270769 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem1270768 m n). Qed.
Lemma lem1270770 (n : nat) (m : nat) : (term29 m n) = (term24 n m).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem1270773 (n : nat) (m : nat) : term24 n m.
Proof. exact (EQ_MP (@lem1270770 n m) (@lem1270769 m n)). Qed.
Lemma lem1270774 (y : nadd) (B1 : nat) (x : nadd) (n : nat) : term30 y B1 x n.
Proof. exact (@lem1270773 (term31 y n B1) (dest_nadd x n)). Qed.
Lemma lem1270775 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term32 y B1 x n.
Proof. exact (@lem1270774 y B1 x n (@lem1270747 n x y B1 h1)). Qed.
Lemma lem1270776 (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term33 y B1 x.
Proof. exact (fun n : nat => @lem1270775 n x y B1 h1). Qed.
Lemma lem1270777 (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term33 y B1 x.
Proof. exact (h1). Qed.
Lemma lem1270778 (n : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term34 y B1 x n.
Proof. exact (@lem1270777 y B1 x h1 n). Qed.
Lemma lem1270779 (y : nadd) (B1 : nat) (x : nadd) (n : nat) : (term34 y B1 x n) = (term32 y B1 x n).
Proof. exact (eq_refl (term34 y B1 x n)). Qed.
Lemma lem1270780 (n : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term32 y B1 x n.
Proof. exact (EQ_MP (@lem1270779 y B1 x n) (@lem1270778 n y B1 x h1)). Qed.
Lemma lem1270781 (n : nat) (p : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term35 y B1 x n p.
Proof. exact (@lem1270780 n y B1 x h1 p). Qed.
Lemma lem1270782 (y : nadd) (B1 : nat) (x : nadd) (n : nat) (p : nat) : (term35 y B1 x n p) = (term36 y B1 x n p).
Proof. exact (eq_refl (term35 y B1 x n p)). Qed.
Lemma lem1270783 (n : nat) (p : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term36 y B1 x n p.
Proof. exact (EQ_MP (@lem1270782 y B1 x n p) (@lem1270781 n p y B1 x h1)). Qed.
Lemma lem1270784 (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term37 y n B1 p) : term37 y n B1 p.
Proof. exact (h1). Qed.
Lemma lem1270785 (x : nadd) (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term33 y B1 x) (h2 : term37 y n B1 p) : term38 x n p.
Proof. exact (@lem1270783 n p y B1 x h1 (@lem1270784 y n B1 p h2)). Qed.
Lemma lem1270786 (x : nadd) (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term37 y n B1 p) : term39 y B1 x n p.
Proof. exact (fun h0 : term33 y B1 x => @lem1270785 x y n B1 p h0 h1). Qed.
Lemma lem1270787 (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term33 y B1 x.
Proof. exact (h1). Qed.
Lemma lem1270788 (x : nadd) (y : nadd) (n : nat) (B1 : nat) (p : nat) (h1 : term33 y B1 x) (h2 : term37 y n B1 p) : term38 x n p.
Proof. exact (@lem1270786 x y n B1 p h2 (@lem1270787 y B1 x h1)). Qed.
Lemma lem1270789 (n : nat) (p : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term36 y B1 x n p.
Proof. exact (fun h0 : term37 y n B1 p => @lem1270788 x y n B1 p h1 h0). Qed.
Lemma lem1270790 (n : nat) (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term32 y B1 x n.
Proof. exact (fun p : nat => @lem1270789 n p y B1 x h1). Qed.
Lemma lem1270791 (y : nadd) (B1 : nat) (x : nadd) (h1 : term33 y B1 x) : term33 y B1 x.
Proof. exact (fun n : nat => @lem1270790 n y B1 x h1). Qed.
Lemma lem1270792 (y : nadd) (B1 : nat) (x : nadd) : term40 y B1 x.
Proof. exact (fun h0 : term33 y B1 x => @lem1270791 y B1 x h0). Qed.
Lemma lem1270793 (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term33 y B1 x.
Proof. exact (@lem1270792 y B1 x (@lem1270776 x y B1 h1)). Qed.
Lemma lem1270794 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term34 y B1 x n.
Proof. exact (@lem1270793 x y B1 h1 n). Qed.
Lemma lem1270795 (y : nadd) (B1 : nat) (x : nadd) (n : nat) : (term34 y B1 x n) = (term32 y B1 x n).
Proof. exact (eq_refl (term34 y B1 x n)). Qed.
Lemma lem1270796 (n : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term32 y B1 x n.
Proof. exact (EQ_MP (@lem1270795 y B1 x n) (@lem1270794 n x y B1 h1)). Qed.
Lemma lem1270797 (n : nat) (p : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term35 y B1 x n p.
Proof. exact (@lem1270796 n x y B1 h1 p). Qed.
Lemma lem1270798 (y : nadd) (B1 : nat) (x : nadd) (n : nat) (p : nat) : (term35 y B1 x n p) = (term36 y B1 x n p).
Proof. exact (eq_refl (term35 y B1 x n p)). Qed.
Lemma lem1270801 (n : nat) (p : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term36 y B1 x n p.
Proof. exact (EQ_MP (@lem1270798 y B1 x n p) (@lem1270797 n p x y B1 h1)). Qed.
Lemma lem1270802 (z : nadd) (n : nat) (B2 : nat) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term41 y x z n B2 B1.
Proof. exact (@lem1270801 n (term42 z n B2 B1) x y B1 h1). Qed.
Lemma lem1270803 (m : nat) : term43 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1270804 (m : nat) : (term43 m) = (term44 m).
Proof. exact (eq_refl (term43 m)). Qed.
Lemma lem1270805 (m : nat) : term44 m.
Proof. exact (EQ_MP (@lem1270804 m) (@lem1270803 m)). Qed.
Lemma lem1270806 (m : nat) (n : nat) : term45 m n.
Proof. exact (@lem1270805 m n). Qed.
Lemma lem1270807 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem1270808 (m : nat) (n : nat) : term46 m n.
Proof. exact (EQ_MP (@lem1270807 m n) (@lem1270806 m n)). Qed.
Lemma lem1270809 (m : nat) (n : nat) (p : nat) : term47 m n p.
Proof. exact (@lem1270808 m n p). Qed.
Lemma lem1270810 (p : nat) (m : nat) (n : nat) : (term47 m n p) = ((term48 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term47 m n p)). Qed.
Lemma lem1270812 (m : nat) : term49 m.
Proof. exact (@lem77960 m). Qed.
Lemma lem1270813 (m : nat) : (term49 m) = (term50 m).
Proof. exact (eq_refl (term49 m)). Qed.
Lemma lem1270814 (m : nat) : term50 m.
Proof. exact (EQ_MP (@lem1270813 m) (@lem1270812 m)). Qed.
Lemma lem1270815 (m : nat) (n : nat) : term51 m n.
Proof. exact (@lem1270814 m n). Qed.
Lemma lem1270816 (m : nat) (n : nat) : (term51 m n) = (term52 m n).
Proof. exact (eq_refl (term51 m n)). Qed.
Lemma lem1270817 (m : nat) (n : nat) : term52 m n.
Proof. exact (EQ_MP (@lem1270816 m n) (@lem1270815 m n)). Qed.
Lemma lem1270818 (m : nat) (n : nat) (p : nat) : term53 m n p.
Proof. exact (@lem1270817 m n p). Qed.
Lemma lem1270819 (m : nat) (n : nat) (p : nat) : (term53 m n p) = ((term54 m n p) = (term55 m n p)).
Proof. exact (eq_refl (term53 m n p)). Qed.
Lemma lem1270826 (n : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : term13 y z B2 n.
Proof. exact (@lem1270687 y z B2 h1 n). Qed.
Lemma lem1270827 (y : nadd) (z : nadd) (n : nat) (B2 : nat) : (term13 y z B2 n) = (term14 y z n B2).
Proof. exact (eq_refl (term13 y z B2 n)). Qed.
Lemma lem1270828 (n : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : term14 y z n B2.
Proof. exact (EQ_MP (@lem1270827 y z n B2) (@lem1270826 n y z B2 h1)). Qed.
Lemma lem1270829 (y : nadd) (z : nadd) (n : nat) (B2 : nat) : (term14 y z n B2) = ((term14 y z n B2) = True).
Proof. exact (@lem7 (term14 y z n B2)). Qed.
Lemma lem1270834 (m : nat) (n : nat) (p : nat) : (term54 m n p) = (term55 m n p).
Proof. exact (EQ_MP (@lem1270819 m n p) (@lem1270818 m n p)). Qed.
Lemma lem1270835 (z : nadd) (n : nat) (B2 : nat) (B1 : nat) : (term42 z n B2 B1) = (term56 z n B2 B1).
Proof. exact (@lem1270834 (dest_nadd z n) B2 B1). Qed.
Lemma lem1270836 (y : nadd) (n : nat) (B1 : nat) : (term57 y n B1) = (term57 y n B1).
Proof. exact (eq_refl (term57 y n B1)). Qed.
Lemma lem1270837 (y : nadd) (z : nadd) (n : nat) (B2 : nat) (B1 : nat) : (term58 y z n B2 B1) = (term59 y z n B2 B1).
Proof. exact (MK_COMB (@lem1270836 y n B1) (@lem1270835 z n B2 B1)). Qed.
Lemma lem1270839 (p : nat) (m : nat) (n : nat) : (term48 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1270810 p m n) (@lem1270809 m n p)). Qed.
Lemma lem1270840 (B1 : nat) (y : nadd) (z : nadd) (n : nat) (B2 : nat) : (term59 y z n B2 B1) = (term14 y z n B2).
Proof. exact (@lem1270839 B1 (dest_nadd y n) (term31 z n B2)). Qed.
Lemma lem1270842 (n : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : (term14 y z n B2) = True.
Proof. exact (EQ_MP (@lem1270829 y z n B2) (@lem1270828 n y z B2 h1)). Qed.
Lemma lem1270843 (n : nat) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : (term59 y z n B2 B1) = True.
Proof. exact (TRANS (@lem1270840 B1 y z n B2) (@lem1270842 n y z B2 h1)). Qed.
Lemma lem1270844 (n : nat) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : (term58 y z n B2 B1) = True.
Proof. exact (TRANS (@lem1270837 y z n B2 B1) (@lem1270843 n B1 y z B2 h1)). Qed.
Lemma lem1270845 (n : nat) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : True = (term58 y z n B2 B1).
Proof. exact (SYM (@lem1270844 n B1 y z B2 h1)). Qed.
Lemma lem1270846 (n : nat) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 y z B2) : term58 y z n B2 B1.
Proof. exact (EQ_MP (@lem1270845 n B1 y z B2 h1) (@lem0)). Qed.
Lemma lem1270847 (n : nat) (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 x y B1) (h2 : term12 y z B2) : term60 x z n B2 B1.
Proof. exact (@lem1270802 z n B2 x y B1 h1 (@lem1270846 n B1 y z B2 h2)). Qed.
Lemma lem1270852 (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 x y B1) (h2 : term12 y z B2) : term61 x z B2 B1.
Proof. exact (fun n : nat => @lem1270847 n x B1 y z B2 h1 h2). Qed.
Lemma lem1270853 (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (B2 : nat) (h1 : term12 x y B1) (h2 : term12 y z B2) : term3 x z.
Proof. exact (ex_intro (term62 x z) (Nat.add B2 B1) (@lem1270852 x B1 y z B2 h1 h2)). Qed.
Lemma lem1270854 (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (h1 : term12 x y B1) (h2 : term3 y z) : term3 x z.
Proof. exact (ex_elim (@lem1270686 y z h2) (fun B2 : nat => fun h0 : term62 y z B2 => @lem1270853 x B1 y z B2 h1 h0)). Qed.
Lemma lem1270855 (z : nadd) (x : nadd) (y : nadd) (B1 : nat) (h1 : term12 x y B1) : term63 y x z.
Proof. exact (fun h0 : term3 y z => @lem1270854 x B1 y z h1 h0). Qed.
Lemma lem1270856 (x : nadd) (y : nadd) (z : nadd) (h1 : term7 x y z) : term3 y z.
Proof. exact (proj2 (@lem1270682 x y z h1)). Qed.
Lemma lem1270857 (x : nadd) (y : nadd) (z : nadd) (h1 : term7 x y z) : term3 x y.
Proof. exact (proj1 (@lem1270682 x y z h1)). Qed.
Lemma lem1270858 (x : nadd) (B1 : nat) (y : nadd) (z : nadd) (h1 : term12 x y B1) (h2 : term3 y z) : term3 x z.
Proof. exact (@lem1270855 z x y B1 h1 (@lem1270683 y z h2)). Qed.
Lemma lem1270859 (x : nadd) (y : nadd) (z : nadd) (h1 : term3 x y) (h2 : term3 y z) : term3 x z.
Proof. exact (ex_elim (@lem1270684 x y h1) (fun B1 : nat => fun h0 : term62 x y B1 => @lem1270858 x B1 y z h0 h2)). Qed.
Lemma lem1270860 (x : nadd) (y : nadd) (z : nadd) (h1 : term3 x y) (h2 : term7 x y z) : (term3 y z) = (term3 x z).
Proof. exact (prop_ext (fun h3 : term3 y z => @lem1270859 x y z h1 h3) (fun h3 : term3 x z => @lem1270856 x y z h2)). Qed.
Lemma lem1270861 (x : nadd) (y : nadd) (z : nadd) (h1 : term3 x y) (h2 : term7 x y z) : term3 x z.
Proof. exact (EQ_MP (@lem1270860 x y z h1 h2) (@lem1270856 x y z h2)). Qed.
Lemma lem1270862 (x : nadd) (y : nadd) (z : nadd) (h1 : term7 x y z) : (term3 x y) = (term3 x z).
Proof. exact (prop_ext (fun h2 : term3 x y => @lem1270861 x y z h2 h1) (fun h2 : term3 x z => @lem1270857 x y z h1)). Qed.
Lemma lem1270863 (x : nadd) (y : nadd) (z : nadd) (h1 : term7 x y z) : term3 x z.
Proof. exact (EQ_MP (@lem1270862 x y z h1) (@lem1270857 x y z h1)). Qed.
Lemma lem1270864 (y : nadd) (x : nadd) (z : nadd) : term11 y x z.
Proof. exact (fun h0 : term7 x y z => @lem1270863 x y z h0). Qed.
Lemma lem1270865 (y : nadd) (x : nadd) (z : nadd) : term10 y x z.
Proof. exact (EQ_MP (@lem1270681 y x z) (@lem1270864 y x z)). Qed.
Lemma lem1270870 (y : nadd) (x : nadd) : term64 y x.
Proof. exact (fun z : nadd => @lem1270865 y x z). Qed.
Lemma lem1270875 (x : nadd) : term65 x.
Proof. exact (fun y : nadd => @lem1270870 y x). Qed.
Lemma lem1270880 : term66.
Proof. exact (fun x : nadd => @lem1270875 x). Qed.
