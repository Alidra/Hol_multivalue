Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1249859_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import EQ_ADD_LCANCEL_0_spec.
Require Import thm0_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1249640 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1249641 (d' : nat) (d'' : nat) (d''' : nat) : (term2 d' d'' d''') = (term3 d' d'' d''').
Proof. exact (@lem1249640 d' d'' (S d''')). Qed.
Lemma lem1249651 (p : nat) : (Nat.add p) = (Nat.add p).
Proof. exact (eq_refl (Nat.add p)). Qed.
Lemma lem1249652 (p : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 p d' d'' d''') = (term5 p d' d'' d''').
Proof. exact (MK_COMB (@lem1249651 p) (@lem1249641 d' d'' d''')). Qed.
Lemma lem1249654 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249655 (d' : nat) (p : nat) (d'' : nat) (d''' : nat) : (term5 p d' d'' d''') = (term5 d' p d'' d''').
Proof. exact (@lem1249654 d' p (term6 d'' d''')). Qed.
Lemma lem1249663 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249664 (d'' : nat) (p : nat) (d''' : nat) : (term3 p d'' d''') = (term3 d'' p d''').
Proof. exact (@lem1249663 d'' p (S d''')). Qed.
Lemma lem1249674 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1249675 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term5 d' p d'' d''') = (term5 d' d'' p d''').
Proof. exact (MK_COMB (@lem1249674 d') (@lem1249664 d'' p d''')). Qed.
Lemma lem1249682 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term5 p d' d'' d''') = (term5 d' d'' p d''').
Proof. exact (TRANS (@lem1249655 d' p d'' d''') (@lem1249675 d' d'' p d''')). Qed.
Lemma lem1249683 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term4 p d' d'' d''') = (term5 d' d'' p d''').
Proof. exact (TRANS (@lem1249652 p d' d'' d''') (@lem1249682 d' d'' p d''')). Qed.
Lemma lem1249684 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1249685 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term7 p d' d'' d''') = (term8 d' d'' p d''').
Proof. exact (MK_COMB (@lem1249684) (@lem1249683 d' d'' p d''')). Qed.
Lemma lem1249687 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249688 (d'' : nat) (p : nat) (d' : nat) (d''' : nat) : (term5 p d'' d' d''') = (term5 d'' p d' d''').
Proof. exact (@lem1249687 d'' p (term6 d' d''')). Qed.
Lemma lem1249696 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249697 (d' : nat) (p : nat) (d''' : nat) : (term3 p d' d''') = (term3 d' p d''').
Proof. exact (@lem1249696 d' p (S d''')). Qed.
Lemma lem1249707 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1249708 (d'' : nat) (d' : nat) (p : nat) (d''' : nat) : (term5 d'' p d' d''') = (term5 d'' d' p d''').
Proof. exact (MK_COMB (@lem1249707 d'') (@lem1249697 d' p d''')). Qed.
Lemma lem1249710 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249711 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term5 d'' d' p d''') = (term5 d' d'' p d''').
Proof. exact (@lem1249710 d' d'' (term6 p d''')). Qed.
Lemma lem1249727 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term5 d'' p d' d''') = (term5 d' d'' p d''').
Proof. exact (TRANS (@lem1249708 d'' d' p d''') (@lem1249711 d' d'' p d''')). Qed.
Lemma lem1249728 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : (term5 p d'' d' d''') = (term5 d' d'' p d''').
Proof. exact (TRANS (@lem1249688 d'' p d' d''') (@lem1249727 d' d'' p d''')). Qed.
Lemma lem1249729 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : ((term4 p d' d'' d''') = (term5 p d'' d' d''')) = ((term5 d' d'' p d''') = (term5 d' d'' p d''')).
Proof. exact (MK_COMB (@lem1249685 d' d'' p d''') (@lem1249728 d' d'' p d''')). Qed.
Lemma lem1249731 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1249732 (x : nat) : (x = x) = True.
Proof. exact (@lem1249731 nat x). Qed.
Lemma lem1249733 (d' : nat) (d'' : nat) (p : nat) (d''' : nat) : ((term5 d' d'' p d''') = (term5 d' d'' p d''')) = True.
Proof. exact (@lem1249732 (term5 d' d'' p d''')). Qed.
Lemma lem1249734 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term4 p d' d'' d''') = (term5 p d'' d' d''')) = True.
Proof. exact (TRANS (@lem1249729 d' d'' p d''') (@lem1249733 d' d'' p d''')). Qed.
Lemma lem1249735 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term4 p d' d'' d''') = (term5 p d'' d' d''')).
Proof. exact (SYM (@lem1249734 p d'' d' d''')). Qed.
Lemma lem1249736 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term4 p d' d'' d''') = (term5 p d'' d' d''').
Proof. exact (EQ_MP (@lem1249735 p d'' d' d''') (@lem0)). Qed.
Lemma lem1249740 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1249741 (p : nat) (d'' : nat) (d' : nat) : (term0 p d'' d') = (term1 p d'' d').
Proof. exact (@lem1249740 p d'' d'). Qed.
Lemma lem1249743 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249744 (d'' : nat) (p : nat) (d' : nat) : (term1 p d'' d') = (term1 d'' p d').
Proof. exact (@lem1249743 d'' p d'). Qed.
Lemma lem1249751 (d'' : nat) (p : nat) (d' : nat) : (term0 p d'' d') = (term1 d'' p d').
Proof. exact (TRANS (@lem1249741 p d'' d') (@lem1249744 d'' p d')). Qed.
Lemma lem1249753 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1249754 (d' : nat) (p : nat) : (Nat.add p d') = (Nat.add d' p).
Proof. exact (@lem1249753 d' p). Qed.
Lemma lem1249758 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1249759 (d'' : nat) (d' : nat) (p : nat) : (term1 d'' p d') = (term1 d'' d' p).
Proof. exact (MK_COMB (@lem1249758 d'') (@lem1249754 d' p)). Qed.
Lemma lem1249761 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249762 (d' : nat) (d'' : nat) (p : nat) : (term1 d'' d' p) = (term1 d' d'' p).
Proof. exact (@lem1249761 d' d'' p). Qed.
Lemma lem1249772 (d' : nat) (d'' : nat) (p : nat) : (term1 d'' p d') = (term1 d' d'' p).
Proof. exact (TRANS (@lem1249759 d'' d' p) (@lem1249762 d' d'' p)). Qed.
Lemma lem1249773 (d' : nat) (d'' : nat) (p : nat) : (term0 p d'' d') = (term1 d' d'' p).
Proof. exact (TRANS (@lem1249751 d'' p d') (@lem1249772 d' d'' p)). Qed.
Lemma lem1249774 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1249775 (d' : nat) (d'' : nat) (p : nat) : (term9 p d'' d') = (term10 d' d'' p).
Proof. exact (MK_COMB (@lem1249774) (@lem1249773 d' d'' p)). Qed.
Lemma lem1249777 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249778 (d'' : nat) (p : nat) (d' : nat) : (term1 p d'' d') = (term1 d'' p d').
Proof. exact (@lem1249777 d'' p d'). Qed.
Lemma lem1249786 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1249787 (d' : nat) (p : nat) : (Nat.add p d') = (Nat.add d' p).
Proof. exact (@lem1249786 d' p). Qed.
Lemma lem1249791 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1249792 (d'' : nat) (d' : nat) (p : nat) : (term1 d'' p d') = (term1 d'' d' p).
Proof. exact (MK_COMB (@lem1249791 d'') (@lem1249787 d' p)). Qed.
Lemma lem1249794 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1249795 (d' : nat) (d'' : nat) (p : nat) : (term1 d'' d' p) = (term1 d' d'' p).
Proof. exact (@lem1249794 d' d'' p). Qed.
Lemma lem1249805 (d' : nat) (d'' : nat) (p : nat) : (term1 d'' p d') = (term1 d' d'' p).
Proof. exact (TRANS (@lem1249792 d'' d' p) (@lem1249795 d' d'' p)). Qed.
Lemma lem1249806 (d' : nat) (d'' : nat) (p : nat) : (term1 p d'' d') = (term1 d' d'' p).
Proof. exact (TRANS (@lem1249778 d'' p d') (@lem1249805 d' d'' p)). Qed.
Lemma lem1249807 (d' : nat) (d'' : nat) (p : nat) : ((term0 p d'' d') = (term1 p d'' d')) = ((term1 d' d'' p) = (term1 d' d'' p)).
Proof. exact (MK_COMB (@lem1249775 d' d'' p) (@lem1249806 d' d'' p)). Qed.
Lemma lem1249809 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1249810 (x : nat) : (x = x) = True.
Proof. exact (@lem1249809 nat x). Qed.
Lemma lem1249811 (d' : nat) (d'' : nat) (p : nat) : ((term1 d' d'' p) = (term1 d' d'' p)) = True.
Proof. exact (@lem1249810 (term1 d' d'' p)). Qed.
Lemma lem1249812 (p : nat) (d'' : nat) (d' : nat) : ((term0 p d'' d') = (term1 p d'' d')) = True.
Proof. exact (TRANS (@lem1249807 d' d'' p) (@lem1249811 d' d'' p)). Qed.
Lemma lem1249813 (p : nat) (d'' : nat) (d' : nat) : True = ((term0 p d'' d') = (term1 p d'' d')).
Proof. exact (SYM (@lem1249812 p d'' d')). Qed.
Lemma lem1249814 (p : nat) (d'' : nat) (d' : nat) : (term0 p d'' d') = (term1 p d'' d').
Proof. exact (EQ_MP (@lem1249813 p d'' d') (@lem0)). Qed.
Lemma lem1249815 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1249816 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term7 p d' d'' d''') = (term8 p d'' d' d''').
Proof. exact (MK_COMB (@lem1249815) (@lem1249736 p d'' d' d''')). Qed.
Lemma lem1249817 (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : ((term4 p d' d'' d''') = (term0 p d'' d')) = ((term5 p d'' d' d''') = (term1 p d'' d')).
Proof. exact (MK_COMB (@lem1249816 p d'' d' d''') (@lem1249814 p d'' d')). Qed.
Lemma lem1249824 (m : nat) : term11 m.
Proof. exact (@lem79890 m). Qed.
Lemma lem1249825 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem1249826 (m : nat) : term12 m.
Proof. exact (EQ_MP (@lem1249825 m) (@lem1249824 m)). Qed.
Lemma lem1249827 (m : nat) (n : nat) : term13 m n.
Proof. exact (@lem1249826 m n). Qed.
Lemma lem1249828 (m : nat) (n : nat) : (term13 m n) = (((Nat.add m n) = m) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term13 m n)). Qed.
Lemma lem1249830 (m : nat) : term14 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1249831 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1249832 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1249831 m) (@lem1249830 m)). Qed.
Lemma lem1249833 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1249832 m n). Qed.
Lemma lem1249834 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1249835 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1249834 m n) (@lem1249833 m n)). Qed.
Lemma lem1249836 (m : nat) (n : nat) (p : nat) : term18 m n p.
Proof. exact (@lem1249835 m n p). Qed.
Lemma lem1249837 (m : nat) (n : nat) (p : nat) : (term18 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term18 m n p)). Qed.
Lemma lem1249840 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1249837 m n p) (@lem1249836 m n p)). Qed.
Lemma lem1249841 (p : nat) (d''' : nat) (d'' : nat) (d' : nat) : ((term5 p d'' d' d''') = (term1 p d'' d')) = ((term3 d'' d' d''') = (Nat.add d'' d')).
Proof. exact (@lem1249840 p (term3 d'' d' d''') (Nat.add d'' d')). Qed.
Lemma lem1249843 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1249837 m n p) (@lem1249836 m n p)). Qed.
Lemma lem1249844 (d'' : nat) (d''' : nat) (d' : nat) : ((term3 d'' d' d''') = (Nat.add d'' d')) = ((term6 d' d''') = d').
Proof. exact (@lem1249843 d'' (term6 d' d''') d'). Qed.
Lemma lem1249846 (m : nat) (n : nat) : ((Nat.add m n) = m) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1249828 m n) (@lem1249827 m n)). Qed.
Lemma lem1249849 (d' : nat) (d''' : nat) : ((term6 d' d''') = d') = ((S d''') = (NUMERAL 0)).
Proof. exact (@lem1249846 d' (S d''')). Qed.
Lemma lem1249850 (d'' : nat) (d' : nat) (d''' : nat) : ((term3 d'' d' d''') = (Nat.add d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1249844 d'' d''' d') (@lem1249849 d' d''')). Qed.
Lemma lem1249851 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term5 p d'' d' d''') = (term1 p d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1249841 p d''' d'' d') (@lem1249850 d'' d' d''')). Qed.
Lemma lem1249852 (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : (term19 d''' p d'' d') = (term19 d''' p d'' d').
Proof. exact (eq_refl (term19 d''' p d'' d')). Qed.
Lemma lem1249853 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((term4 p d' d'' d''') = (term0 p d'' d')) = ((term5 p d'' d' d''') = (term1 p d'' d'))) = (((term4 p d' d'' d''') = (term0 p d'' d')) = ((S d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1249852 d''' p d'' d') (@lem1249851 p d'' d' d''')). Qed.
Lemma lem1249854 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term4 p d' d'' d''') = (term0 p d'' d')) = ((S d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1249853 p d'' d' d''') (@lem1249817 d''' p d'' d')). Qed.
Lemma lem1249855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1249856 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term20 d''' p d'' d') = (term21 d''').
Proof. exact (MK_COMB (@lem1249855) (@lem1249854 p d'' d' d''')). Qed.
Lemma lem1249857 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1249858 (p : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term22 d''' p d'' d') = (term23 d''').
Proof. exact (MK_COMB (@lem1249856 p d'' d' d''') (@lem1249857)). Qed.
Lemma lem1249859 (d''' : nat) (p : nat) (d'' : nat) (d' : nat) : (term23 d''') = (term22 d''' p d'' d').
Proof. exact (SYM (@lem1249858 p d'' d' d''')). Qed.
