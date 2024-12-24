Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1254983_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1254601 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254602 (m : nat) (d' : nat) (n : nat) (d'' : nat) : (term2 m d' n d'') = (term3 m d' n d'').
Proof. exact (@lem1254601 m d' (Nat.add n d'')). Qed.
Lemma lem1254604 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254605 (d' : nat) (m : nat) (n : nat) (d'' : nat) : (term3 m d' n d'') = (term3 d' m n d'').
Proof. exact (@lem1254604 d' m (Nat.add n d'')). Qed.
Lemma lem1254612 (d' : nat) (m : nat) (n : nat) (d'' : nat) : (term2 m d' n d'') = (term3 d' m n d'').
Proof. exact (TRANS (@lem1254602 m d' n d'') (@lem1254605 d' m n d'')). Qed.
Lemma lem1254620 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1254621 (d'' : nat) (n : nat) : (Nat.add n d'') = (Nat.add d'' n).
Proof. exact (@lem1254620 d'' n). Qed.
Lemma lem1254625 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1254626 (m : nat) (d'' : nat) (n : nat) : (term1 m n d'') = (term1 m d'' n).
Proof. exact (MK_COMB (@lem1254625 m) (@lem1254621 d'' n)). Qed.
Lemma lem1254628 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254629 (d'' : nat) (m : nat) (n : nat) : (term1 m d'' n) = (term1 d'' m n).
Proof. exact (@lem1254628 d'' m n). Qed.
Lemma lem1254638 (d'' : nat) (m : nat) (n : nat) : (term1 m n d'') = (term1 d'' m n).
Proof. exact (TRANS (@lem1254626 m d'' n) (@lem1254629 d'' m n)). Qed.
Lemma lem1254639 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254640 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term3 d' m n d'') = (term3 d' d'' m n).
Proof. exact (MK_COMB (@lem1254639 d') (@lem1254638 d'' m n)). Qed.
Lemma lem1254647 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term2 m d' n d'') = (term3 d' d'' m n).
Proof. exact (TRANS (@lem1254612 d' m n d'') (@lem1254640 d' d'' m n)). Qed.
Lemma lem1254648 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254649 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term4 m d' n d'') = (term5 d' d'' m n).
Proof. exact (MK_COMB (@lem1254648) (@lem1254647 d' d'' m n)). Qed.
Lemma lem1254651 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254652 (m : nat) (n : nat) (d'' : nat) (d' : nat) : (term3 n m d'' d') = (term3 m n d'' d').
Proof. exact (@lem1254651 m n (Nat.add d'' d')). Qed.
Lemma lem1254660 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254661 (d'' : nat) (n : nat) (d' : nat) : (term1 n d'' d') = (term1 d'' n d').
Proof. exact (@lem1254660 d'' n d'). Qed.
Lemma lem1254669 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1254670 (d' : nat) (n : nat) : (Nat.add n d') = (Nat.add d' n).
Proof. exact (@lem1254669 d' n). Qed.
Lemma lem1254674 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1254675 (d'' : nat) (d' : nat) (n : nat) : (term1 d'' n d') = (term1 d'' d' n).
Proof. exact (MK_COMB (@lem1254674 d'') (@lem1254670 d' n)). Qed.
Lemma lem1254677 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254678 (d' : nat) (d'' : nat) (n : nat) : (term1 d'' d' n) = (term1 d' d'' n).
Proof. exact (@lem1254677 d' d'' n). Qed.
Lemma lem1254688 (d' : nat) (d'' : nat) (n : nat) : (term1 d'' n d') = (term1 d' d'' n).
Proof. exact (TRANS (@lem1254675 d'' d' n) (@lem1254678 d' d'' n)). Qed.
Lemma lem1254689 (d' : nat) (d'' : nat) (n : nat) : (term1 n d'' d') = (term1 d' d'' n).
Proof. exact (TRANS (@lem1254661 d'' n d') (@lem1254688 d' d'' n)). Qed.
Lemma lem1254690 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1254691 (m : nat) (d' : nat) (d'' : nat) (n : nat) : (term3 m n d'' d') = (term3 m d' d'' n).
Proof. exact (MK_COMB (@lem1254690 m) (@lem1254689 d' d'' n)). Qed.
Lemma lem1254693 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254694 (d' : nat) (m : nat) (d'' : nat) (n : nat) : (term3 m d' d'' n) = (term3 d' m d'' n).
Proof. exact (@lem1254693 d' m (Nat.add d'' n)). Qed.
Lemma lem1254702 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254703 (d'' : nat) (m : nat) (n : nat) : (term1 m d'' n) = (term1 d'' m n).
Proof. exact (@lem1254702 d'' m n). Qed.
Lemma lem1254712 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254713 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term3 d' m d'' n) = (term3 d' d'' m n).
Proof. exact (MK_COMB (@lem1254712 d') (@lem1254703 d'' m n)). Qed.
Lemma lem1254720 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term3 m d' d'' n) = (term3 d' d'' m n).
Proof. exact (TRANS (@lem1254694 d' m d'' n) (@lem1254713 d' d'' m n)). Qed.
Lemma lem1254721 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term3 m n d'' d') = (term3 d' d'' m n).
Proof. exact (TRANS (@lem1254691 m d' d'' n) (@lem1254720 d' d'' m n)). Qed.
Lemma lem1254722 (d' : nat) (d'' : nat) (m : nat) (n : nat) : (term3 n m d'' d') = (term3 d' d'' m n).
Proof. exact (TRANS (@lem1254652 m n d'' d') (@lem1254721 d' d'' m n)). Qed.
Lemma lem1254723 (d' : nat) (d'' : nat) (m : nat) (n : nat) : ((term2 m d' n d'') = (term3 n m d'' d')) = ((term3 d' d'' m n) = (term3 d' d'' m n)).
Proof. exact (MK_COMB (@lem1254649 d' d'' m n) (@lem1254722 d' d'' m n)). Qed.
Lemma lem1254725 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1254726 (x : nat) : (x = x) = True.
Proof. exact (@lem1254725 nat x). Qed.
Lemma lem1254727 (d' : nat) (d'' : nat) (m : nat) (n : nat) : ((term3 d' d'' m n) = (term3 d' d'' m n)) = True.
Proof. exact (@lem1254726 (term3 d' d'' m n)). Qed.
Lemma lem1254728 (n : nat) (m : nat) (d'' : nat) (d' : nat) : ((term2 m d' n d'') = (term3 n m d'' d')) = True.
Proof. exact (TRANS (@lem1254723 d' d'' m n) (@lem1254727 d' d'' m n)). Qed.
Lemma lem1254729 (n : nat) (m : nat) (d'' : nat) (d' : nat) : True = ((term2 m d' n d'') = (term3 n m d'' d')).
Proof. exact (SYM (@lem1254728 n m d'' d')). Qed.
Lemma lem1254730 (n : nat) (m : nat) (d'' : nat) (d' : nat) : (term2 m d' n d'') = (term3 n m d'' d').
Proof. exact (EQ_MP (@lem1254729 n m d'' d') (@lem0)). Qed.
Lemma lem1254734 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254735 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term6 m n d' d'' d''') = (term7 m n d' d'' d''').
Proof. exact (@lem1254734 m n (term8 d' d'' d''')). Qed.
Lemma lem1254749 (m : nat) (n : nat) (p : nat) : (term0 m n p) = (term1 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1254750 (d' : nat) (d'' : nat) (d''' : nat) : (term8 d' d'' d''') = (term9 d' d'' d''').
Proof. exact (@lem1254749 d' d'' (S d''')). Qed.
Lemma lem1254760 (n : nat) : (Nat.add n) = (Nat.add n).
Proof. exact (eq_refl (Nat.add n)). Qed.
Lemma lem1254761 (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term10 n d' d'' d''') = (term11 n d' d'' d''').
Proof. exact (MK_COMB (@lem1254760 n) (@lem1254750 d' d'' d''')). Qed.
Lemma lem1254763 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254764 (d' : nat) (n : nat) (d'' : nat) (d''' : nat) : (term11 n d' d'' d''') = (term11 d' n d'' d''').
Proof. exact (@lem1254763 d' n (term12 d'' d''')). Qed.
Lemma lem1254772 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254773 (d'' : nat) (n : nat) (d''' : nat) : (term9 n d'' d''') = (term9 d'' n d''').
Proof. exact (@lem1254772 d'' n (S d''')). Qed.
Lemma lem1254783 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254784 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 d' n d'' d''') = (term11 d' d'' n d''').
Proof. exact (MK_COMB (@lem1254783 d') (@lem1254773 d'' n d''')). Qed.
Lemma lem1254791 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 n d' d'' d''') = (term11 d' d'' n d''').
Proof. exact (TRANS (@lem1254764 d' n d'' d''') (@lem1254784 d' d'' n d''')). Qed.
Lemma lem1254792 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term10 n d' d'' d''') = (term11 d' d'' n d''').
Proof. exact (TRANS (@lem1254761 n d' d'' d''') (@lem1254791 d' d'' n d''')). Qed.
Lemma lem1254793 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1254794 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term7 m n d' d'' d''') = (term13 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1254793 m) (@lem1254792 d' d'' n d''')). Qed.
Lemma lem1254796 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254797 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 m d' d'' n d''') = (term13 d' m d'' n d''').
Proof. exact (@lem1254796 d' m (term9 d'' n d''')). Qed.
Lemma lem1254805 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254806 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term11 m d'' n d''') = (term11 d'' m n d''').
Proof. exact (@lem1254805 d'' m (term12 n d''')). Qed.
Lemma lem1254822 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254823 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 d' m d'' n d''') = (term13 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1254822 d') (@lem1254806 d'' m n d''')). Qed.
Lemma lem1254830 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 m d' d'' n d''') = (term13 d' d'' m n d''').
Proof. exact (TRANS (@lem1254797 d' m d'' n d''') (@lem1254823 d' d'' m n d''')). Qed.
Lemma lem1254831 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term7 m n d' d'' d''') = (term13 d' d'' m n d''').
Proof. exact (TRANS (@lem1254794 m d' d'' n d''') (@lem1254830 d' d'' m n d''')). Qed.
Lemma lem1254832 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term6 m n d' d'' d''') = (term13 d' d'' m n d''').
Proof. exact (TRANS (@lem1254735 m n d' d'' d''') (@lem1254831 d' d'' m n d''')). Qed.
Lemma lem1254833 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254834 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term14 m n d' d'' d''') = (term15 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1254833) (@lem1254832 d' d'' m n d''')). Qed.
Lemma lem1254836 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254837 (m : nat) (n : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term13 n m d'' d' d''') = (term13 m n d'' d' d''').
Proof. exact (@lem1254836 m n (term9 d'' d' d''')). Qed.
Lemma lem1254845 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254846 (d'' : nat) (n : nat) (d' : nat) (d''' : nat) : (term11 n d'' d' d''') = (term11 d'' n d' d''').
Proof. exact (@lem1254845 d'' n (term12 d' d''')). Qed.
Lemma lem1254854 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254855 (d' : nat) (n : nat) (d''' : nat) : (term9 n d' d''') = (term9 d' n d''').
Proof. exact (@lem1254854 d' n (S d''')). Qed.
Lemma lem1254865 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1254866 (d'' : nat) (d' : nat) (n : nat) (d''' : nat) : (term11 d'' n d' d''') = (term11 d'' d' n d''').
Proof. exact (MK_COMB (@lem1254865 d'') (@lem1254855 d' n d''')). Qed.
Lemma lem1254868 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254869 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 d'' d' n d''') = (term11 d' d'' n d''').
Proof. exact (@lem1254868 d' d'' (term12 n d''')). Qed.
Lemma lem1254885 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 d'' n d' d''') = (term11 d' d'' n d''').
Proof. exact (TRANS (@lem1254866 d'' d' n d''') (@lem1254869 d' d'' n d''')). Qed.
Lemma lem1254886 (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term11 n d'' d' d''') = (term11 d' d'' n d''').
Proof. exact (TRANS (@lem1254846 d'' n d' d''') (@lem1254885 d' d'' n d''')). Qed.
Lemma lem1254887 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1254888 (m : nat) (d' : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 m n d'' d' d''') = (term13 m d' d'' n d''').
Proof. exact (MK_COMB (@lem1254887 m) (@lem1254886 d' d'' n d''')). Qed.
Lemma lem1254890 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254891 (d' : nat) (m : nat) (d'' : nat) (n : nat) (d''' : nat) : (term13 m d' d'' n d''') = (term13 d' m d'' n d''').
Proof. exact (@lem1254890 d' m (term9 d'' n d''')). Qed.
Lemma lem1254899 (n : nat) (m : nat) (p : nat) : (term1 m n p) = (term1 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1254900 (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term11 m d'' n d''') = (term11 d'' m n d''').
Proof. exact (@lem1254899 d'' m (term12 n d''')). Qed.
Lemma lem1254916 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1254917 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 d' m d'' n d''') = (term13 d' d'' m n d''').
Proof. exact (MK_COMB (@lem1254916 d') (@lem1254900 d'' m n d''')). Qed.
Lemma lem1254924 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 m d' d'' n d''') = (term13 d' d'' m n d''').
Proof. exact (TRANS (@lem1254891 d' m d'' n d''') (@lem1254917 d' d'' m n d''')). Qed.
Lemma lem1254925 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 m n d'' d' d''') = (term13 d' d'' m n d''').
Proof. exact (TRANS (@lem1254888 m d' d'' n d''') (@lem1254924 d' d'' m n d''')). Qed.
Lemma lem1254926 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : (term13 n m d'' d' d''') = (term13 d' d'' m n d''').
Proof. exact (TRANS (@lem1254837 m n d'' d' d''') (@lem1254925 d' d'' m n d''')). Qed.
Lemma lem1254927 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term6 m n d' d'' d''') = (term13 n m d'' d' d''')) = ((term13 d' d'' m n d''') = (term13 d' d'' m n d''')).
Proof. exact (MK_COMB (@lem1254834 d' d'' m n d''') (@lem1254926 d' d'' m n d''')). Qed.
Lemma lem1254929 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1254930 (x : nat) : (x = x) = True.
Proof. exact (@lem1254929 nat x). Qed.
Lemma lem1254931 (d' : nat) (d'' : nat) (m : nat) (n : nat) (d''' : nat) : ((term13 d' d'' m n d''') = (term13 d' d'' m n d''')) = True.
Proof. exact (@lem1254930 (term13 d' d'' m n d''')). Qed.
Lemma lem1254932 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term6 m n d' d'' d''') = (term13 n m d'' d' d''')) = True.
Proof. exact (TRANS (@lem1254927 d' d'' m n d''') (@lem1254931 d' d'' m n d''')). Qed.
Lemma lem1254933 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term6 m n d' d'' d''') = (term13 n m d'' d' d''')).
Proof. exact (SYM (@lem1254932 n m d'' d' d''')). Qed.
Lemma lem1254934 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term6 m n d' d'' d''') = (term13 n m d'' d' d''').
Proof. exact (EQ_MP (@lem1254933 n m d'' d' d''') (@lem0)). Qed.
Lemma lem1254935 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1254936 (n : nat) (m : nat) (d'' : nat) (d' : nat) : (term4 m d' n d'') = (term5 n m d'' d').
Proof. exact (MK_COMB (@lem1254935) (@lem1254730 n m d'' d')). Qed.
Lemma lem1254937 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term2 m d' n d'') = (term6 m n d' d'' d''')) = ((term3 n m d'' d') = (term13 n m d'' d' d''')).
Proof. exact (MK_COMB (@lem1254936 n m d'' d') (@lem1254934 n m d'' d' d''')). Qed.
Lemma lem1254938 (m : nat) : term16 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1254939 (m : nat) : (term16 m) = (term17 m).
Proof. exact (eq_refl (term16 m)). Qed.
Lemma lem1254940 (m : nat) : term17 m.
Proof. exact (EQ_MP (@lem1254939 m) (@lem1254938 m)). Qed.
Lemma lem1254941 (m : nat) (n : nat) : term18 m n.
Proof. exact (@lem1254940 m n). Qed.
Lemma lem1254942 (m : nat) (n : nat) : (term18 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term18 m n)). Qed.
Lemma lem1254950 (m : nat) : term19 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1254951 (m : nat) : (term19 m) = (term20 m).
Proof. exact (eq_refl (term19 m)). Qed.
Lemma lem1254952 (m : nat) : term20 m.
Proof. exact (EQ_MP (@lem1254951 m) (@lem1254950 m)). Qed.
Lemma lem1254953 (m : nat) (n : nat) : term21 m n.
Proof. exact (@lem1254952 m n). Qed.
Lemma lem1254954 (m : nat) (n : nat) : (term21 m n) = (term22 m n).
Proof. exact (eq_refl (term21 m n)). Qed.
Lemma lem1254955 (m : nat) (n : nat) : term22 m n.
Proof. exact (EQ_MP (@lem1254954 m n) (@lem1254953 m n)). Qed.
Lemma lem1254956 (m : nat) (n : nat) (p : nat) : term23 m n p.
Proof. exact (@lem1254955 m n p). Qed.
Lemma lem1254957 (m : nat) (n : nat) (p : nat) : (term23 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term23 m n p)). Qed.
Lemma lem1254960 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1254957 m n p) (@lem1254956 m n p)). Qed.
Lemma lem1254961 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 n m d'' d') = (term13 n m d'' d' d''')) = ((term1 m d'' d') = (term11 m d'' d' d''')).
Proof. exact (@lem1254960 n (term1 m d'' d') (term11 m d'' d' d''')). Qed.
Lemma lem1254963 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1254957 m n p) (@lem1254956 m n p)). Qed.
Lemma lem1254964 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term1 m d'' d') = (term11 m d'' d' d''')) = ((Nat.add d'' d') = (term9 d'' d' d''')).
Proof. exact (@lem1254963 m (Nat.add d'' d') (term9 d'' d' d''')). Qed.
Lemma lem1254966 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1254957 m n p) (@lem1254956 m n p)). Qed.
Lemma lem1254967 (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add d'' d') = (term9 d'' d' d''')) = (d' = (term12 d' d''')).
Proof. exact (@lem1254966 d'' d' (term12 d' d''')). Qed.
Lemma lem1254969 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1254942 m n) (@lem1254941 m n)). Qed.
Lemma lem1254972 (d' : nat) (d''' : nat) : (d' = (term12 d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (@lem1254969 d' (S d''')). Qed.
Lemma lem1254973 (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add d'' d') = (term9 d'' d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1254967 d'' d' d''') (@lem1254972 d' d''')). Qed.
Lemma lem1254974 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term1 m d'' d') = (term11 m d'' d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1254964 m d'' d' d''') (@lem1254973 d'' d' d''')). Qed.
Lemma lem1254975 (n : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 n m d'' d') = (term13 n m d'' d' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1254961 n m d'' d' d''') (@lem1254974 m d'' d' d''')). Qed.
Lemma lem1254976 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term24 m n d' d'' d''') = (term24 m n d' d'' d''').
Proof. exact (eq_refl (term24 m n d' d'' d''')). Qed.
Lemma lem1254977 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (((term2 m d' n d'') = (term6 m n d' d'' d''')) = ((term3 n m d'' d') = (term13 n m d'' d' d'''))) = (((term2 m d' n d'') = (term6 m n d' d'' d''')) = ((S d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1254976 m n d' d'' d''') (@lem1254975 n m d'' d' d''')). Qed.
Lemma lem1254978 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : ((term2 m d' n d'') = (term6 m n d' d'' d''')) = ((S d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1254977 m n d' d'' d''') (@lem1254937 n m d'' d' d''')). Qed.
Lemma lem1254979 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1254980 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term25 m n d' d'' d''') = (term26 d''').
Proof. exact (MK_COMB (@lem1254979) (@lem1254978 m n d' d'' d''')). Qed.
Lemma lem1254981 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1254982 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term27 m n d' d'' d''') = (term28 d''').
Proof. exact (MK_COMB (@lem1254980 m n d' d'' d''') (@lem1254981)). Qed.
Lemma lem1254983 (m : nat) (n : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term28 d''') = (term27 m n d' d'' d''').
Proof. exact (SYM (@lem1254982 m n d' d'' d''')). Qed.
