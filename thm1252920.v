Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1252920_term_abbrevs.
Require Import ADD_AC_spec.
Require Import EQ_ADD_LCANCEL_spec.
Require Import thm0_spec.
Require Import thm272789_spec.
Require Import thm272790_spec.
Require Import thm272791_spec.
Require Import thm272793_spec.
Lemma lem1252533 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1252534 (d'' : nat) (q : nat) : (Nat.add q d'') = (Nat.add d'' q).
Proof. exact (@lem1252533 d'' q). Qed.
Lemma lem1252538 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1252539 (m : nat) (d'' : nat) (q : nat) : (term0 m q d'') = (term0 m d'' q).
Proof. exact (MK_COMB (@lem1252538 m) (@lem1252534 d'' q)). Qed.
Lemma lem1252541 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252542 (d'' : nat) (m : nat) (q : nat) : (term0 m d'' q) = (term0 d'' m q).
Proof. exact (@lem1252541 d'' m q). Qed.
Lemma lem1252552 (d'' : nat) (m : nat) (q : nat) : (term0 m q d'') = (term0 d'' m q).
Proof. exact (TRANS (@lem1252539 m d'' q) (@lem1252542 d'' m q)). Qed.
Lemma lem1252553 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1252554 (d'' : nat) (m : nat) (q : nat) : (term1 m q d'') = (term1 d'' m q).
Proof. exact (MK_COMB (@lem1252553) (@lem1252552 d'' m q)). Qed.
Lemma lem1252556 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252557 (m : nat) (q : nat) (d'' : nat) : (term0 q m d'') = (term0 m q d'').
Proof. exact (@lem1252556 m q d''). Qed.
Lemma lem1252565 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (proj1 (@lem79120 n m (@el nat))). Qed.
Lemma lem1252566 (d'' : nat) (q : nat) : (Nat.add q d'') = (Nat.add d'' q).
Proof. exact (@lem1252565 d'' q). Qed.
Lemma lem1252570 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1252571 (m : nat) (d'' : nat) (q : nat) : (term0 m q d'') = (term0 m d'' q).
Proof. exact (MK_COMB (@lem1252570 m) (@lem1252566 d'' q)). Qed.
Lemma lem1252573 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252574 (d'' : nat) (m : nat) (q : nat) : (term0 m d'' q) = (term0 d'' m q).
Proof. exact (@lem1252573 d'' m q). Qed.
Lemma lem1252584 (d'' : nat) (m : nat) (q : nat) : (term0 m q d'') = (term0 d'' m q).
Proof. exact (TRANS (@lem1252571 m d'' q) (@lem1252574 d'' m q)). Qed.
Lemma lem1252585 (d'' : nat) (m : nat) (q : nat) : (term0 q m d'') = (term0 d'' m q).
Proof. exact (TRANS (@lem1252557 m q d'') (@lem1252584 d'' m q)). Qed.
Lemma lem1252586 (d'' : nat) (m : nat) (q : nat) : ((term0 m q d'') = (term0 q m d'')) = ((term0 d'' m q) = (term0 d'' m q)).
Proof. exact (MK_COMB (@lem1252554 d'' m q) (@lem1252585 d'' m q)). Qed.
Lemma lem1252588 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1252589 (x : nat) : (x = x) = True.
Proof. exact (@lem1252588 nat x). Qed.
Lemma lem1252590 (d'' : nat) (m : nat) (q : nat) : ((term0 d'' m q) = (term0 d'' m q)) = True.
Proof. exact (@lem1252589 (term0 d'' m q)). Qed.
Lemma lem1252591 (q : nat) (m : nat) (d'' : nat) : ((term0 m q d'') = (term0 q m d'')) = True.
Proof. exact (TRANS (@lem1252586 d'' m q) (@lem1252590 d'' m q)). Qed.
Lemma lem1252592 (q : nat) (m : nat) (d'' : nat) : True = ((term0 m q d'') = (term0 q m d'')).
Proof. exact (SYM (@lem1252591 q m d'')). Qed.
Lemma lem1252593 (q : nat) (m : nat) (d'' : nat) : (term0 m q d'') = (term0 q m d'').
Proof. exact (EQ_MP (@lem1252592 q m d'') (@lem0)). Qed.
Lemma lem1252597 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252598 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m q d' d'' d''') = (term4 m q d' d'' d''').
Proof. exact (@lem1252597 (Nat.add m d') q (term5 d' d'' d''')). Qed.
Lemma lem1252600 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252601 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 m q d' d'' d''') = (term6 m q d' d'' d''').
Proof. exact (@lem1252600 m d' (term7 q d' d'' d''')). Qed.
Lemma lem1252603 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252604 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term6 m q d' d'' d''') = (term8 m q d' d'' d''').
Proof. exact (@lem1252603 d' m (term7 q d' d'' d''')). Qed.
Lemma lem1252611 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term4 m q d' d'' d''') = (term8 m q d' d'' d''').
Proof. exact (TRANS (@lem1252601 m q d' d'' d''') (@lem1252604 m q d' d'' d''')). Qed.
Lemma lem1252612 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term3 m q d' d'' d''') = (term8 m q d' d'' d''').
Proof. exact (TRANS (@lem1252598 m q d' d'' d''') (@lem1252611 m q d' d'' d''')). Qed.
Lemma lem1252626 (m : nat) (n : nat) (p : nat) : (term2 m n p) = (term0 m n p).
Proof. exact (proj1 (@lem272793 n m p)). Qed.
Lemma lem1252627 (d' : nat) (d'' : nat) (d''' : nat) : (term5 d' d'' d''') = (term9 d' d'' d''').
Proof. exact (@lem1252626 d' d'' (S d''')). Qed.
Lemma lem1252637 (q : nat) : (Nat.add q) = (Nat.add q).
Proof. exact (eq_refl (Nat.add q)). Qed.
Lemma lem1252638 (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term7 q d' d'' d''') = (term10 q d' d'' d''').
Proof. exact (MK_COMB (@lem1252637 q) (@lem1252627 d' d'' d''')). Qed.
Lemma lem1252640 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252641 (d' : nat) (q : nat) (d'' : nat) (d''' : nat) : (term10 q d' d'' d''') = (term10 d' q d'' d''').
Proof. exact (@lem1252640 d' q (term11 d'' d''')). Qed.
Lemma lem1252649 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252650 (d'' : nat) (q : nat) (d''' : nat) : (term9 q d'' d''') = (term9 d'' q d''').
Proof. exact (@lem1252649 d'' q (S d''')). Qed.
Lemma lem1252660 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252661 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 d' q d'' d''') = (term10 d' d'' q d''').
Proof. exact (MK_COMB (@lem1252660 d') (@lem1252650 d'' q d''')). Qed.
Lemma lem1252668 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 q d' d'' d''') = (term10 d' d'' q d''').
Proof. exact (TRANS (@lem1252641 d' q d'' d''') (@lem1252661 d' d'' q d''')). Qed.
Lemma lem1252669 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term7 q d' d'' d''') = (term10 d' d'' q d''').
Proof. exact (TRANS (@lem1252638 q d' d'' d''') (@lem1252668 d' d'' q d''')). Qed.
Lemma lem1252670 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1252671 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term12 m q d' d'' d''') = (term13 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1252670 m) (@lem1252669 d' d'' q d''')). Qed.
Lemma lem1252673 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252674 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' m d'' q d''').
Proof. exact (@lem1252673 d' m (term9 d'' q d''')). Qed.
Lemma lem1252682 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252683 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term10 m d'' q d''') = (term10 d'' m q d''').
Proof. exact (@lem1252682 d'' m (term11 q d''')). Qed.
Lemma lem1252699 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252700 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 d' m d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1252699 d') (@lem1252683 d'' m q d''')). Qed.
Lemma lem1252707 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1252674 d' m d'' q d''') (@lem1252700 d' d'' m q d''')). Qed.
Lemma lem1252708 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term12 m q d' d'' d''') = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1252671 m d' d'' q d''') (@lem1252707 d' d'' m q d''')). Qed.
Lemma lem1252709 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252710 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term8 m q d' d'' d''') = (term14 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1252709 d') (@lem1252708 d' d'' m q d''')). Qed.
Lemma lem1252717 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term3 m q d' d'' d''') = (term14 d' d'' m q d''').
Proof. exact (TRANS (@lem1252612 m q d' d'' d''') (@lem1252710 d' d'' m q d''')). Qed.
Lemma lem1252718 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1252719 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term15 m q d' d'' d''') = (term16 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1252718) (@lem1252717 d' d'' m q d''')). Qed.
Lemma lem1252721 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252722 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term17 q m d'' d' d''') = (term17 m q d'' d' d''').
Proof. exact (@lem1252721 m q (term18 d'' d' d''')). Qed.
Lemma lem1252730 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252731 (d'' : nat) (q : nat) (d' : nat) (d''' : nat) : (term19 q d'' d' d''') = (term19 d'' q d' d''').
Proof. exact (@lem1252730 d'' q (term20 d' d''')). Qed.
Lemma lem1252739 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252740 (q : nat) (d' : nat) (d''' : nat) : (term18 q d' d''') = (term21 q d' d''').
Proof. exact (@lem1252739 d' q (term11 d' d''')). Qed.
Lemma lem1252748 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252749 (d' : nat) (q : nat) (d''' : nat) : (term9 q d' d''') = (term9 d' q d''').
Proof. exact (@lem1252748 d' q (S d''')). Qed.
Lemma lem1252759 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252760 (d' : nat) (q : nat) (d''' : nat) : (term21 q d' d''') = (term22 d' q d''').
Proof. exact (MK_COMB (@lem1252759 d') (@lem1252749 d' q d''')). Qed.
Lemma lem1252767 (d' : nat) (q : nat) (d''' : nat) : (term18 q d' d''') = (term22 d' q d''').
Proof. exact (TRANS (@lem1252740 q d' d''') (@lem1252760 d' q d''')). Qed.
Lemma lem1252768 (d'' : nat) : (Nat.add d'') = (Nat.add d'').
Proof. exact (eq_refl (Nat.add d'')). Qed.
Lemma lem1252769 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term19 d'' q d' d''') = (term23 d'' d' q d''').
Proof. exact (MK_COMB (@lem1252768 d'') (@lem1252767 d' q d''')). Qed.
Lemma lem1252771 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252772 (d'' : nat) (d' : nat) (q : nat) (d''' : nat) : (term23 d'' d' q d''') = (term24 d'' d' q d''').
Proof. exact (@lem1252771 d' d'' (term9 d' q d''')). Qed.
Lemma lem1252780 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252781 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term10 d'' d' q d''') = (term10 d' d'' q d''').
Proof. exact (@lem1252780 d' d'' (term11 q d''')). Qed.
Lemma lem1252797 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252798 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term24 d'' d' q d''') = (term25 d' d'' q d''').
Proof. exact (MK_COMB (@lem1252797 d') (@lem1252781 d' d'' q d''')). Qed.
Lemma lem1252805 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term23 d'' d' q d''') = (term25 d' d'' q d''').
Proof. exact (TRANS (@lem1252772 d'' d' q d''') (@lem1252798 d' d'' q d''')). Qed.
Lemma lem1252806 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term19 d'' q d' d''') = (term25 d' d'' q d''').
Proof. exact (TRANS (@lem1252769 d'' d' q d''') (@lem1252805 d' d'' q d''')). Qed.
Lemma lem1252807 (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term19 q d'' d' d''') = (term25 d' d'' q d''').
Proof. exact (TRANS (@lem1252731 d'' q d' d''') (@lem1252806 d' d'' q d''')). Qed.
Lemma lem1252808 (m : nat) : (Nat.add m) = (Nat.add m).
Proof. exact (eq_refl (Nat.add m)). Qed.
Lemma lem1252809 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term17 m q d'' d' d''') = (term26 m d' d'' q d''').
Proof. exact (MK_COMB (@lem1252808 m) (@lem1252807 d' d'' q d''')). Qed.
Lemma lem1252811 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252812 (m : nat) (d' : nat) (d'' : nat) (q : nat) (d''' : nat) : (term26 m d' d'' q d''') = (term27 m d' d'' q d''').
Proof. exact (@lem1252811 d' m (term10 d' d'' q d''')). Qed.
Lemma lem1252820 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252821 (d' : nat) (m : nat) (d'' : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' m d'' q d''').
Proof. exact (@lem1252820 d' m (term9 d'' q d''')). Qed.
Lemma lem1252829 (n : nat) (m : nat) (p : nat) : (term0 m n p) = (term0 n m p).
Proof. exact (proj2 (@lem272793 n m p)). Qed.
Lemma lem1252830 (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term10 m d'' q d''') = (term10 d'' m q d''').
Proof. exact (@lem1252829 d'' m (term11 q d''')). Qed.
Lemma lem1252846 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252847 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 d' m d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1252846 d') (@lem1252830 d'' m q d''')). Qed.
Lemma lem1252854 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term13 m d' d'' q d''') = (term13 d' d'' m q d''').
Proof. exact (TRANS (@lem1252821 d' m d'' q d''') (@lem1252847 d' d'' m q d''')). Qed.
Lemma lem1252855 (d' : nat) : (Nat.add d') = (Nat.add d').
Proof. exact (eq_refl (Nat.add d')). Qed.
Lemma lem1252856 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term27 m d' d'' q d''') = (term14 d' d'' m q d''').
Proof. exact (MK_COMB (@lem1252855 d') (@lem1252854 d' d'' m q d''')). Qed.
Lemma lem1252863 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term26 m d' d'' q d''') = (term14 d' d'' m q d''').
Proof. exact (TRANS (@lem1252812 m d' d'' q d''') (@lem1252856 d' d'' m q d''')). Qed.
Lemma lem1252864 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term17 m q d'' d' d''') = (term14 d' d'' m q d''').
Proof. exact (TRANS (@lem1252809 m d' d'' q d''') (@lem1252863 d' d'' m q d''')). Qed.
Lemma lem1252865 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : (term17 q m d'' d' d''') = (term14 d' d'' m q d''').
Proof. exact (TRANS (@lem1252722 m q d'' d' d''') (@lem1252864 d' d'' m q d''')). Qed.
Lemma lem1252866 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term3 m q d' d'' d''') = (term17 q m d'' d' d''')) = ((term14 d' d'' m q d''') = (term14 d' d'' m q d''')).
Proof. exact (MK_COMB (@lem1252719 d' d'' m q d''') (@lem1252865 d' d'' m q d''')). Qed.
Lemma lem1252868 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem272791 A x) (@lem272790 A x)). Qed.
Lemma lem1252869 (x : nat) : (x = x) = True.
Proof. exact (@lem1252868 nat x). Qed.
Lemma lem1252870 (d' : nat) (d'' : nat) (m : nat) (q : nat) (d''' : nat) : ((term14 d' d'' m q d''') = (term14 d' d'' m q d''')) = True.
Proof. exact (@lem1252869 (term14 d' d'' m q d''')). Qed.
Lemma lem1252871 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term3 m q d' d'' d''') = (term17 q m d'' d' d''')) = True.
Proof. exact (TRANS (@lem1252866 d' d'' m q d''') (@lem1252870 d' d'' m q d''')). Qed.
Lemma lem1252872 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : True = ((term3 m q d' d'' d''') = (term17 q m d'' d' d''')).
Proof. exact (SYM (@lem1252871 q m d'' d' d''')). Qed.
Lemma lem1252873 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term3 m q d' d'' d''') = (term17 q m d'' d' d''').
Proof. exact (EQ_MP (@lem1252872 q m d'' d' d''') (@lem0)). Qed.
Lemma lem1252874 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1252875 (q : nat) (m : nat) (d'' : nat) : (term1 m q d'') = (term1 q m d'').
Proof. exact (MK_COMB (@lem1252874) (@lem1252593 q m d'')). Qed.
Lemma lem1252876 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 m q d'') = (term3 m q d' d'' d''')) = ((term0 q m d'') = (term17 q m d'' d' d''')).
Proof. exact (MK_COMB (@lem1252875 q m d'') (@lem1252873 q m d'' d' d''')). Qed.
Lemma lem1252877 (m : nat) : term28 m.
Proof. exact (@lem272789 m). Qed.
Lemma lem1252878 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1252879 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1252878 m) (@lem1252877 m)). Qed.
Lemma lem1252880 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1252879 m n). Qed.
Lemma lem1252881 (m : nat) (n : nat) : (term30 m n) = ((m = (Nat.add m n)) = (n = (NUMERAL 0))).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1252889 (m : nat) : term31 m.
Proof. exact (@lem79639 m). Qed.
Lemma lem1252890 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem1252891 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem1252890 m) (@lem1252889 m)). Qed.
Lemma lem1252892 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem1252891 m n). Qed.
Lemma lem1252893 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem1252894 (m : nat) (n : nat) : term34 m n.
Proof. exact (EQ_MP (@lem1252893 m n) (@lem1252892 m n)). Qed.
Lemma lem1252895 (m : nat) (n : nat) (p : nat) : term35 m n p.
Proof. exact (@lem1252894 m n p). Qed.
Lemma lem1252896 (m : nat) (n : nat) (p : nat) : (term35 m n p) = (((Nat.add m n) = (Nat.add m p)) = (n = p)).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem1252899 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1252896 m n p) (@lem1252895 m n p)). Qed.
Lemma lem1252900 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 q m d'') = (term17 q m d'' d' d''')) = ((Nat.add m d'') = (term19 m d'' d' d''')).
Proof. exact (@lem1252899 q (Nat.add m d'') (term19 m d'' d' d''')). Qed.
Lemma lem1252902 (m : nat) (n : nat) (p : nat) : ((Nat.add m n) = (Nat.add m p)) = (n = p).
Proof. exact (EQ_MP (@lem1252896 m n p) (@lem1252895 m n p)). Qed.
Lemma lem1252903 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m d'') = (term19 m d'' d' d''')) = (d'' = (term18 d'' d' d''')).
Proof. exact (@lem1252902 m d'' (term18 d'' d' d''')). Qed.
Lemma lem1252905 (m : nat) (n : nat) : (m = (Nat.add m n)) = (n = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1252881 m n) (@lem1252880 m n)). Qed.
Lemma lem1252910 (d'' : nat) (d' : nat) (d''' : nat) : (d'' = (term18 d'' d' d''')) = ((term20 d' d''') = (NUMERAL 0)).
Proof. exact (@lem1252905 d'' (term20 d' d''')). Qed.
Lemma lem1252911 (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((Nat.add m d'') = (term19 m d'' d' d''')) = ((term20 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1252903 m d'' d' d''') (@lem1252910 d'' d' d''')). Qed.
Lemma lem1252912 (q : nat) (m : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 q m d'') = (term17 q m d'' d' d''')) = ((term20 d' d''') = (NUMERAL 0)).
Proof. exact (TRANS (@lem1252900 q m d'' d' d''') (@lem1252911 m d'' d' d''')). Qed.
Lemma lem1252913 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term36 m q d' d'' d''') = (term36 m q d' d'' d''').
Proof. exact (eq_refl (term36 m q d' d'' d''')). Qed.
Lemma lem1252914 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (((term0 m q d'') = (term3 m q d' d'' d''')) = ((term0 q m d'') = (term17 q m d'' d' d'''))) = (((term0 m q d'') = (term3 m q d' d'' d''')) = ((term20 d' d''') = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem1252913 m q d' d'' d''') (@lem1252912 q m d'' d' d''')). Qed.
Lemma lem1252915 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : ((term0 m q d'') = (term3 m q d' d'' d''')) = ((term20 d' d''') = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem1252914 m q d'' d' d''') (@lem1252876 q m d'' d' d''')). Qed.
Lemma lem1252916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1252917 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term37 m q d' d'' d''') = (term38 d' d''').
Proof. exact (MK_COMB (@lem1252916) (@lem1252915 m q d'' d' d''')). Qed.
Lemma lem1252918 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem1252919 (m : nat) (q : nat) (d'' : nat) (d' : nat) (d''' : nat) : (term39 m q d' d'' d''') = (term40 d' d''').
Proof. exact (MK_COMB (@lem1252917 m q d'' d' d''') (@lem1252918)). Qed.
Lemma lem1252920 (m : nat) (q : nat) (d' : nat) (d'' : nat) (d''' : nat) : (term40 d' d''') = (term39 m q d' d'' d''').
Proof. exact (SYM (@lem1252919 m q d'' d' d''')). Qed.
