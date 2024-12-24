Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_GT_term_abbrevs.
Require Import GT_spec.
Require Import REAL_OF_NUM_LT_spec.
Require Import real_gt_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1483731 (m : nat) : term0 m.
Proof. exact (@lem1483667 m). Qed.
Lemma lem1483732 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1483733 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1483732 m) (@lem1483731 m)). Qed.
Lemma lem1483734 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1483733 m n). Qed.
Lemma lem1483735 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1483737 (y : real) : term4 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem1483738 (y : real) : (term4 y) = (term5 y).
Proof. exact (eq_refl (term4 y)). Qed.
Lemma lem1483739 (y : real) : term5 y.
Proof. exact (EQ_MP (@lem1483738 y) (@lem1483737 y)). Qed.
Lemma lem1483740 (y : real) (x : real) : term6 y x.
Proof. exact (@lem1483739 y x). Qed.
Lemma lem1483741 (y : real) (x : real) : (term6 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term6 y x)). Qed.
Lemma lem1483743 (n : nat) : term7 n.
Proof. exact (@lem90463 n). Qed.
Lemma lem1483744 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1483745 (n : nat) : term8 n.
Proof. exact (EQ_MP (@lem1483744 n) (@lem1483743 n)). Qed.
Lemma lem1483746 (n : nat) (m : nat) : term9 n m.
Proof. exact (@lem1483745 n m). Qed.
Lemma lem1483747 (n : nat) (m : nat) : (term9 n m) = ((Peano.gt m n) = (Peano.lt n m)).
Proof. exact (eq_refl (term9 n m)). Qed.
Lemma lem1483760 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1483741 y x) (@lem1483740 y x)). Qed.
Lemma lem1483761 (n : nat) (m : nat) : (term10 m n) = (term3 n m).
Proof. exact (@lem1483760 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1483763 (m : nat) (n : nat) : (term3 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1483735 m n) (@lem1483734 m n)). Qed.
Lemma lem1483764 (n : nat) (m : nat) : (term3 n m) = (Peano.lt n m).
Proof. exact (@lem1483763 n m). Qed.
Lemma lem1483765 (n : nat) (m : nat) : (term10 m n) = (Peano.lt n m).
Proof. exact (TRANS (@lem1483761 n m) (@lem1483764 n m)). Qed.
Lemma lem1483766 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483767 (n : nat) (m : nat) : (term11 m n) = (term12 n m).
Proof. exact (MK_COMB (@lem1483766) (@lem1483765 n m)). Qed.
Lemma lem1483769 (n : nat) (m : nat) : (Peano.gt m n) = (Peano.lt n m).
Proof. exact (EQ_MP (@lem1483747 n m) (@lem1483746 n m)). Qed.
Lemma lem1483770 (n : nat) (m : nat) : ((term10 m n) = (Peano.gt m n)) = ((Peano.lt n m) = (Peano.lt n m)).
Proof. exact (MK_COMB (@lem1483767 n m) (@lem1483769 n m)). Qed.
Lemma lem1483772 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483773 (x : Prop) : (x = x) = True.
Proof. exact (@lem1483772 Prop x). Qed.
Lemma lem1483774 (n : nat) (m : nat) : ((Peano.lt n m) = (Peano.lt n m)) = True.
Proof. exact (@lem1483773 (Peano.lt n m)). Qed.
Lemma lem1483775 (m : nat) (n : nat) : ((term10 m n) = (Peano.gt m n)) = True.
Proof. exact (TRANS (@lem1483770 n m) (@lem1483774 n m)). Qed.
Lemma lem1483776 (m : nat) : (term13 m) = term14.
Proof. exact (fun_ext (fun n : nat => @lem1483775 m n)). Qed.
Lemma lem1483777 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483778 (m : nat) : (term15 m) = term16.
Proof. exact (MK_COMB (@lem1483777) (@lem1483776 m)). Qed.
Lemma lem1483780 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483781 (t : Prop) : (term18 t) = t.
Proof. exact (@lem1483780 nat t). Qed.
Lemma lem1483782 : term16 = True.
Proof. exact (@lem1483781 True). Qed.
Lemma lem1483783 (m : nat) : (term15 m) = True.
Proof. exact (TRANS (@lem1483778 m) (@lem1483782)). Qed.
Lemma lem1483784 : term19 = term14.
Proof. exact (fun_ext (fun m : nat => @lem1483783 m)). Qed.
Lemma lem1483785 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483786 : term20 = term16.
Proof. exact (MK_COMB (@lem1483785) (@lem1483784)). Qed.
Lemma lem1483788 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483789 (t : Prop) : (term18 t) = t.
Proof. exact (@lem1483788 nat t). Qed.
Lemma lem1483790 : term16 = True.
Proof. exact (@lem1483789 True). Qed.
Lemma lem1483791 : term20 = True.
Proof. exact (TRANS (@lem1483786) (@lem1483790)). Qed.
Lemma lem1483792 : True = term20.
Proof. exact (SYM (@lem1483791)). Qed.
Lemma lem1483793 : term20.
Proof. exact (EQ_MP (@lem1483792) (@lem0)). Qed.
