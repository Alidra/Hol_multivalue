Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_DIV_term_abbrevs.
Require Import REAL_POW_INV_spec.
Require Import REAL_POW_MUL_spec.
Require Import real_div_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1595723 (x : real) : term0 x.
Proof. exact (@lem1595679 x). Qed.
Lemma lem1595724 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1595725 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1595724 x) (@lem1595723 x)). Qed.
Lemma lem1595726 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem1595725 x n). Qed.
Lemma lem1595727 (x : real) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem1595729 (x : real) : term5 x.
Proof. exact (@lem1595570 x). Qed.
Lemma lem1595730 (x : real) : (term5 x) = (term6 x).
Proof. exact (eq_refl (term5 x)). Qed.
Lemma lem1595731 (x : real) : term6 x.
Proof. exact (EQ_MP (@lem1595730 x) (@lem1595729 x)). Qed.
Lemma lem1595732 (x : real) (y : real) : term7 x y.
Proof. exact (@lem1595731 x y). Qed.
Lemma lem1595733 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (eq_refl (term7 x y)). Qed.
Lemma lem1595734 (x : real) (y : real) : term8 x y.
Proof. exact (EQ_MP (@lem1595733 x y) (@lem1595732 x y)). Qed.
Lemma lem1595735 (x : real) (y : real) (n : nat) : term9 x y n.
Proof. exact (@lem1595734 x y n). Qed.
Lemma lem1595736 (x : real) (y : real) (n : nat) : (term9 x y n) = ((term10 x y n) = (term11 x y n)).
Proof. exact (eq_refl (term9 x y n)). Qed.
Lemma lem1595738 (x : real) : term12 x.
Proof. exact (@lem1344936 x). Qed.
Lemma lem1595739 (x : real) : (term12 x) = (term13 x).
Proof. exact (eq_refl (term12 x)). Qed.
Lemma lem1595740 (x : real) : term13 x.
Proof. exact (EQ_MP (@lem1595739 x) (@lem1595738 x)). Qed.
Lemma lem1595741 (x : real) (y : real) : term14 x y.
Proof. exact (@lem1595740 x y). Qed.
Lemma lem1595742 (x : real) (y : real) : (term14 x y) = ((real_div x y) = (term15 x y)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1595759 (x : real) (y : real) : (real_div x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1595742 x y) (@lem1595741 x y)). Qed.
Lemma lem1595760 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1595761 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1595760) (@lem1595759 x y)). Qed.
Lemma lem1595762 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1595763 (x : real) (y : real) (n : nat) : (term18 x y n) = (term19 x y n).
Proof. exact (MK_COMB (@lem1595761 x y) (@lem1595762 n)). Qed.
Lemma lem1595765 (x : real) (y : real) (n : nat) : (term10 x y n) = (term11 x y n).
Proof. exact (EQ_MP (@lem1595736 x y n) (@lem1595735 x y n)). Qed.
Lemma lem1595766 (x : real) (y : real) (n : nat) : (term19 x y n) = (term20 x y n).
Proof. exact (@lem1595765 x (real_inv y) n). Qed.
Lemma lem1595768 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem1595727 x n) (@lem1595726 x n)). Qed.
Lemma lem1595769 (y : real) (n : nat) : (term3 y n) = (term4 y n).
Proof. exact (@lem1595768 y n). Qed.
Lemma lem1595770 (x : real) (n : nat) : (term21 x n) = (term21 x n).
Proof. exact (eq_refl (term21 x n)). Qed.
Lemma lem1595771 (x : real) (y : real) (n : nat) : (term20 x y n) = (term22 x y n).
Proof. exact (MK_COMB (@lem1595770 x n) (@lem1595769 y n)). Qed.
Lemma lem1595772 (x : real) (y : real) (n : nat) : (term19 x y n) = (term22 x y n).
Proof. exact (TRANS (@lem1595766 x y n) (@lem1595771 x y n)). Qed.
Lemma lem1595773 (x : real) (y : real) (n : nat) : (term18 x y n) = (term22 x y n).
Proof. exact (TRANS (@lem1595763 x y n) (@lem1595772 x y n)). Qed.
Lemma lem1595774 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1595775 (x : real) (y : real) (n : nat) : (term23 x y n) = (term24 x y n).
Proof. exact (MK_COMB (@lem1595774) (@lem1595773 x y n)). Qed.
Lemma lem1595777 (x : real) (y : real) : (real_div x y) = (term15 x y).
Proof. exact (EQ_MP (@lem1595742 x y) (@lem1595741 x y)). Qed.
Lemma lem1595778 (x : real) (y : real) (n : nat) : (term25 x y n) = (term22 x y n).
Proof. exact (@lem1595777 (real_pow x n) (real_pow y n)). Qed.
Lemma lem1595779 (x : real) (y : real) (n : nat) : ((term18 x y n) = (term25 x y n)) = ((term22 x y n) = (term22 x y n)).
Proof. exact (MK_COMB (@lem1595775 x y n) (@lem1595778 x y n)). Qed.
Lemma lem1595781 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595782 (x : real) : (x = x) = True.
Proof. exact (@lem1595781 real x). Qed.
Lemma lem1595783 (x : real) (y : real) (n : nat) : ((term22 x y n) = (term22 x y n)) = True.
Proof. exact (@lem1595782 (term22 x y n)). Qed.
Lemma lem1595784 (x : real) (y : real) (n : nat) : ((term18 x y n) = (term25 x y n)) = True.
Proof. exact (TRANS (@lem1595779 x y n) (@lem1595783 x y n)). Qed.
Lemma lem1595785 (x : real) (y : real) : (term26 x y) = term27.
Proof. exact (fun_ext (fun n : nat => @lem1595784 x y n)). Qed.
Lemma lem1595786 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595787 (x : real) (y : real) : (term28 x y) = term29.
Proof. exact (MK_COMB (@lem1595786) (@lem1595785 x y)). Qed.
Lemma lem1595789 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595790 (t : Prop) : (term31 t) = t.
Proof. exact (@lem1595789 nat t). Qed.
Lemma lem1595791 : term29 = True.
Proof. exact (@lem1595790 True). Qed.
Lemma lem1595792 (x : real) (y : real) : (term28 x y) = True.
Proof. exact (TRANS (@lem1595787 x y) (@lem1595791)). Qed.
Lemma lem1595793 (x : real) : (term32 x) = term33.
Proof. exact (fun_ext (fun y : real => @lem1595792 x y)). Qed.
Lemma lem1595794 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1595795 (x : real) : (term34 x) = term35.
Proof. exact (MK_COMB (@lem1595794) (@lem1595793 x)). Qed.
Lemma lem1595797 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595798 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1595797 real t). Qed.
Lemma lem1595799 : term35 = True.
Proof. exact (@lem1595798 True). Qed.
Lemma lem1595800 (x : real) : (term34 x) = True.
Proof. exact (TRANS (@lem1595795 x) (@lem1595799)). Qed.
Lemma lem1595801 : term37 = term33.
Proof. exact (fun_ext (fun x : real => @lem1595800 x)). Qed.
Lemma lem1595802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1595803 : term38 = term35.
Proof. exact (MK_COMB (@lem1595802) (@lem1595801)). Qed.
Lemma lem1595805 {A : Type'} (t : Prop) : (term30 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595806 (t : Prop) : (term36 t) = t.
Proof. exact (@lem1595805 real t). Qed.
Lemma lem1595807 : term35 = True.
Proof. exact (@lem1595806 True). Qed.
Lemma lem1595808 : term38 = True.
Proof. exact (TRANS (@lem1595803) (@lem1595807)). Qed.
Lemma lem1595809 : True = term38.
Proof. exact (SYM (@lem1595808)). Qed.
Lemma lem1595810 : term38.
Proof. exact (EQ_MP (@lem1595809) (@lem0)). Qed.
