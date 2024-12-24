Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_POW_term_abbrevs.
Require Import REAL_POW_INV_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1595680 (x : real) : term0 x.
Proof. exact (@lem1595679 x). Qed.
Lemma lem1595681 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1595682 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1595681 x) (@lem1595680 x)). Qed.
Lemma lem1595683 (x : real) (n : nat) : term2 x n.
Proof. exact (@lem1595682 x n). Qed.
Lemma lem1595684 (x : real) (n : nat) : (term2 x n) = ((term3 x n) = (term4 x n)).
Proof. exact (eq_refl (term2 x n)). Qed.
Lemma lem1595697 (x : real) (n : nat) : (term3 x n) = (term4 x n).
Proof. exact (EQ_MP (@lem1595684 x n) (@lem1595683 x n)). Qed.
Lemma lem1595698 (x : real) (n : nat) : (term5 x n) = (term5 x n).
Proof. exact (eq_refl (term5 x n)). Qed.
Lemma lem1595699 (x : real) (n : nat) : ((term4 x n) = (term3 x n)) = ((term4 x n) = (term4 x n)).
Proof. exact (MK_COMB (@lem1595698 x n) (@lem1595697 x n)). Qed.
Lemma lem1595701 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1595702 (x : real) : (x = x) = True.
Proof. exact (@lem1595701 real x). Qed.
Lemma lem1595703 (x : real) (n : nat) : ((term4 x n) = (term4 x n)) = True.
Proof. exact (@lem1595702 (term4 x n)). Qed.
Lemma lem1595704 (x : real) (n : nat) : ((term4 x n) = (term3 x n)) = True.
Proof. exact (TRANS (@lem1595699 x n) (@lem1595703 x n)). Qed.
Lemma lem1595705 (x : real) : (term6 x) = term7.
Proof. exact (fun_ext (fun n : nat => @lem1595704 x n)). Qed.
Lemma lem1595706 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1595707 (x : real) : (term8 x) = term9.
Proof. exact (MK_COMB (@lem1595706) (@lem1595705 x)). Qed.
Lemma lem1595709 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595710 (t : Prop) : (term11 t) = t.
Proof. exact (@lem1595709 nat t). Qed.
Lemma lem1595711 : term9 = True.
Proof. exact (@lem1595710 True). Qed.
Lemma lem1595712 (x : real) : (term8 x) = True.
Proof. exact (TRANS (@lem1595707 x) (@lem1595711)). Qed.
Lemma lem1595713 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1595712 x)). Qed.
Lemma lem1595714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1595715 : term14 = term15.
Proof. exact (MK_COMB (@lem1595714) (@lem1595713)). Qed.
Lemma lem1595717 {A : Type'} (t : Prop) : (term10 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1595718 (t : Prop) : (term16 t) = t.
Proof. exact (@lem1595717 real t). Qed.
Lemma lem1595719 : term15 = True.
Proof. exact (@lem1595718 True). Qed.
Lemma lem1595720 : term14 = True.
Proof. exact (TRANS (@lem1595715) (@lem1595719)). Qed.
Lemma lem1595721 : True = term14.
Proof. exact (SYM (@lem1595720)). Qed.
Lemma lem1595722 : term14.
Proof. exact (EQ_MP (@lem1595721) (@lem0)). Qed.
