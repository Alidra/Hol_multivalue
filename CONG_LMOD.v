Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONG_LMOD_term_abbrevs.
Require Import CONG_spec.
Require Import MOD_MOD_REFL_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem3070638 (m : nat) : term0 m.
Proof. exact (@lem183010 m). Qed.
Lemma lem3070639 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem3070640 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem3070639 m) (@lem3070638 m)). Qed.
Lemma lem3070641 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem3070640 m n). Qed.
Lemma lem3070642 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Nat.modulo m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem3070644 (x : nat) : term4 x.
Proof. exact (@lem3070637 x). Qed.
Lemma lem3070645 (x : nat) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem3070646 (x : nat) : term5 x.
Proof. exact (EQ_MP (@lem3070645 x) (@lem3070644 x)). Qed.
Lemma lem3070647 (x : nat) (y : nat) : term6 x y.
Proof. exact (@lem3070646 x y). Qed.
Lemma lem3070648 (x : nat) (y : nat) : (term6 x y) = (term7 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem3070649 (x : nat) (y : nat) : term7 x y.
Proof. exact (EQ_MP (@lem3070648 x y) (@lem3070647 x y)). Qed.
Lemma lem3070650 (x : nat) (y : nat) (n : nat) : term8 x y n.
Proof. exact (@lem3070649 x y n). Qed.
Lemma lem3070651 (x : nat) (y : nat) (n : nat) : (term8 x y n) = ((term9 x y n) = ((Nat.modulo x n) = (Nat.modulo y n))).
Proof. exact (eq_refl (term8 x y n)). Qed.
Lemma lem3070668 (x : nat) (y : nat) (n : nat) : (term9 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (EQ_MP (@lem3070651 x y n) (@lem3070650 x y n)). Qed.
Lemma lem3070669 (x : nat) (y : nat) (n : nat) : (term10 x y n) = ((term3 x n) = (Nat.modulo y n)).
Proof. exact (@lem3070668 (Nat.modulo x n) y n). Qed.
Lemma lem3070673 (m : nat) (n : nat) : (term3 m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem3070642 m n) (@lem3070641 m n)). Qed.
Lemma lem3070674 (x : nat) (n : nat) : (term3 x n) = (Nat.modulo x n).
Proof. exact (@lem3070673 x n). Qed.
Lemma lem3070675 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem3070676 (x : nat) (n : nat) : (term11 x n) = (term12 x n).
Proof. exact (MK_COMB (@lem3070675) (@lem3070674 x n)). Qed.
Lemma lem3070677 (y : nat) (n : nat) : (Nat.modulo y n) = (Nat.modulo y n).
Proof. exact (eq_refl (Nat.modulo y n)). Qed.
Lemma lem3070678 (x : nat) (y : nat) (n : nat) : ((term3 x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (MK_COMB (@lem3070676 x n) (@lem3070677 y n)). Qed.
Lemma lem3070681 (x : nat) (y : nat) (n : nat) : (term10 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (TRANS (@lem3070669 x y n) (@lem3070678 x y n)). Qed.
Lemma lem3070682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3070683 (x : nat) (y : nat) (n : nat) : (term13 x y n) = (term14 x y n).
Proof. exact (MK_COMB (@lem3070682) (@lem3070681 x y n)). Qed.
Lemma lem3070685 (x : nat) (y : nat) (n : nat) : (term9 x y n) = ((Nat.modulo x n) = (Nat.modulo y n)).
Proof. exact (EQ_MP (@lem3070651 x y n) (@lem3070650 x y n)). Qed.
Lemma lem3070688 (x : nat) (y : nat) (n : nat) : ((term10 x y n) = (term9 x y n)) = (((Nat.modulo x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n))).
Proof. exact (MK_COMB (@lem3070683 x y n) (@lem3070685 x y n)). Qed.
Lemma lem3070690 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem3070691 (x : Prop) : (x = x) = True.
Proof. exact (@lem3070690 Prop x). Qed.
Lemma lem3070692 (x : nat) (y : nat) (n : nat) : (((Nat.modulo x n) = (Nat.modulo y n)) = ((Nat.modulo x n) = (Nat.modulo y n))) = True.
Proof. exact (@lem3070691 ((Nat.modulo x n) = (Nat.modulo y n))). Qed.
Lemma lem3070693 (x : nat) (y : nat) (n : nat) : ((term10 x y n) = (term9 x y n)) = True.
Proof. exact (TRANS (@lem3070688 x y n) (@lem3070692 x y n)). Qed.
Lemma lem3070694 (x : nat) (y : nat) : (term15 x y) = term16.
Proof. exact (fun_ext (fun n : nat => @lem3070693 x y n)). Qed.
Lemma lem3070695 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070696 (x : nat) (y : nat) : (term17 x y) = term18.
Proof. exact (MK_COMB (@lem3070695) (@lem3070694 x y)). Qed.
Lemma lem3070698 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070699 (t : Prop) : (term20 t) = t.
Proof. exact (@lem3070698 nat t). Qed.
Lemma lem3070700 : term18 = True.
Proof. exact (@lem3070699 True). Qed.
Lemma lem3070701 (x : nat) (y : nat) : (term17 x y) = True.
Proof. exact (TRANS (@lem3070696 x y) (@lem3070700)). Qed.
Lemma lem3070702 (x : nat) : (term21 x) = term16.
Proof. exact (fun_ext (fun y : nat => @lem3070701 x y)). Qed.
Lemma lem3070703 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070704 (x : nat) : (term22 x) = term18.
Proof. exact (MK_COMB (@lem3070703) (@lem3070702 x)). Qed.
Lemma lem3070706 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070707 (t : Prop) : (term20 t) = t.
Proof. exact (@lem3070706 nat t). Qed.
Lemma lem3070708 : term18 = True.
Proof. exact (@lem3070707 True). Qed.
Lemma lem3070709 (x : nat) : (term22 x) = True.
Proof. exact (TRANS (@lem3070704 x) (@lem3070708)). Qed.
Lemma lem3070710 : term23 = term16.
Proof. exact (fun_ext (fun x : nat => @lem3070709 x)). Qed.
Lemma lem3070711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3070712 : term24 = term18.
Proof. exact (MK_COMB (@lem3070711) (@lem3070710)). Qed.
Lemma lem3070714 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem3070715 (t : Prop) : (term20 t) = t.
Proof. exact (@lem3070714 nat t). Qed.
Lemma lem3070716 : term18 = True.
Proof. exact (@lem3070715 True). Qed.
Lemma lem3070717 : term24 = True.
Proof. exact (TRANS (@lem3070712) (@lem3070716)). Qed.
Lemma lem3070718 : True = term24.
Proof. exact (SYM (@lem3070717)). Qed.
Lemma lem3070719 : term24.
Proof. exact (EQ_MP (@lem3070718) (@lem0)). Qed.
