Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_OF_NUM_GE_term_abbrevs.
Require Import GE_spec.
Require Import real_ge_spec.
Require Import thm0_spec.
Require Import thm1340282_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1483668 (m : nat) : term0 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1483669 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem1483670 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem1483669 m) (@lem1483668 m)). Qed.
Lemma lem1483671 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem1483670 m n). Qed.
Lemma lem1483672 (m : nat) (n : nat) : (term2 m n) = ((term3 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem1483674 (y : real) : term4 y.
Proof. exact (@lem1342163 y). Qed.
Lemma lem1483675 (y : real) : (term4 y) = (term5 y).
Proof. exact (eq_refl (term4 y)). Qed.
Lemma lem1483676 (y : real) : term5 y.
Proof. exact (EQ_MP (@lem1483675 y) (@lem1483674 y)). Qed.
Lemma lem1483677 (y : real) (x : real) : term6 y x.
Proof. exact (@lem1483676 y x). Qed.
Lemma lem1483678 (y : real) (x : real) : (term6 y x) = ((real_ge x y) = (real_le y x)).
Proof. exact (eq_refl (term6 y x)). Qed.
Lemma lem1483680 (n : nat) : term7 n.
Proof. exact (@lem90226 n). Qed.
Lemma lem1483681 (n : nat) : (term7 n) = (term8 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem1483682 (n : nat) : term8 n.
Proof. exact (EQ_MP (@lem1483681 n) (@lem1483680 n)). Qed.
Lemma lem1483683 (n : nat) (m : nat) : term9 n m.
Proof. exact (@lem1483682 n m). Qed.
Lemma lem1483684 (n : nat) (m : nat) : (term9 n m) = ((Peano.ge m n) = (Peano.le n m)).
Proof. exact (eq_refl (term9 n m)). Qed.
Lemma lem1483697 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1483678 y x) (@lem1483677 y x)). Qed.
Lemma lem1483698 (n : nat) (m : nat) : (term10 m n) = (term3 n m).
Proof. exact (@lem1483697 (real_of_num n) (real_of_num m)). Qed.
Lemma lem1483700 (m : nat) (n : nat) : (term3 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1483672 m n) (@lem1483671 m n)). Qed.
Lemma lem1483701 (n : nat) (m : nat) : (term3 n m) = (Peano.le n m).
Proof. exact (@lem1483700 n m). Qed.
Lemma lem1483702 (n : nat) (m : nat) : (term10 m n) = (Peano.le n m).
Proof. exact (TRANS (@lem1483698 n m) (@lem1483701 n m)). Qed.
Lemma lem1483703 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1483704 (n : nat) (m : nat) : (term11 m n) = (term12 n m).
Proof. exact (MK_COMB (@lem1483703) (@lem1483702 n m)). Qed.
Lemma lem1483706 (n : nat) (m : nat) : (Peano.ge m n) = (Peano.le n m).
Proof. exact (EQ_MP (@lem1483684 n m) (@lem1483683 n m)). Qed.
Lemma lem1483707 (n : nat) (m : nat) : ((term10 m n) = (Peano.ge m n)) = ((Peano.le n m) = (Peano.le n m)).
Proof. exact (MK_COMB (@lem1483704 n m) (@lem1483706 n m)). Qed.
Lemma lem1483709 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1483710 (x : Prop) : (x = x) = True.
Proof. exact (@lem1483709 Prop x). Qed.
Lemma lem1483711 (n : nat) (m : nat) : ((Peano.le n m) = (Peano.le n m)) = True.
Proof. exact (@lem1483710 (Peano.le n m)). Qed.
Lemma lem1483712 (m : nat) (n : nat) : ((term10 m n) = (Peano.ge m n)) = True.
Proof. exact (TRANS (@lem1483707 n m) (@lem1483711 n m)). Qed.
Lemma lem1483713 (m : nat) : (term13 m) = term14.
Proof. exact (fun_ext (fun n : nat => @lem1483712 m n)). Qed.
Lemma lem1483714 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483715 (m : nat) : (term15 m) = term16.
Proof. exact (MK_COMB (@lem1483714) (@lem1483713 m)). Qed.
Lemma lem1483717 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483718 (t : Prop) : (term18 t) = t.
Proof. exact (@lem1483717 nat t). Qed.
Lemma lem1483719 : term16 = True.
Proof. exact (@lem1483718 True). Qed.
Lemma lem1483720 (m : nat) : (term15 m) = True.
Proof. exact (TRANS (@lem1483715 m) (@lem1483719)). Qed.
Lemma lem1483721 : term19 = term14.
Proof. exact (fun_ext (fun m : nat => @lem1483720 m)). Qed.
Lemma lem1483722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1483723 : term20 = term16.
Proof. exact (MK_COMB (@lem1483722) (@lem1483721)). Qed.
Lemma lem1483725 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1483726 (t : Prop) : (term18 t) = t.
Proof. exact (@lem1483725 nat t). Qed.
Lemma lem1483727 : term16 = True.
Proof. exact (@lem1483726 True). Qed.
Lemma lem1483728 : term20 = True.
Proof. exact (TRANS (@lem1483723) (@lem1483727)). Qed.
Lemma lem1483729 : True = term20.
Proof. exact (SYM (@lem1483728)). Qed.
Lemma lem1483730 : term20.
Proof. exact (EQ_MP (@lem1483729) (@lem0)). Qed.
