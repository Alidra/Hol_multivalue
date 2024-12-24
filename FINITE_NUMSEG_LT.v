Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_NUMSEG_LT_term_abbrevs.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_NUMSEG_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem4621453 {_100044 : Type'} (s : _100044 -> Prop) : term0 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4621454 {_100044 : Type'} (s : _100044 -> Prop) : (term0 _100044 s) = (term1 _100044 s).
Proof. exact (eq_refl (term0 _100044 s)). Qed.
Lemma lem4621455 {_100044 : Type'} (s : _100044 -> Prop) : term1 _100044 s.
Proof. exact (EQ_MP (@lem4621454 _100044 s) (@lem4621453 _100044 s)). Qed.
Lemma lem4621456 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term2 _100044 s n.
Proof. exact (@lem4621455 _100044 s n). Qed.
Lemma lem4621457 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term2 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term3 _100044 s n)).
Proof. exact (eq_refl (term2 _100044 s n)). Qed.
Lemma lem4621464 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term3 _100044 s n).
Proof. exact (EQ_MP (@lem4621457 _100044 s n) (@lem4621456 _100044 s n)). Qed.
Lemma lem4621465 (s : nat -> Prop) (n : nat) : (@HAS_SIZE nat s n) = (term4 s n).
Proof. exact (@lem4621464 nat s n). Qed.
Lemma lem4621466 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem4621465 (term7 n) n). Qed.
Lemma lem4621479 : term8 = term9.
Proof. exact (fun_ext (fun n : nat => @lem4621466 n)). Qed.
Lemma lem4621480 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621481 : term10 = term11.
Proof. exact (MK_COMB (@lem4621480) (@lem4621479)). Qed.
Lemma lem4621486 : term11.
Proof. exact (EQ_MP (@lem4621481) (@lem4621384)). Qed.
Lemma lem4621487 (n : nat) : term12 n.
Proof. exact (@lem4621486 n). Qed.
Lemma lem4621488 (n : nat) : (term12 n) = (term6 n).
Proof. exact (eq_refl (term12 n)). Qed.
Lemma lem4621489 (n : nat) : term6 n.
Proof. exact (EQ_MP (@lem4621488 n) (@lem4621487 n)). Qed.
Lemma lem4621491 (n : nat) : term13 n.
Proof. exact (proj1 (@lem4621489 n)). Qed.
Lemma lem4621492 (n : nat) : (term13 n) = ((term13 n) = True).
Proof. exact (@lem7 (term13 n)). Qed.
Lemma lem4621499 (n : nat) : (term13 n) = True.
Proof. exact (EQ_MP (@lem4621492 n) (@lem4621491 n)). Qed.
Lemma lem4621500 : term14 = term15.
Proof. exact (fun_ext (fun n : nat => @lem4621499 n)). Qed.
Lemma lem4621501 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem4621502 : term16 = term17.
Proof. exact (MK_COMB (@lem4621501) (@lem4621500)). Qed.
Lemma lem4621504 {A : Type'} (t : Prop) : (term18 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4621505 (t : Prop) : (term19 t) = t.
Proof. exact (@lem4621504 nat t). Qed.
Lemma lem4621506 : term17 = True.
Proof. exact (@lem4621505 True). Qed.
Lemma lem4621507 : term16 = True.
Proof. exact (TRANS (@lem4621502) (@lem4621506)). Qed.
Lemma lem4621508 : True = term16.
Proof. exact (SYM (@lem4621507)). Qed.
Lemma lem4621509 : term16.
Proof. exact (EQ_MP (@lem4621508) (@lem0)). Qed.
