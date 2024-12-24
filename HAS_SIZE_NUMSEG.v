Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import HAS_SIZE_NUMSEG_term_abbrevs.
Require Import CARD_NUMSEG_spec.
Require Import FINITE_NUMSEG_spec.
Require Import HAS_SIZE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem5393503 (m : nat) : term0 m.
Proof. exact (@lem5393502 m). Qed.
Lemma lem5393504 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5393505 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5393504 m) (@lem5393503 m)). Qed.
Lemma lem5393506 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5393505 m n). Qed.
Lemma lem5393507 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term4 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5393509 (m : nat) : term5 m.
Proof. exact (@lem5329299 m). Qed.
Lemma lem5393510 (m : nat) : (term5 m) = (term6 m).
Proof. exact (eq_refl (term5 m)). Qed.
Lemma lem5393511 (m : nat) : term6 m.
Proof. exact (EQ_MP (@lem5393510 m) (@lem5393509 m)). Qed.
Lemma lem5393512 (m : nat) (n : nat) : term7 m n.
Proof. exact (@lem5393511 m n). Qed.
Lemma lem5393513 (m : nat) (n : nat) : (term7 m n) = (term8 m n).
Proof. exact (eq_refl (term7 m n)). Qed.
Lemma lem5393514 (m : nat) (n : nat) : term8 m n.
Proof. exact (EQ_MP (@lem5393513 m n) (@lem5393512 m n)). Qed.
Lemma lem5393515 (m : nat) (n : nat) : (term8 m n) = ((term8 m n) = True).
Proof. exact (@lem7 (term8 m n)). Qed.
Lemma lem5393517 {_100044 : Type'} (s : _100044 -> Prop) : term9 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem5393518 {_100044 : Type'} (s : _100044 -> Prop) : (term9 _100044 s) = (term10 _100044 s).
Proof. exact (eq_refl (term9 _100044 s)). Qed.
Lemma lem5393519 {_100044 : Type'} (s : _100044 -> Prop) : term10 _100044 s.
Proof. exact (EQ_MP (@lem5393518 _100044 s) (@lem5393517 _100044 s)). Qed.
Lemma lem5393520 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term11 _100044 s n.
Proof. exact (@lem5393519 _100044 s n). Qed.
Lemma lem5393521 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term11 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term12 _100044 s n)).
Proof. exact (eq_refl (term11 _100044 s n)). Qed.
Lemma lem5393532 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term12 _100044 s n).
Proof. exact (EQ_MP (@lem5393521 _100044 s n) (@lem5393520 _100044 s n)). Qed.
Lemma lem5393533 (s : nat -> Prop) (n : nat) : (@HAS_SIZE nat s n) = (term13 s n).
Proof. exact (@lem5393532 nat s n). Qed.
Lemma lem5393534 (n : nat) (m : nat) : (term14 n m) = (term15 n m).
Proof. exact (@lem5393533 (dotdot m n) (term4 n m)). Qed.
Lemma lem5393538 (m : nat) (n : nat) : (term8 m n) = True.
Proof. exact (EQ_MP (@lem5393515 m n) (@lem5393514 m n)). Qed.
Lemma lem5393539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5393540 (m : nat) (n : nat) : (term16 m n) = (and True).
Proof. exact (MK_COMB (@lem5393539) (@lem5393538 m n)). Qed.
Lemma lem5393544 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (EQ_MP (@lem5393507 n m) (@lem5393506 m n)). Qed.
Lemma lem5393545 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5393546 (n : nat) (m : nat) : (term17 m n) = (term18 n m).
Proof. exact (MK_COMB (@lem5393545) (@lem5393544 n m)). Qed.
Lemma lem5393547 (n : nat) (m : nat) : (term4 n m) = (term4 n m).
Proof. exact (eq_refl (term4 n m)). Qed.
Lemma lem5393548 (n : nat) (m : nat) : ((term3 m n) = (term4 n m)) = ((term4 n m) = (term4 n m)).
Proof. exact (MK_COMB (@lem5393546 n m) (@lem5393547 n m)). Qed.
Lemma lem5393550 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5393551 (x : nat) : (x = x) = True.
Proof. exact (@lem5393550 nat x). Qed.
Lemma lem5393552 (n : nat) (m : nat) : ((term4 n m) = (term4 n m)) = True.
Proof. exact (@lem5393551 (term4 n m)). Qed.
Lemma lem5393553 (n : nat) (m : nat) : ((term3 m n) = (term4 n m)) = True.
Proof. exact (TRANS (@lem5393548 n m) (@lem5393552 n m)). Qed.
Lemma lem5393554 (n : nat) (m : nat) : (term15 n m) = (True /\ True).
Proof. exact (MK_COMB (@lem5393540 m n) (@lem5393553 n m)). Qed.
Lemma lem5393556 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5393557 : (True /\ True) = True.
Proof. exact (@lem5393556 True). Qed.
Lemma lem5393558 (n : nat) (m : nat) : (term15 n m) = True.
Proof. exact (TRANS (@lem5393554 n m) (@lem5393557)). Qed.
Lemma lem5393559 (n : nat) (m : nat) : (term14 n m) = True.
Proof. exact (TRANS (@lem5393534 n m) (@lem5393558 n m)). Qed.
Lemma lem5393560 (m : nat) : (term19 m) = term20.
Proof. exact (fun_ext (fun n : nat => @lem5393559 n m)). Qed.
Lemma lem5393561 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393562 (m : nat) : (term21 m) = term22.
Proof. exact (MK_COMB (@lem5393561) (@lem5393560 m)). Qed.
Lemma lem5393564 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5393565 (t : Prop) : (term24 t) = t.
Proof. exact (@lem5393564 nat t). Qed.
Lemma lem5393566 : term22 = True.
Proof. exact (@lem5393565 True). Qed.
Lemma lem5393567 (m : nat) : (term21 m) = True.
Proof. exact (TRANS (@lem5393562 m) (@lem5393566)). Qed.
Lemma lem5393568 : term25 = term20.
Proof. exact (fun_ext (fun m : nat => @lem5393567 m)). Qed.
Lemma lem5393569 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393570 : term26 = term22.
Proof. exact (MK_COMB (@lem5393569) (@lem5393568)). Qed.
Lemma lem5393572 {A : Type'} (t : Prop) : (term23 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5393573 (t : Prop) : (term24 t) = t.
Proof. exact (@lem5393572 nat t). Qed.
Lemma lem5393574 : term22 = True.
Proof. exact (@lem5393573 True). Qed.
Lemma lem5393575 : term26 = True.
Proof. exact (TRANS (@lem5393570) (@lem5393574)). Qed.
Lemma lem5393576 : True = term26.
Proof. exact (SYM (@lem5393575)). Qed.
Lemma lem5393577 : term26.
Proof. exact (EQ_MP (@lem5393576) (@lem0)). Qed.
