Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_CLAUSES_NUMSEG_term_abbrevs.
Require Import ITERATE_CLAUSES_NUMSEG_spec.
Require Import MONOIDAL_REAL_ADD_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm7064097_spec.
Require Import thm7064111_spec.
Require Import thm7064171_spec.
Require Import thm7065437_spec.
Lemma lem7221566 {_123419 : Type'} (f : nat -> _123419) (op : type1400 _123419) : term0 _123419 f op.
Proof. exact (@lem6192133 _123419 f op). Qed.
Lemma lem7221567 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : (term0 _123419 f op) = (term1 _123419 op f).
Proof. exact (eq_refl (term0 _123419 f op)). Qed.
Lemma lem7221570 {_123419 : Type'} (op : type1400 _123419) (f : nat -> _123419) : term1 _123419 op f.
Proof. exact (EQ_MP (@lem7221567 _123419 op f) (@lem7221566 _123419 f op)). Qed.
Lemma lem7221571 (op : type1627) (f : nat -> real) : term2 op f.
Proof. exact (@lem7221570 real op f). Qed.
Lemma lem7221572 (f : nat -> real) : term3 f.
Proof. exact (@lem7221571 real_add f). Qed.
Lemma lem7221573 (f : nat -> real) : term4 f.
Proof. exact (@lem7221572 f (@lem7067132)). Qed.
Lemma lem7221589 : (@neutral real real_add) = term5.
Proof. exact (EQ_MP (@lem7064171) (@lem7065437)). Qed.
Lemma lem7221590 (m : nat) (f : nat -> real) : (term6 m f) = (term6 m f).
Proof. exact (eq_refl (term6 m f)). Qed.
Lemma lem7221591 (m : nat) (f : nat -> real) : (term7 m f) = (term8 m f).
Proof. exact (MK_COMB (@lem7221590 m f) (@lem7221589)). Qed.
Lemma lem7221594 (m : nat) (f : nat -> real) : (term9 m f) = (term9 m f).
Proof. exact (eq_refl (term9 m f)). Qed.
Lemma lem7221595 (m : nat) (f : nat -> real) : ((term10 m f) = (term7 m f)) = ((term10 m f) = (term8 m f)).
Proof. exact (MK_COMB (@lem7221594 m f) (@lem7221591 m f)). Qed.
Lemma lem7221598 (f : nat -> real) : (term11 f) = (term12 f).
Proof. exact (fun_ext (fun m : nat => @lem7221595 m f)). Qed.
Lemma lem7221599 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7221600 (f : nat -> real) : (term13 f) = (term14 f).
Proof. exact (MK_COMB (@lem7221599) (@lem7221598 f)). Qed.
Lemma lem7221605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221606 (f : nat -> real) : (term15 f) = (term16 f).
Proof. exact (MK_COMB (@lem7221605) (@lem7221600 f)). Qed.
Lemma lem7221617 (f : nat -> real) : (term17 f) = (term17 f).
Proof. exact (eq_refl (term17 f)). Qed.
Lemma lem7221618 (f : nat -> real) : (term4 f) = (term18 f).
Proof. exact (MK_COMB (@lem7221606 f) (@lem7221617 f)). Qed.
Lemma lem7221621 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7221622 (f : nat -> real) : (term19 f) = (term20 f).
Proof. exact (MK_COMB (@lem7221621) (@lem7221618 f)). Qed.
Lemma lem7221632 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221633 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221632 nat). Qed.
Lemma lem7221634 (m : nat) : (term21 m) = (term21 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem7221635 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem7221633) (@lem7221634 m)). Qed.
Lemma lem7221636 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221637 (m : nat) (f : nat -> real) : (term24 m f) = (term10 m f).
Proof. exact (MK_COMB (@lem7221635 m) (@lem7221636 f)). Qed.
Lemma lem7221638 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7221639 (m : nat) (f : nat -> real) : (term25 m f) = (term9 m f).
Proof. exact (MK_COMB (@lem7221638) (@lem7221637 m f)). Qed.
Lemma lem7221644 (m : nat) (f : nat -> real) : (term8 m f) = (term8 m f).
Proof. exact (eq_refl (term8 m f)). Qed.
Lemma lem7221645 (m : nat) (f : nat -> real) : ((term24 m f) = (term8 m f)) = ((term10 m f) = (term8 m f)).
Proof. exact (MK_COMB (@lem7221639 m f) (@lem7221644 m f)). Qed.
Lemma lem7221648 (f : nat -> real) : (term26 f) = (term12 f).
Proof. exact (fun_ext (fun m : nat => @lem7221645 m f)). Qed.
Lemma lem7221649 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7221650 (f : nat -> real) : (term27 f) = (term14 f).
Proof. exact (MK_COMB (@lem7221649) (@lem7221648 f)). Qed.
Lemma lem7221655 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7221656 (f : nat -> real) : (term28 f) = (term16 f).
Proof. exact (MK_COMB (@lem7221655) (@lem7221650 f)). Qed.
Lemma lem7221668 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221669 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221668 nat). Qed.
Lemma lem7221670 (m : nat) (n : nat) : (term29 m n) = (term29 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem7221671 (m : nat) (n : nat) : (term30 m n) = (term31 m n).
Proof. exact (MK_COMB (@lem7221669) (@lem7221670 m n)). Qed.
Lemma lem7221672 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221673 (m : nat) (n : nat) (f : nat -> real) : (term32 m n f) = (term33 m n f).
Proof. exact (MK_COMB (@lem7221671 m n) (@lem7221672 f)). Qed.
Lemma lem7221674 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7221675 (m : nat) (n : nat) (f : nat -> real) : (term34 m n f) = (term35 m n f).
Proof. exact (MK_COMB (@lem7221674) (@lem7221673 m n f)). Qed.
Lemma lem7221677 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221678 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221677 nat). Qed.
Lemma lem7221679 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7221680 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem7221678) (@lem7221679 m n)). Qed.
Lemma lem7221681 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221682 (m : nat) (n : nat) (f : nat -> real) : (term38 m n f) = (term39 m n f).
Proof. exact (MK_COMB (@lem7221680 m n) (@lem7221681 f)). Qed.
Lemma lem7221683 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem7221684 (m : nat) (n : nat) (f : nat -> real) : (term40 m n f) = (term41 m n f).
Proof. exact (MK_COMB (@lem7221683) (@lem7221682 m n f)). Qed.
Lemma lem7221685 (f : nat -> real) (n : nat) : (term42 f n) = (term42 f n).
Proof. exact (eq_refl (term42 f n)). Qed.
Lemma lem7221686 (m : nat) (f : nat -> real) (n : nat) : (term43 m f n) = (term44 m f n).
Proof. exact (MK_COMB (@lem7221684 m n f) (@lem7221685 f n)). Qed.
Lemma lem7221687 (m : nat) (n : nat) : (term45 m n) = (term45 m n).
Proof. exact (eq_refl (term45 m n)). Qed.
Lemma lem7221688 (m : nat) (f : nat -> real) (n : nat) : (term46 m f n) = (term47 m f n).
Proof. exact (MK_COMB (@lem7221687 m n) (@lem7221686 m f n)). Qed.
Lemma lem7221690 {_131408 : Type'} : (@sum _131408) = (@iterate real _131408 real_add).
Proof. exact (TRANS (@lem7064097 _131408) (@lem7064111 _131408)). Qed.
Lemma lem7221691 : (@sum nat) = (@iterate real nat real_add).
Proof. exact (@lem7221690 nat). Qed.
Lemma lem7221692 (m : nat) (n : nat) : (dotdot m n) = (dotdot m n).
Proof. exact (eq_refl (dotdot m n)). Qed.
Lemma lem7221693 (m : nat) (n : nat) : (term36 m n) = (term37 m n).
Proof. exact (MK_COMB (@lem7221691) (@lem7221692 m n)). Qed.
Lemma lem7221694 (f : nat -> real) : f = f.
Proof. exact (eq_refl f). Qed.
Lemma lem7221695 (m : nat) (n : nat) (f : nat -> real) : (term38 m n f) = (term39 m n f).
Proof. exact (MK_COMB (@lem7221693 m n) (@lem7221694 f)). Qed.
Lemma lem7221696 (m : nat) (n : nat) (f : nat -> real) : (term48 m n f) = (term49 m n f).
Proof. exact (MK_COMB (@lem7221688 m f n) (@lem7221695 m n f)). Qed.
Lemma lem7221697 (m : nat) (n : nat) (f : nat -> real) : ((term32 m n f) = (term48 m n f)) = ((term33 m n f) = (term49 m n f)).
Proof. exact (MK_COMB (@lem7221675 m n f) (@lem7221696 m n f)). Qed.
Lemma lem7221700 (m : nat) (f : nat -> real) : (term50 m f) = (term51 m f).
Proof. exact (fun_ext (fun n : nat => @lem7221697 m n f)). Qed.
Lemma lem7221701 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7221702 (m : nat) (f : nat -> real) : (term52 m f) = (term53 m f).
Proof. exact (MK_COMB (@lem7221701) (@lem7221700 m f)). Qed.
Lemma lem7221707 (f : nat -> real) : (term54 f) = (term55 f).
Proof. exact (fun_ext (fun m : nat => @lem7221702 m f)). Qed.
Lemma lem7221708 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7221709 (f : nat -> real) : (term56 f) = (term17 f).
Proof. exact (MK_COMB (@lem7221708) (@lem7221707 f)). Qed.
Lemma lem7221714 (f : nat -> real) : (term57 f) = (term18 f).
Proof. exact (MK_COMB (@lem7221656 f) (@lem7221709 f)). Qed.
Lemma lem7221717 (f : nat -> real) : (term58 f) = (term59 f).
Proof. exact (MK_COMB (@lem7221622 f) (@lem7221714 f)). Qed.
Lemma lem7221719 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem7221720 (f : nat -> real) : (term59 f) = True.
Proof. exact (@lem7221719 (term18 f)). Qed.
Lemma lem7221721 (f : nat -> real) : (term58 f) = True.
Proof. exact (TRANS (@lem7221717 f) (@lem7221720 f)). Qed.
Lemma lem7221722 (f : nat -> real) : True = (term58 f).
Proof. exact (SYM (@lem7221721 f)). Qed.
Lemma lem7221723 (f : nat -> real) : term58 f.
Proof. exact (EQ_MP (@lem7221722 f) (@lem0)). Qed.
Lemma lem7221724 (f : nat -> real) : term57 f.
Proof. exact (@lem7221723 f (@lem7221573 f)). Qed.
