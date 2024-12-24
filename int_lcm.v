Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_lcm_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem2802641 : int_lcm = term0.
Proof. exact (@int_lcm_def). Qed.
Lemma lem2802642 (_30834 : prod int int) : _30834 = _30834.
Proof. exact (eq_refl _30834). Qed.
Lemma lem2802643 (_30834 : prod int int) : (int_lcm _30834) = (term1 _30834).
Proof. exact (MK_COMB (@lem2802641) (@lem2802642 _30834)). Qed.
Lemma lem2802644 (_30834 : prod int int) : (term1 _30834) = (term2 _30834).
Proof. exact (eq_refl (term1 _30834)). Qed.
Lemma lem2802645 (_30834 : prod int int) : (int_lcm _30834) = (term2 _30834).
Proof. exact (TRANS (@lem2802643 _30834) (@lem2802644 _30834)). Qed.
Lemma lem2802646 : term3.
Proof. exact (fun _30834 : prod int int => @lem2802645 _30834). Qed.
Lemma lem2802647 (_30834 : prod int int) : term4 _30834.
Proof. exact (@lem2802646 _30834). Qed.
Lemma lem2802648 (_30834 : prod int int) : (term4 _30834) = ((int_lcm _30834) = (term2 _30834)).
Proof. exact (eq_refl (term4 _30834)). Qed.
Lemma lem2802649 (_30834 : prod int int) : (int_lcm _30834) = (term2 _30834).
Proof. exact (EQ_MP (@lem2802648 _30834) (@lem2802647 _30834)). Qed.
Lemma lem2802650 (m : int) (n : int) : (term5 m n) = (term6 m n).
Proof. exact (@lem2802649 (@pair int int m n)). Qed.
Lemma lem2802651 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem2802652 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem2802653 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem2802652 A B x) (@lem2802651 A B x)). Qed.
Lemma lem2802654 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem2802653 A B x y). Qed.
Lemma lem2802655 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem2802657 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem2802658 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem2802659 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem2802658 A B x) (@lem2802657 A B x)). Qed.
Lemma lem2802660 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem2802659 A B x y). Qed.
Lemma lem2802661 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem2802664 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem2802661 A B y x) (@lem2802660 A B x y)). Qed.
Lemma lem2802665 (y : int) (x : int) : (term15 x y) = x.
Proof. exact (@lem2802664 int int y x). Qed.
Lemma lem2802666 (n : int) (m : int) : (term15 m n) = m.
Proof. exact (@lem2802665 n m). Qed.
Lemma lem2802667 (m : int) (n : int) : m = (term15 m n).
Proof. exact (SYM (@lem2802666 n m)). Qed.
Lemma lem2802669 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem2802655 A B x y) (@lem2802654 A B x y)). Qed.
Lemma lem2802670 (x : int) (y : int) : (term16 x y) = y.
Proof. exact (@lem2802669 int int x y). Qed.
Lemma lem2802671 (m : int) (n : int) : (term16 m n) = n.
Proof. exact (@lem2802670 m n). Qed.
Lemma lem2802672 (m : int) (n : int) : n = (term16 m n).
Proof. exact (SYM (@lem2802671 m n)). Qed.
Lemma lem2802673 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem2802674 (m : int) (n : int) : (term18 m) = (term19 m n).
Proof. exact (MK_COMB (@lem2802673) (@lem2802667 m n)). Qed.
Lemma lem2802675 (m : int) (n : int) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem2802676 (m : int) : (term21 m) = (term21 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem2802677 (m : int) (n : int) : ((term18 m) = (term19 m n)) = ((term18 m) = (term20 m n)).
Proof. exact (MK_COMB (@lem2802676 m) (@lem2802675 m n)). Qed.
Lemma lem2802678 (m : int) : (term18 m) = (term22 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem2802679 : (@eq (int -> int)) = (@eq (int -> int)).
Proof. exact (eq_refl (@eq (int -> int))). Qed.
Lemma lem2802680 (m : int) : (term21 m) = (term23 m).
Proof. exact (MK_COMB (@lem2802679) (@lem2802678 m)). Qed.
Lemma lem2802681 (m : int) (n : int) : (term20 m n) = (term20 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem2802682 (m : int) (n : int) : ((term18 m) = (term20 m n)) = ((term22 m) = (term20 m n)).
Proof. exact (MK_COMB (@lem2802680 m) (@lem2802681 m n)). Qed.
Lemma lem2802683 (m : int) (n : int) : ((term18 m) = (term19 m n)) = ((term22 m) = (term20 m n)).
Proof. exact (TRANS (@lem2802677 m n) (@lem2802682 m n)). Qed.
Lemma lem2802684 (m : int) (n : int) : (term22 m) = (term20 m n).
Proof. exact (EQ_MP (@lem2802683 m n) (@lem2802674 m n)). Qed.
Lemma lem2802685 (m : int) (n : int) : (term24 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem2802684 m n) (@lem2802672 m n)). Qed.
Lemma lem2802686 (m : int) (n : int) : (term25 m n) = (term6 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem2802687 (m : int) (n : int) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem2802688 (m : int) (n : int) : ((term24 m n) = (term25 m n)) = ((term24 m n) = (term6 m n)).
Proof. exact (MK_COMB (@lem2802687 m n) (@lem2802686 m n)). Qed.
Lemma lem2802689 (m : int) (n : int) : (term24 m n) = (term27 m n).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem2802690 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2802691 (m : int) (n : int) : (term26 m n) = (term28 m n).
Proof. exact (MK_COMB (@lem2802690) (@lem2802689 m n)). Qed.
Lemma lem2802692 (m : int) (n : int) : (term6 m n) = (term6 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem2802693 (m : int) (n : int) : ((term24 m n) = (term6 m n)) = ((term27 m n) = (term6 m n)).
Proof. exact (MK_COMB (@lem2802691 m n) (@lem2802692 m n)). Qed.
Lemma lem2802694 (m : int) (n : int) : ((term24 m n) = (term25 m n)) = ((term27 m n) = (term6 m n)).
Proof. exact (TRANS (@lem2802688 m n) (@lem2802693 m n)). Qed.
Lemma lem2802695 (m : int) (n : int) : (term27 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem2802694 m n) (@lem2802685 m n)). Qed.
Lemma lem2802696 (m : int) (n : int) : (term6 m n) = (term27 m n).
Proof. exact (SYM (@lem2802695 m n)). Qed.
Lemma lem2802697 (m : int) (n : int) : (term5 m n) = (term27 m n).
Proof. exact (TRANS (@lem2802650 m n) (@lem2802696 m n)). Qed.
Lemma lem2802698 (m : int) : term29 m.
Proof. exact (fun n : int => @lem2802697 m n). Qed.
Lemma lem2802699 : term30.
Proof. exact (fun m : int => @lem2802698 m). Qed.
