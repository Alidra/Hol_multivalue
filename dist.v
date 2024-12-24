Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import dist_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem1244652 : dist = term0.
Proof. exact (@dist_def). Qed.
Lemma lem1244653 (_22820 : prod nat nat) : _22820 = _22820.
Proof. exact (eq_refl _22820). Qed.
Lemma lem1244654 (_22820 : prod nat nat) : (dist _22820) = (term1 _22820).
Proof. exact (MK_COMB (@lem1244652) (@lem1244653 _22820)). Qed.
Lemma lem1244655 (_22820 : prod nat nat) : (term1 _22820) = (term2 _22820).
Proof. exact (eq_refl (term1 _22820)). Qed.
Lemma lem1244656 (_22820 : prod nat nat) : (dist _22820) = (term2 _22820).
Proof. exact (TRANS (@lem1244654 _22820) (@lem1244655 _22820)). Qed.
Lemma lem1244657 : term3.
Proof. exact (fun _22820 : prod nat nat => @lem1244656 _22820). Qed.
Lemma lem1244658 (_22820 : prod nat nat) : term4 _22820.
Proof. exact (@lem1244657 _22820). Qed.
Lemma lem1244659 (_22820 : prod nat nat) : (term4 _22820) = ((dist _22820) = (term2 _22820)).
Proof. exact (eq_refl (term4 _22820)). Qed.
Lemma lem1244660 (_22820 : prod nat nat) : (dist _22820) = (term2 _22820).
Proof. exact (EQ_MP (@lem1244659 _22820) (@lem1244658 _22820)). Qed.
Lemma lem1244661 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (@lem1244660 (@pair nat nat m n)). Qed.
Lemma lem1244662 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1244663 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem1244664 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem1244663 A B x) (@lem1244662 A B x)). Qed.
Lemma lem1244665 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem1244664 A B x y). Qed.
Lemma lem1244666 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem1244668 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1244669 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem1244670 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem1244669 A B x) (@lem1244668 A B x)). Qed.
Lemma lem1244671 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem1244670 A B x y). Qed.
Lemma lem1244672 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem1244675 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem1244672 A B y x) (@lem1244671 A B x y)). Qed.
Lemma lem1244676 (y : nat) (x : nat) : (term15 x y) = x.
Proof. exact (@lem1244675 nat nat y x). Qed.
Lemma lem1244677 (n : nat) (m : nat) : (term15 m n) = m.
Proof. exact (@lem1244676 n m). Qed.
Lemma lem1244678 (m : nat) (n : nat) : m = (term15 m n).
Proof. exact (SYM (@lem1244677 n m)). Qed.
Lemma lem1244680 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem1244666 A B x y) (@lem1244665 A B x y)). Qed.
Lemma lem1244681 (x : nat) (y : nat) : (term16 x y) = y.
Proof. exact (@lem1244680 nat nat x y). Qed.
Lemma lem1244682 (m : nat) (n : nat) : (term16 m n) = n.
Proof. exact (@lem1244681 m n). Qed.
Lemma lem1244683 (m : nat) (n : nat) : n = (term16 m n).
Proof. exact (SYM (@lem1244682 m n)). Qed.
Lemma lem1244684 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1244685 (m : nat) (n : nat) : (term18 m) = (term19 m n).
Proof. exact (MK_COMB (@lem1244684) (@lem1244678 m n)). Qed.
Lemma lem1244686 (m : nat) (n : nat) : (term19 m n) = (term20 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1244687 (m : nat) : (term21 m) = (term21 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1244688 (m : nat) (n : nat) : ((term18 m) = (term19 m n)) = ((term18 m) = (term20 m n)).
Proof. exact (MK_COMB (@lem1244687 m) (@lem1244686 m n)). Qed.
Lemma lem1244689 (m : nat) : (term18 m) = (term22 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1244690 : (@eq (nat -> nat)) = (@eq (nat -> nat)).
Proof. exact (eq_refl (@eq (nat -> nat))). Qed.
Lemma lem1244691 (m : nat) : (term21 m) = (term23 m).
Proof. exact (MK_COMB (@lem1244690) (@lem1244689 m)). Qed.
Lemma lem1244692 (m : nat) (n : nat) : (term20 m n) = (term20 m n).
Proof. exact (eq_refl (term20 m n)). Qed.
Lemma lem1244693 (m : nat) (n : nat) : ((term18 m) = (term20 m n)) = ((term22 m) = (term20 m n)).
Proof. exact (MK_COMB (@lem1244691 m) (@lem1244692 m n)). Qed.
Lemma lem1244694 (m : nat) (n : nat) : ((term18 m) = (term19 m n)) = ((term22 m) = (term20 m n)).
Proof. exact (TRANS (@lem1244688 m n) (@lem1244693 m n)). Qed.
Lemma lem1244695 (m : nat) (n : nat) : (term22 m) = (term20 m n).
Proof. exact (EQ_MP (@lem1244694 m n) (@lem1244685 m n)). Qed.
Lemma lem1244696 (m : nat) (n : nat) : (term24 m n) = (term25 m n).
Proof. exact (MK_COMB (@lem1244695 m n) (@lem1244683 m n)). Qed.
Lemma lem1244697 (m : nat) (n : nat) : (term25 m n) = (term6 m n).
Proof. exact (eq_refl (term25 m n)). Qed.
Lemma lem1244698 (m : nat) (n : nat) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem1244699 (m : nat) (n : nat) : ((term24 m n) = (term25 m n)) = ((term24 m n) = (term6 m n)).
Proof. exact (MK_COMB (@lem1244698 m n) (@lem1244697 m n)). Qed.
Lemma lem1244700 (n : nat) (m : nat) : (term24 m n) = (term27 n m).
Proof. exact (eq_refl (term24 m n)). Qed.
Lemma lem1244701 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1244702 (n : nat) (m : nat) : (term26 m n) = (term28 n m).
Proof. exact (MK_COMB (@lem1244701) (@lem1244700 n m)). Qed.
Lemma lem1244703 (m : nat) (n : nat) : (term6 m n) = (term6 m n).
Proof. exact (eq_refl (term6 m n)). Qed.
Lemma lem1244704 (m : nat) (n : nat) : ((term24 m n) = (term6 m n)) = ((term27 n m) = (term6 m n)).
Proof. exact (MK_COMB (@lem1244702 n m) (@lem1244703 m n)). Qed.
Lemma lem1244705 (m : nat) (n : nat) : ((term24 m n) = (term25 m n)) = ((term27 n m) = (term6 m n)).
Proof. exact (TRANS (@lem1244699 m n) (@lem1244704 m n)). Qed.
Lemma lem1244706 (m : nat) (n : nat) : (term27 n m) = (term6 m n).
Proof. exact (EQ_MP (@lem1244705 m n) (@lem1244696 m n)). Qed.
Lemma lem1244707 (n : nat) (m : nat) : (term6 m n) = (term27 n m).
Proof. exact (SYM (@lem1244706 m n)). Qed.
Lemma lem1244708 (n : nat) (m : nat) : (term5 m n) = (term27 n m).
Proof. exact (TRANS (@lem1244661 m n) (@lem1244707 n m)). Qed.
Lemma lem1244709 (n : nat) : term29 n.
Proof. exact (fun m : nat => @lem1244708 n m). Qed.
Lemma lem1244710 : term30.
Proof. exact (fun n : nat => @lem1244709 n). Qed.
