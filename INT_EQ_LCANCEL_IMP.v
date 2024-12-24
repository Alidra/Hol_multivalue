Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_EQ_LCANCEL_IMP_term_abbrevs.
Require Import REAL_EQ_LCANCEL_IMP_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2301624 (x : int) : term0 x.
Proof. exact (@lem1640851 (real_of_int x)). Qed.
Lemma lem2301625 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2301626 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2301625 x) (@lem2301624 x)). Qed.
Lemma lem2301627 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2301626 x (real_of_int y)). Qed.
Lemma lem2301628 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2301629 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2301628 x y) (@lem2301627 x y)). Qed.
Lemma lem2301630 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2301629 x y (real_of_int z)). Qed.
Lemma lem2301631 (z : int) (x : int) (y : int) : (term4 x y z) = (term5 z x y).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2301632 (z : int) (x : int) (y : int) : term5 z x y.
Proof. exact (EQ_MP (@lem2301631 z x y) (@lem2301630 x y z)). Qed.
Lemma lem2301634 (n : nat) : (real_of_num n) = (term6 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2301635 : term7 = term8.
Proof. exact (@lem2301634 (NUMERAL 0)). Qed.
Lemma lem2301636 (z : int) : (term9 z) = (term9 z).
Proof. exact (eq_refl (term9 z)). Qed.
Lemma lem2301637 (z : int) : ((real_of_int z) = term7) = ((real_of_int z) = term8).
Proof. exact (MK_COMB (@lem2301636 z) (@lem2301635)). Qed.
Lemma lem2301639 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301640 (z : int) : ((real_of_int z) = term8) = (z = term10).
Proof. exact (@lem2301639 z term10). Qed.
Lemma lem2301641 (z : int) : ((real_of_int z) = term7) = (z = term10).
Proof. exact (TRANS (@lem2301637 z) (@lem2301640 z)). Qed.
Lemma lem2301642 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2301643 (z : int) : (term11 z) = (term12 z).
Proof. exact (MK_COMB (@lem2301642) (@lem2301641 z)). Qed.
Lemma lem2301644 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2301645 (z : int) : (term13 z) = (term14 z).
Proof. exact (MK_COMB (@lem2301644) (@lem2301643 z)). Qed.
Lemma lem2301647 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301648 (z : int) (x : int) : (term15 z x) = (term16 z x).
Proof. exact (@lem2301647 z x). Qed.
Lemma lem2301649 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2301650 (z : int) (x : int) : (term17 z x) = (term18 z x).
Proof. exact (MK_COMB (@lem2301649) (@lem2301648 z x)). Qed.
Lemma lem2301652 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2301653 (z : int) (y : int) : (term15 z y) = (term16 z y).
Proof. exact (@lem2301652 z y). Qed.
Lemma lem2301654 (x : int) (z : int) (y : int) : ((term15 z x) = (term15 z y)) = ((term16 z x) = (term16 z y)).
Proof. exact (MK_COMB (@lem2301650 z x) (@lem2301653 z y)). Qed.
Lemma lem2301656 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301657 (x : int) (z : int) (y : int) : ((term16 z x) = (term16 z y)) = ((int_mul z x) = (int_mul z y)).
Proof. exact (@lem2301656 (int_mul z x) (int_mul z y)). Qed.
Lemma lem2301658 (x : int) (z : int) (y : int) : ((term15 z x) = (term15 z y)) = ((int_mul z x) = (int_mul z y)).
Proof. exact (TRANS (@lem2301654 x z y) (@lem2301657 x z y)). Qed.
Lemma lem2301659 (x : int) (z : int) (y : int) : (term19 x z y) = (term20 x z y).
Proof. exact (MK_COMB (@lem2301645 z) (@lem2301658 x z y)). Qed.
Lemma lem2301660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2301661 (x : int) (z : int) (y : int) : (term21 x z y) = (term22 x z y).
Proof. exact (MK_COMB (@lem2301660) (@lem2301659 x z y)). Qed.
Lemma lem2301663 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2301664 (z : int) (x : int) (y : int) : (term5 z x y) = (term23 z x y).
Proof. exact (MK_COMB (@lem2301661 x z y) (@lem2301663 x y)). Qed.
Lemma lem2301665 (z : int) (x : int) (y : int) : term23 z x y.
Proof. exact (EQ_MP (@lem2301664 z x y) (@lem2301632 z x y)). Qed.
Lemma lem2301666 (x : int) (y : int) : term24 x y.
Proof. exact (fun z : int => @lem2301665 z x y). Qed.
Lemma lem2301667 (x : int) : term25 x.
Proof. exact (fun y : int => @lem2301666 x y). Qed.
Lemma lem2301668 : term26.
Proof. exact (fun x : int => @lem2301667 x). Qed.
