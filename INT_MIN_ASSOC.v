Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_ASSOC_term_abbrevs.
Require Import REAL_MIN_ASSOC_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305589 (x : int) : term0 x.
Proof. exact (@lem1574873 (real_of_int x)). Qed.
Lemma lem2305590 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305591 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305590 x) (@lem2305589 x)). Qed.
Lemma lem2305592 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305591 x (real_of_int y)). Qed.
Lemma lem2305593 (x : int) (y : int) : (term2 x y) = (term3 x y).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305594 (x : int) (y : int) : term3 x y.
Proof. exact (EQ_MP (@lem2305593 x y) (@lem2305592 x y)). Qed.
Lemma lem2305595 (x : int) (y : int) (z : int) : term4 x y z.
Proof. exact (@lem2305594 x y (real_of_int z)). Qed.
Lemma lem2305596 (x : int) (y : int) (z : int) : (term4 x y z) = ((term5 x y z) = (term6 x y z)).
Proof. exact (eq_refl (term4 x y z)). Qed.
Lemma lem2305597 (x : int) (y : int) (z : int) : (term5 x y z) = (term6 x y z).
Proof. exact (EQ_MP (@lem2305596 x y z) (@lem2305595 x y z)). Qed.
Lemma lem2305599 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305600 (y : int) (z : int) : (term7 y z) = (term8 y z).
Proof. exact (@lem2305599 y z). Qed.
Lemma lem2305601 (x : int) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2305602 (x : int) (y : int) (z : int) : (term5 x y z) = (term10 x y z).
Proof. exact (MK_COMB (@lem2305601 x) (@lem2305600 y z)). Qed.
Lemma lem2305604 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305605 (x : int) (y : int) (z : int) : (term10 x y z) = (term11 x y z).
Proof. exact (@lem2305604 x (int_min y z)). Qed.
Lemma lem2305606 (x : int) (y : int) (z : int) : (term5 x y z) = (term11 x y z).
Proof. exact (TRANS (@lem2305602 x y z) (@lem2305605 x y z)). Qed.
Lemma lem2305607 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305608 (x : int) (y : int) (z : int) : (term12 x y z) = (term13 x y z).
Proof. exact (MK_COMB (@lem2305607) (@lem2305606 x y z)). Qed.
Lemma lem2305610 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305611 : real_min = real_min.
Proof. exact (eq_refl real_min). Qed.
Lemma lem2305612 (x : int) (y : int) : (term14 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2305611) (@lem2305610 x y)). Qed.
Lemma lem2305613 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2305614 (x : int) (y : int) (z : int) : (term6 x y z) = (term16 x y z).
Proof. exact (MK_COMB (@lem2305612 x y) (@lem2305613 z)). Qed.
Lemma lem2305616 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305617 (x : int) (y : int) (z : int) : (term16 x y z) = (term17 x y z).
Proof. exact (@lem2305616 (int_min x y) z). Qed.
Lemma lem2305618 (x : int) (y : int) (z : int) : (term6 x y z) = (term17 x y z).
Proof. exact (TRANS (@lem2305614 x y z) (@lem2305617 x y z)). Qed.
Lemma lem2305619 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term11 x y z) = (term17 x y z)).
Proof. exact (MK_COMB (@lem2305608 x y z) (@lem2305618 x y z)). Qed.
Lemma lem2305621 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305622 (x : int) (y : int) (z : int) : ((term11 x y z) = (term17 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (@lem2305621 (term18 x y z) (term19 x y z)). Qed.
Lemma lem2305623 (x : int) (y : int) (z : int) : ((term5 x y z) = (term6 x y z)) = ((term18 x y z) = (term19 x y z)).
Proof. exact (TRANS (@lem2305619 x y z) (@lem2305622 x y z)). Qed.
Lemma lem2305624 (x : int) (y : int) (z : int) : (term18 x y z) = (term19 x y z).
Proof. exact (EQ_MP (@lem2305623 x y z) (@lem2305597 x y z)). Qed.
Lemma lem2305625 (x : int) (y : int) : term20 x y.
Proof. exact (fun z : int => @lem2305624 x y z). Qed.
Lemma lem2305626 (x : int) : term21 x.
Proof. exact (fun y : int => @lem2305625 x y). Qed.
Lemma lem2305627 : term22.
Proof. exact (fun x : int => @lem2305626 x). Qed.
