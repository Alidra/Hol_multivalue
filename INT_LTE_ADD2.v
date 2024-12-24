Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LTE_ADD2_term_abbrevs.
Require Import REAL_LTE_ADD2_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299936_spec.
Require Import thm2299937_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303533 (w : int) : term0 w.
Proof. exact (@lem1519000 (real_of_int w)). Qed.
Lemma lem2303534 (w : int) : (term0 w) = (term1 w).
Proof. exact (eq_refl (term0 w)). Qed.
Lemma lem2303535 (w : int) : term1 w.
Proof. exact (EQ_MP (@lem2303534 w) (@lem2303533 w)). Qed.
Lemma lem2303536 (w : int) (x : int) : term2 w x.
Proof. exact (@lem2303535 w (real_of_int x)). Qed.
Lemma lem2303537 (w : int) (x : int) : (term2 w x) = (term3 w x).
Proof. exact (eq_refl (term2 w x)). Qed.
Lemma lem2303538 (w : int) (x : int) : term3 w x.
Proof. exact (EQ_MP (@lem2303537 w x) (@lem2303536 w x)). Qed.
Lemma lem2303539 (w : int) (x : int) (y : int) : term4 w x y.
Proof. exact (@lem2303538 w x (real_of_int y)). Qed.
Lemma lem2303540 (w : int) (y : int) (x : int) : (term4 w x y) = (term5 w y x).
Proof. exact (eq_refl (term4 w x y)). Qed.
Lemma lem2303541 (w : int) (y : int) (x : int) : term5 w y x.
Proof. exact (EQ_MP (@lem2303540 w y x) (@lem2303539 w x y)). Qed.
Lemma lem2303542 (w : int) (y : int) (x : int) (z : int) : term6 w y x z.
Proof. exact (@lem2303541 w y x (real_of_int z)). Qed.
Lemma lem2303543 (w : int) (y : int) (x : int) (z : int) : (term6 w y x z) = (term7 w y x z).
Proof. exact (eq_refl (term6 w y x z)). Qed.
Lemma lem2303544 (w : int) (y : int) (x : int) (z : int) : term7 w y x z.
Proof. exact (EQ_MP (@lem2303543 w y x z) (@lem2303542 w y x z)). Qed.
Lemma lem2303546 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303547 (w : int) (x : int) : (term8 w x) = (int_lt w x).
Proof. exact (@lem2303546 w x). Qed.
Lemma lem2303548 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2303549 (w : int) (x : int) : (term9 w x) = (term10 w x).
Proof. exact (MK_COMB (@lem2303548) (@lem2303547 w x)). Qed.
Lemma lem2303551 (x : int) (y : int) : (term11 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303552 (y : int) (z : int) : (term11 y z) = (int_le y z).
Proof. exact (@lem2303551 y z). Qed.
Lemma lem2303553 (w : int) (x : int) (y : int) (z : int) : (term12 w x y z) = (term13 w x y z).
Proof. exact (MK_COMB (@lem2303549 w x) (@lem2303552 y z)). Qed.
Lemma lem2303554 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2303555 (w : int) (x : int) (y : int) (z : int) : (term14 w x y z) = (term15 w x y z).
Proof. exact (MK_COMB (@lem2303554) (@lem2303553 w x y z)). Qed.
Lemma lem2303557 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303558 (w : int) (y : int) : (term16 w y) = (term17 w y).
Proof. exact (@lem2303557 w y). Qed.
Lemma lem2303559 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2303560 (w : int) (y : int) : (term18 w y) = (term19 w y).
Proof. exact (MK_COMB (@lem2303559) (@lem2303558 w y)). Qed.
Lemma lem2303562 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2303563 (x : int) (z : int) : (term16 x z) = (term17 x z).
Proof. exact (@lem2303562 x z). Qed.
Lemma lem2303564 (w : int) (y : int) (x : int) (z : int) : (term20 w y x z) = (term21 w y x z).
Proof. exact (MK_COMB (@lem2303560 w y) (@lem2303563 x z)). Qed.
Lemma lem2303566 (x : int) (y : int) : (term8 x y) = (int_lt x y).
Proof. exact (EQ_MP (@lem2299937 x y) (@lem2299936 x y)). Qed.
Lemma lem2303567 (w : int) (y : int) (x : int) (z : int) : (term21 w y x z) = (term22 w y x z).
Proof. exact (@lem2303566 (int_add w y) (int_add x z)). Qed.
Lemma lem2303568 (w : int) (y : int) (x : int) (z : int) : (term20 w y x z) = (term22 w y x z).
Proof. exact (TRANS (@lem2303564 w y x z) (@lem2303567 w y x z)). Qed.
Lemma lem2303569 (w : int) (y : int) (x : int) (z : int) : (term7 w y x z) = (term23 w y x z).
Proof. exact (MK_COMB (@lem2303555 w x y z) (@lem2303568 w y x z)). Qed.
Lemma lem2303570 (w : int) (y : int) (x : int) (z : int) : term23 w y x z.
Proof. exact (EQ_MP (@lem2303569 w y x z) (@lem2303544 w y x z)). Qed.
Lemma lem2303571 (w : int) (y : int) (x : int) : term24 w y x.
Proof. exact (fun z : int => @lem2303570 w y x z). Qed.
Lemma lem2303572 (w : int) (x : int) : term25 w x.
Proof. exact (fun y : int => @lem2303571 w y x). Qed.
Lemma lem2303573 (w : int) : term26 w.
Proof. exact (fun x : int => @lem2303572 w x). Qed.
Lemma lem2303574 : term27.
Proof. exact (fun w : int => @lem2303573 w). Qed.
