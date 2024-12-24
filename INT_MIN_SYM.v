Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MIN_SYM_term_abbrevs.
Require Import REAL_MIN_SYM_spec.
Require Import thm2299882_spec.
Require Import thm2299883_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305766 (x : int) : term0 x.
Proof. exact (@lem1559391 (real_of_int x)). Qed.
Lemma lem2305767 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305768 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2305767 x) (@lem2305766 x)). Qed.
Lemma lem2305769 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2305768 x (real_of_int y)). Qed.
Lemma lem2305770 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2305771 (y : int) (x : int) : (term3 x y) = (term3 y x).
Proof. exact (EQ_MP (@lem2305770 y x) (@lem2305769 x y)). Qed.
Lemma lem2305773 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305774 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305775 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2305774) (@lem2305773 x y)). Qed.
Lemma lem2305777 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299883 x y) (@lem2299882 x y)). Qed.
Lemma lem2305778 (y : int) (x : int) : (term3 y x) = (term4 y x).
Proof. exact (@lem2305777 y x). Qed.
Lemma lem2305779 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((term4 x y) = (term4 y x)).
Proof. exact (MK_COMB (@lem2305775 x y) (@lem2305778 y x)). Qed.
Lemma lem2305781 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305782 (y : int) (x : int) : ((term4 x y) = (term4 y x)) = ((int_min x y) = (int_min y x)).
Proof. exact (@lem2305781 (int_min x y) (int_min y x)). Qed.
Lemma lem2305783 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((int_min x y) = (int_min y x)).
Proof. exact (TRANS (@lem2305779 y x) (@lem2305782 y x)). Qed.
Lemma lem2305784 (y : int) (x : int) : (int_min x y) = (int_min y x).
Proof. exact (EQ_MP (@lem2305783 y x) (@lem2305771 y x)). Qed.
Lemma lem2305785 (x : int) : term7 x.
Proof. exact (fun y : int => @lem2305784 y x). Qed.
Lemma lem2305786 : term8.
Proof. exact (fun x : int => @lem2305785 x). Qed.
