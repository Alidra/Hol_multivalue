Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_2_term_abbrevs.
Require Import REAL_MUL_2_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299912_spec.
Require Import thm2299913_spec.
Require Import thm2299918_spec.
Require Import thm2299919_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2305787 (x : int) : term0 x.
Proof. exact (@lem1629935 (real_of_int x)). Qed.
Lemma lem2305788 (x : int) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2305789 (x : int) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem2305788 x) (@lem2305787 x)). Qed.
Lemma lem2305791 (n : nat) : (real_of_num n) = (term3 n).
Proof. exact (EQ_MP (@lem2299919 n) (@lem2299918 n)). Qed.
Lemma lem2305792 : term4 = term5.
Proof. exact (@lem2305791 term6). Qed.
Lemma lem2305793 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2305794 : term7 = term8.
Proof. exact (MK_COMB (@lem2305793) (@lem2305792)). Qed.
Lemma lem2305795 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2305796 (x : int) : (term1 x) = (term9 x).
Proof. exact (MK_COMB (@lem2305794) (@lem2305795 x)). Qed.
Lemma lem2305798 (x : int) (y : int) : (term10 x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2305799 (x : int) : (term9 x) = (term12 x).
Proof. exact (@lem2305798 term13 x). Qed.
Lemma lem2305800 (x : int) : (term1 x) = (term12 x).
Proof. exact (TRANS (@lem2305796 x) (@lem2305799 x)). Qed.
Lemma lem2305801 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2305802 (x : int) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem2305801) (@lem2305800 x)). Qed.
Lemma lem2305804 (x : int) (y : int) : (term16 x y) = (term17 x y).
Proof. exact (EQ_MP (@lem2299913 x y) (@lem2299912 x y)). Qed.
Lemma lem2305805 (x : int) : (term2 x) = (term18 x).
Proof. exact (@lem2305804 x x). Qed.
Lemma lem2305806 (x : int) : ((term1 x) = (term2 x)) = ((term12 x) = (term18 x)).
Proof. exact (MK_COMB (@lem2305802 x) (@lem2305805 x)). Qed.
Lemma lem2305808 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2305809 (x : int) : ((term12 x) = (term18 x)) = ((term19 x) = (int_add x x)).
Proof. exact (@lem2305808 (term19 x) (int_add x x)). Qed.
Lemma lem2305810 (x : int) : ((term1 x) = (term2 x)) = ((term19 x) = (int_add x x)).
Proof. exact (TRANS (@lem2305806 x) (@lem2305809 x)). Qed.
Lemma lem2305811 (x : int) : (term19 x) = (int_add x x).
Proof. exact (EQ_MP (@lem2305810 x) (@lem2305789 x)). Qed.
Lemma lem2305812 : term20.
Proof. exact (fun x : int => @lem2305811 x). Qed.
