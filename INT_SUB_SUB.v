Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_SUB_SUB_term_abbrevs.
Require Import REAL_SUB_SUB_spec.
Require Import thm2299897_spec.
Require Import thm2299898_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2310447 (x : int) : term0 x.
Proof. exact (@lem1512089 (real_of_int x)). Qed.
Lemma lem2310448 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2310449 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2310448 x) (@lem2310447 x)). Qed.
Lemma lem2310450 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2310449 x (real_of_int y)). Qed.
Lemma lem2310451 (x : int) (y : int) : (term2 x y) = ((term3 y x) = (term4 y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2310452 (x : int) (y : int) : (term3 y x) = (term4 y).
Proof. exact (EQ_MP (@lem2310451 x y) (@lem2310450 x y)). Qed.
Lemma lem2310454 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310455 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2310456 (x : int) (y : int) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem2310455) (@lem2310454 x y)). Qed.
Lemma lem2310457 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2310458 (y : int) (x : int) : (term3 y x) = (term9 y x).
Proof. exact (MK_COMB (@lem2310456 x y) (@lem2310457 x)). Qed.
Lemma lem2310460 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299898 x y) (@lem2299897 x y)). Qed.
Lemma lem2310461 (y : int) (x : int) : (term9 y x) = (term10 y x).
Proof. exact (@lem2310460 (int_sub x y) x). Qed.
Lemma lem2310462 (y : int) (x : int) : (term3 y x) = (term10 y x).
Proof. exact (TRANS (@lem2310458 y x) (@lem2310461 y x)). Qed.
Lemma lem2310463 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2310464 (y : int) (x : int) : (term11 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem2310463) (@lem2310462 y x)). Qed.
Lemma lem2310466 (x : int) : (term4 x) = (term13 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2310467 (y : int) : (term4 y) = (term13 y).
Proof. exact (@lem2310466 y). Qed.
Lemma lem2310468 (x : int) (y : int) : ((term3 y x) = (term4 y)) = ((term10 y x) = (term13 y)).
Proof. exact (MK_COMB (@lem2310464 y x) (@lem2310467 y)). Qed.
Lemma lem2310470 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2310471 (x : int) (y : int) : ((term10 y x) = (term13 y)) = ((term14 y x) = (int_neg y)).
Proof. exact (@lem2310470 (term14 y x) (int_neg y)). Qed.
Lemma lem2310472 (x : int) (y : int) : ((term3 y x) = (term4 y)) = ((term14 y x) = (int_neg y)).
Proof. exact (TRANS (@lem2310468 x y) (@lem2310471 x y)). Qed.
Lemma lem2310473 (x : int) (y : int) : (term14 y x) = (int_neg y).
Proof. exact (EQ_MP (@lem2310472 x y) (@lem2310452 x y)). Qed.
Lemma lem2310474 (x : int) : term15 x.
Proof. exact (fun y : int => @lem2310473 x y). Qed.
Lemma lem2310475 : term16.
Proof. exact (fun x : int => @lem2310474 x). Qed.
