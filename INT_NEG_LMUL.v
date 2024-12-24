Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_NEG_LMUL_term_abbrevs.
Require Import REAL_NEG_LMUL_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299915_spec.
Require Import thm2299916_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306517 (x : int) : term0 x.
Proof. exact (@lem1491418 (real_of_int x)). Qed.
Lemma lem2306518 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306519 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306518 x) (@lem2306517 x)). Qed.
Lemma lem2306520 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306519 x (real_of_int y)). Qed.
Lemma lem2306521 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306522 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2306521 x y) (@lem2306520 x y)). Qed.
Lemma lem2306524 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306525 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2306526 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2306525) (@lem2306524 x y)). Qed.
Lemma lem2306528 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306529 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2306528 (int_mul x y)). Qed.
Lemma lem2306530 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2306526 x y) (@lem2306529 x y)). Qed.
Lemma lem2306531 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306532 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2306531) (@lem2306530 x y)). Qed.
Lemma lem2306534 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299916 x) (@lem2299915 x)). Qed.
Lemma lem2306535 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2306536 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2306535) (@lem2306534 x)). Qed.
Lemma lem2306537 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2306538 (x : int) (y : int) : (term4 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2306536 x) (@lem2306537 y)). Qed.
Lemma lem2306540 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306541 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (@lem2306540 (int_neg x) y). Qed.
Lemma lem2306542 (x : int) (y : int) : (term4 x y) = (term16 x y).
Proof. exact (TRANS (@lem2306538 x y) (@lem2306541 x y)). Qed.
Lemma lem2306543 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term10 x y) = (term16 x y)).
Proof. exact (MK_COMB (@lem2306532 x y) (@lem2306542 x y)). Qed.
Lemma lem2306545 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306546 (x : int) (y : int) : ((term10 x y) = (term16 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (@lem2306545 (term17 x y) (term18 x y)). Qed.
Lemma lem2306547 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (TRANS (@lem2306543 x y) (@lem2306546 x y)). Qed.
Lemma lem2306548 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2306547 x y) (@lem2306522 x y)). Qed.
Lemma lem2306549 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2306548 x y). Qed.
Lemma lem2306550 : term20.
Proof. exact (fun x : int => @lem2306549 x). Qed.
