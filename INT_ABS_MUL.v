Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_ABS_MUL_term_abbrevs.
Require Import REAL_ABS_MUL_spec.
Require Import thm2299891_spec.
Require Import thm2299892_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2300395 (x : int) : term0 x.
Proof. exact (@lem1582313 (real_of_int x)). Qed.
Lemma lem2300396 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2300397 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2300396 x) (@lem2300395 x)). Qed.
Lemma lem2300398 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2300397 x (real_of_int y)). Qed.
Lemma lem2300399 (x : int) (y : int) : (term2 x y) = ((term3 x y) = (term4 x y)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2300400 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2300399 x y) (@lem2300398 x y)). Qed.
Lemma lem2300402 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2300403 : real_abs = real_abs.
Proof. exact (eq_refl real_abs). Qed.
Lemma lem2300404 (x : int) (y : int) : (term3 x y) = (term7 x y).
Proof. exact (MK_COMB (@lem2300403) (@lem2300402 x y)). Qed.
Lemma lem2300406 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300407 (x : int) (y : int) : (term7 x y) = (term10 x y).
Proof. exact (@lem2300406 (int_mul x y)). Qed.
Lemma lem2300408 (x : int) (y : int) : (term3 x y) = (term10 x y).
Proof. exact (TRANS (@lem2300404 x y) (@lem2300407 x y)). Qed.
Lemma lem2300409 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2300410 (x : int) (y : int) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem2300409) (@lem2300408 x y)). Qed.
Lemma lem2300412 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300413 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2300414 (x : int) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem2300413) (@lem2300412 x)). Qed.
Lemma lem2300416 (x : int) : (term8 x) = (term9 x).
Proof. exact (EQ_MP (@lem2299892 x) (@lem2299891 x)). Qed.
Lemma lem2300417 (y : int) : (term8 y) = (term9 y).
Proof. exact (@lem2300416 y). Qed.
Lemma lem2300418 (x : int) (y : int) : (term4 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem2300414 x) (@lem2300417 y)). Qed.
Lemma lem2300420 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2300421 (x : int) (y : int) : (term15 x y) = (term16 x y).
Proof. exact (@lem2300420 (int_abs x) (int_abs y)). Qed.
Lemma lem2300422 (x : int) (y : int) : (term4 x y) = (term16 x y).
Proof. exact (TRANS (@lem2300418 x y) (@lem2300421 x y)). Qed.
Lemma lem2300423 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term10 x y) = (term16 x y)).
Proof. exact (MK_COMB (@lem2300410 x y) (@lem2300422 x y)). Qed.
Lemma lem2300425 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2300426 (x : int) (y : int) : ((term10 x y) = (term16 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (@lem2300425 (term17 x y) (term18 x y)). Qed.
Lemma lem2300427 (x : int) (y : int) : ((term3 x y) = (term4 x y)) = ((term17 x y) = (term18 x y)).
Proof. exact (TRANS (@lem2300423 x y) (@lem2300426 x y)). Qed.
Lemma lem2300428 (x : int) (y : int) : (term17 x y) = (term18 x y).
Proof. exact (EQ_MP (@lem2300427 x y) (@lem2300400 x y)). Qed.
Lemma lem2300429 (x : int) : term19 x.
Proof. exact (fun y : int => @lem2300428 x y). Qed.
Lemma lem2300430 : term20.
Proof. exact (fun x : int => @lem2300429 x). Qed.
