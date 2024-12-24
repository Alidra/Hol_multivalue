Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_eq_term_abbrevs.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2267744_spec.
Require Import thm2267745_spec.
Require Import thm32_spec.
Lemma lem2268355 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2268357 (x : int) (y : int) (h1 : (real_of_int x) = (real_of_int y)) : (real_of_int x) = (real_of_int y).
Proof. exact (h1). Qed.
Lemma lem2268361 (x : int) (y : int) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem2268362 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2268363 (x : int) (y : int) (h1 : x = y) : (real_of_int x) = (real_of_int y).
Proof. exact (MK_COMB (@lem2268362) (@lem2268361 x y h1)). Qed.
Lemma lem2268364 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2268365 (x : int) (y : int) (h1 : x = y) : (term0 x) = (term0 y).
Proof. exact (MK_COMB (@lem2268364) (@lem2268363 x y h1)). Qed.
Lemma lem2268366 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2268367 (x : int) (y : int) (h1 : x = y) : ((real_of_int x) = (real_of_int y)) = ((real_of_int y) = (real_of_int y)).
Proof. exact (MK_COMB (@lem2268365 x y h1) (@lem2268366 y)). Qed.
Lemma lem2268369 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2268370 (x : real) : (x = x) = True.
Proof. exact (@lem2268369 real x). Qed.
Lemma lem2268371 (y : int) : ((real_of_int y) = (real_of_int y)) = True.
Proof. exact (@lem2268370 (real_of_int y)). Qed.
Lemma lem2268372 (x : int) (y : int) (h1 : x = y) : ((real_of_int x) = (real_of_int y)) = True.
Proof. exact (TRANS (@lem2268367 x y h1) (@lem2268371 y)). Qed.
Lemma lem2268373 (x : int) (y : int) (h1 : x = y) : True = ((real_of_int x) = (real_of_int y)).
Proof. exact (SYM (@lem2268372 x y h1)). Qed.
Lemma lem2268374 (x : int) (y : int) (h1 : x = y) : (real_of_int x) = (real_of_int y).
Proof. exact (EQ_MP (@lem2268373 x y h1) (@lem0)). Qed.
Lemma lem2268379 (x : int) (y : int) (h1 : (real_of_int x) = (real_of_int y)) : (term1 x) = (term1 y).
Proof. exact (MK_COMB (@lem2268355) (@lem2268357 x y h1)). Qed.
Lemma lem2268387 (a : int) : (term1 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2268388 (x : int) : (term1 x) = x.
Proof. exact (@lem2268387 x). Qed.
Lemma lem2268389 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2268390 (x : int) : (term2 x) = (@eq int x).
Proof. exact (MK_COMB (@lem2268389) (@lem2268388 x)). Qed.
Lemma lem2268392 (a : int) : (term1 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2268393 (y : int) : (term1 y) = y.
Proof. exact (@lem2268392 y). Qed.
Lemma lem2268394 (x : int) (y : int) : ((term1 x) = (term1 y)) = (x = y).
Proof. exact (MK_COMB (@lem2268390 x) (@lem2268393 y)). Qed.
Lemma lem2268397 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem2268398 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (MK_COMB (@lem2268397) (@lem2268394 x y)). Qed.
Lemma lem2268401 (x : int) (y : int) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem2268402 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2268398 x y) (@lem2268401 x y)). Qed.
Lemma lem2268406 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem2268407 (x : int) (y : int) : (term6 x y) = True.
Proof. exact (@lem2268406 (x = y)). Qed.
Lemma lem2268408 (x : int) (y : int) : (term5 x y) = True.
Proof. exact (TRANS (@lem2268402 x y) (@lem2268407 x y)). Qed.
Lemma lem2268409 (x : int) (y : int) : True = (term5 x y).
Proof. exact (SYM (@lem2268408 x y)). Qed.
Lemma lem2268410 (x : int) (y : int) : term5 x y.
Proof. exact (EQ_MP (@lem2268409 x y) (@lem0)). Qed.
Lemma lem2268412 (x : int) (y : int) (h1 : (real_of_int x) = (real_of_int y)) : x = y.
Proof. exact (@lem2268410 x y (@lem2268379 x y h1)). Qed.
Lemma lem2268413 (x : int) (y : int) : term7 x y.
Proof. exact (fun h0 : (real_of_int x) = (real_of_int y) => @lem2268412 x y h0). Qed.
Lemma lem2268414 (x : int) (y : int) : term8 x y.
Proof. exact (fun h0 : x = y => @lem2268374 x y h0). Qed.
Lemma lem2268415 (x : int) (y : int) : term9 x y.
Proof. exact (conj (@lem2268414 x y) (@lem2268413 x y)). Qed.
Lemma lem2268416 (x : int) (y : int) : (term9 x y) = ((x = y) = ((real_of_int x) = (real_of_int y))).
Proof. exact (@lem32 (x = y) ((real_of_int x) = (real_of_int y))). Qed.
Lemma lem2268417 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2268416 x y) (@lem2268415 x y)). Qed.
Lemma lem2268422 (x : int) : term10 x.
Proof. exact (fun y : int => @lem2268417 x y). Qed.
Lemma lem2268427 : term11.
Proof. exact (fun x : int => @lem2268422 x). Qed.
