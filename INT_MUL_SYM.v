Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_MUL_SYM_term_abbrevs.
Require Import thm1338712_spec.
Require Import thm2299906_spec.
Require Import thm2299907_spec.
Require Import thm2299948_spec.
Require Import thm2299949_spec.
Lemma lem2306291 (x : int) : term0 x.
Proof. exact (@lem1338712 (real_of_int x)). Qed.
Lemma lem2306292 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2306293 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2306292 x) (@lem2306291 x)). Qed.
Lemma lem2306294 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2306293 x (real_of_int y)). Qed.
Lemma lem2306295 (y : int) (x : int) : (term2 x y) = ((term3 x y) = (term3 y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2306296 (y : int) (x : int) : (term3 x y) = (term3 y x).
Proof. exact (EQ_MP (@lem2306295 y x) (@lem2306294 x y)). Qed.
Lemma lem2306298 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306299 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2306300 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2306299) (@lem2306298 x y)). Qed.
Lemma lem2306302 (x : int) (y : int) : (term3 x y) = (term4 x y).
Proof. exact (EQ_MP (@lem2299907 x y) (@lem2299906 x y)). Qed.
Lemma lem2306303 (y : int) (x : int) : (term3 y x) = (term4 y x).
Proof. exact (@lem2306302 y x). Qed.
Lemma lem2306304 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((term4 x y) = (term4 y x)).
Proof. exact (MK_COMB (@lem2306300 x y) (@lem2306303 y x)). Qed.
Lemma lem2306306 (x : int) (y : int) : ((real_of_int x) = (real_of_int y)) = (x = y).
Proof. exact (EQ_MP (@lem2299949 x y) (@lem2299948 x y)). Qed.
Lemma lem2306307 (y : int) (x : int) : ((term4 x y) = (term4 y x)) = ((int_mul x y) = (int_mul y x)).
Proof. exact (@lem2306306 (int_mul x y) (int_mul y x)). Qed.
Lemma lem2306308 (y : int) (x : int) : ((term3 x y) = (term3 y x)) = ((int_mul x y) = (int_mul y x)).
Proof. exact (TRANS (@lem2306304 y x) (@lem2306307 y x)). Qed.
Lemma lem2306309 (y : int) (x : int) : (int_mul x y) = (int_mul y x).
Proof. exact (EQ_MP (@lem2306308 y x) (@lem2306296 y x)). Qed.
Lemma lem2306310 (x : int) : term7 x.
Proof. exact (fun y : int => @lem2306309 y x). Qed.
Lemma lem2306311 : term8.
Proof. exact (fun x : int => @lem2306310 x). Qed.
