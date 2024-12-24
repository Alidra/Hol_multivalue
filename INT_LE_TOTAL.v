Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_TOTAL_term_abbrevs.
Require Import thm1339697_spec.
Require Import thm2299942_spec.
Require Import thm2299943_spec.
Lemma lem2303407 (x : int) : term0 x.
Proof. exact (@lem1339697 (real_of_int x)). Qed.
Lemma lem2303408 (x : int) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem2303409 (x : int) : term1 x.
Proof. exact (EQ_MP (@lem2303408 x) (@lem2303407 x)). Qed.
Lemma lem2303410 (x : int) (y : int) : term2 x y.
Proof. exact (@lem2303409 x (real_of_int y)). Qed.
Lemma lem2303411 (y : int) (x : int) : (term2 x y) = (term3 y x).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem2303412 (y : int) (x : int) : term3 y x.
Proof. exact (EQ_MP (@lem2303411 y x) (@lem2303410 x y)). Qed.
Lemma lem2303414 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303415 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2303416 (x : int) (y : int) : (term5 x y) = (term6 x y).
Proof. exact (MK_COMB (@lem2303415) (@lem2303414 x y)). Qed.
Lemma lem2303418 (x : int) (y : int) : (term4 x y) = (int_le x y).
Proof. exact (EQ_MP (@lem2299943 x y) (@lem2299942 x y)). Qed.
Lemma lem2303419 (y : int) (x : int) : (term4 y x) = (int_le y x).
Proof. exact (@lem2303418 y x). Qed.
Lemma lem2303420 (y : int) (x : int) : (term3 y x) = (term7 y x).
Proof. exact (MK_COMB (@lem2303416 x y) (@lem2303419 y x)). Qed.
Lemma lem2303421 (y : int) (x : int) : term7 y x.
Proof. exact (EQ_MP (@lem2303420 y x) (@lem2303412 y x)). Qed.
Lemma lem2303422 (x : int) : term8 x.
Proof. exact (fun y : int => @lem2303421 y x). Qed.
Lemma lem2303423 : term9.
Proof. exact (fun x : int => @lem2303422 x). Qed.
