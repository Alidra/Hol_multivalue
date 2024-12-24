Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LT_term_abbrevs.
Require Import int_le_spec.
Require Import int_lt_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2318307 (y : real) : term0 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem2318308 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem2318309 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem2318308 y) (@lem2318307 y)). Qed.
Lemma lem2318310 (y : real) (x : real) : term2 y x.
Proof. exact (@lem2318309 y x). Qed.
Lemma lem2318311 (y : real) (x : real) : (term2 y x) = ((real_lt x y) = (term3 y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem2318313 (x : int) : term4 x.
Proof. exact (@lem2269094 x). Qed.
Lemma lem2318314 (x : int) : (term4 x) = (term5 x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem2318315 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2318314 x) (@lem2318313 x)). Qed.
Lemma lem2318316 (x : int) (y : int) : term6 x y.
Proof. exact (@lem2318315 x y). Qed.
Lemma lem2318317 (x : int) (y : int) : (term6 x y) = ((int_le x y) = (term7 x y)).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem2318319 (x : int) : term8 x.
Proof. exact (@lem2269769 x). Qed.
Lemma lem2318320 (x : int) : (term8 x) = (term9 x).
Proof. exact (eq_refl (term8 x)). Qed.
Lemma lem2318321 (x : int) : term9 x.
Proof. exact (EQ_MP (@lem2318320 x) (@lem2318319 x)). Qed.
Lemma lem2318322 (x : int) (y : int) : term10 x y.
Proof. exact (@lem2318321 x y). Qed.
Lemma lem2318323 (x : int) (y : int) : (term10 x y) = ((int_lt x y) = (term11 x y)).
Proof. exact (eq_refl (term10 x y)). Qed.
Lemma lem2318336 (x : int) (y : int) : (int_lt x y) = (term11 x y).
Proof. exact (EQ_MP (@lem2318323 x y) (@lem2318322 x y)). Qed.
Lemma lem2318338 (y : real) (x : real) : (real_lt x y) = (term3 y x).
Proof. exact (EQ_MP (@lem2318311 y x) (@lem2318310 y x)). Qed.
Lemma lem2318339 (y : int) (x : int) : (term11 x y) = (term12 y x).
Proof. exact (@lem2318338 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2318340 (y : int) (x : int) : (int_lt x y) = (term12 y x).
Proof. exact (TRANS (@lem2318336 x y) (@lem2318339 y x)). Qed.
Lemma lem2318341 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318342 (y : int) (x : int) : (term13 x y) = (term14 y x).
Proof. exact (MK_COMB (@lem2318341) (@lem2318340 y x)). Qed.
Lemma lem2318344 (x : int) (y : int) : (int_le x y) = (term7 x y).
Proof. exact (EQ_MP (@lem2318317 x y) (@lem2318316 x y)). Qed.
Lemma lem2318345 (y : int) (x : int) : (int_le y x) = (term7 y x).
Proof. exact (@lem2318344 y x). Qed.
Lemma lem2318346 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2318347 (y : int) (x : int) : (term15 y x) = (term12 y x).
Proof. exact (MK_COMB (@lem2318346) (@lem2318345 y x)). Qed.
Lemma lem2318348 (y : int) (x : int) : ((int_lt x y) = (term15 y x)) = ((term12 y x) = (term12 y x)).
Proof. exact (MK_COMB (@lem2318342 y x) (@lem2318347 y x)). Qed.
Lemma lem2318350 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318351 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318350 Prop x). Qed.
Lemma lem2318352 (y : int) (x : int) : ((term12 y x) = (term12 y x)) = True.
Proof. exact (@lem2318351 (term12 y x)). Qed.
Lemma lem2318353 (y : int) (x : int) : ((int_lt x y) = (term15 y x)) = True.
Proof. exact (TRANS (@lem2318348 y x) (@lem2318352 y x)). Qed.
Lemma lem2318354 (x : int) : (term16 x) = term17.
Proof. exact (fun_ext (fun y : int => @lem2318353 y x)). Qed.
Lemma lem2318355 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2318356 (x : int) : (term18 x) = term19.
Proof. exact (MK_COMB (@lem2318355) (@lem2318354 x)). Qed.
Lemma lem2318358 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2318359 (t : Prop) : (term21 t) = t.
Proof. exact (@lem2318358 int t). Qed.
Lemma lem2318360 : term19 = True.
Proof. exact (@lem2318359 True). Qed.
Lemma lem2318361 (x : int) : (term18 x) = True.
Proof. exact (TRANS (@lem2318356 x) (@lem2318360)). Qed.
Lemma lem2318362 : term22 = term17.
Proof. exact (fun_ext (fun x : int => @lem2318361 x)). Qed.
Lemma lem2318363 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2318364 : term23 = term19.
Proof. exact (MK_COMB (@lem2318363) (@lem2318362)). Qed.
Lemma lem2318366 {A : Type'} (t : Prop) : (term20 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2318367 (t : Prop) : (term21 t) = t.
Proof. exact (@lem2318366 int t). Qed.
Lemma lem2318368 : term19 = True.
Proof. exact (@lem2318367 True). Qed.
Lemma lem2318369 : term23 = True.
Proof. exact (TRANS (@lem2318364) (@lem2318368)). Qed.
Lemma lem2318370 : True = term23.
Proof. exact (SYM (@lem2318369)). Qed.
Lemma lem2318371 : term23.
Proof. exact (EQ_MP (@lem2318370) (@lem0)). Qed.
