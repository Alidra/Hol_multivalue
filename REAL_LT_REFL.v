Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_REFL_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1339240_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm7_spec.
Lemma lem1379382 (x : real) : term0 x.
Proof. exact (@lem1339240 x). Qed.
Lemma lem1379383 (x : real) : (term0 x) = (real_le x x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1379384 (x : real) : real_le x x.
Proof. exact (EQ_MP (@lem1379383 x) (@lem1379382 x)). Qed.
Lemma lem1379385 (x : real) : (real_le x x) = ((real_le x x) = True).
Proof. exact (@lem7 (real_le x x)). Qed.
Lemma lem1379387 (y : real) : term1 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1379388 (y : real) : (term1 y) = (term2 y).
Proof. exact (eq_refl (term1 y)). Qed.
Lemma lem1379389 (y : real) : term2 y.
Proof. exact (EQ_MP (@lem1379388 y) (@lem1379387 y)). Qed.
Lemma lem1379390 (y : real) (x : real) : term3 y x.
Proof. exact (@lem1379389 y x). Qed.
Lemma lem1379391 (y : real) (x : real) : (term3 y x) = ((real_lt x y) = (term4 y x)).
Proof. exact (eq_refl (term3 y x)). Qed.
Lemma lem1379398 (y : real) (x : real) : (real_lt x y) = (term4 y x).
Proof. exact (EQ_MP (@lem1379391 y x) (@lem1379390 y x)). Qed.
Lemma lem1379399 (x : real) : (real_lt x x) = (term5 x).
Proof. exact (@lem1379398 x x). Qed.
Lemma lem1379401 (x : real) : (real_le x x) = True.
Proof. exact (EQ_MP (@lem1379385 x) (@lem1379384 x)). Qed.
Lemma lem1379402 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1379403 (x : real) : (term5 x) = (~ True).
Proof. exact (MK_COMB (@lem1379402) (@lem1379401 x)). Qed.
Lemma lem1379405 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1379406 (x : real) : (term5 x) = False.
Proof. exact (TRANS (@lem1379403 x) (@lem1379405)). Qed.
Lemma lem1379407 (x : real) : (real_lt x x) = False.
Proof. exact (TRANS (@lem1379399 x) (@lem1379406 x)). Qed.
Lemma lem1379408 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1379409 (x : real) : (term6 x) = (~ False).
Proof. exact (MK_COMB (@lem1379408) (@lem1379407 x)). Qed.
Lemma lem1379411 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1379412 (x : real) : (term6 x) = True.
Proof. exact (TRANS (@lem1379409 x) (@lem1379411)). Qed.
Lemma lem1379413 : term7 = term8.
Proof. exact (fun_ext (fun x : real => @lem1379412 x)). Qed.
Lemma lem1379414 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1379415 : term9 = term10.
Proof. exact (MK_COMB (@lem1379414) (@lem1379413)). Qed.
Lemma lem1379417 {A : Type'} (t : Prop) : (term11 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1379418 (t : Prop) : (term12 t) = t.
Proof. exact (@lem1379417 real t). Qed.
Lemma lem1379419 : term10 = True.
Proof. exact (@lem1379418 True). Qed.
Lemma lem1379420 : term9 = True.
Proof. exact (TRANS (@lem1379415) (@lem1379419)). Qed.
Lemma lem1379421 : True = term9.
Proof. exact (SYM (@lem1379420)). Qed.
Lemma lem1379422 : term9.
Proof. exact (EQ_MP (@lem1379421) (@lem0)). Qed.
