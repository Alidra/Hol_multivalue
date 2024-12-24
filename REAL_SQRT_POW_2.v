Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SQRT_POW_2_term_abbrevs.
Require Import SQRT_WORKS_GEN_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1968360 (x : real) : term0 x.
Proof. exact (@lem1919069 x). Qed.
Lemma lem1968361 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1968362 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1968361 x) (@lem1968360 x)). Qed.
Lemma lem1968372 (x : real) : (term2 x) = (real_abs x).
Proof. exact (proj2 (@lem1968362 x)). Qed.
Lemma lem1968373 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1968374 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1968373) (@lem1968372 x)). Qed.
Lemma lem1968375 (x : real) : (real_abs x) = (real_abs x).
Proof. exact (eq_refl (real_abs x)). Qed.
Lemma lem1968376 (x : real) : ((term2 x) = (real_abs x)) = ((real_abs x) = (real_abs x)).
Proof. exact (MK_COMB (@lem1968374 x) (@lem1968375 x)). Qed.
Lemma lem1968378 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1968379 (x : real) : (x = x) = True.
Proof. exact (@lem1968378 real x). Qed.
Lemma lem1968380 (x : real) : ((real_abs x) = (real_abs x)) = True.
Proof. exact (@lem1968379 (real_abs x)). Qed.
Lemma lem1968381 (x : real) : ((term2 x) = (real_abs x)) = True.
Proof. exact (TRANS (@lem1968376 x) (@lem1968380 x)). Qed.
Lemma lem1968382 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1968381 x)). Qed.
Lemma lem1968383 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1968384 : term7 = term8.
Proof. exact (MK_COMB (@lem1968383) (@lem1968382)). Qed.
Lemma lem1968386 {A : Type'} (t : Prop) : (term9 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1968387 (t : Prop) : (term10 t) = t.
Proof. exact (@lem1968386 real t). Qed.
Lemma lem1968388 : term8 = True.
Proof. exact (@lem1968387 True). Qed.
Lemma lem1968389 : term7 = True.
Proof. exact (TRANS (@lem1968384) (@lem1968388)). Qed.
Lemma lem1968390 : True = term7.
Proof. exact (SYM (@lem1968389)). Qed.
Lemma lem1968391 : term7.
Proof. exact (EQ_MP (@lem1968390) (@lem0)). Qed.
