Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_MUL_SYM_term_abbrevs.
Require Import TREAL_EQ_AP_spec.
Require Import TREAL_MUL_SYM_EQ_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1328321 (x : prod hreal hreal) : term0 x.
Proof. exact (@lem1327751 x). Qed.
Lemma lem1328322 (x : prod hreal hreal) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1328323 (x : prod hreal hreal) : term1 x.
Proof. exact (EQ_MP (@lem1328322 x) (@lem1328321 x)). Qed.
Lemma lem1328324 (x : prod hreal hreal) (y : prod hreal hreal) : term2 x y.
Proof. exact (@lem1328323 x y). Qed.
Lemma lem1328325 (y : prod hreal hreal) (x : prod hreal hreal) : (term2 x y) = ((treal_mul x y) = (treal_mul y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1328327 (x : prod hreal hreal) : term3 x.
Proof. exact (@lem1326851 x). Qed.
Lemma lem1328328 (x : prod hreal hreal) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1328329 (x : prod hreal hreal) : term4 x.
Proof. exact (EQ_MP (@lem1328328 x) (@lem1328327 x)). Qed.
Lemma lem1328330 (x : prod hreal hreal) (y : prod hreal hreal) : term5 x y.
Proof. exact (@lem1328329 x y). Qed.
Lemma lem1328331 (x : prod hreal hreal) (y : prod hreal hreal) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1328332 (x : prod hreal hreal) (y : prod hreal hreal) : term6 x y.
Proof. exact (EQ_MP (@lem1328331 x y) (@lem1328330 x y)). Qed.
Lemma lem1328333 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : x = y.
Proof. exact (h1). Qed.
Lemma lem1328334 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : treal_eq x y.
Proof. exact (@lem1328332 x y (@lem1328333 x y h1)). Qed.
Lemma lem1328335 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_eq x y) = ((treal_eq x y) = True).
Proof. exact (@lem7 (treal_eq x y)). Qed.
Lemma lem1328336 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : x = y) : (treal_eq x y) = True.
Proof. exact (EQ_MP (@lem1328335 x y) (@lem1328334 x y h1)). Qed.
Lemma lem1328351 (x : prod hreal hreal) (y : prod hreal hreal) : term7 x y.
Proof. exact (fun h0 : x = y => @lem1328336 x y h0). Qed.
Lemma lem1328352 (y : prod hreal hreal) (x : prod hreal hreal) : term8 y x.
Proof. exact (@lem1328351 (treal_mul x y) (treal_mul y x)). Qed.
Lemma lem1328358 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_mul x y) = (treal_mul y x).
Proof. exact (EQ_MP (@lem1328325 y x) (@lem1328324 x y)). Qed.
Lemma lem1328359 (x : prod hreal hreal) (y : prod hreal hreal) : (treal_mul y x) = (treal_mul x y).
Proof. exact (@lem1328358 x y). Qed.
Lemma lem1328362 (x : prod hreal hreal) (y : prod hreal hreal) : (term9 x y) = (term9 x y).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1328363 (x : prod hreal hreal) (y : prod hreal hreal) : ((treal_mul x y) = (treal_mul y x)) = ((treal_mul x y) = (treal_mul x y)).
Proof. exact (MK_COMB (@lem1328362 x y) (@lem1328359 x y)). Qed.
Lemma lem1328365 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1328366 (x : prod hreal hreal) : (x = x) = True.
Proof. exact (@lem1328365 (prod hreal hreal) x). Qed.
Lemma lem1328367 (x : prod hreal hreal) (y : prod hreal hreal) : ((treal_mul x y) = (treal_mul x y)) = True.
Proof. exact (@lem1328366 (treal_mul x y)). Qed.
Lemma lem1328368 (y : prod hreal hreal) (x : prod hreal hreal) : ((treal_mul x y) = (treal_mul y x)) = True.
Proof. exact (TRANS (@lem1328363 x y) (@lem1328367 x y)). Qed.
Lemma lem1328369 (y : prod hreal hreal) (x : prod hreal hreal) : True = ((treal_mul x y) = (treal_mul y x)).
Proof. exact (SYM (@lem1328368 y x)). Qed.
Lemma lem1328370 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_mul x y) = (treal_mul y x).
Proof. exact (EQ_MP (@lem1328369 y x) (@lem0)). Qed.
Lemma lem1328371 (y : prod hreal hreal) (x : prod hreal hreal) : (term10 y x) = True.
Proof. exact (@lem1328352 y x (@lem1328370 y x)). Qed.
Lemma lem1328372 (x : prod hreal hreal) : (term11 x) = term12.
Proof. exact (fun_ext (fun y : prod hreal hreal => @lem1328371 y x)). Qed.
Lemma lem1328373 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1328374 (x : prod hreal hreal) : (term13 x) = term14.
Proof. exact (MK_COMB (@lem1328373) (@lem1328372 x)). Qed.
Lemma lem1328376 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328377 (t : Prop) : (term16 t) = t.
Proof. exact (@lem1328376 (prod hreal hreal) t). Qed.
Lemma lem1328378 : term14 = True.
Proof. exact (@lem1328377 True). Qed.
Lemma lem1328379 (x : prod hreal hreal) : (term13 x) = True.
Proof. exact (TRANS (@lem1328374 x) (@lem1328378)). Qed.
Lemma lem1328380 : term17 = term12.
Proof. exact (fun_ext (fun x : prod hreal hreal => @lem1328379 x)). Qed.
Lemma lem1328381 : (@all (prod hreal hreal)) = (@all (prod hreal hreal)).
Proof. exact (eq_refl (@all (prod hreal hreal))). Qed.
Lemma lem1328382 : term18 = term14.
Proof. exact (MK_COMB (@lem1328381) (@lem1328380)). Qed.
Lemma lem1328384 {A : Type'} (t : Prop) : (term15 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1328385 (t : Prop) : (term16 t) = t.
Proof. exact (@lem1328384 (prod hreal hreal) t). Qed.
Lemma lem1328386 : term14 = True.
Proof. exact (@lem1328385 True). Qed.
Lemma lem1328387 : term18 = True.
Proof. exact (TRANS (@lem1328382) (@lem1328386)). Qed.
Lemma lem1328388 : True = term18.
Proof. exact (SYM (@lem1328387)). Qed.
Lemma lem1328389 : term18.
Proof. exact (EQ_MP (@lem1328388) (@lem0)). Qed.
