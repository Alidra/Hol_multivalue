Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm22403_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem22297 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem22298 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem22299 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem22298 a) (@lem22297 a)). Qed.
Lemma lem22300 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem22301 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem22310 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem22311 (b : Prop) (a : Prop) (h1 : a = True) : (term3 b a) = (term4 b).
Proof. exact (MK_COMB (@lem22310 b) (@lem22300 a h1)). Qed.
Lemma lem22312 (b : Prop) : (term4 b) = ((term5 b) = (True \/ b)).
Proof. exact (eq_refl (term4 b)). Qed.
Lemma lem22313 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem22314 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = ((term3 b a) = ((term5 b) = (True \/ b))).
Proof. exact (MK_COMB (@lem22313 b a) (@lem22312 b)). Qed.
Lemma lem22315 (a : Prop) (b : Prop) : (term3 b a) = ((term7 a b) = (a \/ b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem22316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22317 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem22316) (@lem22315 a b)). Qed.
Lemma lem22318 (b : Prop) : ((term5 b) = (True \/ b)) = ((term5 b) = (True \/ b)).
Proof. exact (eq_refl ((term5 b) = (True \/ b))). Qed.
Lemma lem22319 (a : Prop) (b : Prop) : ((term3 b a) = ((term5 b) = (True \/ b))) = (((term7 a b) = (a \/ b)) = ((term5 b) = (True \/ b))).
Proof. exact (MK_COMB (@lem22317 a b) (@lem22318 b)). Qed.
Lemma lem22320 (a : Prop) (b : Prop) : ((term3 b a) = (term4 b)) = (((term7 a b) = (a \/ b)) = ((term5 b) = (True \/ b))).
Proof. exact (TRANS (@lem22314 a b) (@lem22319 a b)). Qed.
Lemma lem22321 (b : Prop) (a : Prop) (h1 : a = True) : ((term7 a b) = (a \/ b)) = ((term5 b) = (True \/ b)).
Proof. exact (EQ_MP (@lem22320 a b) (@lem22311 b a h1)). Qed.
Lemma lem22322 (b : Prop) (a : Prop) (h1 : a = True) : ((term5 b) = (True \/ b)) = ((term7 a b) = (a \/ b)).
Proof. exact (SYM (@lem22321 b a h1)). Qed.
Lemma lem22323 (b : Prop) : (term2 b) = (term2 b).
Proof. exact (eq_refl (term2 b)). Qed.
Lemma lem22324 (b : Prop) (a : Prop) (h1 : a = False) : (term3 b a) = (term9 b).
Proof. exact (MK_COMB (@lem22323 b) (@lem22301 a h1)). Qed.
Lemma lem22325 (b : Prop) : (term9 b) = ((term10 b) = (False \/ b)).
Proof. exact (eq_refl (term9 b)). Qed.
Lemma lem22326 (b : Prop) (a : Prop) : (term6 b a) = (term6 b a).
Proof. exact (eq_refl (term6 b a)). Qed.
Lemma lem22327 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = ((term3 b a) = ((term10 b) = (False \/ b))).
Proof. exact (MK_COMB (@lem22326 b a) (@lem22325 b)). Qed.
Lemma lem22328 (a : Prop) (b : Prop) : (term3 b a) = ((term7 a b) = (a \/ b)).
Proof. exact (eq_refl (term3 b a)). Qed.
Lemma lem22329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22330 (a : Prop) (b : Prop) : (term6 b a) = (term8 a b).
Proof. exact (MK_COMB (@lem22329) (@lem22328 a b)). Qed.
Lemma lem22331 (b : Prop) : ((term10 b) = (False \/ b)) = ((term10 b) = (False \/ b)).
Proof. exact (eq_refl ((term10 b) = (False \/ b))). Qed.
Lemma lem22332 (a : Prop) (b : Prop) : ((term3 b a) = ((term10 b) = (False \/ b))) = (((term7 a b) = (a \/ b)) = ((term10 b) = (False \/ b))).
Proof. exact (MK_COMB (@lem22330 a b) (@lem22331 b)). Qed.
Lemma lem22333 (a : Prop) (b : Prop) : ((term3 b a) = (term9 b)) = (((term7 a b) = (a \/ b)) = ((term10 b) = (False \/ b))).
Proof. exact (TRANS (@lem22327 a b) (@lem22332 a b)). Qed.
Lemma lem22334 (b : Prop) (a : Prop) (h1 : a = False) : ((term7 a b) = (a \/ b)) = ((term10 b) = (False \/ b)).
Proof. exact (EQ_MP (@lem22333 a b) (@lem22324 b a h1)). Qed.
Lemma lem22335 (b : Prop) (a : Prop) (h1 : a = False) : ((term10 b) = (False \/ b)) = ((term7 a b) = (a \/ b)).
Proof. exact (SYM (@lem22334 b a h1)). Qed.
Lemma lem22341 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem22342 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem22343 : term11 = (imp False).
Proof. exact (MK_COMB (@lem22342) (@lem22341)). Qed.
Lemma lem22344 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem22345 (b : Prop) : (term5 b) = (False -> b).
Proof. exact (MK_COMB (@lem22343) (@lem22344 b)). Qed.
Lemma lem22347 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem22348 (b : Prop) : (False -> b) = True.
Proof. exact (@lem22347 b). Qed.
Lemma lem22349 (b : Prop) : (term5 b) = True.
Proof. exact (TRANS (@lem22345 b) (@lem22348 b)). Qed.
Lemma lem22350 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22351 (b : Prop) : (term12 b) = (@eq Prop True).
Proof. exact (MK_COMB (@lem22350) (@lem22349 b)). Qed.
Lemma lem22353 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem22354 (b : Prop) : (True \/ b) = True.
Proof. exact (@lem22353 b). Qed.
Lemma lem22355 (b : Prop) : ((term5 b) = (True \/ b)) = (True = True).
Proof. exact (MK_COMB (@lem22351 b) (@lem22354 b)). Qed.
Lemma lem22357 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem22358 : (True = True) = True.
Proof. exact (@lem22357 True). Qed.
Lemma lem22359 (b : Prop) : ((term5 b) = (True \/ b)) = True.
Proof. exact (TRANS (@lem22355 b) (@lem22358)). Qed.
Lemma lem22360 (b : Prop) : True = ((term5 b) = (True \/ b)).
Proof. exact (SYM (@lem22359 b)). Qed.
Lemma lem22361 (b : Prop) : (term5 b) = (True \/ b).
Proof. exact (EQ_MP (@lem22360 b) (@lem0)). Qed.
Lemma lem22367 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem22368 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem22369 : term13 = (imp True).
Proof. exact (MK_COMB (@lem22368) (@lem22367)). Qed.
Lemma lem22370 (b : Prop) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem22371 (b : Prop) : (term10 b) = (True -> b).
Proof. exact (MK_COMB (@lem22369) (@lem22370 b)). Qed.
Lemma lem22373 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem22374 (b : Prop) : (True -> b) = b.
Proof. exact (@lem22373 b). Qed.
Lemma lem22375 (b : Prop) : (term10 b) = b.
Proof. exact (TRANS (@lem22371 b) (@lem22374 b)). Qed.
Lemma lem22376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem22377 (b : Prop) : (term14 b) = (@eq Prop b).
Proof. exact (MK_COMB (@lem22376) (@lem22375 b)). Qed.
Lemma lem22379 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem22380 (b : Prop) : (False \/ b) = b.
Proof. exact (@lem22379 b). Qed.
Lemma lem22381 (b : Prop) : ((term10 b) = (False \/ b)) = (b = b).
Proof. exact (MK_COMB (@lem22377 b) (@lem22380 b)). Qed.
Lemma lem22383 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem22384 (x : Prop) : (x = x) = True.
Proof. exact (@lem22383 Prop x). Qed.
Lemma lem22385 (b : Prop) : (b = b) = True.
Proof. exact (@lem22384 b). Qed.
Lemma lem22386 (b : Prop) : ((term10 b) = (False \/ b)) = True.
Proof. exact (TRANS (@lem22381 b) (@lem22385 b)). Qed.
Lemma lem22387 (b : Prop) : True = ((term10 b) = (False \/ b)).
Proof. exact (SYM (@lem22386 b)). Qed.
Lemma lem22388 (b : Prop) : (term10 b) = (False \/ b).
Proof. exact (EQ_MP (@lem22387 b) (@lem0)). Qed.
Lemma lem22389 (b : Prop) (a : Prop) (h1 : a = False) : (term7 a b) = (a \/ b).
Proof. exact (EQ_MP (@lem22335 b a h1) (@lem22388 b)). Qed.
Lemma lem22390 (b : Prop) (a : Prop) (h1 : a = True) : (term7 a b) = (a \/ b).
Proof. exact (EQ_MP (@lem22322 b a h1) (@lem22361 b)). Qed.
Lemma lem22393 (a : Prop) (b : Prop) : (term7 a b) = (a \/ b).
Proof. exact (or_elim (@lem22299 a) (fun h0 : a = True => @lem22390 b a h0) (fun h0 : a = False => @lem22389 b a h0)). Qed.
Lemma lem22398 (a : Prop) : term15 a.
Proof. exact (fun b : Prop => @lem22393 a b). Qed.
Lemma lem22403 : term16.
Proof. exact (fun a : Prop => @lem22398 a). Qed.
