Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CONTRAPOS_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem10308 (t1 : Prop) : term0 t1.
Proof. exact (@lem9851 t1). Qed.
Lemma lem10309 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem10310 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem10309 t1) (@lem10308 t1)). Qed.
Lemma lem10311 (t1 : Prop) (h1 : t1 = True) : t1 = True.
Proof. exact (h1). Qed.
Lemma lem10312 (t1 : Prop) (h1 : t1 = False) : t1 = False.
Proof. exact (h1). Qed.
Lemma lem10321 (t2 : Prop) : (term2 t2) = (term2 t2).
Proof. exact (eq_refl (term2 t2)). Qed.
Lemma lem10322 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term3 t2 t1) = (term4 t2).
Proof. exact (MK_COMB (@lem10321 t2) (@lem10311 t1 h1)). Qed.
Lemma lem10323 (t2 : Prop) : (term4 t2) = ((term5 t2) = (t2 -> True)).
Proof. exact (eq_refl (term4 t2)). Qed.
Lemma lem10324 (t2 : Prop) (t1 : Prop) : (term6 t2 t1) = (term6 t2 t1).
Proof. exact (eq_refl (term6 t2 t1)). Qed.
Lemma lem10325 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term4 t2)) = ((term3 t2 t1) = ((term5 t2) = (t2 -> True))).
Proof. exact (MK_COMB (@lem10324 t2 t1) (@lem10323 t2)). Qed.
Lemma lem10326 (t2 : Prop) (t1 : Prop) : (term3 t2 t1) = ((term7 t1 t2) = (t2 -> t1)).
Proof. exact (eq_refl (term3 t2 t1)). Qed.
Lemma lem10327 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10328 (t2 : Prop) (t1 : Prop) : (term6 t2 t1) = (term8 t2 t1).
Proof. exact (MK_COMB (@lem10327) (@lem10326 t2 t1)). Qed.
Lemma lem10329 (t2 : Prop) : ((term5 t2) = (t2 -> True)) = ((term5 t2) = (t2 -> True)).
Proof. exact (eq_refl ((term5 t2) = (t2 -> True))). Qed.
Lemma lem10330 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = ((term5 t2) = (t2 -> True))) = (((term7 t1 t2) = (t2 -> t1)) = ((term5 t2) = (t2 -> True))).
Proof. exact (MK_COMB (@lem10328 t2 t1) (@lem10329 t2)). Qed.
Lemma lem10331 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term4 t2)) = (((term7 t1 t2) = (t2 -> t1)) = ((term5 t2) = (t2 -> True))).
Proof. exact (TRANS (@lem10325 t1 t2) (@lem10330 t1 t2)). Qed.
Lemma lem10332 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term7 t1 t2) = (t2 -> t1)) = ((term5 t2) = (t2 -> True)).
Proof. exact (EQ_MP (@lem10331 t1 t2) (@lem10322 t2 t1 h1)). Qed.
Lemma lem10333 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : ((term5 t2) = (t2 -> True)) = ((term7 t1 t2) = (t2 -> t1)).
Proof. exact (SYM (@lem10332 t2 t1 h1)). Qed.
Lemma lem10334 (t2 : Prop) : (term2 t2) = (term2 t2).
Proof. exact (eq_refl (term2 t2)). Qed.
Lemma lem10335 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term3 t2 t1) = (term9 t2).
Proof. exact (MK_COMB (@lem10334 t2) (@lem10312 t1 h1)). Qed.
Lemma lem10336 (t2 : Prop) : (term9 t2) = ((term10 t2) = (t2 -> False)).
Proof. exact (eq_refl (term9 t2)). Qed.
Lemma lem10337 (t2 : Prop) (t1 : Prop) : (term6 t2 t1) = (term6 t2 t1).
Proof. exact (eq_refl (term6 t2 t1)). Qed.
Lemma lem10338 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term9 t2)) = ((term3 t2 t1) = ((term10 t2) = (t2 -> False))).
Proof. exact (MK_COMB (@lem10337 t2 t1) (@lem10336 t2)). Qed.
Lemma lem10339 (t2 : Prop) (t1 : Prop) : (term3 t2 t1) = ((term7 t1 t2) = (t2 -> t1)).
Proof. exact (eq_refl (term3 t2 t1)). Qed.
Lemma lem10340 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10341 (t2 : Prop) (t1 : Prop) : (term6 t2 t1) = (term8 t2 t1).
Proof. exact (MK_COMB (@lem10340) (@lem10339 t2 t1)). Qed.
Lemma lem10342 (t2 : Prop) : ((term10 t2) = (t2 -> False)) = ((term10 t2) = (t2 -> False)).
Proof. exact (eq_refl ((term10 t2) = (t2 -> False))). Qed.
Lemma lem10343 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = ((term10 t2) = (t2 -> False))) = (((term7 t1 t2) = (t2 -> t1)) = ((term10 t2) = (t2 -> False))).
Proof. exact (MK_COMB (@lem10341 t2 t1) (@lem10342 t2)). Qed.
Lemma lem10344 (t1 : Prop) (t2 : Prop) : ((term3 t2 t1) = (term9 t2)) = (((term7 t1 t2) = (t2 -> t1)) = ((term10 t2) = (t2 -> False))).
Proof. exact (TRANS (@lem10338 t1 t2) (@lem10343 t1 t2)). Qed.
Lemma lem10345 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term7 t1 t2) = (t2 -> t1)) = ((term10 t2) = (t2 -> False)).
Proof. exact (EQ_MP (@lem10344 t1 t2) (@lem10335 t2 t1 h1)). Qed.
Lemma lem10346 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : ((term10 t2) = (t2 -> False)) = ((term7 t1 t2) = (t2 -> t1)).
Proof. exact (SYM (@lem10345 t2 t1 h1)). Qed.
Lemma lem10352 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem10353 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem10354 : term11 = (imp False).
Proof. exact (MK_COMB (@lem10353) (@lem10352)). Qed.
Lemma lem10355 (t2 : Prop) : (~ t2) = (~ t2).
Proof. exact (eq_refl (~ t2)). Qed.
Lemma lem10356 (t2 : Prop) : (term5 t2) = (term12 t2).
Proof. exact (MK_COMB (@lem10354) (@lem10355 t2)). Qed.
Lemma lem10358 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem10359 (t2 : Prop) : (term12 t2) = True.
Proof. exact (@lem10358 (~ t2)). Qed.
Lemma lem10360 (t2 : Prop) : (term5 t2) = True.
Proof. exact (TRANS (@lem10356 t2) (@lem10359 t2)). Qed.
Lemma lem10361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10362 (t2 : Prop) : (term13 t2) = (@eq Prop True).
Proof. exact (MK_COMB (@lem10361) (@lem10360 t2)). Qed.
Lemma lem10364 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem10365 (t2 : Prop) : (t2 -> True) = True.
Proof. exact (@lem10364 t2). Qed.
Lemma lem10366 (t2 : Prop) : ((term5 t2) = (t2 -> True)) = (True = True).
Proof. exact (MK_COMB (@lem10362 t2) (@lem10365 t2)). Qed.
Lemma lem10368 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem10369 : (True = True) = True.
Proof. exact (@lem10368 True). Qed.
Lemma lem10370 (t2 : Prop) : ((term5 t2) = (t2 -> True)) = True.
Proof. exact (TRANS (@lem10366 t2) (@lem10369)). Qed.
Lemma lem10371 (t2 : Prop) : True = ((term5 t2) = (t2 -> True)).
Proof. exact (SYM (@lem10370 t2)). Qed.
Lemma lem10372 (t2 : Prop) : (term5 t2) = (t2 -> True).
Proof. exact (EQ_MP (@lem10371 t2) (@lem0)). Qed.
Lemma lem10378 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem10379 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem10380 : term14 = (imp True).
Proof. exact (MK_COMB (@lem10379) (@lem10378)). Qed.
Lemma lem10381 (t2 : Prop) : (~ t2) = (~ t2).
Proof. exact (eq_refl (~ t2)). Qed.
Lemma lem10382 (t2 : Prop) : (term10 t2) = (term15 t2).
Proof. exact (MK_COMB (@lem10380) (@lem10381 t2)). Qed.
Lemma lem10384 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem10385 (t2 : Prop) : (term15 t2) = (~ t2).
Proof. exact (@lem10384 (~ t2)). Qed.
Lemma lem10386 (t2 : Prop) : (term10 t2) = (~ t2).
Proof. exact (TRANS (@lem10382 t2) (@lem10385 t2)). Qed.
Lemma lem10387 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem10388 (t2 : Prop) : (term16 t2) = (term17 t2).
Proof. exact (MK_COMB (@lem10387) (@lem10386 t2)). Qed.
Lemma lem10390 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem1823 t)). Qed.
Lemma lem10391 (t2 : Prop) : (t2 -> False) = (~ t2).
Proof. exact (@lem10390 t2). Qed.
Lemma lem10392 (t2 : Prop) : ((term10 t2) = (t2 -> False)) = ((~ t2) = (~ t2)).
Proof. exact (MK_COMB (@lem10388 t2) (@lem10391 t2)). Qed.
Lemma lem10394 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem10395 (x : Prop) : (x = x) = True.
Proof. exact (@lem10394 Prop x). Qed.
Lemma lem10396 (t2 : Prop) : ((~ t2) = (~ t2)) = True.
Proof. exact (@lem10395 (~ t2)). Qed.
Lemma lem10397 (t2 : Prop) : ((term10 t2) = (t2 -> False)) = True.
Proof. exact (TRANS (@lem10392 t2) (@lem10396 t2)). Qed.
Lemma lem10398 (t2 : Prop) : True = ((term10 t2) = (t2 -> False)).
Proof. exact (SYM (@lem10397 t2)). Qed.
Lemma lem10399 (t2 : Prop) : (term10 t2) = (t2 -> False).
Proof. exact (EQ_MP (@lem10398 t2) (@lem0)). Qed.
Lemma lem10400 (t2 : Prop) (t1 : Prop) (h1 : t1 = False) : (term7 t1 t2) = (t2 -> t1).
Proof. exact (EQ_MP (@lem10346 t2 t1 h1) (@lem10399 t2)). Qed.
Lemma lem10401 (t2 : Prop) (t1 : Prop) (h1 : t1 = True) : (term7 t1 t2) = (t2 -> t1).
Proof. exact (EQ_MP (@lem10333 t2 t1 h1) (@lem10372 t2)). Qed.
Lemma lem10404 (t2 : Prop) (t1 : Prop) : (term7 t1 t2) = (t2 -> t1).
Proof. exact (or_elim (@lem10310 t1) (fun h0 : t1 = True => @lem10401 t2 t1 h0) (fun h0 : t1 = False => @lem10400 t2 t1 h0)). Qed.
Lemma lem10409 (t1 : Prop) : term18 t1.
Proof. exact (fun t2 : Prop => @lem10404 t2 t1). Qed.
Lemma lem10414 : term19.
Proof. exact (fun t1 : Prop => @lem10409 t1). Qed.
