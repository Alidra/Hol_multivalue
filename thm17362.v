Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm17362_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem17274 (p : Prop) : term0 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem17275 (p : Prop) : (term0 p) = (term1 p).
Proof. exact (eq_refl (term0 p)). Qed.
Lemma lem17276 (p : Prop) : term1 p.
Proof. exact (EQ_MP (@lem17275 p) (@lem17274 p)). Qed.
Lemma lem17277 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem17278 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem17287 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17288 (q : Prop) (p : Prop) (h1 : p = True) : (term3 q p) = (term4 q).
Proof. exact (MK_COMB (@lem17287 q) (@lem17277 p h1)). Qed.
Lemma lem17289 (q : Prop) : (term4 q) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl (term4 q)). Qed.
Lemma lem17290 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17291 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = ((term3 q p) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17290 q p) (@lem17289 q)). Qed.
Lemma lem17292 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17293 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17294 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17293) (@lem17292 p q)). Qed.
Lemma lem17295 (q : Prop) : ((term5 q) = (term6 q)) = ((term5 q) = (term6 q)).
Proof. exact (eq_refl ((term5 q) = (term6 q))). Qed.
Lemma lem17296 (p : Prop) (q : Prop) : ((term3 q p) = ((term5 q) = (term6 q))) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (MK_COMB (@lem17294 p q) (@lem17295 q)). Qed.
Lemma lem17297 (p : Prop) (q : Prop) : ((term3 q p) = (term4 q)) = (((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q))).
Proof. exact (TRANS (@lem17291 p q) (@lem17296 p q)). Qed.
Lemma lem17298 (q : Prop) (p : Prop) (h1 : p = True) : ((term8 p q) = (term9 p q)) = ((term5 q) = (term6 q)).
Proof. exact (EQ_MP (@lem17297 p q) (@lem17288 q p h1)). Qed.
Lemma lem17299 (q : Prop) (p : Prop) (h1 : p = True) : ((term5 q) = (term6 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17298 q p h1)). Qed.
Lemma lem17300 (q : Prop) : (term2 q) = (term2 q).
Proof. exact (eq_refl (term2 q)). Qed.
Lemma lem17301 (q : Prop) (p : Prop) (h1 : p = False) : (term3 q p) = (term11 q).
Proof. exact (MK_COMB (@lem17300 q) (@lem17278 p h1)). Qed.
Lemma lem17302 (q : Prop) : (term11 q) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl (term11 q)). Qed.
Lemma lem17303 (q : Prop) (p : Prop) : (term7 q p) = (term7 q p).
Proof. exact (eq_refl (term7 q p)). Qed.
Lemma lem17304 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = ((term3 q p) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17303 q p) (@lem17302 q)). Qed.
Lemma lem17305 (p : Prop) (q : Prop) : (term3 q p) = ((term8 p q) = (term9 p q)).
Proof. exact (eq_refl (term3 q p)). Qed.
Lemma lem17306 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17307 (p : Prop) (q : Prop) : (term7 q p) = (term10 p q).
Proof. exact (MK_COMB (@lem17306) (@lem17305 p q)). Qed.
Lemma lem17308 (q : Prop) : ((term12 q) = (term13 q)) = ((term12 q) = (term13 q)).
Proof. exact (eq_refl ((term12 q) = (term13 q))). Qed.
Lemma lem17309 (p : Prop) (q : Prop) : ((term3 q p) = ((term12 q) = (term13 q))) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (MK_COMB (@lem17307 p q) (@lem17308 q)). Qed.
Lemma lem17310 (p : Prop) (q : Prop) : ((term3 q p) = (term11 q)) = (((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q))).
Proof. exact (TRANS (@lem17304 p q) (@lem17309 p q)). Qed.
Lemma lem17311 (q : Prop) (p : Prop) (h1 : p = False) : ((term8 p q) = (term9 p q)) = ((term12 q) = (term13 q)).
Proof. exact (EQ_MP (@lem17310 p q) (@lem17301 q p h1)). Qed.
Lemma lem17312 (q : Prop) (p : Prop) (h1 : p = False) : ((term12 q) = (term13 q)) = ((term8 p q) = (term9 p q)).
Proof. exact (SYM (@lem17311 q p h1)). Qed.
Lemma lem17316 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem17317 (q : Prop) : (True -> q) = q.
Proof. exact (@lem17316 q). Qed.
Lemma lem17318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17319 (q : Prop) : (term5 q) = (~ q).
Proof. exact (MK_COMB (@lem17318) (@lem17317 q)). Qed.
Lemma lem17320 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17321 (q : Prop) : (term14 q) = (term15 q).
Proof. exact (MK_COMB (@lem17320) (@lem17319 q)). Qed.
Lemma lem17323 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem17324 (q : Prop) : (term6 q) = (~ q).
Proof. exact (@lem17323 (~ q)). Qed.
Lemma lem17325 (q : Prop) : ((term5 q) = (term6 q)) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem17321 q) (@lem17324 q)). Qed.
Lemma lem17327 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem17328 (x : Prop) : (x = x) = True.
Proof. exact (@lem17327 Prop x). Qed.
Lemma lem17329 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem17328 (~ q)). Qed.
Lemma lem17330 (q : Prop) : ((term5 q) = (term6 q)) = True.
Proof. exact (TRANS (@lem17325 q) (@lem17329 q)). Qed.
Lemma lem17331 (q : Prop) : True = ((term5 q) = (term6 q)).
Proof. exact (SYM (@lem17330 q)). Qed.
Lemma lem17332 (q : Prop) : (term5 q) = (term6 q).
Proof. exact (EQ_MP (@lem17331 q) (@lem0)). Qed.
Lemma lem17336 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem17337 (q : Prop) : (False -> q) = True.
Proof. exact (@lem17336 q). Qed.
Lemma lem17338 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem17339 (q : Prop) : (term12 q) = (~ True).
Proof. exact (MK_COMB (@lem17338) (@lem17337 q)). Qed.
Lemma lem17341 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem17342 (q : Prop) : (term12 q) = False.
Proof. exact (TRANS (@lem17339 q) (@lem17341)). Qed.
Lemma lem17343 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem17344 (q : Prop) : (term16 q) = (@eq Prop False).
Proof. exact (MK_COMB (@lem17343) (@lem17342 q)). Qed.
Lemma lem17346 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem17347 (q : Prop) : (term13 q) = False.
Proof. exact (@lem17346 (~ q)). Qed.
Lemma lem17348 (q : Prop) : ((term12 q) = (term13 q)) = (False = False).
Proof. exact (MK_COMB (@lem17344 q) (@lem17347 q)). Qed.
Lemma lem17350 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem17351 : (False = False) = (~ False).
Proof. exact (@lem17350 False). Qed.
Lemma lem17353 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem17354 : (False = False) = True.
Proof. exact (TRANS (@lem17351) (@lem17353)). Qed.
Lemma lem17355 (q : Prop) : ((term12 q) = (term13 q)) = True.
Proof. exact (TRANS (@lem17348 q) (@lem17354)). Qed.
Lemma lem17356 (q : Prop) : True = ((term12 q) = (term13 q)).
Proof. exact (SYM (@lem17355 q)). Qed.
Lemma lem17357 (q : Prop) : (term12 q) = (term13 q).
Proof. exact (EQ_MP (@lem17356 q) (@lem0)). Qed.
Lemma lem17358 (q : Prop) (p : Prop) (h1 : p = False) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17312 q p h1) (@lem17357 q)). Qed.
Lemma lem17359 (q : Prop) (p : Prop) (h1 : p = True) : (term8 p q) = (term9 p q).
Proof. exact (EQ_MP (@lem17299 q p h1) (@lem17332 q)). Qed.
Lemma lem17362 (p : Prop) (q : Prop) : (term8 p q) = (term9 p q).
Proof. exact (or_elim (@lem17276 p) (fun h0 : p = True => @lem17359 q p h0) (fun h0 : p = False => @lem17358 q p h0)). Qed.
