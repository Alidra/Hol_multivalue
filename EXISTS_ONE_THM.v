Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_ONE_THM_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_EXISTS_THM_spec.
Require Import thm0_spec.
Require Import thm10416_spec.
Require Import thm10417_spec.
Require Import thm16264_spec.
Require Import thm16265_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem16267 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem10660 A P). Qed.
Lemma lem16268 {A : Type'} (P : A -> Prop) : (term0 A P) = ((term1 A P) = (term2 A P)).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem16278 (p : Prop) : term3 p.
Proof. exact (@lem9851 p). Qed.
Lemma lem16279 (p : Prop) : (term3 p) = (term4 p).
Proof. exact (eq_refl (term3 p)). Qed.
Lemma lem16280 (p : Prop) : term4 p.
Proof. exact (EQ_MP (@lem16279 p) (@lem16278 p)). Qed.
Lemma lem16281 (p : Prop) (h1 : p = True) : p = True.
Proof. exact (h1). Qed.
Lemma lem16282 (p : Prop) (h1 : p = False) : p = False.
Proof. exact (h1). Qed.
Lemma lem16291 (q : Prop) : (term5 q) = (term5 q).
Proof. exact (eq_refl (term5 q)). Qed.
Lemma lem16292 (q : Prop) (p : Prop) (h1 : p = True) : (term6 q p) = (term7 q).
Proof. exact (MK_COMB (@lem16291 q) (@lem16281 p h1)). Qed.
Lemma lem16293 (q : Prop) : (term7 q) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl (term7 q)). Qed.
Lemma lem16294 (q : Prop) (p : Prop) : (term8 q p) = (term8 q p).
Proof. exact (eq_refl (term8 q p)). Qed.
Lemma lem16295 (p : Prop) (q : Prop) : ((term6 q p) = (term7 q)) = ((term6 q p) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem16294 q p) (@lem16293 q)). Qed.
Lemma lem16296 (p : Prop) (q : Prop) : (term6 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem16297 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16298 (p : Prop) (q : Prop) : (term8 q p) = (term9 p q).
Proof. exact (MK_COMB (@lem16297) (@lem16296 p q)). Qed.
Lemma lem16299 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (eq_refl ((True = q) = ((~ True) = (~ q)))). Qed.
Lemma lem16300 (p : Prop) (q : Prop) : ((term6 q p) = ((True = q) = ((~ True) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (MK_COMB (@lem16298 p q) (@lem16299 q)). Qed.
Lemma lem16301 (p : Prop) (q : Prop) : ((term6 q p) = (term7 q)) = (((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q)))).
Proof. exact (TRANS (@lem16295 p q) (@lem16300 p q)). Qed.
Lemma lem16302 (q : Prop) (p : Prop) (h1 : p = True) : ((p = q) = ((~ p) = (~ q))) = ((True = q) = ((~ True) = (~ q))).
Proof. exact (EQ_MP (@lem16301 p q) (@lem16292 q p h1)). Qed.
Lemma lem16303 (q : Prop) (p : Prop) (h1 : p = True) : ((True = q) = ((~ True) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem16302 q p h1)). Qed.
Lemma lem16304 (q : Prop) : (term5 q) = (term5 q).
Proof. exact (eq_refl (term5 q)). Qed.
Lemma lem16305 (q : Prop) (p : Prop) (h1 : p = False) : (term6 q p) = (term10 q).
Proof. exact (MK_COMB (@lem16304 q) (@lem16282 p h1)). Qed.
Lemma lem16306 (q : Prop) : (term10 q) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl (term10 q)). Qed.
Lemma lem16307 (q : Prop) (p : Prop) : (term8 q p) = (term8 q p).
Proof. exact (eq_refl (term8 q p)). Qed.
Lemma lem16308 (p : Prop) (q : Prop) : ((term6 q p) = (term10 q)) = ((term6 q p) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem16307 q p) (@lem16306 q)). Qed.
Lemma lem16309 (p : Prop) (q : Prop) : (term6 q p) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (eq_refl (term6 q p)). Qed.
Lemma lem16310 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16311 (p : Prop) (q : Prop) : (term8 q p) = (term9 p q).
Proof. exact (MK_COMB (@lem16310) (@lem16309 p q)). Qed.
Lemma lem16312 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (eq_refl ((False = q) = ((~ False) = (~ q)))). Qed.
Lemma lem16313 (p : Prop) (q : Prop) : ((term6 q p) = ((False = q) = ((~ False) = (~ q)))) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (MK_COMB (@lem16311 p q) (@lem16312 q)). Qed.
Lemma lem16314 (p : Prop) (q : Prop) : ((term6 q p) = (term10 q)) = (((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q)))).
Proof. exact (TRANS (@lem16308 p q) (@lem16313 p q)). Qed.
Lemma lem16315 (q : Prop) (p : Prop) (h1 : p = False) : ((p = q) = ((~ p) = (~ q))) = ((False = q) = ((~ False) = (~ q))).
Proof. exact (EQ_MP (@lem16314 p q) (@lem16305 q p h1)). Qed.
Lemma lem16316 (q : Prop) (p : Prop) (h1 : p = False) : ((False = q) = ((~ False) = (~ q))) = ((p = q) = ((~ p) = (~ q))).
Proof. exact (SYM (@lem16315 q p h1)). Qed.
Lemma lem16320 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem16321 (q : Prop) : (True = q) = q.
Proof. exact (@lem16320 q). Qed.
Lemma lem16322 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16323 (q : Prop) : (term11 q) = (@eq Prop q).
Proof. exact (MK_COMB (@lem16322) (@lem16321 q)). Qed.
Lemma lem16327 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem16328 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16329 : term12 = (@eq Prop False).
Proof. exact (MK_COMB (@lem16328) (@lem16327)). Qed.
Lemma lem16330 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem16331 (q : Prop) : ((~ True) = (~ q)) = (False = (~ q)).
Proof. exact (MK_COMB (@lem16329) (@lem16330 q)). Qed.
Lemma lem16333 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem16334 (q : Prop) : (False = (~ q)) = (term13 q).
Proof. exact (@lem16333 (~ q)). Qed.
Lemma lem16336 (t : Prop) : (term13 t) = t.
Proof. exact (EQ_MP (@lem10417 t) (@lem10416 t)). Qed.
Lemma lem16337 (q : Prop) : (term13 q) = q.
Proof. exact (@lem16336 q). Qed.
Lemma lem16338 (q : Prop) : (False = (~ q)) = q.
Proof. exact (TRANS (@lem16334 q) (@lem16337 q)). Qed.
Lemma lem16339 (q : Prop) : ((~ True) = (~ q)) = q.
Proof. exact (TRANS (@lem16331 q) (@lem16338 q)). Qed.
Lemma lem16340 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = (q = q).
Proof. exact (MK_COMB (@lem16323 q) (@lem16339 q)). Qed.
Lemma lem16342 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem16343 (x : Prop) : (x = x) = True.
Proof. exact (@lem16342 Prop x). Qed.
Lemma lem16344 (q : Prop) : (q = q) = True.
Proof. exact (@lem16343 q). Qed.
Lemma lem16345 (q : Prop) : ((True = q) = ((~ True) = (~ q))) = True.
Proof. exact (TRANS (@lem16340 q) (@lem16344 q)). Qed.
Lemma lem16346 (q : Prop) : True = ((True = q) = ((~ True) = (~ q))).
Proof. exact (SYM (@lem16345 q)). Qed.
Lemma lem16347 (q : Prop) : (True = q) = ((~ True) = (~ q)).
Proof. exact (EQ_MP (@lem16346 q) (@lem0)). Qed.
Lemma lem16351 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem16352 (q : Prop) : (False = q) = (~ q).
Proof. exact (@lem16351 q). Qed.
Lemma lem16353 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16354 (q : Prop) : (term14 q) = (term15 q).
Proof. exact (MK_COMB (@lem16353) (@lem16352 q)). Qed.
Lemma lem16358 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem16359 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16360 : term16 = (@eq Prop True).
Proof. exact (MK_COMB (@lem16359) (@lem16358)). Qed.
Lemma lem16361 (q : Prop) : (~ q) = (~ q).
Proof. exact (eq_refl (~ q)). Qed.
Lemma lem16362 (q : Prop) : ((~ False) = (~ q)) = (True = (~ q)).
Proof. exact (MK_COMB (@lem16360) (@lem16361 q)). Qed.
Lemma lem16364 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem16365 (q : Prop) : (True = (~ q)) = (~ q).
Proof. exact (@lem16364 (~ q)). Qed.
Lemma lem16366 (q : Prop) : ((~ False) = (~ q)) = (~ q).
Proof. exact (TRANS (@lem16362 q) (@lem16365 q)). Qed.
Lemma lem16367 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = ((~ q) = (~ q)).
Proof. exact (MK_COMB (@lem16354 q) (@lem16366 q)). Qed.
Lemma lem16369 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem16370 (x : Prop) : (x = x) = True.
Proof. exact (@lem16369 Prop x). Qed.
Lemma lem16371 (q : Prop) : ((~ q) = (~ q)) = True.
Proof. exact (@lem16370 (~ q)). Qed.
Lemma lem16372 (q : Prop) : ((False = q) = ((~ False) = (~ q))) = True.
Proof. exact (TRANS (@lem16367 q) (@lem16371 q)). Qed.
Lemma lem16373 (q : Prop) : True = ((False = q) = ((~ False) = (~ q))).
Proof. exact (SYM (@lem16372 q)). Qed.
Lemma lem16374 (q : Prop) : (False = q) = ((~ False) = (~ q)).
Proof. exact (EQ_MP (@lem16373 q) (@lem0)). Qed.
Lemma lem16375 (q : Prop) (p : Prop) (h1 : p = False) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem16316 q p h1) (@lem16374 q)). Qed.
Lemma lem16376 (q : Prop) (p : Prop) (h1 : p = True) : (p = q) = ((~ p) = (~ q)).
Proof. exact (EQ_MP (@lem16303 q p h1) (@lem16347 q)). Qed.
Lemma lem16381 (p : Prop) (q : Prop) : (p = q) = ((~ p) = (~ q)).
Proof. exact (or_elim (@lem16280 p) (fun h0 : p = True => @lem16376 q p h0) (fun h0 : p = False => @lem16375 q p h0)). Qed.
Lemma lem16382 (P : unit -> Prop) : ((term17 P) = (P tt)) = ((term18 P) = (term19 P)).
Proof. exact (@lem16381 (term17 P) (P tt)). Qed.
Lemma lem16383 (P : unit -> Prop) : ((term18 P) = (term19 P)) = ((term17 P) = (P tt)).
Proof. exact (SYM (@lem16382 P)). Qed.
Lemma lem16387 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (EQ_MP (@lem16268 A P) (@lem16267 A P)). Qed.
Lemma lem16388 (P : unit -> Prop) : (term18 P) = (term20 P).
Proof. exact (@lem16387 unit P). Qed.
Lemma lem16394 (P : unit -> Prop) : (term21 P) = (P tt).
Proof. exact (EQ_MP (@lem16265 P) (@lem16264 P)). Qed.
Lemma lem16395 (P : unit -> Prop) : (term22 P) = (term23 P).
Proof. exact (@lem16394 (term24 P)). Qed.
Lemma lem16396 (P : unit -> Prop) (x : unit) : (term25 P x) = (term26 P x).
Proof. exact (eq_refl (term25 P x)). Qed.
Lemma lem16397 (P : unit -> Prop) : (term27 P) = (term24 P).
Proof. exact (fun_ext (fun x : unit => @lem16396 P x)). Qed.
Lemma lem16398 : (@all unit) = (@all unit).
Proof. exact (eq_refl (@all unit)). Qed.
Lemma lem16399 (P : unit -> Prop) : (term22 P) = (term20 P).
Proof. exact (MK_COMB (@lem16398) (@lem16397 P)). Qed.
Lemma lem16400 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16401 (P : unit -> Prop) : (term28 P) = (term29 P).
Proof. exact (MK_COMB (@lem16400) (@lem16399 P)). Qed.
Lemma lem16402 (P : unit -> Prop) : (term23 P) = (term19 P).
Proof. exact (eq_refl (term23 P)). Qed.
Lemma lem16403 (P : unit -> Prop) : ((term22 P) = (term23 P)) = ((term20 P) = (term19 P)).
Proof. exact (MK_COMB (@lem16401 P) (@lem16402 P)). Qed.
Lemma lem16404 (P : unit -> Prop) : (term20 P) = (term19 P).
Proof. exact (EQ_MP (@lem16403 P) (@lem16395 P)). Qed.
Lemma lem16405 (P : unit -> Prop) : (term18 P) = (term19 P).
Proof. exact (TRANS (@lem16388 P) (@lem16404 P)). Qed.
Lemma lem16406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem16407 (P : unit -> Prop) : (term30 P) = (term31 P).
Proof. exact (MK_COMB (@lem16406) (@lem16405 P)). Qed.
Lemma lem16408 (P : unit -> Prop) : (term19 P) = (term19 P).
Proof. exact (eq_refl (term19 P)). Qed.
Lemma lem16409 (P : unit -> Prop) : ((term18 P) = (term19 P)) = ((term19 P) = (term19 P)).
Proof. exact (MK_COMB (@lem16407 P) (@lem16408 P)). Qed.
Lemma lem16411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem16412 (x : Prop) : (x = x) = True.
Proof. exact (@lem16411 Prop x). Qed.
Lemma lem16413 (P : unit -> Prop) : ((term19 P) = (term19 P)) = True.
Proof. exact (@lem16412 (term19 P)). Qed.
Lemma lem16414 (P : unit -> Prop) : ((term18 P) = (term19 P)) = True.
Proof. exact (TRANS (@lem16409 P) (@lem16413 P)). Qed.
Lemma lem16415 (P : unit -> Prop) : True = ((term18 P) = (term19 P)).
Proof. exact (SYM (@lem16414 P)). Qed.
Lemma lem16416 (P : unit -> Prop) : (term18 P) = (term19 P).
Proof. exact (EQ_MP (@lem16415 P) (@lem0)). Qed.
Lemma lem16417 (P : unit -> Prop) : (term17 P) = (P tt).
Proof. exact (EQ_MP (@lem16383 P) (@lem16416 P)). Qed.
