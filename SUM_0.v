Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_0_term_abbrevs.
Require Import SUM_EQ_0_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Lemma lem7069293 {A : Type'} (f : A -> real) : term0 A f.
Proof. exact (@lem7069292 A f). Qed.
Lemma lem7069294 {A : Type'} (f : A -> real) : (term0 A f) = (term1 A f).
Proof. exact (eq_refl (term0 A f)). Qed.
Lemma lem7069295 {A : Type'} (f : A -> real) : term1 A f.
Proof. exact (EQ_MP (@lem7069294 A f) (@lem7069293 A f)). Qed.
Lemma lem7069296 {A : Type'} (f : A -> real) (s : A -> Prop) : term2 A f s.
Proof. exact (@lem7069295 A f s). Qed.
Lemma lem7069297 {A : Type'} (s : A -> Prop) (f : A -> real) : (term2 A f s) = (term3 A s f).
Proof. exact (eq_refl (term2 A f s)). Qed.
Lemma lem7069298 {A : Type'} (s : A -> Prop) (f : A -> real) : term3 A s f.
Proof. exact (EQ_MP (@lem7069297 A s f) (@lem7069296 A f s)). Qed.
Lemma lem7069299 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term4 A s f) : term4 A s f.
Proof. exact (h1). Qed.
Lemma lem7069300 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term4 A s f) : (@sum A s f) = term5.
Proof. exact (@lem7069298 A s f (@lem7069299 A s f h1)). Qed.
Lemma lem7069313 {A : Type'} (s : A -> Prop) (f : A -> real) : term3 A s f.
Proof. exact (fun h0 : term4 A s f => @lem7069300 A s f h0). Qed.
Lemma lem7069314 {A : Type'} (s : A -> Prop) (f : A -> real) : term3 A s f.
Proof. exact (@lem7069313 A s f). Qed.
Lemma lem7069315 {A : Type'} (s : A -> Prop) : term6 A s.
Proof. exact (@lem7069314 A s (term7 A)). Qed.
Lemma lem7069323 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term8 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7069324 (p : Prop) (q : Prop) (p' : Prop) : term9 p q p'.
Proof. exact (fun q' : Prop => @lem7069323 p q p' q'). Qed.
Lemma lem7069325 (p : Prop) (q : Prop) : term10 p q.
Proof. exact (fun p' : Prop => @lem7069324 p q p'). Qed.
Lemma lem7069326 {A : Type'} (s : A -> Prop) (x : A) : term11 A s x.
Proof. exact (@lem7069325 (@IN A x s) ((term12 A x) = term5)). Qed.
Lemma lem7069327 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) : term13 A s x p'.
Proof. exact (@lem7069326 A s x p'). Qed.
Lemma lem7069328 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) : (term13 A s x p') = (term14 A s x p').
Proof. exact (eq_refl (term13 A s x p')). Qed.
Lemma lem7069329 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) : term14 A s x p'.
Proof. exact (EQ_MP (@lem7069328 A s x p') (@lem7069327 A s x p')). Qed.
Lemma lem7069330 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term15 A s x p' q'.
Proof. exact (@lem7069329 A s x p' q'). Qed.
Lemma lem7069331 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : (term15 A s x p' q') = (term16 A s x p' q').
Proof. exact (eq_refl (term15 A s x p' q')). Qed.
Lemma lem7069332 {A : Type'} (s : A -> Prop) (x : A) (p' : Prop) (q' : Prop) : term16 A s x p' q'.
Proof. exact (EQ_MP (@lem7069331 A s x p' q') (@lem7069330 A s x p' q')). Qed.
Lemma lem7069333 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7069334 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term17 A x s q'.
Proof. exact (@lem7069332 A s x (@IN A x s) q'). Qed.
Lemma lem7069335 {A : Type'} (x : A) (s : A -> Prop) (q' : Prop) : term18 A x s q'.
Proof. exact (@lem7069334 A x s q' (@lem7069333 A x s)). Qed.
Lemma lem7069342 {A B : Type'} (f : A -> B) (y : A) : (term19 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7069343 {A : Type'} (f : A -> real) (y : A) : (term20 A f y) = (f y).
Proof. exact (@lem7069342 A real f y). Qed.
Lemma lem7069344 {A : Type'} (x : A) : (term21 A x) = (term12 A x).
Proof. exact (@lem7069343 A (term7 A) x). Qed.
Lemma lem7069345 {A : Type'} (n : A) : (term12 A n) = term5.
Proof. exact (eq_refl (term12 A n)). Qed.
Lemma lem7069346 {A : Type'} : (term22 A) = (term7 A).
Proof. exact (fun_ext (fun n : A => @lem7069345 A n)). Qed.
Lemma lem7069347 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7069348 {A : Type'} (x : A) : (term21 A x) = (term12 A x).
Proof. exact (MK_COMB (@lem7069346 A) (@lem7069347 A x)). Qed.
Lemma lem7069349 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069350 {A : Type'} (x : A) : (term23 A x) = (term24 A x).
Proof. exact (MK_COMB (@lem7069349) (@lem7069348 A x)). Qed.
Lemma lem7069351 {A : Type'} (x : A) : (term12 A x) = term5.
Proof. exact (eq_refl (term12 A x)). Qed.
Lemma lem7069352 {A : Type'} (x : A) : ((term21 A x) = (term12 A x)) = ((term12 A x) = term5).
Proof. exact (MK_COMB (@lem7069350 A x) (@lem7069351 A x)). Qed.
Lemma lem7069353 {A : Type'} (x : A) : (term12 A x) = term5.
Proof. exact (EQ_MP (@lem7069352 A x) (@lem7069344 A x)). Qed.
Lemma lem7069354 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069355 {A : Type'} (x : A) : (term24 A x) = term25.
Proof. exact (MK_COMB (@lem7069354) (@lem7069353 A x)). Qed.
Lemma lem7069356 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem7069357 {A : Type'} (x : A) : ((term12 A x) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem7069355 A x) (@lem7069356)). Qed.
Lemma lem7069359 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7069360 (x : real) : (x = x) = True.
Proof. exact (@lem7069359 real x). Qed.
Lemma lem7069361 : (term5 = term5) = True.
Proof. exact (@lem7069360 term5). Qed.
Lemma lem7069362 {A : Type'} (x : A) : ((term12 A x) = term5) = True.
Proof. exact (TRANS (@lem7069357 A x) (@lem7069361)). Qed.
Lemma lem7069363 {A : Type'} (s : A -> Prop) (x : A) : term26 A s x.
Proof. exact (fun h0 : @IN A x s => @lem7069362 A x). Qed.
Lemma lem7069364 {A : Type'} (x : A) (s : A -> Prop) : term27 A x s.
Proof. exact (@lem7069335 A x s True). Qed.
Lemma lem7069365 {A : Type'} (x : A) (s : A -> Prop) : (term28 A s x) = (term29 A x s).
Proof. exact (@lem7069364 A x s (@lem7069363 A s x)). Qed.
Lemma lem7069367 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7069368 {A : Type'} (x : A) (s : A -> Prop) : (term29 A x s) = True.
Proof. exact (@lem7069367 (@IN A x s)). Qed.
Lemma lem7069369 {A : Type'} (s : A -> Prop) (x : A) : (term28 A s x) = True.
Proof. exact (TRANS (@lem7069365 A x s) (@lem7069368 A x s)). Qed.
Lemma lem7069370 {A : Type'} (s : A -> Prop) : (term30 A s) = (term31 A).
Proof. exact (fun_ext (fun x : A => @lem7069369 A s x)). Qed.
Lemma lem7069371 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7069372 {A : Type'} (s : A -> Prop) : (term32 A s) = (term33 A).
Proof. exact (MK_COMB (@lem7069371 A) (@lem7069370 A s)). Qed.
Lemma lem7069374 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7069375 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (@lem7069374 A t). Qed.
Lemma lem7069376 {A : Type'} : (term33 A) = True.
Proof. exact (@lem7069375 A True). Qed.
Lemma lem7069377 {A : Type'} (s : A -> Prop) : (term32 A s) = True.
Proof. exact (TRANS (@lem7069372 A s) (@lem7069376 A)). Qed.
Lemma lem7069378 {A : Type'} (s : A -> Prop) : True = (term32 A s).
Proof. exact (SYM (@lem7069377 A s)). Qed.
Lemma lem7069379 {A : Type'} (s : A -> Prop) : term32 A s.
Proof. exact (EQ_MP (@lem7069378 A s) (@lem0)). Qed.
Lemma lem7069380 {A : Type'} (s : A -> Prop) : (term35 A s) = term5.
Proof. exact (@lem7069315 A s (@lem7069379 A s)). Qed.
Lemma lem7069381 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem7069382 {A : Type'} (s : A -> Prop) : (term36 A s) = term25.
Proof. exact (MK_COMB (@lem7069381) (@lem7069380 A s)). Qed.
Lemma lem7069383 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem7069384 {A : Type'} (s : A -> Prop) : ((term35 A s) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem7069382 A s) (@lem7069383)). Qed.
Lemma lem7069386 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7069387 (x : real) : (x = x) = True.
Proof. exact (@lem7069386 real x). Qed.
Lemma lem7069388 : (term5 = term5) = True.
Proof. exact (@lem7069387 term5). Qed.
Lemma lem7069389 {A : Type'} (s : A -> Prop) : ((term35 A s) = term5) = True.
Proof. exact (TRANS (@lem7069384 A s) (@lem7069388)). Qed.
Lemma lem7069390 {A : Type'} : (term37 A) = (term38 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7069389 A s)). Qed.
Lemma lem7069391 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7069392 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (MK_COMB (@lem7069391 A) (@lem7069390 A)). Qed.
Lemma lem7069394 {A : Type'} (t : Prop) : (term34 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7069395 {A : Type'} (t : Prop) : (term41 A t) = t.
Proof. exact (@lem7069394 (A -> Prop) t). Qed.
Lemma lem7069396 {A : Type'} : (term40 A) = True.
Proof. exact (@lem7069395 A True). Qed.
Lemma lem7069397 {A : Type'} : (term39 A) = True.
Proof. exact (TRANS (@lem7069392 A) (@lem7069396 A)). Qed.
Lemma lem7069398 {A : Type'} : True = (term39 A).
Proof. exact (SYM (@lem7069397 A)). Qed.
Lemma lem7069399 {A : Type'} : term39 A.
Proof. exact (EQ_MP (@lem7069398 A) (@lem0)). Qed.
