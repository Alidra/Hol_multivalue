Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import bool_RECURSION_term_abbrevs.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem15312 {A B : Type'} (f : A -> B) (y : A) : (term0 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem15313 {A : Type'} (f : Prop -> A) (y : Prop) : (term1 A f y) = (f y).
Proof. exact (@lem15312 Prop A f y). Qed.
Lemma lem15314 {A : Type'} (b : A) (a : A) : (term2 A b a) = (term3 A b a).
Proof. exact (@lem15313 A (term4 A b a) False). Qed.
Lemma lem15315 {A : Type'} (x : Prop) (b : A) (a : A) : (term5 A b a x) = (@COND A x b a).
Proof. exact (eq_refl (term5 A b a x)). Qed.
Lemma lem15316 {A : Type'} (b : A) (a : A) : (term6 A b a) = (term4 A b a).
Proof. exact (fun_ext (fun x : Prop => @lem15315 A x b a)). Qed.
Lemma lem15317 : False = False.
Proof. exact (eq_refl False). Qed.
Lemma lem15318 {A : Type'} (b : A) (a : A) : (term2 A b a) = (term3 A b a).
Proof. exact (MK_COMB (@lem15316 A b a) (@lem15317)). Qed.
Lemma lem15319 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem15320 {A : Type'} (b : A) (a : A) : (term7 A b a) = (term8 A b a).
Proof. exact (MK_COMB (@lem15319 A) (@lem15318 A b a)). Qed.
Lemma lem15321 {A : Type'} (b : A) (a : A) : (term3 A b a) = (@COND A False b a).
Proof. exact (eq_refl (term3 A b a)). Qed.
Lemma lem15322 {A : Type'} (b : A) (a : A) : ((term2 A b a) = (term3 A b a)) = ((term3 A b a) = (@COND A False b a)).
Proof. exact (MK_COMB (@lem15320 A b a) (@lem15321 A b a)). Qed.
Lemma lem15323 {A : Type'} (b : A) (a : A) : (term3 A b a) = (@COND A False b a).
Proof. exact (EQ_MP (@lem15322 A b a) (@lem15314 A b a)). Qed.
Lemma lem15325 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem15326 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (@lem15325 A t1 t2). Qed.
Lemma lem15327 {A : Type'} (b : A) (a : A) : (@COND A False b a) = a.
Proof. exact (@lem15326 A b a). Qed.
Lemma lem15328 {A : Type'} (b : A) (a : A) : (term3 A b a) = a.
Proof. exact (TRANS (@lem15323 A b a) (@lem15327 A b a)). Qed.
Lemma lem15329 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem15330 {A : Type'} (b : A) (a : A) : (term8 A b a) = (@eq A a).
Proof. exact (MK_COMB (@lem15329 A) (@lem15328 A b a)). Qed.
Lemma lem15331 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem15332 {A : Type'} (b : A) (a : A) : ((term3 A b a) = a) = (a = a).
Proof. exact (MK_COMB (@lem15330 A b a) (@lem15331 A a)). Qed.
Lemma lem15334 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem15334 A x). Qed.
Lemma lem15336 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem15335 A a). Qed.
Lemma lem15337 {A : Type'} (b : A) (a : A) : ((term3 A b a) = a) = True.
Proof. exact (TRANS (@lem15332 A b a) (@lem15336 A a)). Qed.
Lemma lem15338 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem15339 {A : Type'} (b : A) (a : A) : (term9 A b a) = (and True).
Proof. exact (MK_COMB (@lem15338) (@lem15337 A b a)). Qed.
Lemma lem15343 {A B : Type'} (f : A -> B) (y : A) : (term0 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem15344 {A : Type'} (f : Prop -> A) (y : Prop) : (term1 A f y) = (f y).
Proof. exact (@lem15343 Prop A f y). Qed.
Lemma lem15345 {A : Type'} (b : A) (a : A) : (term10 A b a) = (term11 A b a).
Proof. exact (@lem15344 A (term4 A b a) True). Qed.
Lemma lem15346 {A : Type'} (x : Prop) (b : A) (a : A) : (term5 A b a x) = (@COND A x b a).
Proof. exact (eq_refl (term5 A b a x)). Qed.
Lemma lem15347 {A : Type'} (b : A) (a : A) : (term6 A b a) = (term4 A b a).
Proof. exact (fun_ext (fun x : Prop => @lem15346 A x b a)). Qed.
Lemma lem15348 : True = True.
Proof. exact (eq_refl True). Qed.
Lemma lem15349 {A : Type'} (b : A) (a : A) : (term10 A b a) = (term11 A b a).
Proof. exact (MK_COMB (@lem15347 A b a) (@lem15348)). Qed.
Lemma lem15350 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem15351 {A : Type'} (b : A) (a : A) : (term12 A b a) = (term13 A b a).
Proof. exact (MK_COMB (@lem15350 A) (@lem15349 A b a)). Qed.
Lemma lem15352 {A : Type'} (b : A) (a : A) : (term11 A b a) = (@COND A True b a).
Proof. exact (eq_refl (term11 A b a)). Qed.
Lemma lem15353 {A : Type'} (b : A) (a : A) : ((term10 A b a) = (term11 A b a)) = ((term11 A b a) = (@COND A True b a)).
Proof. exact (MK_COMB (@lem15351 A b a) (@lem15352 A b a)). Qed.
Lemma lem15354 {A : Type'} (b : A) (a : A) : (term11 A b a) = (@COND A True b a).
Proof. exact (EQ_MP (@lem15353 A b a) (@lem15345 A b a)). Qed.
Lemma lem15356 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem15357 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (@lem15356 A t2 t1). Qed.
Lemma lem15358 {A : Type'} (a : A) (b : A) : (@COND A True b a) = b.
Proof. exact (@lem15357 A a b). Qed.
Lemma lem15359 {A : Type'} (a : A) (b : A) : (term11 A b a) = b.
Proof. exact (TRANS (@lem15354 A b a) (@lem15358 A a b)). Qed.
Lemma lem15360 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem15361 {A : Type'} (a : A) (b : A) : (term13 A b a) = (@eq A b).
Proof. exact (MK_COMB (@lem15360 A) (@lem15359 A a b)). Qed.
Lemma lem15362 {A : Type'} (b : A) : b = b.
Proof. exact (eq_refl b). Qed.
Lemma lem15363 {A : Type'} (a : A) (b : A) : ((term11 A b a) = b) = (b = b).
Proof. exact (MK_COMB (@lem15361 A a b) (@lem15362 A b)). Qed.
Lemma lem15365 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem15366 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem15365 A x). Qed.
Lemma lem15367 {A : Type'} (b : A) : (b = b) = True.
Proof. exact (@lem15366 A b). Qed.
Lemma lem15368 {A : Type'} (a : A) (b : A) : ((term11 A b a) = b) = True.
Proof. exact (TRANS (@lem15363 A a b) (@lem15367 A b)). Qed.
Lemma lem15369 {A : Type'} (a : A) (b : A) : (term14 A a b) = (True /\ True).
Proof. exact (MK_COMB (@lem15339 A b a) (@lem15368 A a b)). Qed.
Lemma lem15371 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem15372 : (True /\ True) = True.
Proof. exact (@lem15371 True). Qed.
Lemma lem15373 {A : Type'} (a : A) (b : A) : (term14 A a b) = True.
Proof. exact (TRANS (@lem15369 A a b) (@lem15372)). Qed.
Lemma lem15374 {A : Type'} (a : A) (b : A) : True = (term14 A a b).
Proof. exact (SYM (@lem15373 A a b)). Qed.
Lemma lem15375 {A : Type'} (a : A) (b : A) : term14 A a b.
Proof. exact (EQ_MP (@lem15374 A a b) (@lem0)). Qed.
Lemma lem15376 {A : Type'} (a : A) (b : A) : term15 A a b.
Proof. exact (ex_intro (term16 A a b) (term4 A b a) (@lem15375 A a b)). Qed.
Lemma lem15381 {A : Type'} (a : A) : term17 A a.
Proof. exact (fun b : A => @lem15376 A a b). Qed.
Lemma lem15386 {A : Type'} : term18 A.
Proof. exact (fun a : A => @lem15381 A a). Qed.
