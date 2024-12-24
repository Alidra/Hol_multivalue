Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EXISTS_UNIQUE_REFL_term_abbrevs.
Require Import EXISTS_UNIQUE_THM_spec.
Require Import thm0_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4364 {A : Type'} (P : A -> Prop) : term0 A P.
Proof. exact (@lem4356 A P). Qed.
Lemma lem4365 {A : Type'} (P : A -> Prop) : (term0 A P) = ((term1 A P) = (term2 A P)).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4368 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (EQ_MP (@lem4365 A P) (@lem4364 A P)). Qed.
Lemma lem4369 {A : Type'} (P : A -> Prop) : (term1 A P) = (term2 A P).
Proof. exact (@lem4368 A P). Qed.
Lemma lem4370 {A : Type'} (a : A) : (term3 A a) = (term4 A a).
Proof. exact (@lem4369 A (term5 A a)). Qed.
Lemma lem4371 {A : Type'} (x : A) (a : A) : (term6 A a x) = (x = a).
Proof. exact (eq_refl (term6 A a x)). Qed.
Lemma lem4372 {A : Type'} (a : A) : (term7 A a) = (term5 A a).
Proof. exact (fun_ext (fun x : A => @lem4371 A x a)). Qed.
Lemma lem4373 {A : Type'} : (@ex1 A) = (@ex1 A).
Proof. exact (eq_refl (@ex1 A)). Qed.
Lemma lem4374 {A : Type'} (a : A) : (term3 A a) = (term8 A a).
Proof. exact (MK_COMB (@lem4373 A) (@lem4372 A a)). Qed.
Lemma lem4375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4376 {A : Type'} (a : A) : (term9 A a) = (term10 A a).
Proof. exact (MK_COMB (@lem4375) (@lem4374 A a)). Qed.
Lemma lem4377 {A : Type'} (x : A) (a : A) : (term6 A a x) = (x = a).
Proof. exact (eq_refl (term6 A a x)). Qed.
Lemma lem4378 {A : Type'} (a : A) : (term7 A a) = (term5 A a).
Proof. exact (fun_ext (fun x : A => @lem4377 A x a)). Qed.
Lemma lem4379 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4380 {A : Type'} (a : A) : (term11 A a) = (term12 A a).
Proof. exact (MK_COMB (@lem4379 A) (@lem4378 A a)). Qed.
Lemma lem4381 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4382 {A : Type'} (a : A) : (term13 A a) = (term14 A a).
Proof. exact (MK_COMB (@lem4381) (@lem4380 A a)). Qed.
Lemma lem4383 {A : Type'} (x : A) (a : A) : (term6 A a x) = (x = a).
Proof. exact (eq_refl (term6 A a x)). Qed.
Lemma lem4384 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4385 {A : Type'} (x : A) (a : A) : (term15 A a x) = (term16 A x a).
Proof. exact (MK_COMB (@lem4384) (@lem4383 A x a)). Qed.
Lemma lem4386 {A : Type'} (x' : A) (a : A) : (term6 A a x') = (x' = a).
Proof. exact (eq_refl (term6 A a x')). Qed.
Lemma lem4387 {A : Type'} (x : A) (x' : A) (a : A) : (term17 A x a x') = (term18 A x x' a).
Proof. exact (MK_COMB (@lem4385 A x a) (@lem4386 A x' a)). Qed.
Lemma lem4388 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4389 {A : Type'} (x : A) (x' : A) (a : A) : (term19 A x a x') = (term20 A x x' a).
Proof. exact (MK_COMB (@lem4388) (@lem4387 A x x' a)). Qed.
Lemma lem4390 {A : Type'} (x : A) (x' : A) : (x = x') = (x = x').
Proof. exact (eq_refl (x = x')). Qed.
Lemma lem4391 {A : Type'} (a : A) (x : A) (x' : A) : (term21 A a x x') = (term22 A a x x').
Proof. exact (MK_COMB (@lem4389 A x x' a) (@lem4390 A x x')). Qed.
Lemma lem4392 {A : Type'} (a : A) (x : A) : (term23 A a x) = (term24 A a x).
Proof. exact (fun_ext (fun x' : A => @lem4391 A a x x')). Qed.
Lemma lem4393 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4394 {A : Type'} (a : A) (x : A) : (term25 A a x) = (term26 A a x).
Proof. exact (MK_COMB (@lem4393 A) (@lem4392 A a x)). Qed.
Lemma lem4395 {A : Type'} (a : A) : (term27 A a) = (term28 A a).
Proof. exact (fun_ext (fun x : A => @lem4394 A a x)). Qed.
Lemma lem4396 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4397 {A : Type'} (a : A) : (term29 A a) = (term30 A a).
Proof. exact (MK_COMB (@lem4396 A) (@lem4395 A a)). Qed.
Lemma lem4398 {A : Type'} (a : A) : (term4 A a) = (term31 A a).
Proof. exact (MK_COMB (@lem4382 A a) (@lem4397 A a)). Qed.
Lemma lem4399 {A : Type'} (a : A) : ((term3 A a) = (term4 A a)) = ((term8 A a) = (term31 A a)).
Proof. exact (MK_COMB (@lem4376 A a) (@lem4398 A a)). Qed.
Lemma lem4400 {A : Type'} (a : A) : (term8 A a) = (term31 A a).
Proof. exact (EQ_MP (@lem4399 A a) (@lem4370 A a)). Qed.
Lemma lem4427 {A : Type'} (a : A) : (term31 A a) = (term8 A a).
Proof. exact (SYM (@lem4400 A a)). Qed.
Lemma lem4428 {A : Type'} (x : A) (x' : A) (a : A) (h1 : term18 A x x' a) : term18 A x x' a.
Proof. exact (h1). Qed.
Lemma lem4429 {A : Type'} (x' : A) (a : A) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem4430 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4434 {A : Type'} (x : A) (a : A) (h1 : x = a) : x = a.
Proof. exact (h1). Qed.
Lemma lem4435 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4436 {A : Type'} (x : A) (a : A) (h1 : x = a) : (@eq A x) = (@eq A a).
Proof. exact (MK_COMB (@lem4435 A) (@lem4434 A x a h1)). Qed.
Lemma lem4438 {A : Type'} (x' : A) (a : A) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem4439 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : (x = x') = (a = a).
Proof. exact (MK_COMB (@lem4436 A x a h1) (@lem4438 A x' a h2)). Qed.
Lemma lem4441 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4442 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4441 A x). Qed.
Lemma lem4443 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem4442 A a). Qed.
Lemma lem4444 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : (x = x') = True.
Proof. exact (TRANS (@lem4439 A x x' a h1 h2) (@lem4443 A a)). Qed.
Lemma lem4445 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : True = (x = x').
Proof. exact (SYM (@lem4444 A x x' a h1 h2)). Qed.
Lemma lem4446 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : x = x'.
Proof. exact (EQ_MP (@lem4445 A x x' a h1 h2) (@lem0)). Qed.
Lemma lem4447 {A : Type'} (a : A) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem4448 {A : Type'} (a : A) : term12 A a.
Proof. exact (ex_intro (term5 A a) a (@lem4447 A a)). Qed.
Lemma lem4449 {A : Type'} (x : A) (x' : A) (a : A) (h1 : term18 A x x' a) : x' = a.
Proof. exact (proj2 (@lem4428 A x x' a h1)). Qed.
Lemma lem4450 {A : Type'} (x : A) (x' : A) (a : A) (h1 : term18 A x x' a) : x = a.
Proof. exact (proj1 (@lem4428 A x x' a h1)). Qed.
Lemma lem4451 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : (x' = a) = (x = x').
Proof. exact (prop_ext (fun h3 : x' = a => @lem4446 A x x' a h1 h2) (fun h3 : x = x' => @lem4429 A x' a h2)). Qed.
Lemma lem4452 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : x = x'.
Proof. exact (EQ_MP (@lem4451 A x x' a h1 h2) (@lem4429 A x' a h2)). Qed.
Lemma lem4453 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : (x = a) = (x = x').
Proof. exact (prop_ext (fun h3 : x = a => @lem4452 A x x' a h1 h2) (fun h3 : x = x' => @lem4430 A x a h1)). Qed.
Lemma lem4454 {A : Type'} (x : A) (x' : A) (a : A) (h1 : x = a) (h2 : x' = a) : x = x'.
Proof. exact (EQ_MP (@lem4453 A x x' a h1 h2) (@lem4430 A x a h1)). Qed.
Lemma lem4455 {A : Type'} (x' : A) (x : A) (a : A) (h1 : term18 A x x' a) (h2 : x = a) : (x' = a) = (x = x').
Proof. exact (prop_ext (fun h3 : x' = a => @lem4454 A x x' a h2 h3) (fun h3 : x = x' => @lem4449 A x x' a h1)). Qed.
Lemma lem4456 {A : Type'} (x' : A) (x : A) (a : A) (h1 : term18 A x x' a) (h2 : x = a) : x = x'.
Proof. exact (EQ_MP (@lem4455 A x' x a h1 h2) (@lem4449 A x x' a h1)). Qed.
Lemma lem4457 {A : Type'} (x : A) (x' : A) (a : A) (h1 : term18 A x x' a) : (x = a) = (x = x').
Proof. exact (prop_ext (fun h2 : x = a => @lem4456 A x' x a h1 h2) (fun h2 : x = x' => @lem4450 A x x' a h1)). Qed.
Lemma lem4458 {A : Type'} (x : A) (x' : A) (a : A) (h1 : term18 A x x' a) : x = x'.
Proof. exact (EQ_MP (@lem4457 A x x' a h1) (@lem4450 A x x' a h1)). Qed.
Lemma lem4459 {A : Type'} (a : A) (x : A) (x' : A) : term22 A a x x'.
Proof. exact (fun h0 : term18 A x x' a => @lem4458 A x x' a h0). Qed.
Lemma lem4464 {A : Type'} (a : A) (x : A) : term26 A a x.
Proof. exact (fun x' : A => @lem4459 A a x x'). Qed.
Lemma lem4469 {A : Type'} (a : A) : term30 A a.
Proof. exact (fun x : A => @lem4464 A a x). Qed.
Lemma lem4470 {A : Type'} (a : A) : term31 A a.
Proof. exact (conj (@lem4448 A a) (@lem4469 A a)). Qed.
Lemma lem4471 {A : Type'} (a : A) : term8 A a.
Proof. exact (EQ_MP (@lem4427 A a) (@lem4470 A a)). Qed.
Lemma lem4476 {A : Type'} : term32 A.
Proof. exact (fun a : A => @lem4471 A a). Qed.
