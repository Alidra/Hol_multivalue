Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_ANTISYM_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3218234 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3218235 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3218234 A s t). Qed.
Lemma lem3218242 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218243 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term1 A s t) = (term2 A s t).
Proof. exact (MK_COMB (@lem3218242) (@lem3218235 A s t)). Qed.
Lemma lem3218245 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3218246 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3218245 A s t). Qed.
Lemma lem3218247 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (@SUBSET A t s) = (term0 A t s).
Proof. exact (@lem3218246 A t s). Qed.
Lemma lem3218254 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term3 A t s) = (term4 A t s).
Proof. exact (MK_COMB (@lem3218243 A s t) (@lem3218247 A t s)). Qed.
Lemma lem3218257 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218258 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term5 A t s) = (term6 A t s).
Proof. exact (MK_COMB (@lem3218257) (@lem3218254 A t s)). Qed.
Lemma lem3218262 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3218263 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term7 A s t).
Proof. exact (@lem3218262 A s t). Qed.
Lemma lem3218272 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term3 A t s) = (s = t)) = ((term4 A t s) = (term7 A s t)).
Proof. exact (MK_COMB (@lem3218258 A t s) (@lem3218263 A s t)). Qed.
Lemma lem3218277 {A : Type'} (s : A -> Prop) : (term8 A s) = (term9 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3218272 A s t)). Qed.
Lemma lem3218278 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3218279 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (MK_COMB (@lem3218278 A) (@lem3218277 A s)). Qed.
Lemma lem3218284 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3218279 A s)). Qed.
Lemma lem3218285 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3218286 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3218285 A) (@lem3218284 A)). Qed.
Lemma lem3218291 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3218286 A)). Qed.
Lemma lem3218311 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3218312 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3218311 A P x). Qed.
Lemma lem3218313 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3218312 A s x). Qed.
Lemma lem3218314 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3218315 {A : Type'} (s : A -> Prop) (x : A) : (term16 A x s) = (term17 A s x).
Proof. exact (MK_COMB (@lem3218314) (@lem3218313 A s x)). Qed.
Lemma lem3218317 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3218318 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3218317 A P x). Qed.
Lemma lem3218319 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3218318 A t x). Qed.
Lemma lem3218320 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term18 A s x t) = (term19 A s t x).
Proof. exact (MK_COMB (@lem3218315 A s x) (@lem3218319 A t x)). Qed.
Lemma lem3218323 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term20 A s t) = (term21 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218320 A s t x)). Qed.
Lemma lem3218324 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218325 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term22 A s t).
Proof. exact (MK_COMB (@lem3218324 A) (@lem3218323 A s t)). Qed.
Lemma lem3218330 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term2 A s t) = (term23 A s t).
Proof. exact (MK_COMB (@lem3218330) (@lem3218325 A s t)). Qed.
Lemma lem3218339 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3218340 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3218339 A P x). Qed.
Lemma lem3218341 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3218340 A t x). Qed.
Lemma lem3218342 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3218343 {A : Type'} (t : A -> Prop) (x : A) : (term16 A x t) = (term17 A t x).
Proof. exact (MK_COMB (@lem3218342) (@lem3218341 A t x)). Qed.
Lemma lem3218345 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3218346 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3218345 A P x). Qed.
Lemma lem3218347 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3218346 A s x). Qed.
Lemma lem3218348 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term18 A t x s) = (term19 A t s x).
Proof. exact (MK_COMB (@lem3218343 A t x) (@lem3218347 A s x)). Qed.
Lemma lem3218351 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term20 A t s) = (term21 A t s).
Proof. exact (fun_ext (fun x : A => @lem3218348 A t s x)). Qed.
Lemma lem3218352 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218353 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term0 A t s) = (term22 A t s).
Proof. exact (MK_COMB (@lem3218352 A) (@lem3218351 A t s)). Qed.
Lemma lem3218358 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term4 A t s) = (term24 A t s).
Proof. exact (MK_COMB (@lem3218331 A s t) (@lem3218353 A t s)). Qed.
Lemma lem3218361 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218362 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term6 A t s) = (term25 A t s).
Proof. exact (MK_COMB (@lem3218361) (@lem3218358 A t s)). Qed.
Lemma lem3218370 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3218371 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3218370 A P x). Qed.
Lemma lem3218372 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3218371 A s x). Qed.
Lemma lem3218373 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218374 {A : Type'} (s : A -> Prop) (x : A) : (term26 A x s) = (term27 A s x).
Proof. exact (MK_COMB (@lem3218373) (@lem3218372 A s x)). Qed.
Lemma lem3218376 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3218377 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3218376 A P x). Qed.
Lemma lem3218378 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3218377 A t x). Qed.
Lemma lem3218379 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((@IN A x s) = (@IN A x t)) = ((s x) = (t x)).
Proof. exact (MK_COMB (@lem3218374 A s x) (@lem3218378 A t x)). Qed.
Lemma lem3218382 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term28 A s t) = (term29 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218379 A s t x)). Qed.
Lemma lem3218383 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218384 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term7 A s t) = (term30 A s t).
Proof. exact (MK_COMB (@lem3218383 A) (@lem3218382 A s t)). Qed.
Lemma lem3218389 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term4 A t s) = (term7 A s t)) = ((term24 A t s) = (term30 A s t)).
Proof. exact (MK_COMB (@lem3218362 A t s) (@lem3218384 A s t)). Qed.
Lemma lem3218392 {A : Type'} (s : A -> Prop) : (term9 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3218389 A s t)). Qed.
Lemma lem3218393 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3218394 {A : Type'} (s : A -> Prop) : (term11 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3218393 A) (@lem3218392 A s)). Qed.
Lemma lem3218399 {A : Type'} : (term13 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3218394 A s)). Qed.
Lemma lem3218400 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3218401 {A : Type'} : (term15 A) = (term34 A).
Proof. exact (MK_COMB (@lem3218400 A) (@lem3218399 A)). Qed.
Lemma lem3218406 {A : Type'} : (term34 A) = (term15 A).
Proof. exact (SYM (@lem3218401 A)). Qed.
Lemma lem3218408 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3218409 {A : Type'} : (term34 A) = (term36 A).
Proof. exact (@lem3218408 (term34 A)). Qed.
Lemma lem3218410 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (SYM (@lem3218409 A)). Qed.
Lemma lem3218411 {A : Type'} (h1 : term37 A) : term37 A.
Proof. exact (h1). Qed.
Lemma lem3218414 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3218415 {A : Type'} : term38 A.
Proof. exact (fun h0 : term36 A => @lem3218414 A h0). Qed.
Lemma lem3218416 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3218417 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3218418 {A : Type'} (h1 : term36 A) (h2 : term38 A) : term36 A.
Proof. exact (@lem3218416 A h2 (@lem3218417 A h1)). Qed.
Lemma lem3218419 {A : Type'} (h1 : term36 A) : term39 A.
Proof. exact (fun h0 : term38 A => @lem3218418 A h1 h0). Qed.
Lemma lem3218420 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (h1). Qed.
Lemma lem3218421 {A : Type'} (h1 : term36 A) (h2 : term38 A) : term36 A.
Proof. exact (@lem3218419 A h1 (@lem3218420 A h2)). Qed.
Lemma lem3218422 {A : Type'} (h1 : term38 A) : term38 A.
Proof. exact (fun h0 : term36 A => @lem3218421 A h0 h1). Qed.
Lemma lem3218423 {A : Type'} : term40 A.
Proof. exact (fun h0 : term38 A => @lem3218422 A h0). Qed.
Lemma lem3218426 {A : Type'} : term38 A.
Proof. exact (@lem3218423 A (@lem3218415 A)). Qed.
Lemma lem3218427 {A : Type'} : term38 A.
Proof. exact (@lem3218426 A). Qed.
Lemma lem3218429 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3218430 {A : Type'} : (term36 A) = (term41 A).
Proof. exact (@lem3218429 (term37 A)). Qed.
Lemma lem3218432 (t : Prop) : (term42 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3218433 {A : Type'} : (term41 A) = (term34 A).
Proof. exact (@lem3218432 (term34 A)). Qed.
Lemma lem3218464 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (TRANS (@lem3218430 A) (@lem3218433 A)). Qed.
Lemma lem3218469 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = ((s x) = (t x)).
Proof. exact (eq_refl ((s x) = (t x))). Qed.
Lemma lem3218470 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term29 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218469 A s t x)). Qed.
Lemma lem3218471 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218472 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term30 A s t).
Proof. exact (MK_COMB (@lem3218471 A) (@lem3218470 A s t)). Qed.
Lemma lem3218477 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term19 A t s x) = (term19 A t s x).
Proof. exact (eq_refl (term19 A t s x)). Qed.
Lemma lem3218478 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term21 A t s) = (term21 A t s).
Proof. exact (fun_ext (fun x : A => @lem3218477 A t s x)). Qed.
Lemma lem3218479 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218480 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term22 A t s) = (term22 A t s).
Proof. exact (MK_COMB (@lem3218479 A) (@lem3218478 A t s)). Qed.
Lemma lem3218485 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term19 A s t x) = (term19 A s t x).
Proof. exact (eq_refl (term19 A s t x)). Qed.
Lemma lem3218486 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = (term21 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218485 A s t x)). Qed.
Lemma lem3218487 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218488 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term22 A s t).
Proof. exact (MK_COMB (@lem3218487 A) (@lem3218486 A s t)). Qed.
Lemma lem3218489 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218490 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term23 A s t).
Proof. exact (MK_COMB (@lem3218489) (@lem3218488 A s t)). Qed.
Lemma lem3218491 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term24 A t s).
Proof. exact (MK_COMB (@lem3218490 A s t) (@lem3218480 A t s)). Qed.
Lemma lem3218492 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218493 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term25 A t s) = (term25 A t s).
Proof. exact (MK_COMB (@lem3218492) (@lem3218491 A t s)). Qed.
Lemma lem3218494 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term24 A t s) = (term30 A s t)) = ((term24 A t s) = (term30 A s t)).
Proof. exact (MK_COMB (@lem3218493 A t s) (@lem3218472 A s t)). Qed.
Lemma lem3218495 {A : Type'} (s : A -> Prop) : (term31 A s) = (term31 A s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3218494 A s t)). Qed.
Lemma lem3218496 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3218497 {A : Type'} (s : A -> Prop) : (term32 A s) = (term32 A s).
Proof. exact (MK_COMB (@lem3218496 A) (@lem3218495 A s)). Qed.
Lemma lem3218498 {A : Type'} : (term33 A) = (term33 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3218497 A s)). Qed.
Lemma lem3218499 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3218500 {A : Type'} : (term34 A) = (term34 A).
Proof. exact (MK_COMB (@lem3218499 A) (@lem3218498 A)). Qed.
Lemma lem3218539 {A : Type'} : (term36 A) = (term34 A).
Proof. exact (TRANS (@lem3218464 A) (@lem3218500 A)). Qed.
Lemma lem3218540 {A : Type'} : (term34 A) = (term36 A).
Proof. exact (SYM (@lem3218539 A)). Qed.
Lemma lem3218542 (p : Prop) : p = (term35 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3218543 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term24 A t s) = (term30 A s t)) = (term43 A s t).
Proof. exact (@lem3218542 ((term24 A t s) = (term30 A s t))). Qed.
Lemma lem3218544 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term43 A s t) = ((term24 A t s) = (term30 A s t)).
Proof. exact (SYM (@lem3218543 A s t)). Qed.
Lemma lem3218545 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term44 A s t.
Proof. exact (h1). Qed.
Lemma lem3218554 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term45 A s t x) = (term46 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3218559 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term19 A s t x) = (term47 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3218560 {A : Type'} (P : A -> Prop) : (term48 A P) = (term49 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3218561 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term51 A s t).
Proof. exact (@lem3218560 A (term21 A s t)). Qed.
Lemma lem3218562 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term52 A s t x) = (term19 A s t x).
Proof. exact (eq_refl (term52 A s t x)). Qed.
Lemma lem3218563 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3218564 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term45 A s t x).
Proof. exact (MK_COMB (@lem3218563) (@lem3218562 A s t x)). Qed.
Lemma lem3218565 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term53 A s t x) = (term46 A s t x).
Proof. exact (TRANS (@lem3218564 A s t x) (@lem3218554 A s t x)). Qed.
Lemma lem3218566 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term54 A s t) = (term55 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218565 A s t x)). Qed.
Lemma lem3218567 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218568 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term51 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3218567 A) (@lem3218566 A s t)). Qed.
Lemma lem3218569 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term50 A s t) = (term56 A s t).
Proof. exact (TRANS (@lem3218561 A s t) (@lem3218568 A s t)). Qed.
Lemma lem3218570 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term21 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218559 A s t x)). Qed.
Lemma lem3218571 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218572 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term22 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3218571 A) (@lem3218570 A s t)). Qed.
Lemma lem3218581 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term45 A t s x) = (term46 A t s x).
Proof. exact (@lem17362 (t x) (s x)). Qed.
Lemma lem3218586 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term19 A t s x) = (term47 A t s x).
Proof. exact (@lem17265 (t x) (s x)). Qed.
Lemma lem3218587 {A : Type'} (P : A -> Prop) : (term48 A P) = (term49 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3218588 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term51 A t s).
Proof. exact (@lem3218587 A (term21 A t s)). Qed.
Lemma lem3218589 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term52 A t s x) = (term19 A t s x).
Proof. exact (eq_refl (term52 A t s x)). Qed.
Lemma lem3218590 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3218591 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term53 A t s x) = (term45 A t s x).
Proof. exact (MK_COMB (@lem3218590) (@lem3218589 A t s x)). Qed.
Lemma lem3218592 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term53 A t s x) = (term46 A t s x).
Proof. exact (TRANS (@lem3218591 A t s x) (@lem3218581 A t s x)). Qed.
Lemma lem3218593 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term54 A t s) = (term55 A t s).
Proof. exact (fun_ext (fun x : A => @lem3218592 A t s x)). Qed.
Lemma lem3218594 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218595 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term51 A t s) = (term56 A t s).
Proof. exact (MK_COMB (@lem3218594 A) (@lem3218593 A t s)). Qed.
Lemma lem3218596 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term50 A t s) = (term56 A t s).
Proof. exact (TRANS (@lem3218588 A t s) (@lem3218595 A t s)). Qed.
Lemma lem3218597 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term21 A t s) = (term57 A t s).
Proof. exact (fun_ext (fun x : A => @lem3218586 A t s x)). Qed.
Lemma lem3218598 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218599 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term22 A t s) = (term58 A t s).
Proof. exact (MK_COMB (@lem3218598 A) (@lem3218597 A t s)). Qed.
Lemma lem3218600 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3218601 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term60 A s t).
Proof. exact (MK_COMB (@lem3218600) (@lem3218569 A s t)). Qed.
Lemma lem3218602 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term61 A t s) = (term62 A t s).
Proof. exact (MK_COMB (@lem3218601 A s t) (@lem3218596 A t s)). Qed.
Lemma lem3218603 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term63 A t s) = (term61 A t s).
Proof. exact (@lem17045 (term22 A s t) (term22 A t s)). Qed.
Lemma lem3218604 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term63 A t s) = (term62 A t s).
Proof. exact (TRANS (@lem3218603 A t s) (@lem3218602 A t s)). Qed.
Lemma lem3218605 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218606 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term23 A s t) = (term64 A s t).
Proof. exact (MK_COMB (@lem3218605) (@lem3218572 A s t)). Qed.
Lemma lem3218607 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term24 A t s) = (term65 A t s).
Proof. exact (MK_COMB (@lem3218606 A s t) (@lem3218599 A t s)). Qed.
Lemma lem3218622 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term66 A s t x) = (term67 A s t x).
Proof. exact (@lem17930 (s x) (t x)). Qed.
Lemma lem3218633 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : ((s x) = (t x)) = (term68 A s t x).
Proof. exact (@lem17784 (s x) (t x)). Qed.
Lemma lem3218634 {A : Type'} (P : A -> Prop) : (term48 A P) = (term49 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3218635 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term69 A s t) = (term70 A s t).
Proof. exact (@lem3218634 A (term29 A s t)). Qed.
Lemma lem3218636 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = ((s x) = (t x)).
Proof. exact (eq_refl (term71 A s t x)). Qed.
Lemma lem3218637 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3218638 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term66 A s t x).
Proof. exact (MK_COMB (@lem3218637) (@lem3218636 A s t x)). Qed.
Lemma lem3218639 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term72 A s t x) = (term67 A s t x).
Proof. exact (TRANS (@lem3218638 A s t x) (@lem3218622 A s t x)). Qed.
Lemma lem3218640 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term73 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218639 A s t x)). Qed.
Lemma lem3218641 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218642 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term70 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3218641 A) (@lem3218640 A s t)). Qed.
Lemma lem3218643 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term69 A s t) = (term75 A s t).
Proof. exact (TRANS (@lem3218635 A s t) (@lem3218642 A s t)). Qed.
Lemma lem3218644 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term29 A s t) = (term76 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218633 A s t x)). Qed.
Lemma lem3218645 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218646 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term30 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3218645 A) (@lem3218644 A s t)). Qed.
Lemma lem3218647 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218648 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term78 A t s) = (term79 A t s).
Proof. exact (MK_COMB (@lem3218647) (@lem3218604 A t s)). Qed.
Lemma lem3218649 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term80 A s t) = (term81 A s t).
Proof. exact (MK_COMB (@lem3218648 A t s) (@lem3218646 A s t)). Qed.
Lemma lem3218650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218651 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term82 A t s) = (term83 A t s).
Proof. exact (MK_COMB (@lem3218650) (@lem3218607 A t s)). Qed.
Lemma lem3218652 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3218651 A t s) (@lem3218643 A s t)). Qed.
Lemma lem3218653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3218654 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term86 A s t) = (term87 A s t).
Proof. exact (MK_COMB (@lem3218653) (@lem3218652 A s t)). Qed.
Lemma lem3218655 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term88 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem3218654 A s t) (@lem3218649 A s t)). Qed.
Lemma lem3218656 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = (term88 A s t).
Proof. exact (@lem17646 (term24 A t s) (term30 A s t)). Qed.
Lemma lem3218657 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = (term89 A s t).
Proof. exact (TRANS (@lem3218656 A s t) (@lem3218655 A s t)). Qed.
Lemma lem3218827 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3218828 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term90 A P Q) = (term91 A P Q).
Proof. exact (@lem3218827 A P Q). Qed.
Lemma lem3218829 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term93 A s t).
Proof. exact (@lem3218828 A (term94 A s t) (term57 A s t)). Qed.
Lemma lem3218830 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term95 A s t x) = (term96 A s t x).
Proof. exact (eq_refl (term95 A s t x)). Qed.
Lemma lem3218831 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218832 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term97 A s t x) = (term98 A s t x).
Proof. exact (MK_COMB (@lem3218831) (@lem3218830 A s t x)). Qed.
Lemma lem3218833 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term99 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term99 A s t x)). Qed.
Lemma lem3218834 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term100 A s t x) = (term68 A s t x).
Proof. exact (MK_COMB (@lem3218832 A s t x) (@lem3218833 A s t x)). Qed.
Lemma lem3218835 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term101 A s t) = (term76 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218834 A s t x)). Qed.
Lemma lem3218836 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218837 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term92 A s t) = (term77 A s t).
Proof. exact (MK_COMB (@lem3218836 A) (@lem3218835 A s t)). Qed.
Lemma lem3218838 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218839 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term102 A s t) = (term103 A s t).
Proof. exact (MK_COMB (@lem3218838) (@lem3218837 A s t)). Qed.
Lemma lem3218840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term95 A s t x) = (term96 A s t x).
Proof. exact (eq_refl (term95 A s t x)). Qed.
Lemma lem3218841 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term104 A s t) = (term94 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218840 A s t x)). Qed.
Lemma lem3218842 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218843 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term105 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3218842 A) (@lem3218841 A s t)). Qed.
Lemma lem3218844 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218845 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term107 A s t) = (term108 A s t).
Proof. exact (MK_COMB (@lem3218844) (@lem3218843 A s t)). Qed.
Lemma lem3218846 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term99 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term99 A s t x)). Qed.
Lemma lem3218847 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term109 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218846 A s t x)). Qed.
Lemma lem3218848 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3218849 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term110 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3218848 A) (@lem3218847 A s t)). Qed.
Lemma lem3218850 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term93 A s t) = (term111 A s t).
Proof. exact (MK_COMB (@lem3218845 A s t) (@lem3218849 A s t)). Qed.
Lemma lem3218851 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term92 A s t) = (term93 A s t)) = ((term77 A s t) = (term111 A s t)).
Proof. exact (MK_COMB (@lem3218839 A s t) (@lem3218850 A s t)). Qed.
Lemma lem3218852 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term77 A s t) = (term111 A s t).
Proof. exact (EQ_MP (@lem3218851 A s t) (@lem3218829 A s t)). Qed.
Lemma lem3218913 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A t s) = (term79 A t s).
Proof. exact (eq_refl (term79 A t s)). Qed.
Lemma lem3218914 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term81 A s t) = (term112 A s t).
Proof. exact (MK_COMB (@lem3218913 A t s) (@lem3218852 A s t)). Qed.
Lemma lem3218915 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term87 A s t).
Proof. exact (eq_refl (term87 A s t)). Qed.
Lemma lem3218916 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term113 A s t).
Proof. exact (MK_COMB (@lem3218915 A s t) (@lem3218914 A s t)). Qed.
Lemma lem3218918 {A : Type'} (P : Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3218919 {A : Type'} (P : Prop) (Q : A -> Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (@lem3218918 A P Q). Qed.
Lemma lem3218920 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term117 A s t).
Proof. exact (@lem3218919 A (term65 A t s) (term74 A s t)). Qed.
Lemma lem3218921 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term118 A s t x) = (term67 A s t x).
Proof. exact (eq_refl (term118 A s t x)). Qed.
Lemma lem3218922 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term119 A s t) = (term74 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218921 A s t x)). Qed.
Lemma lem3218923 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218924 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term120 A s t) = (term75 A s t).
Proof. exact (MK_COMB (@lem3218923 A) (@lem3218922 A s t)). Qed.
Lemma lem3218925 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term83 A t s) = (term83 A t s).
Proof. exact (eq_refl (term83 A t s)). Qed.
Lemma lem3218926 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term85 A s t).
Proof. exact (MK_COMB (@lem3218925 A t s) (@lem3218924 A s t)). Qed.
Lemma lem3218927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218928 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term121 A s t) = (term122 A s t).
Proof. exact (MK_COMB (@lem3218927) (@lem3218926 A s t)). Qed.
Lemma lem3218929 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term118 A s t x) = (term67 A s t x).
Proof. exact (eq_refl (term118 A s t x)). Qed.
Lemma lem3218930 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term83 A t s) = (term83 A t s).
Proof. exact (eq_refl (term83 A t s)). Qed.
Lemma lem3218931 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term123 A s t x) = (term124 A s t x).
Proof. exact (MK_COMB (@lem3218930 A t s) (@lem3218929 A s t x)). Qed.
Lemma lem3218932 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term125 A s t) = (term126 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218931 A s t x)). Qed.
Lemma lem3218933 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218934 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term117 A s t) = (term127 A s t).
Proof. exact (MK_COMB (@lem3218933 A) (@lem3218932 A s t)). Qed.
Lemma lem3218935 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term116 A s t) = (term117 A s t)) = ((term85 A s t) = (term127 A s t)).
Proof. exact (MK_COMB (@lem3218928 A s t) (@lem3218934 A s t)). Qed.
Lemma lem3218936 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term85 A s t) = (term127 A s t).
Proof. exact (EQ_MP (@lem3218935 A s t) (@lem3218920 A s t)). Qed.
Lemma lem3218937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3218938 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term128 A s t).
Proof. exact (MK_COMB (@lem3218937) (@lem3218936 A s t)). Qed.
Lemma lem3218940 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3218941 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (@lem3218940 A P Q). Qed.
Lemma lem3218942 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term131 A t s) = (term132 A t s).
Proof. exact (@lem3218941 A (term55 A s t) (term55 A t s)). Qed.
Lemma lem3218943 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term133 A s t x) = (term46 A s t x).
Proof. exact (eq_refl (term133 A s t x)). Qed.
Lemma lem3218944 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term134 A s t) = (term55 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218943 A s t x)). Qed.
Lemma lem3218945 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218946 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term56 A s t).
Proof. exact (MK_COMB (@lem3218945 A) (@lem3218944 A s t)). Qed.
Lemma lem3218947 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3218948 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term136 A s t) = (term60 A s t).
Proof. exact (MK_COMB (@lem3218947) (@lem3218946 A s t)). Qed.
Lemma lem3218949 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term133 A t s x) = (term46 A t s x).
Proof. exact (eq_refl (term133 A t s x)). Qed.
Lemma lem3218950 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term134 A t s) = (term55 A t s).
Proof. exact (fun_ext (fun x : A => @lem3218949 A t s x)). Qed.
Lemma lem3218951 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218952 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term135 A t s) = (term56 A t s).
Proof. exact (MK_COMB (@lem3218951 A) (@lem3218950 A t s)). Qed.
Lemma lem3218953 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term131 A t s) = (term62 A t s).
Proof. exact (MK_COMB (@lem3218948 A s t) (@lem3218952 A t s)). Qed.
Lemma lem3218954 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218955 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term137 A t s) = (term138 A t s).
Proof. exact (MK_COMB (@lem3218954) (@lem3218953 A t s)). Qed.
Lemma lem3218956 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term133 A s t x) = (term46 A s t x).
Proof. exact (eq_refl (term133 A s t x)). Qed.
Lemma lem3218957 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3218958 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term139 A s t x) = (term140 A s t x).
Proof. exact (MK_COMB (@lem3218957) (@lem3218956 A s t x)). Qed.
Lemma lem3218959 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term133 A t s x) = (term46 A t s x).
Proof. exact (eq_refl (term133 A t s x)). Qed.
Lemma lem3218960 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term141 A t s x) = (term142 A t s x).
Proof. exact (MK_COMB (@lem3218958 A s t x) (@lem3218959 A t s x)). Qed.
Lemma lem3218961 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term143 A t s) = (term144 A t s).
Proof. exact (fun_ext (fun x : A => @lem3218960 A t s x)). Qed.
Lemma lem3218962 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218963 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term132 A t s) = (term145 A t s).
Proof. exact (MK_COMB (@lem3218962 A) (@lem3218961 A t s)). Qed.
Lemma lem3218964 {A : Type'} (t : A -> Prop) (s : A -> Prop) : ((term131 A t s) = (term132 A t s)) = ((term62 A t s) = (term145 A t s)).
Proof. exact (MK_COMB (@lem3218955 A t s) (@lem3218963 A t s)). Qed.
Lemma lem3218965 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term62 A t s) = (term145 A t s).
Proof. exact (EQ_MP (@lem3218964 A t s) (@lem3218942 A t s)). Qed.
Lemma lem3218966 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218967 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term79 A t s) = (term146 A t s).
Proof. exact (MK_COMB (@lem3218966) (@lem3218965 A t s)). Qed.
Lemma lem3218968 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term111 A s t).
Proof. exact (eq_refl (term111 A s t)). Qed.
Lemma lem3218969 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term147 A s t).
Proof. exact (MK_COMB (@lem3218967 A t s) (@lem3218968 A s t)). Qed.
Lemma lem3218971 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3218972 {A : Type'} (P : A -> Prop) (Q : Prop) : (term148 A P Q) = (term149 A P Q).
Proof. exact (@lem3218971 A P Q). Qed.
Lemma lem3218973 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term151 A s t).
Proof. exact (@lem3218972 A (term144 A t s) (term111 A s t)). Qed.
Lemma lem3218974 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term152 A t s x) = (term142 A t s x).
Proof. exact (eq_refl (term152 A t s x)). Qed.
Lemma lem3218975 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term153 A t s) = (term144 A t s).
Proof. exact (fun_ext (fun x : A => @lem3218974 A t s x)). Qed.
Lemma lem3218976 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218977 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term154 A t s) = (term145 A t s).
Proof. exact (MK_COMB (@lem3218976 A) (@lem3218975 A t s)). Qed.
Lemma lem3218978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218979 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term155 A t s) = (term146 A t s).
Proof. exact (MK_COMB (@lem3218978) (@lem3218977 A t s)). Qed.
Lemma lem3218980 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term111 A s t).
Proof. exact (eq_refl (term111 A s t)). Qed.
Lemma lem3218981 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term150 A s t) = (term147 A s t).
Proof. exact (MK_COMB (@lem3218979 A t s) (@lem3218980 A s t)). Qed.
Lemma lem3218982 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3218983 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term156 A s t) = (term157 A s t).
Proof. exact (MK_COMB (@lem3218982) (@lem3218981 A s t)). Qed.
Lemma lem3218984 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term152 A t s x) = (term142 A t s x).
Proof. exact (eq_refl (term152 A t s x)). Qed.
Lemma lem3218985 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3218986 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term158 A t s x) = (term159 A t s x).
Proof. exact (MK_COMB (@lem3218985) (@lem3218984 A t s x)). Qed.
Lemma lem3218987 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term111 A s t).
Proof. exact (eq_refl (term111 A s t)). Qed.
Lemma lem3218988 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term160 A x s t) = (term161 A x s t).
Proof. exact (MK_COMB (@lem3218986 A t s x) (@lem3218987 A s t)). Qed.
Lemma lem3218989 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term162 A s t) = (term163 A s t).
Proof. exact (fun_ext (fun x : A => @lem3218988 A x s t)). Qed.
Lemma lem3218990 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3218991 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term151 A s t) = (term164 A s t).
Proof. exact (MK_COMB (@lem3218990 A) (@lem3218989 A s t)). Qed.
Lemma lem3218992 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term150 A s t) = (term151 A s t)) = ((term147 A s t) = (term164 A s t)).
Proof. exact (MK_COMB (@lem3218983 A s t) (@lem3218991 A s t)). Qed.
Lemma lem3218993 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term147 A s t) = (term164 A s t).
Proof. exact (EQ_MP (@lem3218992 A s t) (@lem3218973 A s t)). Qed.
Lemma lem3218994 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term112 A s t) = (term164 A s t).
Proof. exact (TRANS (@lem3218969 A s t) (@lem3218993 A s t)). Qed.
Lemma lem3218995 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term113 A s t) = (term165 A s t).
Proof. exact (MK_COMB (@lem3218938 A s t) (@lem3218994 A s t)). Qed.
Lemma lem3218997 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3218998 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term129 A P Q) = (term130 A P Q).
Proof. exact (@lem3218997 A P Q). Qed.
Lemma lem3218999 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term166 A s t) = (term167 A s t).
Proof. exact (@lem3218998 A (term126 A s t) (term163 A s t)). Qed.
Lemma lem3219000 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term168 A s t x) = (term124 A s t x).
Proof. exact (eq_refl (term168 A s t x)). Qed.
Lemma lem3219001 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term169 A s t) = (term126 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219000 A s t x)). Qed.
Lemma lem3219002 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3219003 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term170 A s t) = (term127 A s t).
Proof. exact (MK_COMB (@lem3219002 A) (@lem3219001 A s t)). Qed.
Lemma lem3219004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3219005 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term171 A s t) = (term128 A s t).
Proof. exact (MK_COMB (@lem3219004) (@lem3219003 A s t)). Qed.
Lemma lem3219006 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term172 A s t x) = (term161 A x s t).
Proof. exact (eq_refl (term172 A s t x)). Qed.
Lemma lem3219007 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term173 A s t) = (term163 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219006 A x s t)). Qed.
Lemma lem3219008 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3219009 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term174 A s t) = (term164 A s t).
Proof. exact (MK_COMB (@lem3219008 A) (@lem3219007 A s t)). Qed.
Lemma lem3219010 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term166 A s t) = (term165 A s t).
Proof. exact (MK_COMB (@lem3219005 A s t) (@lem3219009 A s t)). Qed.
Lemma lem3219011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3219012 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term175 A s t) = (term176 A s t).
Proof. exact (MK_COMB (@lem3219011) (@lem3219010 A s t)). Qed.
Lemma lem3219013 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term168 A s t x) = (term124 A s t x).
Proof. exact (eq_refl (term168 A s t x)). Qed.
Lemma lem3219014 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3219015 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term177 A s t x) = (term178 A s t x).
Proof. exact (MK_COMB (@lem3219014) (@lem3219013 A s t x)). Qed.
Lemma lem3219016 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term172 A s t x) = (term161 A x s t).
Proof. exact (eq_refl (term172 A s t x)). Qed.
Lemma lem3219017 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term179 A s t x) = (term180 A x s t).
Proof. exact (MK_COMB (@lem3219015 A s t x) (@lem3219016 A x s t)). Qed.
Lemma lem3219018 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term181 A s t) = (term182 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219017 A x s t)). Qed.
Lemma lem3219019 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3219020 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term167 A s t) = (term183 A s t).
Proof. exact (MK_COMB (@lem3219019 A) (@lem3219018 A s t)). Qed.
Lemma lem3219021 {A : Type'} (s : A -> Prop) (t : A -> Prop) : ((term166 A s t) = (term167 A s t)) = ((term165 A s t) = (term183 A s t)).
Proof. exact (MK_COMB (@lem3219012 A s t) (@lem3219020 A s t)). Qed.
Lemma lem3219022 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term165 A s t) = (term183 A s t).
Proof. exact (EQ_MP (@lem3219021 A s t) (@lem3218999 A s t)). Qed.
Lemma lem3219023 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term113 A s t) = (term183 A s t).
Proof. exact (TRANS (@lem3218995 A s t) (@lem3219022 A s t)). Qed.
Lemma lem3219024 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term89 A s t) = (term183 A s t).
Proof. exact (TRANS (@lem3218916 A s t) (@lem3219023 A s t)). Qed.
Lemma lem3219025 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term44 A s t) = (term183 A s t).
Proof. exact (TRANS (@lem3218657 A s t) (@lem3219024 A s t)). Qed.
Lemma lem3219026 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : term183 A s t.
Proof. exact (EQ_MP (@lem3219025 A s t) (@lem3218545 A s t h1)). Qed.
Lemma lem3219027 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term180 A x s t) : term180 A x s t.
Proof. exact (h1). Qed.
Lemma lem3219038 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3219039 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219038 A s t x)). Qed.
Lemma lem3219040 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219041 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3219040 A) (@lem3219039 A s t)). Qed.
Lemma lem3219052 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term96 A s t x) = (term96 A s t x).
Proof. exact (eq_refl (term96 A s t x)). Qed.
Lemma lem3219053 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term94 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219052 A s t x)). Qed.
Lemma lem3219054 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219055 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3219054 A) (@lem3219053 A s t)). Qed.
Lemma lem3219056 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3219057 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term108 A s t) = (term108 A s t).
Proof. exact (MK_COMB (@lem3219056) (@lem3219055 A s t)). Qed.
Lemma lem3219058 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term111 A s t) = (term111 A s t).
Proof. exact (MK_COMB (@lem3219057 A s t) (@lem3219041 A s t)). Qed.
Lemma lem3219085 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term159 A t s x) = (term159 A t s x).
Proof. exact (eq_refl (term159 A t s x)). Qed.
Lemma lem3219086 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term161 A x s t) = (term161 A x s t).
Proof. exact (MK_COMB (@lem3219085 A t s x) (@lem3219058 A s t)). Qed.
Lemma lem3219111 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term67 A s t x) = (term67 A s t x).
Proof. exact (eq_refl (term67 A s t x)). Qed.
Lemma lem3219122 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term47 A t s x) = (term47 A t s x).
Proof. exact (eq_refl (term47 A t s x)). Qed.
Lemma lem3219123 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term57 A t s) = (term57 A t s).
Proof. exact (fun_ext (fun x : A => @lem3219122 A t s x)). Qed.
Lemma lem3219124 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219125 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term58 A t s) = (term58 A t s).
Proof. exact (MK_COMB (@lem3219124 A) (@lem3219123 A t s)). Qed.
Lemma lem3219136 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3219137 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219136 A s t x)). Qed.
Lemma lem3219138 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219139 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3219138 A) (@lem3219137 A s t)). Qed.
Lemma lem3219140 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3219141 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term64 A s t) = (term64 A s t).
Proof. exact (MK_COMB (@lem3219140) (@lem3219139 A s t)). Qed.
Lemma lem3219142 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term65 A t s) = (term65 A t s).
Proof. exact (MK_COMB (@lem3219141 A s t) (@lem3219125 A t s)). Qed.
Lemma lem3219143 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3219144 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term83 A t s) = (term83 A t s).
Proof. exact (MK_COMB (@lem3219143) (@lem3219142 A t s)). Qed.
Lemma lem3219145 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term124 A s t x) = (term124 A s t x).
Proof. exact (MK_COMB (@lem3219144 A t s) (@lem3219111 A s t x)). Qed.
Lemma lem3219146 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3219147 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term178 A s t x) = (term178 A s t x).
Proof. exact (MK_COMB (@lem3219146) (@lem3219145 A s t x)). Qed.
Lemma lem3219148 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term180 A x s t) = (term180 A x s t).
Proof. exact (MK_COMB (@lem3219147 A s t x) (@lem3219086 A x s t)). Qed.
Lemma lem3219149 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term180 A x s t) : term180 A x s t.
Proof. exact (EQ_MP (@lem3219148 A x s t) (@lem3219027 A x s t h1)). Qed.
Lemma lem3219150 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term124 A s t x.
Proof. exact (h1). Qed.
Lemma lem3219151 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term161 A x s t.
Proof. exact (h1). Qed.
Lemma lem3219152 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term67 A s t x.
Proof. exact (proj2 (@lem3219150 A s t x h1)). Qed.
Lemma lem3219153 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term65 A t s.
Proof. exact (proj1 (@lem3219150 A s t x h1)). Qed.
Lemma lem3219154 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term184 A s t x.
Proof. exact (proj2 (@lem3219152 A s t x h1)). Qed.
Lemma lem3219155 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term185 A s t x.
Proof. exact (proj1 (@lem3219152 A s t x h1)). Qed.
Lemma lem3219156 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term58 A t s.
Proof. exact (proj2 (@lem3219153 A s t x h1)). Qed.
Lemma lem3219157 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term58 A s t.
Proof. exact (proj1 (@lem3219153 A s t x h1)). Qed.
Lemma lem3219164 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term111 A s t.
Proof. exact (proj2 (@lem3219151 A x s t h1)). Qed.
Lemma lem3219165 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term142 A t s x.
Proof. exact (proj1 (@lem3219151 A x s t h1)). Qed.
Lemma lem3219166 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term58 A s t.
Proof. exact (proj2 (@lem3219164 A x s t h1)). Qed.
Lemma lem3219167 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term106 A s t.
Proof. exact (proj1 (@lem3219164 A x s t h1)). Qed.
Lemma lem3219168 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term46 A s t x) : term46 A s t x.
Proof. exact (h1). Qed.
Lemma lem3219169 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term46 A t s x) : term46 A t s x.
Proof. exact (h1). Qed.
Lemma lem3219203 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) : term186 A s x.
Proof. exact (h1). Qed.
Lemma lem3219207 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3219228 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term47 A t s x) = (term47 A t s x).
Proof. exact (eq_refl (term47 A t s x)). Qed.
Lemma lem3219229 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term57 A t s) = (term57 A t s).
Proof. exact (fun_ext (fun x : A => @lem3219228 A t s x)). Qed.
Lemma lem3219230 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219232 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term58 A t s) = (term58 A t s).
Proof. exact (MK_COMB (@lem3219230 A) (@lem3219229 A t s)). Qed.
Lemma lem3219233 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term58 A t s.
Proof. exact (EQ_MP (@lem3219232 A t s) (@lem3219156 A s t x h1)). Qed.
Lemma lem3219237 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) : term186 A s x.
Proof. exact (h1). Qed.
Lemma lem3219241 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3219249 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3219250 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219249 A s t x)). Qed.
Lemma lem3219251 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219253 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3219251 A) (@lem3219250 A s t)). Qed.
Lemma lem3219254 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term58 A s t.
Proof. exact (EQ_MP (@lem3219253 A s t) (@lem3219157 A s t x h1)). Qed.
Lemma lem3219271 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) : term186 A t x.
Proof. exact (h1). Qed.
Lemma lem3219275 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3219305 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) : term186 A t x.
Proof. exact (h1). Qed.
Lemma lem3219309 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3219330 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term47 A s t x) = (term47 A s t x).
Proof. exact (eq_refl (term47 A s t x)). Qed.
Lemma lem3219331 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term57 A s t) = (term57 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219330 A s t x)). Qed.
Lemma lem3219332 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219334 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term58 A s t) = (term58 A s t).
Proof. exact (MK_COMB (@lem3219332 A) (@lem3219331 A s t)). Qed.
Lemma lem3219335 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term58 A s t.
Proof. exact (EQ_MP (@lem3219334 A s t) (@lem3219166 A x s t h1)). Qed.
Lemma lem3219351 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term96 A s t x) = (term96 A s t x).
Proof. exact (eq_refl (term96 A s t x)). Qed.
Lemma lem3219352 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term94 A s t) = (term94 A s t).
Proof. exact (fun_ext (fun x : A => @lem3219351 A s t x)). Qed.
Lemma lem3219353 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3219355 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term106 A s t) = (term106 A s t).
Proof. exact (MK_COMB (@lem3219353 A) (@lem3219352 A s t)). Qed.
Lemma lem3219356 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term106 A s t.
Proof. exact (EQ_MP (@lem3219355 A s t) (@lem3219167 A x s t h1)). Qed.
Lemma lem3219387 {A : Type'} (_33109 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term99 A t s _33109.
Proof. exact (@lem3219233 A s t x h1 _33109). Qed.
Lemma lem3219388 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33109 : A) : (term99 A t s _33109) = (term47 A t s _33109).
Proof. exact (eq_refl (term99 A t s _33109)). Qed.
Lemma lem3219390 {A : Type'} (_33110 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term99 A s t _33110.
Proof. exact (@lem3219254 A s t x h1 _33110). Qed.
Lemma lem3219391 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33110 : A) : (term99 A s t _33110) = (term47 A s t _33110).
Proof. exact (eq_refl (term99 A s t _33110)). Qed.
Lemma lem3219405 {A : Type'} (_33115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term99 A s t _33115.
Proof. exact (@lem3219335 A x s t h1 _33115). Qed.
Lemma lem3219406 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33115 : A) : (term99 A s t _33115) = (term47 A s t _33115).
Proof. exact (eq_refl (term99 A s t _33115)). Qed.
Lemma lem3219408 {A : Type'} (_33116 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term95 A s t _33116.
Proof. exact (@lem3219356 A x s t h1 _33116). Qed.
Lemma lem3219409 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33116 : A) : (term95 A s t _33116) = (term96 A s t _33116).
Proof. exact (eq_refl (term95 A s t _33116)). Qed.
Lemma lem3219427 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) : term186 A s x.
Proof. exact (h1). Qed.
Lemma lem3219429 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3219441 {A : Type'} (_33109 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term47 A t s _33109.
Proof. exact (EQ_MP (@lem3219388 A t s _33109) (@lem3219387 A _33109 s t x h1)). Qed.
Lemma lem3219443 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) : term186 A s x.
Proof. exact (h1). Qed.
Lemma lem3219445 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3219451 {A : Type'} (_33110 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term47 A s t _33110.
Proof. exact (EQ_MP (@lem3219391 A s t _33110) (@lem3219390 A _33110 s t x h1)). Qed.
Lemma lem3219459 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) : term186 A t x.
Proof. exact (h1). Qed.
Lemma lem3219461 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3219475 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) : term186 A t x.
Proof. exact (h1). Qed.
Lemma lem3219477 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3219489 {A : Type'} (_33115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term47 A s t _33115.
Proof. exact (EQ_MP (@lem3219406 A s t _33115) (@lem3219405 A _33115 x s t h1)). Qed.
Lemma lem3219493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term46 A s t x) : term186 A t x.
Proof. exact (proj2 (@lem3219168 A s t x h1)). Qed.
Lemma lem3219499 {A : Type'} (_33116 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term96 A s t _33116.
Proof. exact (EQ_MP (@lem3219409 A s t _33116) (@lem3219408 A _33116 x s t h1)). Qed.
Lemma lem3219509 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term46 A t s x) : term186 A s x.
Proof. exact (proj2 (@lem3219169 A t s x h1)). Qed.
Lemma lem3219511 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3219512 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term187 A s x.
Proof. exact (fun h0 : term186 A s x => @lem3219511 A s x h1). Qed.
Lemma lem3219514 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219515 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (s x).
Proof. exact (@lem3219514 (s x)). Qed.
Lemma lem3219516 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3219515 A s x) (@lem3219512 A s x h1)). Qed.
Lemma lem3219519 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3219521 {A : Type'} (s : A -> Prop) (x : A) : (term186 A s x) = (term189 A s x).
Proof. exact (@lem3219519 (s x)). Qed.
Lemma lem3219524 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) : term189 A s x.
Proof. exact (EQ_MP (@lem3219521 A s x) (@lem3219427 A s x h1)). Qed.
Lemma lem3219527 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (@lem3219524 A s x h1 (@lem3219516 A s x h2)). Qed.
Lemma lem3219528 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : term190.
Proof. exact (fun h0 : ~ False => @lem3219527 A s x h1 h2). Qed.
Lemma lem3219530 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219531 : term190 = False.
Proof. exact (@lem3219530 False). Qed.
Lemma lem3219532 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3219531) (@lem3219528 A s x h1 h2)). Qed.
Lemma lem3219534 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3219535 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term187 A t x.
Proof. exact (fun h0 : term186 A t x => @lem3219534 A t x h1). Qed.
Lemma lem3219537 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219538 {A : Type'} (t : A -> Prop) (x : A) : (term187 A t x) = (t x).
Proof. exact (@lem3219537 (t x)). Qed.
Lemma lem3219539 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3219538 A t x) (@lem3219535 A t x h1)). Qed.
Lemma lem3219545 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3219546 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : (term47 A t s _33109) = (term96 A s t _33109).
Proof. exact (@lem3219545 (s _33109) (term186 A t _33109)). Qed.
Lemma lem3219552 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3219553 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : (term191 A t s _33109) = (term192 A s t _33109).
Proof. exact (MK_COMB (@lem3219552) (@lem3219546 A s t _33109)). Qed.
Lemma lem3219559 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : (term96 A s t _33109) = (term96 A s t _33109).
Proof. exact (eq_refl (term96 A s t _33109)). Qed.
Lemma lem3219560 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : ((term47 A t s _33109) = (term96 A s t _33109)) = ((term96 A s t _33109) = (term96 A s t _33109)).
Proof. exact (MK_COMB (@lem3219553 A s t _33109) (@lem3219559 A s t _33109)). Qed.
Lemma lem3219562 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3219563 (x : Prop) : (x = x) = True.
Proof. exact (@lem3219562 Prop x). Qed.
Lemma lem3219564 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : ((term96 A s t _33109) = (term96 A s t _33109)) = True.
Proof. exact (@lem3219563 (term96 A s t _33109)). Qed.
Lemma lem3219565 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : ((term47 A t s _33109) = (term96 A s t _33109)) = True.
Proof. exact (TRANS (@lem3219560 A s t _33109) (@lem3219564 A s t _33109)). Qed.
Lemma lem3219566 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : True = ((term47 A t s _33109) = (term96 A s t _33109)).
Proof. exact (SYM (@lem3219565 A s t _33109)). Qed.
Lemma lem3219567 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33109 : A) : (term47 A t s _33109) = (term96 A s t _33109).
Proof. exact (EQ_MP (@lem3219566 A s t _33109) (@lem0)). Qed.
Lemma lem3219568 {A : Type'} (_33109 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term96 A s t _33109.
Proof. exact (EQ_MP (@lem3219567 A s t _33109) (@lem3219441 A _33109 s t x h1)). Qed.
Lemma lem3219570 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3219571 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33109 : A) : (term96 A s t _33109) = (term194 A t s _33109).
Proof. exact (@lem3219570 (term186 A t _33109) (s _33109)). Qed.
Lemma lem3219573 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3219574 {A : Type'} (t : A -> Prop) (_33109 : A) : (term195 A t _33109) = (t _33109).
Proof. exact (@lem3219573 (t _33109)). Qed.
Lemma lem3219575 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3219576 {A : Type'} (t : A -> Prop) (_33109 : A) : (term196 A t _33109) = (term17 A t _33109).
Proof. exact (MK_COMB (@lem3219575) (@lem3219574 A t _33109)). Qed.
Lemma lem3219577 {A : Type'} (s : A -> Prop) (_33109 : A) : (s _33109) = (s _33109).
Proof. exact (eq_refl (s _33109)). Qed.
Lemma lem3219578 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33109 : A) : (term194 A t s _33109) = (term19 A t s _33109).
Proof. exact (MK_COMB (@lem3219576 A t _33109) (@lem3219577 A s _33109)). Qed.
Lemma lem3219579 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33109 : A) : (term96 A s t _33109) = (term19 A t s _33109).
Proof. exact (TRANS (@lem3219571 A t s _33109) (@lem3219578 A t s _33109)). Qed.
Lemma lem3219582 {A : Type'} (_33109 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term19 A t s _33109.
Proof. exact (EQ_MP (@lem3219579 A t s _33109) (@lem3219568 A _33109 s t x h1)). Qed.
Lemma lem3219583 {A : Type'} (_33109 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term19 A t s _33109.
Proof. exact (@lem3219582 A _33109 s t x h1). Qed.
Lemma lem3219584 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term19 A t s x.
Proof. exact (@lem3219583 A x s t x h1). Qed.
Lemma lem3219587 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term124 A s t x) : s x.
Proof. exact (@lem3219584 A s t x h2 (@lem3219539 A t x h1)). Qed.
Lemma lem3219588 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term124 A s t x) : term187 A s x.
Proof. exact (fun h0 : term186 A s x => @lem3219587 A s t x h1 h2). Qed.
Lemma lem3219590 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219591 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (s x).
Proof. exact (@lem3219590 (s x)). Qed.
Lemma lem3219592 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) (h2 : term124 A s t x) : s x.
Proof. exact (EQ_MP (@lem3219591 A s x) (@lem3219588 A s t x h1 h2)). Qed.
Lemma lem3219595 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3219597 {A : Type'} (s : A -> Prop) (x : A) : (term186 A s x) = (term189 A s x).
Proof. exact (@lem3219595 (s x)). Qed.
Lemma lem3219600 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) : term189 A s x.
Proof. exact (EQ_MP (@lem3219597 A s x) (@lem3219443 A s x h1)). Qed.
Lemma lem3219603 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (@lem3219600 A s x h1 (@lem3219592 A s t x h2 h3)). Qed.
Lemma lem3219604 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : term190.
Proof. exact (fun h0 : ~ False => @lem3219603 A s t x h1 h2 h3). Qed.
Lemma lem3219606 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219607 : term190 = False.
Proof. exact (@lem3219606 False). Qed.
Lemma lem3219608 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219607) (@lem3219604 A s t x h1 h2 h3)). Qed.
Lemma lem3219610 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3219611 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term187 A s x.
Proof. exact (fun h0 : term186 A s x => @lem3219610 A s x h1). Qed.
Lemma lem3219613 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219614 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (s x).
Proof. exact (@lem3219613 (s x)). Qed.
Lemma lem3219615 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3219614 A s x) (@lem3219611 A s x h1)). Qed.
Lemma lem3219621 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3219622 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : (term47 A s t _33110) = (term96 A t s _33110).
Proof. exact (@lem3219621 (t _33110) (term186 A s _33110)). Qed.
Lemma lem3219628 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3219629 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : (term191 A s t _33110) = (term192 A t s _33110).
Proof. exact (MK_COMB (@lem3219628) (@lem3219622 A t s _33110)). Qed.
Lemma lem3219635 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : (term96 A t s _33110) = (term96 A t s _33110).
Proof. exact (eq_refl (term96 A t s _33110)). Qed.
Lemma lem3219636 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : ((term47 A s t _33110) = (term96 A t s _33110)) = ((term96 A t s _33110) = (term96 A t s _33110)).
Proof. exact (MK_COMB (@lem3219629 A t s _33110) (@lem3219635 A t s _33110)). Qed.
Lemma lem3219638 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3219639 (x : Prop) : (x = x) = True.
Proof. exact (@lem3219638 Prop x). Qed.
Lemma lem3219640 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : ((term96 A t s _33110) = (term96 A t s _33110)) = True.
Proof. exact (@lem3219639 (term96 A t s _33110)). Qed.
Lemma lem3219641 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : ((term47 A s t _33110) = (term96 A t s _33110)) = True.
Proof. exact (TRANS (@lem3219636 A t s _33110) (@lem3219640 A t s _33110)). Qed.
Lemma lem3219642 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : True = ((term47 A s t _33110) = (term96 A t s _33110)).
Proof. exact (SYM (@lem3219641 A t s _33110)). Qed.
Lemma lem3219643 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33110 : A) : (term47 A s t _33110) = (term96 A t s _33110).
Proof. exact (EQ_MP (@lem3219642 A t s _33110) (@lem0)). Qed.
Lemma lem3219644 {A : Type'} (_33110 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term96 A t s _33110.
Proof. exact (EQ_MP (@lem3219643 A t s _33110) (@lem3219451 A _33110 s t x h1)). Qed.
Lemma lem3219646 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3219647 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33110 : A) : (term96 A t s _33110) = (term194 A s t _33110).
Proof. exact (@lem3219646 (term186 A s _33110) (t _33110)). Qed.
Lemma lem3219649 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3219650 {A : Type'} (s : A -> Prop) (_33110 : A) : (term195 A s _33110) = (s _33110).
Proof. exact (@lem3219649 (s _33110)). Qed.
Lemma lem3219651 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3219652 {A : Type'} (s : A -> Prop) (_33110 : A) : (term196 A s _33110) = (term17 A s _33110).
Proof. exact (MK_COMB (@lem3219651) (@lem3219650 A s _33110)). Qed.
Lemma lem3219653 {A : Type'} (t : A -> Prop) (_33110 : A) : (t _33110) = (t _33110).
Proof. exact (eq_refl (t _33110)). Qed.
Lemma lem3219654 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33110 : A) : (term194 A s t _33110) = (term19 A s t _33110).
Proof. exact (MK_COMB (@lem3219652 A s _33110) (@lem3219653 A t _33110)). Qed.
Lemma lem3219655 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33110 : A) : (term96 A t s _33110) = (term19 A s t _33110).
Proof. exact (TRANS (@lem3219647 A s t _33110) (@lem3219654 A s t _33110)). Qed.
Lemma lem3219658 {A : Type'} (_33110 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term19 A s t _33110.
Proof. exact (EQ_MP (@lem3219655 A s t _33110) (@lem3219644 A _33110 s t x h1)). Qed.
Lemma lem3219659 {A : Type'} (_33110 : A) (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term19 A s t _33110.
Proof. exact (@lem3219658 A _33110 s t x h1). Qed.
Lemma lem3219660 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : term19 A s t x.
Proof. exact (@lem3219659 A x s t x h1). Qed.
Lemma lem3219663 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term124 A s t x) : t x.
Proof. exact (@lem3219660 A s t x h2 (@lem3219615 A s x h1)). Qed.
Lemma lem3219664 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term124 A s t x) : term187 A t x.
Proof. exact (fun h0 : term186 A t x => @lem3219663 A s t x h1 h2). Qed.
Lemma lem3219666 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219667 {A : Type'} (t : A -> Prop) (x : A) : (term187 A t x) = (t x).
Proof. exact (@lem3219666 (t x)). Qed.
Lemma lem3219668 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : s x) (h2 : term124 A s t x) : t x.
Proof. exact (EQ_MP (@lem3219667 A t x) (@lem3219664 A s t x h1 h2)). Qed.
Lemma lem3219671 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3219673 {A : Type'} (t : A -> Prop) (x : A) : (term186 A t x) = (term189 A t x).
Proof. exact (@lem3219671 (t x)). Qed.
Lemma lem3219676 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) : term189 A t x.
Proof. exact (EQ_MP (@lem3219673 A t x) (@lem3219459 A t x h1)). Qed.
Lemma lem3219679 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (@lem3219676 A t x h1 (@lem3219668 A s t x h2 h3)). Qed.
Lemma lem3219680 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : term190.
Proof. exact (fun h0 : ~ False => @lem3219679 A s t x h1 h2 h3). Qed.
Lemma lem3219682 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219683 : term190 = False.
Proof. exact (@lem3219682 False). Qed.
Lemma lem3219684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219683) (@lem3219680 A s t x h1 h2 h3)). Qed.
Lemma lem3219686 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3219687 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term187 A t x.
Proof. exact (fun h0 : term186 A t x => @lem3219686 A t x h1). Qed.
Lemma lem3219689 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219690 {A : Type'} (t : A -> Prop) (x : A) : (term187 A t x) = (t x).
Proof. exact (@lem3219689 (t x)). Qed.
Lemma lem3219691 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3219690 A t x) (@lem3219687 A t x h1)). Qed.
Lemma lem3219694 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3219696 {A : Type'} (t : A -> Prop) (x : A) : (term186 A t x) = (term189 A t x).
Proof. exact (@lem3219694 (t x)). Qed.
Lemma lem3219699 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) : term189 A t x.
Proof. exact (EQ_MP (@lem3219696 A t x) (@lem3219475 A t x h1)). Qed.
Lemma lem3219702 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (@lem3219699 A t x h1 (@lem3219691 A t x h2)). Qed.
Lemma lem3219703 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : term190.
Proof. exact (fun h0 : ~ False => @lem3219702 A t x h1 h2). Qed.
Lemma lem3219705 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219706 : term190 = False.
Proof. exact (@lem3219705 False). Qed.
Lemma lem3219707 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3219706) (@lem3219703 A t x h1 h2)). Qed.
Lemma lem3219709 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term46 A s t x) : s x.
Proof. exact (proj1 (@lem3219168 A s t x h1)). Qed.
Lemma lem3219710 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term46 A s t x) : term187 A s x.
Proof. exact (fun h0 : term186 A s x => @lem3219709 A s t x h1). Qed.
Lemma lem3219712 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219713 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (s x).
Proof. exact (@lem3219712 (s x)). Qed.
Lemma lem3219714 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term46 A s t x) : s x.
Proof. exact (EQ_MP (@lem3219713 A s x) (@lem3219710 A s t x h1)). Qed.
Lemma lem3219720 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3219721 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : (term47 A s t _33115) = (term96 A t s _33115).
Proof. exact (@lem3219720 (t _33115) (term186 A s _33115)). Qed.
Lemma lem3219727 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3219728 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : (term191 A s t _33115) = (term192 A t s _33115).
Proof. exact (MK_COMB (@lem3219727) (@lem3219721 A t s _33115)). Qed.
Lemma lem3219734 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : (term96 A t s _33115) = (term96 A t s _33115).
Proof. exact (eq_refl (term96 A t s _33115)). Qed.
Lemma lem3219735 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : ((term47 A s t _33115) = (term96 A t s _33115)) = ((term96 A t s _33115) = (term96 A t s _33115)).
Proof. exact (MK_COMB (@lem3219728 A t s _33115) (@lem3219734 A t s _33115)). Qed.
Lemma lem3219737 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3219738 (x : Prop) : (x = x) = True.
Proof. exact (@lem3219737 Prop x). Qed.
Lemma lem3219739 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : ((term96 A t s _33115) = (term96 A t s _33115)) = True.
Proof. exact (@lem3219738 (term96 A t s _33115)). Qed.
Lemma lem3219740 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : ((term47 A s t _33115) = (term96 A t s _33115)) = True.
Proof. exact (TRANS (@lem3219735 A t s _33115) (@lem3219739 A t s _33115)). Qed.
Lemma lem3219741 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : True = ((term47 A s t _33115) = (term96 A t s _33115)).
Proof. exact (SYM (@lem3219740 A t s _33115)). Qed.
Lemma lem3219742 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33115 : A) : (term47 A s t _33115) = (term96 A t s _33115).
Proof. exact (EQ_MP (@lem3219741 A t s _33115) (@lem0)). Qed.
Lemma lem3219743 {A : Type'} (_33115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term96 A t s _33115.
Proof. exact (EQ_MP (@lem3219742 A t s _33115) (@lem3219489 A _33115 x s t h1)). Qed.
Lemma lem3219745 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3219746 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33115 : A) : (term96 A t s _33115) = (term194 A s t _33115).
Proof. exact (@lem3219745 (term186 A s _33115) (t _33115)). Qed.
Lemma lem3219748 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3219749 {A : Type'} (s : A -> Prop) (_33115 : A) : (term195 A s _33115) = (s _33115).
Proof. exact (@lem3219748 (s _33115)). Qed.
Lemma lem3219750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3219751 {A : Type'} (s : A -> Prop) (_33115 : A) : (term196 A s _33115) = (term17 A s _33115).
Proof. exact (MK_COMB (@lem3219750) (@lem3219749 A s _33115)). Qed.
Lemma lem3219752 {A : Type'} (t : A -> Prop) (_33115 : A) : (t _33115) = (t _33115).
Proof. exact (eq_refl (t _33115)). Qed.
Lemma lem3219753 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33115 : A) : (term194 A s t _33115) = (term19 A s t _33115).
Proof. exact (MK_COMB (@lem3219751 A s _33115) (@lem3219752 A t _33115)). Qed.
Lemma lem3219754 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_33115 : A) : (term96 A t s _33115) = (term19 A s t _33115).
Proof. exact (TRANS (@lem3219746 A s t _33115) (@lem3219753 A s t _33115)). Qed.
Lemma lem3219757 {A : Type'} (_33115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term19 A s t _33115.
Proof. exact (EQ_MP (@lem3219754 A s t _33115) (@lem3219743 A _33115 x s t h1)). Qed.
Lemma lem3219758 {A : Type'} (_33115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term19 A s t _33115.
Proof. exact (@lem3219757 A _33115 x s t h1). Qed.
Lemma lem3219759 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term19 A s t x.
Proof. exact (@lem3219758 A x x s t h1). Qed.
Lemma lem3219762 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A s t x) (h2 : term161 A x s t) : t x.
Proof. exact (@lem3219759 A x s t h2 (@lem3219714 A s t x h1)). Qed.
Lemma lem3219763 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A s t x) (h2 : term161 A x s t) : term187 A t x.
Proof. exact (fun h0 : term186 A t x => @lem3219762 A x s t h1 h2). Qed.
Lemma lem3219765 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219766 {A : Type'} (t : A -> Prop) (x : A) : (term187 A t x) = (t x).
Proof. exact (@lem3219765 (t x)). Qed.
Lemma lem3219767 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A s t x) (h2 : term161 A x s t) : t x.
Proof. exact (EQ_MP (@lem3219766 A t x) (@lem3219763 A x s t h1 h2)). Qed.
Lemma lem3219770 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3219772 {A : Type'} (t : A -> Prop) (x : A) : (term186 A t x) = (term189 A t x).
Proof. exact (@lem3219770 (t x)). Qed.
Lemma lem3219775 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term46 A s t x) : term189 A t x.
Proof. exact (EQ_MP (@lem3219772 A t x) (@lem3219493 A s t x h1)). Qed.
Lemma lem3219778 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A s t x) (h2 : term161 A x s t) : False.
Proof. exact (@lem3219775 A s t x h1 (@lem3219767 A x s t h1 h2)). Qed.
Lemma lem3219779 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A s t x) (h2 : term161 A x s t) : term190.
Proof. exact (fun h0 : ~ False => @lem3219778 A x s t h1 h2). Qed.
Lemma lem3219781 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219782 : term190 = False.
Proof. exact (@lem3219781 False). Qed.
Lemma lem3219783 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A s t x) (h2 : term161 A x s t) : False.
Proof. exact (EQ_MP (@lem3219782) (@lem3219779 A x s t h1 h2)). Qed.
Lemma lem3219785 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term46 A t s x) : t x.
Proof. exact (proj1 (@lem3219169 A t s x h1)). Qed.
Lemma lem3219786 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term46 A t s x) : term187 A t x.
Proof. exact (fun h0 : term186 A t x => @lem3219785 A t s x h1). Qed.
Lemma lem3219788 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219789 {A : Type'} (t : A -> Prop) (x : A) : (term187 A t x) = (t x).
Proof. exact (@lem3219788 (t x)). Qed.
Lemma lem3219790 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term46 A t s x) : t x.
Proof. exact (EQ_MP (@lem3219789 A t x) (@lem3219786 A t s x h1)). Qed.
Lemma lem3219792 (b : Prop) (a : Prop) : (a \/ b) = (term193 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3219793 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33116 : A) : (term96 A s t _33116) = (term194 A t s _33116).
Proof. exact (@lem3219792 (term186 A t _33116) (s _33116)). Qed.
Lemma lem3219795 (a : Prop) : (term42 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3219796 {A : Type'} (t : A -> Prop) (_33116 : A) : (term195 A t _33116) = (t _33116).
Proof. exact (@lem3219795 (t _33116)). Qed.
Lemma lem3219797 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3219798 {A : Type'} (t : A -> Prop) (_33116 : A) : (term196 A t _33116) = (term17 A t _33116).
Proof. exact (MK_COMB (@lem3219797) (@lem3219796 A t _33116)). Qed.
Lemma lem3219799 {A : Type'} (s : A -> Prop) (_33116 : A) : (s _33116) = (s _33116).
Proof. exact (eq_refl (s _33116)). Qed.
Lemma lem3219800 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33116 : A) : (term194 A t s _33116) = (term19 A t s _33116).
Proof. exact (MK_COMB (@lem3219798 A t _33116) (@lem3219799 A s _33116)). Qed.
Lemma lem3219801 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_33116 : A) : (term96 A s t _33116) = (term19 A t s _33116).
Proof. exact (TRANS (@lem3219793 A t s _33116) (@lem3219800 A t s _33116)). Qed.
Lemma lem3219804 {A : Type'} (_33116 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term19 A t s _33116.
Proof. exact (EQ_MP (@lem3219801 A t s _33116) (@lem3219499 A _33116 x s t h1)). Qed.
Lemma lem3219805 {A : Type'} (_33116 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term19 A t s _33116.
Proof. exact (@lem3219804 A _33116 x s t h1). Qed.
Lemma lem3219806 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : term19 A t s x.
Proof. exact (@lem3219805 A x x s t h1). Qed.
Lemma lem3219809 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A t s x) (h2 : term161 A x s t) : s x.
Proof. exact (@lem3219806 A x s t h2 (@lem3219790 A t s x h1)). Qed.
Lemma lem3219810 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A t s x) (h2 : term161 A x s t) : term187 A s x.
Proof. exact (fun h0 : term186 A s x => @lem3219809 A x s t h1 h2). Qed.
Lemma lem3219812 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219813 {A : Type'} (s : A -> Prop) (x : A) : (term187 A s x) = (s x).
Proof. exact (@lem3219812 (s x)). Qed.
Lemma lem3219814 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A t s x) (h2 : term161 A x s t) : s x.
Proof. exact (EQ_MP (@lem3219813 A s x) (@lem3219810 A x s t h1 h2)). Qed.
Lemma lem3219817 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3219819 {A : Type'} (s : A -> Prop) (x : A) : (term186 A s x) = (term189 A s x).
Proof. exact (@lem3219817 (s x)). Qed.
Lemma lem3219822 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) (h1 : term46 A t s x) : term189 A s x.
Proof. exact (EQ_MP (@lem3219819 A s x) (@lem3219509 A t s x h1)). Qed.
Lemma lem3219825 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A t s x) (h2 : term161 A x s t) : False.
Proof. exact (@lem3219822 A t s x h1 (@lem3219814 A x s t h1 h2)). Qed.
Lemma lem3219826 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A t s x) (h2 : term161 A x s t) : term190.
Proof. exact (fun h0 : ~ False => @lem3219825 A x s t h1 h2). Qed.
Lemma lem3219828 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3219829 : term190 = False.
Proof. exact (@lem3219828 False). Qed.
Lemma lem3219830 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term46 A t s x) (h2 : term161 A x s t) : False.
Proof. exact (EQ_MP (@lem3219829) (@lem3219826 A x s t h1 h2)). Qed.
Lemma lem3219831 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3219707 A t x h1 h2) (fun h3 : False => @lem3219477 A t x h2)). Qed.
Lemma lem3219832 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3219831 A t x h1 h2) (@lem3219477 A t x h2)). Qed.
Lemma lem3219833 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : (term186 A t x) = False.
Proof. exact (prop_ext (fun h3 : term186 A t x => @lem3219832 A t x h1 h2) (fun h3 : False => @lem3219475 A t x h1)). Qed.
Lemma lem3219834 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3219833 A t x h1 h2) (@lem3219475 A t x h1)). Qed.
Lemma lem3219835 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3219684 A s t x h1 h2 h3) (fun h4 : False => @lem3219461 A s x h2)). Qed.
Lemma lem3219836 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219835 A s t x h1 h2 h3) (@lem3219461 A s x h2)). Qed.
Lemma lem3219837 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : (term186 A t x) = False.
Proof. exact (prop_ext (fun h4 : term186 A t x => @lem3219836 A s t x h1 h2 h3) (fun h4 : False => @lem3219459 A t x h1)). Qed.
Lemma lem3219838 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219837 A s t x h1 h2 h3) (@lem3219459 A t x h1)). Qed.
Lemma lem3219839 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3219608 A s t x h1 h2 h3) (fun h4 : False => @lem3219445 A t x h2)). Qed.
Lemma lem3219840 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219839 A s t x h1 h2 h3) (@lem3219445 A t x h2)). Qed.
Lemma lem3219841 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : (term186 A s x) = False.
Proof. exact (prop_ext (fun h4 : term186 A s x => @lem3219840 A s t x h1 h2 h3) (fun h4 : False => @lem3219443 A s x h1)). Qed.
Lemma lem3219842 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219841 A s t x h1 h2 h3) (@lem3219443 A s x h1)). Qed.
Lemma lem3219843 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3219532 A s x h1 h2) (fun h3 : False => @lem3219429 A s x h2)). Qed.
Lemma lem3219844 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3219843 A s x h1 h2) (@lem3219429 A s x h2)). Qed.
Lemma lem3219845 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : (term186 A s x) = False.
Proof. exact (prop_ext (fun h3 : term186 A s x => @lem3219844 A s x h1 h2) (fun h3 : False => @lem3219427 A s x h1)). Qed.
Lemma lem3219846 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3219845 A s x h1 h2) (@lem3219427 A s x h1)). Qed.
Lemma lem3219847 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3219834 A t x h1 h2) (fun h3 : False => @lem3219309 A t x h2)). Qed.
Lemma lem3219848 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3219847 A t x h1 h2) (@lem3219309 A t x h2)). Qed.
Lemma lem3219849 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : (term186 A t x) = False.
Proof. exact (prop_ext (fun h3 : term186 A t x => @lem3219848 A t x h1 h2) (fun h3 : False => @lem3219305 A t x h1)). Qed.
Lemma lem3219850 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3219849 A t x h1 h2) (@lem3219305 A t x h1)). Qed.
Lemma lem3219851 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3219838 A s t x h1 h2 h3) (fun h4 : False => @lem3219275 A s x h2)). Qed.
Lemma lem3219852 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219851 A s t x h1 h2 h3) (@lem3219275 A s x h2)). Qed.
Lemma lem3219853 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : (term186 A t x) = False.
Proof. exact (prop_ext (fun h4 : term186 A t x => @lem3219852 A s t x h1 h2 h3) (fun h4 : False => @lem3219271 A t x h1)). Qed.
Lemma lem3219854 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219853 A s t x h1 h2 h3) (@lem3219271 A t x h1)). Qed.
Lemma lem3219855 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3219842 A s t x h1 h2 h3) (fun h4 : False => @lem3219241 A t x h2)). Qed.
Lemma lem3219856 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219855 A s t x h1 h2 h3) (@lem3219241 A t x h2)). Qed.
Lemma lem3219857 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : (term186 A s x) = False.
Proof. exact (prop_ext (fun h4 : term186 A s x => @lem3219856 A s t x h1 h2 h3) (fun h4 : False => @lem3219237 A s x h1)). Qed.
Lemma lem3219858 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219857 A s t x h1 h2 h3) (@lem3219237 A s x h1)). Qed.
Lemma lem3219859 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3219846 A s x h1 h2) (fun h3 : False => @lem3219207 A s x h2)). Qed.
Lemma lem3219860 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3219859 A s x h1 h2) (@lem3219207 A s x h2)). Qed.
Lemma lem3219861 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : (term186 A s x) = False.
Proof. exact (prop_ext (fun h3 : term186 A s x => @lem3219860 A s x h1 h2) (fun h3 : False => @lem3219203 A s x h1)). Qed.
Lemma lem3219862 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3219861 A s x h1 h2) (@lem3219203 A s x h1)). Qed.
Lemma lem3219863 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3219850 A t x h1 h2) (fun h3 : False => @lem3219309 A t x h2)). Qed.
Lemma lem3219864 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3219863 A t x h1 h2) (@lem3219309 A t x h2)). Qed.
Lemma lem3219865 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : (term186 A t x) = False.
Proof. exact (prop_ext (fun h3 : term186 A t x => @lem3219864 A t x h1 h2) (fun h3 : False => @lem3219305 A t x h1)). Qed.
Lemma lem3219866 {A : Type'} (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3219865 A t x h1 h2) (@lem3219305 A t x h1)). Qed.
Lemma lem3219867 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : (s x) = False.
Proof. exact (prop_ext (fun h4 : s x => @lem3219854 A s t x h1 h2 h3) (fun h4 : False => @lem3219275 A s x h2)). Qed.
Lemma lem3219868 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219867 A s t x h1 h2 h3) (@lem3219275 A s x h2)). Qed.
Lemma lem3219869 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : (term186 A t x) = False.
Proof. exact (prop_ext (fun h4 : term186 A t x => @lem3219868 A s t x h1 h2 h3) (fun h4 : False => @lem3219271 A t x h1)). Qed.
Lemma lem3219870 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : s x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219869 A s t x h1 h2 h3) (@lem3219271 A t x h1)). Qed.
Lemma lem3219871 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3219858 A s t x h1 h2 h3) (fun h4 : False => @lem3219241 A t x h2)). Qed.
Lemma lem3219872 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219871 A s t x h1 h2 h3) (@lem3219241 A t x h2)). Qed.
Lemma lem3219873 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : (term186 A s x) = False.
Proof. exact (prop_ext (fun h4 : term186 A s x => @lem3219872 A s t x h1 h2 h3) (fun h4 : False => @lem3219237 A s x h1)). Qed.
Lemma lem3219874 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : t x) (h3 : term124 A s t x) : False.
Proof. exact (EQ_MP (@lem3219873 A s t x h1 h2 h3) (@lem3219237 A s x h1)). Qed.
Lemma lem3219875 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3219862 A s x h1 h2) (fun h3 : False => @lem3219207 A s x h2)). Qed.
Lemma lem3219876 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3219875 A s x h1 h2) (@lem3219207 A s x h2)). Qed.
Lemma lem3219877 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : (term186 A s x) = False.
Proof. exact (prop_ext (fun h3 : term186 A s x => @lem3219876 A s x h1 h2) (fun h3 : False => @lem3219203 A s x h1)). Qed.
Lemma lem3219878 {A : Type'} (s : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : s x) : False.
Proof. exact (EQ_MP (@lem3219877 A s x h1 h2) (@lem3219203 A s x h1)). Qed.
Lemma lem3219879 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term161 A x s t) : False.
Proof. exact (or_elim (@lem3219165 A x s t h1) (fun h0 : term46 A s t x => @lem3219783 A x s t h0 h1) (fun h0 : term46 A t s x => @lem3219830 A x s t h0 h1)). Qed.
Lemma lem3219880 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A t x) (h2 : term124 A s t x) : False.
Proof. exact (or_elim (@lem3219155 A s t x h2) (fun h0 : s x => @lem3219870 A s t x h1 h0 h2) (fun h0 : t x => @lem3219866 A t x h1 h0)). Qed.
Lemma lem3219881 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term186 A s x) (h2 : term124 A s t x) : False.
Proof. exact (or_elim (@lem3219155 A s t x h2) (fun h0 : s x => @lem3219878 A s x h1 h0) (fun h0 : t x => @lem3219874 A s t x h1 h0 h2)). Qed.
Lemma lem3219882 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term124 A s t x) : False.
Proof. exact (or_elim (@lem3219154 A s t x h1) (fun h0 : term186 A s x => @lem3219881 A s t x h0 h1) (fun h0 : term186 A t x => @lem3219880 A s t x h0 h1)). Qed.
Lemma lem3219883 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term180 A x s t) : False.
Proof. exact (or_elim (@lem3219149 A x s t h1) (fun h0 : term124 A s t x => @lem3219882 A s t x h0) (fun h0 : term161 A x s t => @lem3219879 A x s t h0)). Qed.
Lemma lem3219884 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term180 A x s t) : (term180 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term180 A x s t => @lem3219883 A x s t h1) (fun h2 : False => @lem3219149 A x s t h1)). Qed.
Lemma lem3219885 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term180 A x s t) : False.
Proof. exact (EQ_MP (@lem3219884 A x s t h1) (@lem3219149 A x s t h1)). Qed.
Lemma lem3219886 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : False.
Proof. exact (ex_elim (@lem3219026 A s t h1) (fun x : A => fun h0 : term182 A s t x => @lem3219885 A x s t h0)). Qed.
Lemma lem3219887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : (term44 A s t) = False.
Proof. exact (prop_ext (fun h2 : term44 A s t => @lem3219886 A s t h1) (fun h2 : False => @lem3218545 A s t h1)). Qed.
Lemma lem3219888 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term44 A s t) : False.
Proof. exact (EQ_MP (@lem3219887 A s t h1) (@lem3218545 A s t h1)). Qed.
Lemma lem3219889 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term43 A s t.
Proof. exact (fun h0 : term44 A s t => @lem3219888 A s t h0). Qed.
Lemma lem3219890 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term24 A t s) = (term30 A s t).
Proof. exact (EQ_MP (@lem3218544 A s t) (@lem3219889 A s t)). Qed.
Lemma lem3219895 {A : Type'} (s : A -> Prop) : term32 A s.
Proof. exact (fun t : A -> Prop => @lem3219890 A s t). Qed.
Lemma lem3219900 {A : Type'} : term34 A.
Proof. exact (fun s : A -> Prop => @lem3219895 A s). Qed.
Lemma lem3219901 {A : Type'} : term36 A.
Proof. exact (EQ_MP (@lem3218540 A) (@lem3219900 A)). Qed.
Lemma lem3219903 {A : Type'} : term36 A.
Proof. exact (@lem3218427 A (@lem3219901 A)). Qed.
Lemma lem3219904 {A : Type'} (h1 : term37 A) : False.
Proof. exact (@lem3219903 A (@lem3218411 A h1)). Qed.
Lemma lem3219905 {A : Type'} (h1 : term37 A) : (term37 A) = False.
Proof. exact (prop_ext (fun h2 : term37 A => @lem3219904 A h1) (fun h2 : False => @lem3218411 A h1)). Qed.
Lemma lem3219906 {A : Type'} (h1 : term37 A) : False.
Proof. exact (EQ_MP (@lem3219905 A h1) (@lem3218411 A h1)). Qed.
Lemma lem3219907 {A : Type'} : term36 A.
Proof. exact (fun h0 : term37 A => @lem3219906 A h0). Qed.
Lemma lem3219908 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem3218410 A) (@lem3219907 A)). Qed.
Lemma lem3219909 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3218406 A) (@lem3219908 A)). Qed.
Lemma lem3219910 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3218291 A) (@lem3219909 A)). Qed.
