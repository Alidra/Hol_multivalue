Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_COMM_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3277219 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3277220 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3277219 A s t). Qed.
Lemma lem3277221 {A : Type'} (y : A) (x : A) (s : A -> Prop) : ((term1 A x y s) = (term1 A y x s)) = (term2 A y x s).
Proof. exact (@lem3277220 A (term1 A x y s) (term1 A y x s)). Qed.
Lemma lem3277230 {A : Type'} (y : A) (x : A) : (term3 A y x) = (term4 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3277221 A y x s)). Qed.
Lemma lem3277231 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3277232 {A : Type'} (y : A) (x : A) : (term5 A y x) = (term6 A y x).
Proof. exact (MK_COMB (@lem3277231 A) (@lem3277230 A y x)). Qed.
Lemma lem3277237 {A : Type'} (x : A) : (term7 A x) = (term8 A x).
Proof. exact (fun_ext (fun y : A => @lem3277232 A y x)). Qed.
Lemma lem3277238 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277239 {A : Type'} (x : A) : (term9 A x) = (term10 A x).
Proof. exact (MK_COMB (@lem3277238 A) (@lem3277237 A x)). Qed.
Lemma lem3277244 {A : Type'} : (term11 A) = (term12 A).
Proof. exact (fun_ext (fun x : A => @lem3277239 A x)). Qed.
Lemma lem3277245 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277246 {A : Type'} : (term13 A) = (term14 A).
Proof. exact (MK_COMB (@lem3277245 A) (@lem3277244 A)). Qed.
Lemma lem3277251 {A : Type'} : (term14 A) = (term13 A).
Proof. exact (SYM (@lem3277246 A)). Qed.
Lemma lem3277271 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3277272 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3277271 A y x s). Qed.
Lemma lem3277273 {A : Type'} (x : A) (x' : A) (y : A) (s : A -> Prop) : (term17 A x' x y s) = (term18 A x x' y s).
Proof. exact (@lem3277272 A x x' (@INSERT A y s)). Qed.
Lemma lem3277279 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3277280 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3277279 A y x s). Qed.
Lemma lem3277281 {A : Type'} (y : A) (x' : A) (s : A -> Prop) : (term15 A x' y s) = (term16 A y x' s).
Proof. exact (@lem3277280 A y x' s). Qed.
Lemma lem3277287 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3277288 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3277287 A P x). Qed.
Lemma lem3277289 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3277288 A s x'). Qed.
Lemma lem3277290 {A : Type'} (x' : A) (y : A) : (term19 A x' y) = (term19 A x' y).
Proof. exact (eq_refl (term19 A x' y)). Qed.
Lemma lem3277291 {A : Type'} (y : A) (s : A -> Prop) (x' : A) : (term16 A y x' s) = (term20 A y s x').
Proof. exact (MK_COMB (@lem3277290 A x' y) (@lem3277289 A s x')). Qed.
Lemma lem3277294 {A : Type'} (y : A) (s : A -> Prop) (x' : A) : (term15 A x' y s) = (term20 A y s x').
Proof. exact (TRANS (@lem3277281 A y x' s) (@lem3277291 A y s x')). Qed.
Lemma lem3277295 {A : Type'} (x' : A) (x : A) : (term19 A x' x) = (term19 A x' x).
Proof. exact (eq_refl (term19 A x' x)). Qed.
Lemma lem3277296 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term18 A x x' y s) = (term21 A x y s x').
Proof. exact (MK_COMB (@lem3277295 A x' x) (@lem3277294 A y s x')). Qed.
Lemma lem3277299 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term17 A x' x y s) = (term21 A x y s x').
Proof. exact (TRANS (@lem3277273 A x x' y s) (@lem3277296 A x y s x')). Qed.
Lemma lem3277300 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3277301 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term22 A x' x y s) = (term23 A x y s x').
Proof. exact (MK_COMB (@lem3277300) (@lem3277299 A x y s x')). Qed.
Lemma lem3277303 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3277304 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3277303 A y x s). Qed.
Lemma lem3277305 {A : Type'} (y : A) (x' : A) (x : A) (s : A -> Prop) : (term17 A x' y x s) = (term18 A y x' x s).
Proof. exact (@lem3277304 A y x' (@INSERT A x s)). Qed.
Lemma lem3277311 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3277312 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term15 A x y s) = (term16 A y x s).
Proof. exact (@lem3277311 A y x s). Qed.
Lemma lem3277313 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term15 A x' x s) = (term16 A x x' s).
Proof. exact (@lem3277312 A x x' s). Qed.
Lemma lem3277319 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3277320 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3277319 A P x). Qed.
Lemma lem3277321 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3277320 A s x'). Qed.
Lemma lem3277322 {A : Type'} (x' : A) (x : A) : (term19 A x' x) = (term19 A x' x).
Proof. exact (eq_refl (term19 A x' x)). Qed.
Lemma lem3277323 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term16 A x x' s) = (term20 A x s x').
Proof. exact (MK_COMB (@lem3277322 A x' x) (@lem3277321 A s x')). Qed.
Lemma lem3277326 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term15 A x' x s) = (term20 A x s x').
Proof. exact (TRANS (@lem3277313 A x x' s) (@lem3277323 A x s x')). Qed.
Lemma lem3277327 {A : Type'} (x' : A) (y : A) : (term19 A x' y) = (term19 A x' y).
Proof. exact (eq_refl (term19 A x' y)). Qed.
Lemma lem3277328 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term18 A y x' x s) = (term21 A y x s x').
Proof. exact (MK_COMB (@lem3277327 A x' y) (@lem3277326 A x s x')). Qed.
Lemma lem3277331 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term17 A x' y x s) = (term21 A y x s x').
Proof. exact (TRANS (@lem3277305 A y x' x s) (@lem3277328 A y x s x')). Qed.
Lemma lem3277332 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : ((term17 A x' x y s) = (term17 A x' y x s)) = ((term21 A x y s x') = (term21 A y x s x')).
Proof. exact (MK_COMB (@lem3277301 A x y s x') (@lem3277331 A y x s x')). Qed.
Lemma lem3277335 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term24 A y x s) = (term25 A y x s).
Proof. exact (fun_ext (fun x' : A => @lem3277332 A y x s x')). Qed.
Lemma lem3277336 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277337 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term2 A y x s) = (term26 A y x s).
Proof. exact (MK_COMB (@lem3277336 A) (@lem3277335 A y x s)). Qed.
Lemma lem3277342 {A : Type'} (y : A) (x : A) : (term4 A y x) = (term27 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3277337 A y x s)). Qed.
Lemma lem3277343 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3277344 {A : Type'} (y : A) (x : A) : (term6 A y x) = (term28 A y x).
Proof. exact (MK_COMB (@lem3277343 A) (@lem3277342 A y x)). Qed.
Lemma lem3277349 {A : Type'} (x : A) : (term8 A x) = (term29 A x).
Proof. exact (fun_ext (fun y : A => @lem3277344 A y x)). Qed.
Lemma lem3277350 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277351 {A : Type'} (x : A) : (term10 A x) = (term30 A x).
Proof. exact (MK_COMB (@lem3277350 A) (@lem3277349 A x)). Qed.
Lemma lem3277356 {A : Type'} : (term12 A) = (term31 A).
Proof. exact (fun_ext (fun x : A => @lem3277351 A x)). Qed.
Lemma lem3277357 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277358 {A : Type'} : (term14 A) = (term32 A).
Proof. exact (MK_COMB (@lem3277357 A) (@lem3277356 A)). Qed.
Lemma lem3277363 {A : Type'} : (term32 A) = (term14 A).
Proof. exact (SYM (@lem3277358 A)). Qed.
Lemma lem3277365 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3277366 {A : Type'} : (term32 A) = (term34 A).
Proof. exact (@lem3277365 (term32 A)). Qed.
Lemma lem3277367 {A : Type'} : (term34 A) = (term32 A).
Proof. exact (SYM (@lem3277366 A)). Qed.
Lemma lem3277368 {A : Type'} (h1 : term35 A) : term35 A.
Proof. exact (h1). Qed.
Lemma lem3277371 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem3277372 {A : Type'} : term36 A.
Proof. exact (fun h0 : term34 A => @lem3277371 A h0). Qed.
Lemma lem3277373 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3277374 {A : Type'} (h1 : term34 A) : term34 A.
Proof. exact (h1). Qed.
Lemma lem3277375 {A : Type'} (h1 : term34 A) (h2 : term36 A) : term34 A.
Proof. exact (@lem3277373 A h2 (@lem3277374 A h1)). Qed.
Lemma lem3277376 {A : Type'} (h1 : term34 A) : term37 A.
Proof. exact (fun h0 : term36 A => @lem3277375 A h1 h0). Qed.
Lemma lem3277377 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (h1). Qed.
Lemma lem3277378 {A : Type'} (h1 : term34 A) (h2 : term36 A) : term34 A.
Proof. exact (@lem3277376 A h1 (@lem3277377 A h2)). Qed.
Lemma lem3277379 {A : Type'} (h1 : term36 A) : term36 A.
Proof. exact (fun h0 : term34 A => @lem3277378 A h0 h1). Qed.
Lemma lem3277380 {A : Type'} : term38 A.
Proof. exact (fun h0 : term36 A => @lem3277379 A h0). Qed.
Lemma lem3277383 {A : Type'} : term36 A.
Proof. exact (@lem3277380 A (@lem3277372 A)). Qed.
Lemma lem3277384 {A : Type'} : term36 A.
Proof. exact (@lem3277383 A). Qed.
Lemma lem3277386 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3277387 {A : Type'} : (term34 A) = (term39 A).
Proof. exact (@lem3277386 (term35 A)). Qed.
Lemma lem3277389 (t : Prop) : (term40 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3277390 {A : Type'} : (term39 A) = (term32 A).
Proof. exact (@lem3277389 (term32 A)). Qed.
Lemma lem3277419 {A : Type'} : (term34 A) = (term32 A).
Proof. exact (TRANS (@lem3277387 A) (@lem3277390 A)). Qed.
Lemma lem3277440 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : ((term21 A x y s x') = (term21 A y x s x')) = ((term21 A x y s x') = (term21 A y x s x')).
Proof. exact (eq_refl ((term21 A x y s x') = (term21 A y x s x'))). Qed.
Lemma lem3277441 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term25 A y x s) = (term25 A y x s).
Proof. exact (fun_ext (fun x' : A => @lem3277440 A y x s x')). Qed.
Lemma lem3277442 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277443 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term26 A y x s) = (term26 A y x s).
Proof. exact (MK_COMB (@lem3277442 A) (@lem3277441 A y x s)). Qed.
Lemma lem3277444 {A : Type'} (y : A) (x : A) : (term27 A y x) = (term27 A y x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3277443 A y x s)). Qed.
Lemma lem3277445 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3277446 {A : Type'} (y : A) (x : A) : (term28 A y x) = (term28 A y x).
Proof. exact (MK_COMB (@lem3277445 A) (@lem3277444 A y x)). Qed.
Lemma lem3277447 {A : Type'} (x : A) : (term29 A x) = (term29 A x).
Proof. exact (fun_ext (fun y : A => @lem3277446 A y x)). Qed.
Lemma lem3277448 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277449 {A : Type'} (x : A) : (term30 A x) = (term30 A x).
Proof. exact (MK_COMB (@lem3277448 A) (@lem3277447 A x)). Qed.
Lemma lem3277450 {A : Type'} : (term31 A) = (term31 A).
Proof. exact (fun_ext (fun x : A => @lem3277449 A x)). Qed.
Lemma lem3277451 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3277452 {A : Type'} : (term32 A) = (term32 A).
Proof. exact (MK_COMB (@lem3277451 A) (@lem3277450 A)). Qed.
Lemma lem3277487 {A : Type'} : (term34 A) = (term32 A).
Proof. exact (TRANS (@lem3277419 A) (@lem3277452 A)). Qed.
Lemma lem3277488 {A : Type'} : (term32 A) = (term34 A).
Proof. exact (SYM (@lem3277487 A)). Qed.
Lemma lem3277490 (p : Prop) : p = (term33 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3277491 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : ((term21 A x y s x') = (term21 A y x s x')) = (term41 A y x s x').
Proof. exact (@lem3277490 ((term21 A x y s x') = (term21 A y x s x'))). Qed.
Lemma lem3277492 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term41 A y x s x') = ((term21 A x y s x') = (term21 A y x s x')).
Proof. exact (SYM (@lem3277491 A y x s x')). Qed.
Lemma lem3277493 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term42 A y x s x') : term42 A y x s x'.
Proof. exact (h1). Qed.
Lemma lem3277504 {A : Type'} (y : A) (s : A -> Prop) (x' : A) : (term43 A y s x') = (term44 A y s x').
Proof. exact (@lem17160 (x' = y) (s x')). Qed.
Lemma lem3277509 {A : Type'} (x' : A) (x : A) : (term45 A x' x) = (term45 A x' x).
Proof. exact (eq_refl (term45 A x' x)). Qed.
Lemma lem3277510 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term46 A x y s x') = (term47 A x y s x').
Proof. exact (MK_COMB (@lem3277509 A x' x) (@lem3277504 A y s x')). Qed.
Lemma lem3277511 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term48 A x y s x') = (term46 A x y s x').
Proof. exact (@lem17160 (x' = x) (term20 A y s x')). Qed.
Lemma lem3277512 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term48 A x y s x') = (term47 A x y s x').
Proof. exact (TRANS (@lem3277511 A x y s x') (@lem3277510 A x y s x')). Qed.
Lemma lem3277526 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term43 A x s x') = (term44 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3277531 {A : Type'} (x' : A) (y : A) : (term45 A x' y) = (term45 A x' y).
Proof. exact (eq_refl (term45 A x' y)). Qed.
Lemma lem3277532 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term46 A y x s x') = (term47 A y x s x').
Proof. exact (MK_COMB (@lem3277531 A x' y) (@lem3277526 A x s x')). Qed.
Lemma lem3277533 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term48 A y x s x') = (term46 A y x s x').
Proof. exact (@lem17160 (x' = y) (term20 A x s x')). Qed.
Lemma lem3277534 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term48 A y x s x') = (term47 A y x s x').
Proof. exact (TRANS (@lem3277533 A y x s x') (@lem3277532 A y x s x')). Qed.
Lemma lem3277537 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term21 A y x s x') = (term21 A y x s x').
Proof. exact (eq_refl (term21 A y x s x')). Qed.
Lemma lem3277538 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3277539 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term49 A x y s x') = (term50 A x y s x').
Proof. exact (MK_COMB (@lem3277538) (@lem3277512 A x y s x')). Qed.
Lemma lem3277540 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term51 A y x s x') = (term52 A y x s x').
Proof. exact (MK_COMB (@lem3277539 A x y s x') (@lem3277537 A y x s x')). Qed.
Lemma lem3277542 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) : (term53 A x y s x') = (term53 A x y s x').
Proof. exact (eq_refl (term53 A x y s x')). Qed.
Lemma lem3277543 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term54 A y x s x') = (term55 A y x s x').
Proof. exact (MK_COMB (@lem3277542 A x y s x') (@lem3277534 A y x s x')). Qed.
Lemma lem3277544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3277545 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term56 A y x s x') = (term57 A y x s x').
Proof. exact (MK_COMB (@lem3277544) (@lem3277543 A y x s x')). Qed.
Lemma lem3277546 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term58 A y x s x') = (term59 A y x s x').
Proof. exact (MK_COMB (@lem3277545 A y x s x') (@lem3277540 A y x s x')). Qed.
Lemma lem3277547 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term42 A y x s x') = (term58 A y x s x').
Proof. exact (@lem17646 (term21 A x y s x') (term21 A y x s x')). Qed.
Lemma lem3277552 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term42 A y x s x') = (term59 A y x s x').
Proof. exact (TRANS (@lem3277547 A y x s x') (@lem3277546 A y x s x')). Qed.
Lemma lem3277651 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term42 A y x s x') : term59 A y x s x'.
Proof. exact (EQ_MP (@lem3277552 A y x s x') (@lem3277493 A y x s x' h1)). Qed.
Lemma lem3277652 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term55 A y x s x'.
Proof. exact (h1). Qed.
Lemma lem3277653 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term52 A y x s x'.
Proof. exact (h1). Qed.
Lemma lem3277654 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term47 A y x s x'.
Proof. exact (proj2 (@lem3277652 A y x s x' h1)). Qed.
Lemma lem3277655 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term21 A x y s x'.
Proof. exact (proj1 (@lem3277652 A y x s x' h1)). Qed.
Lemma lem3277656 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term44 A x s x'.
Proof. exact (proj2 (@lem3277654 A y x s x' h1)). Qed.
Lemma lem3277661 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (h1 : term20 A y s x') : term20 A y s x'.
Proof. exact (h1). Qed.
Lemma lem3277664 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term21 A y x s x'.
Proof. exact (proj2 (@lem3277653 A y x s x' h1)). Qed.
Lemma lem3277665 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term47 A x y s x'.
Proof. exact (proj1 (@lem3277653 A y x s x' h1)). Qed.
Lemma lem3277666 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term44 A y s x'.
Proof. exact (proj2 (@lem3277665 A y x s x' h1)). Qed.
Lemma lem3277671 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term20 A x s x') : term20 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3277689 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3277705 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3277721 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3277737 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3277753 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3277769 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3277773 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term60 A x' x.
Proof. exact (proj1 (@lem3277656 A y x s x' h1)). Qed.
Lemma lem3277777 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3277779 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term60 A x' y.
Proof. exact (proj1 (@lem3277654 A y x s x' h1)). Qed.
Lemma lem3277785 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3277791 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term61 A s x'.
Proof. exact (proj2 (@lem3277656 A y x s x' h1)). Qed.
Lemma lem3277793 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3277797 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term60 A x' y.
Proof. exact (proj1 (@lem3277666 A y x s x' h1)). Qed.
Lemma lem3277801 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : x' = y.
Proof. exact (h1). Qed.
Lemma lem3277803 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term60 A x' x.
Proof. exact (proj1 (@lem3277665 A y x s x' h1)). Qed.
Lemma lem3277809 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3277815 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term61 A s x'.
Proof. exact (proj2 (@lem3277666 A y x s x' h1)). Qed.
Lemma lem3277817 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3277845 {A : Type'} (x : A) : (term62 A x) = (term62 A x).
Proof. exact (eq_refl (term62 A x)). Qed.
Lemma lem3277846 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term63 A x x') = (term64 A x).
Proof. exact (MK_COMB (@lem3277845 A x) (@lem3277777 A x' x h1)). Qed.
Lemma lem3277847 {A : Type'} (x : A) : (term64 A x) = (term65 A x).
Proof. exact (eq_refl (term64 A x)). Qed.
Lemma lem3277848 {A : Type'} (x : A) (x' : A) : (term66 A x x') = (term66 A x x').
Proof. exact (eq_refl (term66 A x x')). Qed.
Lemma lem3277849 {A : Type'} (x' : A) (x : A) : ((term63 A x x') = (term64 A x)) = ((term63 A x x') = (term65 A x)).
Proof. exact (MK_COMB (@lem3277848 A x x') (@lem3277847 A x)). Qed.
Lemma lem3277850 {A : Type'} (x' : A) (x : A) : (term63 A x x') = (term60 A x' x).
Proof. exact (eq_refl (term63 A x x')). Qed.
Lemma lem3277851 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3277852 {A : Type'} (x' : A) (x : A) : (term66 A x x') = (term67 A x' x).
Proof. exact (MK_COMB (@lem3277851) (@lem3277850 A x' x)). Qed.
Lemma lem3277853 {A : Type'} (x : A) : (term65 A x) = (term65 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3277854 {A : Type'} (x' : A) (x : A) : ((term63 A x x') = (term65 A x)) = ((term60 A x' x) = (term65 A x)).
Proof. exact (MK_COMB (@lem3277852 A x' x) (@lem3277853 A x)). Qed.
Lemma lem3277855 {A : Type'} (x' : A) (x : A) : ((term63 A x x') = (term64 A x)) = ((term60 A x' x) = (term65 A x)).
Proof. exact (TRANS (@lem3277849 A x' x) (@lem3277854 A x' x)). Qed.
Lemma lem3277856 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term60 A x' x) = (term65 A x).
Proof. exact (EQ_MP (@lem3277855 A x' x) (@lem3277846 A x' x h1)). Qed.
Lemma lem3277857 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : term65 A x.
Proof. exact (EQ_MP (@lem3277856 A x' x h2) (@lem3277773 A y x s x' h1)). Qed.
Lemma lem3277885 {A : Type'} (y : A) : (term62 A y) = (term62 A y).
Proof. exact (eq_refl (term62 A y)). Qed.
Lemma lem3277886 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term63 A y x') = (term64 A y).
Proof. exact (MK_COMB (@lem3277885 A y) (@lem3277785 A x' y h1)). Qed.
Lemma lem3277887 {A : Type'} (y : A) : (term64 A y) = (term65 A y).
Proof. exact (eq_refl (term64 A y)). Qed.
Lemma lem3277888 {A : Type'} (y : A) (x' : A) : (term66 A y x') = (term66 A y x').
Proof. exact (eq_refl (term66 A y x')). Qed.
Lemma lem3277889 {A : Type'} (x' : A) (y : A) : ((term63 A y x') = (term64 A y)) = ((term63 A y x') = (term65 A y)).
Proof. exact (MK_COMB (@lem3277888 A y x') (@lem3277887 A y)). Qed.
Lemma lem3277890 {A : Type'} (x' : A) (y : A) : (term63 A y x') = (term60 A x' y).
Proof. exact (eq_refl (term63 A y x')). Qed.
Lemma lem3277891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3277892 {A : Type'} (x' : A) (y : A) : (term66 A y x') = (term67 A x' y).
Proof. exact (MK_COMB (@lem3277891) (@lem3277890 A x' y)). Qed.
Lemma lem3277893 {A : Type'} (y : A) : (term65 A y) = (term65 A y).
Proof. exact (eq_refl (term65 A y)). Qed.
Lemma lem3277894 {A : Type'} (x' : A) (y : A) : ((term63 A y x') = (term65 A y)) = ((term60 A x' y) = (term65 A y)).
Proof. exact (MK_COMB (@lem3277892 A x' y) (@lem3277893 A y)). Qed.
Lemma lem3277895 {A : Type'} (x' : A) (y : A) : ((term63 A y x') = (term64 A y)) = ((term60 A x' y) = (term65 A y)).
Proof. exact (TRANS (@lem3277889 A x' y) (@lem3277894 A x' y)). Qed.
Lemma lem3277896 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term60 A x' y) = (term65 A y).
Proof. exact (EQ_MP (@lem3277895 A x' y) (@lem3277886 A x' y h1)). Qed.
Lemma lem3277897 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : term65 A y.
Proof. exact (EQ_MP (@lem3277896 A x' y h2) (@lem3277779 A y x s x' h1)). Qed.
Lemma lem3277951 {A : Type'} (y : A) : (term62 A y) = (term62 A y).
Proof. exact (eq_refl (term62 A y)). Qed.
Lemma lem3277952 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term63 A y x') = (term64 A y).
Proof. exact (MK_COMB (@lem3277951 A y) (@lem3277801 A x' y h1)). Qed.
Lemma lem3277953 {A : Type'} (y : A) : (term64 A y) = (term65 A y).
Proof. exact (eq_refl (term64 A y)). Qed.
Lemma lem3277954 {A : Type'} (y : A) (x' : A) : (term66 A y x') = (term66 A y x').
Proof. exact (eq_refl (term66 A y x')). Qed.
Lemma lem3277955 {A : Type'} (x' : A) (y : A) : ((term63 A y x') = (term64 A y)) = ((term63 A y x') = (term65 A y)).
Proof. exact (MK_COMB (@lem3277954 A y x') (@lem3277953 A y)). Qed.
Lemma lem3277956 {A : Type'} (x' : A) (y : A) : (term63 A y x') = (term60 A x' y).
Proof. exact (eq_refl (term63 A y x')). Qed.
Lemma lem3277957 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3277958 {A : Type'} (x' : A) (y : A) : (term66 A y x') = (term67 A x' y).
Proof. exact (MK_COMB (@lem3277957) (@lem3277956 A x' y)). Qed.
Lemma lem3277959 {A : Type'} (y : A) : (term65 A y) = (term65 A y).
Proof. exact (eq_refl (term65 A y)). Qed.
Lemma lem3277960 {A : Type'} (x' : A) (y : A) : ((term63 A y x') = (term65 A y)) = ((term60 A x' y) = (term65 A y)).
Proof. exact (MK_COMB (@lem3277958 A x' y) (@lem3277959 A y)). Qed.
Lemma lem3277961 {A : Type'} (x' : A) (y : A) : ((term63 A y x') = (term64 A y)) = ((term60 A x' y) = (term65 A y)).
Proof. exact (TRANS (@lem3277955 A x' y) (@lem3277960 A x' y)). Qed.
Lemma lem3277962 {A : Type'} (x' : A) (y : A) (h1 : x' = y) : (term60 A x' y) = (term65 A y).
Proof. exact (EQ_MP (@lem3277961 A x' y) (@lem3277952 A x' y h1)). Qed.
Lemma lem3277963 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : term65 A y.
Proof. exact (EQ_MP (@lem3277962 A x' y h2) (@lem3277797 A y x s x' h1)). Qed.
Lemma lem3277991 {A : Type'} (x : A) : (term62 A x) = (term62 A x).
Proof. exact (eq_refl (term62 A x)). Qed.
Lemma lem3277992 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term63 A x x') = (term64 A x).
Proof. exact (MK_COMB (@lem3277991 A x) (@lem3277809 A x' x h1)). Qed.
Lemma lem3277993 {A : Type'} (x : A) : (term64 A x) = (term65 A x).
Proof. exact (eq_refl (term64 A x)). Qed.
Lemma lem3277994 {A : Type'} (x : A) (x' : A) : (term66 A x x') = (term66 A x x').
Proof. exact (eq_refl (term66 A x x')). Qed.
Lemma lem3277995 {A : Type'} (x' : A) (x : A) : ((term63 A x x') = (term64 A x)) = ((term63 A x x') = (term65 A x)).
Proof. exact (MK_COMB (@lem3277994 A x x') (@lem3277993 A x)). Qed.
Lemma lem3277996 {A : Type'} (x' : A) (x : A) : (term63 A x x') = (term60 A x' x).
Proof. exact (eq_refl (term63 A x x')). Qed.
Lemma lem3277997 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3277998 {A : Type'} (x' : A) (x : A) : (term66 A x x') = (term67 A x' x).
Proof. exact (MK_COMB (@lem3277997) (@lem3277996 A x' x)). Qed.
Lemma lem3277999 {A : Type'} (x : A) : (term65 A x) = (term65 A x).
Proof. exact (eq_refl (term65 A x)). Qed.
Lemma lem3278000 {A : Type'} (x' : A) (x : A) : ((term63 A x x') = (term65 A x)) = ((term60 A x' x) = (term65 A x)).
Proof. exact (MK_COMB (@lem3277998 A x' x) (@lem3277999 A x)). Qed.
Lemma lem3278001 {A : Type'} (x' : A) (x : A) : ((term63 A x x') = (term64 A x)) = ((term60 A x' x) = (term65 A x)).
Proof. exact (TRANS (@lem3277995 A x' x) (@lem3278000 A x' x)). Qed.
Lemma lem3278002 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term60 A x' x) = (term65 A x).
Proof. exact (EQ_MP (@lem3278001 A x' x) (@lem3277992 A x' x h1)). Qed.
Lemma lem3278003 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : term65 A x.
Proof. exact (EQ_MP (@lem3278002 A x' x h2) (@lem3277803 A y x s x' h1)). Qed.
Lemma lem3278045 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3278046 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3278045 A x). Qed.
Lemma lem3278047 {A : Type'} (x : A) : term68 A x.
Proof. exact (fun h0 : term65 A x => @lem3278046 A x). Qed.
Lemma lem3278049 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278050 {A : Type'} (x : A) : (term68 A x) = (x = x).
Proof. exact (@lem3278049 (x = x)). Qed.
Lemma lem3278051 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3278050 A x) (@lem3278047 A x)). Qed.
Lemma lem3278054 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3278056 {A : Type'} (x : A) : (term65 A x) = (term70 A x).
Proof. exact (@lem3278054 (x = x)). Qed.
Lemma lem3278059 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : term70 A x.
Proof. exact (EQ_MP (@lem3278056 A x) (@lem3277857 A y s x' x h1 h2)). Qed.
Lemma lem3278062 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : False.
Proof. exact (@lem3278059 A y s x' x h1 h2 (@lem3278051 A x)). Qed.
Lemma lem3278063 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : term71.
Proof. exact (fun h0 : ~ False => @lem3278062 A y s x' x h1 h2). Qed.
Lemma lem3278065 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278066 : term71 = False.
Proof. exact (@lem3278065 False). Qed.
Lemma lem3278083 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3278084 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3278083 A x). Qed.
Lemma lem3278085 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3278084 A y). Qed.
Lemma lem3278086 {A : Type'} (y : A) : term68 A y.
Proof. exact (fun h0 : term65 A y => @lem3278085 A y). Qed.
Lemma lem3278088 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278089 {A : Type'} (y : A) : (term68 A y) = (y = y).
Proof. exact (@lem3278088 (y = y)). Qed.
Lemma lem3278090 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3278089 A y) (@lem3278086 A y)). Qed.
Lemma lem3278093 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3278095 {A : Type'} (y : A) : (term65 A y) = (term70 A y).
Proof. exact (@lem3278093 (y = y)). Qed.
Lemma lem3278098 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : term70 A y.
Proof. exact (EQ_MP (@lem3278095 A y) (@lem3277897 A x s x' y h1 h2)). Qed.
Lemma lem3278101 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : False.
Proof. exact (@lem3278098 A x s x' y h1 h2 (@lem3278090 A y)). Qed.
Lemma lem3278102 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : term71.
Proof. exact (fun h0 : ~ False => @lem3278101 A x s x' y h1 h2). Qed.
Lemma lem3278104 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278105 : term71 = False.
Proof. exact (@lem3278104 False). Qed.
Lemma lem3278122 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3278123 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term72 A s x'.
Proof. exact (fun h0 : term61 A s x' => @lem3278122 A s x' h1). Qed.
Lemma lem3278125 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278126 {A : Type'} (s : A -> Prop) (x' : A) : (term72 A s x') = (s x').
Proof. exact (@lem3278125 (s x')). Qed.
Lemma lem3278127 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3278126 A s x') (@lem3278123 A s x' h1)). Qed.
Lemma lem3278130 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3278132 {A : Type'} (s : A -> Prop) (x' : A) : (term61 A s x') = (term73 A s x').
Proof. exact (@lem3278130 (s x')). Qed.
Lemma lem3278135 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : term73 A s x'.
Proof. exact (EQ_MP (@lem3278132 A s x') (@lem3277791 A y x s x' h1)). Qed.
Lemma lem3278138 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : False.
Proof. exact (@lem3278135 A y x s x' h2 (@lem3278127 A s x' h1)). Qed.
Lemma lem3278139 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : term71.
Proof. exact (fun h0 : ~ False => @lem3278138 A y x s x' h1 h2). Qed.
Lemma lem3278141 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278142 : term71 = False.
Proof. exact (@lem3278141 False). Qed.
Lemma lem3278143 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278142) (@lem3278139 A y x s x' h1 h2)). Qed.
Lemma lem3278159 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3278160 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3278159 A x). Qed.
Lemma lem3278161 {A : Type'} (y : A) : y = y.
Proof. exact (@lem3278160 A y). Qed.
Lemma lem3278162 {A : Type'} (y : A) : term68 A y.
Proof. exact (fun h0 : term65 A y => @lem3278161 A y). Qed.
Lemma lem3278164 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278165 {A : Type'} (y : A) : (term68 A y) = (y = y).
Proof. exact (@lem3278164 (y = y)). Qed.
Lemma lem3278166 {A : Type'} (y : A) : y = y.
Proof. exact (EQ_MP (@lem3278165 A y) (@lem3278162 A y)). Qed.
Lemma lem3278169 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3278171 {A : Type'} (y : A) : (term65 A y) = (term70 A y).
Proof. exact (@lem3278169 (y = y)). Qed.
Lemma lem3278174 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : term70 A y.
Proof. exact (EQ_MP (@lem3278171 A y) (@lem3277963 A x s x' y h1 h2)). Qed.
Lemma lem3278177 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : False.
Proof. exact (@lem3278174 A x s x' y h1 h2 (@lem3278166 A y)). Qed.
Lemma lem3278178 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : term71.
Proof. exact (fun h0 : ~ False => @lem3278177 A x s x' y h1 h2). Qed.
Lemma lem3278180 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278181 : term71 = False.
Proof. exact (@lem3278180 False). Qed.
Lemma lem3278198 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3278199 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3278198 A x). Qed.
Lemma lem3278200 {A : Type'} (x : A) : term68 A x.
Proof. exact (fun h0 : term65 A x => @lem3278199 A x). Qed.
Lemma lem3278202 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278203 {A : Type'} (x : A) : (term68 A x) = (x = x).
Proof. exact (@lem3278202 (x = x)). Qed.
Lemma lem3278204 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3278203 A x) (@lem3278200 A x)). Qed.
Lemma lem3278207 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3278209 {A : Type'} (x : A) : (term65 A x) = (term70 A x).
Proof. exact (@lem3278207 (x = x)). Qed.
Lemma lem3278212 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : term70 A x.
Proof. exact (EQ_MP (@lem3278209 A x) (@lem3278003 A y s x' x h1 h2)). Qed.
Lemma lem3278215 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : False.
Proof. exact (@lem3278212 A y s x' x h1 h2 (@lem3278204 A x)). Qed.
Lemma lem3278216 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : term71.
Proof. exact (fun h0 : ~ False => @lem3278215 A y s x' x h1 h2). Qed.
Lemma lem3278218 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278219 : term71 = False.
Proof. exact (@lem3278218 False). Qed.
Lemma lem3278236 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3278237 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term72 A s x'.
Proof. exact (fun h0 : term61 A s x' => @lem3278236 A s x' h1). Qed.
Lemma lem3278239 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278240 {A : Type'} (s : A -> Prop) (x' : A) : (term72 A s x') = (s x').
Proof. exact (@lem3278239 (s x')). Qed.
Lemma lem3278241 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3278240 A s x') (@lem3278237 A s x' h1)). Qed.
Lemma lem3278244 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3278246 {A : Type'} (s : A -> Prop) (x' : A) : (term61 A s x') = (term73 A s x').
Proof. exact (@lem3278244 (s x')). Qed.
Lemma lem3278249 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : term73 A s x'.
Proof. exact (EQ_MP (@lem3278246 A s x') (@lem3277815 A y x s x' h1)). Qed.
Lemma lem3278252 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : False.
Proof. exact (@lem3278249 A y x s x' h2 (@lem3278241 A s x' h1)). Qed.
Lemma lem3278253 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : term71.
Proof. exact (fun h0 : ~ False => @lem3278252 A y x s x' h1 h2). Qed.
Lemma lem3278255 (p : Prop) : (term69 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3278256 : term71 = False.
Proof. exact (@lem3278255 False). Qed.
Lemma lem3278257 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278256) (@lem3278253 A y x s x' h1 h2)). Qed.
Lemma lem3278258 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278219) (@lem3278216 A y s x' x h1 h2)). Qed.
Lemma lem3278259 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278181) (@lem3278178 A x s x' y h1 h2)). Qed.
Lemma lem3278260 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278105) (@lem3278102 A x s x' y h1 h2)). Qed.
Lemma lem3278261 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278066) (@lem3278063 A y s x' x h1 h2)). Qed.
Lemma lem3278262 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3278257 A y x s x' h1 h2) (fun h3 : False => @lem3277817 A s x' h1)). Qed.
Lemma lem3278263 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278262 A y x s x' h1 h2) (@lem3277817 A s x' h1)). Qed.
Lemma lem3278264 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3278258 A y s x' x h1 h2) (fun h3 : False => @lem3277809 A x' x h2)). Qed.
Lemma lem3278265 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278264 A y s x' x h1 h2) (@lem3277809 A x' x h2)). Qed.
Lemma lem3278266 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3278259 A x s x' y h1 h2) (fun h3 : False => @lem3277801 A x' y h2)). Qed.
Lemma lem3278267 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278266 A x s x' y h1 h2) (@lem3277801 A x' y h2)). Qed.
Lemma lem3278268 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3278143 A y x s x' h1 h2) (fun h3 : False => @lem3277793 A s x' h1)). Qed.
Lemma lem3278269 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278268 A y x s x' h1 h2) (@lem3277793 A s x' h1)). Qed.
Lemma lem3278270 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3278260 A x s x' y h1 h2) (fun h3 : False => @lem3277785 A x' y h2)). Qed.
Lemma lem3278271 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278270 A x s x' y h1 h2) (@lem3277785 A x' y h2)). Qed.
Lemma lem3278272 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3278261 A y s x' x h1 h2) (fun h3 : False => @lem3277777 A x' x h2)). Qed.
Lemma lem3278273 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278272 A y s x' x h1 h2) (@lem3277777 A x' x h2)). Qed.
Lemma lem3278274 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3278263 A y x s x' h1 h2) (fun h3 : False => @lem3277769 A s x' h1)). Qed.
Lemma lem3278275 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278274 A y x s x' h1 h2) (@lem3277769 A s x' h1)). Qed.
Lemma lem3278276 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3278265 A y s x' x h1 h2) (fun h3 : False => @lem3277753 A x' x h2)). Qed.
Lemma lem3278277 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278276 A y s x' x h1 h2) (@lem3277753 A x' x h2)). Qed.
Lemma lem3278278 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3278267 A x s x' y h1 h2) (fun h3 : False => @lem3277737 A x' y h2)). Qed.
Lemma lem3278279 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278278 A x s x' y h1 h2) (@lem3277737 A x' y h2)). Qed.
Lemma lem3278280 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3278269 A y x s x' h1 h2) (fun h3 : False => @lem3277721 A s x' h1)). Qed.
Lemma lem3278281 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278280 A y x s x' h1 h2) (@lem3277721 A s x' h1)). Qed.
Lemma lem3278282 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3278271 A x s x' y h1 h2) (fun h3 : False => @lem3277705 A x' y h2)). Qed.
Lemma lem3278283 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278282 A x s x' y h1 h2) (@lem3277705 A x' y h2)). Qed.
Lemma lem3278284 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3278273 A y s x' x h1 h2) (fun h3 : False => @lem3277689 A x' x h2)). Qed.
Lemma lem3278285 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278284 A y s x' x h1 h2) (@lem3277689 A x' x h2)). Qed.
Lemma lem3278286 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3278275 A y x s x' h1 h2) (fun h3 : False => @lem3277769 A s x' h1)). Qed.
Lemma lem3278287 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term52 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278286 A y x s x' h1 h2) (@lem3277769 A s x' h1)). Qed.
Lemma lem3278288 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3278277 A y s x' x h1 h2) (fun h3 : False => @lem3277753 A x' x h2)). Qed.
Lemma lem3278289 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term52 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278288 A y s x' x h1 h2) (@lem3277753 A x' x h2)). Qed.
Lemma lem3278290 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3278279 A x s x' y h1 h2) (fun h3 : False => @lem3277737 A x' y h2)). Qed.
Lemma lem3278291 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term52 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278290 A x s x' y h1 h2) (@lem3277737 A x' y h2)). Qed.
Lemma lem3278292 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3278281 A y x s x' h1 h2) (fun h3 : False => @lem3277721 A s x' h1)). Qed.
Lemma lem3278293 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : s x') (h2 : term55 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278292 A y x s x' h1 h2) (@lem3277721 A s x' h1)). Qed.
Lemma lem3278294 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : (x' = y) = False.
Proof. exact (prop_ext (fun h3 : x' = y => @lem3278283 A x s x' y h1 h2) (fun h3 : False => @lem3277705 A x' y h2)). Qed.
Lemma lem3278295 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (y : A) (h1 : term55 A y x s x') (h2 : x' = y) : False.
Proof. exact (EQ_MP (@lem3278294 A x s x' y h1 h2) (@lem3277705 A x' y h2)). Qed.
Lemma lem3278296 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3278285 A y s x' x h1 h2) (fun h3 : False => @lem3277689 A x' x h2)). Qed.
Lemma lem3278297 {A : Type'} (y : A) (s : A -> Prop) (x' : A) (x : A) (h1 : term55 A y x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3278296 A y s x' x h1 h2) (@lem3277689 A x' x h2)). Qed.
Lemma lem3278298 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') (h2 : term20 A x s x') : False.
Proof. exact (or_elim (@lem3277671 A x s x' h2) (fun h0 : x' = x => @lem3278289 A y s x' x h1 h0) (fun h0 : s x' => @lem3278287 A y x s x' h0 h1)). Qed.
Lemma lem3278299 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term52 A y x s x') : False.
Proof. exact (or_elim (@lem3277664 A y x s x' h1) (fun h0 : x' = y => @lem3278291 A x s x' y h1 h0) (fun h0 : term20 A x s x' => @lem3278298 A y x s x' h1 h0)). Qed.
Lemma lem3278300 {A : Type'} (x : A) (y : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') (h2 : term20 A y s x') : False.
Proof. exact (or_elim (@lem3277661 A y s x' h2) (fun h0 : x' = y => @lem3278295 A x s x' y h1 h0) (fun h0 : s x' => @lem3278293 A y x s x' h0 h1)). Qed.
Lemma lem3278301 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term55 A y x s x') : False.
Proof. exact (or_elim (@lem3277655 A y x s x' h1) (fun h0 : x' = x => @lem3278297 A y s x' x h1 h0) (fun h0 : term20 A y s x' => @lem3278300 A x y s x' h1 h0)). Qed.
Lemma lem3278302 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term42 A y x s x') : False.
Proof. exact (or_elim (@lem3277651 A y x s x' h1) (fun h0 : term55 A y x s x' => @lem3278301 A y x s x' h0) (fun h0 : term52 A y x s x' => @lem3278299 A y x s x' h0)). Qed.
Lemma lem3278303 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term42 A y x s x') : (term42 A y x s x') = False.
Proof. exact (prop_ext (fun h2 : term42 A y x s x' => @lem3278302 A y x s x' h1) (fun h2 : False => @lem3277493 A y x s x' h1)). Qed.
Lemma lem3278304 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) (h1 : term42 A y x s x') : False.
Proof. exact (EQ_MP (@lem3278303 A y x s x' h1) (@lem3277493 A y x s x' h1)). Qed.
Lemma lem3278305 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : term41 A y x s x'.
Proof. exact (fun h0 : term42 A y x s x' => @lem3278304 A y x s x' h0). Qed.
Lemma lem3278306 {A : Type'} (y : A) (x : A) (s : A -> Prop) (x' : A) : (term21 A x y s x') = (term21 A y x s x').
Proof. exact (EQ_MP (@lem3277492 A y x s x') (@lem3278305 A y x s x')). Qed.
Lemma lem3278311 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term26 A y x s.
Proof. exact (fun x' : A => @lem3278306 A y x s x'). Qed.
Lemma lem3278316 {A : Type'} (y : A) (x : A) : term28 A y x.
Proof. exact (fun s : A -> Prop => @lem3278311 A y x s). Qed.
Lemma lem3278321 {A : Type'} (x : A) : term30 A x.
Proof. exact (fun y : A => @lem3278316 A y x). Qed.
Lemma lem3278326 {A : Type'} : term32 A.
Proof. exact (fun x : A => @lem3278321 A x). Qed.
Lemma lem3278327 {A : Type'} : term34 A.
Proof. exact (EQ_MP (@lem3277488 A) (@lem3278326 A)). Qed.
Lemma lem3278329 {A : Type'} : term34 A.
Proof. exact (@lem3277384 A (@lem3278327 A)). Qed.
Lemma lem3278330 {A : Type'} (h1 : term35 A) : False.
Proof. exact (@lem3278329 A (@lem3277368 A h1)). Qed.
Lemma lem3278331 {A : Type'} (h1 : term35 A) : (term35 A) = False.
Proof. exact (prop_ext (fun h2 : term35 A => @lem3278330 A h1) (fun h2 : False => @lem3277368 A h1)). Qed.
Lemma lem3278332 {A : Type'} (h1 : term35 A) : False.
Proof. exact (EQ_MP (@lem3278331 A h1) (@lem3277368 A h1)). Qed.
Lemma lem3278333 {A : Type'} : term34 A.
Proof. exact (fun h0 : term35 A => @lem3278332 A h0). Qed.
Lemma lem3278334 {A : Type'} : term32 A.
Proof. exact (EQ_MP (@lem3277367 A) (@lem3278333 A)). Qed.
Lemma lem3278335 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3277363 A) (@lem3278334 A)). Qed.
Lemma lem3278336 {A : Type'} : term13 A.
Proof. exact (EQ_MP (@lem3277251 A) (@lem3278335 A)). Qed.
