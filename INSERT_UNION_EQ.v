Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_UNION_EQ_term_abbrevs.
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
Require Import thm3211719_spec.
Require Import thm3211720_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3281294 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3281295 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term0 A s t).
Proof. exact (@lem3281294 A s t). Qed.
Lemma lem3281296 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term1 A x s t) = (term2 A x s t)) = (term3 A x s t).
Proof. exact (@lem3281295 A (term1 A x s t) (term2 A x s t)). Qed.
Lemma lem3281305 {A : Type'} (x : A) (s : A -> Prop) : (term4 A x s) = (term5 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3281296 A x s t)). Qed.
Lemma lem3281306 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3281307 {A : Type'} (x : A) (s : A -> Prop) : (term6 A x s) = (term7 A x s).
Proof. exact (MK_COMB (@lem3281306 A) (@lem3281305 A x s)). Qed.
Lemma lem3281312 {A : Type'} (x : A) : (term8 A x) = (term9 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3281307 A x s)). Qed.
Lemma lem3281313 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3281314 {A : Type'} (x : A) : (term10 A x) = (term11 A x).
Proof. exact (MK_COMB (@lem3281313 A) (@lem3281312 A x)). Qed.
Lemma lem3281319 {A : Type'} : (term12 A) = (term13 A).
Proof. exact (fun_ext (fun x : A => @lem3281314 A x)). Qed.
Lemma lem3281320 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3281321 {A : Type'} : (term14 A) = (term15 A).
Proof. exact (MK_COMB (@lem3281320 A) (@lem3281319 A)). Qed.
Lemma lem3281326 {A : Type'} : (term15 A) = (term14 A).
Proof. exact (SYM (@lem3281321 A)). Qed.
Lemma lem3281346 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3281347 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3281346 A s x t). Qed.
Lemma lem3281348 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term18 A x' x s t) = (term19 A x s x' t).
Proof. exact (@lem3281347 A (@INSERT A x s) x' t). Qed.
Lemma lem3281352 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term20 A x y s) = (term21 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3281353 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term20 A x y s) = (term21 A y x s).
Proof. exact (@lem3281352 A y x s). Qed.
Lemma lem3281354 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term20 A x' x s) = (term21 A x x' s).
Proof. exact (@lem3281353 A x x' s). Qed.
Lemma lem3281360 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3281361 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3281360 A P x). Qed.
Lemma lem3281362 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3281361 A s x'). Qed.
Lemma lem3281363 {A : Type'} (x' : A) (x : A) : (term22 A x' x) = (term22 A x' x).
Proof. exact (eq_refl (term22 A x' x)). Qed.
Lemma lem3281364 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term21 A x x' s) = (term23 A x s x').
Proof. exact (MK_COMB (@lem3281363 A x' x) (@lem3281362 A s x')). Qed.
Lemma lem3281367 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term20 A x' x s) = (term23 A x s x').
Proof. exact (TRANS (@lem3281354 A x x' s) (@lem3281364 A x s x')). Qed.
Lemma lem3281368 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3281369 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term24 A x' x s) = (term25 A x s x').
Proof. exact (MK_COMB (@lem3281368) (@lem3281367 A x s x')). Qed.
Lemma lem3281371 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3281372 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3281371 A P x). Qed.
Lemma lem3281373 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3281372 A t x'). Qed.
Lemma lem3281374 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term19 A x s x' t) = (term26 A x s t x').
Proof. exact (MK_COMB (@lem3281369 A x s x') (@lem3281373 A t x')). Qed.
Lemma lem3281377 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term18 A x' x s t) = (term26 A x s t x').
Proof. exact (TRANS (@lem3281348 A x s x' t) (@lem3281374 A x s t x')). Qed.
Lemma lem3281378 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3281379 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term27 A x' x s t) = (term28 A x s t x').
Proof. exact (MK_COMB (@lem3281378) (@lem3281377 A x s t x')). Qed.
Lemma lem3281381 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term20 A x y s) = (term21 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3281382 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term20 A x y s) = (term21 A y x s).
Proof. exact (@lem3281381 A y x s). Qed.
Lemma lem3281383 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term29 A x' x s t) = (term30 A x x' s t).
Proof. exact (@lem3281382 A x x' (@UNION A s t)). Qed.
Lemma lem3281389 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (EQ_MP (@lem3211720 A s x t) (@lem3211719 A s t x)). Qed.
Lemma lem3281390 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term16 A x s t) = (term17 A s x t).
Proof. exact (@lem3281389 A s x t). Qed.
Lemma lem3281391 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term16 A x' s t) = (term17 A s x' t).
Proof. exact (@lem3281390 A s x' t). Qed.
Lemma lem3281395 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3281396 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3281395 A P x). Qed.
Lemma lem3281397 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3281396 A s x'). Qed.
Lemma lem3281398 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3281399 {A : Type'} (s : A -> Prop) (x' : A) : (term31 A x' s) = (term32 A s x').
Proof. exact (MK_COMB (@lem3281398) (@lem3281397 A s x')). Qed.
Lemma lem3281401 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3281402 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3281401 A P x). Qed.
Lemma lem3281403 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3281402 A t x'). Qed.
Lemma lem3281404 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term17 A s x' t) = (term33 A s t x').
Proof. exact (MK_COMB (@lem3281399 A s x') (@lem3281403 A t x')). Qed.
Lemma lem3281407 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term16 A x' s t) = (term33 A s t x').
Proof. exact (TRANS (@lem3281391 A s x' t) (@lem3281404 A s t x')). Qed.
Lemma lem3281408 {A : Type'} (x' : A) (x : A) : (term22 A x' x) = (term22 A x' x).
Proof. exact (eq_refl (term22 A x' x)). Qed.
Lemma lem3281409 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term30 A x x' s t) = (term34 A x s t x').
Proof. exact (MK_COMB (@lem3281408 A x' x) (@lem3281407 A s t x')). Qed.
Lemma lem3281412 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term29 A x' x s t) = (term34 A x s t x').
Proof. exact (TRANS (@lem3281383 A x x' s t) (@lem3281409 A x s t x')). Qed.
Lemma lem3281413 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term18 A x' x s t) = (term29 A x' x s t)) = ((term26 A x s t x') = (term34 A x s t x')).
Proof. exact (MK_COMB (@lem3281379 A x s t x') (@lem3281412 A x s t x')). Qed.
Lemma lem3281416 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term35 A x s t) = (term36 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3281413 A x s t x')). Qed.
Lemma lem3281417 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3281418 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term3 A x s t) = (term37 A x s t).
Proof. exact (MK_COMB (@lem3281417 A) (@lem3281416 A x s t)). Qed.
Lemma lem3281423 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term38 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3281418 A x s t)). Qed.
Lemma lem3281424 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3281425 {A : Type'} (x : A) (s : A -> Prop) : (term7 A x s) = (term39 A x s).
Proof. exact (MK_COMB (@lem3281424 A) (@lem3281423 A x s)). Qed.
Lemma lem3281430 {A : Type'} (x : A) : (term9 A x) = (term40 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3281425 A x s)). Qed.
Lemma lem3281431 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3281432 {A : Type'} (x : A) : (term11 A x) = (term41 A x).
Proof. exact (MK_COMB (@lem3281431 A) (@lem3281430 A x)). Qed.
Lemma lem3281437 {A : Type'} : (term13 A) = (term42 A).
Proof. exact (fun_ext (fun x : A => @lem3281432 A x)). Qed.
Lemma lem3281438 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3281439 {A : Type'} : (term15 A) = (term43 A).
Proof. exact (MK_COMB (@lem3281438 A) (@lem3281437 A)). Qed.
Lemma lem3281444 {A : Type'} : (term43 A) = (term15 A).
Proof. exact (SYM (@lem3281439 A)). Qed.
Lemma lem3281446 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3281447 {A : Type'} : (term43 A) = (term45 A).
Proof. exact (@lem3281446 (term43 A)). Qed.
Lemma lem3281448 {A : Type'} : (term45 A) = (term43 A).
Proof. exact (SYM (@lem3281447 A)). Qed.
Lemma lem3281449 {A : Type'} (h1 : term46 A) : term46 A.
Proof. exact (h1). Qed.
Lemma lem3281452 {A : Type'} (h1 : term45 A) : term45 A.
Proof. exact (h1). Qed.
Lemma lem3281453 {A : Type'} : term47 A.
Proof. exact (fun h0 : term45 A => @lem3281452 A h0). Qed.
Lemma lem3281454 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem3281455 {A : Type'} (h1 : term45 A) : term45 A.
Proof. exact (h1). Qed.
Lemma lem3281456 {A : Type'} (h1 : term45 A) (h2 : term47 A) : term45 A.
Proof. exact (@lem3281454 A h2 (@lem3281455 A h1)). Qed.
Lemma lem3281457 {A : Type'} (h1 : term45 A) : term48 A.
Proof. exact (fun h0 : term47 A => @lem3281456 A h1 h0). Qed.
Lemma lem3281458 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (h1). Qed.
Lemma lem3281459 {A : Type'} (h1 : term45 A) (h2 : term47 A) : term45 A.
Proof. exact (@lem3281457 A h1 (@lem3281458 A h2)). Qed.
Lemma lem3281460 {A : Type'} (h1 : term47 A) : term47 A.
Proof. exact (fun h0 : term45 A => @lem3281459 A h0 h1). Qed.
Lemma lem3281461 {A : Type'} : term49 A.
Proof. exact (fun h0 : term47 A => @lem3281460 A h0). Qed.
Lemma lem3281464 {A : Type'} : term47 A.
Proof. exact (@lem3281461 A (@lem3281453 A)). Qed.
Lemma lem3281465 {A : Type'} : term47 A.
Proof. exact (@lem3281464 A). Qed.
Lemma lem3281467 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3281468 {A : Type'} : (term45 A) = (term50 A).
Proof. exact (@lem3281467 (term46 A)). Qed.
Lemma lem3281470 (t : Prop) : (term51 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3281471 {A : Type'} : (term50 A) = (term43 A).
Proof. exact (@lem3281470 (term43 A)). Qed.
Lemma lem3281500 {A : Type'} : (term45 A) = (term43 A).
Proof. exact (TRANS (@lem3281468 A) (@lem3281471 A)). Qed.
Lemma lem3281521 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term26 A x s t x') = (term34 A x s t x')) = ((term26 A x s t x') = (term34 A x s t x')).
Proof. exact (eq_refl ((term26 A x s t x') = (term34 A x s t x'))). Qed.
Lemma lem3281522 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term36 A x s t) = (term36 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3281521 A x s t x')). Qed.
Lemma lem3281523 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3281524 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term37 A x s t) = (term37 A x s t).
Proof. exact (MK_COMB (@lem3281523 A) (@lem3281522 A x s t)). Qed.
Lemma lem3281525 {A : Type'} (x : A) (s : A -> Prop) : (term38 A x s) = (term38 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3281524 A x s t)). Qed.
Lemma lem3281526 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3281527 {A : Type'} (x : A) (s : A -> Prop) : (term39 A x s) = (term39 A x s).
Proof. exact (MK_COMB (@lem3281526 A) (@lem3281525 A x s)). Qed.
Lemma lem3281528 {A : Type'} (x : A) : (term40 A x) = (term40 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3281527 A x s)). Qed.
Lemma lem3281529 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3281530 {A : Type'} (x : A) : (term41 A x) = (term41 A x).
Proof. exact (MK_COMB (@lem3281529 A) (@lem3281528 A x)). Qed.
Lemma lem3281531 {A : Type'} : (term42 A) = (term42 A).
Proof. exact (fun_ext (fun x : A => @lem3281530 A x)). Qed.
Lemma lem3281532 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3281533 {A : Type'} : (term43 A) = (term43 A).
Proof. exact (MK_COMB (@lem3281532 A) (@lem3281531 A)). Qed.
Lemma lem3281568 {A : Type'} : (term45 A) = (term43 A).
Proof. exact (TRANS (@lem3281500 A) (@lem3281533 A)). Qed.
Lemma lem3281569 {A : Type'} : (term43 A) = (term45 A).
Proof. exact (SYM (@lem3281568 A)). Qed.
Lemma lem3281571 (p : Prop) : p = (term44 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3281572 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term26 A x s t x') = (term34 A x s t x')) = (term52 A x s t x').
Proof. exact (@lem3281571 ((term26 A x s t x') = (term34 A x s t x'))). Qed.
Lemma lem3281573 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term52 A x s t x') = ((term26 A x s t x') = (term34 A x s t x')).
Proof. exact (SYM (@lem3281572 A x s t x')). Qed.
Lemma lem3281574 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term53 A x s t x') : term53 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3281583 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term54 A x s x') = (term55 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3281587 {A : Type'} (t : A -> Prop) (x' : A) : (term56 A t x') = (term56 A t x').
Proof. exact (eq_refl (term56 A t x')). Qed.
Lemma lem3281589 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3281590 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term57 A x s x') = (term58 A x s x').
Proof. exact (MK_COMB (@lem3281589) (@lem3281583 A x s x')). Qed.
Lemma lem3281591 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term59 A x s t x') = (term60 A x s t x').
Proof. exact (MK_COMB (@lem3281590 A x s x') (@lem3281587 A t x')). Qed.
Lemma lem3281592 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term61 A x s t x') = (term59 A x s t x').
Proof. exact (@lem17160 (term23 A x s x') (t x')). Qed.
Lemma lem3281593 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term61 A x s t x') = (term60 A x s t x').
Proof. exact (TRANS (@lem3281592 A x s t x') (@lem3281591 A x s t x')). Qed.
Lemma lem3281607 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term62 A s t x') = (term63 A s t x').
Proof. exact (@lem17160 (s x') (t x')). Qed.
Lemma lem3281612 {A : Type'} (x' : A) (x : A) : (term64 A x' x) = (term64 A x' x).
Proof. exact (eq_refl (term64 A x' x)). Qed.
Lemma lem3281613 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term65 A x s t x') = (term66 A x s t x').
Proof. exact (MK_COMB (@lem3281612 A x' x) (@lem3281607 A s t x')). Qed.
Lemma lem3281614 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term67 A x s t x') = (term65 A x s t x').
Proof. exact (@lem17160 (x' = x) (term33 A s t x')). Qed.
Lemma lem3281615 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term67 A x s t x') = (term66 A x s t x').
Proof. exact (TRANS (@lem3281614 A x s t x') (@lem3281613 A x s t x')). Qed.
Lemma lem3281618 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term34 A x s t x') = (term34 A x s t x').
Proof. exact (eq_refl (term34 A x s t x')). Qed.
Lemma lem3281619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3281620 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term68 A x s t x') = (term69 A x s t x').
Proof. exact (MK_COMB (@lem3281619) (@lem3281593 A x s t x')). Qed.
Lemma lem3281621 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term70 A x s t x') = (term71 A x s t x').
Proof. exact (MK_COMB (@lem3281620 A x s t x') (@lem3281618 A x s t x')). Qed.
Lemma lem3281623 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term72 A x s t x') = (term72 A x s t x').
Proof. exact (eq_refl (term72 A x s t x')). Qed.
Lemma lem3281624 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term73 A x s t x') = (term74 A x s t x').
Proof. exact (MK_COMB (@lem3281623 A x s t x') (@lem3281615 A x s t x')). Qed.
Lemma lem3281625 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3281626 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term75 A x s t x') = (term76 A x s t x').
Proof. exact (MK_COMB (@lem3281625) (@lem3281624 A x s t x')). Qed.
Lemma lem3281627 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term77 A x s t x') = (term78 A x s t x').
Proof. exact (MK_COMB (@lem3281626 A x s t x') (@lem3281621 A x s t x')). Qed.
Lemma lem3281628 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term53 A x s t x') = (term77 A x s t x').
Proof. exact (@lem17646 (term26 A x s t x') (term34 A x s t x')). Qed.
Lemma lem3281633 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term53 A x s t x') = (term78 A x s t x').
Proof. exact (TRANS (@lem3281628 A x s t x') (@lem3281627 A x s t x')). Qed.
Lemma lem3281724 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term53 A x s t x') : term78 A x s t x'.
Proof. exact (EQ_MP (@lem3281633 A x s t x') (@lem3281574 A x s t x' h1)). Qed.
Lemma lem3281725 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term74 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3281726 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term71 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3281727 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term66 A x s t x'.
Proof. exact (proj2 (@lem3281725 A x s t x' h1)). Qed.
Lemma lem3281728 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term26 A x s t x'.
Proof. exact (proj1 (@lem3281725 A x s t x' h1)). Qed.
Lemma lem3281729 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term63 A s t x'.
Proof. exact (proj2 (@lem3281727 A x s t x' h1)). Qed.
Lemma lem3281733 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term23 A x s x') : term23 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3281737 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term34 A x s t x'.
Proof. exact (proj2 (@lem3281726 A x s t x' h1)). Qed.
Lemma lem3281738 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term60 A x s t x'.
Proof. exact (proj1 (@lem3281726 A x s t x' h1)). Qed.
Lemma lem3281740 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term55 A x s x'.
Proof. exact (proj1 (@lem3281738 A x s t x' h1)). Qed.
Lemma lem3281744 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term33 A s t x') : term33 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3281762 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3281778 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3281794 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3281810 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3281826 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3281842 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3281844 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term79 A x' x.
Proof. exact (proj1 (@lem3281727 A x s t x' h1)). Qed.
Lemma lem3281850 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3281854 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term56 A s x'.
Proof. exact (proj1 (@lem3281729 A x s t x' h1)). Qed.
Lemma lem3281858 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3281864 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term56 A t x'.
Proof. exact (proj2 (@lem3281729 A x s t x' h1)). Qed.
Lemma lem3281866 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3281870 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term79 A x' x.
Proof. exact (proj1 (@lem3281740 A x s t x' h1)). Qed.
Lemma lem3281874 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3281880 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term56 A s x'.
Proof. exact (proj2 (@lem3281740 A x s t x' h1)). Qed.
Lemma lem3281882 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3281884 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term56 A t x'.
Proof. exact (proj2 (@lem3281738 A x s t x' h1)). Qed.
Lemma lem3281890 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3281905 {A : Type'} (x : A) : (term80 A x) = (term80 A x).
Proof. exact (eq_refl (term80 A x)). Qed.
Lemma lem3281906 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term81 A x x') = (term82 A x).
Proof. exact (MK_COMB (@lem3281905 A x) (@lem3281850 A x' x h1)). Qed.
Lemma lem3281907 {A : Type'} (x : A) : (term82 A x) = (term83 A x).
Proof. exact (eq_refl (term82 A x)). Qed.
Lemma lem3281908 {A : Type'} (x : A) (x' : A) : (term84 A x x') = (term84 A x x').
Proof. exact (eq_refl (term84 A x x')). Qed.
Lemma lem3281909 {A : Type'} (x' : A) (x : A) : ((term81 A x x') = (term82 A x)) = ((term81 A x x') = (term83 A x)).
Proof. exact (MK_COMB (@lem3281908 A x x') (@lem3281907 A x)). Qed.
Lemma lem3281910 {A : Type'} (x' : A) (x : A) : (term81 A x x') = (term79 A x' x).
Proof. exact (eq_refl (term81 A x x')). Qed.
Lemma lem3281911 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3281912 {A : Type'} (x' : A) (x : A) : (term84 A x x') = (term85 A x' x).
Proof. exact (MK_COMB (@lem3281911) (@lem3281910 A x' x)). Qed.
Lemma lem3281913 {A : Type'} (x : A) : (term83 A x) = (term83 A x).
Proof. exact (eq_refl (term83 A x)). Qed.
Lemma lem3281914 {A : Type'} (x' : A) (x : A) : ((term81 A x x') = (term83 A x)) = ((term79 A x' x) = (term83 A x)).
Proof. exact (MK_COMB (@lem3281912 A x' x) (@lem3281913 A x)). Qed.
Lemma lem3281915 {A : Type'} (x' : A) (x : A) : ((term81 A x x') = (term82 A x)) = ((term79 A x' x) = (term83 A x)).
Proof. exact (TRANS (@lem3281909 A x' x) (@lem3281914 A x' x)). Qed.
Lemma lem3281916 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term79 A x' x) = (term83 A x).
Proof. exact (EQ_MP (@lem3281915 A x' x) (@lem3281906 A x' x h1)). Qed.
Lemma lem3281917 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : term83 A x.
Proof. exact (EQ_MP (@lem3281916 A x' x h2) (@lem3281844 A x s t x' h1)). Qed.
Lemma lem3281971 {A : Type'} (x : A) : (term80 A x) = (term80 A x).
Proof. exact (eq_refl (term80 A x)). Qed.
Lemma lem3281972 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term81 A x x') = (term82 A x).
Proof. exact (MK_COMB (@lem3281971 A x) (@lem3281874 A x' x h1)). Qed.
Lemma lem3281973 {A : Type'} (x : A) : (term82 A x) = (term83 A x).
Proof. exact (eq_refl (term82 A x)). Qed.
Lemma lem3281974 {A : Type'} (x : A) (x' : A) : (term84 A x x') = (term84 A x x').
Proof. exact (eq_refl (term84 A x x')). Qed.
Lemma lem3281975 {A : Type'} (x' : A) (x : A) : ((term81 A x x') = (term82 A x)) = ((term81 A x x') = (term83 A x)).
Proof. exact (MK_COMB (@lem3281974 A x x') (@lem3281973 A x)). Qed.
Lemma lem3281976 {A : Type'} (x' : A) (x : A) : (term81 A x x') = (term79 A x' x).
Proof. exact (eq_refl (term81 A x x')). Qed.
Lemma lem3281977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3281978 {A : Type'} (x' : A) (x : A) : (term84 A x x') = (term85 A x' x).
Proof. exact (MK_COMB (@lem3281977) (@lem3281976 A x' x)). Qed.
Lemma lem3281979 {A : Type'} (x : A) : (term83 A x) = (term83 A x).
Proof. exact (eq_refl (term83 A x)). Qed.
Lemma lem3281980 {A : Type'} (x' : A) (x : A) : ((term81 A x x') = (term83 A x)) = ((term79 A x' x) = (term83 A x)).
Proof. exact (MK_COMB (@lem3281978 A x' x) (@lem3281979 A x)). Qed.
Lemma lem3281981 {A : Type'} (x' : A) (x : A) : ((term81 A x x') = (term82 A x)) = ((term79 A x' x) = (term83 A x)).
Proof. exact (TRANS (@lem3281975 A x' x) (@lem3281980 A x' x)). Qed.
Lemma lem3281982 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term79 A x' x) = (term83 A x).
Proof. exact (EQ_MP (@lem3281981 A x' x) (@lem3281972 A x' x h1)). Qed.
Lemma lem3281983 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : term83 A x.
Proof. exact (EQ_MP (@lem3281982 A x' x h2) (@lem3281870 A x s t x' h1)). Qed.
Lemma lem3282024 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3282025 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3282024 A x). Qed.
Lemma lem3282026 {A : Type'} (x : A) : term86 A x.
Proof. exact (fun h0 : term83 A x => @lem3282025 A x). Qed.
Lemma lem3282028 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282029 {A : Type'} (x : A) : (term86 A x) = (x = x).
Proof. exact (@lem3282028 (x = x)). Qed.
Lemma lem3282030 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3282029 A x) (@lem3282026 A x)). Qed.
Lemma lem3282033 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3282035 {A : Type'} (x : A) : (term83 A x) = (term88 A x).
Proof. exact (@lem3282033 (x = x)). Qed.
Lemma lem3282038 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : term88 A x.
Proof. exact (EQ_MP (@lem3282035 A x) (@lem3281917 A s t x' x h1 h2)). Qed.
Lemma lem3282041 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3282038 A s t x' x h1 h2 (@lem3282030 A x)). Qed.
Lemma lem3282042 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : term89.
Proof. exact (fun h0 : ~ False => @lem3282041 A s t x' x h1 h2). Qed.
Lemma lem3282044 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282045 : term89 = False.
Proof. exact (@lem3282044 False). Qed.
Lemma lem3282074 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3282075 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term90 A s x'.
Proof. exact (fun h0 : term56 A s x' => @lem3282074 A s x' h1). Qed.
Lemma lem3282077 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282078 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3282077 (s x')). Qed.
Lemma lem3282079 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3282078 A s x') (@lem3282075 A s x' h1)). Qed.
Lemma lem3282082 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3282084 {A : Type'} (s : A -> Prop) (x' : A) : (term56 A s x') = (term91 A s x').
Proof. exact (@lem3282082 (s x')). Qed.
Lemma lem3282087 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term91 A s x'.
Proof. exact (EQ_MP (@lem3282084 A s x') (@lem3281854 A x s t x' h1)). Qed.
Lemma lem3282090 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : False.
Proof. exact (@lem3282087 A x s t x' h2 (@lem3282079 A s x' h1)). Qed.
Lemma lem3282091 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : term89.
Proof. exact (fun h0 : ~ False => @lem3282090 A x s t x' h1 h2). Qed.
Lemma lem3282093 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282094 : term89 = False.
Proof. exact (@lem3282093 False). Qed.
Lemma lem3282095 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282094) (@lem3282091 A x s t x' h1 h2)). Qed.
Lemma lem3282123 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3282124 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term90 A t x'.
Proof. exact (fun h0 : term56 A t x' => @lem3282123 A t x' h1). Qed.
Lemma lem3282126 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282127 {A : Type'} (t : A -> Prop) (x' : A) : (term90 A t x') = (t x').
Proof. exact (@lem3282126 (t x')). Qed.
Lemma lem3282128 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3282127 A t x') (@lem3282124 A t x' h1)). Qed.
Lemma lem3282131 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3282133 {A : Type'} (t : A -> Prop) (x' : A) : (term56 A t x') = (term91 A t x').
Proof. exact (@lem3282131 (t x')). Qed.
Lemma lem3282136 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : term91 A t x'.
Proof. exact (EQ_MP (@lem3282133 A t x') (@lem3281864 A x s t x' h1)). Qed.
Lemma lem3282139 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : False.
Proof. exact (@lem3282136 A x s t x' h2 (@lem3282128 A t x' h1)). Qed.
Lemma lem3282140 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : term89.
Proof. exact (fun h0 : ~ False => @lem3282139 A x s t x' h1 h2). Qed.
Lemma lem3282142 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282143 : term89 = False.
Proof. exact (@lem3282142 False). Qed.
Lemma lem3282144 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282143) (@lem3282140 A x s t x' h1 h2)). Qed.
Lemma lem3282172 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3282173 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3282172 A x). Qed.
Lemma lem3282174 {A : Type'} (x : A) : term86 A x.
Proof. exact (fun h0 : term83 A x => @lem3282173 A x). Qed.
Lemma lem3282176 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282177 {A : Type'} (x : A) : (term86 A x) = (x = x).
Proof. exact (@lem3282176 (x = x)). Qed.
Lemma lem3282178 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3282177 A x) (@lem3282174 A x)). Qed.
Lemma lem3282181 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3282183 {A : Type'} (x : A) : (term83 A x) = (term88 A x).
Proof. exact (@lem3282181 (x = x)). Qed.
Lemma lem3282186 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : term88 A x.
Proof. exact (EQ_MP (@lem3282183 A x) (@lem3281983 A s t x' x h1 h2)). Qed.
Lemma lem3282189 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3282186 A s t x' x h1 h2 (@lem3282178 A x)). Qed.
Lemma lem3282190 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : term89.
Proof. exact (fun h0 : ~ False => @lem3282189 A s t x' x h1 h2). Qed.
Lemma lem3282192 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282193 : term89 = False.
Proof. exact (@lem3282192 False). Qed.
Lemma lem3282222 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3282223 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term90 A s x'.
Proof. exact (fun h0 : term56 A s x' => @lem3282222 A s x' h1). Qed.
Lemma lem3282225 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282226 {A : Type'} (s : A -> Prop) (x' : A) : (term90 A s x') = (s x').
Proof. exact (@lem3282225 (s x')). Qed.
Lemma lem3282227 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3282226 A s x') (@lem3282223 A s x' h1)). Qed.
Lemma lem3282230 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3282232 {A : Type'} (s : A -> Prop) (x' : A) : (term56 A s x') = (term91 A s x').
Proof. exact (@lem3282230 (s x')). Qed.
Lemma lem3282235 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term91 A s x'.
Proof. exact (EQ_MP (@lem3282232 A s x') (@lem3281880 A x s t x' h1)). Qed.
Lemma lem3282238 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : False.
Proof. exact (@lem3282235 A x s t x' h2 (@lem3282227 A s x' h1)). Qed.
Lemma lem3282239 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : term89.
Proof. exact (fun h0 : ~ False => @lem3282238 A x s t x' h1 h2). Qed.
Lemma lem3282241 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282242 : term89 = False.
Proof. exact (@lem3282241 False). Qed.
Lemma lem3282243 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282242) (@lem3282239 A x s t x' h1 h2)). Qed.
Lemma lem3282271 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (h1). Qed.
Lemma lem3282272 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : term90 A t x'.
Proof. exact (fun h0 : term56 A t x' => @lem3282271 A t x' h1). Qed.
Lemma lem3282274 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282275 {A : Type'} (t : A -> Prop) (x' : A) : (term90 A t x') = (t x').
Proof. exact (@lem3282274 (t x')). Qed.
Lemma lem3282276 {A : Type'} (t : A -> Prop) (x' : A) (h1 : t x') : t x'.
Proof. exact (EQ_MP (@lem3282275 A t x') (@lem3282272 A t x' h1)). Qed.
Lemma lem3282279 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3282281 {A : Type'} (t : A -> Prop) (x' : A) : (term56 A t x') = (term91 A t x').
Proof. exact (@lem3282279 (t x')). Qed.
Lemma lem3282284 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : term91 A t x'.
Proof. exact (EQ_MP (@lem3282281 A t x') (@lem3281884 A x s t x' h1)). Qed.
Lemma lem3282287 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : False.
Proof. exact (@lem3282284 A x s t x' h2 (@lem3282276 A t x' h1)). Qed.
Lemma lem3282288 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : term89.
Proof. exact (fun h0 : ~ False => @lem3282287 A x s t x' h1 h2). Qed.
Lemma lem3282290 (p : Prop) : (term87 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3282291 : term89 = False.
Proof. exact (@lem3282290 False). Qed.
Lemma lem3282292 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282291) (@lem3282288 A x s t x' h1 h2)). Qed.
Lemma lem3282293 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282193) (@lem3282190 A s t x' x h1 h2)). Qed.
Lemma lem3282294 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282045) (@lem3282042 A s t x' x h1 h2)). Qed.
Lemma lem3282295 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3282292 A x s t x' h1 h2) (fun h3 : False => @lem3281890 A t x' h1)). Qed.
Lemma lem3282296 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282295 A x s t x' h1 h2) (@lem3281890 A t x' h1)). Qed.
Lemma lem3282297 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3282243 A x s t x' h1 h2) (fun h3 : False => @lem3281882 A s x' h1)). Qed.
Lemma lem3282298 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282297 A x s t x' h1 h2) (@lem3281882 A s x' h1)). Qed.
Lemma lem3282299 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3282293 A s t x' x h1 h2) (fun h3 : False => @lem3281874 A x' x h2)). Qed.
Lemma lem3282300 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282299 A s t x' x h1 h2) (@lem3281874 A x' x h2)). Qed.
Lemma lem3282301 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3282144 A x s t x' h1 h2) (fun h3 : False => @lem3281866 A t x' h1)). Qed.
Lemma lem3282302 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282301 A x s t x' h1 h2) (@lem3281866 A t x' h1)). Qed.
Lemma lem3282303 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3282095 A x s t x' h1 h2) (fun h3 : False => @lem3281858 A s x' h1)). Qed.
Lemma lem3282304 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282303 A x s t x' h1 h2) (@lem3281858 A s x' h1)). Qed.
Lemma lem3282305 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3282294 A s t x' x h1 h2) (fun h3 : False => @lem3281850 A x' x h2)). Qed.
Lemma lem3282306 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282305 A s t x' x h1 h2) (@lem3281850 A x' x h2)). Qed.
Lemma lem3282307 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3282296 A x s t x' h1 h2) (fun h3 : False => @lem3281842 A t x' h1)). Qed.
Lemma lem3282308 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282307 A x s t x' h1 h2) (@lem3281842 A t x' h1)). Qed.
Lemma lem3282309 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3282298 A x s t x' h1 h2) (fun h3 : False => @lem3281826 A s x' h1)). Qed.
Lemma lem3282310 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282309 A x s t x' h1 h2) (@lem3281826 A s x' h1)). Qed.
Lemma lem3282311 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3282300 A s t x' x h1 h2) (fun h3 : False => @lem3281810 A x' x h2)). Qed.
Lemma lem3282312 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282311 A s t x' x h1 h2) (@lem3281810 A x' x h2)). Qed.
Lemma lem3282313 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3282302 A x s t x' h1 h2) (fun h3 : False => @lem3281794 A t x' h1)). Qed.
Lemma lem3282314 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282313 A x s t x' h1 h2) (@lem3281794 A t x' h1)). Qed.
Lemma lem3282315 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3282304 A x s t x' h1 h2) (fun h3 : False => @lem3281778 A s x' h1)). Qed.
Lemma lem3282316 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282315 A x s t x' h1 h2) (@lem3281778 A s x' h1)). Qed.
Lemma lem3282317 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3282306 A s t x' x h1 h2) (fun h3 : False => @lem3281762 A x' x h2)). Qed.
Lemma lem3282318 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282317 A s t x' x h1 h2) (@lem3281762 A x' x h2)). Qed.
Lemma lem3282319 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3282308 A x s t x' h1 h2) (fun h3 : False => @lem3281842 A t x' h1)). Qed.
Lemma lem3282320 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282319 A x s t x' h1 h2) (@lem3281842 A t x' h1)). Qed.
Lemma lem3282321 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3282310 A x s t x' h1 h2) (fun h3 : False => @lem3281826 A s x' h1)). Qed.
Lemma lem3282322 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term71 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282321 A x s t x' h1 h2) (@lem3281826 A s x' h1)). Qed.
Lemma lem3282323 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3282312 A s t x' x h1 h2) (fun h3 : False => @lem3281810 A x' x h2)). Qed.
Lemma lem3282324 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term71 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282323 A s t x' x h1 h2) (@lem3281810 A x' x h2)). Qed.
Lemma lem3282325 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : (t x') = False.
Proof. exact (prop_ext (fun h3 : t x' => @lem3282314 A x s t x' h1 h2) (fun h3 : False => @lem3281794 A t x' h1)). Qed.
Lemma lem3282326 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282325 A x s t x' h1 h2) (@lem3281794 A t x' h1)). Qed.
Lemma lem3282327 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3282316 A x s t x' h1 h2) (fun h3 : False => @lem3281778 A s x' h1)). Qed.
Lemma lem3282328 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term74 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282327 A x s t x' h1 h2) (@lem3281778 A s x' h1)). Qed.
Lemma lem3282329 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3282318 A s t x' x h1 h2) (fun h3 : False => @lem3281762 A x' x h2)). Qed.
Lemma lem3282330 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3282329 A s t x' x h1 h2) (@lem3281762 A x' x h2)). Qed.
Lemma lem3282331 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') (h2 : term33 A s t x') : False.
Proof. exact (or_elim (@lem3281744 A s t x' h2) (fun h0 : s x' => @lem3282322 A x s t x' h0 h1) (fun h0 : t x' => @lem3282320 A x s t x' h0 h1)). Qed.
Lemma lem3282332 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term71 A x s t x') : False.
Proof. exact (or_elim (@lem3281737 A x s t x' h1) (fun h0 : x' = x => @lem3282324 A s t x' x h1 h0) (fun h0 : term33 A s t x' => @lem3282331 A x s t x' h1 h0)). Qed.
Lemma lem3282333 {A : Type'} (t : A -> Prop) (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s t x') (h2 : term23 A x s x') : False.
Proof. exact (or_elim (@lem3281733 A x s x' h2) (fun h0 : x' = x => @lem3282330 A s t x' x h1 h0) (fun h0 : s x' => @lem3282328 A x s t x' h0 h1)). Qed.
Lemma lem3282334 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s t x') : False.
Proof. exact (or_elim (@lem3281728 A x s t x' h1) (fun h0 : term23 A x s x' => @lem3282333 A t x s x' h1 h0) (fun h0 : t x' => @lem3282326 A x s t x' h0 h1)). Qed.
Lemma lem3282335 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term53 A x s t x') : False.
Proof. exact (or_elim (@lem3281724 A x s t x' h1) (fun h0 : term74 A x s t x' => @lem3282334 A x s t x' h0) (fun h0 : term71 A x s t x' => @lem3282332 A x s t x' h0)). Qed.
Lemma lem3282336 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term53 A x s t x') : (term53 A x s t x') = False.
Proof. exact (prop_ext (fun h2 : term53 A x s t x' => @lem3282335 A x s t x' h1) (fun h2 : False => @lem3281574 A x s t x' h1)). Qed.
Lemma lem3282337 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term53 A x s t x') : False.
Proof. exact (EQ_MP (@lem3282336 A x s t x' h1) (@lem3281574 A x s t x' h1)). Qed.
Lemma lem3282338 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : term52 A x s t x'.
Proof. exact (fun h0 : term53 A x s t x' => @lem3282337 A x s t x' h0). Qed.
Lemma lem3282339 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term26 A x s t x') = (term34 A x s t x').
Proof. exact (EQ_MP (@lem3281573 A x s t x') (@lem3282338 A x s t x')). Qed.
Lemma lem3282344 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term37 A x s t.
Proof. exact (fun x' : A => @lem3282339 A x s t x'). Qed.
Lemma lem3282349 {A : Type'} (x : A) (s : A -> Prop) : term39 A x s.
Proof. exact (fun t : A -> Prop => @lem3282344 A x s t). Qed.
Lemma lem3282354 {A : Type'} (x : A) : term41 A x.
Proof. exact (fun s : A -> Prop => @lem3282349 A x s). Qed.
Lemma lem3282359 {A : Type'} : term43 A.
Proof. exact (fun x : A => @lem3282354 A x). Qed.
Lemma lem3282360 {A : Type'} : term45 A.
Proof. exact (EQ_MP (@lem3281569 A) (@lem3282359 A)). Qed.
Lemma lem3282362 {A : Type'} : term45 A.
Proof. exact (@lem3281465 A (@lem3282360 A)). Qed.
Lemma lem3282363 {A : Type'} (h1 : term46 A) : False.
Proof. exact (@lem3282362 A (@lem3281449 A h1)). Qed.
Lemma lem3282364 {A : Type'} (h1 : term46 A) : (term46 A) = False.
Proof. exact (prop_ext (fun h2 : term46 A => @lem3282363 A h1) (fun h2 : False => @lem3281449 A h1)). Qed.
Lemma lem3282365 {A : Type'} (h1 : term46 A) : False.
Proof. exact (EQ_MP (@lem3282364 A h1) (@lem3281449 A h1)). Qed.
Lemma lem3282366 {A : Type'} : term45 A.
Proof. exact (fun h0 : term46 A => @lem3282365 A h0). Qed.
Lemma lem3282367 {A : Type'} : term43 A.
Proof. exact (EQ_MP (@lem3281448 A) (@lem3282366 A)). Qed.
Lemma lem3282368 {A : Type'} : term15 A.
Proof. exact (EQ_MP (@lem3281444 A) (@lem3282367 A)). Qed.
Lemma lem3282369 {A : Type'} : term14 A.
Proof. exact (EQ_MP (@lem3281326 A) (@lem3282368 A)). Qed.
