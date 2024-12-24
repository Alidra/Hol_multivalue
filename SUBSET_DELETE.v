Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUBSET_DELETE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Lemma lem3309299 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3309300 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3309299 A s t). Qed.
Lemma lem3309301 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term1 A s t x) = (term2 A s t x).
Proof. exact (@lem3309300 A s (@DELETE A t x)). Qed.
Lemma lem3309308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3309309 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term3 A s t x) = (term4 A s t x).
Proof. exact (MK_COMB (@lem3309308) (@lem3309301 A s t x)). Qed.
Lemma lem3309313 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3309314 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term0 A s t).
Proof. exact (@lem3309313 A s t). Qed.
Lemma lem3309321 {A : Type'} (x : A) (s : A -> Prop) : (term5 A x s) = (term5 A x s).
Proof. exact (eq_refl (term5 A x s)). Qed.
Lemma lem3309322 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term6 A x s t) = (term7 A x s t).
Proof. exact (MK_COMB (@lem3309321 A x s) (@lem3309314 A s t)). Qed.
Lemma lem3309325 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term1 A s t x) = (term6 A x s t)) = ((term2 A s t x) = (term7 A x s t)).
Proof. exact (MK_COMB (@lem3309309 A s t x) (@lem3309322 A x s t)). Qed.
Lemma lem3309330 {A : Type'} (x : A) (s : A -> Prop) : (term8 A x s) = (term9 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3309325 A x s t)). Qed.
Lemma lem3309331 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309332 {A : Type'} (x : A) (s : A -> Prop) : (term10 A x s) = (term11 A x s).
Proof. exact (MK_COMB (@lem3309331 A) (@lem3309330 A x s)). Qed.
Lemma lem3309337 {A : Type'} (x : A) : (term12 A x) = (term13 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3309332 A x s)). Qed.
Lemma lem3309338 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309339 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (MK_COMB (@lem3309338 A) (@lem3309337 A x)). Qed.
Lemma lem3309344 {A : Type'} : (term16 A) = (term17 A).
Proof. exact (fun_ext (fun x : A => @lem3309339 A x)). Qed.
Lemma lem3309345 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309346 {A : Type'} : (term18 A) = (term19 A).
Proof. exact (MK_COMB (@lem3309345 A) (@lem3309344 A)). Qed.
Lemma lem3309351 {A : Type'} : (term19 A) = (term18 A).
Proof. exact (SYM (@lem3309346 A)). Qed.
Lemma lem3309373 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3309374 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3309373 A P x). Qed.
Lemma lem3309375 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3309374 A s x'). Qed.
Lemma lem3309376 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3309377 {A : Type'} (s : A -> Prop) (x' : A) : (term20 A x' s) = (term21 A s x').
Proof. exact (MK_COMB (@lem3309376) (@lem3309375 A s x')). Qed.
Lemma lem3309379 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term22 A x s y) = (term23 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3309380 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term22 A x s y) = (term23 A s x y).
Proof. exact (@lem3309379 A s x y). Qed.
Lemma lem3309381 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term22 A x' t x) = (term23 A t x' x).
Proof. exact (@lem3309380 A t x' x). Qed.
Lemma lem3309385 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3309386 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3309385 A P x). Qed.
Lemma lem3309387 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3309386 A t x'). Qed.
Lemma lem3309388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3309389 {A : Type'} (t : A -> Prop) (x' : A) : (term24 A x' t) = (term25 A t x').
Proof. exact (MK_COMB (@lem3309388) (@lem3309387 A t x')). Qed.
Lemma lem3309392 {A : Type'} (x' : A) (x : A) : (term26 A x' x) = (term26 A x' x).
Proof. exact (eq_refl (term26 A x' x)). Qed.
Lemma lem3309393 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term23 A t x' x) = (term27 A t x' x).
Proof. exact (MK_COMB (@lem3309389 A t x') (@lem3309392 A x' x)). Qed.
Lemma lem3309396 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term22 A x' t x) = (term27 A t x' x).
Proof. exact (TRANS (@lem3309381 A t x' x) (@lem3309393 A t x' x)). Qed.
Lemma lem3309397 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term28 A s x' t x) = (term29 A s t x' x).
Proof. exact (MK_COMB (@lem3309377 A s x') (@lem3309396 A t x' x)). Qed.
Lemma lem3309400 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term30 A s t x) = (term31 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3309397 A s t x' x)). Qed.
Lemma lem3309401 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309402 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term2 A s t x) = (term32 A s t x).
Proof. exact (MK_COMB (@lem3309401 A) (@lem3309400 A s t x)). Qed.
Lemma lem3309407 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3309408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term4 A s t x) = (term33 A s t x).
Proof. exact (MK_COMB (@lem3309407) (@lem3309402 A s t x)). Qed.
Lemma lem3309412 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3309413 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3309412 A P x). Qed.
Lemma lem3309414 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3309413 A s x). Qed.
Lemma lem3309415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3309416 {A : Type'} (s : A -> Prop) (x : A) : (term34 A x s) = (term35 A s x).
Proof. exact (MK_COMB (@lem3309415) (@lem3309414 A s x)). Qed.
Lemma lem3309417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3309418 {A : Type'} (s : A -> Prop) (x : A) : (term5 A x s) = (term36 A s x).
Proof. exact (MK_COMB (@lem3309417) (@lem3309416 A s x)). Qed.
Lemma lem3309426 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3309427 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3309426 A P x). Qed.
Lemma lem3309428 {A : Type'} (s : A -> Prop) (x : A) : (@IN A x s) = (s x).
Proof. exact (@lem3309427 A s x). Qed.
Lemma lem3309429 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3309430 {A : Type'} (s : A -> Prop) (x : A) : (term20 A x s) = (term21 A s x).
Proof. exact (MK_COMB (@lem3309429) (@lem3309428 A s x)). Qed.
Lemma lem3309432 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3309433 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3309432 A P x). Qed.
Lemma lem3309434 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3309433 A t x). Qed.
Lemma lem3309435 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term37 A s x t) = (term38 A s t x).
Proof. exact (MK_COMB (@lem3309430 A s x) (@lem3309434 A t x)). Qed.
Lemma lem3309438 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term39 A s t) = (term40 A s t).
Proof. exact (fun_ext (fun x : A => @lem3309435 A s t x)). Qed.
Lemma lem3309439 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309440 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term0 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3309439 A) (@lem3309438 A s t)). Qed.
Lemma lem3309445 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term7 A x s t) = (term42 A x s t).
Proof. exact (MK_COMB (@lem3309418 A s x) (@lem3309440 A s t)). Qed.
Lemma lem3309448 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term2 A s t x) = (term7 A x s t)) = ((term32 A s t x) = (term42 A x s t)).
Proof. exact (MK_COMB (@lem3309408 A s t x) (@lem3309445 A x s t)). Qed.
Lemma lem3309451 {A : Type'} (x : A) (s : A -> Prop) : (term9 A x s) = (term43 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3309448 A x s t)). Qed.
Lemma lem3309452 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309453 {A : Type'} (x : A) (s : A -> Prop) : (term11 A x s) = (term44 A x s).
Proof. exact (MK_COMB (@lem3309452 A) (@lem3309451 A x s)). Qed.
Lemma lem3309458 {A : Type'} (x : A) : (term13 A x) = (term45 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3309453 A x s)). Qed.
Lemma lem3309459 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309460 {A : Type'} (x : A) : (term15 A x) = (term46 A x).
Proof. exact (MK_COMB (@lem3309459 A) (@lem3309458 A x)). Qed.
Lemma lem3309465 {A : Type'} : (term17 A) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem3309460 A x)). Qed.
Lemma lem3309466 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309467 {A : Type'} : (term19 A) = (term48 A).
Proof. exact (MK_COMB (@lem3309466 A) (@lem3309465 A)). Qed.
Lemma lem3309472 {A : Type'} : (term48 A) = (term19 A).
Proof. exact (SYM (@lem3309467 A)). Qed.
Lemma lem3309474 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3309475 {A : Type'} : (term48 A) = (term50 A).
Proof. exact (@lem3309474 (term48 A)). Qed.
Lemma lem3309476 {A : Type'} : (term50 A) = (term48 A).
Proof. exact (SYM (@lem3309475 A)). Qed.
Lemma lem3309477 {A : Type'} (h1 : term51 A) : term51 A.
Proof. exact (h1). Qed.
Lemma lem3309480 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (h1). Qed.
Lemma lem3309481 {A : Type'} : term52 A.
Proof. exact (fun h0 : term50 A => @lem3309480 A h0). Qed.
Lemma lem3309482 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (h1). Qed.
Lemma lem3309483 {A : Type'} (h1 : term50 A) : term50 A.
Proof. exact (h1). Qed.
Lemma lem3309484 {A : Type'} (h1 : term50 A) (h2 : term52 A) : term50 A.
Proof. exact (@lem3309482 A h2 (@lem3309483 A h1)). Qed.
Lemma lem3309485 {A : Type'} (h1 : term50 A) : term53 A.
Proof. exact (fun h0 : term52 A => @lem3309484 A h1 h0). Qed.
Lemma lem3309486 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (h1). Qed.
Lemma lem3309487 {A : Type'} (h1 : term50 A) (h2 : term52 A) : term50 A.
Proof. exact (@lem3309485 A h1 (@lem3309486 A h2)). Qed.
Lemma lem3309488 {A : Type'} (h1 : term52 A) : term52 A.
Proof. exact (fun h0 : term50 A => @lem3309487 A h0 h1). Qed.
Lemma lem3309489 {A : Type'} : term54 A.
Proof. exact (fun h0 : term52 A => @lem3309488 A h0). Qed.
Lemma lem3309492 {A : Type'} : term52 A.
Proof. exact (@lem3309489 A (@lem3309481 A)). Qed.
Lemma lem3309493 {A : Type'} : term52 A.
Proof. exact (@lem3309492 A). Qed.
Lemma lem3309495 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3309496 {A : Type'} : (term50 A) = (term55 A).
Proof. exact (@lem3309495 (term51 A)). Qed.
Lemma lem3309498 (t : Prop) : (term56 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3309499 {A : Type'} : (term55 A) = (term48 A).
Proof. exact (@lem3309498 (term48 A)). Qed.
Lemma lem3309532 {A : Type'} : (term50 A) = (term48 A).
Proof. exact (TRANS (@lem3309496 A) (@lem3309499 A)). Qed.
Lemma lem3309537 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term38 A s t x) = (term38 A s t x).
Proof. exact (eq_refl (term38 A s t x)). Qed.
Lemma lem3309538 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term40 A s t).
Proof. exact (fun_ext (fun x : A => @lem3309537 A s t x)). Qed.
Lemma lem3309539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309540 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term41 A s t).
Proof. exact (MK_COMB (@lem3309539 A) (@lem3309538 A s t)). Qed.
Lemma lem3309545 {A : Type'} (s : A -> Prop) (x : A) : (term36 A s x) = (term36 A s x).
Proof. exact (eq_refl (term36 A s x)). Qed.
Lemma lem3309546 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term42 A x s t) = (term42 A x s t).
Proof. exact (MK_COMB (@lem3309545 A s x) (@lem3309540 A s t)). Qed.
Lemma lem3309557 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term29 A s t x' x) = (term29 A s t x' x).
Proof. exact (eq_refl (term29 A s t x' x)). Qed.
Lemma lem3309558 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s t x) = (term31 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3309557 A s t x' x)). Qed.
Lemma lem3309559 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309560 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A s t x) = (term32 A s t x).
Proof. exact (MK_COMB (@lem3309559 A) (@lem3309558 A s t x)). Qed.
Lemma lem3309561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3309562 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term33 A s t x) = (term33 A s t x).
Proof. exact (MK_COMB (@lem3309561) (@lem3309560 A s t x)). Qed.
Lemma lem3309563 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term32 A s t x) = (term42 A x s t)) = ((term32 A s t x) = (term42 A x s t)).
Proof. exact (MK_COMB (@lem3309562 A s t x) (@lem3309546 A x s t)). Qed.
Lemma lem3309564 {A : Type'} (x : A) (s : A -> Prop) : (term43 A x s) = (term43 A x s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3309563 A x s t)). Qed.
Lemma lem3309565 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309566 {A : Type'} (x : A) (s : A -> Prop) : (term44 A x s) = (term44 A x s).
Proof. exact (MK_COMB (@lem3309565 A) (@lem3309564 A x s)). Qed.
Lemma lem3309567 {A : Type'} (x : A) : (term45 A x) = (term45 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3309566 A x s)). Qed.
Lemma lem3309568 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3309569 {A : Type'} (x : A) : (term46 A x) = (term46 A x).
Proof. exact (MK_COMB (@lem3309568 A) (@lem3309567 A x)). Qed.
Lemma lem3309570 {A : Type'} : (term47 A) = (term47 A).
Proof. exact (fun_ext (fun x : A => @lem3309569 A x)). Qed.
Lemma lem3309571 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309572 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (MK_COMB (@lem3309571 A) (@lem3309570 A)). Qed.
Lemma lem3309613 {A : Type'} : (term50 A) = (term48 A).
Proof. exact (TRANS (@lem3309532 A) (@lem3309572 A)). Qed.
Lemma lem3309614 {A : Type'} : (term48 A) = (term50 A).
Proof. exact (SYM (@lem3309613 A)). Qed.
Lemma lem3309616 (p : Prop) : p = (term49 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3309617 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term32 A s t x) = (term42 A x s t)) = (term57 A x s t).
Proof. exact (@lem3309616 ((term32 A s t x) = (term42 A x s t))). Qed.
Lemma lem3309618 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term57 A x s t) = ((term32 A s t x) = (term42 A x s t)).
Proof. exact (SYM (@lem3309617 A x s t)). Qed.
Lemma lem3309619 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term58 A x s t) : term58 A x s t.
Proof. exact (h1). Qed.
Lemma lem3309627 {A : Type'} (x' : A) (x : A) : (term59 A x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3309629 {A : Type'} (t : A -> Prop) (x' : A) : (term60 A t x') = (term60 A t x').
Proof. exact (eq_refl (term60 A t x')). Qed.
Lemma lem3309630 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term61 A t x' x) = (term62 A t x' x).
Proof. exact (MK_COMB (@lem3309629 A t x') (@lem3309627 A x' x)). Qed.
Lemma lem3309631 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term63 A t x' x) = (term61 A t x' x).
Proof. exact (@lem17045 (t x') (term26 A x' x)). Qed.
Lemma lem3309632 {A : Type'} (t : A -> Prop) (x' : A) (x : A) : (term63 A t x' x) = (term62 A t x' x).
Proof. exact (TRANS (@lem3309631 A t x' x) (@lem3309630 A t x' x)). Qed.
Lemma lem3309637 {A : Type'} (s : A -> Prop) (x' : A) : (term25 A s x') = (term25 A s x').
Proof. exact (eq_refl (term25 A s x')). Qed.
Lemma lem3309638 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term64 A s t x' x) = (term65 A s t x' x).
Proof. exact (MK_COMB (@lem3309637 A s x') (@lem3309632 A t x' x)). Qed.
Lemma lem3309639 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term66 A s t x' x) = (term64 A s t x' x).
Proof. exact (@lem17362 (s x') (term27 A t x' x)). Qed.
Lemma lem3309640 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term66 A s t x' x) = (term65 A s t x' x).
Proof. exact (TRANS (@lem3309639 A s t x' x) (@lem3309638 A s t x' x)). Qed.
Lemma lem3309645 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term29 A s t x' x) = (term67 A s t x' x).
Proof. exact (@lem17265 (s x') (term27 A t x' x)). Qed.
Lemma lem3309646 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3309647 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term71 A s t x).
Proof. exact (@lem3309646 A (term31 A s t x)). Qed.
Lemma lem3309648 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term72 A s t x x') = (term29 A s t x' x).
Proof. exact (eq_refl (term72 A s t x x')). Qed.
Lemma lem3309649 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3309650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term73 A s t x x') = (term66 A s t x' x).
Proof. exact (MK_COMB (@lem3309649) (@lem3309648 A s t x' x)). Qed.
Lemma lem3309651 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term73 A s t x x') = (term65 A s t x' x).
Proof. exact (TRANS (@lem3309650 A s t x' x) (@lem3309640 A s t x' x)). Qed.
Lemma lem3309652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term74 A s t x) = (term75 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3309651 A s t x' x)). Qed.
Lemma lem3309653 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309654 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term71 A s t x) = (term76 A s t x).
Proof. exact (MK_COMB (@lem3309653 A) (@lem3309652 A s t x)). Qed.
Lemma lem3309655 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term70 A s t x) = (term76 A s t x).
Proof. exact (TRANS (@lem3309647 A s t x) (@lem3309654 A s t x)). Qed.
Lemma lem3309656 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term31 A s t x) = (term77 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3309645 A s t x' x)). Qed.
Lemma lem3309657 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309658 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term32 A s t x) = (term78 A s t x).
Proof. exact (MK_COMB (@lem3309657 A) (@lem3309656 A s t x)). Qed.
Lemma lem3309662 {A : Type'} (s : A -> Prop) (x : A) : (term79 A s x) = (s x).
Proof. exact (@lem16933 (s x)). Qed.
Lemma lem3309671 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term80 A s t x) = (term81 A s t x).
Proof. exact (@lem17362 (s x) (t x)). Qed.
Lemma lem3309676 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term38 A s t x) = (term82 A s t x).
Proof. exact (@lem17265 (s x) (t x)). Qed.
Lemma lem3309677 {A : Type'} (P : A -> Prop) : (term68 A P) = (term69 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem3309678 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term84 A s t).
Proof. exact (@lem3309677 A (term40 A s t)). Qed.
Lemma lem3309679 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term85 A s t x) = (term38 A s t x).
Proof. exact (eq_refl (term85 A s t x)). Qed.
Lemma lem3309680 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3309681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term80 A s t x).
Proof. exact (MK_COMB (@lem3309680) (@lem3309679 A s t x)). Qed.
Lemma lem3309682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term86 A s t x) = (term81 A s t x).
Proof. exact (TRANS (@lem3309681 A s t x) (@lem3309671 A s t x)). Qed.
Lemma lem3309683 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term87 A s t) = (term88 A s t).
Proof. exact (fun_ext (fun x : A => @lem3309682 A s t x)). Qed.
Lemma lem3309684 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309685 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term84 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem3309684 A) (@lem3309683 A s t)). Qed.
Lemma lem3309686 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term83 A s t) = (term89 A s t).
Proof. exact (TRANS (@lem3309678 A s t) (@lem3309685 A s t)). Qed.
Lemma lem3309687 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term40 A s t) = (term90 A s t).
Proof. exact (fun_ext (fun x : A => @lem3309676 A s t x)). Qed.
Lemma lem3309688 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309689 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term41 A s t) = (term91 A s t).
Proof. exact (MK_COMB (@lem3309688 A) (@lem3309687 A s t)). Qed.
Lemma lem3309690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3309691 {A : Type'} (s : A -> Prop) (x : A) : (term92 A s x) = (term93 A s x).
Proof. exact (MK_COMB (@lem3309690) (@lem3309662 A s x)). Qed.
Lemma lem3309692 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term94 A x s t) = (term95 A x s t).
Proof. exact (MK_COMB (@lem3309691 A s x) (@lem3309686 A s t)). Qed.
Lemma lem3309693 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term96 A x s t) = (term94 A x s t).
Proof. exact (@lem17045 (term35 A s x) (term41 A s t)). Qed.
Lemma lem3309694 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term96 A x s t) = (term95 A x s t).
Proof. exact (TRANS (@lem3309693 A x s t) (@lem3309692 A x s t)). Qed.
Lemma lem3309696 {A : Type'} (s : A -> Prop) (x : A) : (term36 A s x) = (term36 A s x).
Proof. exact (eq_refl (term36 A s x)). Qed.
Lemma lem3309697 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term42 A x s t) = (term97 A x s t).
Proof. exact (MK_COMB (@lem3309696 A s x) (@lem3309689 A s t)). Qed.
Lemma lem3309698 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3309699 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term98 A s t x) = (term99 A s t x).
Proof. exact (MK_COMB (@lem3309698) (@lem3309655 A s t x)). Qed.
Lemma lem3309700 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term100 A x s t) = (term101 A x s t).
Proof. exact (MK_COMB (@lem3309699 A s t x) (@lem3309697 A x s t)). Qed.
Lemma lem3309701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3309702 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term102 A s t x) = (term103 A s t x).
Proof. exact (MK_COMB (@lem3309701) (@lem3309658 A s t x)). Qed.
Lemma lem3309703 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term104 A x s t) = (term105 A x s t).
Proof. exact (MK_COMB (@lem3309702 A s t x) (@lem3309694 A x s t)). Qed.
Lemma lem3309704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3309705 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term106 A x s t) = (term107 A x s t).
Proof. exact (MK_COMB (@lem3309704) (@lem3309703 A x s t)). Qed.
Lemma lem3309706 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term108 A x s t) = (term109 A x s t).
Proof. exact (MK_COMB (@lem3309705 A x s t) (@lem3309700 A x s t)). Qed.
Lemma lem3309707 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term58 A x s t) = (term108 A x s t).
Proof. exact (@lem17646 (term32 A s t x) (term42 A x s t)). Qed.
Lemma lem3309708 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term58 A x s t) = (term109 A x s t).
Proof. exact (TRANS (@lem3309707 A x s t) (@lem3309706 A x s t)). Qed.
Lemma lem3309847 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3309848 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (@lem3309847 A P Q). Qed.
Lemma lem3309849 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term113 A x s t).
Proof. exact (@lem3309848 A (s x) (term88 A s t)). Qed.
Lemma lem3309850 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term114 A s t x) = (term81 A s t x).
Proof. exact (eq_refl (term114 A s t x)). Qed.
Lemma lem3309851 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term115 A s t) = (term88 A s t).
Proof. exact (fun_ext (fun x : A => @lem3309850 A s t x)). Qed.
Lemma lem3309852 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309853 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term116 A s t) = (term89 A s t).
Proof. exact (MK_COMB (@lem3309852 A) (@lem3309851 A s t)). Qed.
Lemma lem3309854 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term93 A s x).
Proof. exact (eq_refl (term93 A s x)). Qed.
Lemma lem3309855 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term112 A x s t) = (term95 A x s t).
Proof. exact (MK_COMB (@lem3309854 A s x) (@lem3309853 A s t)). Qed.
Lemma lem3309856 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3309857 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term117 A x s t) = (term118 A x s t).
Proof. exact (MK_COMB (@lem3309856) (@lem3309855 A x s t)). Qed.
Lemma lem3309858 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term114 A s t x') = (term81 A s t x').
Proof. exact (eq_refl (term114 A s t x')). Qed.
Lemma lem3309859 {A : Type'} (s : A -> Prop) (x : A) : (term93 A s x) = (term93 A s x).
Proof. exact (eq_refl (term93 A s x)). Qed.
Lemma lem3309860 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term119 A x s t x') = (term120 A x s t x').
Proof. exact (MK_COMB (@lem3309859 A s x) (@lem3309858 A s t x')). Qed.
Lemma lem3309861 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term121 A x s t) = (term122 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3309860 A x s t x')). Qed.
Lemma lem3309862 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309863 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term113 A x s t) = (term123 A x s t).
Proof. exact (MK_COMB (@lem3309862 A) (@lem3309861 A x s t)). Qed.
Lemma lem3309864 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term112 A x s t) = (term113 A x s t)) = ((term95 A x s t) = (term123 A x s t)).
Proof. exact (MK_COMB (@lem3309857 A x s t) (@lem3309863 A x s t)). Qed.
Lemma lem3309865 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term95 A x s t) = (term123 A x s t).
Proof. exact (EQ_MP (@lem3309864 A x s t) (@lem3309849 A x s t)). Qed.
Lemma lem3309866 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term103 A s t x).
Proof. exact (eq_refl (term103 A s t x)). Qed.
Lemma lem3309867 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term105 A x s t) = (term124 A x s t).
Proof. exact (MK_COMB (@lem3309866 A s t x) (@lem3309865 A x s t)). Qed.
Lemma lem3309869 {A : Type'} (P : Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3309870 {A : Type'} (P : Prop) (Q : A -> Prop) : (term125 A P Q) = (term126 A P Q).
Proof. exact (@lem3309869 A P Q). Qed.
Lemma lem3309871 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term127 A x s t) = (term128 A x s t).
Proof. exact (@lem3309870 A (term78 A s t x) (term122 A x s t)). Qed.
Lemma lem3309872 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term129 A x s t x') = (term120 A x s t x').
Proof. exact (eq_refl (term129 A x s t x')). Qed.
Lemma lem3309873 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term130 A x s t) = (term122 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3309872 A x s t x')). Qed.
Lemma lem3309874 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309875 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term131 A x s t) = (term123 A x s t).
Proof. exact (MK_COMB (@lem3309874 A) (@lem3309873 A x s t)). Qed.
Lemma lem3309876 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term103 A s t x).
Proof. exact (eq_refl (term103 A s t x)). Qed.
Lemma lem3309877 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term127 A x s t) = (term124 A x s t).
Proof. exact (MK_COMB (@lem3309876 A s t x) (@lem3309875 A x s t)). Qed.
Lemma lem3309878 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3309879 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term132 A x s t) = (term133 A x s t).
Proof. exact (MK_COMB (@lem3309878) (@lem3309877 A x s t)). Qed.
Lemma lem3309880 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term129 A x s t x') = (term120 A x s t x').
Proof. exact (eq_refl (term129 A x s t x')). Qed.
Lemma lem3309881 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term103 A s t x).
Proof. exact (eq_refl (term103 A s t x)). Qed.
Lemma lem3309882 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term134 A x s t x') = (term135 A x s t x').
Proof. exact (MK_COMB (@lem3309881 A s t x) (@lem3309880 A x s t x')). Qed.
Lemma lem3309883 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term136 A x s t) = (term137 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3309882 A x s t x')). Qed.
Lemma lem3309884 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309885 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term128 A x s t) = (term138 A x s t).
Proof. exact (MK_COMB (@lem3309884 A) (@lem3309883 A x s t)). Qed.
Lemma lem3309886 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term127 A x s t) = (term128 A x s t)) = ((term124 A x s t) = (term138 A x s t)).
Proof. exact (MK_COMB (@lem3309879 A x s t) (@lem3309885 A x s t)). Qed.
Lemma lem3309887 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term124 A x s t) = (term138 A x s t).
Proof. exact (EQ_MP (@lem3309886 A x s t) (@lem3309871 A x s t)). Qed.
Lemma lem3309888 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term105 A x s t) = (term138 A x s t).
Proof. exact (TRANS (@lem3309867 A x s t) (@lem3309887 A x s t)). Qed.
Lemma lem3309889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3309890 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term107 A x s t) = (term139 A x s t).
Proof. exact (MK_COMB (@lem3309889) (@lem3309888 A x s t)). Qed.
Lemma lem3309892 {A : Type'} (P : A -> Prop) (Q : Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3309893 {A : Type'} (P : A -> Prop) (Q : Prop) : (term140 A P Q) = (term141 A P Q).
Proof. exact (@lem3309892 A P Q). Qed.
Lemma lem3309894 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term142 A x s t) = (term143 A x s t).
Proof. exact (@lem3309893 A (term75 A s t x) (term97 A x s t)). Qed.
Lemma lem3309895 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term144 A s t x x') = (term65 A s t x' x).
Proof. exact (eq_refl (term144 A s t x x')). Qed.
Lemma lem3309896 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term145 A s t x) = (term75 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3309895 A s t x' x)). Qed.
Lemma lem3309897 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309898 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term146 A s t x) = (term76 A s t x).
Proof. exact (MK_COMB (@lem3309897 A) (@lem3309896 A s t x)). Qed.
Lemma lem3309899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3309900 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term147 A s t x) = (term99 A s t x).
Proof. exact (MK_COMB (@lem3309899) (@lem3309898 A s t x)). Qed.
Lemma lem3309901 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term97 A x s t) = (term97 A x s t).
Proof. exact (eq_refl (term97 A x s t)). Qed.
Lemma lem3309902 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term142 A x s t) = (term101 A x s t).
Proof. exact (MK_COMB (@lem3309900 A s t x) (@lem3309901 A x s t)). Qed.
Lemma lem3309903 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3309904 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term148 A x s t) = (term149 A x s t).
Proof. exact (MK_COMB (@lem3309903) (@lem3309902 A x s t)). Qed.
Lemma lem3309905 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term144 A s t x x') = (term65 A s t x' x).
Proof. exact (eq_refl (term144 A s t x x')). Qed.
Lemma lem3309906 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3309907 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term150 A s t x x') = (term151 A s t x' x).
Proof. exact (MK_COMB (@lem3309906) (@lem3309905 A s t x' x)). Qed.
Lemma lem3309908 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term97 A x s t) = (term97 A x s t).
Proof. exact (eq_refl (term97 A x s t)). Qed.
Lemma lem3309909 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term152 A x' x s t) = (term153 A x' x s t).
Proof. exact (MK_COMB (@lem3309907 A s t x' x) (@lem3309908 A x s t)). Qed.
Lemma lem3309910 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term154 A x s t) = (term155 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3309909 A x' x s t)). Qed.
Lemma lem3309911 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309912 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term143 A x s t) = (term156 A x s t).
Proof. exact (MK_COMB (@lem3309911 A) (@lem3309910 A x s t)). Qed.
Lemma lem3309913 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term142 A x s t) = (term143 A x s t)) = ((term101 A x s t) = (term156 A x s t)).
Proof. exact (MK_COMB (@lem3309904 A x s t) (@lem3309912 A x s t)). Qed.
Lemma lem3309914 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term101 A x s t) = (term156 A x s t).
Proof. exact (EQ_MP (@lem3309913 A x s t) (@lem3309894 A x s t)). Qed.
Lemma lem3309915 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term109 A x s t) = (term157 A x s t).
Proof. exact (MK_COMB (@lem3309890 A x s t) (@lem3309914 A x s t)). Qed.
Lemma lem3309917 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term158 A P Q) = (term159 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3309918 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term158 A P Q) = (term159 A P Q).
Proof. exact (@lem3309917 A P Q). Qed.
Lemma lem3309919 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term160 A x s t) = (term161 A x s t).
Proof. exact (@lem3309918 A (term137 A x s t) (term155 A x s t)). Qed.
Lemma lem3309920 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term162 A x s t x') = (term135 A x s t x').
Proof. exact (eq_refl (term162 A x s t x')). Qed.
Lemma lem3309921 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term163 A x s t) = (term137 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3309920 A x s t x')). Qed.
Lemma lem3309922 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309923 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term164 A x s t) = (term138 A x s t).
Proof. exact (MK_COMB (@lem3309922 A) (@lem3309921 A x s t)). Qed.
Lemma lem3309924 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3309925 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term165 A x s t) = (term139 A x s t).
Proof. exact (MK_COMB (@lem3309924) (@lem3309923 A x s t)). Qed.
Lemma lem3309926 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term166 A x s t x') = (term153 A x' x s t).
Proof. exact (eq_refl (term166 A x s t x')). Qed.
Lemma lem3309927 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term167 A x s t) = (term155 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3309926 A x' x s t)). Qed.
Lemma lem3309928 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309929 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term168 A x s t) = (term156 A x s t).
Proof. exact (MK_COMB (@lem3309928 A) (@lem3309927 A x s t)). Qed.
Lemma lem3309930 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term160 A x s t) = (term157 A x s t).
Proof. exact (MK_COMB (@lem3309925 A x s t) (@lem3309929 A x s t)). Qed.
Lemma lem3309931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3309932 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term169 A x s t) = (term170 A x s t).
Proof. exact (MK_COMB (@lem3309931) (@lem3309930 A x s t)). Qed.
Lemma lem3309933 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term162 A x s t x') = (term135 A x s t x').
Proof. exact (eq_refl (term162 A x s t x')). Qed.
Lemma lem3309934 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3309935 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term171 A x s t x') = (term172 A x s t x').
Proof. exact (MK_COMB (@lem3309934) (@lem3309933 A x s t x')). Qed.
Lemma lem3309936 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term166 A x s t x') = (term153 A x' x s t).
Proof. exact (eq_refl (term166 A x s t x')). Qed.
Lemma lem3309937 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term173 A x s t x') = (term174 A x' x s t).
Proof. exact (MK_COMB (@lem3309935 A x s t x') (@lem3309936 A x' x s t)). Qed.
Lemma lem3309938 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term175 A x s t) = (term176 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3309937 A x' x s t)). Qed.
Lemma lem3309939 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3309940 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term161 A x s t) = (term177 A x s t).
Proof. exact (MK_COMB (@lem3309939 A) (@lem3309938 A x s t)). Qed.
Lemma lem3309941 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term160 A x s t) = (term161 A x s t)) = ((term157 A x s t) = (term177 A x s t)).
Proof. exact (MK_COMB (@lem3309932 A x s t) (@lem3309940 A x s t)). Qed.
Lemma lem3309942 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term157 A x s t) = (term177 A x s t).
Proof. exact (EQ_MP (@lem3309941 A x s t) (@lem3309919 A x s t)). Qed.
Lemma lem3309944 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term109 A x s t) = (term177 A x s t).
Proof. exact (TRANS (@lem3309915 A x s t) (@lem3309942 A x s t)). Qed.
Lemma lem3309945 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term58 A x s t) = (term177 A x s t).
Proof. exact (TRANS (@lem3309708 A x s t) (@lem3309944 A x s t)). Qed.
Lemma lem3309946 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term58 A x s t) : term177 A x s t.
Proof. exact (EQ_MP (@lem3309945 A x s t) (@lem3309619 A x s t h1)). Qed.
Lemma lem3309947 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term174 A x' x s t) : term174 A x' x s t.
Proof. exact (h1). Qed.
Lemma lem3309958 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term82 A s t x) = (term82 A s t x).
Proof. exact (eq_refl (term82 A s t x)). Qed.
Lemma lem3309959 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term90 A s t).
Proof. exact (fun_ext (fun x : A => @lem3309958 A s t x)). Qed.
Lemma lem3309960 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3309961 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term91 A s t).
Proof. exact (MK_COMB (@lem3309960 A) (@lem3309959 A s t)). Qed.
Lemma lem3309968 {A : Type'} (s : A -> Prop) (x : A) : (term36 A s x) = (term36 A s x).
Proof. exact (eq_refl (term36 A s x)). Qed.
Lemma lem3309969 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term97 A x s t) = (term97 A x s t).
Proof. exact (MK_COMB (@lem3309968 A s x) (@lem3309961 A s t)). Qed.
Lemma lem3309990 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term151 A s t x' x) = (term151 A s t x' x).
Proof. exact (eq_refl (term151 A s t x' x)). Qed.
Lemma lem3309991 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term153 A x' x s t) = (term153 A x' x s t).
Proof. exact (MK_COMB (@lem3309990 A s t x' x) (@lem3309969 A x s t)). Qed.
Lemma lem3310008 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term120 A x s t x') = (term120 A x s t x').
Proof. exact (eq_refl (term120 A x s t x')). Qed.
Lemma lem3310029 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) : (term67 A s t x' x) = (term67 A s t x' x).
Proof. exact (eq_refl (term67 A s t x' x)). Qed.
Lemma lem3310030 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term77 A s t x) = (term77 A s t x).
Proof. exact (fun_ext (fun x' : A => @lem3310029 A s t x' x)). Qed.
Lemma lem3310031 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310032 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term78 A s t x) = (term78 A s t x).
Proof. exact (MK_COMB (@lem3310031 A) (@lem3310030 A s t x)). Qed.
Lemma lem3310033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3310034 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term103 A s t x) = (term103 A s t x).
Proof. exact (MK_COMB (@lem3310033) (@lem3310032 A s t x)). Qed.
Lemma lem3310035 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term135 A x s t x') = (term135 A x s t x').
Proof. exact (MK_COMB (@lem3310034 A s t x) (@lem3310008 A x s t x')). Qed.
Lemma lem3310036 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3310037 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term172 A x s t x') = (term172 A x s t x').
Proof. exact (MK_COMB (@lem3310036) (@lem3310035 A x s t x')). Qed.
Lemma lem3310038 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) : (term174 A x' x s t) = (term174 A x' x s t).
Proof. exact (MK_COMB (@lem3310037 A x s t x') (@lem3309991 A x' x s t)). Qed.
Lemma lem3310039 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term174 A x' x s t) : term174 A x' x s t.
Proof. exact (EQ_MP (@lem3310038 A x' x s t) (@lem3309947 A x' x s t h1)). Qed.
Lemma lem3310040 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term135 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3310041 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term153 A x' x s t.
Proof. exact (h1). Qed.
Lemma lem3310042 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term120 A x s t x'.
Proof. exact (proj2 (@lem3310040 A x s t x' h1)). Qed.
Lemma lem3310043 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term78 A s t x.
Proof. exact (proj1 (@lem3310040 A x s t x' h1)). Qed.
Lemma lem3310045 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term81 A s t x') : term81 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3310048 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term97 A x s t.
Proof. exact (proj2 (@lem3310041 A x' x s t h1)). Qed.
Lemma lem3310049 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term65 A s t x' x.
Proof. exact (proj1 (@lem3310041 A x' x s t h1)). Qed.
Lemma lem3310050 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term91 A s t.
Proof. exact (proj2 (@lem3310048 A x' x s t h1)). Qed.
Lemma lem3310052 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term62 A t x' x.
Proof. exact (proj2 (@lem3310049 A x' x s t h1)). Qed.
Lemma lem3310073 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (x : A) : (term67 A s t x' x) = (term178 A t s x' x).
Proof. exact (@lem19490 (t x') (term35 A s x') (term26 A x' x)). Qed.
Lemma lem3310074 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term77 A s t x) = (term179 A t s x).
Proof. exact (fun_ext (fun x' : A => @lem3310073 A t s x' x)). Qed.
Lemma lem3310075 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310077 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term78 A s t x) = (term180 A t s x).
Proof. exact (MK_COMB (@lem3310075 A) (@lem3310074 A t s x)). Qed.
Lemma lem3310078 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term180 A t s x.
Proof. exact (EQ_MP (@lem3310077 A t s x) (@lem3310043 A x s t x' h1)). Qed.
Lemma lem3310082 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3310100 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x' : A) (x : A) : (term67 A s t x' x) = (term178 A t s x' x).
Proof. exact (@lem19490 (t x') (term35 A s x') (term26 A x' x)). Qed.
Lemma lem3310101 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term77 A s t x) = (term179 A t s x).
Proof. exact (fun_ext (fun x' : A => @lem3310100 A t s x' x)). Qed.
Lemma lem3310102 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310104 {A : Type'} (t : A -> Prop) (s : A -> Prop) (x : A) : (term78 A s t x) = (term180 A t s x).
Proof. exact (MK_COMB (@lem3310102 A) (@lem3310101 A t s x)). Qed.
Lemma lem3310105 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term180 A t s x.
Proof. exact (EQ_MP (@lem3310104 A t s x) (@lem3310043 A x s t x' h1)). Qed.
Lemma lem3310125 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : (term82 A s t x) = (term82 A s t x).
Proof. exact (eq_refl (term82 A s t x)). Qed.
Lemma lem3310126 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term90 A s t) = (term90 A s t).
Proof. exact (fun_ext (fun x : A => @lem3310125 A s t x)). Qed.
Lemma lem3310127 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3310129 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term91 A s t) = (term91 A s t).
Proof. exact (MK_COMB (@lem3310127 A) (@lem3310126 A s t)). Qed.
Lemma lem3310130 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term91 A s t.
Proof. exact (EQ_MP (@lem3310129 A s t) (@lem3310050 A x' x s t h1)). Qed.
Lemma lem3310138 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term35 A t x') : term35 A t x'.
Proof. exact (h1). Qed.
Lemma lem3310163 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3310164 {A : Type'} (_34114 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term181 A t s x _34114.
Proof. exact (@lem3310078 A x s t x' h1 _34114). Qed.
Lemma lem3310165 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34114 : A) (x : A) : (term181 A t s x _34114) = (term178 A t s _34114 x).
Proof. exact (eq_refl (term181 A t s x _34114)). Qed.
Lemma lem3310166 {A : Type'} (_34114 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term178 A t s _34114 x.
Proof. exact (EQ_MP (@lem3310165 A t s _34114 x) (@lem3310164 A _34114 x s t x' h1)). Qed.
Lemma lem3310167 {A : Type'} (_34115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term181 A t s x _34115.
Proof. exact (@lem3310105 A x s t x' h1 _34115). Qed.
Lemma lem3310168 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) (x : A) : (term181 A t s x _34115) = (term178 A t s _34115 x).
Proof. exact (eq_refl (term181 A t s x _34115)). Qed.
Lemma lem3310169 {A : Type'} (_34115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term178 A t s _34115 x.
Proof. exact (EQ_MP (@lem3310168 A t s _34115 x) (@lem3310167 A _34115 x s t x' h1)). Qed.
Lemma lem3310170 {A : Type'} (_34116 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term182 A s t _34116.
Proof. exact (@lem3310130 A x' x s t h1 _34116). Qed.
Lemma lem3310171 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34116 : A) : (term182 A s t _34116) = (term82 A s t _34116).
Proof. exact (eq_refl (term182 A s t _34116)). Qed.
Lemma lem3310181 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3310193 {A : Type'} (_34114 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term183 A s _34114 x.
Proof. exact (proj2 (@lem3310166 A _34114 x s t x' h1)). Qed.
Lemma lem3310197 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term81 A s t x') : term35 A t x'.
Proof. exact (proj2 (@lem3310045 A s t x' h1)). Qed.
Lemma lem3310203 {A : Type'} (_34115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term82 A s t _34115.
Proof. exact (proj1 (@lem3310169 A _34115 x s t x' h1)). Qed.
Lemma lem3310217 {A : Type'} (_34116 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term82 A s t _34116.
Proof. exact (EQ_MP (@lem3310171 A s t _34116) (@lem3310170 A _34116 x' x s t h1)). Qed.
Lemma lem3310221 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term35 A t x') : term35 A t x'.
Proof. exact (h1). Qed.
Lemma lem3310231 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : s x'.
Proof. exact (proj1 (@lem3310049 A x' x s t h1)). Qed.
Lemma lem3310233 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3310261 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term35 A s x.
Proof. exact (proj1 (@lem3310048 A x' x s t h1)). Qed.
Lemma lem3310276 {A : Type'} (s : A -> Prop) : (term184 A s) = (term184 A s).
Proof. exact (eq_refl (term184 A s)). Qed.
Lemma lem3310277 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term185 A s x') = (term185 A s x).
Proof. exact (MK_COMB (@lem3310276 A s) (@lem3310233 A x' x h1)). Qed.
Lemma lem3310278 {A : Type'} (s : A -> Prop) (x : A) : (term185 A s x) = (s x).
Proof. exact (eq_refl (term185 A s x)). Qed.
Lemma lem3310279 {A : Type'} (s : A -> Prop) (x' : A) : (term186 A s x') = (term186 A s x').
Proof. exact (eq_refl (term186 A s x')). Qed.
Lemma lem3310280 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term185 A s x') = (term185 A s x)) = ((term185 A s x') = (s x)).
Proof. exact (MK_COMB (@lem3310279 A s x') (@lem3310278 A s x)). Qed.
Lemma lem3310281 {A : Type'} (s : A -> Prop) (x' : A) : (term185 A s x') = (s x').
Proof. exact (eq_refl (term185 A s x')). Qed.
Lemma lem3310282 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3310283 {A : Type'} (s : A -> Prop) (x' : A) : (term186 A s x') = (term187 A s x').
Proof. exact (MK_COMB (@lem3310282) (@lem3310281 A s x')). Qed.
Lemma lem3310284 {A : Type'} (s : A -> Prop) (x : A) : (s x) = (s x).
Proof. exact (eq_refl (s x)). Qed.
Lemma lem3310285 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term185 A s x') = (s x)) = ((s x') = (s x)).
Proof. exact (MK_COMB (@lem3310283 A s x') (@lem3310284 A s x)). Qed.
Lemma lem3310286 {A : Type'} (x' : A) (s : A -> Prop) (x : A) : ((term185 A s x') = (term185 A s x)) = ((s x') = (s x)).
Proof. exact (TRANS (@lem3310280 A x' s x) (@lem3310285 A x' s x)). Qed.
Lemma lem3310287 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (s x') = (s x).
Proof. exact (EQ_MP (@lem3310286 A x' s x) (@lem3310277 A s x' x h1)). Qed.
Lemma lem3310316 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (h1). Qed.
Lemma lem3310317 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term188 A s x.
Proof. exact (fun h0 : term35 A s x => @lem3310316 A s x h1). Qed.
Lemma lem3310319 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310320 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (s x).
Proof. exact (@lem3310319 (s x)). Qed.
Lemma lem3310321 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : s x.
Proof. exact (EQ_MP (@lem3310320 A s x) (@lem3310317 A s x h1)). Qed.
Lemma lem3310323 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3310324 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3310323 A x). Qed.
Lemma lem3310325 {A : Type'} (x : A) : term190 A x.
Proof. exact (fun h0 : term191 A x => @lem3310324 A x). Qed.
Lemma lem3310327 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310328 {A : Type'} (x : A) : (term190 A x) = (x = x).
Proof. exact (@lem3310327 (x = x)). Qed.
Lemma lem3310329 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3310328 A x) (@lem3310325 A x)). Qed.
Lemma lem3310331 (a : Prop) (b : Prop) : (term192 a b) = (term193 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3310332 {A : Type'} (s : A -> Prop) (_34114 : A) (x : A) : (term183 A s _34114 x) = (term194 A s _34114 x).
Proof. exact (@lem3310331 (s _34114) (_34114 = x)). Qed.
Lemma lem3310334 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3310335 {A : Type'} (s : A -> Prop) (_34114 : A) (x : A) : (term194 A s _34114 x) = (term195 A s _34114 x).
Proof. exact (@lem3310334 (term196 A s _34114 x)). Qed.
Lemma lem3310336 {A : Type'} (s : A -> Prop) (_34114 : A) (x : A) : (term183 A s _34114 x) = (term195 A s _34114 x).
Proof. exact (TRANS (@lem3310332 A s _34114 x) (@lem3310335 A s _34114 x)). Qed.
Lemma lem3310338 {A : Type'} (s : A -> Prop) (x : A) (h1 : s x) : term197 A s x.
Proof. exact (conj (@lem3310321 A s x h1) (@lem3310329 A x)). Qed.
Lemma lem3310340 {A : Type'} (_34114 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term195 A s _34114 x.
Proof. exact (EQ_MP (@lem3310336 A s _34114 x) (@lem3310193 A _34114 x s t x' h1)). Qed.
Lemma lem3310341 {A : Type'} (_34114 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term195 A s _34114 x.
Proof. exact (@lem3310340 A _34114 x s t x' h1). Qed.
Lemma lem3310342 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term198 A s x.
Proof. exact (@lem3310341 A x x s t x' h1). Qed.
Lemma lem3310345 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : False.
Proof. exact (@lem3310342 A x s t x' h2 (@lem3310338 A s x h1)). Qed.
Lemma lem3310346 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : term199.
Proof. exact (fun h0 : ~ False => @lem3310345 A x s t x' h1 h2). Qed.
Lemma lem3310348 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310349 : term199 = False.
Proof. exact (@lem3310348 False). Qed.
Lemma lem3310350 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : False.
Proof. exact (EQ_MP (@lem3310349) (@lem3310346 A x s t x' h1 h2)). Qed.
Lemma lem3310378 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term81 A s t x') : s x'.
Proof. exact (proj1 (@lem3310045 A s t x' h1)). Qed.
Lemma lem3310379 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term81 A s t x') : term188 A s x'.
Proof. exact (fun h0 : term35 A s x' => @lem3310378 A s t x' h1). Qed.
Lemma lem3310381 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310382 {A : Type'} (s : A -> Prop) (x' : A) : (term188 A s x') = (s x').
Proof. exact (@lem3310381 (s x')). Qed.
Lemma lem3310383 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term81 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3310382 A s x') (@lem3310379 A s t x' h1)). Qed.
Lemma lem3310389 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3310390 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : (term82 A s t _34115) = (term200 A t s _34115).
Proof. exact (@lem3310389 (t _34115) (term35 A s _34115)). Qed.
Lemma lem3310396 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3310397 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : (term201 A s t _34115) = (term202 A t s _34115).
Proof. exact (MK_COMB (@lem3310396) (@lem3310390 A t s _34115)). Qed.
Lemma lem3310403 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : (term200 A t s _34115) = (term200 A t s _34115).
Proof. exact (eq_refl (term200 A t s _34115)). Qed.
Lemma lem3310404 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : ((term82 A s t _34115) = (term200 A t s _34115)) = ((term200 A t s _34115) = (term200 A t s _34115)).
Proof. exact (MK_COMB (@lem3310397 A t s _34115) (@lem3310403 A t s _34115)). Qed.
Lemma lem3310406 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3310407 (x : Prop) : (x = x) = True.
Proof. exact (@lem3310406 Prop x). Qed.
Lemma lem3310408 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : ((term200 A t s _34115) = (term200 A t s _34115)) = True.
Proof. exact (@lem3310407 (term200 A t s _34115)). Qed.
Lemma lem3310409 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : ((term82 A s t _34115) = (term200 A t s _34115)) = True.
Proof. exact (TRANS (@lem3310404 A t s _34115) (@lem3310408 A t s _34115)). Qed.
Lemma lem3310410 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : True = ((term82 A s t _34115) = (term200 A t s _34115)).
Proof. exact (SYM (@lem3310409 A t s _34115)). Qed.
Lemma lem3310411 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34115 : A) : (term82 A s t _34115) = (term200 A t s _34115).
Proof. exact (EQ_MP (@lem3310410 A t s _34115) (@lem0)). Qed.
Lemma lem3310412 {A : Type'} (_34115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term200 A t s _34115.
Proof. exact (EQ_MP (@lem3310411 A t s _34115) (@lem3310203 A _34115 x s t x' h1)). Qed.
Lemma lem3310414 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3310415 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34115 : A) : (term200 A t s _34115) = (term204 A s t _34115).
Proof. exact (@lem3310414 (term35 A s _34115) (t _34115)). Qed.
Lemma lem3310417 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3310418 {A : Type'} (s : A -> Prop) (_34115 : A) : (term79 A s _34115) = (s _34115).
Proof. exact (@lem3310417 (s _34115)). Qed.
Lemma lem3310419 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3310420 {A : Type'} (s : A -> Prop) (_34115 : A) : (term205 A s _34115) = (term21 A s _34115).
Proof. exact (MK_COMB (@lem3310419) (@lem3310418 A s _34115)). Qed.
Lemma lem3310421 {A : Type'} (t : A -> Prop) (_34115 : A) : (t _34115) = (t _34115).
Proof. exact (eq_refl (t _34115)). Qed.
Lemma lem3310422 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34115 : A) : (term204 A s t _34115) = (term38 A s t _34115).
Proof. exact (MK_COMB (@lem3310420 A s _34115) (@lem3310421 A t _34115)). Qed.
Lemma lem3310423 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34115 : A) : (term200 A t s _34115) = (term38 A s t _34115).
Proof. exact (TRANS (@lem3310415 A s t _34115) (@lem3310422 A s t _34115)). Qed.
Lemma lem3310426 {A : Type'} (_34115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term38 A s t _34115.
Proof. exact (EQ_MP (@lem3310423 A s t _34115) (@lem3310412 A _34115 x s t x' h1)). Qed.
Lemma lem3310427 {A : Type'} (_34115 : A) (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term38 A s t _34115.
Proof. exact (@lem3310426 A _34115 x s t x' h1). Qed.
Lemma lem3310428 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : term38 A s t x'.
Proof. exact (@lem3310427 A x' x s t x' h1). Qed.
Lemma lem3310431 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') (h2 : term81 A s t x') : t x'.
Proof. exact (@lem3310428 A x s t x' h1 (@lem3310383 A s t x' h2)). Qed.
Lemma lem3310432 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') (h2 : term81 A s t x') : term188 A t x'.
Proof. exact (fun h0 : term35 A t x' => @lem3310431 A x s t x' h1 h2). Qed.
Lemma lem3310434 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310435 {A : Type'} (t : A -> Prop) (x' : A) : (term188 A t x') = (t x').
Proof. exact (@lem3310434 (t x')). Qed.
Lemma lem3310436 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') (h2 : term81 A s t x') : t x'.
Proof. exact (EQ_MP (@lem3310435 A t x') (@lem3310432 A x s t x' h1 h2)). Qed.
Lemma lem3310439 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3310441 {A : Type'} (t : A -> Prop) (x' : A) : (term35 A t x') = (term206 A t x').
Proof. exact (@lem3310439 (t x')). Qed.
Lemma lem3310444 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term81 A s t x') : term206 A t x'.
Proof. exact (EQ_MP (@lem3310441 A t x') (@lem3310197 A s t x' h1)). Qed.
Lemma lem3310447 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') (h2 : term81 A s t x') : False.
Proof. exact (@lem3310444 A s t x' h2 (@lem3310436 A x s t x' h1 h2)). Qed.
Lemma lem3310448 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') (h2 : term81 A s t x') : term199.
Proof. exact (fun h0 : ~ False => @lem3310447 A x s t x' h1 h2). Qed.
Lemma lem3310450 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310451 : term199 = False.
Proof. exact (@lem3310450 False). Qed.
Lemma lem3310452 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') (h2 : term81 A s t x') : False.
Proof. exact (EQ_MP (@lem3310451) (@lem3310448 A x s t x' h1 h2)). Qed.
Lemma lem3310454 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : s x'.
Proof. exact (proj1 (@lem3310049 A x' x s t h1)). Qed.
Lemma lem3310455 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term188 A s x'.
Proof. exact (fun h0 : term35 A s x' => @lem3310454 A x' x s t h1). Qed.
Lemma lem3310457 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310458 {A : Type'} (s : A -> Prop) (x' : A) : (term188 A s x') = (s x').
Proof. exact (@lem3310457 (s x')). Qed.
Lemma lem3310459 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : s x'.
Proof. exact (EQ_MP (@lem3310458 A s x') (@lem3310455 A x' x s t h1)). Qed.
Lemma lem3310465 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3310466 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : (term82 A s t _34116) = (term200 A t s _34116).
Proof. exact (@lem3310465 (t _34116) (term35 A s _34116)). Qed.
Lemma lem3310472 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3310473 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : (term201 A s t _34116) = (term202 A t s _34116).
Proof. exact (MK_COMB (@lem3310472) (@lem3310466 A t s _34116)). Qed.
Lemma lem3310479 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : (term200 A t s _34116) = (term200 A t s _34116).
Proof. exact (eq_refl (term200 A t s _34116)). Qed.
Lemma lem3310480 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : ((term82 A s t _34116) = (term200 A t s _34116)) = ((term200 A t s _34116) = (term200 A t s _34116)).
Proof. exact (MK_COMB (@lem3310473 A t s _34116) (@lem3310479 A t s _34116)). Qed.
Lemma lem3310482 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3310483 (x : Prop) : (x = x) = True.
Proof. exact (@lem3310482 Prop x). Qed.
Lemma lem3310484 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : ((term200 A t s _34116) = (term200 A t s _34116)) = True.
Proof. exact (@lem3310483 (term200 A t s _34116)). Qed.
Lemma lem3310485 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : ((term82 A s t _34116) = (term200 A t s _34116)) = True.
Proof. exact (TRANS (@lem3310480 A t s _34116) (@lem3310484 A t s _34116)). Qed.
Lemma lem3310486 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : True = ((term82 A s t _34116) = (term200 A t s _34116)).
Proof. exact (SYM (@lem3310485 A t s _34116)). Qed.
Lemma lem3310487 {A : Type'} (t : A -> Prop) (s : A -> Prop) (_34116 : A) : (term82 A s t _34116) = (term200 A t s _34116).
Proof. exact (EQ_MP (@lem3310486 A t s _34116) (@lem0)). Qed.
Lemma lem3310488 {A : Type'} (_34116 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term200 A t s _34116.
Proof. exact (EQ_MP (@lem3310487 A t s _34116) (@lem3310217 A _34116 x' x s t h1)). Qed.
Lemma lem3310490 (b : Prop) (a : Prop) : (a \/ b) = (term203 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3310491 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34116 : A) : (term200 A t s _34116) = (term204 A s t _34116).
Proof. exact (@lem3310490 (term35 A s _34116) (t _34116)). Qed.
Lemma lem3310493 (a : Prop) : (term56 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3310494 {A : Type'} (s : A -> Prop) (_34116 : A) : (term79 A s _34116) = (s _34116).
Proof. exact (@lem3310493 (s _34116)). Qed.
Lemma lem3310495 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3310496 {A : Type'} (s : A -> Prop) (_34116 : A) : (term205 A s _34116) = (term21 A s _34116).
Proof. exact (MK_COMB (@lem3310495) (@lem3310494 A s _34116)). Qed.
Lemma lem3310497 {A : Type'} (t : A -> Prop) (_34116 : A) : (t _34116) = (t _34116).
Proof. exact (eq_refl (t _34116)). Qed.
Lemma lem3310498 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34116 : A) : (term204 A s t _34116) = (term38 A s t _34116).
Proof. exact (MK_COMB (@lem3310496 A s _34116) (@lem3310497 A t _34116)). Qed.
Lemma lem3310499 {A : Type'} (s : A -> Prop) (t : A -> Prop) (_34116 : A) : (term200 A t s _34116) = (term38 A s t _34116).
Proof. exact (TRANS (@lem3310491 A s t _34116) (@lem3310498 A s t _34116)). Qed.
Lemma lem3310502 {A : Type'} (_34116 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term38 A s t _34116.
Proof. exact (EQ_MP (@lem3310499 A s t _34116) (@lem3310488 A _34116 x' x s t h1)). Qed.
Lemma lem3310503 {A : Type'} (_34116 : A) (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term38 A s t _34116.
Proof. exact (@lem3310502 A _34116 x' x s t h1). Qed.
Lemma lem3310504 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term38 A s t x'.
Proof. exact (@lem3310503 A x' x' x s t h1). Qed.
Lemma lem3310507 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : t x'.
Proof. exact (@lem3310504 A x' x s t h1 (@lem3310459 A x' x s t h1)). Qed.
Lemma lem3310508 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term188 A t x'.
Proof. exact (fun h0 : term35 A t x' => @lem3310507 A x' x s t h1). Qed.
Lemma lem3310510 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310511 {A : Type'} (t : A -> Prop) (x' : A) : (term188 A t x') = (t x').
Proof. exact (@lem3310510 (t x')). Qed.
Lemma lem3310512 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : t x'.
Proof. exact (EQ_MP (@lem3310511 A t x') (@lem3310508 A x' x s t h1)). Qed.
Lemma lem3310515 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3310517 {A : Type'} (t : A -> Prop) (x' : A) : (term35 A t x') = (term206 A t x').
Proof. exact (@lem3310515 (t x')). Qed.
Lemma lem3310520 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term35 A t x') : term206 A t x'.
Proof. exact (EQ_MP (@lem3310517 A t x') (@lem3310221 A t x' h1)). Qed.
Lemma lem3310523 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : False.
Proof. exact (@lem3310520 A t x' h1 (@lem3310512 A x' x s t h2)). Qed.
Lemma lem3310524 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : term199.
Proof. exact (fun h0 : ~ False => @lem3310523 A x' x s t h1 h2). Qed.
Lemma lem3310526 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310527 : term199 = False.
Proof. exact (@lem3310526 False). Qed.
Lemma lem3310528 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3310527) (@lem3310524 A x' x s t h1 h2)). Qed.
Lemma lem3310530 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3310287 A s x' x h2) (@lem3310231 A x' x s t h1)). Qed.
Lemma lem3310531 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : term188 A s x.
Proof. exact (fun h0 : term35 A s x => @lem3310530 A s t x' x h1 h2). Qed.
Lemma lem3310533 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310534 {A : Type'} (s : A -> Prop) (x : A) : (term188 A s x) = (s x).
Proof. exact (@lem3310533 (s x)). Qed.
Lemma lem3310535 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : s x.
Proof. exact (EQ_MP (@lem3310534 A s x) (@lem3310531 A s t x' x h1 h2)). Qed.
Lemma lem3310538 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3310540 {A : Type'} (s : A -> Prop) (x : A) : (term35 A s x) = (term206 A s x).
Proof. exact (@lem3310538 (s x)). Qed.
Lemma lem3310543 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : term206 A s x.
Proof. exact (EQ_MP (@lem3310540 A s x) (@lem3310261 A x' x s t h1)). Qed.
Lemma lem3310546 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : False.
Proof. exact (@lem3310543 A x' x s t h1 (@lem3310535 A s t x' x h1 h2)). Qed.
Lemma lem3310547 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : term199.
Proof. exact (fun h0 : ~ False => @lem3310546 A s t x' x h1 h2). Qed.
Lemma lem3310549 (p : Prop) : (term189 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3310550 : term199 = False.
Proof. exact (@lem3310549 False). Qed.
Lemma lem3310552 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3310550) (@lem3310547 A s t x' x h1 h2)). Qed.
Lemma lem3310553 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3310552 A s t x' x h1 h2) (fun h3 : False => @lem3310233 A x' x h2)). Qed.
Lemma lem3310554 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3310553 A s t x' x h1 h2) (@lem3310233 A x' x h2)). Qed.
Lemma lem3310555 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : (term35 A t x') = False.
Proof. exact (prop_ext (fun h3 : term35 A t x' => @lem3310528 A x' x s t h1 h2) (fun h3 : False => @lem3310221 A t x' h1)). Qed.
Lemma lem3310556 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3310555 A x' x s t h1 h2) (@lem3310221 A t x' h1)). Qed.
Lemma lem3310557 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3310350 A x s t x' h1 h2) (fun h3 : False => @lem3310181 A s x h1)). Qed.
Lemma lem3310558 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : False.
Proof. exact (EQ_MP (@lem3310557 A x s t x' h1 h2) (@lem3310181 A s x h1)). Qed.
Lemma lem3310559 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3310554 A s t x' x h1 h2) (fun h3 : False => @lem3310163 A x' x h2)). Qed.
Lemma lem3310560 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3310559 A s t x' x h1 h2) (@lem3310163 A x' x h2)). Qed.
Lemma lem3310561 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : (term35 A t x') = False.
Proof. exact (prop_ext (fun h3 : term35 A t x' => @lem3310556 A x' x s t h1 h2) (fun h3 : False => @lem3310138 A t x' h1)). Qed.
Lemma lem3310562 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3310561 A x' x s t h1 h2) (@lem3310138 A t x' h1)). Qed.
Lemma lem3310563 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3310558 A x s t x' h1 h2) (fun h3 : False => @lem3310082 A s x h1)). Qed.
Lemma lem3310564 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : False.
Proof. exact (EQ_MP (@lem3310563 A x s t x' h1 h2) (@lem3310082 A s x h1)). Qed.
Lemma lem3310565 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3310560 A s t x' x h1 h2) (fun h3 : False => @lem3310163 A x' x h2)). Qed.
Lemma lem3310566 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term153 A x' x s t) (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3310565 A s t x' x h1 h2) (@lem3310163 A x' x h2)). Qed.
Lemma lem3310567 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : (term35 A t x') = False.
Proof. exact (prop_ext (fun h3 : term35 A t x' => @lem3310562 A x' x s t h1 h2) (fun h3 : False => @lem3310138 A t x' h1)). Qed.
Lemma lem3310568 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term35 A t x') (h2 : term153 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3310567 A x' x s t h1 h2) (@lem3310138 A t x' h1)). Qed.
Lemma lem3310569 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : (s x) = False.
Proof. exact (prop_ext (fun h3 : s x => @lem3310564 A x s t x' h1 h2) (fun h3 : False => @lem3310082 A s x h1)). Qed.
Lemma lem3310570 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x) (h2 : term135 A x s t x') : False.
Proof. exact (EQ_MP (@lem3310569 A x s t x' h1 h2) (@lem3310082 A s x h1)). Qed.
Lemma lem3310571 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term153 A x' x s t) : False.
Proof. exact (or_elim (@lem3310052 A x' x s t h1) (fun h0 : term35 A t x' => @lem3310568 A x' x s t h0 h1) (fun h0 : x' = x => @lem3310566 A s t x' x h1 h0)). Qed.
Lemma lem3310572 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term135 A x s t x') : False.
Proof. exact (or_elim (@lem3310042 A x s t x' h1) (fun h0 : s x => @lem3310570 A x s t x' h0 h1) (fun h0 : term81 A s t x' => @lem3310452 A x s t x' h1 h0)). Qed.
Lemma lem3310573 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term174 A x' x s t) : False.
Proof. exact (or_elim (@lem3310039 A x' x s t h1) (fun h0 : term135 A x s t x' => @lem3310572 A x s t x' h0) (fun h0 : term153 A x' x s t => @lem3310571 A x' x s t h0)). Qed.
Lemma lem3310574 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term174 A x' x s t) : (term174 A x' x s t) = False.
Proof. exact (prop_ext (fun h2 : term174 A x' x s t => @lem3310573 A x' x s t h1) (fun h2 : False => @lem3310039 A x' x s t h1)). Qed.
Lemma lem3310575 {A : Type'} (x' : A) (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term174 A x' x s t) : False.
Proof. exact (EQ_MP (@lem3310574 A x' x s t h1) (@lem3310039 A x' x s t h1)). Qed.
Lemma lem3310576 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term58 A x s t) : False.
Proof. exact (ex_elim (@lem3309946 A x s t h1) (fun x' : A => fun h0 : term176 A x s t x' => @lem3310575 A x' x s t h0)). Qed.
Lemma lem3310577 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term58 A x s t) : (term58 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term58 A x s t => @lem3310576 A x s t h1) (fun h2 : False => @lem3309619 A x s t h1)). Qed.
Lemma lem3310578 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term58 A x s t) : False.
Proof. exact (EQ_MP (@lem3310577 A x s t h1) (@lem3309619 A x s t h1)). Qed.
Lemma lem3310579 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term57 A x s t.
Proof. exact (fun h0 : term58 A x s t => @lem3310578 A x s t h0). Qed.
Lemma lem3310580 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term32 A s t x) = (term42 A x s t).
Proof. exact (EQ_MP (@lem3309618 A x s t) (@lem3310579 A x s t)). Qed.
Lemma lem3310585 {A : Type'} (x : A) (s : A -> Prop) : term44 A x s.
Proof. exact (fun t : A -> Prop => @lem3310580 A x s t). Qed.
Lemma lem3310590 {A : Type'} (x : A) : term46 A x.
Proof. exact (fun s : A -> Prop => @lem3310585 A x s). Qed.
Lemma lem3310595 {A : Type'} : term48 A.
Proof. exact (fun x : A => @lem3310590 A x). Qed.
Lemma lem3310596 {A : Type'} : term50 A.
Proof. exact (EQ_MP (@lem3309614 A) (@lem3310595 A)). Qed.
Lemma lem3310598 {A : Type'} : term50 A.
Proof. exact (@lem3309493 A (@lem3310596 A)). Qed.
Lemma lem3310599 {A : Type'} (h1 : term51 A) : False.
Proof. exact (@lem3310598 A (@lem3309477 A h1)). Qed.
Lemma lem3310600 {A : Type'} (h1 : term51 A) : (term51 A) = False.
Proof. exact (prop_ext (fun h2 : term51 A => @lem3310599 A h1) (fun h2 : False => @lem3309477 A h1)). Qed.
Lemma lem3310601 {A : Type'} (h1 : term51 A) : False.
Proof. exact (EQ_MP (@lem3310600 A h1) (@lem3309477 A h1)). Qed.
Lemma lem3310602 {A : Type'} : term50 A.
Proof. exact (fun h0 : term51 A => @lem3310601 A h0). Qed.
Lemma lem3310603 {A : Type'} : term48 A.
Proof. exact (EQ_MP (@lem3309476 A) (@lem3310602 A)). Qed.
Lemma lem3310604 {A : Type'} : term19 A.
Proof. exact (EQ_MP (@lem3309472 A) (@lem3310603 A)). Qed.
Lemma lem3310605 {A : Type'} : term18 A.
Proof. exact (EQ_MP (@lem3309351 A) (@lem3310604 A)). Qed.
