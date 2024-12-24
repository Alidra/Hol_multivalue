Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_SQRT_term_abbrevs.
Require Import SQRT_LE_0_spec.
Require Import SQRT_NEG_spec.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1948347 (x : real) : term0 x.
Proof. exact (@lem1948346 x). Qed.
Lemma lem1948348 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1948350 (x : real) : term3 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1948351 (x : real) : (term3 x) = ((real_abs x) = (term4 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1948356 (x : real) : (real_abs x) = (term4 x).
Proof. exact (EQ_MP (@lem1948351 x) (@lem1948350 x)). Qed.
Lemma lem1948357 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1948356 (sqrt x)). Qed.
Lemma lem1948359 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1948348 x) (@lem1948347 x)). Qed.
Lemma lem1948360 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1948361 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1948360) (@lem1948359 x)). Qed.
Lemma lem1948362 (x : real) : (sqrt x) = (sqrt x).
Proof. exact (eq_refl (sqrt x)). Qed.
Lemma lem1948363 (x : real) : (term9 x) = (term10 x).
Proof. exact (MK_COMB (@lem1948361 x) (@lem1948362 x)). Qed.
Lemma lem1948364 (x : real) : (term11 x) = (term11 x).
Proof. exact (eq_refl (term11 x)). Qed.
Lemma lem1948365 (x : real) : (term6 x) = (term12 x).
Proof. exact (MK_COMB (@lem1948363 x) (@lem1948364 x)). Qed.
Lemma lem1948366 (x : real) : (term5 x) = (term12 x).
Proof. exact (TRANS (@lem1948357 x) (@lem1948365 x)). Qed.
Lemma lem1948367 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1948368 (x : real) : (term13 x) = (term14 x).
Proof. exact (MK_COMB (@lem1948367) (@lem1948366 x)). Qed.
Lemma lem1948370 (x : real) : (real_abs x) = (term4 x).
Proof. exact (EQ_MP (@lem1948351 x) (@lem1948350 x)). Qed.
Lemma lem1948371 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1948372 (x : real) : (term15 x) = (term16 x).
Proof. exact (MK_COMB (@lem1948371) (@lem1948370 x)). Qed.
Lemma lem1948373 (x : real) : ((term5 x) = (term15 x)) = ((term12 x) = (term16 x)).
Proof. exact (MK_COMB (@lem1948368 x) (@lem1948372 x)). Qed.
Lemma lem1948376 (x : real) : ((term12 x) = (term16 x)) = ((term5 x) = (term15 x)).
Proof. exact (SYM (@lem1948373 x)). Qed.
Lemma lem1948377 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term17 _476 _475 _474 _477) = (term18 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1948378 (_474 : real) (_475 : Prop) (x : real) (_477 : real) : (term19 x _475 _474 _477) = (term20 _474 _475 x _477).
Proof. exact (@lem1948377 _474 _475 (term21 x) _477). Qed.
Lemma lem1948379 (x : real) : (term22 x) = (term23 x).
Proof. exact (@lem1948378 (sqrt x) (term2 x) x (term11 x)). Qed.
Lemma lem1948380 (x : real) : (term24 x) = ((term11 x) = (term16 x)).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1948381 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1948382 (x : real) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem1948381 x) (@lem1948380 x)). Qed.
Lemma lem1948383 (x : real) : (term28 x) = ((sqrt x) = (term16 x)).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1948384 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1948385 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1948384 x) (@lem1948383 x)). Qed.
Lemma lem1948386 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1948387 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1948386) (@lem1948385 x)). Qed.
Lemma lem1948388 (x : real) : (term23 x) = (term34 x).
Proof. exact (MK_COMB (@lem1948387 x) (@lem1948382 x)). Qed.
Lemma lem1948389 (x : real) : (term22 x) = ((term12 x) = (term16 x)).
Proof. exact (eq_refl (term22 x)). Qed.
Lemma lem1948390 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1948391 (x : real) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem1948390) (@lem1948389 x)). Qed.
Lemma lem1948392 (x : real) : ((term22 x) = (term23 x)) = (((term12 x) = (term16 x)) = (term34 x)).
Proof. exact (MK_COMB (@lem1948391 x) (@lem1948388 x)). Qed.
Lemma lem1948393 (x : real) : ((term12 x) = (term16 x)) = (term34 x).
Proof. exact (EQ_MP (@lem1948392 x) (@lem1948379 x)). Qed.
Lemma lem1948394 (x : real) : (term34 x) = ((term12 x) = (term16 x)).
Proof. exact (SYM (@lem1948393 x)). Qed.
Lemma lem1948395 (x : real) (h1 : term2 x) : term2 x.
Proof. exact (h1). Qed.
Lemma lem1948396 (x : real) : (term2 x) = ((term2 x) = True).
Proof. exact (@lem7 (term2 x)). Qed.
Lemma lem1948397 (x : real) (h1 : term2 x) : (term2 x) = True.
Proof. exact (EQ_MP (@lem1948396 x) (@lem1948395 x h1)). Qed.
Lemma lem1948398 (x : real) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1948399 (x : real) (h1 : term2 x) : (term38 x) = (term39 x).
Proof. exact (MK_COMB (@lem1948398 x) (@lem1948397 x h1)). Qed.
Lemma lem1948400 (x : real) : (term39 x) = ((sqrt x) = (term40 x)).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1948401 (x : real) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem1948402 (x : real) : ((term38 x) = (term39 x)) = ((term38 x) = ((sqrt x) = (term40 x))).
Proof. exact (MK_COMB (@lem1948401 x) (@lem1948400 x)). Qed.
Lemma lem1948403 (x : real) : (term38 x) = ((sqrt x) = (term16 x)).
Proof. exact (eq_refl (term38 x)). Qed.
Lemma lem1948404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1948405 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1948404) (@lem1948403 x)). Qed.
Lemma lem1948406 (x : real) : ((sqrt x) = (term40 x)) = ((sqrt x) = (term40 x)).
Proof. exact (eq_refl ((sqrt x) = (term40 x))). Qed.
Lemma lem1948407 (x : real) : ((term38 x) = ((sqrt x) = (term40 x))) = (((sqrt x) = (term16 x)) = ((sqrt x) = (term40 x))).
Proof. exact (MK_COMB (@lem1948405 x) (@lem1948406 x)). Qed.
Lemma lem1948408 (x : real) : ((term38 x) = (term39 x)) = (((sqrt x) = (term16 x)) = ((sqrt x) = (term40 x))).
Proof. exact (TRANS (@lem1948402 x) (@lem1948407 x)). Qed.
Lemma lem1948409 (x : real) (h1 : term2 x) : ((sqrt x) = (term16 x)) = ((sqrt x) = (term40 x)).
Proof. exact (EQ_MP (@lem1948408 x) (@lem1948399 x h1)). Qed.
Lemma lem1948410 (x : real) (h1 : term2 x) : ((sqrt x) = (term40 x)) = ((sqrt x) = (term16 x)).
Proof. exact (SYM (@lem1948409 x h1)). Qed.
Lemma lem1948411 (x : real) (h1 : term43 x) : term43 x.
Proof. exact (h1). Qed.
Lemma lem1948412 (x : real) : term44 x.
Proof. exact (@lem82 (term2 x)). Qed.
Lemma lem1948413 (x : real) (h1 : term43 x) : (term2 x) = False.
Proof. exact (@lem1948412 x (@lem1948411 x h1)). Qed.
Lemma lem1948414 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1948415 (x : real) (h1 : term43 x) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1948414 x) (@lem1948413 x h1)). Qed.
Lemma lem1948416 (x : real) : (term47 x) = ((term11 x) = (term48 x)).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1948417 (x : real) : (term49 x) = (term49 x).
Proof. exact (eq_refl (term49 x)). Qed.
Lemma lem1948418 (x : real) : ((term46 x) = (term47 x)) = ((term46 x) = ((term11 x) = (term48 x))).
Proof. exact (MK_COMB (@lem1948417 x) (@lem1948416 x)). Qed.
Lemma lem1948419 (x : real) : (term46 x) = ((term11 x) = (term16 x)).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1948420 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1948421 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1948420) (@lem1948419 x)). Qed.
Lemma lem1948422 (x : real) : ((term11 x) = (term48 x)) = ((term11 x) = (term48 x)).
Proof. exact (eq_refl ((term11 x) = (term48 x))). Qed.
Lemma lem1948423 (x : real) : ((term46 x) = ((term11 x) = (term48 x))) = (((term11 x) = (term16 x)) = ((term11 x) = (term48 x))).
Proof. exact (MK_COMB (@lem1948421 x) (@lem1948422 x)). Qed.
Lemma lem1948424 (x : real) : ((term46 x) = (term47 x)) = (((term11 x) = (term16 x)) = ((term11 x) = (term48 x))).
Proof. exact (TRANS (@lem1948418 x) (@lem1948423 x)). Qed.
Lemma lem1948425 (x : real) (h1 : term43 x) : ((term11 x) = (term16 x)) = ((term11 x) = (term48 x)).
Proof. exact (EQ_MP (@lem1948424 x) (@lem1948415 x h1)). Qed.
Lemma lem1948426 (x : real) (h1 : term43 x) : ((term11 x) = (term48 x)) = ((term11 x) = (term16 x)).
Proof. exact (SYM (@lem1948425 x h1)). Qed.
Lemma lem1948435 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1948436 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1948435 real t2 t1). Qed.
Lemma lem1948437 (x : real) : (term51 x) = x.
Proof. exact (@lem1948436 (real_neg x) x). Qed.
Lemma lem1948438 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1948439 (x : real) : (term40 x) = (sqrt x).
Proof. exact (MK_COMB (@lem1948438) (@lem1948437 x)). Qed.
Lemma lem1948440 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1948441 (x : real) : ((sqrt x) = (term40 x)) = ((sqrt x) = (sqrt x)).
Proof. exact (MK_COMB (@lem1948440 x) (@lem1948439 x)). Qed.
Lemma lem1948443 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1948444 (x : real) : (x = x) = True.
Proof. exact (@lem1948443 real x). Qed.
Lemma lem1948445 (x : real) : ((sqrt x) = (sqrt x)) = True.
Proof. exact (@lem1948444 (sqrt x)). Qed.
Lemma lem1948446 (x : real) : ((sqrt x) = (term40 x)) = True.
Proof. exact (TRANS (@lem1948441 x) (@lem1948445 x)). Qed.
Lemma lem1948447 (x : real) : True = ((sqrt x) = (term40 x)).
Proof. exact (SYM (@lem1948446 x)). Qed.
Lemma lem1948448 (x : real) : (sqrt x) = (term40 x).
Proof. exact (EQ_MP (@lem1948447 x) (@lem0)). Qed.
Lemma lem1948449 (x : real) : term53 x.
Proof. exact (@lem1921835 x). Qed.
Lemma lem1948450 (x : real) : (term53 x) = ((term54 x) = (term11 x)).
Proof. exact (eq_refl (term53 x)). Qed.
Lemma lem1948457 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1948458 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1948457 real t1 t2). Qed.
Lemma lem1948459 (x : real) : (term55 x) = (real_neg x).
Proof. exact (@lem1948458 x (real_neg x)). Qed.
Lemma lem1948460 : sqrt = sqrt.
Proof. exact (eq_refl sqrt). Qed.
Lemma lem1948461 (x : real) : (term48 x) = (term54 x).
Proof. exact (MK_COMB (@lem1948460) (@lem1948459 x)). Qed.
Lemma lem1948463 (x : real) : (term54 x) = (term11 x).
Proof. exact (EQ_MP (@lem1948450 x) (@lem1948449 x)). Qed.
Lemma lem1948464 (x : real) : (term48 x) = (term11 x).
Proof. exact (TRANS (@lem1948461 x) (@lem1948463 x)). Qed.
Lemma lem1948465 (x : real) : (term56 x) = (term56 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1948466 (x : real) : ((term11 x) = (term48 x)) = ((term11 x) = (term11 x)).
Proof. exact (MK_COMB (@lem1948465 x) (@lem1948464 x)). Qed.
Lemma lem1948468 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1948469 (x : real) : (x = x) = True.
Proof. exact (@lem1948468 real x). Qed.
Lemma lem1948470 (x : real) : ((term11 x) = (term11 x)) = True.
Proof. exact (@lem1948469 (term11 x)). Qed.
Lemma lem1948471 (x : real) : ((term11 x) = (term48 x)) = True.
Proof. exact (TRANS (@lem1948466 x) (@lem1948470 x)). Qed.
Lemma lem1948472 (x : real) : True = ((term11 x) = (term48 x)).
Proof. exact (SYM (@lem1948471 x)). Qed.
Lemma lem1948473 (x : real) : (term11 x) = (term48 x).
Proof. exact (EQ_MP (@lem1948472 x) (@lem0)). Qed.
Lemma lem1948474 (x : real) (h1 : term43 x) : (term11 x) = (term16 x).
Proof. exact (EQ_MP (@lem1948426 x h1) (@lem1948473 x)). Qed.
Lemma lem1948475 (x : real) (h1 : term43 x) : (term43 x) = ((term11 x) = (term16 x)).
Proof. exact (prop_ext (fun h2 : term43 x => @lem1948474 x h1) (fun h2 : (term11 x) = (term16 x) => @lem1948411 x h1)). Qed.
Lemma lem1948476 (x : real) (h1 : term43 x) : (term11 x) = (term16 x).
Proof. exact (EQ_MP (@lem1948475 x h1) (@lem1948411 x h1)). Qed.
Lemma lem1948477 (x : real) : term27 x.
Proof. exact (fun h0 : term43 x => @lem1948476 x h0). Qed.
Lemma lem1948478 (x : real) (h1 : term2 x) : (sqrt x) = (term16 x).
Proof. exact (EQ_MP (@lem1948410 x h1) (@lem1948448 x)). Qed.
Lemma lem1948479 (x : real) (h1 : term2 x) : (term2 x) = ((sqrt x) = (term16 x)).
Proof. exact (prop_ext (fun h2 : term2 x => @lem1948478 x h1) (fun h2 : (sqrt x) = (term16 x) => @lem1948395 x h1)). Qed.
Lemma lem1948480 (x : real) (h1 : term2 x) : (sqrt x) = (term16 x).
Proof. exact (EQ_MP (@lem1948479 x h1) (@lem1948395 x h1)). Qed.
Lemma lem1948481 (x : real) : term31 x.
Proof. exact (fun h0 : term2 x => @lem1948480 x h0). Qed.
Lemma lem1948482 (x : real) : term34 x.
Proof. exact (conj (@lem1948481 x) (@lem1948477 x)). Qed.
Lemma lem1948483 (x : real) : (term12 x) = (term16 x).
Proof. exact (EQ_MP (@lem1948394 x) (@lem1948482 x)). Qed.
Lemma lem1948484 (x : real) : (term5 x) = (term15 x).
Proof. exact (EQ_MP (@lem1948376 x) (@lem1948483 x)). Qed.
Lemma lem1948489 : term57.
Proof. exact (fun x : real => @lem1948484 x). Qed.
