Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_LT_term_abbrevs.
Require Import REAL_ADD_RID_spec.
Require Import REAL_LE_LNEG_spec.
Require Import REAL_NEG_SUB_spec.
Require Import REAL_SUB_LE_spec.
Require Import real_lt_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1376326 (x : real) : term0 x.
Proof. exact (@lem1374224 x). Qed.
Lemma lem1376327 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1376328 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem1376327 x) (@lem1376326 x)). Qed.
Lemma lem1376329 (x : real) (y : real) : term2 x y.
Proof. exact (@lem1376328 x y). Qed.
Lemma lem1376330 (y : real) (x : real) : (term2 x y) = ((term3 x y) = (real_le y x)).
Proof. exact (eq_refl (term2 x y)). Qed.
Lemma lem1376332 (x : real) : term4 x.
Proof. exact (@lem1361590 x). Qed.
Lemma lem1376333 (x : real) : (term4 x) = ((term5 x) = x).
Proof. exact (eq_refl (term4 x)). Qed.
Lemma lem1376335 (x : real) : term6 x.
Proof. exact (@lem1362225 x). Qed.
Lemma lem1376336 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1376337 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1376336 x) (@lem1376335 x)). Qed.
Lemma lem1376338 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1376337 x y). Qed.
Lemma lem1376339 (x : real) (y : real) : (term8 x y) = ((term9 x y) = (term10 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1376343 (y : real) (x : real) (h1 : (term11 x y) = (real_sub y x)) : (term11 x y) = (real_sub y x).
Proof. exact (h1). Qed.
Lemma lem1376344 (y : real) (x : real) (h1 : (term11 x y) = (real_sub y x)) : (real_sub y x) = (term11 x y).
Proof. exact (SYM (@lem1376343 y x h1)). Qed.
Lemma lem1376345 (x : real) (y : real) (h1 : (real_sub y x) = (term11 x y)) : (real_sub y x) = (term11 x y).
Proof. exact (h1). Qed.
Lemma lem1376346 (x : real) (y : real) (h1 : (real_sub y x) = (term11 x y)) : (term11 x y) = (real_sub y x).
Proof. exact (SYM (@lem1376345 x y h1)). Qed.
Lemma lem1376347 (x : real) (y : real) : ((term11 x y) = (real_sub y x)) = ((real_sub y x) = (term11 x y)).
Proof. exact (prop_ext (fun h1 : (term11 x y) = (real_sub y x) => @lem1376344 y x h1) (fun h1 : (real_sub y x) = (term11 x y) => @lem1376346 x y h1)). Qed.
Lemma lem1376348 (x : real) : (term12 x) = (term13 x).
Proof. exact (fun_ext (fun y : real => @lem1376347 x y)). Qed.
Lemma lem1376349 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376350 (x : real) : (term14 x) = (term15 x).
Proof. exact (MK_COMB (@lem1376349) (@lem1376348 x)). Qed.
Lemma lem1376351 : term16 = term17.
Proof. exact (fun_ext (fun x : real => @lem1376350 x)). Qed.
Lemma lem1376352 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376353 : term18 = term19.
Proof. exact (MK_COMB (@lem1376352) (@lem1376351)). Qed.
Lemma lem1376354 : term19.
Proof. exact (EQ_MP (@lem1376353) (@lem1374337)). Qed.
Lemma lem1376355 (x : real) : term20 x.
Proof. exact (@lem1376354 x). Qed.
Lemma lem1376356 (x : real) : (term20 x) = (term15 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1376357 (x : real) : term15 x.
Proof. exact (EQ_MP (@lem1376356 x) (@lem1376355 x)). Qed.
Lemma lem1376358 (x : real) (y : real) : term21 x y.
Proof. exact (@lem1376357 x y). Qed.
Lemma lem1376359 (x : real) (y : real) : (term21 x y) = ((real_sub y x) = (term11 x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem1376361 (y : real) : term22 y.
Proof. exact (@lem1341566 y). Qed.
Lemma lem1376362 (y : real) : (term22 y) = (term23 y).
Proof. exact (eq_refl (term22 y)). Qed.
Lemma lem1376363 (y : real) : term23 y.
Proof. exact (EQ_MP (@lem1376362 y) (@lem1376361 y)). Qed.
Lemma lem1376364 (y : real) (x : real) : term24 y x.
Proof. exact (@lem1376363 y x). Qed.
Lemma lem1376365 (y : real) (x : real) : (term24 y x) = ((real_lt x y) = (term25 y x)).
Proof. exact (eq_refl (term24 y x)). Qed.
Lemma lem1376378 (y : real) (x : real) : (real_lt x y) = (term25 y x).
Proof. exact (EQ_MP (@lem1376365 y x) (@lem1376364 y x)). Qed.
Lemma lem1376379 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1376378 (real_sub x y) term28). Qed.
Lemma lem1376380 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376381 (x : real) (y : real) : (term29 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1376380) (@lem1376379 x y)). Qed.
Lemma lem1376383 (y : real) (x : real) : (real_lt x y) = (term25 y x).
Proof. exact (EQ_MP (@lem1376365 y x) (@lem1376364 y x)). Qed.
Lemma lem1376384 (x : real) (y : real) : (real_lt y x) = (term25 x y).
Proof. exact (@lem1376383 x y). Qed.
Lemma lem1376385 (x : real) (y : real) : ((term26 x y) = (real_lt y x)) = ((term27 x y) = (term25 x y)).
Proof. exact (MK_COMB (@lem1376381 x y) (@lem1376384 x y)). Qed.
Lemma lem1376388 (x : real) : (term31 x) = (term32 x).
Proof. exact (fun_ext (fun y : real => @lem1376385 x y)). Qed.
Lemma lem1376389 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376390 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1376389) (@lem1376388 x)). Qed.
Lemma lem1376395 : term35 = term36.
Proof. exact (fun_ext (fun x : real => @lem1376390 x)). Qed.
Lemma lem1376396 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376397 : term37 = term38.
Proof. exact (MK_COMB (@lem1376396) (@lem1376395)). Qed.
Lemma lem1376402 : term38 = term37.
Proof. exact (SYM (@lem1376397)). Qed.
Lemma lem1376414 (x : real) (y : real) : (real_sub y x) = (term11 x y).
Proof. exact (EQ_MP (@lem1376359 x y) (@lem1376358 x y)). Qed.
Lemma lem1376415 (y : real) (x : real) : (real_sub x y) = (term11 y x).
Proof. exact (@lem1376414 y x). Qed.
Lemma lem1376416 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1376417 (y : real) (x : real) : (term39 x y) = (term40 y x).
Proof. exact (MK_COMB (@lem1376416) (@lem1376415 y x)). Qed.
Lemma lem1376418 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem1376419 (y : real) (x : real) : (term41 x y) = (term42 y x).
Proof. exact (MK_COMB (@lem1376417 y x) (@lem1376418)). Qed.
Lemma lem1376420 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1376421 (y : real) (x : real) : (term27 x y) = (term43 y x).
Proof. exact (MK_COMB (@lem1376420) (@lem1376419 y x)). Qed.
Lemma lem1376422 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376423 (y : real) (x : real) : (term30 x y) = (term44 y x).
Proof. exact (MK_COMB (@lem1376422) (@lem1376421 y x)). Qed.
Lemma lem1376424 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1376425 (x : real) (y : real) : ((term27 x y) = (term25 x y)) = ((term43 y x) = (term25 x y)).
Proof. exact (MK_COMB (@lem1376423 y x) (@lem1376424 x y)). Qed.
Lemma lem1376426 (x : real) : (term32 x) = (term45 x).
Proof. exact (fun_ext (fun y : real => @lem1376425 x y)). Qed.
Lemma lem1376427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376428 (x : real) : (term34 x) = (term46 x).
Proof. exact (MK_COMB (@lem1376427) (@lem1376426 x)). Qed.
Lemma lem1376429 : term36 = term47.
Proof. exact (fun_ext (fun x : real => @lem1376428 x)). Qed.
Lemma lem1376430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376431 : term38 = term48.
Proof. exact (MK_COMB (@lem1376430) (@lem1376429)). Qed.
Lemma lem1376432 : term48 = term38.
Proof. exact (SYM (@lem1376431)). Qed.
Lemma lem1376444 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1376339 x y) (@lem1376338 x y)). Qed.
Lemma lem1376445 (y : real) (x : real) : (term42 y x) = (term49 y x).
Proof. exact (@lem1376444 (real_sub y x) term28). Qed.
Lemma lem1376447 (x : real) : (term5 x) = x.
Proof. exact (EQ_MP (@lem1376333 x) (@lem1376332 x)). Qed.
Lemma lem1376448 (y : real) (x : real) : (term50 y x) = (real_sub y x).
Proof. exact (@lem1376447 (real_sub y x)). Qed.
Lemma lem1376449 : term51 = term51.
Proof. exact (eq_refl term51). Qed.
Lemma lem1376450 (y : real) (x : real) : (term49 y x) = (term3 y x).
Proof. exact (MK_COMB (@lem1376449) (@lem1376448 y x)). Qed.
Lemma lem1376452 (y : real) (x : real) : (term3 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1376330 y x) (@lem1376329 x y)). Qed.
Lemma lem1376453 (x : real) (y : real) : (term3 y x) = (real_le x y).
Proof. exact (@lem1376452 x y). Qed.
Lemma lem1376454 (x : real) (y : real) : (term49 y x) = (real_le x y).
Proof. exact (TRANS (@lem1376450 y x) (@lem1376453 x y)). Qed.
Lemma lem1376455 (x : real) (y : real) : (term42 y x) = (real_le x y).
Proof. exact (TRANS (@lem1376445 y x) (@lem1376454 x y)). Qed.
Lemma lem1376456 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1376457 (x : real) (y : real) : (term43 y x) = (term25 x y).
Proof. exact (MK_COMB (@lem1376456) (@lem1376455 x y)). Qed.
Lemma lem1376458 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1376459 (x : real) (y : real) : (term44 y x) = (term52 x y).
Proof. exact (MK_COMB (@lem1376458) (@lem1376457 x y)). Qed.
Lemma lem1376460 (x : real) (y : real) : (term25 x y) = (term25 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1376461 (x : real) (y : real) : ((term43 y x) = (term25 x y)) = ((term25 x y) = (term25 x y)).
Proof. exact (MK_COMB (@lem1376459 x y) (@lem1376460 x y)). Qed.
Lemma lem1376463 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1376464 (x : Prop) : (x = x) = True.
Proof. exact (@lem1376463 Prop x). Qed.
Lemma lem1376465 (x : real) (y : real) : ((term25 x y) = (term25 x y)) = True.
Proof. exact (@lem1376464 (term25 x y)). Qed.
Lemma lem1376466 (x : real) (y : real) : ((term43 y x) = (term25 x y)) = True.
Proof. exact (TRANS (@lem1376461 x y) (@lem1376465 x y)). Qed.
Lemma lem1376467 (x : real) : (term45 x) = term53.
Proof. exact (fun_ext (fun y : real => @lem1376466 x y)). Qed.
Lemma lem1376468 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376469 (x : real) : (term46 x) = term54.
Proof. exact (MK_COMB (@lem1376468) (@lem1376467 x)). Qed.
Lemma lem1376471 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1376472 (t : Prop) : (term56 t) = t.
Proof. exact (@lem1376471 real t). Qed.
Lemma lem1376473 : term54 = True.
Proof. exact (@lem1376472 True). Qed.
Lemma lem1376474 (x : real) : (term46 x) = True.
Proof. exact (TRANS (@lem1376469 x) (@lem1376473)). Qed.
Lemma lem1376475 : term47 = term53.
Proof. exact (fun_ext (fun x : real => @lem1376474 x)). Qed.
Lemma lem1376476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1376477 : term48 = term54.
Proof. exact (MK_COMB (@lem1376476) (@lem1376475)). Qed.
Lemma lem1376479 {A : Type'} (t : Prop) : (term55 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1376480 (t : Prop) : (term56 t) = t.
Proof. exact (@lem1376479 real t). Qed.
Lemma lem1376481 : term54 = True.
Proof. exact (@lem1376480 True). Qed.
Lemma lem1376482 : term48 = True.
Proof. exact (TRANS (@lem1376477) (@lem1376481)). Qed.
Lemma lem1376483 : True = term48.
Proof. exact (SYM (@lem1376482)). Qed.
Lemma lem1376484 : term48.
Proof. exact (EQ_MP (@lem1376483) (@lem0)). Qed.
Lemma lem1376485 : term38.
Proof. exact (EQ_MP (@lem1376432) (@lem1376484)). Qed.
Lemma lem1376486 : term37.
Proof. exact (EQ_MP (@lem1376402) (@lem1376485)). Qed.
