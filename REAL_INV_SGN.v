Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_SGN_term_abbrevs.
Require Import REAL_INV_NEG_spec.
Require Import TREAL_INV_0_spec.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm1340072_spec.
Require Import thm13473_spec.
Require Import thm1592014_spec.
Require Import thm1592030_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1772291 (x : real) : term0 x.
Proof. exact (@lem1590208 x). Qed.
Lemma lem1772292 (x : real) : (term0 x) = ((term1 x) = (term2 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1772294 (x : real) : term3 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1772295 (x : real) : (term3 x) = ((real_sgn x) = (term4 x)).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem1772300 (x : real) : (real_sgn x) = (term4 x).
Proof. exact (EQ_MP (@lem1772295 x) (@lem1772294 x)). Qed.
Lemma lem1772301 : real_inv = real_inv.
Proof. exact (eq_refl real_inv). Qed.
Lemma lem1772302 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1772301) (@lem1772300 x)). Qed.
Lemma lem1772303 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1772304 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1772303) (@lem1772302 x)). Qed.
Lemma lem1772306 (x : real) : (real_sgn x) = (term4 x).
Proof. exact (EQ_MP (@lem1772295 x) (@lem1772294 x)). Qed.
Lemma lem1772307 (x : real) : ((term5 x) = (real_sgn x)) = ((term6 x) = (term4 x)).
Proof. exact (MK_COMB (@lem1772304 x) (@lem1772306 x)). Qed.
Lemma lem1772310 (x : real) : ((term6 x) = (term4 x)) = ((term5 x) = (real_sgn x)).
Proof. exact (SYM (@lem1772307 x)). Qed.
Lemma lem1772311 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term9 _476 _475 _474 _477) = (term10 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1772312 (_474 : real) (_475 : Prop) (_477 : real) : (term11 _475 _474 _477) = (term12 _474 _475 _477).
Proof. exact (@lem1772311 _474 _475 term13 _477). Qed.
Lemma lem1772313 (x : real) : (term14 x) = (term15 x).
Proof. exact (@lem1772312 term16 (term17 x) (term18 x)). Qed.
Lemma lem1772314 (x : real) : (term19 x) = ((term20 x) = (term18 x)).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1772315 (x : real) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1772316 (x : real) : (term22 x) = (term23 x).
Proof. exact (MK_COMB (@lem1772315 x) (@lem1772314 x)). Qed.
Lemma lem1772317 : term24 = (term25 = term16).
Proof. exact (eq_refl term24). Qed.
Lemma lem1772318 (x : real) : (term26 x) = (term26 x).
Proof. exact (eq_refl (term26 x)). Qed.
Lemma lem1772319 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1772318 x) (@lem1772317)). Qed.
Lemma lem1772320 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1772321 (x : real) : (term29 x) = (term30 x).
Proof. exact (MK_COMB (@lem1772320) (@lem1772319 x)). Qed.
Lemma lem1772322 (x : real) : (term15 x) = (term31 x).
Proof. exact (MK_COMB (@lem1772321 x) (@lem1772316 x)). Qed.
Lemma lem1772323 (x : real) : (term14 x) = ((term6 x) = (term4 x)).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1772324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1772325 (x : real) : (term32 x) = (term33 x).
Proof. exact (MK_COMB (@lem1772324) (@lem1772323 x)). Qed.
Lemma lem1772326 (x : real) : ((term14 x) = (term15 x)) = (((term6 x) = (term4 x)) = (term31 x)).
Proof. exact (MK_COMB (@lem1772325 x) (@lem1772322 x)). Qed.
Lemma lem1772327 (x : real) : ((term6 x) = (term4 x)) = (term31 x).
Proof. exact (EQ_MP (@lem1772326 x) (@lem1772313 x)). Qed.
Lemma lem1772328 (x : real) : (term31 x) = ((term6 x) = (term4 x)).
Proof. exact (SYM (@lem1772327 x)). Qed.
Lemma lem1772363 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term9 _476 _475 _474 _477) = (term10 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1772364 (_474 : real) (_475 : Prop) (_477 : real) : (term11 _475 _474 _477) = (term12 _474 _475 _477).
Proof. exact (@lem1772363 _474 _475 term13 _477). Qed.
Lemma lem1772365 (x : real) : (term19 x) = (term34 x).
Proof. exact (@lem1772364 term35 (term36 x) term37). Qed.
Lemma lem1772366 : term38 = (term39 = term37).
Proof. exact (eq_refl term38). Qed.
Lemma lem1772367 (x : real) : (term40 x) = (term40 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1772368 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1772367 x) (@lem1772366)). Qed.
Lemma lem1772369 : term43 = (term44 = term35).
Proof. exact (eq_refl term43). Qed.
Lemma lem1772370 (x : real) : (term45 x) = (term45 x).
Proof. exact (eq_refl (term45 x)). Qed.
Lemma lem1772371 (x : real) : (term46 x) = (term47 x).
Proof. exact (MK_COMB (@lem1772370 x) (@lem1772369)). Qed.
Lemma lem1772372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1772373 (x : real) : (term48 x) = (term49 x).
Proof. exact (MK_COMB (@lem1772372) (@lem1772371 x)). Qed.
Lemma lem1772374 (x : real) : (term34 x) = (term50 x).
Proof. exact (MK_COMB (@lem1772373 x) (@lem1772368 x)). Qed.
Lemma lem1772375 (x : real) : (term19 x) = ((term20 x) = (term18 x)).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem1772376 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1772377 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1772376) (@lem1772375 x)). Qed.
Lemma lem1772378 (x : real) : ((term19 x) = (term34 x)) = (((term20 x) = (term18 x)) = (term50 x)).
Proof. exact (MK_COMB (@lem1772377 x) (@lem1772374 x)). Qed.
Lemma lem1772379 (x : real) : ((term20 x) = (term18 x)) = (term50 x).
Proof. exact (EQ_MP (@lem1772378 x) (@lem1772365 x)). Qed.
Lemma lem1772380 (x : real) : (term50 x) = ((term20 x) = (term18 x)).
Proof. exact (SYM (@lem1772379 x)). Qed.
Lemma lem1772418 : term25 = term16.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
Lemma lem1772419 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1772420 : term53 = term54.
Proof. exact (MK_COMB (@lem1772419) (@lem1772418)). Qed.
Lemma lem1772421 : term16 = term16.
Proof. exact (eq_refl term16). Qed.
Lemma lem1772422 : (term25 = term16) = (term16 = term16).
Proof. exact (MK_COMB (@lem1772420) (@lem1772421)). Qed.
Lemma lem1772424 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1772425 (x : real) : (x = x) = True.
Proof. exact (@lem1772424 real x). Qed.
Lemma lem1772426 : (term16 = term16) = True.
Proof. exact (@lem1772425 term16). Qed.
Lemma lem1772427 : (term25 = term16) = True.
Proof. exact (TRANS (@lem1772422) (@lem1772426)). Qed.
Lemma lem1772428 : True = (term25 = term16).
Proof. exact (SYM (@lem1772427)). Qed.
Lemma lem1772433 (x : real) : (term1 x) = (term2 x).
Proof. exact (EQ_MP (@lem1772292 x) (@lem1772291 x)). Qed.
Lemma lem1772434 : term44 = term55.
Proof. exact (@lem1772433 term16). Qed.
Lemma lem1772436 : term25 = term16.
Proof. exact (@lem1592014 (@lem1592030)). Qed.
Lemma lem1772437 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1772438 : term55 = term35.
Proof. exact (MK_COMB (@lem1772437) (@lem1772436)). Qed.
Lemma lem1772439 : term44 = term35.
Proof. exact (TRANS (@lem1772434) (@lem1772438)). Qed.
Lemma lem1772440 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1772441 : term56 = term57.
Proof. exact (MK_COMB (@lem1772440) (@lem1772439)). Qed.
Lemma lem1772442 : term35 = term35.
Proof. exact (eq_refl term35). Qed.
Lemma lem1772443 : (term44 = term35) = (term35 = term35).
Proof. exact (MK_COMB (@lem1772441) (@lem1772442)). Qed.
Lemma lem1772445 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1772446 (x : real) : (x = x) = True.
Proof. exact (@lem1772445 real x). Qed.
Lemma lem1772447 : (term35 = term35) = True.
Proof. exact (@lem1772446 term35). Qed.
Lemma lem1772448 : (term44 = term35) = True.
Proof. exact (TRANS (@lem1772443) (@lem1772447)). Qed.
Lemma lem1772449 : True = (term44 = term35).
Proof. exact (SYM (@lem1772448)). Qed.
Lemma lem1772454 : term39 = term37.
Proof. exact (EQ_MP (@lem1340072) (@lem1331743)). Qed.
Lemma lem1772455 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1772456 : term58 = term59.
Proof. exact (MK_COMB (@lem1772455) (@lem1772454)). Qed.
Lemma lem1772457 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem1772458 : (term39 = term37) = (term37 = term37).
Proof. exact (MK_COMB (@lem1772456) (@lem1772457)). Qed.
Lemma lem1772460 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1772461 (x : real) : (x = x) = True.
Proof. exact (@lem1772460 real x). Qed.
Lemma lem1772462 : (term37 = term37) = True.
Proof. exact (@lem1772461 term37). Qed.
Lemma lem1772463 : (term39 = term37) = True.
Proof. exact (TRANS (@lem1772458) (@lem1772462)). Qed.
Lemma lem1772464 : True = (term39 = term37).
Proof. exact (SYM (@lem1772463)). Qed.
Lemma lem1772466 : term39 = term37.
Proof. exact (EQ_MP (@lem1772464) (@lem0)). Qed.
Lemma lem1772467 (x : real) : term42 x.
Proof. exact (fun h0 : term60 x => @lem1772466). Qed.
Lemma lem1772468 : term44 = term35.
Proof. exact (EQ_MP (@lem1772449) (@lem0)). Qed.
Lemma lem1772469 (x : real) : term47 x.
Proof. exact (fun h0 : term36 x => @lem1772468). Qed.
Lemma lem1772470 (x : real) : term50 x.
Proof. exact (conj (@lem1772469 x) (@lem1772467 x)). Qed.
Lemma lem1772472 (x : real) : (term20 x) = (term18 x).
Proof. exact (EQ_MP (@lem1772380 x) (@lem1772470 x)). Qed.
Lemma lem1772473 (x : real) : term23 x.
Proof. exact (fun h0 : term61 x => @lem1772472 x). Qed.
Lemma lem1772474 : term25 = term16.
Proof. exact (EQ_MP (@lem1772428) (@lem0)). Qed.
Lemma lem1772475 (x : real) : term28 x.
Proof. exact (fun h0 : term17 x => @lem1772474). Qed.
Lemma lem1772476 (x : real) : term31 x.
Proof. exact (conj (@lem1772475 x) (@lem1772473 x)). Qed.
Lemma lem1772477 (x : real) : (term6 x) = (term4 x).
Proof. exact (EQ_MP (@lem1772328 x) (@lem1772476 x)). Qed.
Lemma lem1772478 (x : real) : (term5 x) = (real_sgn x).
Proof. exact (EQ_MP (@lem1772310 x) (@lem1772477 x)). Qed.
Lemma lem1772483 : term62.
Proof. exact (fun x : real => @lem1772478 x). Qed.
