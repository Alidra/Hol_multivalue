Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import treal_inv_term_abbrevs.
Require Import FST_spec.
Require Import SND_spec.
Lemma lem1325454 : treal_inv = term0.
Proof. exact (@treal_inv_def). Qed.
Lemma lem1325455 (_23674 : prod hreal hreal) : _23674 = _23674.
Proof. exact (eq_refl _23674). Qed.
Lemma lem1325456 (_23674 : prod hreal hreal) : (treal_inv _23674) = (term1 _23674).
Proof. exact (MK_COMB (@lem1325454) (@lem1325455 _23674)). Qed.
Lemma lem1325457 (_23674 : prod hreal hreal) : (term1 _23674) = (term2 _23674).
Proof. exact (eq_refl (term1 _23674)). Qed.
Lemma lem1325458 (_23674 : prod hreal hreal) : (treal_inv _23674) = (term2 _23674).
Proof. exact (TRANS (@lem1325456 _23674) (@lem1325457 _23674)). Qed.
Lemma lem1325459 : term3.
Proof. exact (fun _23674 : prod hreal hreal => @lem1325458 _23674). Qed.
Lemma lem1325460 (_23674 : prod hreal hreal) : term4 _23674.
Proof. exact (@lem1325459 _23674). Qed.
Lemma lem1325461 (_23674 : prod hreal hreal) : (term4 _23674) = ((treal_inv _23674) = (term2 _23674)).
Proof. exact (eq_refl (term4 _23674)). Qed.
Lemma lem1325462 (_23674 : prod hreal hreal) : (treal_inv _23674) = (term2 _23674).
Proof. exact (EQ_MP (@lem1325461 _23674) (@lem1325460 _23674)). Qed.
Lemma lem1325463 (x : hreal) (y : hreal) : (term5 x y) = (term6 x y).
Proof. exact (@lem1325462 (@pair hreal hreal x y)). Qed.
Lemma lem1325464 {A B : Type'} (x : A) : term7 A B x.
Proof. exact (@lem48019 A B x). Qed.
Lemma lem1325465 {A B : Type'} (x : A) : (term7 A B x) = (term8 A B x).
Proof. exact (eq_refl (term7 A B x)). Qed.
Lemma lem1325466 {A B : Type'} (x : A) : term8 A B x.
Proof. exact (EQ_MP (@lem1325465 A B x) (@lem1325464 A B x)). Qed.
Lemma lem1325467 {A B : Type'} (x : A) (y : B) : term9 A B x y.
Proof. exact (@lem1325466 A B x y). Qed.
Lemma lem1325468 {A B : Type'} (x : A) (y : B) : (term9 A B x y) = ((term10 A B x y) = y).
Proof. exact (eq_refl (term9 A B x y)). Qed.
Lemma lem1325470 {A B : Type'} (x : A) : term11 A B x.
Proof. exact (@lem47827 A B x). Qed.
Lemma lem1325471 {A B : Type'} (x : A) : (term11 A B x) = (term12 A B x).
Proof. exact (eq_refl (term11 A B x)). Qed.
Lemma lem1325472 {A B : Type'} (x : A) : term12 A B x.
Proof. exact (EQ_MP (@lem1325471 A B x) (@lem1325470 A B x)). Qed.
Lemma lem1325473 {A B : Type'} (x : A) (y : B) : term13 A B x y.
Proof. exact (@lem1325472 A B x y). Qed.
Lemma lem1325474 {A B : Type'} (y : B) (x : A) : (term13 A B x y) = ((term14 A B x y) = x).
Proof. exact (eq_refl (term13 A B x y)). Qed.
Lemma lem1325477 {A B : Type'} (y : B) (x : A) : (term14 A B x y) = x.
Proof. exact (EQ_MP (@lem1325474 A B y x) (@lem1325473 A B x y)). Qed.
Lemma lem1325478 (y : hreal) (x : hreal) : (term15 x y) = x.
Proof. exact (@lem1325477 hreal hreal y x). Qed.
Lemma lem1325479 (x : hreal) (y : hreal) : x = (term15 x y).
Proof. exact (SYM (@lem1325478 y x)). Qed.
Lemma lem1325481 {A B : Type'} (x : A) (y : B) : (term10 A B x y) = y.
Proof. exact (EQ_MP (@lem1325468 A B x y) (@lem1325467 A B x y)). Qed.
Lemma lem1325482 (x : hreal) (y : hreal) : (term16 x y) = y.
Proof. exact (@lem1325481 hreal hreal x y). Qed.
Lemma lem1325483 (x : hreal) (y : hreal) : y = (term16 x y).
Proof. exact (SYM (@lem1325482 x y)). Qed.
Lemma lem1325484 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1325485 (x : hreal) (y : hreal) : (term18 x) = (term19 x y).
Proof. exact (MK_COMB (@lem1325484) (@lem1325479 x y)). Qed.
Lemma lem1325486 (x : hreal) (y : hreal) : (term19 x y) = (term20 x y).
Proof. exact (eq_refl (term19 x y)). Qed.
Lemma lem1325487 (x : hreal) : (term21 x) = (term21 x).
Proof. exact (eq_refl (term21 x)). Qed.
Lemma lem1325488 (x : hreal) (y : hreal) : ((term18 x) = (term19 x y)) = ((term18 x) = (term20 x y)).
Proof. exact (MK_COMB (@lem1325487 x) (@lem1325486 x y)). Qed.
Lemma lem1325489 (x : hreal) : (term18 x) = (term22 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1325490 : (@eq (hreal -> prod hreal hreal)) = (@eq (hreal -> prod hreal hreal)).
Proof. exact (eq_refl (@eq (hreal -> prod hreal hreal))). Qed.
Lemma lem1325491 (x : hreal) : (term21 x) = (term23 x).
Proof. exact (MK_COMB (@lem1325490) (@lem1325489 x)). Qed.
Lemma lem1325492 (x : hreal) (y : hreal) : (term20 x y) = (term20 x y).
Proof. exact (eq_refl (term20 x y)). Qed.
Lemma lem1325493 (x : hreal) (y : hreal) : ((term18 x) = (term20 x y)) = ((term22 x) = (term20 x y)).
Proof. exact (MK_COMB (@lem1325491 x) (@lem1325492 x y)). Qed.
Lemma lem1325494 (x : hreal) (y : hreal) : ((term18 x) = (term19 x y)) = ((term22 x) = (term20 x y)).
Proof. exact (TRANS (@lem1325488 x y) (@lem1325493 x y)). Qed.
Lemma lem1325495 (x : hreal) (y : hreal) : (term22 x) = (term20 x y).
Proof. exact (EQ_MP (@lem1325494 x y) (@lem1325485 x y)). Qed.
Lemma lem1325496 (x : hreal) (y : hreal) : (term24 x y) = (term25 x y).
Proof. exact (MK_COMB (@lem1325495 x y) (@lem1325483 x y)). Qed.
Lemma lem1325497 (x : hreal) (y : hreal) : (term25 x y) = (term6 x y).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem1325498 (x : hreal) (y : hreal) : (term26 x y) = (term26 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1325499 (x : hreal) (y : hreal) : ((term24 x y) = (term25 x y)) = ((term24 x y) = (term6 x y)).
Proof. exact (MK_COMB (@lem1325498 x y) (@lem1325497 x y)). Qed.
Lemma lem1325500 (y : hreal) (x : hreal) : (term24 x y) = (term27 y x).
Proof. exact (eq_refl (term24 x y)). Qed.
Lemma lem1325501 : (@eq (prod hreal hreal)) = (@eq (prod hreal hreal)).
Proof. exact (eq_refl (@eq (prod hreal hreal))). Qed.
Lemma lem1325502 (y : hreal) (x : hreal) : (term26 x y) = (term28 y x).
Proof. exact (MK_COMB (@lem1325501) (@lem1325500 y x)). Qed.
Lemma lem1325503 (x : hreal) (y : hreal) : (term6 x y) = (term6 x y).
Proof. exact (eq_refl (term6 x y)). Qed.
Lemma lem1325504 (x : hreal) (y : hreal) : ((term24 x y) = (term6 x y)) = ((term27 y x) = (term6 x y)).
Proof. exact (MK_COMB (@lem1325502 y x) (@lem1325503 x y)). Qed.
Lemma lem1325505 (x : hreal) (y : hreal) : ((term24 x y) = (term25 x y)) = ((term27 y x) = (term6 x y)).
Proof. exact (TRANS (@lem1325499 x y) (@lem1325504 x y)). Qed.
Lemma lem1325506 (x : hreal) (y : hreal) : (term27 y x) = (term6 x y).
Proof. exact (EQ_MP (@lem1325505 x y) (@lem1325496 x y)). Qed.
Lemma lem1325507 (y : hreal) (x : hreal) : (term6 x y) = (term27 y x).
Proof. exact (SYM (@lem1325506 x y)). Qed.
Lemma lem1325508 (y : hreal) (x : hreal) : (term5 x y) = (term27 y x).
Proof. exact (TRANS (@lem1325463 x y) (@lem1325507 y x)). Qed.
Lemma lem1325509 (y : hreal) : term29 y.
Proof. exact (fun x : hreal => @lem1325508 y x). Qed.
Lemma lem1325510 : term30.
Proof. exact (fun y : hreal => @lem1325509 y). Qed.
