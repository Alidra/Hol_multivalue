Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import TREAL_ADD_WELLDEF_term_abbrevs.
Require Import TREAL_ADD_SYM_EQ_spec.
Require Import TREAL_ADD_WELLDEFR_spec.
Require Import TREAL_EQ_TRANS_spec.
Require Import thm0_spec.
Require Import thm7_spec.
Lemma lem1333431 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1333432 (x1 : prod hreal hreal) (h1 : term0) : term1 x1.
Proof. exact (@lem1333431 h1 x1). Qed.
Lemma lem1333433 (x1 : prod hreal hreal) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1333434 (x1 : prod hreal hreal) (h1 : term0) : term2 x1.
Proof. exact (EQ_MP (@lem1333433 x1) (@lem1333432 x1 h1)). Qed.
Lemma lem1333435 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) : term3 x1 x2.
Proof. exact (@lem1333434 x1 h1 x2). Qed.
Lemma lem1333436 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term3 x1 x2) = (term4 x1 x2).
Proof. exact (eq_refl (term3 x1 x2)). Qed.
Lemma lem1333437 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) : term4 x1 x2.
Proof. exact (EQ_MP (@lem1333436 x1 x2) (@lem1333435 x1 x2 h1)). Qed.
Lemma lem1333438 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term5 x1 x2 y.
Proof. exact (@lem1333437 x1 x2 h1 y). Qed.
Lemma lem1333439 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : (term5 x1 x2 y) = (term6 x1 x2 y).
Proof. exact (eq_refl (term5 x1 x2 y)). Qed.
Lemma lem1333440 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term6 x1 x2 y.
Proof. exact (EQ_MP (@lem1333439 x1 x2 y) (@lem1333438 x1 x2 y h1)). Qed.
Lemma lem1333441 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : treal_eq x1 x2.
Proof. exact (h1). Qed.
Lemma lem1333442 (y : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) (h2 : treal_eq x1 x2) : term7 x1 x2 y.
Proof. exact (@lem1333440 x1 x2 y h1 (@lem1333441 x1 x2 h2)). Qed.
Lemma lem1333443 (y : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : treal_eq x1 x2) : term8 x1 x2 y.
Proof. exact (fun h0 : term0 => @lem1333442 y x1 x2 h0 h1). Qed.
Lemma lem1333444 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1333445 (y : prod hreal hreal) (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) (h2 : treal_eq x1 x2) : term7 x1 x2 y.
Proof. exact (@lem1333443 y x1 x2 h2 (@lem1333444 h1)). Qed.
Lemma lem1333446 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) (h1 : term0) : term6 x1 x2 y.
Proof. exact (fun h0 : treal_eq x1 x2 => @lem1333445 y x1 x2 h1 h0). Qed.
Lemma lem1333447 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (h1 : term0) : term4 x1 x2.
Proof. exact (fun y : prod hreal hreal => @lem1333446 x1 x2 y h1). Qed.
Lemma lem1333448 (x1 : prod hreal hreal) (h1 : term0) : term2 x1.
Proof. exact (fun x2 : prod hreal hreal => @lem1333447 x1 x2 h1). Qed.
Lemma lem1333449 (h1 : term0) : term0.
Proof. exact (fun x1 : prod hreal hreal => @lem1333448 x1 h1). Qed.
Lemma lem1333450 : term9.
Proof. exact (fun h0 : term0 => @lem1333449 h0). Qed.
Lemma lem1333451 : term0.
Proof. exact (@lem1333450 (@lem1333430)). Qed.
Lemma lem1333452 (x1 : prod hreal hreal) : term1 x1.
Proof. exact (@lem1333451 x1). Qed.
Lemma lem1333453 (x1 : prod hreal hreal) : (term1 x1) = (term2 x1).
Proof. exact (eq_refl (term1 x1)). Qed.
Lemma lem1333454 (x1 : prod hreal hreal) : term2 x1.
Proof. exact (EQ_MP (@lem1333453 x1) (@lem1333452 x1)). Qed.
Lemma lem1333455 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term3 x1 x2.
Proof. exact (@lem1333454 x1 x2). Qed.
Lemma lem1333456 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (term3 x1 x2) = (term4 x1 x2).
Proof. exact (eq_refl (term3 x1 x2)). Qed.
Lemma lem1333457 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term4 x1 x2.
Proof. exact (EQ_MP (@lem1333456 x1 x2) (@lem1333455 x1 x2)). Qed.
Lemma lem1333458 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : term5 x1 x2 y.
Proof. exact (@lem1333457 x1 x2 y). Qed.
Lemma lem1333459 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : (term5 x1 x2 y) = (term6 x1 x2 y).
Proof. exact (eq_refl (term5 x1 x2 y)). Qed.
Lemma lem1333461 (x : prod hreal hreal) : term10 x.
Proof. exact (@lem1327521 x). Qed.
Lemma lem1333462 (x : prod hreal hreal) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1333463 (x : prod hreal hreal) : term11 x.
Proof. exact (EQ_MP (@lem1333462 x) (@lem1333461 x)). Qed.
Lemma lem1333464 (x : prod hreal hreal) (y : prod hreal hreal) : term12 x y.
Proof. exact (@lem1333463 x y). Qed.
Lemma lem1333465 (y : prod hreal hreal) (x : prod hreal hreal) : (term12 x y) = ((treal_add x y) = (treal_add y x)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1333467 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1333468 (x : prod hreal hreal) (h1 : term13) : term14 x.
Proof. exact (@lem1333467 h1 x). Qed.
Lemma lem1333469 (x : prod hreal hreal) : (term14 x) = (term15 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1333470 (x : prod hreal hreal) (h1 : term13) : term15 x.
Proof. exact (EQ_MP (@lem1333469 x) (@lem1333468 x h1)). Qed.
Lemma lem1333471 (x : prod hreal hreal) (y : prod hreal hreal) (h1 : term13) : term16 x y.
Proof. exact (@lem1333470 x h1 y). Qed.
Lemma lem1333472 (y : prod hreal hreal) (x : prod hreal hreal) : (term16 x y) = (term17 y x).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1333473 (y : prod hreal hreal) (x : prod hreal hreal) (h1 : term13) : term17 y x.
Proof. exact (EQ_MP (@lem1333472 y x) (@lem1333471 x y h1)). Qed.
Lemma lem1333474 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) : term18 y x z.
Proof. exact (@lem1333473 y x h1 z). Qed.
Lemma lem1333475 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) : (term18 y x z) = (term19 y x z).
Proof. exact (eq_refl (term18 y x z)). Qed.
Lemma lem1333476 (y : prod hreal hreal) (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) : term19 y x z.
Proof. exact (EQ_MP (@lem1333475 y x z) (@lem1333474 y x z h1)). Qed.
Lemma lem1333477 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term20 x y z) : term20 x y z.
Proof. exact (h1). Qed.
Lemma lem1333478 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) (h2 : term20 x y z) : treal_eq x z.
Proof. exact (@lem1333476 y x z h1 (@lem1333477 x y z h2)). Qed.
Lemma lem1333479 (x : prod hreal hreal) (y : prod hreal hreal) (z : prod hreal hreal) (h1 : term20 x y z) : term21 x z.
Proof. exact (fun h0 : term13 => @lem1333478 x y z h0 h1). Qed.
Lemma lem1333480 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term22 x z) : term22 x z.
Proof. exact (h1). Qed.
Lemma lem1333481 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term22 x z) : term21 x z.
Proof. exact (ex_elim (@lem1333480 x z h1) (fun y : prod hreal hreal => fun h0 : term23 x z y => @lem1333479 x y z h0)). Qed.
Lemma lem1333482 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1333483 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) (h2 : term22 x z) : treal_eq x z.
Proof. exact (@lem1333481 x z h2 (@lem1333482 h1)). Qed.
Lemma lem1333484 (x : prod hreal hreal) (z : prod hreal hreal) (h1 : term13) : term24 x z.
Proof. exact (fun h0 : term22 x z => @lem1333483 x z h1 h0). Qed.
Lemma lem1333485 (x : prod hreal hreal) (h1 : term13) : term25 x.
Proof. exact (fun z : prod hreal hreal => @lem1333484 x z h1). Qed.
Lemma lem1333486 (h1 : term13) : term26.
Proof. exact (fun x : prod hreal hreal => @lem1333485 x h1). Qed.
Lemma lem1333487 : term27.
Proof. exact (fun h0 : term13 => @lem1333486 h0). Qed.
Lemma lem1333488 : term26.
Proof. exact (@lem1333487 (@lem1326778)). Qed.
Lemma lem1333489 (x : prod hreal hreal) : term28 x.
Proof. exact (@lem1333488 x). Qed.
Lemma lem1333490 (x : prod hreal hreal) : (term28 x) = (term25 x).
Proof. exact (eq_refl (term28 x)). Qed.
Lemma lem1333491 (x : prod hreal hreal) : term25 x.
Proof. exact (EQ_MP (@lem1333490 x) (@lem1333489 x)). Qed.
Lemma lem1333492 (x : prod hreal hreal) (z : prod hreal hreal) : term29 x z.
Proof. exact (@lem1333491 x z). Qed.
Lemma lem1333493 (x : prod hreal hreal) (z : prod hreal hreal) : (term29 x z) = (term24 x z).
Proof. exact (eq_refl (term29 x z)). Qed.
Lemma lem1333495 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term30 x1 x2 y1 y2.
Proof. exact (h1). Qed.
Lemma lem1333497 (x : prod hreal hreal) (z : prod hreal hreal) : term24 x z.
Proof. exact (EQ_MP (@lem1333493 x z) (@lem1333492 x z)). Qed.
Lemma lem1333498 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term31 x1 y1 x2 y2.
Proof. exact (@lem1333497 (treal_add x1 y1) (treal_add x2 y2)). Qed.
Lemma lem1333500 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_add x y) = (treal_add y x).
Proof. exact (EQ_MP (@lem1333465 y x) (@lem1333464 x y)). Qed.
Lemma lem1333501 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (treal_add x1 y1) = (treal_add y1 x1).
Proof. exact (@lem1333500 y1 x1). Qed.
Lemma lem1333502 : treal_eq = treal_eq.
Proof. exact (eq_refl treal_eq). Qed.
Lemma lem1333503 (y1 : prod hreal hreal) (x1 : prod hreal hreal) : (term32 x1 y1) = (term32 y1 x1).
Proof. exact (MK_COMB (@lem1333502) (@lem1333501 y1 x1)). Qed.
Lemma lem1333505 (y : prod hreal hreal) (x : prod hreal hreal) : (treal_add x y) = (treal_add y x).
Proof. exact (EQ_MP (@lem1333465 y x) (@lem1333464 x y)). Qed.
Lemma lem1333506 (y2 : prod hreal hreal) (x1 : prod hreal hreal) : (treal_add x1 y2) = (treal_add y2 x1).
Proof. exact (@lem1333505 y2 x1). Qed.
Lemma lem1333507 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) : (term33 y1 x1 y2) = (term7 y1 y2 x1).
Proof. exact (MK_COMB (@lem1333503 y1 x1) (@lem1333506 y2 x1)). Qed.
Lemma lem1333508 (y1 : prod hreal hreal) (x1 : prod hreal hreal) (y2 : prod hreal hreal) : (term7 y1 y2 x1) = (term33 y1 x1 y2).
Proof. exact (SYM (@lem1333507 y1 y2 x1)). Qed.
Lemma lem1333510 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : term6 x1 x2 y.
Proof. exact (EQ_MP (@lem1333459 x1 x2 y) (@lem1333458 x1 x2 y)). Qed.
Lemma lem1333511 (y1 : prod hreal hreal) (y2 : prod hreal hreal) (x1 : prod hreal hreal) : term6 y1 y2 x1.
Proof. exact (@lem1333510 y1 y2 x1). Qed.
Lemma lem1333513 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y : prod hreal hreal) : term6 x1 x2 y.
Proof. exact (EQ_MP (@lem1333459 x1 x2 y) (@lem1333458 x1 x2 y)). Qed.
Lemma lem1333514 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term6 x1 x2 y2.
Proof. exact (@lem1333513 x1 x2 y2). Qed.
Lemma lem1333515 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq y1 y2.
Proof. exact (proj2 (@lem1333495 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333516 (y1 : prod hreal hreal) (y2 : prod hreal hreal) : (treal_eq y1 y2) = ((treal_eq y1 y2) = True).
Proof. exact (@lem7 (treal_eq y1 y2)). Qed.
Lemma lem1333522 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : (treal_eq y1 y2) = True.
Proof. exact (EQ_MP (@lem1333516 y1 y2) (@lem1333515 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333523 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : True = (treal_eq y1 y2).
Proof. exact (SYM (@lem1333522 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333524 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq y1 y2.
Proof. exact (EQ_MP (@lem1333523 x1 x2 y1 y2 h1) (@lem0)). Qed.
Lemma lem1333528 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq x1 x2.
Proof. exact (proj1 (@lem1333495 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333529 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : (treal_eq x1 x2) = ((treal_eq x1 x2) = True).
Proof. exact (@lem7 (treal_eq x1 x2)). Qed.
Lemma lem1333532 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : (treal_eq x1 x2) = True.
Proof. exact (EQ_MP (@lem1333529 x1 x2) (@lem1333528 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333533 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : True = (treal_eq x1 x2).
Proof. exact (SYM (@lem1333532 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333534 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : treal_eq x1 x2.
Proof. exact (EQ_MP (@lem1333533 x1 x2 y1 y2 h1) (@lem0)). Qed.
Lemma lem1333535 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term7 x1 x2 y2.
Proof. exact (@lem1333514 x1 x2 y2 (@lem1333534 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333536 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term7 y1 y2 x1.
Proof. exact (@lem1333511 y1 y2 x1 (@lem1333524 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333537 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term33 y1 x1 y2.
Proof. exact (EQ_MP (@lem1333508 y1 x1 y2) (@lem1333536 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333538 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term34 y1 x1 x2 y2.
Proof. exact (conj (@lem1333537 x1 x2 y1 y2 h1) (@lem1333535 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333539 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term35 x1 y1 x2 y2.
Proof. exact (ex_intro (term36 x1 y1 x2 y2) (treal_add x1 y2) (@lem1333538 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333540 (x1 : prod hreal hreal) (x2 : prod hreal hreal) (y1 : prod hreal hreal) (y2 : prod hreal hreal) (h1 : term30 x1 x2 y1 y2) : term37 x1 y1 x2 y2.
Proof. exact (@lem1333498 x1 y1 x2 y2 (@lem1333539 x1 x2 y1 y2 h1)). Qed.
Lemma lem1333541 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) (y2 : prod hreal hreal) : term38 x1 y1 x2 y2.
Proof. exact (fun h0 : term30 x1 x2 y1 y2 => @lem1333540 x1 x2 y1 y2 h0). Qed.
Lemma lem1333546 (x1 : prod hreal hreal) (y1 : prod hreal hreal) (x2 : prod hreal hreal) : term39 x1 y1 x2.
Proof. exact (fun y2 : prod hreal hreal => @lem1333541 x1 y1 x2 y2). Qed.
Lemma lem1333551 (x1 : prod hreal hreal) (x2 : prod hreal hreal) : term40 x1 x2.
Proof. exact (fun y1 : prod hreal hreal => @lem1333546 x1 y1 x2). Qed.
Lemma lem1333556 (x1 : prod hreal hreal) : term41 x1.
Proof. exact (fun x2 : prod hreal hreal => @lem1333551 x1 x2). Qed.
Lemma lem1333561 : term42.
Proof. exact (fun x1 : prod hreal hreal => @lem1333556 x1). Qed.
