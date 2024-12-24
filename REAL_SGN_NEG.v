Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SGN_NEG_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import real_sgn_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm12653_spec.
Require Import thm1366270_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm1834_spec.
Require Import thm18392_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm20234_spec.
Require Import thm20420_spec.
Require Import thm20421_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Require Import thm996238_spec.
Lemma lem1710424 (x : real) : term0 x.
Proof. exact (@lem1710164 x). Qed.
Lemma lem1710425 (x : real) : (term0 x) = ((real_sgn x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1710434 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1710425 x) (@lem1710424 x)). Qed.
Lemma lem1710435 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1710434 (real_neg x)). Qed.
Lemma lem1710436 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710437 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1710436) (@lem1710435 x)). Qed.
Lemma lem1710439 (x : real) : (real_sgn x) = (term1 x).
Proof. exact (EQ_MP (@lem1710425 x) (@lem1710424 x)). Qed.
Lemma lem1710440 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710441 (x : real) : (term6 x) = (term7 x).
Proof. exact (MK_COMB (@lem1710440) (@lem1710439 x)). Qed.
Lemma lem1710442 (x : real) : ((term2 x) = (term6 x)) = ((term3 x) = (term7 x)).
Proof. exact (MK_COMB (@lem1710437 x) (@lem1710441 x)). Qed.
Lemma lem1710445 : term8 = term9.
Proof. exact (fun_ext (fun x : real => @lem1710442 x)). Qed.
Lemma lem1710446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1710447 : term10 = term11.
Proof. exact (MK_COMB (@lem1710446) (@lem1710445)). Qed.
Lemma lem1710452 : term11 = term10.
Proof. exact (SYM (@lem1710447)). Qed.
Lemma lem1710461 (P : real -> Prop) : (term12 P) = (term13 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1710462 : term14 = term15.
Proof. exact (@lem1710461 term9). Qed.
Lemma lem1710463 (x : real) : (term16 x) = ((term3 x) = (term7 x)).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1710464 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710466 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1710464) (@lem1710463 x)). Qed.
Lemma lem1710467 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1710466 x)). Qed.
Lemma lem1710468 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1710469 : term15 = term21.
Proof. exact (MK_COMB (@lem1710468) (@lem1710467)). Qed.
Lemma lem1710471 : term14 = term21.
Proof. exact (TRANS (@lem1710462) (@lem1710469)). Qed.
Lemma lem1710475 (x : real) (h1 : (term22 x) = False) : (term22 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710476 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710477 (x : real) (h1 : (term22 x) = False) : (term23 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710476) (@lem1710475 x h1)). Qed.
Lemma lem1710478 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1710479 (x : real) (h1 : (term22 x) = False) : (term25 x) = term26.
Proof. exact (MK_COMB (@lem1710477 x h1) (@lem1710478)). Qed.
Lemma lem1710480 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1710481 (x : real) (h1 : (term22 x) = False) : (term3 x) = (term28 x).
Proof. exact (MK_COMB (@lem1710479 x h1) (@lem1710480 x)). Qed.
Lemma lem1710483 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710484 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710483 real t1 t2). Qed.
Lemma lem1710485 (x : real) : (term28 x) = (term27 x).
Proof. exact (@lem1710484 term24 (term27 x)). Qed.
Lemma lem1710486 (x : real) (h1 : (term22 x) = False) : (term3 x) = (term27 x).
Proof. exact (TRANS (@lem1710481 x h1) (@lem1710485 x)). Qed.
Lemma lem1710487 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710488 (x : real) (h1 : (term22 x) = False) : (term5 x) = (term29 x).
Proof. exact (MK_COMB (@lem1710487) (@lem1710486 x h1)). Qed.
Lemma lem1710489 (x : real) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1710490 (x : real) (h1 : (term22 x) = False) : ((term3 x) = (term7 x)) = ((term27 x) = (term7 x)).
Proof. exact (MK_COMB (@lem1710488 x h1) (@lem1710489 x)). Qed.
Lemma lem1710493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710494 (x : real) (h1 : (term22 x) = False) : (term18 x) = (term30 x).
Proof. exact (MK_COMB (@lem1710493) (@lem1710490 x h1)). Qed.
Lemma lem1710495 (x : real) : term31 x.
Proof. exact (fun h0 : (term22 x) = False => @lem1710494 x h0). Qed.
Lemma lem1710497 (x : real) (h1 : (term22 x) = True) : (term22 x) = True.
Proof. exact (h1). Qed.
Lemma lem1710498 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710499 (x : real) (h1 : (term22 x) = True) : (term23 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1710498) (@lem1710497 x h1)). Qed.
Lemma lem1710500 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1710501 (x : real) (h1 : (term22 x) = True) : (term25 x) = term32.
Proof. exact (MK_COMB (@lem1710499 x h1) (@lem1710500)). Qed.
Lemma lem1710502 (x : real) : (term27 x) = (term27 x).
Proof. exact (eq_refl (term27 x)). Qed.
Lemma lem1710503 (x : real) (h1 : (term22 x) = True) : (term3 x) = (term33 x).
Proof. exact (MK_COMB (@lem1710501 x h1) (@lem1710502 x)). Qed.
Lemma lem1710505 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1710506 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1710505 real t2 t1). Qed.
Lemma lem1710507 (x : real) : (term33 x) = term24.
Proof. exact (@lem1710506 (term27 x) term24). Qed.
Lemma lem1710508 (x : real) (h1 : (term22 x) = True) : (term3 x) = term24.
Proof. exact (TRANS (@lem1710503 x h1) (@lem1710507 x)). Qed.
Lemma lem1710509 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710510 (x : real) (h1 : (term22 x) = True) : (term5 x) = term34.
Proof. exact (MK_COMB (@lem1710509) (@lem1710508 x h1)). Qed.
Lemma lem1710511 (x : real) : (term7 x) = (term7 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1710512 (x : real) (h1 : (term22 x) = True) : ((term3 x) = (term7 x)) = (term24 = (term7 x)).
Proof. exact (MK_COMB (@lem1710510 x h1) (@lem1710511 x)). Qed.
Lemma lem1710515 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710516 (x : real) (h1 : (term22 x) = True) : (term18 x) = (term35 x).
Proof. exact (MK_COMB (@lem1710515) (@lem1710512 x h1)). Qed.
Lemma lem1710517 (x : real) : term36 x.
Proof. exact (fun h0 : (term22 x) = True => @lem1710516 x h0). Qed.
Lemma lem1710518 (x : real) : term37 x.
Proof. exact (conj (@lem1710495 x) (@lem1710517 x)). Qed.
Lemma lem1710520 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term38 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1710521 (x : real) : term39 x.
Proof. exact (@lem1710520 (term18 x) (term35 x) (term22 x) (term30 x)). Qed.
Lemma lem1710536 (x : real) : (term18 x) = (term40 x).
Proof. exact (@lem1710521 x (@lem1710518 x)). Qed.
Lemma lem1710540 (x : real) (h1 : (term41 x) = False) : (term41 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710541 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710542 (x : real) (h1 : (term41 x) = False) : (term42 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710541) (@lem1710540 x h1)). Qed.
Lemma lem1710543 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1710544 (x : real) (h1 : (term41 x) = False) : (term43 x) = term26.
Proof. exact (MK_COMB (@lem1710542 x h1) (@lem1710543)). Qed.
Lemma lem1710545 (x : real) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1710546 (x : real) (h1 : (term41 x) = False) : (term1 x) = (term45 x).
Proof. exact (MK_COMB (@lem1710544 x h1) (@lem1710545 x)). Qed.
Lemma lem1710548 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710549 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710548 real t1 t2). Qed.
Lemma lem1710550 (x : real) : (term45 x) = (term44 x).
Proof. exact (@lem1710549 term24 (term44 x)). Qed.
Lemma lem1710551 (x : real) (h1 : (term41 x) = False) : (term1 x) = (term44 x).
Proof. exact (TRANS (@lem1710546 x h1) (@lem1710550 x)). Qed.
Lemma lem1710552 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710553 (x : real) (h1 : (term41 x) = False) : (term7 x) = (term46 x).
Proof. exact (MK_COMB (@lem1710552) (@lem1710551 x h1)). Qed.
Lemma lem1710554 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1710555 (x : real) (h1 : (term41 x) = False) : (term24 = (term7 x)) = (term24 = (term46 x)).
Proof. exact (MK_COMB (@lem1710554) (@lem1710553 x h1)). Qed.
Lemma lem1710558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710559 (x : real) (h1 : (term41 x) = False) : (term35 x) = (term47 x).
Proof. exact (MK_COMB (@lem1710558) (@lem1710555 x h1)). Qed.
Lemma lem1710560 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1710561 (x : real) (h1 : (term41 x) = False) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1710560 x) (@lem1710559 x h1)). Qed.
Lemma lem1710564 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710565 (x : real) (h1 : (term41 x) = False) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1710564) (@lem1710561 x h1)). Qed.
Lemma lem1710567 (x : real) (h1 : (term41 x) = False) : (term41 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710568 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710569 (x : real) (h1 : (term41 x) = False) : (term42 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710568) (@lem1710567 x h1)). Qed.
Lemma lem1710570 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1710571 (x : real) (h1 : (term41 x) = False) : (term43 x) = term26.
Proof. exact (MK_COMB (@lem1710569 x h1) (@lem1710570)). Qed.
Lemma lem1710572 (x : real) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1710573 (x : real) (h1 : (term41 x) = False) : (term1 x) = (term45 x).
Proof. exact (MK_COMB (@lem1710571 x h1) (@lem1710572 x)). Qed.
Lemma lem1710575 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710576 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710575 real t1 t2). Qed.
Lemma lem1710577 (x : real) : (term45 x) = (term44 x).
Proof. exact (@lem1710576 term24 (term44 x)). Qed.
Lemma lem1710578 (x : real) (h1 : (term41 x) = False) : (term1 x) = (term44 x).
Proof. exact (TRANS (@lem1710573 x h1) (@lem1710577 x)). Qed.
Lemma lem1710579 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710580 (x : real) (h1 : (term41 x) = False) : (term7 x) = (term46 x).
Proof. exact (MK_COMB (@lem1710579) (@lem1710578 x h1)). Qed.
Lemma lem1710581 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1710582 (x : real) (h1 : (term41 x) = False) : ((term27 x) = (term7 x)) = ((term27 x) = (term46 x)).
Proof. exact (MK_COMB (@lem1710581 x) (@lem1710580 x h1)). Qed.
Lemma lem1710585 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710586 (x : real) (h1 : (term41 x) = False) : (term30 x) = (term53 x).
Proof. exact (MK_COMB (@lem1710585) (@lem1710582 x h1)). Qed.
Lemma lem1710587 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1710588 (x : real) (h1 : (term41 x) = False) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1710587 x) (@lem1710586 x h1)). Qed.
Lemma lem1710591 (x : real) (h1 : (term41 x) = False) : (term40 x) = (term57 x).
Proof. exact (MK_COMB (@lem1710565 x h1) (@lem1710588 x h1)). Qed.
Lemma lem1710594 (x : real) : term58 x.
Proof. exact (fun h0 : (term41 x) = False => @lem1710591 x h0). Qed.
Lemma lem1710596 (x : real) (h1 : (term41 x) = True) : (term41 x) = True.
Proof. exact (h1). Qed.
Lemma lem1710597 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710598 (x : real) (h1 : (term41 x) = True) : (term42 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1710597) (@lem1710596 x h1)). Qed.
Lemma lem1710599 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1710600 (x : real) (h1 : (term41 x) = True) : (term43 x) = term32.
Proof. exact (MK_COMB (@lem1710598 x h1) (@lem1710599)). Qed.
Lemma lem1710601 (x : real) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1710602 (x : real) (h1 : (term41 x) = True) : (term1 x) = (term59 x).
Proof. exact (MK_COMB (@lem1710600 x h1) (@lem1710601 x)). Qed.
Lemma lem1710604 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1710605 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1710604 real t2 t1). Qed.
Lemma lem1710606 (x : real) : (term59 x) = term24.
Proof. exact (@lem1710605 (term44 x) term24). Qed.
Lemma lem1710607 (x : real) (h1 : (term41 x) = True) : (term1 x) = term24.
Proof. exact (TRANS (@lem1710602 x h1) (@lem1710606 x)). Qed.
Lemma lem1710608 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710609 (x : real) (h1 : (term41 x) = True) : (term7 x) = term60.
Proof. exact (MK_COMB (@lem1710608) (@lem1710607 x h1)). Qed.
Lemma lem1710610 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1710611 (x : real) (h1 : (term41 x) = True) : (term24 = (term7 x)) = (term24 = term60).
Proof. exact (MK_COMB (@lem1710610) (@lem1710609 x h1)). Qed.
Lemma lem1710614 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710615 (x : real) (h1 : (term41 x) = True) : (term35 x) = term61.
Proof. exact (MK_COMB (@lem1710614) (@lem1710611 x h1)). Qed.
Lemma lem1710616 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1710617 (x : real) (h1 : (term41 x) = True) : (term49 x) = (term62 x).
Proof. exact (MK_COMB (@lem1710616 x) (@lem1710615 x h1)). Qed.
Lemma lem1710620 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710621 (x : real) (h1 : (term41 x) = True) : (term51 x) = (term63 x).
Proof. exact (MK_COMB (@lem1710620) (@lem1710617 x h1)). Qed.
Lemma lem1710623 (x : real) (h1 : (term41 x) = True) : (term41 x) = True.
Proof. exact (h1). Qed.
Lemma lem1710624 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710625 (x : real) (h1 : (term41 x) = True) : (term42 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1710624) (@lem1710623 x h1)). Qed.
Lemma lem1710626 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1710627 (x : real) (h1 : (term41 x) = True) : (term43 x) = term32.
Proof. exact (MK_COMB (@lem1710625 x h1) (@lem1710626)). Qed.
Lemma lem1710628 (x : real) : (term44 x) = (term44 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1710629 (x : real) (h1 : (term41 x) = True) : (term1 x) = (term59 x).
Proof. exact (MK_COMB (@lem1710627 x h1) (@lem1710628 x)). Qed.
Lemma lem1710631 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1710632 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1710631 real t2 t1). Qed.
Lemma lem1710633 (x : real) : (term59 x) = term24.
Proof. exact (@lem1710632 (term44 x) term24). Qed.
Lemma lem1710634 (x : real) (h1 : (term41 x) = True) : (term1 x) = term24.
Proof. exact (TRANS (@lem1710629 x h1) (@lem1710633 x)). Qed.
Lemma lem1710635 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710636 (x : real) (h1 : (term41 x) = True) : (term7 x) = term60.
Proof. exact (MK_COMB (@lem1710635) (@lem1710634 x h1)). Qed.
Lemma lem1710637 (x : real) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem1710638 (x : real) (h1 : (term41 x) = True) : ((term27 x) = (term7 x)) = ((term27 x) = term60).
Proof. exact (MK_COMB (@lem1710637 x) (@lem1710636 x h1)). Qed.
Lemma lem1710641 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710642 (x : real) (h1 : (term41 x) = True) : (term30 x) = (term64 x).
Proof. exact (MK_COMB (@lem1710641) (@lem1710638 x h1)). Qed.
Lemma lem1710643 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1710644 (x : real) (h1 : (term41 x) = True) : (term55 x) = (term65 x).
Proof. exact (MK_COMB (@lem1710643 x) (@lem1710642 x h1)). Qed.
Lemma lem1710647 (x : real) (h1 : (term41 x) = True) : (term40 x) = (term66 x).
Proof. exact (MK_COMB (@lem1710621 x h1) (@lem1710644 x h1)). Qed.
Lemma lem1710650 (x : real) : term67 x.
Proof. exact (fun h0 : (term41 x) = True => @lem1710647 x h0). Qed.
Lemma lem1710651 (x : real) : term68 x.
Proof. exact (conj (@lem1710594 x) (@lem1710650 x)). Qed.
Lemma lem1710653 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term38 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1710654 (x : real) : term69 x.
Proof. exact (@lem1710653 (term40 x) (term66 x) (term41 x) (term57 x)). Qed.
Lemma lem1710669 (x : real) : (term40 x) = (term70 x).
Proof. exact (@lem1710654 x (@lem1710651 x)). Qed.
Lemma lem1710677 (x : real) (h1 : (term71 x) = False) : (term71 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710678 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710679 (x : real) (h1 : (term71 x) = False) : (term72 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710678) (@lem1710677 x h1)). Qed.
Lemma lem1710680 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710681 (x : real) (h1 : (term71 x) = False) : (term73 x) = term74.
Proof. exact (MK_COMB (@lem1710679 x h1) (@lem1710680)). Qed.
Lemma lem1710682 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710683 (x : real) (h1 : (term71 x) = False) : (term27 x) = term76.
Proof. exact (MK_COMB (@lem1710681 x h1) (@lem1710682)). Qed.
Lemma lem1710685 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710686 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710685 real t1 t2). Qed.
Lemma lem1710687 : term76 = term75.
Proof. exact (@lem1710686 term60 term75). Qed.
Lemma lem1710688 (x : real) (h1 : (term71 x) = False) : (term27 x) = term75.
Proof. exact (TRANS (@lem1710683 x h1) (@lem1710687)). Qed.
Lemma lem1710689 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710690 (x : real) (h1 : (term71 x) = False) : (term29 x) = term77.
Proof. exact (MK_COMB (@lem1710689) (@lem1710688 x h1)). Qed.
Lemma lem1710691 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710692 (x : real) (h1 : (term71 x) = False) : ((term27 x) = term60) = (term75 = term60).
Proof. exact (MK_COMB (@lem1710690 x h1) (@lem1710691)). Qed.
Lemma lem1710695 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710696 (x : real) (h1 : (term71 x) = False) : (term64 x) = term78.
Proof. exact (MK_COMB (@lem1710695) (@lem1710692 x h1)). Qed.
Lemma lem1710697 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1710698 (x : real) (h1 : (term71 x) = False) : (term65 x) = (term79 x).
Proof. exact (MK_COMB (@lem1710697 x) (@lem1710696 x h1)). Qed.
Lemma lem1710701 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1710702 (x : real) (h1 : (term71 x) = False) : (term66 x) = (term80 x).
Proof. exact (MK_COMB (@lem1710701 x) (@lem1710698 x h1)). Qed.
Lemma lem1710705 (x : real) : (term81 x) = (term81 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem1710706 (x : real) (h1 : (term71 x) = False) : (term82 x) = (term83 x).
Proof. exact (MK_COMB (@lem1710705 x) (@lem1710702 x h1)). Qed.
Lemma lem1710709 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710710 (x : real) (h1 : (term71 x) = False) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1710709) (@lem1710706 x h1)). Qed.
Lemma lem1710716 (x : real) (h1 : (term71 x) = False) : (term71 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710717 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710718 (x : real) (h1 : (term71 x) = False) : (term72 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710717) (@lem1710716 x h1)). Qed.
Lemma lem1710719 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710720 (x : real) (h1 : (term71 x) = False) : (term73 x) = term74.
Proof. exact (MK_COMB (@lem1710718 x h1) (@lem1710719)). Qed.
Lemma lem1710721 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710722 (x : real) (h1 : (term71 x) = False) : (term27 x) = term76.
Proof. exact (MK_COMB (@lem1710720 x h1) (@lem1710721)). Qed.
Lemma lem1710724 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710725 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710724 real t1 t2). Qed.
Lemma lem1710726 : term76 = term75.
Proof. exact (@lem1710725 term60 term75). Qed.
Lemma lem1710727 (x : real) (h1 : (term71 x) = False) : (term27 x) = term75.
Proof. exact (TRANS (@lem1710722 x h1) (@lem1710726)). Qed.
Lemma lem1710728 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710729 (x : real) (h1 : (term71 x) = False) : (term29 x) = term77.
Proof. exact (MK_COMB (@lem1710728) (@lem1710727 x h1)). Qed.
Lemma lem1710730 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1710731 (x : real) (h1 : (term71 x) = False) : ((term27 x) = (term46 x)) = (term75 = (term46 x)).
Proof. exact (MK_COMB (@lem1710729 x h1) (@lem1710730 x)). Qed.
Lemma lem1710734 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710735 (x : real) (h1 : (term71 x) = False) : (term53 x) = (term86 x).
Proof. exact (MK_COMB (@lem1710734) (@lem1710731 x h1)). Qed.
Lemma lem1710736 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1710737 (x : real) (h1 : (term71 x) = False) : (term56 x) = (term87 x).
Proof. exact (MK_COMB (@lem1710736 x) (@lem1710735 x h1)). Qed.
Lemma lem1710740 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1710741 (x : real) (h1 : (term71 x) = False) : (term57 x) = (term88 x).
Proof. exact (MK_COMB (@lem1710740 x) (@lem1710737 x h1)). Qed.
Lemma lem1710744 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1710745 (x : real) (h1 : (term71 x) = False) : (term90 x) = (term91 x).
Proof. exact (MK_COMB (@lem1710744 x) (@lem1710741 x h1)). Qed.
Lemma lem1710748 (x : real) (h1 : (term71 x) = False) : (term70 x) = (term92 x).
Proof. exact (MK_COMB (@lem1710710 x h1) (@lem1710745 x h1)). Qed.
Lemma lem1710751 (x : real) : term93 x.
Proof. exact (fun h0 : (term71 x) = False => @lem1710748 x h0). Qed.
Lemma lem1710757 (x : real) (h1 : (term71 x) = True) : (term71 x) = True.
Proof. exact (h1). Qed.
Lemma lem1710758 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710759 (x : real) (h1 : (term71 x) = True) : (term72 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1710758) (@lem1710757 x h1)). Qed.
Lemma lem1710760 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710761 (x : real) (h1 : (term71 x) = True) : (term73 x) = term94.
Proof. exact (MK_COMB (@lem1710759 x h1) (@lem1710760)). Qed.
Lemma lem1710762 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710763 (x : real) (h1 : (term71 x) = True) : (term27 x) = term95.
Proof. exact (MK_COMB (@lem1710761 x h1) (@lem1710762)). Qed.
Lemma lem1710765 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1710766 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1710765 real t2 t1). Qed.
Lemma lem1710767 : term95 = term60.
Proof. exact (@lem1710766 term75 term60). Qed.
Lemma lem1710768 (x : real) (h1 : (term71 x) = True) : (term27 x) = term60.
Proof. exact (TRANS (@lem1710763 x h1) (@lem1710767)). Qed.
Lemma lem1710769 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710770 (x : real) (h1 : (term71 x) = True) : (term29 x) = term96.
Proof. exact (MK_COMB (@lem1710769) (@lem1710768 x h1)). Qed.
Lemma lem1710771 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710772 (x : real) (h1 : (term71 x) = True) : ((term27 x) = term60) = (term60 = term60).
Proof. exact (MK_COMB (@lem1710770 x h1) (@lem1710771)). Qed.
Lemma lem1710774 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1710775 (x : real) : (x = x) = True.
Proof. exact (@lem1710774 real x). Qed.
Lemma lem1710776 : (term60 = term60) = True.
Proof. exact (@lem1710775 term60). Qed.
Lemma lem1710777 (x : real) (h1 : (term71 x) = True) : ((term27 x) = term60) = True.
Proof. exact (TRANS (@lem1710772 x h1) (@lem1710776)). Qed.
Lemma lem1710778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710779 (x : real) (h1 : (term71 x) = True) : (term64 x) = (~ True).
Proof. exact (MK_COMB (@lem1710778) (@lem1710777 x h1)). Qed.
Lemma lem1710781 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem1710782 (x : real) (h1 : (term71 x) = True) : (term64 x) = False.
Proof. exact (TRANS (@lem1710779 x h1) (@lem1710781)). Qed.
Lemma lem1710783 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1710784 (x : real) (h1 : (term71 x) = True) : (term65 x) = (term97 x).
Proof. exact (MK_COMB (@lem1710783 x) (@lem1710782 x h1)). Qed.
Lemma lem1710786 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1710787 (x : real) : (term97 x) = False.
Proof. exact (@lem1710786 (term98 x)). Qed.
Lemma lem1710788 (x : real) (h1 : (term71 x) = True) : (term65 x) = False.
Proof. exact (TRANS (@lem1710784 x h1) (@lem1710787 x)). Qed.
Lemma lem1710789 (x : real) : (term63 x) = (term63 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1710790 (x : real) (h1 : (term71 x) = True) : (term66 x) = (term99 x).
Proof. exact (MK_COMB (@lem1710789 x) (@lem1710788 x h1)). Qed.
Lemma lem1710792 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1710793 (x : real) : (term99 x) = (term62 x).
Proof. exact (@lem1710792 (term62 x)). Qed.
Lemma lem1710796 (x : real) (h1 : (term71 x) = True) : (term66 x) = (term62 x).
Proof. exact (TRANS (@lem1710790 x h1) (@lem1710793 x)). Qed.
Lemma lem1710797 (x : real) : (term81 x) = (term81 x).
Proof. exact (eq_refl (term81 x)). Qed.
Lemma lem1710798 (x : real) (h1 : (term71 x) = True) : (term82 x) = (term100 x).
Proof. exact (MK_COMB (@lem1710797 x) (@lem1710796 x h1)). Qed.
Lemma lem1710801 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710802 (x : real) (h1 : (term71 x) = True) : (term84 x) = (term101 x).
Proof. exact (MK_COMB (@lem1710801) (@lem1710798 x h1)). Qed.
Lemma lem1710808 (x : real) (h1 : (term71 x) = True) : (term71 x) = True.
Proof. exact (h1). Qed.
Lemma lem1710809 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710810 (x : real) (h1 : (term71 x) = True) : (term72 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1710809) (@lem1710808 x h1)). Qed.
Lemma lem1710811 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710812 (x : real) (h1 : (term71 x) = True) : (term73 x) = term94.
Proof. exact (MK_COMB (@lem1710810 x h1) (@lem1710811)). Qed.
Lemma lem1710813 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710814 (x : real) (h1 : (term71 x) = True) : (term27 x) = term95.
Proof. exact (MK_COMB (@lem1710812 x h1) (@lem1710813)). Qed.
Lemma lem1710816 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1710817 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1710816 real t2 t1). Qed.
Lemma lem1710818 : term95 = term60.
Proof. exact (@lem1710817 term75 term60). Qed.
Lemma lem1710819 (x : real) (h1 : (term71 x) = True) : (term27 x) = term60.
Proof. exact (TRANS (@lem1710814 x h1) (@lem1710818)). Qed.
Lemma lem1710820 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1710821 (x : real) (h1 : (term71 x) = True) : (term29 x) = term96.
Proof. exact (MK_COMB (@lem1710820) (@lem1710819 x h1)). Qed.
Lemma lem1710822 (x : real) : (term46 x) = (term46 x).
Proof. exact (eq_refl (term46 x)). Qed.
Lemma lem1710823 (x : real) (h1 : (term71 x) = True) : ((term27 x) = (term46 x)) = (term60 = (term46 x)).
Proof. exact (MK_COMB (@lem1710821 x h1) (@lem1710822 x)). Qed.
Lemma lem1710826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710827 (x : real) (h1 : (term71 x) = True) : (term53 x) = (term102 x).
Proof. exact (MK_COMB (@lem1710826) (@lem1710823 x h1)). Qed.
Lemma lem1710828 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1710829 (x : real) (h1 : (term71 x) = True) : (term56 x) = (term103 x).
Proof. exact (MK_COMB (@lem1710828 x) (@lem1710827 x h1)). Qed.
Lemma lem1710832 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1710833 (x : real) (h1 : (term71 x) = True) : (term57 x) = (term104 x).
Proof. exact (MK_COMB (@lem1710832 x) (@lem1710829 x h1)). Qed.
Lemma lem1710836 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1710837 (x : real) (h1 : (term71 x) = True) : (term90 x) = (term105 x).
Proof. exact (MK_COMB (@lem1710836 x) (@lem1710833 x h1)). Qed.
Lemma lem1710840 (x : real) (h1 : (term71 x) = True) : (term70 x) = (term106 x).
Proof. exact (MK_COMB (@lem1710802 x h1) (@lem1710837 x h1)). Qed.
Lemma lem1710843 (x : real) : term107 x.
Proof. exact (fun h0 : (term71 x) = True => @lem1710840 x h0). Qed.
Lemma lem1710844 (x : real) : term108 x.
Proof. exact (conj (@lem1710751 x) (@lem1710843 x)). Qed.
Lemma lem1710846 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term38 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1710847 (x : real) : term109 x.
Proof. exact (@lem1710846 (term70 x) (term106 x) (term71 x) (term92 x)). Qed.
Lemma lem1710862 (x : real) : (term70 x) = (term110 x).
Proof. exact (@lem1710847 x (@lem1710844 x)). Qed.
Lemma lem1710872 (x : real) (h1 : (term111 x) = False) : (term111 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710873 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710874 (x : real) (h1 : (term111 x) = False) : (term112 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710873) (@lem1710872 x h1)). Qed.
Lemma lem1710875 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710876 (x : real) (h1 : (term111 x) = False) : (term113 x) = term74.
Proof. exact (MK_COMB (@lem1710874 x h1) (@lem1710875)). Qed.
Lemma lem1710877 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710878 (x : real) (h1 : (term111 x) = False) : (term44 x) = term76.
Proof. exact (MK_COMB (@lem1710876 x h1) (@lem1710877)). Qed.
Lemma lem1710880 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710881 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710880 real t1 t2). Qed.
Lemma lem1710882 : term76 = term75.
Proof. exact (@lem1710881 term60 term75). Qed.
Lemma lem1710883 (x : real) (h1 : (term111 x) = False) : (term44 x) = term75.
Proof. exact (TRANS (@lem1710878 x h1) (@lem1710882)). Qed.
Lemma lem1710884 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710885 (x : real) (h1 : (term111 x) = False) : (term46 x) = term114.
Proof. exact (MK_COMB (@lem1710884) (@lem1710883 x h1)). Qed.
Lemma lem1710886 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1710887 (x : real) (h1 : (term111 x) = False) : (term24 = (term46 x)) = (term24 = term114).
Proof. exact (MK_COMB (@lem1710886) (@lem1710885 x h1)). Qed.
Lemma lem1710890 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710891 (x : real) (h1 : (term111 x) = False) : (term47 x) = term115.
Proof. exact (MK_COMB (@lem1710890) (@lem1710887 x h1)). Qed.
Lemma lem1710892 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1710893 (x : real) (h1 : (term111 x) = False) : (term50 x) = (term116 x).
Proof. exact (MK_COMB (@lem1710892 x) (@lem1710891 x h1)). Qed.
Lemma lem1710896 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710897 (x : real) (h1 : (term111 x) = False) : (term52 x) = (term117 x).
Proof. exact (MK_COMB (@lem1710896) (@lem1710893 x h1)). Qed.
Lemma lem1710899 (x : real) (h1 : (term111 x) = False) : (term111 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710900 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710901 (x : real) (h1 : (term111 x) = False) : (term112 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710900) (@lem1710899 x h1)). Qed.
Lemma lem1710902 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710903 (x : real) (h1 : (term111 x) = False) : (term113 x) = term74.
Proof. exact (MK_COMB (@lem1710901 x h1) (@lem1710902)). Qed.
Lemma lem1710904 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710905 (x : real) (h1 : (term111 x) = False) : (term44 x) = term76.
Proof. exact (MK_COMB (@lem1710903 x h1) (@lem1710904)). Qed.
Lemma lem1710907 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710908 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710907 real t1 t2). Qed.
Lemma lem1710909 : term76 = term75.
Proof. exact (@lem1710908 term60 term75). Qed.
Lemma lem1710910 (x : real) (h1 : (term111 x) = False) : (term44 x) = term75.
Proof. exact (TRANS (@lem1710905 x h1) (@lem1710909)). Qed.
Lemma lem1710911 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710912 (x : real) (h1 : (term111 x) = False) : (term46 x) = term114.
Proof. exact (MK_COMB (@lem1710911) (@lem1710910 x h1)). Qed.
Lemma lem1710913 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1710914 (x : real) (h1 : (term111 x) = False) : (term60 = (term46 x)) = (term60 = term114).
Proof. exact (MK_COMB (@lem1710913) (@lem1710912 x h1)). Qed.
Lemma lem1710917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710918 (x : real) (h1 : (term111 x) = False) : (term102 x) = term118.
Proof. exact (MK_COMB (@lem1710917) (@lem1710914 x h1)). Qed.
Lemma lem1710919 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1710920 (x : real) (h1 : (term111 x) = False) : (term103 x) = (term119 x).
Proof. exact (MK_COMB (@lem1710919 x) (@lem1710918 x h1)). Qed.
Lemma lem1710923 (x : real) (h1 : (term111 x) = False) : (term104 x) = (term120 x).
Proof. exact (MK_COMB (@lem1710897 x h1) (@lem1710920 x h1)). Qed.
Lemma lem1710926 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1710927 (x : real) (h1 : (term111 x) = False) : (term105 x) = (term121 x).
Proof. exact (MK_COMB (@lem1710926 x) (@lem1710923 x h1)). Qed.
Lemma lem1710930 (x : real) : (term101 x) = (term101 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1710931 (x : real) (h1 : (term111 x) = False) : (term106 x) = (term122 x).
Proof. exact (MK_COMB (@lem1710930 x) (@lem1710927 x h1)). Qed.
Lemma lem1710934 (x : real) : (term123 x) = (term123 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem1710935 (x : real) (h1 : (term111 x) = False) : (term124 x) = (term125 x).
Proof. exact (MK_COMB (@lem1710934 x) (@lem1710931 x h1)). Qed.
Lemma lem1710938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710939 (x : real) (h1 : (term111 x) = False) : (term126 x) = (term127 x).
Proof. exact (MK_COMB (@lem1710938) (@lem1710935 x h1)). Qed.
Lemma lem1710953 (x : real) (h1 : (term111 x) = False) : (term111 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710954 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710955 (x : real) (h1 : (term111 x) = False) : (term112 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710954) (@lem1710953 x h1)). Qed.
Lemma lem1710956 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710957 (x : real) (h1 : (term111 x) = False) : (term113 x) = term74.
Proof. exact (MK_COMB (@lem1710955 x h1) (@lem1710956)). Qed.
Lemma lem1710958 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710959 (x : real) (h1 : (term111 x) = False) : (term44 x) = term76.
Proof. exact (MK_COMB (@lem1710957 x h1) (@lem1710958)). Qed.
Lemma lem1710961 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710962 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710961 real t1 t2). Qed.
Lemma lem1710963 : term76 = term75.
Proof. exact (@lem1710962 term60 term75). Qed.
Lemma lem1710964 (x : real) (h1 : (term111 x) = False) : (term44 x) = term75.
Proof. exact (TRANS (@lem1710959 x h1) (@lem1710963)). Qed.
Lemma lem1710965 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710966 (x : real) (h1 : (term111 x) = False) : (term46 x) = term114.
Proof. exact (MK_COMB (@lem1710965) (@lem1710964 x h1)). Qed.
Lemma lem1710967 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1710968 (x : real) (h1 : (term111 x) = False) : (term24 = (term46 x)) = (term24 = term114).
Proof. exact (MK_COMB (@lem1710967) (@lem1710966 x h1)). Qed.
Lemma lem1710971 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710972 (x : real) (h1 : (term111 x) = False) : (term47 x) = term115.
Proof. exact (MK_COMB (@lem1710971) (@lem1710968 x h1)). Qed.
Lemma lem1710973 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1710974 (x : real) (h1 : (term111 x) = False) : (term50 x) = (term116 x).
Proof. exact (MK_COMB (@lem1710973 x) (@lem1710972 x h1)). Qed.
Lemma lem1710977 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1710978 (x : real) (h1 : (term111 x) = False) : (term52 x) = (term117 x).
Proof. exact (MK_COMB (@lem1710977) (@lem1710974 x h1)). Qed.
Lemma lem1710980 (x : real) (h1 : (term111 x) = False) : (term111 x) = False.
Proof. exact (h1). Qed.
Lemma lem1710981 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1710982 (x : real) (h1 : (term111 x) = False) : (term112 x) = (@COND real False).
Proof. exact (MK_COMB (@lem1710981) (@lem1710980 x h1)). Qed.
Lemma lem1710983 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1710984 (x : real) (h1 : (term111 x) = False) : (term113 x) = term74.
Proof. exact (MK_COMB (@lem1710982 x h1) (@lem1710983)). Qed.
Lemma lem1710985 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1710986 (x : real) (h1 : (term111 x) = False) : (term44 x) = term76.
Proof. exact (MK_COMB (@lem1710984 x h1) (@lem1710985)). Qed.
Lemma lem1710988 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem1710989 (t1 : real) (t2 : real) : (@COND real False t1 t2) = t2.
Proof. exact (@lem1710988 real t1 t2). Qed.
Lemma lem1710990 : term76 = term75.
Proof. exact (@lem1710989 term60 term75). Qed.
Lemma lem1710991 (x : real) (h1 : (term111 x) = False) : (term44 x) = term75.
Proof. exact (TRANS (@lem1710986 x h1) (@lem1710990)). Qed.
Lemma lem1710992 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1710993 (x : real) (h1 : (term111 x) = False) : (term46 x) = term114.
Proof. exact (MK_COMB (@lem1710992) (@lem1710991 x h1)). Qed.
Lemma lem1710994 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1710995 (x : real) (h1 : (term111 x) = False) : (term75 = (term46 x)) = (term75 = term114).
Proof. exact (MK_COMB (@lem1710994) (@lem1710993 x h1)). Qed.
Lemma lem1710998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1710999 (x : real) (h1 : (term111 x) = False) : (term86 x) = term128.
Proof. exact (MK_COMB (@lem1710998) (@lem1710995 x h1)). Qed.
Lemma lem1711000 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1711001 (x : real) (h1 : (term111 x) = False) : (term87 x) = (term129 x).
Proof. exact (MK_COMB (@lem1711000 x) (@lem1710999 x h1)). Qed.
Lemma lem1711004 (x : real) (h1 : (term111 x) = False) : (term88 x) = (term130 x).
Proof. exact (MK_COMB (@lem1710978 x h1) (@lem1711001 x h1)). Qed.
Lemma lem1711007 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1711008 (x : real) (h1 : (term111 x) = False) : (term91 x) = (term131 x).
Proof. exact (MK_COMB (@lem1711007 x) (@lem1711004 x h1)). Qed.
Lemma lem1711011 (x : real) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem1711012 (x : real) (h1 : (term111 x) = False) : (term92 x) = (term132 x).
Proof. exact (MK_COMB (@lem1711011 x) (@lem1711008 x h1)). Qed.
Lemma lem1711015 (x : real) : (term133 x) = (term133 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1711016 (x : real) (h1 : (term111 x) = False) : (term134 x) = (term135 x).
Proof. exact (MK_COMB (@lem1711015 x) (@lem1711012 x h1)). Qed.
Lemma lem1711019 (x : real) (h1 : (term111 x) = False) : (term110 x) = (term136 x).
Proof. exact (MK_COMB (@lem1710939 x h1) (@lem1711016 x h1)). Qed.
Lemma lem1711022 (x : real) : term137 x.
Proof. exact (fun h0 : (term111 x) = False => @lem1711019 x h0). Qed.
Lemma lem1711030 (x : real) (h1 : (term111 x) = True) : (term111 x) = True.
Proof. exact (h1). Qed.
Lemma lem1711031 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1711032 (x : real) (h1 : (term111 x) = True) : (term112 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1711031) (@lem1711030 x h1)). Qed.
Lemma lem1711033 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1711034 (x : real) (h1 : (term111 x) = True) : (term113 x) = term94.
Proof. exact (MK_COMB (@lem1711032 x h1) (@lem1711033)). Qed.
Lemma lem1711035 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711036 (x : real) (h1 : (term111 x) = True) : (term44 x) = term95.
Proof. exact (MK_COMB (@lem1711034 x h1) (@lem1711035)). Qed.
Lemma lem1711038 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1711039 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1711038 real t2 t1). Qed.
Lemma lem1711040 : term95 = term60.
Proof. exact (@lem1711039 term75 term60). Qed.
Lemma lem1711041 (x : real) (h1 : (term111 x) = True) : (term44 x) = term60.
Proof. exact (TRANS (@lem1711036 x h1) (@lem1711040)). Qed.
Lemma lem1711042 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711043 (x : real) (h1 : (term111 x) = True) : (term46 x) = term138.
Proof. exact (MK_COMB (@lem1711042) (@lem1711041 x h1)). Qed.
Lemma lem1711044 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1711045 (x : real) (h1 : (term111 x) = True) : (term24 = (term46 x)) = (term24 = term138).
Proof. exact (MK_COMB (@lem1711044) (@lem1711043 x h1)). Qed.
Lemma lem1711048 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1711049 (x : real) (h1 : (term111 x) = True) : (term47 x) = term139.
Proof. exact (MK_COMB (@lem1711048) (@lem1711045 x h1)). Qed.
Lemma lem1711050 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1711051 (x : real) (h1 : (term111 x) = True) : (term50 x) = (term140 x).
Proof. exact (MK_COMB (@lem1711050 x) (@lem1711049 x h1)). Qed.
Lemma lem1711054 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711055 (x : real) (h1 : (term111 x) = True) : (term52 x) = (term141 x).
Proof. exact (MK_COMB (@lem1711054) (@lem1711051 x h1)). Qed.
Lemma lem1711057 (x : real) (h1 : (term111 x) = True) : (term111 x) = True.
Proof. exact (h1). Qed.
Lemma lem1711058 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1711059 (x : real) (h1 : (term111 x) = True) : (term112 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1711058) (@lem1711057 x h1)). Qed.
Lemma lem1711060 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1711061 (x : real) (h1 : (term111 x) = True) : (term113 x) = term94.
Proof. exact (MK_COMB (@lem1711059 x h1) (@lem1711060)). Qed.
Lemma lem1711062 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711063 (x : real) (h1 : (term111 x) = True) : (term44 x) = term95.
Proof. exact (MK_COMB (@lem1711061 x h1) (@lem1711062)). Qed.
Lemma lem1711065 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1711066 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1711065 real t2 t1). Qed.
Lemma lem1711067 : term95 = term60.
Proof. exact (@lem1711066 term75 term60). Qed.
Lemma lem1711068 (x : real) (h1 : (term111 x) = True) : (term44 x) = term60.
Proof. exact (TRANS (@lem1711063 x h1) (@lem1711067)). Qed.
Lemma lem1711069 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711070 (x : real) (h1 : (term111 x) = True) : (term46 x) = term138.
Proof. exact (MK_COMB (@lem1711069) (@lem1711068 x h1)). Qed.
Lemma lem1711071 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1711072 (x : real) (h1 : (term111 x) = True) : (term60 = (term46 x)) = (term60 = term138).
Proof. exact (MK_COMB (@lem1711071) (@lem1711070 x h1)). Qed.
Lemma lem1711075 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1711076 (x : real) (h1 : (term111 x) = True) : (term102 x) = term142.
Proof. exact (MK_COMB (@lem1711075) (@lem1711072 x h1)). Qed.
Lemma lem1711077 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1711078 (x : real) (h1 : (term111 x) = True) : (term103 x) = (term143 x).
Proof. exact (MK_COMB (@lem1711077 x) (@lem1711076 x h1)). Qed.
Lemma lem1711081 (x : real) (h1 : (term111 x) = True) : (term104 x) = (term144 x).
Proof. exact (MK_COMB (@lem1711055 x h1) (@lem1711078 x h1)). Qed.
Lemma lem1711084 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1711085 (x : real) (h1 : (term111 x) = True) : (term105 x) = (term145 x).
Proof. exact (MK_COMB (@lem1711084 x) (@lem1711081 x h1)). Qed.
Lemma lem1711088 (x : real) : (term101 x) = (term101 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1711089 (x : real) (h1 : (term111 x) = True) : (term106 x) = (term146 x).
Proof. exact (MK_COMB (@lem1711088 x) (@lem1711085 x h1)). Qed.
Lemma lem1711092 (x : real) : (term123 x) = (term123 x).
Proof. exact (eq_refl (term123 x)). Qed.
Lemma lem1711093 (x : real) (h1 : (term111 x) = True) : (term124 x) = (term147 x).
Proof. exact (MK_COMB (@lem1711092 x) (@lem1711089 x h1)). Qed.
Lemma lem1711096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711097 (x : real) (h1 : (term111 x) = True) : (term126 x) = (term148 x).
Proof. exact (MK_COMB (@lem1711096) (@lem1711093 x h1)). Qed.
Lemma lem1711111 (x : real) (h1 : (term111 x) = True) : (term111 x) = True.
Proof. exact (h1). Qed.
Lemma lem1711112 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1711113 (x : real) (h1 : (term111 x) = True) : (term112 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1711112) (@lem1711111 x h1)). Qed.
Lemma lem1711114 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1711115 (x : real) (h1 : (term111 x) = True) : (term113 x) = term94.
Proof. exact (MK_COMB (@lem1711113 x h1) (@lem1711114)). Qed.
Lemma lem1711116 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711117 (x : real) (h1 : (term111 x) = True) : (term44 x) = term95.
Proof. exact (MK_COMB (@lem1711115 x h1) (@lem1711116)). Qed.
Lemma lem1711119 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1711120 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1711119 real t2 t1). Qed.
Lemma lem1711121 : term95 = term60.
Proof. exact (@lem1711120 term75 term60). Qed.
Lemma lem1711122 (x : real) (h1 : (term111 x) = True) : (term44 x) = term60.
Proof. exact (TRANS (@lem1711117 x h1) (@lem1711121)). Qed.
Lemma lem1711123 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711124 (x : real) (h1 : (term111 x) = True) : (term46 x) = term138.
Proof. exact (MK_COMB (@lem1711123) (@lem1711122 x h1)). Qed.
Lemma lem1711125 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem1711126 (x : real) (h1 : (term111 x) = True) : (term24 = (term46 x)) = (term24 = term138).
Proof. exact (MK_COMB (@lem1711125) (@lem1711124 x h1)). Qed.
Lemma lem1711129 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1711130 (x : real) (h1 : (term111 x) = True) : (term47 x) = term139.
Proof. exact (MK_COMB (@lem1711129) (@lem1711126 x h1)). Qed.
Lemma lem1711131 (x : real) : (term48 x) = (term48 x).
Proof. exact (eq_refl (term48 x)). Qed.
Lemma lem1711132 (x : real) (h1 : (term111 x) = True) : (term50 x) = (term140 x).
Proof. exact (MK_COMB (@lem1711131 x) (@lem1711130 x h1)). Qed.
Lemma lem1711135 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711136 (x : real) (h1 : (term111 x) = True) : (term52 x) = (term141 x).
Proof. exact (MK_COMB (@lem1711135) (@lem1711132 x h1)). Qed.
Lemma lem1711138 (x : real) (h1 : (term111 x) = True) : (term111 x) = True.
Proof. exact (h1). Qed.
Lemma lem1711139 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1711140 (x : real) (h1 : (term111 x) = True) : (term112 x) = (@COND real True).
Proof. exact (MK_COMB (@lem1711139) (@lem1711138 x h1)). Qed.
Lemma lem1711141 : term60 = term60.
Proof. exact (eq_refl term60). Qed.
Lemma lem1711142 (x : real) (h1 : (term111 x) = True) : (term113 x) = term94.
Proof. exact (MK_COMB (@lem1711140 x h1) (@lem1711141)). Qed.
Lemma lem1711143 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711144 (x : real) (h1 : (term111 x) = True) : (term44 x) = term95.
Proof. exact (MK_COMB (@lem1711142 x h1) (@lem1711143)). Qed.
Lemma lem1711146 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1711147 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1711146 real t2 t1). Qed.
Lemma lem1711148 : term95 = term60.
Proof. exact (@lem1711147 term75 term60). Qed.
Lemma lem1711149 (x : real) (h1 : (term111 x) = True) : (term44 x) = term60.
Proof. exact (TRANS (@lem1711144 x h1) (@lem1711148)). Qed.
Lemma lem1711150 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711151 (x : real) (h1 : (term111 x) = True) : (term46 x) = term138.
Proof. exact (MK_COMB (@lem1711150) (@lem1711149 x h1)). Qed.
Lemma lem1711152 : term77 = term77.
Proof. exact (eq_refl term77). Qed.
Lemma lem1711153 (x : real) (h1 : (term111 x) = True) : (term75 = (term46 x)) = (term75 = term138).
Proof. exact (MK_COMB (@lem1711152) (@lem1711151 x h1)). Qed.
Lemma lem1711156 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1711157 (x : real) (h1 : (term111 x) = True) : (term86 x) = term149.
Proof. exact (MK_COMB (@lem1711156) (@lem1711153 x h1)). Qed.
Lemma lem1711158 (x : real) : (term54 x) = (term54 x).
Proof. exact (eq_refl (term54 x)). Qed.
Lemma lem1711159 (x : real) (h1 : (term111 x) = True) : (term87 x) = (term150 x).
Proof. exact (MK_COMB (@lem1711158 x) (@lem1711157 x h1)). Qed.
Lemma lem1711162 (x : real) (h1 : (term111 x) = True) : (term88 x) = (term151 x).
Proof. exact (MK_COMB (@lem1711136 x h1) (@lem1711159 x h1)). Qed.
Lemma lem1711165 (x : real) : (term89 x) = (term89 x).
Proof. exact (eq_refl (term89 x)). Qed.
Lemma lem1711166 (x : real) (h1 : (term111 x) = True) : (term91 x) = (term152 x).
Proof. exact (MK_COMB (@lem1711165 x) (@lem1711162 x h1)). Qed.
Lemma lem1711169 (x : real) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem1711170 (x : real) (h1 : (term111 x) = True) : (term92 x) = (term153 x).
Proof. exact (MK_COMB (@lem1711169 x) (@lem1711166 x h1)). Qed.
Lemma lem1711173 (x : real) : (term133 x) = (term133 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1711174 (x : real) (h1 : (term111 x) = True) : (term134 x) = (term154 x).
Proof. exact (MK_COMB (@lem1711173 x) (@lem1711170 x h1)). Qed.
Lemma lem1711177 (x : real) (h1 : (term111 x) = True) : (term110 x) = (term155 x).
Proof. exact (MK_COMB (@lem1711097 x h1) (@lem1711174 x h1)). Qed.
Lemma lem1711180 (x : real) : term156 x.
Proof. exact (fun h0 : (term111 x) = True => @lem1711177 x h0). Qed.
Lemma lem1711181 (x : real) : term157 x.
Proof. exact (conj (@lem1711022 x) (@lem1711180 x)). Qed.
Lemma lem1711183 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term38 x x1 b x0.
Proof. exact (or_elim (@lem20234 b) (fun h0 : b = True => @lem20421 x x1 x0 b h0) (fun h0 : b = False => @lem20420 x x1 x0 b h0)). Qed.
Lemma lem1711184 (x : real) : term158 x.
Proof. exact (@lem1711183 (term110 x) (term155 x) (term111 x) (term136 x)). Qed.
Lemma lem1711421 (x : real) : (term110 x) = (term159 x).
Proof. exact (@lem1711184 x (@lem1711181 x)). Qed.
Lemma lem1711422 (x : real) : (term160 x) = (term160 x).
Proof. exact (eq_refl (term160 x)). Qed.
Lemma lem1711423 (x : real) : ((term70 x) = (term110 x)) = ((term70 x) = (term159 x)).
Proof. exact (MK_COMB (@lem1711422 x) (@lem1711421 x)). Qed.
Lemma lem1711424 (x : real) : (term70 x) = (term159 x).
Proof. exact (EQ_MP (@lem1711423 x) (@lem1710862 x)). Qed.
Lemma lem1711425 (x : real) : (term161 x) = (term161 x).
Proof. exact (eq_refl (term161 x)). Qed.
Lemma lem1711426 (x : real) : ((term40 x) = (term70 x)) = ((term40 x) = (term159 x)).
Proof. exact (MK_COMB (@lem1711425 x) (@lem1711424 x)). Qed.
Lemma lem1711427 (x : real) : (term40 x) = (term159 x).
Proof. exact (EQ_MP (@lem1711426 x) (@lem1710669 x)). Qed.
Lemma lem1711428 (x : real) : (term162 x) = (term162 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem1711429 (x : real) : ((term18 x) = (term40 x)) = ((term18 x) = (term159 x)).
Proof. exact (MK_COMB (@lem1711428 x) (@lem1711427 x)). Qed.
Lemma lem1711430 (x : real) : (term18 x) = (term159 x).
Proof. exact (EQ_MP (@lem1711429 x) (@lem1710536 x)). Qed.
Lemma lem1711431 : term20 = term163.
Proof. exact (fun_ext (fun x : real => @lem1711430 x)). Qed.
Lemma lem1711432 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1711433 : term21 = term164.
Proof. exact (MK_COMB (@lem1711432) (@lem1711431)). Qed.
Lemma lem1711434 : term14 = term164.
Proof. exact (TRANS (@lem1710471) (@lem1711433)). Qed.
Lemma lem1711435 (x : real) : (term111 x) = (term165 x).
Proof. exact (@lem1483521 term75 x). Qed.
Lemma lem1711441 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem1483519 term75 x). Qed.
Lemma lem1711446 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483448 (term168 x)). Qed.
Lemma lem1711448 (x : real) : (term166 x) = (term168 x).
Proof. exact (TRANS (@lem1711441 x) (@lem1711446 x)). Qed.
Lemma lem1711449 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711450 (x : real) : (term169 x) = (term170 x).
Proof. exact (MK_COMB (@lem1711449) (@lem1711448 x)). Qed.
Lemma lem1711451 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711452 (x : real) : (term165 x) = (term171 x).
Proof. exact (MK_COMB (@lem1711450 x) (@lem1711451)). Qed.
Lemma lem1711453 (x : real) : (term111 x) = (term171 x).
Proof. exact (TRANS (@lem1711435 x) (@lem1711452 x)). Qed.
Lemma lem1711454 (x : real) : (term71 x) = (term172 x).
Proof. exact (@lem1483521 term75 (real_neg x)). Qed.
Lemma lem1711461 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1711464 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1711465 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1711464) (@lem1711461 x)). Qed.
Lemma lem1711466 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1711467 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1711469 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711470 : term181 = term182.
Proof. exact (@lem1711469 term183 term183). Qed.
Lemma lem1711471 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711472 : term185 = term183.
Proof. exact (EQ_MP (@lem1711471) (@lem940073)). Qed.
Lemma lem1711473 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711474 : term182 = term24.
Proof. exact (MK_COMB (@lem1711473) (@lem1711472)). Qed.
Lemma lem1711475 : term181 = term24.
Proof. exact (TRANS (@lem1711470) (@lem1711474)). Qed.
Lemma lem1711476 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1711477 : term186 = term187.
Proof. exact (MK_COMB (@lem1711476) (@lem1711475)). Qed.
Lemma lem1711478 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1711479 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1711477) (@lem1711478 x)). Qed.
Lemma lem1711480 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1711467 x) (@lem1711479 x)). Qed.
Lemma lem1711481 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1711482 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1711480 x) (@lem1711481 x)). Qed.
Lemma lem1711483 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1711484 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1711483) (@lem1711482 x)). Qed.
Lemma lem1711485 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1711486 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1711484 x) (@lem1711485 x)). Qed.
Lemma lem1711487 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1711466 x) (@lem1711486 x)). Qed.
Lemma lem1711488 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1711465 x) (@lem1711487 x)). Qed.
Lemma lem1711489 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711490 (x : real) : (term191 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1711489) (@lem1711488 x)). Qed.
Lemma lem1711491 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711492 (x : real) : (term172 x) = (term192 x).
Proof. exact (MK_COMB (@lem1711490 x) (@lem1711491)). Qed.
Lemma lem1711493 (x : real) : (term71 x) = (term192 x).
Proof. exact (TRANS (@lem1711454 x) (@lem1711492 x)). Qed.
Lemma lem1711494 (x : real) : (term41 x) = (term193 x).
Proof. exact (@lem1483521 x term75). Qed.
Lemma lem1711500 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem1483519 x term75). Qed.
Lemma lem1711502 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1711503 : term197 = term75.
Proof. exact (@lem1711502 term183). Qed.
Lemma lem1711504 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1711505 (x : real) : (term195 x) = (term198 x).
Proof. exact (MK_COMB (@lem1711504 x) (@lem1711503)). Qed.
Lemma lem1711506 (x : real) : (term198 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1711507 (x : real) : (term195 x) = x.
Proof. exact (TRANS (@lem1711505 x) (@lem1711506 x)). Qed.
Lemma lem1711509 (x : real) : (term194 x) = x.
Proof. exact (TRANS (@lem1711500 x) (@lem1711507 x)). Qed.
Lemma lem1711510 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711511 (x : real) : (term199 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1711510) (@lem1711509 x)). Qed.
Lemma lem1711512 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711513 (x : real) : (term193 x) = (term192 x).
Proof. exact (MK_COMB (@lem1711511 x) (@lem1711512)). Qed.
Lemma lem1711514 (x : real) : (term41 x) = (term192 x).
Proof. exact (TRANS (@lem1711494 x) (@lem1711513 x)). Qed.
Lemma lem1711515 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1711516 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711523 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1711524 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1711525 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1711524) (@lem1711523 x)). Qed.
Lemma lem1711526 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1711525 x) (@lem1711516)). Qed.
Lemma lem1711527 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1711529 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1711530 : term197 = term75.
Proof. exact (@lem1711529 term183). Qed.
Lemma lem1711531 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1711532 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1711531 x) (@lem1711530)). Qed.
Lemma lem1711533 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1711534 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1711532 x) (@lem1711533 x)). Qed.
Lemma lem1711535 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1711527 x) (@lem1711534 x)). Qed.
Lemma lem1711536 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1711526 x) (@lem1711535 x)). Qed.
Lemma lem1711537 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711538 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1711537) (@lem1711536 x)). Qed.
Lemma lem1711539 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711540 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1711538 x) (@lem1711539)). Qed.
Lemma lem1711541 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1711515 x) (@lem1711540 x)). Qed.
Lemma lem1711542 : term61 = term209.
Proof. exact (@lem1483554 term24 term60). Qed.
Lemma lem1711548 : term210 = term211.
Proof. exact (@lem1483519 term24 term60). Qed.
Lemma lem1711550 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711551 : term181 = term182.
Proof. exact (@lem1711550 term183 term183). Qed.
Lemma lem1711552 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711553 : term185 = term183.
Proof. exact (EQ_MP (@lem1711552) (@lem940073)). Qed.
Lemma lem1711554 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711555 : term182 = term24.
Proof. exact (MK_COMB (@lem1711554) (@lem1711553)). Qed.
Lemma lem1711556 : term181 = term24.
Proof. exact (TRANS (@lem1711551) (@lem1711555)). Qed.
Lemma lem1711557 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1711558 : term211 = term213.
Proof. exact (MK_COMB (@lem1711557) (@lem1711556)). Qed.
Lemma lem1711559 : term213 = term214.
Proof. exact (@lem1367770 term183 term183). Qed.
Lemma lem1711560 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem1711561 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem1711562 : term217 = term218.
Proof. exact (EQ_MP (@lem1711561) (@lem1711560)). Qed.
Lemma lem1711563 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711564 : term214 = term219.
Proof. exact (MK_COMB (@lem1711563) (@lem1711562)). Qed.
Lemma lem1711565 : term213 = term219.
Proof. exact (TRANS (@lem1711559) (@lem1711564)). Qed.
Lemma lem1711566 : term211 = term219.
Proof. exact (TRANS (@lem1711558) (@lem1711565)). Qed.
Lemma lem1711568 : term210 = term219.
Proof. exact (TRANS (@lem1711548) (@lem1711566)). Qed.
Lemma lem1711569 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711570 : term220 = term221.
Proof. exact (MK_COMB (@lem1711569) (@lem1711568)). Qed.
Lemma lem1711571 : term221 = term222.
Proof. exact (@lem1483512 term219). Qed.
Lemma lem1711573 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1711574 : term222 = term225.
Proof. exact (@lem1711573 term183 term218). Qed.
Lemma lem1711575 : term226 = term216.
Proof. exact (@lem996238 term216). Qed.
Lemma lem1711576 : (term226 = term216) = (term227 = term218).
Proof. exact (@lem1007663 (BIT1 0) term216 term216). Qed.
Lemma lem1711577 : term227 = term218.
Proof. exact (EQ_MP (@lem1711576) (@lem1711575)). Qed.
Lemma lem1711578 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711579 : term228 = term219.
Proof. exact (MK_COMB (@lem1711578) (@lem1711577)). Qed.
Lemma lem1711580 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711581 : term225 = term221.
Proof. exact (MK_COMB (@lem1711580) (@lem1711579)). Qed.
Lemma lem1711582 : term222 = term221.
Proof. exact (TRANS (@lem1711574) (@lem1711581)). Qed.
Lemma lem1711583 : term221 = term221.
Proof. exact (TRANS (@lem1711571) (@lem1711582)). Qed.
Lemma lem1711584 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem1711585 : (term220 = term221) = (term220 = term221).
Proof. exact (MK_COMB (@lem1711584) (@lem1711583)). Qed.
Lemma lem1711586 : term220 = term221.
Proof. exact (EQ_MP (@lem1711585) (@lem1711570)). Qed.
Lemma lem1711587 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711588 : term230 = term231.
Proof. exact (MK_COMB (@lem1711587) (@lem1711586)). Qed.
Lemma lem1711589 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711590 : term232 = term233.
Proof. exact (MK_COMB (@lem1711588) (@lem1711589)). Qed.
Lemma lem1711591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711592 : term234 = term235.
Proof. exact (MK_COMB (@lem1711591) (@lem1711568)). Qed.
Lemma lem1711593 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711594 : term236 = term237.
Proof. exact (MK_COMB (@lem1711592) (@lem1711593)). Qed.
Lemma lem1711595 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711596 : term238 = term239.
Proof. exact (MK_COMB (@lem1711595) (@lem1711594)). Qed.
Lemma lem1711597 : term209 = term240.
Proof. exact (MK_COMB (@lem1711596) (@lem1711590)). Qed.
Lemma lem1711598 : term61 = term240.
Proof. exact (TRANS (@lem1711542) (@lem1711597)). Qed.
Lemma lem1711599 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1711600 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1711599) (@lem1711541 x)). Qed.
Lemma lem1711601 (x : real) : (term62 x) = (term242 x).
Proof. exact (MK_COMB (@lem1711600 x) (@lem1711598)). Qed.
Lemma lem1711602 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1711603 (x : real) : (term81 x) = (term243 x).
Proof. exact (MK_COMB (@lem1711602) (@lem1711514 x)). Qed.
Lemma lem1711604 (x : real) : (term100 x) = (term244 x).
Proof. exact (MK_COMB (@lem1711603 x) (@lem1711601 x)). Qed.
Lemma lem1711605 (x : real) : (term245 x) = (term246 x).
Proof. exact (@lem1483531 term75 x). Qed.
Lemma lem1711611 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem1483519 term75 x). Qed.
Lemma lem1711616 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483448 (term168 x)). Qed.
Lemma lem1711618 (x : real) : (term166 x) = (term168 x).
Proof. exact (TRANS (@lem1711611 x) (@lem1711616 x)). Qed.
Lemma lem1711619 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1711620 (x : real) : (term247 x) = (term248 x).
Proof. exact (MK_COMB (@lem1711619) (@lem1711618 x)). Qed.
Lemma lem1711621 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711622 (x : real) : (term246 x) = (term249 x).
Proof. exact (MK_COMB (@lem1711620 x) (@lem1711621)). Qed.
Lemma lem1711623 (x : real) : (term245 x) = (term249 x).
Proof. exact (TRANS (@lem1711605 x) (@lem1711622 x)). Qed.
Lemma lem1711624 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1711625 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711632 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1711633 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1711634 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1711633) (@lem1711632 x)). Qed.
Lemma lem1711635 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1711634 x) (@lem1711625)). Qed.
Lemma lem1711636 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1711638 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1711639 : term197 = term75.
Proof. exact (@lem1711638 term183). Qed.
Lemma lem1711640 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1711641 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1711640 x) (@lem1711639)). Qed.
Lemma lem1711642 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1711643 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1711641 x) (@lem1711642 x)). Qed.
Lemma lem1711644 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1711636 x) (@lem1711643 x)). Qed.
Lemma lem1711645 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1711635 x) (@lem1711644 x)). Qed.
Lemma lem1711646 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711647 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1711646) (@lem1711645 x)). Qed.
Lemma lem1711648 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711649 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1711647 x) (@lem1711648)). Qed.
Lemma lem1711650 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1711624 x) (@lem1711649 x)). Qed.
Lemma lem1711651 : term139 = term250.
Proof. exact (@lem1483554 term24 term138). Qed.
Lemma lem1711655 : term138 = term181.
Proof. exact (@lem1483512 term60). Qed.
Lemma lem1711657 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711658 : term181 = term182.
Proof. exact (@lem1711657 term183 term183). Qed.
Lemma lem1711659 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711660 : term185 = term183.
Proof. exact (EQ_MP (@lem1711659) (@lem940073)). Qed.
Lemma lem1711661 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711662 : term182 = term24.
Proof. exact (MK_COMB (@lem1711661) (@lem1711660)). Qed.
Lemma lem1711663 : term181 = term24.
Proof. exact (TRANS (@lem1711658) (@lem1711662)). Qed.
Lemma lem1711665 : term138 = term24.
Proof. exact (TRANS (@lem1711655) (@lem1711663)). Qed.
Lemma lem1711668 : term251 = term251.
Proof. exact (eq_refl term251). Qed.
Lemma lem1711669 : term252 = term253.
Proof. exact (MK_COMB (@lem1711668) (@lem1711665)). Qed.
Lemma lem1711670 : term253 = term254.
Proof. exact (@lem1483519 term24 term24). Qed.
Lemma lem1711672 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1711673 : term255 = term256.
Proof. exact (@lem1711672 term183 term183). Qed.
Lemma lem1711674 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711675 : term185 = term183.
Proof. exact (EQ_MP (@lem1711674) (@lem940073)). Qed.
Lemma lem1711676 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711677 : term182 = term24.
Proof. exact (MK_COMB (@lem1711676) (@lem1711675)). Qed.
Lemma lem1711678 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711679 : term256 = term60.
Proof. exact (MK_COMB (@lem1711678) (@lem1711677)). Qed.
Lemma lem1711680 : term255 = term60.
Proof. exact (TRANS (@lem1711673) (@lem1711679)). Qed.
Lemma lem1711681 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1711682 : term254 = term257.
Proof. exact (MK_COMB (@lem1711681) (@lem1711680)). Qed.
Lemma lem1711684 (m : nat) : (term258 m) = term75.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1711685 : term257 = term75.
Proof. exact (@lem1711684 term183). Qed.
Lemma lem1711686 : term254 = term75.
Proof. exact (TRANS (@lem1711682) (@lem1711685)). Qed.
Lemma lem1711687 : term253 = term75.
Proof. exact (TRANS (@lem1711670) (@lem1711686)). Qed.
Lemma lem1711688 : term252 = term75.
Proof. exact (TRANS (@lem1711669) (@lem1711687)). Qed.
Lemma lem1711689 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711690 : term259 = term114.
Proof. exact (MK_COMB (@lem1711689) (@lem1711688)). Qed.
Lemma lem1711691 : term114 = term197.
Proof. exact (@lem1483512 term75). Qed.
Lemma lem1711693 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1711694 : term197 = term75.
Proof. exact (@lem1711693 term183). Qed.
Lemma lem1711695 : term114 = term75.
Proof. exact (TRANS (@lem1711691) (@lem1711694)). Qed.
Lemma lem1711696 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem1711697 : (term259 = term114) = (term259 = term75).
Proof. exact (MK_COMB (@lem1711696) (@lem1711695)). Qed.
Lemma lem1711698 : term259 = term75.
Proof. exact (EQ_MP (@lem1711697) (@lem1711690)). Qed.
Lemma lem1711699 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711700 : term261 = term262.
Proof. exact (MK_COMB (@lem1711699) (@lem1711698)). Qed.
Lemma lem1711701 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711702 : term263 = term264.
Proof. exact (MK_COMB (@lem1711700) (@lem1711701)). Qed.
Lemma lem1711703 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711704 : term265 = term262.
Proof. exact (MK_COMB (@lem1711703) (@lem1711688)). Qed.
Lemma lem1711705 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711706 : term266 = term264.
Proof. exact (MK_COMB (@lem1711704) (@lem1711705)). Qed.
Lemma lem1711707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711708 : term267 = term268.
Proof. exact (MK_COMB (@lem1711707) (@lem1711706)). Qed.
Lemma lem1711709 : term250 = term269.
Proof. exact (MK_COMB (@lem1711708) (@lem1711702)). Qed.
Lemma lem1711710 : term139 = term269.
Proof. exact (TRANS (@lem1711651) (@lem1711709)). Qed.
Lemma lem1711711 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1711712 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1711711) (@lem1711650 x)). Qed.
Lemma lem1711713 (x : real) : (term140 x) = (term270 x).
Proof. exact (MK_COMB (@lem1711712 x) (@lem1711710)). Qed.
Lemma lem1711714 (x : real) : (term98 x) = (term271 x).
Proof. exact (@lem1483531 term75 (real_neg x)). Qed.
Lemma lem1711721 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1711724 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1711725 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1711724) (@lem1711721 x)). Qed.
Lemma lem1711726 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1711727 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1711729 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711730 : term181 = term182.
Proof. exact (@lem1711729 term183 term183). Qed.
Lemma lem1711731 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711732 : term185 = term183.
Proof. exact (EQ_MP (@lem1711731) (@lem940073)). Qed.
Lemma lem1711733 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711734 : term182 = term24.
Proof. exact (MK_COMB (@lem1711733) (@lem1711732)). Qed.
Lemma lem1711735 : term181 = term24.
Proof. exact (TRANS (@lem1711730) (@lem1711734)). Qed.
Lemma lem1711736 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1711737 : term186 = term187.
Proof. exact (MK_COMB (@lem1711736) (@lem1711735)). Qed.
Lemma lem1711738 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1711739 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1711737) (@lem1711738 x)). Qed.
Lemma lem1711740 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1711727 x) (@lem1711739 x)). Qed.
Lemma lem1711741 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1711742 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1711740 x) (@lem1711741 x)). Qed.
Lemma lem1711743 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1711744 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1711743) (@lem1711742 x)). Qed.
Lemma lem1711745 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1711746 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1711744 x) (@lem1711745 x)). Qed.
Lemma lem1711747 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1711726 x) (@lem1711746 x)). Qed.
Lemma lem1711748 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1711725 x) (@lem1711747 x)). Qed.
Lemma lem1711749 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1711750 (x : real) : (term272 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1711749) (@lem1711748 x)). Qed.
Lemma lem1711751 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711752 (x : real) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem1711750 x) (@lem1711751)). Qed.
Lemma lem1711753 (x : real) : (term98 x) = (term273 x).
Proof. exact (TRANS (@lem1711714 x) (@lem1711752 x)). Qed.
Lemma lem1711754 : term142 = term274.
Proof. exact (@lem1483554 term60 term138). Qed.
Lemma lem1711758 : term138 = term181.
Proof. exact (@lem1483512 term60). Qed.
Lemma lem1711760 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711761 : term181 = term182.
Proof. exact (@lem1711760 term183 term183). Qed.
Lemma lem1711762 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711763 : term185 = term183.
Proof. exact (EQ_MP (@lem1711762) (@lem940073)). Qed.
Lemma lem1711764 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711765 : term182 = term24.
Proof. exact (MK_COMB (@lem1711764) (@lem1711763)). Qed.
Lemma lem1711766 : term181 = term24.
Proof. exact (TRANS (@lem1711761) (@lem1711765)). Qed.
Lemma lem1711768 : term138 = term24.
Proof. exact (TRANS (@lem1711758) (@lem1711766)). Qed.
Lemma lem1711771 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem1711772 : term276 = term277.
Proof. exact (MK_COMB (@lem1711771) (@lem1711768)). Qed.
Lemma lem1711773 : term277 = term278.
Proof. exact (@lem1483519 term60 term24). Qed.
Lemma lem1711775 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1711776 : term255 = term256.
Proof. exact (@lem1711775 term183 term183). Qed.
Lemma lem1711777 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711778 : term185 = term183.
Proof. exact (EQ_MP (@lem1711777) (@lem940073)). Qed.
Lemma lem1711779 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711780 : term182 = term24.
Proof. exact (MK_COMB (@lem1711779) (@lem1711778)). Qed.
Lemma lem1711781 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711782 : term256 = term60.
Proof. exact (MK_COMB (@lem1711781) (@lem1711780)). Qed.
Lemma lem1711783 : term255 = term60.
Proof. exact (TRANS (@lem1711776) (@lem1711782)). Qed.
Lemma lem1711784 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem1711785 : term278 = term280.
Proof. exact (MK_COMB (@lem1711784) (@lem1711783)). Qed.
Lemma lem1711786 : term280 = term281.
Proof. exact (@lem1367763 term183 term183). Qed.
Lemma lem1711787 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem1711788 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem1711789 : term217 = term218.
Proof. exact (EQ_MP (@lem1711788) (@lem1711787)). Qed.
Lemma lem1711790 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711791 : term214 = term219.
Proof. exact (MK_COMB (@lem1711790) (@lem1711789)). Qed.
Lemma lem1711792 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711793 : term281 = term221.
Proof. exact (MK_COMB (@lem1711792) (@lem1711791)). Qed.
Lemma lem1711794 : term280 = term221.
Proof. exact (TRANS (@lem1711786) (@lem1711793)). Qed.
Lemma lem1711795 : term278 = term221.
Proof. exact (TRANS (@lem1711785) (@lem1711794)). Qed.
Lemma lem1711796 : term277 = term221.
Proof. exact (TRANS (@lem1711773) (@lem1711795)). Qed.
Lemma lem1711797 : term276 = term221.
Proof. exact (TRANS (@lem1711772) (@lem1711796)). Qed.
Lemma lem1711798 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711799 : term282 = term283.
Proof. exact (MK_COMB (@lem1711798) (@lem1711797)). Qed.
Lemma lem1711800 : term283 = term284.
Proof. exact (@lem1483512 term221). Qed.
Lemma lem1711802 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711803 : term284 = term228.
Proof. exact (@lem1711802 term183 term218). Qed.
Lemma lem1711804 : term226 = term216.
Proof. exact (@lem996238 term216). Qed.
Lemma lem1711805 : (term226 = term216) = (term227 = term218).
Proof. exact (@lem1007663 (BIT1 0) term216 term216). Qed.
Lemma lem1711806 : term227 = term218.
Proof. exact (EQ_MP (@lem1711805) (@lem1711804)). Qed.
Lemma lem1711807 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711808 : term228 = term219.
Proof. exact (MK_COMB (@lem1711807) (@lem1711806)). Qed.
Lemma lem1711809 : term284 = term219.
Proof. exact (TRANS (@lem1711803) (@lem1711808)). Qed.
Lemma lem1711810 : term283 = term219.
Proof. exact (TRANS (@lem1711800) (@lem1711809)). Qed.
Lemma lem1711811 : term285 = term285.
Proof. exact (eq_refl term285). Qed.
Lemma lem1711812 : (term282 = term283) = (term282 = term219).
Proof. exact (MK_COMB (@lem1711811) (@lem1711810)). Qed.
Lemma lem1711813 : term282 = term219.
Proof. exact (EQ_MP (@lem1711812) (@lem1711799)). Qed.
Lemma lem1711814 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711815 : term286 = term235.
Proof. exact (MK_COMB (@lem1711814) (@lem1711813)). Qed.
Lemma lem1711816 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711817 : term287 = term237.
Proof. exact (MK_COMB (@lem1711815) (@lem1711816)). Qed.
Lemma lem1711818 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711819 : term288 = term231.
Proof. exact (MK_COMB (@lem1711818) (@lem1711797)). Qed.
Lemma lem1711820 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711821 : term289 = term233.
Proof. exact (MK_COMB (@lem1711819) (@lem1711820)). Qed.
Lemma lem1711822 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711823 : term290 = term291.
Proof. exact (MK_COMB (@lem1711822) (@lem1711821)). Qed.
Lemma lem1711824 : term274 = term292.
Proof. exact (MK_COMB (@lem1711823) (@lem1711817)). Qed.
Lemma lem1711825 : term142 = term292.
Proof. exact (TRANS (@lem1711754) (@lem1711824)). Qed.
Lemma lem1711826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1711827 (x : real) : (term54 x) = (term293 x).
Proof. exact (MK_COMB (@lem1711826) (@lem1711753 x)). Qed.
Lemma lem1711828 (x : real) : (term143 x) = (term294 x).
Proof. exact (MK_COMB (@lem1711827 x) (@lem1711825)). Qed.
Lemma lem1711829 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711830 (x : real) : (term141 x) = (term295 x).
Proof. exact (MK_COMB (@lem1711829) (@lem1711713 x)). Qed.
Lemma lem1711831 (x : real) : (term144 x) = (term296 x).
Proof. exact (MK_COMB (@lem1711830 x) (@lem1711828 x)). Qed.
Lemma lem1711832 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1711833 (x : real) : (term89 x) = (term297 x).
Proof. exact (MK_COMB (@lem1711832) (@lem1711623 x)). Qed.
Lemma lem1711834 (x : real) : (term145 x) = (term298 x).
Proof. exact (MK_COMB (@lem1711833 x) (@lem1711831 x)). Qed.
Lemma lem1711835 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711836 (x : real) : (term101 x) = (term299 x).
Proof. exact (MK_COMB (@lem1711835) (@lem1711604 x)). Qed.
Lemma lem1711837 (x : real) : (term146 x) = (term300 x).
Proof. exact (MK_COMB (@lem1711836 x) (@lem1711834 x)). Qed.
Lemma lem1711838 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1711839 (x : real) : (term123 x) = (term243 x).
Proof. exact (MK_COMB (@lem1711838) (@lem1711493 x)). Qed.
Lemma lem1711840 (x : real) : (term147 x) = (term301 x).
Proof. exact (MK_COMB (@lem1711839 x) (@lem1711837 x)). Qed.
Lemma lem1711841 (x : real) : (term302 x) = (term303 x).
Proof. exact (@lem1483531 (real_neg x) term75). Qed.
Lemma lem1711842 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711849 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1711850 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1711851 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1711850) (@lem1711849 x)). Qed.
Lemma lem1711852 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1711851 x) (@lem1711842)). Qed.
Lemma lem1711853 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1711855 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1711856 : term197 = term75.
Proof. exact (@lem1711855 term183). Qed.
Lemma lem1711857 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1711858 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1711857 x) (@lem1711856)). Qed.
Lemma lem1711859 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1711860 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1711858 x) (@lem1711859 x)). Qed.
Lemma lem1711861 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1711853 x) (@lem1711860 x)). Qed.
Lemma lem1711862 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1711852 x) (@lem1711861 x)). Qed.
Lemma lem1711863 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1711864 (x : real) : (term304 x) = (term248 x).
Proof. exact (MK_COMB (@lem1711863) (@lem1711862 x)). Qed.
Lemma lem1711865 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711866 (x : real) : (term303 x) = (term249 x).
Proof. exact (MK_COMB (@lem1711864 x) (@lem1711865)). Qed.
Lemma lem1711867 (x : real) : (term302 x) = (term249 x).
Proof. exact (TRANS (@lem1711841 x) (@lem1711866 x)). Qed.
Lemma lem1711868 (x : real) : (term41 x) = (term193 x).
Proof. exact (@lem1483521 x term75). Qed.
Lemma lem1711874 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem1483519 x term75). Qed.
Lemma lem1711876 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1711877 : term197 = term75.
Proof. exact (@lem1711876 term183). Qed.
Lemma lem1711878 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1711879 (x : real) : (term195 x) = (term198 x).
Proof. exact (MK_COMB (@lem1711878 x) (@lem1711877)). Qed.
Lemma lem1711880 (x : real) : (term198 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1711881 (x : real) : (term195 x) = x.
Proof. exact (TRANS (@lem1711879 x) (@lem1711880 x)). Qed.
Lemma lem1711883 (x : real) : (term194 x) = x.
Proof. exact (TRANS (@lem1711874 x) (@lem1711881 x)). Qed.
Lemma lem1711884 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711885 (x : real) : (term199 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1711884) (@lem1711883 x)). Qed.
Lemma lem1711886 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711887 (x : real) : (term193 x) = (term192 x).
Proof. exact (MK_COMB (@lem1711885 x) (@lem1711886)). Qed.
Lemma lem1711888 (x : real) : (term41 x) = (term192 x).
Proof. exact (TRANS (@lem1711868 x) (@lem1711887 x)). Qed.
Lemma lem1711889 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1711890 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711897 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1711898 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1711899 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1711898) (@lem1711897 x)). Qed.
Lemma lem1711900 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1711899 x) (@lem1711890)). Qed.
Lemma lem1711901 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1711903 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1711904 : term197 = term75.
Proof. exact (@lem1711903 term183). Qed.
Lemma lem1711905 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1711906 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1711905 x) (@lem1711904)). Qed.
Lemma lem1711907 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1711908 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1711906 x) (@lem1711907 x)). Qed.
Lemma lem1711909 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1711901 x) (@lem1711908 x)). Qed.
Lemma lem1711910 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1711900 x) (@lem1711909 x)). Qed.
Lemma lem1711911 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711912 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1711911) (@lem1711910 x)). Qed.
Lemma lem1711913 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711914 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1711912 x) (@lem1711913)). Qed.
Lemma lem1711915 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1711889 x) (@lem1711914 x)). Qed.
Lemma lem1711916 : term61 = term209.
Proof. exact (@lem1483554 term24 term60). Qed.
Lemma lem1711922 : term210 = term211.
Proof. exact (@lem1483519 term24 term60). Qed.
Lemma lem1711924 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711925 : term181 = term182.
Proof. exact (@lem1711924 term183 term183). Qed.
Lemma lem1711926 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711927 : term185 = term183.
Proof. exact (EQ_MP (@lem1711926) (@lem940073)). Qed.
Lemma lem1711928 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711929 : term182 = term24.
Proof. exact (MK_COMB (@lem1711928) (@lem1711927)). Qed.
Lemma lem1711930 : term181 = term24.
Proof. exact (TRANS (@lem1711925) (@lem1711929)). Qed.
Lemma lem1711931 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1711932 : term211 = term213.
Proof. exact (MK_COMB (@lem1711931) (@lem1711930)). Qed.
Lemma lem1711933 : term213 = term214.
Proof. exact (@lem1367770 term183 term183). Qed.
Lemma lem1711934 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem1711935 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem1711936 : term217 = term218.
Proof. exact (EQ_MP (@lem1711935) (@lem1711934)). Qed.
Lemma lem1711937 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711938 : term214 = term219.
Proof. exact (MK_COMB (@lem1711937) (@lem1711936)). Qed.
Lemma lem1711939 : term213 = term219.
Proof. exact (TRANS (@lem1711933) (@lem1711938)). Qed.
Lemma lem1711940 : term211 = term219.
Proof. exact (TRANS (@lem1711932) (@lem1711939)). Qed.
Lemma lem1711942 : term210 = term219.
Proof. exact (TRANS (@lem1711922) (@lem1711940)). Qed.
Lemma lem1711943 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711944 : term220 = term221.
Proof. exact (MK_COMB (@lem1711943) (@lem1711942)). Qed.
Lemma lem1711945 : term221 = term222.
Proof. exact (@lem1483512 term219). Qed.
Lemma lem1711947 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1711948 : term222 = term225.
Proof. exact (@lem1711947 term183 term218). Qed.
Lemma lem1711949 : term226 = term216.
Proof. exact (@lem996238 term216). Qed.
Lemma lem1711950 : (term226 = term216) = (term227 = term218).
Proof. exact (@lem1007663 (BIT1 0) term216 term216). Qed.
Lemma lem1711951 : term227 = term218.
Proof. exact (EQ_MP (@lem1711950) (@lem1711949)). Qed.
Lemma lem1711952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711953 : term228 = term219.
Proof. exact (MK_COMB (@lem1711952) (@lem1711951)). Qed.
Lemma lem1711954 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1711955 : term225 = term221.
Proof. exact (MK_COMB (@lem1711954) (@lem1711953)). Qed.
Lemma lem1711956 : term222 = term221.
Proof. exact (TRANS (@lem1711948) (@lem1711955)). Qed.
Lemma lem1711957 : term221 = term221.
Proof. exact (TRANS (@lem1711945) (@lem1711956)). Qed.
Lemma lem1711958 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem1711959 : (term220 = term221) = (term220 = term221).
Proof. exact (MK_COMB (@lem1711958) (@lem1711957)). Qed.
Lemma lem1711960 : term220 = term221.
Proof. exact (EQ_MP (@lem1711959) (@lem1711944)). Qed.
Lemma lem1711961 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711962 : term230 = term231.
Proof. exact (MK_COMB (@lem1711961) (@lem1711960)). Qed.
Lemma lem1711963 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711964 : term232 = term233.
Proof. exact (MK_COMB (@lem1711962) (@lem1711963)). Qed.
Lemma lem1711965 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1711966 : term234 = term235.
Proof. exact (MK_COMB (@lem1711965) (@lem1711942)). Qed.
Lemma lem1711967 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1711968 : term236 = term237.
Proof. exact (MK_COMB (@lem1711966) (@lem1711967)). Qed.
Lemma lem1711969 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1711970 : term238 = term239.
Proof. exact (MK_COMB (@lem1711969) (@lem1711968)). Qed.
Lemma lem1711971 : term209 = term240.
Proof. exact (MK_COMB (@lem1711970) (@lem1711964)). Qed.
Lemma lem1711972 : term61 = term240.
Proof. exact (TRANS (@lem1711916) (@lem1711971)). Qed.
Lemma lem1711973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1711974 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1711973) (@lem1711915 x)). Qed.
Lemma lem1711975 (x : real) : (term62 x) = (term242 x).
Proof. exact (MK_COMB (@lem1711974 x) (@lem1711972)). Qed.
Lemma lem1711976 (x : real) : (term98 x) = (term271 x).
Proof. exact (@lem1483531 term75 (real_neg x)). Qed.
Lemma lem1711983 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1711986 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1711987 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1711986) (@lem1711983 x)). Qed.
Lemma lem1711988 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1711989 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1711991 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1711992 : term181 = term182.
Proof. exact (@lem1711991 term183 term183). Qed.
Lemma lem1711993 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1711994 : term185 = term183.
Proof. exact (EQ_MP (@lem1711993) (@lem940073)). Qed.
Lemma lem1711995 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1711996 : term182 = term24.
Proof. exact (MK_COMB (@lem1711995) (@lem1711994)). Qed.
Lemma lem1711997 : term181 = term24.
Proof. exact (TRANS (@lem1711992) (@lem1711996)). Qed.
Lemma lem1711998 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1711999 : term186 = term187.
Proof. exact (MK_COMB (@lem1711998) (@lem1711997)). Qed.
Lemma lem1712000 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1712001 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1711999) (@lem1712000 x)). Qed.
Lemma lem1712002 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1711989 x) (@lem1712001 x)). Qed.
Lemma lem1712003 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1712004 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1712002 x) (@lem1712003 x)). Qed.
Lemma lem1712005 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712006 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1712005) (@lem1712004 x)). Qed.
Lemma lem1712007 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1712008 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1712006 x) (@lem1712007 x)). Qed.
Lemma lem1712009 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1711988 x) (@lem1712008 x)). Qed.
Lemma lem1712010 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1711987 x) (@lem1712009 x)). Qed.
Lemma lem1712011 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712012 (x : real) : (term272 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1712011) (@lem1712010 x)). Qed.
Lemma lem1712013 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712014 (x : real) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem1712012 x) (@lem1712013)). Qed.
Lemma lem1712015 (x : real) : (term98 x) = (term273 x).
Proof. exact (TRANS (@lem1711976 x) (@lem1712014 x)). Qed.
Lemma lem1712016 : term78 = term305.
Proof. exact (@lem1483554 term75 term60). Qed.
Lemma lem1712022 : term306 = term307.
Proof. exact (@lem1483519 term75 term60). Qed.
Lemma lem1712024 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712025 : term181 = term182.
Proof. exact (@lem1712024 term183 term183). Qed.
Lemma lem1712026 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712027 : term185 = term183.
Proof. exact (EQ_MP (@lem1712026) (@lem940073)). Qed.
Lemma lem1712028 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712029 : term182 = term24.
Proof. exact (MK_COMB (@lem1712028) (@lem1712027)). Qed.
Lemma lem1712030 : term181 = term24.
Proof. exact (TRANS (@lem1712025) (@lem1712029)). Qed.
Lemma lem1712031 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712032 : term307 = term308.
Proof. exact (MK_COMB (@lem1712031) (@lem1712030)). Qed.
Lemma lem1712033 : term308 = term24.
Proof. exact (@lem1483448 term24). Qed.
Lemma lem1712034 : term307 = term24.
Proof. exact (TRANS (@lem1712032) (@lem1712033)). Qed.
Lemma lem1712036 : term306 = term24.
Proof. exact (TRANS (@lem1712022) (@lem1712034)). Qed.
Lemma lem1712037 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712038 : term309 = term60.
Proof. exact (MK_COMB (@lem1712037) (@lem1712036)). Qed.
Lemma lem1712039 : term60 = term255.
Proof. exact (@lem1483512 term24). Qed.
Lemma lem1712041 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712042 : term255 = term256.
Proof. exact (@lem1712041 term183 term183). Qed.
Lemma lem1712043 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712044 : term185 = term183.
Proof. exact (EQ_MP (@lem1712043) (@lem940073)). Qed.
Lemma lem1712045 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712046 : term182 = term24.
Proof. exact (MK_COMB (@lem1712045) (@lem1712044)). Qed.
Lemma lem1712047 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712048 : term256 = term60.
Proof. exact (MK_COMB (@lem1712047) (@lem1712046)). Qed.
Lemma lem1712049 : term255 = term60.
Proof. exact (TRANS (@lem1712042) (@lem1712048)). Qed.
Lemma lem1712050 : term60 = term60.
Proof. exact (TRANS (@lem1712039) (@lem1712049)). Qed.
Lemma lem1712051 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem1712052 : (term309 = term60) = (term309 = term60).
Proof. exact (MK_COMB (@lem1712051) (@lem1712050)). Qed.
Lemma lem1712053 : term309 = term60.
Proof. exact (EQ_MP (@lem1712052) (@lem1712038)). Qed.
Lemma lem1712054 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712055 : term311 = term312.
Proof. exact (MK_COMB (@lem1712054) (@lem1712053)). Qed.
Lemma lem1712056 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712057 : term313 = term314.
Proof. exact (MK_COMB (@lem1712055) (@lem1712056)). Qed.
Lemma lem1712058 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712059 : term315 = term316.
Proof. exact (MK_COMB (@lem1712058) (@lem1712036)). Qed.
Lemma lem1712060 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712061 : term317 = term318.
Proof. exact (MK_COMB (@lem1712059) (@lem1712060)). Qed.
Lemma lem1712062 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712063 : term319 = term320.
Proof. exact (MK_COMB (@lem1712062) (@lem1712061)). Qed.
Lemma lem1712064 : term305 = term321.
Proof. exact (MK_COMB (@lem1712063) (@lem1712057)). Qed.
Lemma lem1712065 : term78 = term321.
Proof. exact (TRANS (@lem1712016) (@lem1712064)). Qed.
Lemma lem1712066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712067 (x : real) : (term54 x) = (term293 x).
Proof. exact (MK_COMB (@lem1712066) (@lem1712015 x)). Qed.
Lemma lem1712068 (x : real) : (term79 x) = (term322 x).
Proof. exact (MK_COMB (@lem1712067 x) (@lem1712065)). Qed.
Lemma lem1712069 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712070 (x : real) : (term63 x) = (term323 x).
Proof. exact (MK_COMB (@lem1712069) (@lem1711975 x)). Qed.
Lemma lem1712071 (x : real) : (term80 x) = (term324 x).
Proof. exact (MK_COMB (@lem1712070 x) (@lem1712068 x)). Qed.
Lemma lem1712072 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712073 (x : real) : (term81 x) = (term243 x).
Proof. exact (MK_COMB (@lem1712072) (@lem1711888 x)). Qed.
Lemma lem1712074 (x : real) : (term83 x) = (term325 x).
Proof. exact (MK_COMB (@lem1712073 x) (@lem1712071 x)). Qed.
Lemma lem1712075 (x : real) : (term245 x) = (term246 x).
Proof. exact (@lem1483531 term75 x). Qed.
Lemma lem1712081 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem1483519 term75 x). Qed.
Lemma lem1712086 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483448 (term168 x)). Qed.
Lemma lem1712088 (x : real) : (term166 x) = (term168 x).
Proof. exact (TRANS (@lem1712081 x) (@lem1712086 x)). Qed.
Lemma lem1712089 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712090 (x : real) : (term247 x) = (term248 x).
Proof. exact (MK_COMB (@lem1712089) (@lem1712088 x)). Qed.
Lemma lem1712091 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712092 (x : real) : (term246 x) = (term249 x).
Proof. exact (MK_COMB (@lem1712090 x) (@lem1712091)). Qed.
Lemma lem1712093 (x : real) : (term245 x) = (term249 x).
Proof. exact (TRANS (@lem1712075 x) (@lem1712092 x)). Qed.
Lemma lem1712094 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1712095 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712102 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712103 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1712104 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1712103) (@lem1712102 x)). Qed.
Lemma lem1712105 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1712104 x) (@lem1712095)). Qed.
Lemma lem1712106 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1712108 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712109 : term197 = term75.
Proof. exact (@lem1712108 term183). Qed.
Lemma lem1712110 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1712111 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1712110 x) (@lem1712109)). Qed.
Lemma lem1712112 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1712113 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1712111 x) (@lem1712112 x)). Qed.
Lemma lem1712114 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1712106 x) (@lem1712113 x)). Qed.
Lemma lem1712115 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1712105 x) (@lem1712114 x)). Qed.
Lemma lem1712116 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712117 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1712116) (@lem1712115 x)). Qed.
Lemma lem1712118 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712119 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1712117 x) (@lem1712118)). Qed.
Lemma lem1712120 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1712094 x) (@lem1712119 x)). Qed.
Lemma lem1712121 : term139 = term250.
Proof. exact (@lem1483554 term24 term138). Qed.
Lemma lem1712125 : term138 = term181.
Proof. exact (@lem1483512 term60). Qed.
Lemma lem1712127 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712128 : term181 = term182.
Proof. exact (@lem1712127 term183 term183). Qed.
Lemma lem1712129 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712130 : term185 = term183.
Proof. exact (EQ_MP (@lem1712129) (@lem940073)). Qed.
Lemma lem1712131 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712132 : term182 = term24.
Proof. exact (MK_COMB (@lem1712131) (@lem1712130)). Qed.
Lemma lem1712133 : term181 = term24.
Proof. exact (TRANS (@lem1712128) (@lem1712132)). Qed.
Lemma lem1712135 : term138 = term24.
Proof. exact (TRANS (@lem1712125) (@lem1712133)). Qed.
Lemma lem1712138 : term251 = term251.
Proof. exact (eq_refl term251). Qed.
Lemma lem1712139 : term252 = term253.
Proof. exact (MK_COMB (@lem1712138) (@lem1712135)). Qed.
Lemma lem1712140 : term253 = term254.
Proof. exact (@lem1483519 term24 term24). Qed.
Lemma lem1712142 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712143 : term255 = term256.
Proof. exact (@lem1712142 term183 term183). Qed.
Lemma lem1712144 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712145 : term185 = term183.
Proof. exact (EQ_MP (@lem1712144) (@lem940073)). Qed.
Lemma lem1712146 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712147 : term182 = term24.
Proof. exact (MK_COMB (@lem1712146) (@lem1712145)). Qed.
Lemma lem1712148 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712149 : term256 = term60.
Proof. exact (MK_COMB (@lem1712148) (@lem1712147)). Qed.
Lemma lem1712150 : term255 = term60.
Proof. exact (TRANS (@lem1712143) (@lem1712149)). Qed.
Lemma lem1712151 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1712152 : term254 = term257.
Proof. exact (MK_COMB (@lem1712151) (@lem1712150)). Qed.
Lemma lem1712154 (m : nat) : (term258 m) = term75.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1712155 : term257 = term75.
Proof. exact (@lem1712154 term183). Qed.
Lemma lem1712156 : term254 = term75.
Proof. exact (TRANS (@lem1712152) (@lem1712155)). Qed.
Lemma lem1712157 : term253 = term75.
Proof. exact (TRANS (@lem1712140) (@lem1712156)). Qed.
Lemma lem1712158 : term252 = term75.
Proof. exact (TRANS (@lem1712139) (@lem1712157)). Qed.
Lemma lem1712159 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712160 : term259 = term114.
Proof. exact (MK_COMB (@lem1712159) (@lem1712158)). Qed.
Lemma lem1712161 : term114 = term197.
Proof. exact (@lem1483512 term75). Qed.
Lemma lem1712163 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712164 : term197 = term75.
Proof. exact (@lem1712163 term183). Qed.
Lemma lem1712165 : term114 = term75.
Proof. exact (TRANS (@lem1712161) (@lem1712164)). Qed.
Lemma lem1712166 : term260 = term260.
Proof. exact (eq_refl term260). Qed.
Lemma lem1712167 : (term259 = term114) = (term259 = term75).
Proof. exact (MK_COMB (@lem1712166) (@lem1712165)). Qed.
Lemma lem1712168 : term259 = term75.
Proof. exact (EQ_MP (@lem1712167) (@lem1712160)). Qed.
Lemma lem1712169 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712170 : term261 = term262.
Proof. exact (MK_COMB (@lem1712169) (@lem1712168)). Qed.
Lemma lem1712171 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712172 : term263 = term264.
Proof. exact (MK_COMB (@lem1712170) (@lem1712171)). Qed.
Lemma lem1712173 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712174 : term265 = term262.
Proof. exact (MK_COMB (@lem1712173) (@lem1712158)). Qed.
Lemma lem1712175 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712176 : term266 = term264.
Proof. exact (MK_COMB (@lem1712174) (@lem1712175)). Qed.
Lemma lem1712177 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712178 : term267 = term268.
Proof. exact (MK_COMB (@lem1712177) (@lem1712176)). Qed.
Lemma lem1712179 : term250 = term269.
Proof. exact (MK_COMB (@lem1712178) (@lem1712172)). Qed.
Lemma lem1712180 : term139 = term269.
Proof. exact (TRANS (@lem1712121) (@lem1712179)). Qed.
Lemma lem1712181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712182 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1712181) (@lem1712120 x)). Qed.
Lemma lem1712183 (x : real) : (term140 x) = (term270 x).
Proof. exact (MK_COMB (@lem1712182 x) (@lem1712180)). Qed.
Lemma lem1712184 (x : real) : (term98 x) = (term271 x).
Proof. exact (@lem1483531 term75 (real_neg x)). Qed.
Lemma lem1712191 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712194 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1712195 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1712194) (@lem1712191 x)). Qed.
Lemma lem1712196 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1712197 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1712199 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712200 : term181 = term182.
Proof. exact (@lem1712199 term183 term183). Qed.
Lemma lem1712201 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712202 : term185 = term183.
Proof. exact (EQ_MP (@lem1712201) (@lem940073)). Qed.
Lemma lem1712203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712204 : term182 = term24.
Proof. exact (MK_COMB (@lem1712203) (@lem1712202)). Qed.
Lemma lem1712205 : term181 = term24.
Proof. exact (TRANS (@lem1712200) (@lem1712204)). Qed.
Lemma lem1712206 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1712207 : term186 = term187.
Proof. exact (MK_COMB (@lem1712206) (@lem1712205)). Qed.
Lemma lem1712208 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1712209 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1712207) (@lem1712208 x)). Qed.
Lemma lem1712210 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1712197 x) (@lem1712209 x)). Qed.
Lemma lem1712211 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1712212 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1712210 x) (@lem1712211 x)). Qed.
Lemma lem1712213 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712214 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1712213) (@lem1712212 x)). Qed.
Lemma lem1712215 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1712216 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1712214 x) (@lem1712215 x)). Qed.
Lemma lem1712217 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1712196 x) (@lem1712216 x)). Qed.
Lemma lem1712218 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1712195 x) (@lem1712217 x)). Qed.
Lemma lem1712219 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712220 (x : real) : (term272 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1712219) (@lem1712218 x)). Qed.
Lemma lem1712221 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712222 (x : real) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem1712220 x) (@lem1712221)). Qed.
Lemma lem1712223 (x : real) : (term98 x) = (term273 x).
Proof. exact (TRANS (@lem1712184 x) (@lem1712222 x)). Qed.
Lemma lem1712224 : term149 = term326.
Proof. exact (@lem1483554 term75 term138). Qed.
Lemma lem1712228 : term138 = term181.
Proof. exact (@lem1483512 term60). Qed.
Lemma lem1712230 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712231 : term181 = term182.
Proof. exact (@lem1712230 term183 term183). Qed.
Lemma lem1712232 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712233 : term185 = term183.
Proof. exact (EQ_MP (@lem1712232) (@lem940073)). Qed.
Lemma lem1712234 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712235 : term182 = term24.
Proof. exact (MK_COMB (@lem1712234) (@lem1712233)). Qed.
Lemma lem1712236 : term181 = term24.
Proof. exact (TRANS (@lem1712231) (@lem1712235)). Qed.
Lemma lem1712238 : term138 = term24.
Proof. exact (TRANS (@lem1712228) (@lem1712236)). Qed.
Lemma lem1712241 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1712242 : term327 = term328.
Proof. exact (MK_COMB (@lem1712241) (@lem1712238)). Qed.
Lemma lem1712243 : term328 = term329.
Proof. exact (@lem1483519 term75 term24). Qed.
Lemma lem1712245 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712246 : term255 = term256.
Proof. exact (@lem1712245 term183 term183). Qed.
Lemma lem1712247 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712248 : term185 = term183.
Proof. exact (EQ_MP (@lem1712247) (@lem940073)). Qed.
Lemma lem1712249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712250 : term182 = term24.
Proof. exact (MK_COMB (@lem1712249) (@lem1712248)). Qed.
Lemma lem1712251 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712252 : term256 = term60.
Proof. exact (MK_COMB (@lem1712251) (@lem1712250)). Qed.
Lemma lem1712253 : term255 = term60.
Proof. exact (TRANS (@lem1712246) (@lem1712252)). Qed.
Lemma lem1712254 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712255 : term329 = term330.
Proof. exact (MK_COMB (@lem1712254) (@lem1712253)). Qed.
Lemma lem1712256 : term330 = term60.
Proof. exact (@lem1483448 term60). Qed.
Lemma lem1712257 : term329 = term60.
Proof. exact (TRANS (@lem1712255) (@lem1712256)). Qed.
Lemma lem1712258 : term328 = term60.
Proof. exact (TRANS (@lem1712243) (@lem1712257)). Qed.
Lemma lem1712259 : term327 = term60.
Proof. exact (TRANS (@lem1712242) (@lem1712258)). Qed.
Lemma lem1712260 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712261 : term331 = term138.
Proof. exact (MK_COMB (@lem1712260) (@lem1712259)). Qed.
Lemma lem1712262 : term138 = term181.
Proof. exact (@lem1483512 term60). Qed.
Lemma lem1712264 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712265 : term181 = term182.
Proof. exact (@lem1712264 term183 term183). Qed.
Lemma lem1712266 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712267 : term185 = term183.
Proof. exact (EQ_MP (@lem1712266) (@lem940073)). Qed.
Lemma lem1712268 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712269 : term182 = term24.
Proof. exact (MK_COMB (@lem1712268) (@lem1712267)). Qed.
Lemma lem1712270 : term181 = term24.
Proof. exact (TRANS (@lem1712265) (@lem1712269)). Qed.
Lemma lem1712271 : term138 = term24.
Proof. exact (TRANS (@lem1712262) (@lem1712270)). Qed.
Lemma lem1712272 : term332 = term332.
Proof. exact (eq_refl term332). Qed.
Lemma lem1712273 : (term331 = term138) = (term331 = term24).
Proof. exact (MK_COMB (@lem1712272) (@lem1712271)). Qed.
Lemma lem1712274 : term331 = term24.
Proof. exact (EQ_MP (@lem1712273) (@lem1712261)). Qed.
Lemma lem1712275 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712276 : term333 = term316.
Proof. exact (MK_COMB (@lem1712275) (@lem1712274)). Qed.
Lemma lem1712277 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712278 : term334 = term318.
Proof. exact (MK_COMB (@lem1712276) (@lem1712277)). Qed.
Lemma lem1712279 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712280 : term335 = term312.
Proof. exact (MK_COMB (@lem1712279) (@lem1712259)). Qed.
Lemma lem1712281 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712282 : term336 = term314.
Proof. exact (MK_COMB (@lem1712280) (@lem1712281)). Qed.
Lemma lem1712283 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712284 : term337 = term338.
Proof. exact (MK_COMB (@lem1712283) (@lem1712282)). Qed.
Lemma lem1712285 : term326 = term339.
Proof. exact (MK_COMB (@lem1712284) (@lem1712278)). Qed.
Lemma lem1712286 : term149 = term339.
Proof. exact (TRANS (@lem1712224) (@lem1712285)). Qed.
Lemma lem1712287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712288 (x : real) : (term54 x) = (term293 x).
Proof. exact (MK_COMB (@lem1712287) (@lem1712223 x)). Qed.
Lemma lem1712289 (x : real) : (term150 x) = (term340 x).
Proof. exact (MK_COMB (@lem1712288 x) (@lem1712286)). Qed.
Lemma lem1712290 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712291 (x : real) : (term141 x) = (term295 x).
Proof. exact (MK_COMB (@lem1712290) (@lem1712183 x)). Qed.
Lemma lem1712292 (x : real) : (term151 x) = (term341 x).
Proof. exact (MK_COMB (@lem1712291 x) (@lem1712289 x)). Qed.
Lemma lem1712293 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712294 (x : real) : (term89 x) = (term297 x).
Proof. exact (MK_COMB (@lem1712293) (@lem1712093 x)). Qed.
Lemma lem1712295 (x : real) : (term152 x) = (term342 x).
Proof. exact (MK_COMB (@lem1712294 x) (@lem1712292 x)). Qed.
Lemma lem1712296 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712297 (x : real) : (term85 x) = (term343 x).
Proof. exact (MK_COMB (@lem1712296) (@lem1712074 x)). Qed.
Lemma lem1712298 (x : real) : (term153 x) = (term344 x).
Proof. exact (MK_COMB (@lem1712297 x) (@lem1712295 x)). Qed.
Lemma lem1712299 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712300 (x : real) : (term133 x) = (term297 x).
Proof. exact (MK_COMB (@lem1712299) (@lem1711867 x)). Qed.
Lemma lem1712301 (x : real) : (term154 x) = (term345 x).
Proof. exact (MK_COMB (@lem1712300 x) (@lem1712298 x)). Qed.
Lemma lem1712302 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712303 (x : real) : (term148 x) = (term346 x).
Proof. exact (MK_COMB (@lem1712302) (@lem1711840 x)). Qed.
Lemma lem1712304 (x : real) : (term155 x) = (term347 x).
Proof. exact (MK_COMB (@lem1712303 x) (@lem1712301 x)). Qed.
Lemma lem1712305 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712306 (x : real) : (term348 x) = (term241 x).
Proof. exact (MK_COMB (@lem1712305) (@lem1711453 x)). Qed.
Lemma lem1712307 (x : real) : (term349 x) = (term350 x).
Proof. exact (MK_COMB (@lem1712306 x) (@lem1712304 x)). Qed.
Lemma lem1712308 (x : real) : (term351 x) = (term352 x).
Proof. exact (@lem1483531 x term75). Qed.
Lemma lem1712314 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem1483519 x term75). Qed.
Lemma lem1712316 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712317 : term197 = term75.
Proof. exact (@lem1712316 term183). Qed.
Lemma lem1712318 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1712319 (x : real) : (term195 x) = (term198 x).
Proof. exact (MK_COMB (@lem1712318 x) (@lem1712317)). Qed.
Lemma lem1712320 (x : real) : (term198 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1712321 (x : real) : (term195 x) = x.
Proof. exact (TRANS (@lem1712319 x) (@lem1712320 x)). Qed.
Lemma lem1712323 (x : real) : (term194 x) = x.
Proof. exact (TRANS (@lem1712314 x) (@lem1712321 x)). Qed.
Lemma lem1712324 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712325 (x : real) : (term353 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1712324) (@lem1712323 x)). Qed.
Lemma lem1712326 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712327 (x : real) : (term352 x) = (term273 x).
Proof. exact (MK_COMB (@lem1712325 x) (@lem1712326)). Qed.
Lemma lem1712328 (x : real) : (term351 x) = (term273 x).
Proof. exact (TRANS (@lem1712308 x) (@lem1712327 x)). Qed.
Lemma lem1712329 (x : real) : (term71 x) = (term172 x).
Proof. exact (@lem1483521 term75 (real_neg x)). Qed.
Lemma lem1712336 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712339 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1712340 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1712339) (@lem1712336 x)). Qed.
Lemma lem1712341 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1712342 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1712344 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712345 : term181 = term182.
Proof. exact (@lem1712344 term183 term183). Qed.
Lemma lem1712346 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712347 : term185 = term183.
Proof. exact (EQ_MP (@lem1712346) (@lem940073)). Qed.
Lemma lem1712348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712349 : term182 = term24.
Proof. exact (MK_COMB (@lem1712348) (@lem1712347)). Qed.
Lemma lem1712350 : term181 = term24.
Proof. exact (TRANS (@lem1712345) (@lem1712349)). Qed.
Lemma lem1712351 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1712352 : term186 = term187.
Proof. exact (MK_COMB (@lem1712351) (@lem1712350)). Qed.
Lemma lem1712353 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1712354 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1712352) (@lem1712353 x)). Qed.
Lemma lem1712355 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1712342 x) (@lem1712354 x)). Qed.
Lemma lem1712356 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1712357 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1712355 x) (@lem1712356 x)). Qed.
Lemma lem1712358 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712359 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1712358) (@lem1712357 x)). Qed.
Lemma lem1712360 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1712361 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1712359 x) (@lem1712360 x)). Qed.
Lemma lem1712362 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1712341 x) (@lem1712361 x)). Qed.
Lemma lem1712363 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1712340 x) (@lem1712362 x)). Qed.
Lemma lem1712364 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712365 (x : real) : (term191 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1712364) (@lem1712363 x)). Qed.
Lemma lem1712366 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712367 (x : real) : (term172 x) = (term192 x).
Proof. exact (MK_COMB (@lem1712365 x) (@lem1712366)). Qed.
Lemma lem1712368 (x : real) : (term71 x) = (term192 x).
Proof. exact (TRANS (@lem1712329 x) (@lem1712367 x)). Qed.
Lemma lem1712369 (x : real) : (term41 x) = (term193 x).
Proof. exact (@lem1483521 x term75). Qed.
Lemma lem1712375 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem1483519 x term75). Qed.
Lemma lem1712377 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712378 : term197 = term75.
Proof. exact (@lem1712377 term183). Qed.
Lemma lem1712379 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1712380 (x : real) : (term195 x) = (term198 x).
Proof. exact (MK_COMB (@lem1712379 x) (@lem1712378)). Qed.
Lemma lem1712381 (x : real) : (term198 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1712382 (x : real) : (term195 x) = x.
Proof. exact (TRANS (@lem1712380 x) (@lem1712381 x)). Qed.
Lemma lem1712384 (x : real) : (term194 x) = x.
Proof. exact (TRANS (@lem1712375 x) (@lem1712382 x)). Qed.
Lemma lem1712385 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712386 (x : real) : (term199 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1712385) (@lem1712384 x)). Qed.
Lemma lem1712387 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712388 (x : real) : (term193 x) = (term192 x).
Proof. exact (MK_COMB (@lem1712386 x) (@lem1712387)). Qed.
Lemma lem1712389 (x : real) : (term41 x) = (term192 x).
Proof. exact (TRANS (@lem1712369 x) (@lem1712388 x)). Qed.
Lemma lem1712390 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1712391 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712398 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712399 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1712400 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1712399) (@lem1712398 x)). Qed.
Lemma lem1712401 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1712400 x) (@lem1712391)). Qed.
Lemma lem1712402 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1712404 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712405 : term197 = term75.
Proof. exact (@lem1712404 term183). Qed.
Lemma lem1712406 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1712407 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1712406 x) (@lem1712405)). Qed.
Lemma lem1712408 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1712409 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1712407 x) (@lem1712408 x)). Qed.
Lemma lem1712410 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1712402 x) (@lem1712409 x)). Qed.
Lemma lem1712411 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1712401 x) (@lem1712410 x)). Qed.
Lemma lem1712412 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712413 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1712412) (@lem1712411 x)). Qed.
Lemma lem1712414 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712415 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1712413 x) (@lem1712414)). Qed.
Lemma lem1712416 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1712390 x) (@lem1712415 x)). Qed.
Lemma lem1712417 : term61 = term209.
Proof. exact (@lem1483554 term24 term60). Qed.
Lemma lem1712423 : term210 = term211.
Proof. exact (@lem1483519 term24 term60). Qed.
Lemma lem1712425 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712426 : term181 = term182.
Proof. exact (@lem1712425 term183 term183). Qed.
Lemma lem1712427 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712428 : term185 = term183.
Proof. exact (EQ_MP (@lem1712427) (@lem940073)). Qed.
Lemma lem1712429 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712430 : term182 = term24.
Proof. exact (MK_COMB (@lem1712429) (@lem1712428)). Qed.
Lemma lem1712431 : term181 = term24.
Proof. exact (TRANS (@lem1712426) (@lem1712430)). Qed.
Lemma lem1712432 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1712433 : term211 = term213.
Proof. exact (MK_COMB (@lem1712432) (@lem1712431)). Qed.
Lemma lem1712434 : term213 = term214.
Proof. exact (@lem1367770 term183 term183). Qed.
Lemma lem1712435 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem1712436 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem1712437 : term217 = term218.
Proof. exact (EQ_MP (@lem1712436) (@lem1712435)). Qed.
Lemma lem1712438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712439 : term214 = term219.
Proof. exact (MK_COMB (@lem1712438) (@lem1712437)). Qed.
Lemma lem1712440 : term213 = term219.
Proof. exact (TRANS (@lem1712434) (@lem1712439)). Qed.
Lemma lem1712441 : term211 = term219.
Proof. exact (TRANS (@lem1712433) (@lem1712440)). Qed.
Lemma lem1712443 : term210 = term219.
Proof. exact (TRANS (@lem1712423) (@lem1712441)). Qed.
Lemma lem1712444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712445 : term220 = term221.
Proof. exact (MK_COMB (@lem1712444) (@lem1712443)). Qed.
Lemma lem1712446 : term221 = term222.
Proof. exact (@lem1483512 term219). Qed.
Lemma lem1712448 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712449 : term222 = term225.
Proof. exact (@lem1712448 term183 term218). Qed.
Lemma lem1712450 : term226 = term216.
Proof. exact (@lem996238 term216). Qed.
Lemma lem1712451 : (term226 = term216) = (term227 = term218).
Proof. exact (@lem1007663 (BIT1 0) term216 term216). Qed.
Lemma lem1712452 : term227 = term218.
Proof. exact (EQ_MP (@lem1712451) (@lem1712450)). Qed.
Lemma lem1712453 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712454 : term228 = term219.
Proof. exact (MK_COMB (@lem1712453) (@lem1712452)). Qed.
Lemma lem1712455 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712456 : term225 = term221.
Proof. exact (MK_COMB (@lem1712455) (@lem1712454)). Qed.
Lemma lem1712457 : term222 = term221.
Proof. exact (TRANS (@lem1712449) (@lem1712456)). Qed.
Lemma lem1712458 : term221 = term221.
Proof. exact (TRANS (@lem1712446) (@lem1712457)). Qed.
Lemma lem1712459 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem1712460 : (term220 = term221) = (term220 = term221).
Proof. exact (MK_COMB (@lem1712459) (@lem1712458)). Qed.
Lemma lem1712461 : term220 = term221.
Proof. exact (EQ_MP (@lem1712460) (@lem1712445)). Qed.
Lemma lem1712462 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712463 : term230 = term231.
Proof. exact (MK_COMB (@lem1712462) (@lem1712461)). Qed.
Lemma lem1712464 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712465 : term232 = term233.
Proof. exact (MK_COMB (@lem1712463) (@lem1712464)). Qed.
Lemma lem1712466 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712467 : term234 = term235.
Proof. exact (MK_COMB (@lem1712466) (@lem1712443)). Qed.
Lemma lem1712468 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712469 : term236 = term237.
Proof. exact (MK_COMB (@lem1712467) (@lem1712468)). Qed.
Lemma lem1712470 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712471 : term238 = term239.
Proof. exact (MK_COMB (@lem1712470) (@lem1712469)). Qed.
Lemma lem1712472 : term209 = term240.
Proof. exact (MK_COMB (@lem1712471) (@lem1712465)). Qed.
Lemma lem1712473 : term61 = term240.
Proof. exact (TRANS (@lem1712417) (@lem1712472)). Qed.
Lemma lem1712474 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712475 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1712474) (@lem1712416 x)). Qed.
Lemma lem1712476 (x : real) : (term62 x) = (term242 x).
Proof. exact (MK_COMB (@lem1712475 x) (@lem1712473)). Qed.
Lemma lem1712477 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712478 (x : real) : (term81 x) = (term243 x).
Proof. exact (MK_COMB (@lem1712477) (@lem1712389 x)). Qed.
Lemma lem1712479 (x : real) : (term100 x) = (term244 x).
Proof. exact (MK_COMB (@lem1712478 x) (@lem1712476 x)). Qed.
Lemma lem1712480 (x : real) : (term245 x) = (term246 x).
Proof. exact (@lem1483531 term75 x). Qed.
Lemma lem1712486 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem1483519 term75 x). Qed.
Lemma lem1712491 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483448 (term168 x)). Qed.
Lemma lem1712493 (x : real) : (term166 x) = (term168 x).
Proof. exact (TRANS (@lem1712486 x) (@lem1712491 x)). Qed.
Lemma lem1712494 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712495 (x : real) : (term247 x) = (term248 x).
Proof. exact (MK_COMB (@lem1712494) (@lem1712493 x)). Qed.
Lemma lem1712496 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712497 (x : real) : (term246 x) = (term249 x).
Proof. exact (MK_COMB (@lem1712495 x) (@lem1712496)). Qed.
Lemma lem1712498 (x : real) : (term245 x) = (term249 x).
Proof. exact (TRANS (@lem1712480 x) (@lem1712497 x)). Qed.
Lemma lem1712499 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1712500 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712507 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712508 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1712509 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1712508) (@lem1712507 x)). Qed.
Lemma lem1712510 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1712509 x) (@lem1712500)). Qed.
Lemma lem1712511 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1712513 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712514 : term197 = term75.
Proof. exact (@lem1712513 term183). Qed.
Lemma lem1712515 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1712516 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1712515 x) (@lem1712514)). Qed.
Lemma lem1712517 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1712518 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1712516 x) (@lem1712517 x)). Qed.
Lemma lem1712519 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1712511 x) (@lem1712518 x)). Qed.
Lemma lem1712520 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1712510 x) (@lem1712519 x)). Qed.
Lemma lem1712521 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712522 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1712521) (@lem1712520 x)). Qed.
Lemma lem1712523 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712524 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1712522 x) (@lem1712523)). Qed.
Lemma lem1712525 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1712499 x) (@lem1712524 x)). Qed.
Lemma lem1712526 : term115 = term354.
Proof. exact (@lem1483554 term24 term114). Qed.
Lemma lem1712530 : term114 = term197.
Proof. exact (@lem1483512 term75). Qed.
Lemma lem1712532 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712533 : term197 = term75.
Proof. exact (@lem1712532 term183). Qed.
Lemma lem1712535 : term114 = term75.
Proof. exact (TRANS (@lem1712530) (@lem1712533)). Qed.
Lemma lem1712538 : term251 = term251.
Proof. exact (eq_refl term251). Qed.
Lemma lem1712539 : term355 = term356.
Proof. exact (MK_COMB (@lem1712538) (@lem1712535)). Qed.
Lemma lem1712540 : term356 = term357.
Proof. exact (@lem1483519 term24 term75). Qed.
Lemma lem1712542 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712543 : term197 = term75.
Proof. exact (@lem1712542 term183). Qed.
Lemma lem1712544 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1712545 : term357 = term358.
Proof. exact (MK_COMB (@lem1712544) (@lem1712543)). Qed.
Lemma lem1712546 : term358 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1712547 : term357 = term24.
Proof. exact (TRANS (@lem1712545) (@lem1712546)). Qed.
Lemma lem1712548 : term356 = term24.
Proof. exact (TRANS (@lem1712540) (@lem1712547)). Qed.
Lemma lem1712549 : term355 = term24.
Proof. exact (TRANS (@lem1712539) (@lem1712548)). Qed.
Lemma lem1712550 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712551 : term359 = term60.
Proof. exact (MK_COMB (@lem1712550) (@lem1712549)). Qed.
Lemma lem1712552 : term60 = term255.
Proof. exact (@lem1483512 term24). Qed.
Lemma lem1712554 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712555 : term255 = term256.
Proof. exact (@lem1712554 term183 term183). Qed.
Lemma lem1712556 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712557 : term185 = term183.
Proof. exact (EQ_MP (@lem1712556) (@lem940073)). Qed.
Lemma lem1712558 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712559 : term182 = term24.
Proof. exact (MK_COMB (@lem1712558) (@lem1712557)). Qed.
Lemma lem1712560 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712561 : term256 = term60.
Proof. exact (MK_COMB (@lem1712560) (@lem1712559)). Qed.
Lemma lem1712562 : term255 = term60.
Proof. exact (TRANS (@lem1712555) (@lem1712561)). Qed.
Lemma lem1712563 : term60 = term60.
Proof. exact (TRANS (@lem1712552) (@lem1712562)). Qed.
Lemma lem1712564 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem1712565 : (term359 = term60) = (term359 = term60).
Proof. exact (MK_COMB (@lem1712564) (@lem1712563)). Qed.
Lemma lem1712566 : term359 = term60.
Proof. exact (EQ_MP (@lem1712565) (@lem1712551)). Qed.
Lemma lem1712567 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712568 : term361 = term312.
Proof. exact (MK_COMB (@lem1712567) (@lem1712566)). Qed.
Lemma lem1712569 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712570 : term362 = term314.
Proof. exact (MK_COMB (@lem1712568) (@lem1712569)). Qed.
Lemma lem1712571 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712572 : term363 = term316.
Proof. exact (MK_COMB (@lem1712571) (@lem1712549)). Qed.
Lemma lem1712573 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712574 : term364 = term318.
Proof. exact (MK_COMB (@lem1712572) (@lem1712573)). Qed.
Lemma lem1712575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712576 : term365 = term320.
Proof. exact (MK_COMB (@lem1712575) (@lem1712574)). Qed.
Lemma lem1712577 : term354 = term321.
Proof. exact (MK_COMB (@lem1712576) (@lem1712570)). Qed.
Lemma lem1712578 : term115 = term321.
Proof. exact (TRANS (@lem1712526) (@lem1712577)). Qed.
Lemma lem1712579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712580 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1712579) (@lem1712525 x)). Qed.
Lemma lem1712581 (x : real) : (term116 x) = (term366 x).
Proof. exact (MK_COMB (@lem1712580 x) (@lem1712578)). Qed.
Lemma lem1712582 (x : real) : (term98 x) = (term271 x).
Proof. exact (@lem1483531 term75 (real_neg x)). Qed.
Lemma lem1712589 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712592 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1712593 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1712592) (@lem1712589 x)). Qed.
Lemma lem1712594 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1712595 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1712597 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712598 : term181 = term182.
Proof. exact (@lem1712597 term183 term183). Qed.
Lemma lem1712599 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712600 : term185 = term183.
Proof. exact (EQ_MP (@lem1712599) (@lem940073)). Qed.
Lemma lem1712601 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712602 : term182 = term24.
Proof. exact (MK_COMB (@lem1712601) (@lem1712600)). Qed.
Lemma lem1712603 : term181 = term24.
Proof. exact (TRANS (@lem1712598) (@lem1712602)). Qed.
Lemma lem1712604 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1712605 : term186 = term187.
Proof. exact (MK_COMB (@lem1712604) (@lem1712603)). Qed.
Lemma lem1712606 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1712607 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1712605) (@lem1712606 x)). Qed.
Lemma lem1712608 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1712595 x) (@lem1712607 x)). Qed.
Lemma lem1712609 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1712610 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1712608 x) (@lem1712609 x)). Qed.
Lemma lem1712611 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712612 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1712611) (@lem1712610 x)). Qed.
Lemma lem1712613 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1712614 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1712612 x) (@lem1712613 x)). Qed.
Lemma lem1712615 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1712594 x) (@lem1712614 x)). Qed.
Lemma lem1712616 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1712593 x) (@lem1712615 x)). Qed.
Lemma lem1712617 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712618 (x : real) : (term272 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1712617) (@lem1712616 x)). Qed.
Lemma lem1712619 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712620 (x : real) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem1712618 x) (@lem1712619)). Qed.
Lemma lem1712621 (x : real) : (term98 x) = (term273 x).
Proof. exact (TRANS (@lem1712582 x) (@lem1712620 x)). Qed.
Lemma lem1712622 : term118 = term367.
Proof. exact (@lem1483554 term60 term114). Qed.
Lemma lem1712626 : term114 = term197.
Proof. exact (@lem1483512 term75). Qed.
Lemma lem1712628 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712629 : term197 = term75.
Proof. exact (@lem1712628 term183). Qed.
Lemma lem1712631 : term114 = term75.
Proof. exact (TRANS (@lem1712626) (@lem1712629)). Qed.
Lemma lem1712634 : term275 = term275.
Proof. exact (eq_refl term275). Qed.
Lemma lem1712635 : term368 = term369.
Proof. exact (MK_COMB (@lem1712634) (@lem1712631)). Qed.
Lemma lem1712636 : term369 = term370.
Proof. exact (@lem1483519 term60 term75). Qed.
Lemma lem1712638 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712639 : term197 = term75.
Proof. exact (@lem1712638 term183). Qed.
Lemma lem1712640 : term279 = term279.
Proof. exact (eq_refl term279). Qed.
Lemma lem1712641 : term370 = term371.
Proof. exact (MK_COMB (@lem1712640) (@lem1712639)). Qed.
Lemma lem1712642 : term371 = term60.
Proof. exact (@lem1483450 term60). Qed.
Lemma lem1712643 : term370 = term60.
Proof. exact (TRANS (@lem1712641) (@lem1712642)). Qed.
Lemma lem1712644 : term369 = term60.
Proof. exact (TRANS (@lem1712636) (@lem1712643)). Qed.
Lemma lem1712645 : term368 = term60.
Proof. exact (TRANS (@lem1712635) (@lem1712644)). Qed.
Lemma lem1712646 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712647 : term372 = term138.
Proof. exact (MK_COMB (@lem1712646) (@lem1712645)). Qed.
Lemma lem1712648 : term138 = term181.
Proof. exact (@lem1483512 term60). Qed.
Lemma lem1712650 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712651 : term181 = term182.
Proof. exact (@lem1712650 term183 term183). Qed.
Lemma lem1712652 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712653 : term185 = term183.
Proof. exact (EQ_MP (@lem1712652) (@lem940073)). Qed.
Lemma lem1712654 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712655 : term182 = term24.
Proof. exact (MK_COMB (@lem1712654) (@lem1712653)). Qed.
Lemma lem1712656 : term181 = term24.
Proof. exact (TRANS (@lem1712651) (@lem1712655)). Qed.
Lemma lem1712657 : term138 = term24.
Proof. exact (TRANS (@lem1712648) (@lem1712656)). Qed.
Lemma lem1712658 : term373 = term373.
Proof. exact (eq_refl term373). Qed.
Lemma lem1712659 : (term372 = term138) = (term372 = term24).
Proof. exact (MK_COMB (@lem1712658) (@lem1712657)). Qed.
Lemma lem1712660 : term372 = term24.
Proof. exact (EQ_MP (@lem1712659) (@lem1712647)). Qed.
Lemma lem1712661 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712662 : term374 = term316.
Proof. exact (MK_COMB (@lem1712661) (@lem1712660)). Qed.
Lemma lem1712663 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712664 : term375 = term318.
Proof. exact (MK_COMB (@lem1712662) (@lem1712663)). Qed.
Lemma lem1712665 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712666 : term376 = term312.
Proof. exact (MK_COMB (@lem1712665) (@lem1712645)). Qed.
Lemma lem1712667 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712668 : term377 = term314.
Proof. exact (MK_COMB (@lem1712666) (@lem1712667)). Qed.
Lemma lem1712669 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712670 : term378 = term338.
Proof. exact (MK_COMB (@lem1712669) (@lem1712668)). Qed.
Lemma lem1712671 : term367 = term339.
Proof. exact (MK_COMB (@lem1712670) (@lem1712664)). Qed.
Lemma lem1712672 : term118 = term339.
Proof. exact (TRANS (@lem1712622) (@lem1712671)). Qed.
Lemma lem1712673 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712674 (x : real) : (term54 x) = (term293 x).
Proof. exact (MK_COMB (@lem1712673) (@lem1712621 x)). Qed.
Lemma lem1712675 (x : real) : (term119 x) = (term340 x).
Proof. exact (MK_COMB (@lem1712674 x) (@lem1712672)). Qed.
Lemma lem1712676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712677 (x : real) : (term117 x) = (term379 x).
Proof. exact (MK_COMB (@lem1712676) (@lem1712581 x)). Qed.
Lemma lem1712678 (x : real) : (term120 x) = (term380 x).
Proof. exact (MK_COMB (@lem1712677 x) (@lem1712675 x)). Qed.
Lemma lem1712679 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712680 (x : real) : (term89 x) = (term297 x).
Proof. exact (MK_COMB (@lem1712679) (@lem1712498 x)). Qed.
Lemma lem1712681 (x : real) : (term121 x) = (term381 x).
Proof. exact (MK_COMB (@lem1712680 x) (@lem1712678 x)). Qed.
Lemma lem1712682 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712683 (x : real) : (term101 x) = (term299 x).
Proof. exact (MK_COMB (@lem1712682) (@lem1712479 x)). Qed.
Lemma lem1712684 (x : real) : (term122 x) = (term382 x).
Proof. exact (MK_COMB (@lem1712683 x) (@lem1712681 x)). Qed.
Lemma lem1712685 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712686 (x : real) : (term123 x) = (term243 x).
Proof. exact (MK_COMB (@lem1712685) (@lem1712368 x)). Qed.
Lemma lem1712687 (x : real) : (term125 x) = (term383 x).
Proof. exact (MK_COMB (@lem1712686 x) (@lem1712684 x)). Qed.
Lemma lem1712688 (x : real) : (term302 x) = (term303 x).
Proof. exact (@lem1483531 (real_neg x) term75). Qed.
Lemma lem1712689 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712696 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712697 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1712698 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1712697) (@lem1712696 x)). Qed.
Lemma lem1712699 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1712698 x) (@lem1712689)). Qed.
Lemma lem1712700 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1712702 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712703 : term197 = term75.
Proof. exact (@lem1712702 term183). Qed.
Lemma lem1712704 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1712705 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1712704 x) (@lem1712703)). Qed.
Lemma lem1712706 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1712707 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1712705 x) (@lem1712706 x)). Qed.
Lemma lem1712708 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1712700 x) (@lem1712707 x)). Qed.
Lemma lem1712709 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1712699 x) (@lem1712708 x)). Qed.
Lemma lem1712710 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712711 (x : real) : (term304 x) = (term248 x).
Proof. exact (MK_COMB (@lem1712710) (@lem1712709 x)). Qed.
Lemma lem1712712 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712713 (x : real) : (term303 x) = (term249 x).
Proof. exact (MK_COMB (@lem1712711 x) (@lem1712712)). Qed.
Lemma lem1712714 (x : real) : (term302 x) = (term249 x).
Proof. exact (TRANS (@lem1712688 x) (@lem1712713 x)). Qed.
Lemma lem1712715 (x : real) : (term41 x) = (term193 x).
Proof. exact (@lem1483521 x term75). Qed.
Lemma lem1712721 (x : real) : (term194 x) = (term195 x).
Proof. exact (@lem1483519 x term75). Qed.
Lemma lem1712723 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712724 : term197 = term75.
Proof. exact (@lem1712723 term183). Qed.
Lemma lem1712725 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1712726 (x : real) : (term195 x) = (term198 x).
Proof. exact (MK_COMB (@lem1712725 x) (@lem1712724)). Qed.
Lemma lem1712727 (x : real) : (term198 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1712728 (x : real) : (term195 x) = x.
Proof. exact (TRANS (@lem1712726 x) (@lem1712727 x)). Qed.
Lemma lem1712730 (x : real) : (term194 x) = x.
Proof. exact (TRANS (@lem1712721 x) (@lem1712728 x)). Qed.
Lemma lem1712731 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712732 (x : real) : (term199 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1712731) (@lem1712730 x)). Qed.
Lemma lem1712733 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712734 (x : real) : (term193 x) = (term192 x).
Proof. exact (MK_COMB (@lem1712732 x) (@lem1712733)). Qed.
Lemma lem1712735 (x : real) : (term41 x) = (term192 x).
Proof. exact (TRANS (@lem1712715 x) (@lem1712734 x)). Qed.
Lemma lem1712736 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1712737 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712744 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712745 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1712746 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1712745) (@lem1712744 x)). Qed.
Lemma lem1712747 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1712746 x) (@lem1712737)). Qed.
Lemma lem1712748 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1712750 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712751 : term197 = term75.
Proof. exact (@lem1712750 term183). Qed.
Lemma lem1712752 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1712753 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1712752 x) (@lem1712751)). Qed.
Lemma lem1712754 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1712755 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1712753 x) (@lem1712754 x)). Qed.
Lemma lem1712756 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1712748 x) (@lem1712755 x)). Qed.
Lemma lem1712757 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1712747 x) (@lem1712756 x)). Qed.
Lemma lem1712758 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712759 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1712758) (@lem1712757 x)). Qed.
Lemma lem1712760 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712761 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1712759 x) (@lem1712760)). Qed.
Lemma lem1712762 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1712736 x) (@lem1712761 x)). Qed.
Lemma lem1712763 : term61 = term209.
Proof. exact (@lem1483554 term24 term60). Qed.
Lemma lem1712769 : term210 = term211.
Proof. exact (@lem1483519 term24 term60). Qed.
Lemma lem1712771 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712772 : term181 = term182.
Proof. exact (@lem1712771 term183 term183). Qed.
Lemma lem1712773 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712774 : term185 = term183.
Proof. exact (EQ_MP (@lem1712773) (@lem940073)). Qed.
Lemma lem1712775 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712776 : term182 = term24.
Proof. exact (MK_COMB (@lem1712775) (@lem1712774)). Qed.
Lemma lem1712777 : term181 = term24.
Proof. exact (TRANS (@lem1712772) (@lem1712776)). Qed.
Lemma lem1712778 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1712779 : term211 = term213.
Proof. exact (MK_COMB (@lem1712778) (@lem1712777)). Qed.
Lemma lem1712780 : term213 = term214.
Proof. exact (@lem1367770 term183 term183). Qed.
Lemma lem1712781 : term215 = term216.
Proof. exact (@lem706885). Qed.
Lemma lem1712782 : (term215 = term216) = (term217 = term218).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term216). Qed.
Lemma lem1712783 : term217 = term218.
Proof. exact (EQ_MP (@lem1712782) (@lem1712781)). Qed.
Lemma lem1712784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712785 : term214 = term219.
Proof. exact (MK_COMB (@lem1712784) (@lem1712783)). Qed.
Lemma lem1712786 : term213 = term219.
Proof. exact (TRANS (@lem1712780) (@lem1712785)). Qed.
Lemma lem1712787 : term211 = term219.
Proof. exact (TRANS (@lem1712779) (@lem1712786)). Qed.
Lemma lem1712789 : term210 = term219.
Proof. exact (TRANS (@lem1712769) (@lem1712787)). Qed.
Lemma lem1712790 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712791 : term220 = term221.
Proof. exact (MK_COMB (@lem1712790) (@lem1712789)). Qed.
Lemma lem1712792 : term221 = term222.
Proof. exact (@lem1483512 term219). Qed.
Lemma lem1712794 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712795 : term222 = term225.
Proof. exact (@lem1712794 term183 term218). Qed.
Lemma lem1712796 : term226 = term216.
Proof. exact (@lem996238 term216). Qed.
Lemma lem1712797 : (term226 = term216) = (term227 = term218).
Proof. exact (@lem1007663 (BIT1 0) term216 term216). Qed.
Lemma lem1712798 : term227 = term218.
Proof. exact (EQ_MP (@lem1712797) (@lem1712796)). Qed.
Lemma lem1712799 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712800 : term228 = term219.
Proof. exact (MK_COMB (@lem1712799) (@lem1712798)). Qed.
Lemma lem1712801 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712802 : term225 = term221.
Proof. exact (MK_COMB (@lem1712801) (@lem1712800)). Qed.
Lemma lem1712803 : term222 = term221.
Proof. exact (TRANS (@lem1712795) (@lem1712802)). Qed.
Lemma lem1712804 : term221 = term221.
Proof. exact (TRANS (@lem1712792) (@lem1712803)). Qed.
Lemma lem1712805 : term229 = term229.
Proof. exact (eq_refl term229). Qed.
Lemma lem1712806 : (term220 = term221) = (term220 = term221).
Proof. exact (MK_COMB (@lem1712805) (@lem1712804)). Qed.
Lemma lem1712807 : term220 = term221.
Proof. exact (EQ_MP (@lem1712806) (@lem1712791)). Qed.
Lemma lem1712808 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712809 : term230 = term231.
Proof. exact (MK_COMB (@lem1712808) (@lem1712807)). Qed.
Lemma lem1712810 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712811 : term232 = term233.
Proof. exact (MK_COMB (@lem1712809) (@lem1712810)). Qed.
Lemma lem1712812 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712813 : term234 = term235.
Proof. exact (MK_COMB (@lem1712812) (@lem1712789)). Qed.
Lemma lem1712814 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712815 : term236 = term237.
Proof. exact (MK_COMB (@lem1712813) (@lem1712814)). Qed.
Lemma lem1712816 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712817 : term238 = term239.
Proof. exact (MK_COMB (@lem1712816) (@lem1712815)). Qed.
Lemma lem1712818 : term209 = term240.
Proof. exact (MK_COMB (@lem1712817) (@lem1712811)). Qed.
Lemma lem1712819 : term61 = term240.
Proof. exact (TRANS (@lem1712763) (@lem1712818)). Qed.
Lemma lem1712820 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712821 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1712820) (@lem1712762 x)). Qed.
Lemma lem1712822 (x : real) : (term62 x) = (term242 x).
Proof. exact (MK_COMB (@lem1712821 x) (@lem1712819)). Qed.
Lemma lem1712823 (x : real) : (term98 x) = (term271 x).
Proof. exact (@lem1483531 term75 (real_neg x)). Qed.
Lemma lem1712830 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712833 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1712834 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1712833) (@lem1712830 x)). Qed.
Lemma lem1712835 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1712836 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1712838 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712839 : term181 = term182.
Proof. exact (@lem1712838 term183 term183). Qed.
Lemma lem1712840 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712841 : term185 = term183.
Proof. exact (EQ_MP (@lem1712840) (@lem940073)). Qed.
Lemma lem1712842 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712843 : term182 = term24.
Proof. exact (MK_COMB (@lem1712842) (@lem1712841)). Qed.
Lemma lem1712844 : term181 = term24.
Proof. exact (TRANS (@lem1712839) (@lem1712843)). Qed.
Lemma lem1712845 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1712846 : term186 = term187.
Proof. exact (MK_COMB (@lem1712845) (@lem1712844)). Qed.
Lemma lem1712847 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1712848 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1712846) (@lem1712847 x)). Qed.
Lemma lem1712849 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1712836 x) (@lem1712848 x)). Qed.
Lemma lem1712850 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1712851 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1712849 x) (@lem1712850 x)). Qed.
Lemma lem1712852 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712853 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1712852) (@lem1712851 x)). Qed.
Lemma lem1712854 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1712855 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1712853 x) (@lem1712854 x)). Qed.
Lemma lem1712856 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1712835 x) (@lem1712855 x)). Qed.
Lemma lem1712857 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1712834 x) (@lem1712856 x)). Qed.
Lemma lem1712858 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712859 (x : real) : (term272 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1712858) (@lem1712857 x)). Qed.
Lemma lem1712860 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712861 (x : real) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem1712859 x) (@lem1712860)). Qed.
Lemma lem1712862 (x : real) : (term98 x) = (term273 x).
Proof. exact (TRANS (@lem1712823 x) (@lem1712861 x)). Qed.
Lemma lem1712863 : term78 = term305.
Proof. exact (@lem1483554 term75 term60). Qed.
Lemma lem1712869 : term306 = term307.
Proof. exact (@lem1483519 term75 term60). Qed.
Lemma lem1712871 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1712872 : term181 = term182.
Proof. exact (@lem1712871 term183 term183). Qed.
Lemma lem1712873 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712874 : term185 = term183.
Proof. exact (EQ_MP (@lem1712873) (@lem940073)). Qed.
Lemma lem1712875 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712876 : term182 = term24.
Proof. exact (MK_COMB (@lem1712875) (@lem1712874)). Qed.
Lemma lem1712877 : term181 = term24.
Proof. exact (TRANS (@lem1712872) (@lem1712876)). Qed.
Lemma lem1712878 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1712879 : term307 = term308.
Proof. exact (MK_COMB (@lem1712878) (@lem1712877)). Qed.
Lemma lem1712880 : term308 = term24.
Proof. exact (@lem1483448 term24). Qed.
Lemma lem1712881 : term307 = term24.
Proof. exact (TRANS (@lem1712879) (@lem1712880)). Qed.
Lemma lem1712883 : term306 = term24.
Proof. exact (TRANS (@lem1712869) (@lem1712881)). Qed.
Lemma lem1712884 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712885 : term309 = term60.
Proof. exact (MK_COMB (@lem1712884) (@lem1712883)). Qed.
Lemma lem1712886 : term60 = term255.
Proof. exact (@lem1483512 term24). Qed.
Lemma lem1712888 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712889 : term255 = term256.
Proof. exact (@lem1712888 term183 term183). Qed.
Lemma lem1712890 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712891 : term185 = term183.
Proof. exact (EQ_MP (@lem1712890) (@lem940073)). Qed.
Lemma lem1712892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1712893 : term182 = term24.
Proof. exact (MK_COMB (@lem1712892) (@lem1712891)). Qed.
Lemma lem1712894 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712895 : term256 = term60.
Proof. exact (MK_COMB (@lem1712894) (@lem1712893)). Qed.
Lemma lem1712896 : term255 = term60.
Proof. exact (TRANS (@lem1712889) (@lem1712895)). Qed.
Lemma lem1712897 : term60 = term60.
Proof. exact (TRANS (@lem1712886) (@lem1712896)). Qed.
Lemma lem1712898 : term310 = term310.
Proof. exact (eq_refl term310). Qed.
Lemma lem1712899 : (term309 = term60) = (term309 = term60).
Proof. exact (MK_COMB (@lem1712898) (@lem1712897)). Qed.
Lemma lem1712900 : term309 = term60.
Proof. exact (EQ_MP (@lem1712899) (@lem1712885)). Qed.
Lemma lem1712901 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712902 : term311 = term312.
Proof. exact (MK_COMB (@lem1712901) (@lem1712900)). Qed.
Lemma lem1712903 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712904 : term313 = term314.
Proof. exact (MK_COMB (@lem1712902) (@lem1712903)). Qed.
Lemma lem1712905 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712906 : term315 = term316.
Proof. exact (MK_COMB (@lem1712905) (@lem1712883)). Qed.
Lemma lem1712907 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712908 : term317 = term318.
Proof. exact (MK_COMB (@lem1712906) (@lem1712907)). Qed.
Lemma lem1712909 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712910 : term319 = term320.
Proof. exact (MK_COMB (@lem1712909) (@lem1712908)). Qed.
Lemma lem1712911 : term305 = term321.
Proof. exact (MK_COMB (@lem1712910) (@lem1712904)). Qed.
Lemma lem1712912 : term78 = term321.
Proof. exact (TRANS (@lem1712863) (@lem1712911)). Qed.
Lemma lem1712913 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712914 (x : real) : (term54 x) = (term293 x).
Proof. exact (MK_COMB (@lem1712913) (@lem1712862 x)). Qed.
Lemma lem1712915 (x : real) : (term79 x) = (term322 x).
Proof. exact (MK_COMB (@lem1712914 x) (@lem1712912)). Qed.
Lemma lem1712916 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1712917 (x : real) : (term63 x) = (term323 x).
Proof. exact (MK_COMB (@lem1712916) (@lem1712822 x)). Qed.
Lemma lem1712918 (x : real) : (term80 x) = (term324 x).
Proof. exact (MK_COMB (@lem1712917 x) (@lem1712915 x)). Qed.
Lemma lem1712919 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1712920 (x : real) : (term81 x) = (term243 x).
Proof. exact (MK_COMB (@lem1712919) (@lem1712735 x)). Qed.
Lemma lem1712921 (x : real) : (term83 x) = (term325 x).
Proof. exact (MK_COMB (@lem1712920 x) (@lem1712918 x)). Qed.
Lemma lem1712922 (x : real) : (term245 x) = (term246 x).
Proof. exact (@lem1483531 term75 x). Qed.
Lemma lem1712928 (x : real) : (term166 x) = (term167 x).
Proof. exact (@lem1483519 term75 x). Qed.
Lemma lem1712933 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1483448 (term168 x)). Qed.
Lemma lem1712935 (x : real) : (term166 x) = (term168 x).
Proof. exact (TRANS (@lem1712928 x) (@lem1712933 x)). Qed.
Lemma lem1712936 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1712937 (x : real) : (term247 x) = (term248 x).
Proof. exact (MK_COMB (@lem1712936) (@lem1712935 x)). Qed.
Lemma lem1712938 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712939 (x : real) : (term246 x) = (term249 x).
Proof. exact (MK_COMB (@lem1712937 x) (@lem1712938)). Qed.
Lemma lem1712940 (x : real) : (term245 x) = (term249 x).
Proof. exact (TRANS (@lem1712922 x) (@lem1712939 x)). Qed.
Lemma lem1712941 (x : real) : (term22 x) = (term200 x).
Proof. exact (@lem1483521 (real_neg x) term75). Qed.
Lemma lem1712942 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712949 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1712950 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1712951 (x : real) : (term201 x) = (term202 x).
Proof. exact (MK_COMB (@lem1712950) (@lem1712949 x)). Qed.
Lemma lem1712952 (x : real) : (term203 x) = (term204 x).
Proof. exact (MK_COMB (@lem1712951 x) (@lem1712942)). Qed.
Lemma lem1712953 (x : real) : (term204 x) = (term205 x).
Proof. exact (@lem1483519 (term168 x) term75). Qed.
Lemma lem1712955 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712956 : term197 = term75.
Proof. exact (@lem1712955 term183). Qed.
Lemma lem1712957 (x : real) : (term206 x) = (term206 x).
Proof. exact (eq_refl (term206 x)). Qed.
Lemma lem1712958 (x : real) : (term205 x) = (term207 x).
Proof. exact (MK_COMB (@lem1712957 x) (@lem1712956)). Qed.
Lemma lem1712959 (x : real) : (term207 x) = (term168 x).
Proof. exact (@lem1483450 (term168 x)). Qed.
Lemma lem1712960 (x : real) : (term205 x) = (term168 x).
Proof. exact (TRANS (@lem1712958 x) (@lem1712959 x)). Qed.
Lemma lem1712961 (x : real) : (term204 x) = (term168 x).
Proof. exact (TRANS (@lem1712953 x) (@lem1712960 x)). Qed.
Lemma lem1712962 (x : real) : (term203 x) = (term168 x).
Proof. exact (TRANS (@lem1712952 x) (@lem1712961 x)). Qed.
Lemma lem1712963 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1712964 (x : real) : (term208 x) = (term170 x).
Proof. exact (MK_COMB (@lem1712963) (@lem1712962 x)). Qed.
Lemma lem1712965 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1712966 (x : real) : (term200 x) = (term171 x).
Proof. exact (MK_COMB (@lem1712964 x) (@lem1712965)). Qed.
Lemma lem1712967 (x : real) : (term22 x) = (term171 x).
Proof. exact (TRANS (@lem1712941 x) (@lem1712966 x)). Qed.
Lemma lem1712968 : term115 = term354.
Proof. exact (@lem1483554 term24 term114). Qed.
Lemma lem1712972 : term114 = term197.
Proof. exact (@lem1483512 term75). Qed.
Lemma lem1712974 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712975 : term197 = term75.
Proof. exact (@lem1712974 term183). Qed.
Lemma lem1712977 : term114 = term75.
Proof. exact (TRANS (@lem1712972) (@lem1712975)). Qed.
Lemma lem1712980 : term251 = term251.
Proof. exact (eq_refl term251). Qed.
Lemma lem1712981 : term355 = term356.
Proof. exact (MK_COMB (@lem1712980) (@lem1712977)). Qed.
Lemma lem1712982 : term356 = term357.
Proof. exact (@lem1483519 term24 term75). Qed.
Lemma lem1712984 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1712985 : term197 = term75.
Proof. exact (@lem1712984 term183). Qed.
Lemma lem1712986 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem1712987 : term357 = term358.
Proof. exact (MK_COMB (@lem1712986) (@lem1712985)). Qed.
Lemma lem1712988 : term358 = term24.
Proof. exact (@lem1483450 term24). Qed.
Lemma lem1712989 : term357 = term24.
Proof. exact (TRANS (@lem1712987) (@lem1712988)). Qed.
Lemma lem1712990 : term356 = term24.
Proof. exact (TRANS (@lem1712982) (@lem1712989)). Qed.
Lemma lem1712991 : term355 = term24.
Proof. exact (TRANS (@lem1712981) (@lem1712990)). Qed.
Lemma lem1712992 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1712993 : term359 = term60.
Proof. exact (MK_COMB (@lem1712992) (@lem1712991)). Qed.
Lemma lem1712994 : term60 = term255.
Proof. exact (@lem1483512 term24). Qed.
Lemma lem1712996 (m : nat) (n : nat) : (term223 m n) = (term224 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem1712997 : term255 = term256.
Proof. exact (@lem1712996 term183 term183). Qed.
Lemma lem1712998 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1712999 : term185 = term183.
Proof. exact (EQ_MP (@lem1712998) (@lem940073)). Qed.
Lemma lem1713000 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1713001 : term182 = term24.
Proof. exact (MK_COMB (@lem1713000) (@lem1712999)). Qed.
Lemma lem1713002 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1713003 : term256 = term60.
Proof. exact (MK_COMB (@lem1713002) (@lem1713001)). Qed.
Lemma lem1713004 : term255 = term60.
Proof. exact (TRANS (@lem1712997) (@lem1713003)). Qed.
Lemma lem1713005 : term60 = term60.
Proof. exact (TRANS (@lem1712994) (@lem1713004)). Qed.
Lemma lem1713006 : term360 = term360.
Proof. exact (eq_refl term360). Qed.
Lemma lem1713007 : (term359 = term60) = (term359 = term60).
Proof. exact (MK_COMB (@lem1713006) (@lem1713005)). Qed.
Lemma lem1713008 : term359 = term60.
Proof. exact (EQ_MP (@lem1713007) (@lem1712993)). Qed.
Lemma lem1713009 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1713010 : term361 = term312.
Proof. exact (MK_COMB (@lem1713009) (@lem1713008)). Qed.
Lemma lem1713011 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1713012 : term362 = term314.
Proof. exact (MK_COMB (@lem1713010) (@lem1713011)). Qed.
Lemma lem1713013 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1713014 : term363 = term316.
Proof. exact (MK_COMB (@lem1713013) (@lem1712991)). Qed.
Lemma lem1713015 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1713016 : term364 = term318.
Proof. exact (MK_COMB (@lem1713014) (@lem1713015)). Qed.
Lemma lem1713017 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713018 : term365 = term320.
Proof. exact (MK_COMB (@lem1713017) (@lem1713016)). Qed.
Lemma lem1713019 : term354 = term321.
Proof. exact (MK_COMB (@lem1713018) (@lem1713012)). Qed.
Lemma lem1713020 : term115 = term321.
Proof. exact (TRANS (@lem1712968) (@lem1713019)). Qed.
Lemma lem1713021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1713022 (x : real) : (term48 x) = (term241 x).
Proof. exact (MK_COMB (@lem1713021) (@lem1712967 x)). Qed.
Lemma lem1713023 (x : real) : (term116 x) = (term366 x).
Proof. exact (MK_COMB (@lem1713022 x) (@lem1713020)). Qed.
Lemma lem1713024 (x : real) : (term98 x) = (term271 x).
Proof. exact (@lem1483531 term75 (real_neg x)). Qed.
Lemma lem1713031 (x : real) : (real_neg x) = (term168 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1713034 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1713035 (x : real) : (term174 x) = (term175 x).
Proof. exact (MK_COMB (@lem1713034) (@lem1713031 x)). Qed.
Lemma lem1713036 (x : real) : (term175 x) = (term176 x).
Proof. exact (@lem1483519 term75 (term168 x)). Qed.
Lemma lem1713037 (x : real) : (term177 x) = (term178 x).
Proof. exact (@lem1483476 term60 term60 x). Qed.
Lemma lem1713039 (m : nat) (n : nat) : (term179 m n) = (term180 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1713040 : term181 = term182.
Proof. exact (@lem1713039 term183 term183). Qed.
Lemma lem1713041 : (term184 = (BIT1 0)) = (term185 = term183).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1713042 : term185 = term183.
Proof. exact (EQ_MP (@lem1713041) (@lem940073)). Qed.
Lemma lem1713043 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1713044 : term182 = term24.
Proof. exact (MK_COMB (@lem1713043) (@lem1713042)). Qed.
Lemma lem1713045 : term181 = term24.
Proof. exact (TRANS (@lem1713040) (@lem1713044)). Qed.
Lemma lem1713046 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1713047 : term186 = term187.
Proof. exact (MK_COMB (@lem1713046) (@lem1713045)). Qed.
Lemma lem1713048 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1713049 (x : real) : (term178 x) = (term188 x).
Proof. exact (MK_COMB (@lem1713047) (@lem1713048 x)). Qed.
Lemma lem1713050 (x : real) : (term177 x) = (term188 x).
Proof. exact (TRANS (@lem1713037 x) (@lem1713049 x)). Qed.
Lemma lem1713051 (x : real) : (term188 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1713052 (x : real) : (term177 x) = x.
Proof. exact (TRANS (@lem1713050 x) (@lem1713051 x)). Qed.
Lemma lem1713053 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1713054 (x : real) : (term176 x) = (term190 x).
Proof. exact (MK_COMB (@lem1713053) (@lem1713052 x)). Qed.
Lemma lem1713055 (x : real) : (term190 x) = x.
Proof. exact (@lem1483448 x). Qed.
Lemma lem1713056 (x : real) : (term176 x) = x.
Proof. exact (TRANS (@lem1713054 x) (@lem1713055 x)). Qed.
Lemma lem1713057 (x : real) : (term175 x) = x.
Proof. exact (TRANS (@lem1713036 x) (@lem1713056 x)). Qed.
Lemma lem1713058 (x : real) : (term174 x) = x.
Proof. exact (TRANS (@lem1713035 x) (@lem1713057 x)). Qed.
Lemma lem1713059 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1713060 (x : real) : (term272 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1713059) (@lem1713058 x)). Qed.
Lemma lem1713061 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1713062 (x : real) : (term271 x) = (term273 x).
Proof. exact (MK_COMB (@lem1713060 x) (@lem1713061)). Qed.
Lemma lem1713063 (x : real) : (term98 x) = (term273 x).
Proof. exact (TRANS (@lem1713024 x) (@lem1713062 x)). Qed.
Lemma lem1713064 : term128 = term384.
Proof. exact (@lem1483554 term75 term114). Qed.
Lemma lem1713068 : term114 = term197.
Proof. exact (@lem1483512 term75). Qed.
Lemma lem1713070 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1713071 : term197 = term75.
Proof. exact (@lem1713070 term183). Qed.
Lemma lem1713073 : term114 = term75.
Proof. exact (TRANS (@lem1713068) (@lem1713071)). Qed.
Lemma lem1713076 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem1713077 : term385 = term386.
Proof. exact (MK_COMB (@lem1713076) (@lem1713073)). Qed.
Lemma lem1713078 : term386 = term387.
Proof. exact (@lem1483519 term75 term75). Qed.
Lemma lem1713080 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1713081 : term197 = term75.
Proof. exact (@lem1713080 term183). Qed.
Lemma lem1713082 : term189 = term189.
Proof. exact (eq_refl term189). Qed.
Lemma lem1713083 : term387 = term388.
Proof. exact (MK_COMB (@lem1713082) (@lem1713081)). Qed.
Lemma lem1713084 : term388 = term75.
Proof. exact (@lem1483448 term75). Qed.
Lemma lem1713085 : term387 = term75.
Proof. exact (TRANS (@lem1713083) (@lem1713084)). Qed.
Lemma lem1713086 : term386 = term75.
Proof. exact (TRANS (@lem1713078) (@lem1713085)). Qed.
Lemma lem1713087 : term385 = term75.
Proof. exact (TRANS (@lem1713077) (@lem1713086)). Qed.
Lemma lem1713088 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1713089 : term389 = term114.
Proof. exact (MK_COMB (@lem1713088) (@lem1713087)). Qed.
Lemma lem1713090 : term114 = term197.
Proof. exact (@lem1483512 term75). Qed.
Lemma lem1713092 (x : nat) : (term196 x) = term75.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1713093 : term197 = term75.
Proof. exact (@lem1713092 term183). Qed.
Lemma lem1713094 : term114 = term75.
Proof. exact (TRANS (@lem1713090) (@lem1713093)). Qed.
Lemma lem1713095 : term390 = term390.
Proof. exact (eq_refl term390). Qed.
Lemma lem1713096 : (term389 = term114) = (term389 = term75).
Proof. exact (MK_COMB (@lem1713095) (@lem1713094)). Qed.
Lemma lem1713097 : term389 = term75.
Proof. exact (EQ_MP (@lem1713096) (@lem1713089)). Qed.
Lemma lem1713098 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1713099 : term391 = term262.
Proof. exact (MK_COMB (@lem1713098) (@lem1713097)). Qed.
Lemma lem1713100 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1713101 : term392 = term264.
Proof. exact (MK_COMB (@lem1713099) (@lem1713100)). Qed.
Lemma lem1713102 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1713103 : term393 = term262.
Proof. exact (MK_COMB (@lem1713102) (@lem1713087)). Qed.
Lemma lem1713104 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1713105 : term394 = term264.
Proof. exact (MK_COMB (@lem1713103) (@lem1713104)). Qed.
Lemma lem1713106 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713107 : term395 = term268.
Proof. exact (MK_COMB (@lem1713106) (@lem1713105)). Qed.
Lemma lem1713108 : term384 = term269.
Proof. exact (MK_COMB (@lem1713107) (@lem1713101)). Qed.
Lemma lem1713109 : term128 = term269.
Proof. exact (TRANS (@lem1713064) (@lem1713108)). Qed.
Lemma lem1713110 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1713111 (x : real) : (term54 x) = (term293 x).
Proof. exact (MK_COMB (@lem1713110) (@lem1713063 x)). Qed.
Lemma lem1713112 (x : real) : (term129 x) = (term396 x).
Proof. exact (MK_COMB (@lem1713111 x) (@lem1713109)). Qed.
Lemma lem1713113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713114 (x : real) : (term117 x) = (term379 x).
Proof. exact (MK_COMB (@lem1713113) (@lem1713023 x)). Qed.
Lemma lem1713115 (x : real) : (term130 x) = (term397 x).
Proof. exact (MK_COMB (@lem1713114 x) (@lem1713112 x)). Qed.
Lemma lem1713116 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1713117 (x : real) : (term89 x) = (term297 x).
Proof. exact (MK_COMB (@lem1713116) (@lem1712940 x)). Qed.
Lemma lem1713118 (x : real) : (term131 x) = (term398 x).
Proof. exact (MK_COMB (@lem1713117 x) (@lem1713115 x)). Qed.
Lemma lem1713119 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713120 (x : real) : (term85 x) = (term343 x).
Proof. exact (MK_COMB (@lem1713119) (@lem1712921 x)). Qed.
Lemma lem1713121 (x : real) : (term132 x) = (term399 x).
Proof. exact (MK_COMB (@lem1713120 x) (@lem1713118 x)). Qed.
Lemma lem1713122 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1713123 (x : real) : (term133 x) = (term297 x).
Proof. exact (MK_COMB (@lem1713122) (@lem1712714 x)). Qed.
Lemma lem1713124 (x : real) : (term135 x) = (term400 x).
Proof. exact (MK_COMB (@lem1713123 x) (@lem1713121 x)). Qed.
Lemma lem1713125 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713126 (x : real) : (term127 x) = (term401 x).
Proof. exact (MK_COMB (@lem1713125) (@lem1712687 x)). Qed.
Lemma lem1713127 (x : real) : (term136 x) = (term402 x).
Proof. exact (MK_COMB (@lem1713126 x) (@lem1713124 x)). Qed.
Lemma lem1713128 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1713129 (x : real) : (term403 x) = (term293 x).
Proof. exact (MK_COMB (@lem1713128) (@lem1712328 x)). Qed.
Lemma lem1713130 (x : real) : (term404 x) = (term405 x).
Proof. exact (MK_COMB (@lem1713129 x) (@lem1713127 x)). Qed.
Lemma lem1713131 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713132 (x : real) : (term406 x) = (term407 x).
Proof. exact (MK_COMB (@lem1713131) (@lem1712307 x)). Qed.
Lemma lem1713133 (x : real) : (term159 x) = (term408 x).
Proof. exact (MK_COMB (@lem1713132 x) (@lem1713130 x)). Qed.
Lemma lem1713134 : term163 = term409.
Proof. exact (fun_ext (fun x : real => @lem1713133 x)). Qed.
Lemma lem1713135 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1713136 : term164 = term410.
Proof. exact (MK_COMB (@lem1713135) (@lem1713134)). Qed.
Lemma lem1713137 : term14 = term410.
Proof. exact (TRANS (@lem1711434) (@lem1713136)). Qed.
Lemma lem1713139 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term411 A P Q) = (term412 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1713140 (P : real -> Prop) (Q : real -> Prop) : (term413 P Q) = (term414 P Q).
Proof. exact (@lem1713139 real P Q). Qed.
Lemma lem1713141 : term415 = term416.
Proof. exact (@lem1713140 term417 term418). Qed.
Lemma lem1713142 (x : real) : (term419 x) = (term350 x).
Proof. exact (eq_refl (term419 x)). Qed.
Lemma lem1713143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713144 (x : real) : (term420 x) = (term407 x).
Proof. exact (MK_COMB (@lem1713143) (@lem1713142 x)). Qed.
Lemma lem1713145 (x : real) : (term421 x) = (term405 x).
Proof. exact (eq_refl (term421 x)). Qed.
Lemma lem1713146 (x : real) : (term422 x) = (term408 x).
Proof. exact (MK_COMB (@lem1713144 x) (@lem1713145 x)). Qed.
Lemma lem1713147 : term423 = term409.
Proof. exact (fun_ext (fun x : real => @lem1713146 x)). Qed.
Lemma lem1713148 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1713149 : term415 = term410.
Proof. exact (MK_COMB (@lem1713148) (@lem1713147)). Qed.
Lemma lem1713150 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1713151 : term424 = term425.
Proof. exact (MK_COMB (@lem1713150) (@lem1713149)). Qed.
Lemma lem1713152 (x : real) : (term419 x) = (term350 x).
Proof. exact (eq_refl (term419 x)). Qed.
Lemma lem1713153 : term426 = term417.
Proof. exact (fun_ext (fun x : real => @lem1713152 x)). Qed.
Lemma lem1713154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1713155 : term427 = term428.
Proof. exact (MK_COMB (@lem1713154) (@lem1713153)). Qed.
Lemma lem1713156 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713157 : term429 = term430.
Proof. exact (MK_COMB (@lem1713156) (@lem1713155)). Qed.
Lemma lem1713158 (x : real) : (term421 x) = (term405 x).
Proof. exact (eq_refl (term421 x)). Qed.
Lemma lem1713159 : term431 = term418.
Proof. exact (fun_ext (fun x : real => @lem1713158 x)). Qed.
Lemma lem1713160 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1713161 : term432 = term433.
Proof. exact (MK_COMB (@lem1713160) (@lem1713159)). Qed.
Lemma lem1713162 : term416 = term434.
Proof. exact (MK_COMB (@lem1713157) (@lem1713161)). Qed.
Lemma lem1713163 : (term415 = term416) = (term410 = term434).
Proof. exact (MK_COMB (@lem1713151) (@lem1713162)). Qed.
Lemma lem1713164 : term410 = term434.
Proof. exact (EQ_MP (@lem1713163) (@lem1713141)). Qed.
Lemma lem1713262 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term412 A P Q) = (term411 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1713263 (P : real -> Prop) (Q : real -> Prop) : (term414 P Q) = (term413 P Q).
Proof. exact (@lem1713262 real P Q). Qed.
Lemma lem1713264 : term416 = term415.
Proof. exact (@lem1713263 term417 term418). Qed.
Lemma lem1713265 (x : real) : (term419 x) = (term350 x).
Proof. exact (eq_refl (term419 x)). Qed.
Lemma lem1713266 : term426 = term417.
Proof. exact (fun_ext (fun x : real => @lem1713265 x)). Qed.
Lemma lem1713267 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1713268 : term427 = term428.
Proof. exact (MK_COMB (@lem1713267) (@lem1713266)). Qed.
Lemma lem1713269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713270 : term429 = term430.
Proof. exact (MK_COMB (@lem1713269) (@lem1713268)). Qed.
Lemma lem1713271 (x : real) : (term421 x) = (term405 x).
Proof. exact (eq_refl (term421 x)). Qed.
Lemma lem1713272 : term431 = term418.
Proof. exact (fun_ext (fun x : real => @lem1713271 x)). Qed.
Lemma lem1713273 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1713274 : term432 = term433.
Proof. exact (MK_COMB (@lem1713273) (@lem1713272)). Qed.
Lemma lem1713275 : term416 = term434.
Proof. exact (MK_COMB (@lem1713270) (@lem1713274)). Qed.
Lemma lem1713276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1713277 : term435 = term436.
Proof. exact (MK_COMB (@lem1713276) (@lem1713275)). Qed.
Lemma lem1713278 (x : real) : (term419 x) = (term350 x).
Proof. exact (eq_refl (term419 x)). Qed.
Lemma lem1713279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713280 (x : real) : (term420 x) = (term407 x).
Proof. exact (MK_COMB (@lem1713279) (@lem1713278 x)). Qed.
Lemma lem1713281 (x : real) : (term421 x) = (term405 x).
Proof. exact (eq_refl (term421 x)). Qed.
Lemma lem1713282 (x : real) : (term422 x) = (term408 x).
Proof. exact (MK_COMB (@lem1713280 x) (@lem1713281 x)). Qed.
Lemma lem1713283 : term423 = term409.
Proof. exact (fun_ext (fun x : real => @lem1713282 x)). Qed.
Lemma lem1713284 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1713285 : term415 = term410.
Proof. exact (MK_COMB (@lem1713284) (@lem1713283)). Qed.
Lemma lem1713286 : (term416 = term415) = (term434 = term410).
Proof. exact (MK_COMB (@lem1713277) (@lem1713285)). Qed.
Lemma lem1713287 : term434 = term410.
Proof. exact (EQ_MP (@lem1713286) (@lem1713264)). Qed.
Lemma lem1713288 : term410 = term410.
Proof. exact (TRANS (@lem1713164) (@lem1713287)). Qed.
Lemma lem1713291 : term14 = term410.
Proof. exact (TRANS (@lem1713137) (@lem1713288)). Qed.
Lemma lem1713308 (x : real) : (term396 x) = (term437 x).
Proof. exact (@lem19158 term264 (term273 x) term264). Qed.
Lemma lem1713325 (x : real) : (term366 x) = (term438 x).
Proof. exact (@lem19158 term318 (term171 x) term314). Qed.
Lemma lem1713326 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713327 (x : real) : (term379 x) = (term439 x).
Proof. exact (MK_COMB (@lem1713326) (@lem1713325 x)). Qed.
Lemma lem1713328 (x : real) : (term397 x) = (term440 x).
Proof. exact (MK_COMB (@lem1713327 x) (@lem1713308 x)). Qed.
Lemma lem1713331 (x : real) : (term297 x) = (term297 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1713332 (x : real) : (term398 x) = (term441 x).
Proof. exact (MK_COMB (@lem1713331 x) (@lem1713328 x)). Qed.
Lemma lem1713333 (x : real) : (term441 x) = (term442 x).
Proof. exact (@lem19158 (term438 x) (term249 x) (term437 x)). Qed.
Lemma lem1713340 (x : real) : (term443 x) = (term444 x).
Proof. exact (@lem19158 (term445 x) (term249 x) (term445 x)). Qed.
Lemma lem1713347 (x : real) : (term446 x) = (term447 x).
Proof. exact (@lem19158 (term448 x) (term249 x) (term449 x)). Qed.
Lemma lem1713348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713349 (x : real) : (term450 x) = (term451 x).
Proof. exact (MK_COMB (@lem1713348) (@lem1713347 x)). Qed.
Lemma lem1713350 (x : real) : (term442 x) = (term452 x).
Proof. exact (MK_COMB (@lem1713349 x) (@lem1713340 x)). Qed.
Lemma lem1713351 (x : real) : (term441 x) = (term452 x).
Proof. exact (TRANS (@lem1713333 x) (@lem1713350 x)). Qed.
Lemma lem1713352 (x : real) : (term398 x) = (term452 x).
Proof. exact (TRANS (@lem1713332 x) (@lem1713351 x)). Qed.
Lemma lem1713369 (x : real) : (term322 x) = (term453 x).
Proof. exact (@lem19158 term318 (term273 x) term314). Qed.
Lemma lem1713386 (x : real) : (term242 x) = (term454 x).
Proof. exact (@lem19158 term237 (term171 x) term233). Qed.
Lemma lem1713387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713388 (x : real) : (term323 x) = (term455 x).
Proof. exact (MK_COMB (@lem1713387) (@lem1713386 x)). Qed.
Lemma lem1713389 (x : real) : (term324 x) = (term456 x).
Proof. exact (MK_COMB (@lem1713388 x) (@lem1713369 x)). Qed.
Lemma lem1713392 (x : real) : (term243 x) = (term243 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1713393 (x : real) : (term325 x) = (term457 x).
Proof. exact (MK_COMB (@lem1713392 x) (@lem1713389 x)). Qed.
Lemma lem1713394 (x : real) : (term457 x) = (term458 x).
Proof. exact (@lem19158 (term454 x) (term192 x) (term453 x)). Qed.
Lemma lem1713401 (x : real) : (term459 x) = (term460 x).
Proof. exact (@lem19158 (term461 x) (term192 x) (term462 x)). Qed.
Lemma lem1713408 (x : real) : (term463 x) = (term464 x).
Proof. exact (@lem19158 (term465 x) (term192 x) (term466 x)). Qed.
Lemma lem1713409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713410 (x : real) : (term467 x) = (term468 x).
Proof. exact (MK_COMB (@lem1713409) (@lem1713408 x)). Qed.
Lemma lem1713411 (x : real) : (term458 x) = (term469 x).
Proof. exact (MK_COMB (@lem1713410 x) (@lem1713401 x)). Qed.
Lemma lem1713412 (x : real) : (term457 x) = (term469 x).
Proof. exact (TRANS (@lem1713394 x) (@lem1713411 x)). Qed.
Lemma lem1713413 (x : real) : (term325 x) = (term469 x).
Proof. exact (TRANS (@lem1713393 x) (@lem1713412 x)). Qed.
Lemma lem1713414 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713415 (x : real) : (term343 x) = (term470 x).
Proof. exact (MK_COMB (@lem1713414) (@lem1713413 x)). Qed.
Lemma lem1713416 (x : real) : (term399 x) = (term471 x).
Proof. exact (MK_COMB (@lem1713415 x) (@lem1713352 x)). Qed.
Lemma lem1713419 (x : real) : (term297 x) = (term297 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1713420 (x : real) : (term400 x) = (term472 x).
Proof. exact (MK_COMB (@lem1713419 x) (@lem1713416 x)). Qed.
Lemma lem1713421 (x : real) : (term472 x) = (term473 x).
Proof. exact (@lem19158 (term469 x) (term249 x) (term452 x)). Qed.
Lemma lem1713422 (x : real) : (term474 x) = (term475 x).
Proof. exact (@lem19158 (term447 x) (term249 x) (term444 x)). Qed.
Lemma lem1713429 (x : real) : (term476 x) = (term477 x).
Proof. exact (@lem19158 (term478 x) (term249 x) (term478 x)). Qed.
Lemma lem1713436 (x : real) : (term479 x) = (term480 x).
Proof. exact (@lem19158 (term481 x) (term249 x) (term482 x)). Qed.
Lemma lem1713437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713438 (x : real) : (term483 x) = (term484 x).
Proof. exact (MK_COMB (@lem1713437) (@lem1713436 x)). Qed.
Lemma lem1713439 (x : real) : (term475 x) = (term485 x).
Proof. exact (MK_COMB (@lem1713438 x) (@lem1713429 x)). Qed.
Lemma lem1713440 (x : real) : (term474 x) = (term485 x).
Proof. exact (TRANS (@lem1713422 x) (@lem1713439 x)). Qed.
Lemma lem1713441 (x : real) : (term486 x) = (term487 x).
Proof. exact (@lem19158 (term464 x) (term249 x) (term460 x)). Qed.
Lemma lem1713448 (x : real) : (term488 x) = (term489 x).
Proof. exact (@lem19158 (term490 x) (term249 x) (term491 x)). Qed.
Lemma lem1713455 (x : real) : (term492 x) = (term493 x).
Proof. exact (@lem19158 (term494 x) (term249 x) (term495 x)). Qed.
Lemma lem1713456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713457 (x : real) : (term496 x) = (term497 x).
Proof. exact (MK_COMB (@lem1713456) (@lem1713455 x)). Qed.
Lemma lem1713458 (x : real) : (term487 x) = (term498 x).
Proof. exact (MK_COMB (@lem1713457 x) (@lem1713448 x)). Qed.
Lemma lem1713459 (x : real) : (term486 x) = (term498 x).
Proof. exact (TRANS (@lem1713441 x) (@lem1713458 x)). Qed.
Lemma lem1713460 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713461 (x : real) : (term499 x) = (term500 x).
Proof. exact (MK_COMB (@lem1713460) (@lem1713459 x)). Qed.
Lemma lem1713462 (x : real) : (term473 x) = (term501 x).
Proof. exact (MK_COMB (@lem1713461 x) (@lem1713440 x)). Qed.
Lemma lem1713463 (x : real) : (term472 x) = (term501 x).
Proof. exact (TRANS (@lem1713421 x) (@lem1713462 x)). Qed.
Lemma lem1713464 (x : real) : (term400 x) = (term501 x).
Proof. exact (TRANS (@lem1713420 x) (@lem1713463 x)). Qed.
Lemma lem1713481 (x : real) : (term340 x) = (term502 x).
Proof. exact (@lem19158 term314 (term273 x) term318). Qed.
Lemma lem1713498 (x : real) : (term366 x) = (term438 x).
Proof. exact (@lem19158 term318 (term171 x) term314). Qed.
Lemma lem1713499 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713500 (x : real) : (term379 x) = (term439 x).
Proof. exact (MK_COMB (@lem1713499) (@lem1713498 x)). Qed.
Lemma lem1713501 (x : real) : (term380 x) = (term503 x).
Proof. exact (MK_COMB (@lem1713500 x) (@lem1713481 x)). Qed.
Lemma lem1713504 (x : real) : (term297 x) = (term297 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1713505 (x : real) : (term381 x) = (term504 x).
Proof. exact (MK_COMB (@lem1713504 x) (@lem1713501 x)). Qed.
Lemma lem1713506 (x : real) : (term504 x) = (term505 x).
Proof. exact (@lem19158 (term438 x) (term249 x) (term502 x)). Qed.
Lemma lem1713513 (x : real) : (term506 x) = (term507 x).
Proof. exact (@lem19158 (term462 x) (term249 x) (term461 x)). Qed.
Lemma lem1713520 (x : real) : (term446 x) = (term447 x).
Proof. exact (@lem19158 (term448 x) (term249 x) (term449 x)). Qed.
Lemma lem1713521 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713522 (x : real) : (term450 x) = (term451 x).
Proof. exact (MK_COMB (@lem1713521) (@lem1713520 x)). Qed.
Lemma lem1713523 (x : real) : (term505 x) = (term508 x).
Proof. exact (MK_COMB (@lem1713522 x) (@lem1713513 x)). Qed.
Lemma lem1713524 (x : real) : (term504 x) = (term508 x).
Proof. exact (TRANS (@lem1713506 x) (@lem1713523 x)). Qed.
Lemma lem1713525 (x : real) : (term381 x) = (term508 x).
Proof. exact (TRANS (@lem1713505 x) (@lem1713524 x)). Qed.
Lemma lem1713542 (x : real) : (term242 x) = (term454 x).
Proof. exact (@lem19158 term237 (term171 x) term233). Qed.
Lemma lem1713545 (x : real) : (term243 x) = (term243 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1713546 (x : real) : (term244 x) = (term463 x).
Proof. exact (MK_COMB (@lem1713545 x) (@lem1713542 x)). Qed.
Lemma lem1713553 (x : real) : (term463 x) = (term464 x).
Proof. exact (@lem19158 (term465 x) (term192 x) (term466 x)). Qed.
Lemma lem1713554 (x : real) : (term244 x) = (term464 x).
Proof. exact (TRANS (@lem1713546 x) (@lem1713553 x)). Qed.
Lemma lem1713555 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713556 (x : real) : (term299 x) = (term468 x).
Proof. exact (MK_COMB (@lem1713555) (@lem1713554 x)). Qed.
Lemma lem1713557 (x : real) : (term382 x) = (term509 x).
Proof. exact (MK_COMB (@lem1713556 x) (@lem1713525 x)). Qed.
Lemma lem1713560 (x : real) : (term243 x) = (term243 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1713561 (x : real) : (term383 x) = (term510 x).
Proof. exact (MK_COMB (@lem1713560 x) (@lem1713557 x)). Qed.
Lemma lem1713562 (x : real) : (term510 x) = (term511 x).
Proof. exact (@lem19158 (term464 x) (term192 x) (term508 x)). Qed.
Lemma lem1713563 (x : real) : (term512 x) = (term513 x).
Proof. exact (@lem19158 (term447 x) (term192 x) (term507 x)). Qed.
Lemma lem1713570 (x : real) : (term514 x) = (term515 x).
Proof. exact (@lem19158 (term516 x) (term192 x) (term517 x)). Qed.
Lemma lem1713577 (x : real) : (term518 x) = (term519 x).
Proof. exact (@lem19158 (term481 x) (term192 x) (term482 x)). Qed.
Lemma lem1713578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713579 (x : real) : (term520 x) = (term521 x).
Proof. exact (MK_COMB (@lem1713578) (@lem1713577 x)). Qed.
Lemma lem1713580 (x : real) : (term513 x) = (term522 x).
Proof. exact (MK_COMB (@lem1713579 x) (@lem1713570 x)). Qed.
Lemma lem1713581 (x : real) : (term512 x) = (term522 x).
Proof. exact (TRANS (@lem1713563 x) (@lem1713580 x)). Qed.
Lemma lem1713588 (x : real) : (term523 x) = (term524 x).
Proof. exact (@lem19158 (term494 x) (term192 x) (term495 x)). Qed.
Lemma lem1713589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713590 (x : real) : (term525 x) = (term526 x).
Proof. exact (MK_COMB (@lem1713589) (@lem1713588 x)). Qed.
Lemma lem1713591 (x : real) : (term511 x) = (term527 x).
Proof. exact (MK_COMB (@lem1713590 x) (@lem1713581 x)). Qed.
Lemma lem1713592 (x : real) : (term510 x) = (term527 x).
Proof. exact (TRANS (@lem1713562 x) (@lem1713591 x)). Qed.
Lemma lem1713593 (x : real) : (term383 x) = (term527 x).
Proof. exact (TRANS (@lem1713561 x) (@lem1713592 x)). Qed.
Lemma lem1713594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713595 (x : real) : (term401 x) = (term528 x).
Proof. exact (MK_COMB (@lem1713594) (@lem1713593 x)). Qed.
Lemma lem1713596 (x : real) : (term402 x) = (term529 x).
Proof. exact (MK_COMB (@lem1713595 x) (@lem1713464 x)). Qed.
Lemma lem1713599 (x : real) : (term293 x) = (term293 x).
Proof. exact (eq_refl (term293 x)). Qed.
Lemma lem1713600 (x : real) : (term405 x) = (term530 x).
Proof. exact (MK_COMB (@lem1713599 x) (@lem1713596 x)). Qed.
Lemma lem1713601 (x : real) : (term530 x) = (term531 x).
Proof. exact (@lem19158 (term527 x) (term273 x) (term501 x)). Qed.
Lemma lem1713602 (x : real) : (term532 x) = (term533 x).
Proof. exact (@lem19158 (term498 x) (term273 x) (term485 x)). Qed.
Lemma lem1713603 (x : real) : (term534 x) = (term535 x).
Proof. exact (@lem19158 (term480 x) (term273 x) (term477 x)). Qed.
Lemma lem1713610 (x : real) : (term536 x) = (term537 x).
Proof. exact (@lem19158 (term538 x) (term273 x) (term538 x)). Qed.
Lemma lem1713617 (x : real) : (term539 x) = (term540 x).
Proof. exact (@lem19158 (term541 x) (term273 x) (term542 x)). Qed.
Lemma lem1713618 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713619 (x : real) : (term543 x) = (term544 x).
Proof. exact (MK_COMB (@lem1713618) (@lem1713617 x)). Qed.
Lemma lem1713620 (x : real) : (term535 x) = (term545 x).
Proof. exact (MK_COMB (@lem1713619 x) (@lem1713610 x)). Qed.
Lemma lem1713621 (x : real) : (term534 x) = (term545 x).
Proof. exact (TRANS (@lem1713603 x) (@lem1713620 x)). Qed.
Lemma lem1713622 (x : real) : (term546 x) = (term547 x).
Proof. exact (@lem19158 (term493 x) (term273 x) (term489 x)). Qed.
Lemma lem1713629 (x : real) : (term548 x) = (term549 x).
Proof. exact (@lem19158 (term550 x) (term273 x) (term551 x)). Qed.
Lemma lem1713636 (x : real) : (term552 x) = (term553 x).
Proof. exact (@lem19158 (term554 x) (term273 x) (term555 x)). Qed.
Lemma lem1713637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713638 (x : real) : (term556 x) = (term557 x).
Proof. exact (MK_COMB (@lem1713637) (@lem1713636 x)). Qed.
Lemma lem1713639 (x : real) : (term547 x) = (term558 x).
Proof. exact (MK_COMB (@lem1713638 x) (@lem1713629 x)). Qed.
Lemma lem1713640 (x : real) : (term546 x) = (term558 x).
Proof. exact (TRANS (@lem1713622 x) (@lem1713639 x)). Qed.
Lemma lem1713641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713642 (x : real) : (term559 x) = (term560 x).
Proof. exact (MK_COMB (@lem1713641) (@lem1713640 x)). Qed.
Lemma lem1713643 (x : real) : (term533 x) = (term561 x).
Proof. exact (MK_COMB (@lem1713642 x) (@lem1713621 x)). Qed.
Lemma lem1713644 (x : real) : (term532 x) = (term561 x).
Proof. exact (TRANS (@lem1713602 x) (@lem1713643 x)). Qed.
Lemma lem1713645 (x : real) : (term562 x) = (term563 x).
Proof. exact (@lem19158 (term524 x) (term273 x) (term522 x)). Qed.
Lemma lem1713646 (x : real) : (term564 x) = (term565 x).
Proof. exact (@lem19158 (term519 x) (term273 x) (term515 x)). Qed.
Lemma lem1713653 (x : real) : (term566 x) = (term567 x).
Proof. exact (@lem19158 (term568 x) (term273 x) (term569 x)). Qed.
Lemma lem1713660 (x : real) : (term570 x) = (term571 x).
Proof. exact (@lem19158 (term572 x) (term273 x) (term573 x)). Qed.
Lemma lem1713661 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713662 (x : real) : (term574 x) = (term575 x).
Proof. exact (MK_COMB (@lem1713661) (@lem1713660 x)). Qed.
Lemma lem1713663 (x : real) : (term565 x) = (term576 x).
Proof. exact (MK_COMB (@lem1713662 x) (@lem1713653 x)). Qed.
Lemma lem1713664 (x : real) : (term564 x) = (term576 x).
Proof. exact (TRANS (@lem1713646 x) (@lem1713663 x)). Qed.
Lemma lem1713671 (x : real) : (term577 x) = (term578 x).
Proof. exact (@lem19158 (term579 x) (term273 x) (term580 x)). Qed.
Lemma lem1713672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713673 (x : real) : (term581 x) = (term582 x).
Proof. exact (MK_COMB (@lem1713672) (@lem1713671 x)). Qed.
Lemma lem1713674 (x : real) : (term563 x) = (term583 x).
Proof. exact (MK_COMB (@lem1713673 x) (@lem1713664 x)). Qed.
Lemma lem1713675 (x : real) : (term562 x) = (term583 x).
Proof. exact (TRANS (@lem1713645 x) (@lem1713674 x)). Qed.
Lemma lem1713676 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713677 (x : real) : (term584 x) = (term585 x).
Proof. exact (MK_COMB (@lem1713676) (@lem1713675 x)). Qed.
Lemma lem1713678 (x : real) : (term531 x) = (term586 x).
Proof. exact (MK_COMB (@lem1713677 x) (@lem1713644 x)). Qed.
Lemma lem1713679 (x : real) : (term530 x) = (term586 x).
Proof. exact (TRANS (@lem1713601 x) (@lem1713678 x)). Qed.
Lemma lem1713680 (x : real) : (term405 x) = (term586 x).
Proof. exact (TRANS (@lem1713600 x) (@lem1713679 x)). Qed.
Lemma lem1713697 (x : real) : (term340 x) = (term502 x).
Proof. exact (@lem19158 term314 (term273 x) term318). Qed.
Lemma lem1713714 (x : real) : (term270 x) = (term587 x).
Proof. exact (@lem19158 term264 (term171 x) term264). Qed.
Lemma lem1713715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713716 (x : real) : (term295 x) = (term588 x).
Proof. exact (MK_COMB (@lem1713715) (@lem1713714 x)). Qed.
Lemma lem1713717 (x : real) : (term341 x) = (term589 x).
Proof. exact (MK_COMB (@lem1713716 x) (@lem1713697 x)). Qed.
Lemma lem1713720 (x : real) : (term297 x) = (term297 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1713721 (x : real) : (term342 x) = (term590 x).
Proof. exact (MK_COMB (@lem1713720 x) (@lem1713717 x)). Qed.
Lemma lem1713722 (x : real) : (term590 x) = (term591 x).
Proof. exact (@lem19158 (term587 x) (term249 x) (term502 x)). Qed.
Lemma lem1713729 (x : real) : (term506 x) = (term507 x).
Proof. exact (@lem19158 (term462 x) (term249 x) (term461 x)). Qed.
Lemma lem1713736 (x : real) : (term592 x) = (term593 x).
Proof. exact (@lem19158 (term594 x) (term249 x) (term594 x)). Qed.
Lemma lem1713737 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713738 (x : real) : (term595 x) = (term596 x).
Proof. exact (MK_COMB (@lem1713737) (@lem1713736 x)). Qed.
Lemma lem1713739 (x : real) : (term591 x) = (term597 x).
Proof. exact (MK_COMB (@lem1713738 x) (@lem1713729 x)). Qed.
Lemma lem1713740 (x : real) : (term590 x) = (term597 x).
Proof. exact (TRANS (@lem1713722 x) (@lem1713739 x)). Qed.
Lemma lem1713741 (x : real) : (term342 x) = (term597 x).
Proof. exact (TRANS (@lem1713721 x) (@lem1713740 x)). Qed.
Lemma lem1713758 (x : real) : (term322 x) = (term453 x).
Proof. exact (@lem19158 term318 (term273 x) term314). Qed.
Lemma lem1713775 (x : real) : (term242 x) = (term454 x).
Proof. exact (@lem19158 term237 (term171 x) term233). Qed.
Lemma lem1713776 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713777 (x : real) : (term323 x) = (term455 x).
Proof. exact (MK_COMB (@lem1713776) (@lem1713775 x)). Qed.
Lemma lem1713778 (x : real) : (term324 x) = (term456 x).
Proof. exact (MK_COMB (@lem1713777 x) (@lem1713758 x)). Qed.
Lemma lem1713781 (x : real) : (term243 x) = (term243 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1713782 (x : real) : (term325 x) = (term457 x).
Proof. exact (MK_COMB (@lem1713781 x) (@lem1713778 x)). Qed.
Lemma lem1713783 (x : real) : (term457 x) = (term458 x).
Proof. exact (@lem19158 (term454 x) (term192 x) (term453 x)). Qed.
Lemma lem1713790 (x : real) : (term459 x) = (term460 x).
Proof. exact (@lem19158 (term461 x) (term192 x) (term462 x)). Qed.
Lemma lem1713797 (x : real) : (term463 x) = (term464 x).
Proof. exact (@lem19158 (term465 x) (term192 x) (term466 x)). Qed.
Lemma lem1713798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713799 (x : real) : (term467 x) = (term468 x).
Proof. exact (MK_COMB (@lem1713798) (@lem1713797 x)). Qed.
Lemma lem1713800 (x : real) : (term458 x) = (term469 x).
Proof. exact (MK_COMB (@lem1713799 x) (@lem1713790 x)). Qed.
Lemma lem1713801 (x : real) : (term457 x) = (term469 x).
Proof. exact (TRANS (@lem1713783 x) (@lem1713800 x)). Qed.
Lemma lem1713802 (x : real) : (term325 x) = (term469 x).
Proof. exact (TRANS (@lem1713782 x) (@lem1713801 x)). Qed.
Lemma lem1713803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713804 (x : real) : (term343 x) = (term470 x).
Proof. exact (MK_COMB (@lem1713803) (@lem1713802 x)). Qed.
Lemma lem1713805 (x : real) : (term344 x) = (term598 x).
Proof. exact (MK_COMB (@lem1713804 x) (@lem1713741 x)). Qed.
Lemma lem1713808 (x : real) : (term297 x) = (term297 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1713809 (x : real) : (term345 x) = (term599 x).
Proof. exact (MK_COMB (@lem1713808 x) (@lem1713805 x)). Qed.
Lemma lem1713810 (x : real) : (term599 x) = (term600 x).
Proof. exact (@lem19158 (term469 x) (term249 x) (term597 x)). Qed.
Lemma lem1713811 (x : real) : (term601 x) = (term602 x).
Proof. exact (@lem19158 (term593 x) (term249 x) (term507 x)). Qed.
Lemma lem1713818 (x : real) : (term603 x) = (term604 x).
Proof. exact (@lem19158 (term516 x) (term249 x) (term517 x)). Qed.
Lemma lem1713825 (x : real) : (term605 x) = (term606 x).
Proof. exact (@lem19158 (term607 x) (term249 x) (term607 x)). Qed.
Lemma lem1713826 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713827 (x : real) : (term608 x) = (term609 x).
Proof. exact (MK_COMB (@lem1713826) (@lem1713825 x)). Qed.
Lemma lem1713828 (x : real) : (term602 x) = (term610 x).
Proof. exact (MK_COMB (@lem1713827 x) (@lem1713818 x)). Qed.
Lemma lem1713829 (x : real) : (term601 x) = (term610 x).
Proof. exact (TRANS (@lem1713811 x) (@lem1713828 x)). Qed.
Lemma lem1713830 (x : real) : (term486 x) = (term487 x).
Proof. exact (@lem19158 (term464 x) (term249 x) (term460 x)). Qed.
Lemma lem1713837 (x : real) : (term488 x) = (term489 x).
Proof. exact (@lem19158 (term490 x) (term249 x) (term491 x)). Qed.
Lemma lem1713844 (x : real) : (term492 x) = (term493 x).
Proof. exact (@lem19158 (term494 x) (term249 x) (term495 x)). Qed.
Lemma lem1713845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713846 (x : real) : (term496 x) = (term497 x).
Proof. exact (MK_COMB (@lem1713845) (@lem1713844 x)). Qed.
Lemma lem1713847 (x : real) : (term487 x) = (term498 x).
Proof. exact (MK_COMB (@lem1713846 x) (@lem1713837 x)). Qed.
Lemma lem1713848 (x : real) : (term486 x) = (term498 x).
Proof. exact (TRANS (@lem1713830 x) (@lem1713847 x)). Qed.
Lemma lem1713849 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713850 (x : real) : (term499 x) = (term500 x).
Proof. exact (MK_COMB (@lem1713849) (@lem1713848 x)). Qed.
Lemma lem1713851 (x : real) : (term600 x) = (term611 x).
Proof. exact (MK_COMB (@lem1713850 x) (@lem1713829 x)). Qed.
Lemma lem1713852 (x : real) : (term599 x) = (term611 x).
Proof. exact (TRANS (@lem1713810 x) (@lem1713851 x)). Qed.
Lemma lem1713853 (x : real) : (term345 x) = (term611 x).
Proof. exact (TRANS (@lem1713809 x) (@lem1713852 x)). Qed.
Lemma lem1713870 (x : real) : (term294 x) = (term612 x).
Proof. exact (@lem19158 term233 (term273 x) term237). Qed.
Lemma lem1713887 (x : real) : (term270 x) = (term587 x).
Proof. exact (@lem19158 term264 (term171 x) term264). Qed.
Lemma lem1713888 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713889 (x : real) : (term295 x) = (term588 x).
Proof. exact (MK_COMB (@lem1713888) (@lem1713887 x)). Qed.
Lemma lem1713890 (x : real) : (term296 x) = (term613 x).
Proof. exact (MK_COMB (@lem1713889 x) (@lem1713870 x)). Qed.
Lemma lem1713893 (x : real) : (term297 x) = (term297 x).
Proof. exact (eq_refl (term297 x)). Qed.
Lemma lem1713894 (x : real) : (term298 x) = (term614 x).
Proof. exact (MK_COMB (@lem1713893 x) (@lem1713890 x)). Qed.
Lemma lem1713895 (x : real) : (term614 x) = (term615 x).
Proof. exact (@lem19158 (term587 x) (term249 x) (term612 x)). Qed.
Lemma lem1713902 (x : real) : (term616 x) = (term617 x).
Proof. exact (@lem19158 (term618 x) (term249 x) (term619 x)). Qed.
Lemma lem1713909 (x : real) : (term592 x) = (term593 x).
Proof. exact (@lem19158 (term594 x) (term249 x) (term594 x)). Qed.
Lemma lem1713910 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713911 (x : real) : (term595 x) = (term596 x).
Proof. exact (MK_COMB (@lem1713910) (@lem1713909 x)). Qed.
Lemma lem1713912 (x : real) : (term615 x) = (term620 x).
Proof. exact (MK_COMB (@lem1713911 x) (@lem1713902 x)). Qed.
Lemma lem1713913 (x : real) : (term614 x) = (term620 x).
Proof. exact (TRANS (@lem1713895 x) (@lem1713912 x)). Qed.
Lemma lem1713914 (x : real) : (term298 x) = (term620 x).
Proof. exact (TRANS (@lem1713894 x) (@lem1713913 x)). Qed.
Lemma lem1713931 (x : real) : (term242 x) = (term454 x).
Proof. exact (@lem19158 term237 (term171 x) term233). Qed.
Lemma lem1713934 (x : real) : (term243 x) = (term243 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1713935 (x : real) : (term244 x) = (term463 x).
Proof. exact (MK_COMB (@lem1713934 x) (@lem1713931 x)). Qed.
Lemma lem1713942 (x : real) : (term463 x) = (term464 x).
Proof. exact (@lem19158 (term465 x) (term192 x) (term466 x)). Qed.
Lemma lem1713943 (x : real) : (term244 x) = (term464 x).
Proof. exact (TRANS (@lem1713935 x) (@lem1713942 x)). Qed.
Lemma lem1713944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713945 (x : real) : (term299 x) = (term468 x).
Proof. exact (MK_COMB (@lem1713944) (@lem1713943 x)). Qed.
Lemma lem1713946 (x : real) : (term300 x) = (term621 x).
Proof. exact (MK_COMB (@lem1713945 x) (@lem1713914 x)). Qed.
Lemma lem1713949 (x : real) : (term243 x) = (term243 x).
Proof. exact (eq_refl (term243 x)). Qed.
Lemma lem1713950 (x : real) : (term301 x) = (term622 x).
Proof. exact (MK_COMB (@lem1713949 x) (@lem1713946 x)). Qed.
Lemma lem1713951 (x : real) : (term622 x) = (term623 x).
Proof. exact (@lem19158 (term464 x) (term192 x) (term620 x)). Qed.
Lemma lem1713952 (x : real) : (term624 x) = (term625 x).
Proof. exact (@lem19158 (term593 x) (term192 x) (term617 x)). Qed.
Lemma lem1713959 (x : real) : (term626 x) = (term627 x).
Proof. exact (@lem19158 (term628 x) (term192 x) (term629 x)). Qed.
Lemma lem1713966 (x : real) : (term630 x) = (term631 x).
Proof. exact (@lem19158 (term607 x) (term192 x) (term607 x)). Qed.
Lemma lem1713967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713968 (x : real) : (term632 x) = (term633 x).
Proof. exact (MK_COMB (@lem1713967) (@lem1713966 x)). Qed.
Lemma lem1713969 (x : real) : (term625 x) = (term634 x).
Proof. exact (MK_COMB (@lem1713968 x) (@lem1713959 x)). Qed.
Lemma lem1713970 (x : real) : (term624 x) = (term634 x).
Proof. exact (TRANS (@lem1713952 x) (@lem1713969 x)). Qed.
Lemma lem1713977 (x : real) : (term523 x) = (term524 x).
Proof. exact (@lem19158 (term494 x) (term192 x) (term495 x)). Qed.
Lemma lem1713978 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713979 (x : real) : (term525 x) = (term526 x).
Proof. exact (MK_COMB (@lem1713978) (@lem1713977 x)). Qed.
Lemma lem1713980 (x : real) : (term623 x) = (term635 x).
Proof. exact (MK_COMB (@lem1713979 x) (@lem1713970 x)). Qed.
Lemma lem1713981 (x : real) : (term622 x) = (term635 x).
Proof. exact (TRANS (@lem1713951 x) (@lem1713980 x)). Qed.
Lemma lem1713982 (x : real) : (term301 x) = (term635 x).
Proof. exact (TRANS (@lem1713950 x) (@lem1713981 x)). Qed.
Lemma lem1713983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1713984 (x : real) : (term346 x) = (term636 x).
Proof. exact (MK_COMB (@lem1713983) (@lem1713982 x)). Qed.
Lemma lem1713985 (x : real) : (term347 x) = (term637 x).
Proof. exact (MK_COMB (@lem1713984 x) (@lem1713853 x)). Qed.
Lemma lem1713988 (x : real) : (term241 x) = (term241 x).
Proof. exact (eq_refl (term241 x)). Qed.
Lemma lem1713989 (x : real) : (term350 x) = (term638 x).
Proof. exact (MK_COMB (@lem1713988 x) (@lem1713985 x)). Qed.
Lemma lem1713990 (x : real) : (term638 x) = (term639 x).
Proof. exact (@lem19158 (term635 x) (term171 x) (term611 x)). Qed.
Lemma lem1713991 (x : real) : (term640 x) = (term641 x).
Proof. exact (@lem19158 (term498 x) (term171 x) (term610 x)). Qed.
Lemma lem1713992 (x : real) : (term642 x) = (term643 x).
Proof. exact (@lem19158 (term606 x) (term171 x) (term604 x)). Qed.
Lemma lem1713999 (x : real) : (term644 x) = (term645 x).
Proof. exact (@lem19158 (term646 x) (term171 x) (term647 x)). Qed.
Lemma lem1714006 (x : real) : (term648 x) = (term649 x).
Proof. exact (@lem19158 (term650 x) (term171 x) (term650 x)). Qed.
Lemma lem1714007 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1714008 (x : real) : (term651 x) = (term652 x).
Proof. exact (MK_COMB (@lem1714007) (@lem1714006 x)). Qed.
Lemma lem1714009 (x : real) : (term643 x) = (term653 x).
Proof. exact (MK_COMB (@lem1714008 x) (@lem1713999 x)). Qed.
Lemma lem1714010 (x : real) : (term642 x) = (term653 x).
Proof. exact (TRANS (@lem1713992 x) (@lem1714009 x)). Qed.
Lemma lem1714011 (x : real) : (term654 x) = (term655 x).
Proof. exact (@lem19158 (term493 x) (term171 x) (term489 x)). Qed.
Lemma lem1714018 (x : real) : (term656 x) = (term657 x).
Proof. exact (@lem19158 (term550 x) (term171 x) (term551 x)). Qed.
Lemma lem1714025 (x : real) : (term658 x) = (term659 x).
Proof. exact (@lem19158 (term554 x) (term171 x) (term555 x)). Qed.
Lemma lem1714026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1714027 (x : real) : (term660 x) = (term661 x).
Proof. exact (MK_COMB (@lem1714026) (@lem1714025 x)). Qed.
Lemma lem1714028 (x : real) : (term655 x) = (term662 x).
Proof. exact (MK_COMB (@lem1714027 x) (@lem1714018 x)). Qed.
Lemma lem1714029 (x : real) : (term654 x) = (term662 x).
Proof. exact (TRANS (@lem1714011 x) (@lem1714028 x)). Qed.
Lemma lem1714030 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1714031 (x : real) : (term663 x) = (term664 x).
Proof. exact (MK_COMB (@lem1714030) (@lem1714029 x)). Qed.
Lemma lem1714032 (x : real) : (term641 x) = (term665 x).
Proof. exact (MK_COMB (@lem1714031 x) (@lem1714010 x)). Qed.
Lemma lem1714033 (x : real) : (term640 x) = (term665 x).
Proof. exact (TRANS (@lem1713991 x) (@lem1714032 x)). Qed.
Lemma lem1714034 (x : real) : (term666 x) = (term667 x).
Proof. exact (@lem19158 (term524 x) (term171 x) (term634 x)). Qed.
Lemma lem1714035 (x : real) : (term668 x) = (term669 x).
Proof. exact (@lem19158 (term631 x) (term171 x) (term627 x)). Qed.
Lemma lem1714042 (x : real) : (term670 x) = (term671 x).
Proof. exact (@lem19158 (term672 x) (term171 x) (term673 x)). Qed.
Lemma lem1714049 (x : real) : (term674 x) = (term675 x).
Proof. exact (@lem19158 (term676 x) (term171 x) (term676 x)). Qed.
Lemma lem1714050 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1714051 (x : real) : (term677 x) = (term678 x).
Proof. exact (MK_COMB (@lem1714050) (@lem1714049 x)). Qed.
Lemma lem1714052 (x : real) : (term669 x) = (term679 x).
Proof. exact (MK_COMB (@lem1714051 x) (@lem1714042 x)). Qed.
Lemma lem1714053 (x : real) : (term668 x) = (term679 x).
Proof. exact (TRANS (@lem1714035 x) (@lem1714052 x)). Qed.
Lemma lem1714060 (x : real) : (term680 x) = (term681 x).
Proof. exact (@lem19158 (term579 x) (term171 x) (term580 x)). Qed.
Lemma lem1714061 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1714062 (x : real) : (term682 x) = (term683 x).
Proof. exact (MK_COMB (@lem1714061) (@lem1714060 x)). Qed.
Lemma lem1714063 (x : real) : (term667 x) = (term684 x).
Proof. exact (MK_COMB (@lem1714062 x) (@lem1714053 x)). Qed.
Lemma lem1714064 (x : real) : (term666 x) = (term684 x).
Proof. exact (TRANS (@lem1714034 x) (@lem1714063 x)). Qed.
Lemma lem1714065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1714066 (x : real) : (term685 x) = (term686 x).
Proof. exact (MK_COMB (@lem1714065) (@lem1714064 x)). Qed.
Lemma lem1714067 (x : real) : (term639 x) = (term687 x).
Proof. exact (MK_COMB (@lem1714066 x) (@lem1714033 x)). Qed.
Lemma lem1714068 (x : real) : (term638 x) = (term687 x).
Proof. exact (TRANS (@lem1713990 x) (@lem1714067 x)). Qed.
Lemma lem1714069 (x : real) : (term350 x) = (term687 x).
Proof. exact (TRANS (@lem1713989 x) (@lem1714068 x)). Qed.
Lemma lem1714070 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1714071 (x : real) : (term407 x) = (term688 x).
Proof. exact (MK_COMB (@lem1714070) (@lem1714069 x)). Qed.
Lemma lem1714072 (x : real) : (term408 x) = (term689 x).
Proof. exact (MK_COMB (@lem1714071 x) (@lem1713680 x)). Qed.
Lemma lem1714073 : term409 = term690.
Proof. exact (fun_ext (fun x : real => @lem1714072 x)). Qed.
Lemma lem1714074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1714075 : term410 = term691.
Proof. exact (MK_COMB (@lem1714074) (@lem1714073)). Qed.
Lemma lem1714076 : term14 = term691.
Proof. exact (TRANS (@lem1713291) (@lem1714075)). Qed.
Lemma lem1714242 (x : real) (h1 : term689 x) : term689 x.
Proof. exact (h1). Qed.
Lemma lem1714243 (x : real) (h1 : term687 x) : term687 x.
Proof. exact (h1). Qed.
Lemma lem1714244 (x : real) (h1 : term684 x) : term684 x.
Proof. exact (h1). Qed.
Lemma lem1714245 (x : real) (h1 : term681 x) : term681 x.
Proof. exact (h1). Qed.
Lemma lem1714246 (x : real) (h1 : term692 x) : term692 x.
Proof. exact (h1). Qed.
Lemma lem1714247 (x : real) (h1 : term692 x) : term579 x.
Proof. exact (proj2 (@lem1714246 x h1)). Qed.
Lemma lem1714249 (x : real) (h1 : term692 x) : term494 x.
Proof. exact (proj2 (@lem1714247 x h1)). Qed.
Lemma lem1714251 (x : real) (h1 : term692 x) : term465 x.
Proof. exact (proj2 (@lem1714249 x h1)). Qed.
Lemma lem1714252 (x : real) (h1 : term692 x) : term192 x.
Proof. exact (proj1 (@lem1714249 x h1)). Qed.
Lemma lem1714254 (x : real) (h1 : term692 x) : term171 x.
Proof. exact (proj1 (@lem1714251 x h1)). Qed.
Lemma lem1714256 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714257 : term318 = term694.
Proof. exact (@lem1714256 (NUMERAL 0) term183). Qed.
Lemma lem1714258 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714259 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714260 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714259 h1) (fun h1 : term694 = True => @lem1714258)). Qed.
Lemma lem1714261 : term694 = True.
Proof. exact (EQ_MP (@lem1714260) (@lem1714258)). Qed.
Lemma lem1714262 : term318 = True.
Proof. exact (TRANS (@lem1714257) (@lem1714261)). Qed.
Lemma lem1714263 : True = term318.
Proof. exact (SYM (@lem1714262)). Qed.
Lemma lem1714264 : term318.
Proof. exact (EQ_MP (@lem1714263) (@lem0)). Qed.
Lemma lem1714265 (x : real) (h1 : term692 x) : term696 x.
Proof. exact (conj (@lem1714264) (@lem1714252 x h1)). Qed.
Lemma lem1714267 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714268 (x : real) : term698 x.
Proof. exact (@lem1714267 term24 x). Qed.
Lemma lem1714269 (x : real) (h1 : term692 x) : term699 x.
Proof. exact (@lem1714268 x (@lem1714265 x h1)). Qed.
Lemma lem1714270 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1714271 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714272 (x : real) : (term700 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1714271) (@lem1714270 x)). Qed.
Lemma lem1714273 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714274 (x : real) : (term699 x) = (term192 x).
Proof. exact (MK_COMB (@lem1714272 x) (@lem1714273)). Qed.
Lemma lem1714275 (x : real) (h1 : term692 x) : term192 x.
Proof. exact (EQ_MP (@lem1714274 x) (@lem1714269 x h1)). Qed.
Lemma lem1714277 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714278 : term318 = term694.
Proof. exact (@lem1714277 (NUMERAL 0) term183). Qed.
Lemma lem1714279 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714280 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714281 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714280 h1) (fun h1 : term694 = True => @lem1714279)). Qed.
Lemma lem1714282 : term694 = True.
Proof. exact (EQ_MP (@lem1714281) (@lem1714279)). Qed.
Lemma lem1714283 : term318 = True.
Proof. exact (TRANS (@lem1714278) (@lem1714282)). Qed.
Lemma lem1714284 : True = term318.
Proof. exact (SYM (@lem1714283)). Qed.
Lemma lem1714285 : term318.
Proof. exact (EQ_MP (@lem1714284) (@lem0)). Qed.
Lemma lem1714286 (x : real) (h1 : term692 x) : term701 x.
Proof. exact (conj (@lem1714285) (@lem1714254 x h1)). Qed.
Lemma lem1714288 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714289 (x : real) : term702 x.
Proof. exact (@lem1714288 term24 (term168 x)). Qed.
Lemma lem1714290 (x : real) (h1 : term692 x) : term703 x.
Proof. exact (@lem1714289 x (@lem1714286 x h1)). Qed.
Lemma lem1714291 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1714292 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714293 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1714292) (@lem1714291 x)). Qed.
Lemma lem1714294 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714295 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1714293 x) (@lem1714294)). Qed.
Lemma lem1714296 (x : real) (h1 : term692 x) : term171 x.
Proof. exact (EQ_MP (@lem1714295 x) (@lem1714290 x h1)). Qed.
Lemma lem1714297 (x : real) (h1 : term692 x) : term706 x.
Proof. exact (conj (@lem1714296 x h1) (@lem1714275 x h1)). Qed.
Lemma lem1714299 (x : real) (y : real) : term707 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1714300 (x : real) : term708 x.
Proof. exact (@lem1714299 (term168 x) x). Qed.
Lemma lem1714301 (x : real) (h1 : term692 x) : term709 x.
Proof. exact (@lem1714300 x (@lem1714297 x h1)). Qed.
Lemma lem1714302 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1714304 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1714305 : term713 = term75.
Proof. exact (@lem1714304 term183). Qed.
Lemma lem1714306 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1714307 : term714 = term715.
Proof. exact (MK_COMB (@lem1714306) (@lem1714305)). Qed.
Lemma lem1714308 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1714309 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1714307) (@lem1714308 x)). Qed.
Lemma lem1714310 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1714302 x) (@lem1714309 x)). Qed.
Lemma lem1714311 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1714312 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1714310 x) (@lem1714311 x)). Qed.
Lemma lem1714313 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714314 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1714313) (@lem1714312 x)). Qed.
Lemma lem1714315 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714316 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1714314 x) (@lem1714315)). Qed.
Lemma lem1714317 (x : real) (h1 : term692 x) : term264.
Proof. exact (EQ_MP (@lem1714316 x) (@lem1714301 x h1)). Qed.
Lemma lem1714319 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714320 : term264 = term718.
Proof. exact (@lem1714319 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714321 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714322 : term264 = False.
Proof. exact (TRANS (@lem1714320) (@lem1714321)). Qed.
Lemma lem1714323 (x : real) (h1 : term692 x) : False.
Proof. exact (EQ_MP (@lem1714322) (@lem1714317 x h1)). Qed.
Lemma lem1714324 (x : real) (h1 : term719 x) : term719 x.
Proof. exact (h1). Qed.
Lemma lem1714325 (x : real) (h1 : term719 x) : term580 x.
Proof. exact (proj2 (@lem1714324 x h1)). Qed.
Lemma lem1714327 (x : real) (h1 : term719 x) : term495 x.
Proof. exact (proj2 (@lem1714325 x h1)). Qed.
Lemma lem1714329 (x : real) (h1 : term719 x) : term466 x.
Proof. exact (proj2 (@lem1714327 x h1)). Qed.
Lemma lem1714331 (x : real) (h1 : term719 x) : term233.
Proof. exact (proj2 (@lem1714329 x h1)). Qed.
Lemma lem1714334 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714335 : term233 = False.
Proof. exact (@lem1714334 term218 (NUMERAL 0)). Qed.
Lemma lem1714336 (x : real) (h1 : term719 x) : False.
Proof. exact (EQ_MP (@lem1714335) (@lem1714331 x h1)). Qed.
Lemma lem1714337 (x : real) (h1 : term681 x) : False.
Proof. exact (or_elim (@lem1714245 x h1) (fun h0 : term692 x => @lem1714323 x h0) (fun h0 : term719 x => @lem1714336 x h0)). Qed.
Lemma lem1714338 (x : real) (h1 : term679 x) : term679 x.
Proof. exact (h1). Qed.
Lemma lem1714339 (x : real) (h1 : term675 x) : term675 x.
Proof. exact (h1). Qed.
Lemma lem1714340 (x : real) (h1 : term721 x) : term721 x.
Proof. exact (h1). Qed.
Lemma lem1714341 (x : real) (h1 : term721 x) : term676 x.
Proof. exact (proj2 (@lem1714340 x h1)). Qed.
Lemma lem1714343 (x : real) (h1 : term721 x) : term607 x.
Proof. exact (proj2 (@lem1714341 x h1)). Qed.
Lemma lem1714345 (x : real) (h1 : term721 x) : term594 x.
Proof. exact (proj2 (@lem1714343 x h1)). Qed.
Lemma lem1714347 (x : real) (h1 : term721 x) : term264.
Proof. exact (proj2 (@lem1714345 x h1)). Qed.
Lemma lem1714350 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714351 : term264 = term718.
Proof. exact (@lem1714350 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714352 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714353 : term264 = False.
Proof. exact (TRANS (@lem1714351) (@lem1714352)). Qed.
Lemma lem1714354 (x : real) (h1 : term721 x) : False.
Proof. exact (EQ_MP (@lem1714353) (@lem1714347 x h1)). Qed.
Lemma lem1714355 (x : real) (h1 : term721 x) : term721 x.
Proof. exact (h1). Qed.
Lemma lem1714356 (x : real) (h1 : term721 x) : term676 x.
Proof. exact (proj2 (@lem1714355 x h1)). Qed.
Lemma lem1714358 (x : real) (h1 : term721 x) : term607 x.
Proof. exact (proj2 (@lem1714356 x h1)). Qed.
Lemma lem1714360 (x : real) (h1 : term721 x) : term594 x.
Proof. exact (proj2 (@lem1714358 x h1)). Qed.
Lemma lem1714362 (x : real) (h1 : term721 x) : term264.
Proof. exact (proj2 (@lem1714360 x h1)). Qed.
Lemma lem1714365 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714366 : term264 = term718.
Proof. exact (@lem1714365 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714367 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714368 : term264 = False.
Proof. exact (TRANS (@lem1714366) (@lem1714367)). Qed.
Lemma lem1714369 (x : real) (h1 : term721 x) : False.
Proof. exact (EQ_MP (@lem1714368) (@lem1714362 x h1)). Qed.
Lemma lem1714370 (x : real) (h1 : term675 x) : False.
Proof. exact (or_elim (@lem1714339 x h1) (fun h0 : term721 x => @lem1714354 x h0) (fun h0 : term721 x => @lem1714369 x h0)). Qed.
Lemma lem1714371 (x : real) (h1 : term671 x) : term671 x.
Proof. exact (h1). Qed.
Lemma lem1714372 (x : real) (h1 : term722 x) : term722 x.
Proof. exact (h1). Qed.
Lemma lem1714373 (x : real) (h1 : term722 x) : term672 x.
Proof. exact (proj2 (@lem1714372 x h1)). Qed.
Lemma lem1714375 (x : real) (h1 : term722 x) : term628 x.
Proof. exact (proj2 (@lem1714373 x h1)). Qed.
Lemma lem1714377 (x : real) (h1 : term722 x) : term618 x.
Proof. exact (proj2 (@lem1714375 x h1)). Qed.
Lemma lem1714379 (x : real) (h1 : term722 x) : term233.
Proof. exact (proj2 (@lem1714377 x h1)). Qed.
Lemma lem1714382 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714383 : term233 = False.
Proof. exact (@lem1714382 term218 (NUMERAL 0)). Qed.
Lemma lem1714384 (x : real) (h1 : term722 x) : False.
Proof. exact (EQ_MP (@lem1714383) (@lem1714379 x h1)). Qed.
Lemma lem1714385 (x : real) (h1 : term723 x) : term723 x.
Proof. exact (h1). Qed.
Lemma lem1714386 (x : real) (h1 : term723 x) : term673 x.
Proof. exact (proj2 (@lem1714385 x h1)). Qed.
Lemma lem1714387 (x : real) (h1 : term723 x) : term171 x.
Proof. exact (proj1 (@lem1714385 x h1)). Qed.
Lemma lem1714388 (x : real) (h1 : term723 x) : term629 x.
Proof. exact (proj2 (@lem1714386 x h1)). Qed.
Lemma lem1714390 (x : real) (h1 : term723 x) : term619 x.
Proof. exact (proj2 (@lem1714388 x h1)). Qed.
Lemma lem1714393 (x : real) (h1 : term723 x) : term273 x.
Proof. exact (proj1 (@lem1714390 x h1)). Qed.
Lemma lem1714395 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714396 : term318 = term694.
Proof. exact (@lem1714395 (NUMERAL 0) term183). Qed.
Lemma lem1714397 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714398 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714399 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714398 h1) (fun h1 : term694 = True => @lem1714397)). Qed.
Lemma lem1714400 : term694 = True.
Proof. exact (EQ_MP (@lem1714399) (@lem1714397)). Qed.
Lemma lem1714401 : term318 = True.
Proof. exact (TRANS (@lem1714396) (@lem1714400)). Qed.
Lemma lem1714402 : True = term318.
Proof. exact (SYM (@lem1714401)). Qed.
Lemma lem1714403 : term318.
Proof. exact (EQ_MP (@lem1714402) (@lem0)). Qed.
Lemma lem1714404 (x : real) (h1 : term723 x) : term724 x.
Proof. exact (conj (@lem1714403) (@lem1714393 x h1)). Qed.
Lemma lem1714406 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1714407 (x : real) : term726 x.
Proof. exact (@lem1714406 term24 x). Qed.
Lemma lem1714408 (x : real) (h1 : term723 x) : term727 x.
Proof. exact (@lem1714407 x (@lem1714404 x h1)). Qed.
Lemma lem1714409 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1714410 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1714411 (x : real) : (term728 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1714410) (@lem1714409 x)). Qed.
Lemma lem1714412 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714413 (x : real) : (term727 x) = (term273 x).
Proof. exact (MK_COMB (@lem1714411 x) (@lem1714412)). Qed.
Lemma lem1714414 (x : real) (h1 : term723 x) : term273 x.
Proof. exact (EQ_MP (@lem1714413 x) (@lem1714408 x h1)). Qed.
Lemma lem1714416 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714417 : term318 = term694.
Proof. exact (@lem1714416 (NUMERAL 0) term183). Qed.
Lemma lem1714418 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714419 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714420 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714419 h1) (fun h1 : term694 = True => @lem1714418)). Qed.
Lemma lem1714421 : term694 = True.
Proof. exact (EQ_MP (@lem1714420) (@lem1714418)). Qed.
Lemma lem1714422 : term318 = True.
Proof. exact (TRANS (@lem1714417) (@lem1714421)). Qed.
Lemma lem1714423 : True = term318.
Proof. exact (SYM (@lem1714422)). Qed.
Lemma lem1714424 : term318.
Proof. exact (EQ_MP (@lem1714423) (@lem0)). Qed.
Lemma lem1714425 (x : real) (h1 : term723 x) : term701 x.
Proof. exact (conj (@lem1714424) (@lem1714387 x h1)). Qed.
Lemma lem1714427 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714428 (x : real) : term702 x.
Proof. exact (@lem1714427 term24 (term168 x)). Qed.
Lemma lem1714429 (x : real) (h1 : term723 x) : term703 x.
Proof. exact (@lem1714428 x (@lem1714425 x h1)). Qed.
Lemma lem1714430 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1714431 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714432 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1714431) (@lem1714430 x)). Qed.
Lemma lem1714433 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714434 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1714432 x) (@lem1714433)). Qed.
Lemma lem1714435 (x : real) (h1 : term723 x) : term171 x.
Proof. exact (EQ_MP (@lem1714434 x) (@lem1714429 x h1)). Qed.
Lemma lem1714436 (x : real) (h1 : term723 x) : term729 x.
Proof. exact (conj (@lem1714435 x h1) (@lem1714414 x h1)). Qed.
Lemma lem1714438 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1714439 (x : real) : term731 x.
Proof. exact (@lem1714438 (term168 x) x). Qed.
Lemma lem1714440 (x : real) (h1 : term723 x) : term709 x.
Proof. exact (@lem1714439 x (@lem1714436 x h1)). Qed.
Lemma lem1714441 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1714443 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1714444 : term713 = term75.
Proof. exact (@lem1714443 term183). Qed.
Lemma lem1714445 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1714446 : term714 = term715.
Proof. exact (MK_COMB (@lem1714445) (@lem1714444)). Qed.
Lemma lem1714447 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1714448 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1714446) (@lem1714447 x)). Qed.
Lemma lem1714449 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1714441 x) (@lem1714448 x)). Qed.
Lemma lem1714450 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1714451 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1714449 x) (@lem1714450 x)). Qed.
Lemma lem1714452 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714453 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1714452) (@lem1714451 x)). Qed.
Lemma lem1714454 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714455 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1714453 x) (@lem1714454)). Qed.
Lemma lem1714456 (x : real) (h1 : term723 x) : term264.
Proof. exact (EQ_MP (@lem1714455 x) (@lem1714440 x h1)). Qed.
Lemma lem1714458 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714459 : term264 = term718.
Proof. exact (@lem1714458 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714460 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714461 : term264 = False.
Proof. exact (TRANS (@lem1714459) (@lem1714460)). Qed.
Lemma lem1714462 (x : real) (h1 : term723 x) : False.
Proof. exact (EQ_MP (@lem1714461) (@lem1714456 x h1)). Qed.
Lemma lem1714463 (x : real) (h1 : term671 x) : False.
Proof. exact (or_elim (@lem1714371 x h1) (fun h0 : term722 x => @lem1714384 x h0) (fun h0 : term723 x => @lem1714462 x h0)). Qed.
Lemma lem1714464 (x : real) (h1 : term679 x) : False.
Proof. exact (or_elim (@lem1714338 x h1) (fun h0 : term675 x => @lem1714370 x h0) (fun h0 : term671 x => @lem1714463 x h0)). Qed.
Lemma lem1714465 (x : real) (h1 : term684 x) : False.
Proof. exact (or_elim (@lem1714244 x h1) (fun h0 : term681 x => @lem1714337 x h0) (fun h0 : term679 x => @lem1714464 x h0)). Qed.
Lemma lem1714466 (x : real) (h1 : term665 x) : term665 x.
Proof. exact (h1). Qed.
Lemma lem1714467 (x : real) (h1 : term662 x) : term662 x.
Proof. exact (h1). Qed.
Lemma lem1714468 (x : real) (h1 : term659 x) : term659 x.
Proof. exact (h1). Qed.
Lemma lem1714469 (x : real) (h1 : term732 x) : term732 x.
Proof. exact (h1). Qed.
Lemma lem1714470 (x : real) (h1 : term732 x) : term554 x.
Proof. exact (proj2 (@lem1714469 x h1)). Qed.
Lemma lem1714472 (x : real) (h1 : term732 x) : term494 x.
Proof. exact (proj2 (@lem1714470 x h1)). Qed.
Lemma lem1714474 (x : real) (h1 : term732 x) : term465 x.
Proof. exact (proj2 (@lem1714472 x h1)). Qed.
Lemma lem1714475 (x : real) (h1 : term732 x) : term192 x.
Proof. exact (proj1 (@lem1714472 x h1)). Qed.
Lemma lem1714477 (x : real) (h1 : term732 x) : term171 x.
Proof. exact (proj1 (@lem1714474 x h1)). Qed.
Lemma lem1714479 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714480 : term318 = term694.
Proof. exact (@lem1714479 (NUMERAL 0) term183). Qed.
Lemma lem1714481 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714482 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714483 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714482 h1) (fun h1 : term694 = True => @lem1714481)). Qed.
Lemma lem1714484 : term694 = True.
Proof. exact (EQ_MP (@lem1714483) (@lem1714481)). Qed.
Lemma lem1714485 : term318 = True.
Proof. exact (TRANS (@lem1714480) (@lem1714484)). Qed.
Lemma lem1714486 : True = term318.
Proof. exact (SYM (@lem1714485)). Qed.
Lemma lem1714487 : term318.
Proof. exact (EQ_MP (@lem1714486) (@lem0)). Qed.
Lemma lem1714488 (x : real) (h1 : term732 x) : term696 x.
Proof. exact (conj (@lem1714487) (@lem1714475 x h1)). Qed.
Lemma lem1714490 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714491 (x : real) : term698 x.
Proof. exact (@lem1714490 term24 x). Qed.
Lemma lem1714492 (x : real) (h1 : term732 x) : term699 x.
Proof. exact (@lem1714491 x (@lem1714488 x h1)). Qed.
Lemma lem1714493 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1714494 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714495 (x : real) : (term700 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1714494) (@lem1714493 x)). Qed.
Lemma lem1714496 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714497 (x : real) : (term699 x) = (term192 x).
Proof. exact (MK_COMB (@lem1714495 x) (@lem1714496)). Qed.
Lemma lem1714498 (x : real) (h1 : term732 x) : term192 x.
Proof. exact (EQ_MP (@lem1714497 x) (@lem1714492 x h1)). Qed.
Lemma lem1714500 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714501 : term318 = term694.
Proof. exact (@lem1714500 (NUMERAL 0) term183). Qed.
Lemma lem1714502 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714503 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714504 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714503 h1) (fun h1 : term694 = True => @lem1714502)). Qed.
Lemma lem1714505 : term694 = True.
Proof. exact (EQ_MP (@lem1714504) (@lem1714502)). Qed.
Lemma lem1714506 : term318 = True.
Proof. exact (TRANS (@lem1714501) (@lem1714505)). Qed.
Lemma lem1714507 : True = term318.
Proof. exact (SYM (@lem1714506)). Qed.
Lemma lem1714508 : term318.
Proof. exact (EQ_MP (@lem1714507) (@lem0)). Qed.
Lemma lem1714509 (x : real) (h1 : term732 x) : term701 x.
Proof. exact (conj (@lem1714508) (@lem1714477 x h1)). Qed.
Lemma lem1714511 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714512 (x : real) : term702 x.
Proof. exact (@lem1714511 term24 (term168 x)). Qed.
Lemma lem1714513 (x : real) (h1 : term732 x) : term703 x.
Proof. exact (@lem1714512 x (@lem1714509 x h1)). Qed.
Lemma lem1714514 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1714515 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714516 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1714515) (@lem1714514 x)). Qed.
Lemma lem1714517 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714518 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1714516 x) (@lem1714517)). Qed.
Lemma lem1714519 (x : real) (h1 : term732 x) : term171 x.
Proof. exact (EQ_MP (@lem1714518 x) (@lem1714513 x h1)). Qed.
Lemma lem1714520 (x : real) (h1 : term732 x) : term706 x.
Proof. exact (conj (@lem1714519 x h1) (@lem1714498 x h1)). Qed.
Lemma lem1714522 (x : real) (y : real) : term707 x y.
Proof. exact (proj2 (@lem1483584 x y)). Qed.
Lemma lem1714523 (x : real) : term708 x.
Proof. exact (@lem1714522 (term168 x) x). Qed.
Lemma lem1714524 (x : real) (h1 : term732 x) : term709 x.
Proof. exact (@lem1714523 x (@lem1714520 x h1)). Qed.
Lemma lem1714525 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1714527 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1714528 : term713 = term75.
Proof. exact (@lem1714527 term183). Qed.
Lemma lem1714529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1714530 : term714 = term715.
Proof. exact (MK_COMB (@lem1714529) (@lem1714528)). Qed.
Lemma lem1714531 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1714532 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1714530) (@lem1714531 x)). Qed.
Lemma lem1714533 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1714525 x) (@lem1714532 x)). Qed.
Lemma lem1714534 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1714535 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1714533 x) (@lem1714534 x)). Qed.
Lemma lem1714536 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714537 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1714536) (@lem1714535 x)). Qed.
Lemma lem1714538 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714539 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1714537 x) (@lem1714538)). Qed.
Lemma lem1714540 (x : real) (h1 : term732 x) : term264.
Proof. exact (EQ_MP (@lem1714539 x) (@lem1714524 x h1)). Qed.
Lemma lem1714542 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714543 : term264 = term718.
Proof. exact (@lem1714542 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714544 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714545 : term264 = False.
Proof. exact (TRANS (@lem1714543) (@lem1714544)). Qed.
Lemma lem1714546 (x : real) (h1 : term732 x) : False.
Proof. exact (EQ_MP (@lem1714545) (@lem1714540 x h1)). Qed.
Lemma lem1714547 (x : real) (h1 : term733 x) : term733 x.
Proof. exact (h1). Qed.
Lemma lem1714548 (x : real) (h1 : term733 x) : term555 x.
Proof. exact (proj2 (@lem1714547 x h1)). Qed.
Lemma lem1714550 (x : real) (h1 : term733 x) : term495 x.
Proof. exact (proj2 (@lem1714548 x h1)). Qed.
Lemma lem1714552 (x : real) (h1 : term733 x) : term466 x.
Proof. exact (proj2 (@lem1714550 x h1)). Qed.
Lemma lem1714554 (x : real) (h1 : term733 x) : term233.
Proof. exact (proj2 (@lem1714552 x h1)). Qed.
Lemma lem1714557 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714558 : term233 = False.
Proof. exact (@lem1714557 term218 (NUMERAL 0)). Qed.
Lemma lem1714559 (x : real) (h1 : term733 x) : False.
Proof. exact (EQ_MP (@lem1714558) (@lem1714554 x h1)). Qed.
Lemma lem1714560 (x : real) (h1 : term659 x) : False.
Proof. exact (or_elim (@lem1714468 x h1) (fun h0 : term732 x => @lem1714546 x h0) (fun h0 : term733 x => @lem1714559 x h0)). Qed.
Lemma lem1714561 (x : real) (h1 : term657 x) : term657 x.
Proof. exact (h1). Qed.
Lemma lem1714562 (x : real) (h1 : term734 x) : term734 x.
Proof. exact (h1). Qed.
Lemma lem1714563 (x : real) (h1 : term734 x) : term550 x.
Proof. exact (proj2 (@lem1714562 x h1)). Qed.
Lemma lem1714564 (x : real) (h1 : term734 x) : term171 x.
Proof. exact (proj1 (@lem1714562 x h1)). Qed.
Lemma lem1714565 (x : real) (h1 : term734 x) : term490 x.
Proof. exact (proj2 (@lem1714563 x h1)). Qed.
Lemma lem1714567 (x : real) (h1 : term734 x) : term461 x.
Proof. exact (proj2 (@lem1714565 x h1)). Qed.
Lemma lem1714570 (x : real) (h1 : term734 x) : term273 x.
Proof. exact (proj1 (@lem1714567 x h1)). Qed.
Lemma lem1714572 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714573 : term318 = term694.
Proof. exact (@lem1714572 (NUMERAL 0) term183). Qed.
Lemma lem1714574 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714575 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714576 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714575 h1) (fun h1 : term694 = True => @lem1714574)). Qed.
Lemma lem1714577 : term694 = True.
Proof. exact (EQ_MP (@lem1714576) (@lem1714574)). Qed.
Lemma lem1714578 : term318 = True.
Proof. exact (TRANS (@lem1714573) (@lem1714577)). Qed.
Lemma lem1714579 : True = term318.
Proof. exact (SYM (@lem1714578)). Qed.
Lemma lem1714580 : term318.
Proof. exact (EQ_MP (@lem1714579) (@lem0)). Qed.
Lemma lem1714581 (x : real) (h1 : term734 x) : term724 x.
Proof. exact (conj (@lem1714580) (@lem1714570 x h1)). Qed.
Lemma lem1714583 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1714584 (x : real) : term726 x.
Proof. exact (@lem1714583 term24 x). Qed.
Lemma lem1714585 (x : real) (h1 : term734 x) : term727 x.
Proof. exact (@lem1714584 x (@lem1714581 x h1)). Qed.
Lemma lem1714586 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1714587 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1714588 (x : real) : (term728 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1714587) (@lem1714586 x)). Qed.
Lemma lem1714589 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714590 (x : real) : (term727 x) = (term273 x).
Proof. exact (MK_COMB (@lem1714588 x) (@lem1714589)). Qed.
Lemma lem1714591 (x : real) (h1 : term734 x) : term273 x.
Proof. exact (EQ_MP (@lem1714590 x) (@lem1714585 x h1)). Qed.
Lemma lem1714593 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714594 : term318 = term694.
Proof. exact (@lem1714593 (NUMERAL 0) term183). Qed.
Lemma lem1714595 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714596 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714597 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714596 h1) (fun h1 : term694 = True => @lem1714595)). Qed.
Lemma lem1714598 : term694 = True.
Proof. exact (EQ_MP (@lem1714597) (@lem1714595)). Qed.
Lemma lem1714599 : term318 = True.
Proof. exact (TRANS (@lem1714594) (@lem1714598)). Qed.
Lemma lem1714600 : True = term318.
Proof. exact (SYM (@lem1714599)). Qed.
Lemma lem1714601 : term318.
Proof. exact (EQ_MP (@lem1714600) (@lem0)). Qed.
Lemma lem1714602 (x : real) (h1 : term734 x) : term701 x.
Proof. exact (conj (@lem1714601) (@lem1714564 x h1)). Qed.
Lemma lem1714604 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714605 (x : real) : term702 x.
Proof. exact (@lem1714604 term24 (term168 x)). Qed.
Lemma lem1714606 (x : real) (h1 : term734 x) : term703 x.
Proof. exact (@lem1714605 x (@lem1714602 x h1)). Qed.
Lemma lem1714607 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1714608 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714609 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1714608) (@lem1714607 x)). Qed.
Lemma lem1714610 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714611 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1714609 x) (@lem1714610)). Qed.
Lemma lem1714612 (x : real) (h1 : term734 x) : term171 x.
Proof. exact (EQ_MP (@lem1714611 x) (@lem1714606 x h1)). Qed.
Lemma lem1714613 (x : real) (h1 : term734 x) : term729 x.
Proof. exact (conj (@lem1714612 x h1) (@lem1714591 x h1)). Qed.
Lemma lem1714615 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1714616 (x : real) : term731 x.
Proof. exact (@lem1714615 (term168 x) x). Qed.
Lemma lem1714617 (x : real) (h1 : term734 x) : term709 x.
Proof. exact (@lem1714616 x (@lem1714613 x h1)). Qed.
Lemma lem1714618 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1714620 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1714621 : term713 = term75.
Proof. exact (@lem1714620 term183). Qed.
Lemma lem1714622 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1714623 : term714 = term715.
Proof. exact (MK_COMB (@lem1714622) (@lem1714621)). Qed.
Lemma lem1714624 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1714625 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1714623) (@lem1714624 x)). Qed.
Lemma lem1714626 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1714618 x) (@lem1714625 x)). Qed.
Lemma lem1714627 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1714628 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1714626 x) (@lem1714627 x)). Qed.
Lemma lem1714629 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714630 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1714629) (@lem1714628 x)). Qed.
Lemma lem1714631 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714632 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1714630 x) (@lem1714631)). Qed.
Lemma lem1714633 (x : real) (h1 : term734 x) : term264.
Proof. exact (EQ_MP (@lem1714632 x) (@lem1714617 x h1)). Qed.
Lemma lem1714635 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714636 : term264 = term718.
Proof. exact (@lem1714635 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714637 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714638 : term264 = False.
Proof. exact (TRANS (@lem1714636) (@lem1714637)). Qed.
Lemma lem1714639 (x : real) (h1 : term734 x) : False.
Proof. exact (EQ_MP (@lem1714638) (@lem1714633 x h1)). Qed.
Lemma lem1714640 (x : real) (h1 : term735 x) : term735 x.
Proof. exact (h1). Qed.
Lemma lem1714641 (x : real) (h1 : term735 x) : term551 x.
Proof. exact (proj2 (@lem1714640 x h1)). Qed.
Lemma lem1714643 (x : real) (h1 : term735 x) : term491 x.
Proof. exact (proj2 (@lem1714641 x h1)). Qed.
Lemma lem1714645 (x : real) (h1 : term735 x) : term462 x.
Proof. exact (proj2 (@lem1714643 x h1)). Qed.
Lemma lem1714647 (x : real) (h1 : term735 x) : term314.
Proof. exact (proj2 (@lem1714645 x h1)). Qed.
Lemma lem1714650 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714651 : term314 = False.
Proof. exact (@lem1714650 term183 (NUMERAL 0)). Qed.
Lemma lem1714652 (x : real) (h1 : term735 x) : False.
Proof. exact (EQ_MP (@lem1714651) (@lem1714647 x h1)). Qed.
Lemma lem1714653 (x : real) (h1 : term657 x) : False.
Proof. exact (or_elim (@lem1714561 x h1) (fun h0 : term734 x => @lem1714639 x h0) (fun h0 : term735 x => @lem1714652 x h0)). Qed.
Lemma lem1714654 (x : real) (h1 : term662 x) : False.
Proof. exact (or_elim (@lem1714467 x h1) (fun h0 : term659 x => @lem1714560 x h0) (fun h0 : term657 x => @lem1714653 x h0)). Qed.
Lemma lem1714655 (x : real) (h1 : term653 x) : term653 x.
Proof. exact (h1). Qed.
Lemma lem1714656 (x : real) (h1 : term649 x) : term649 x.
Proof. exact (h1). Qed.
Lemma lem1714657 (x : real) (h1 : term736 x) : term736 x.
Proof. exact (h1). Qed.
Lemma lem1714658 (x : real) (h1 : term736 x) : term650 x.
Proof. exact (proj2 (@lem1714657 x h1)). Qed.
Lemma lem1714660 (x : real) (h1 : term736 x) : term607 x.
Proof. exact (proj2 (@lem1714658 x h1)). Qed.
Lemma lem1714662 (x : real) (h1 : term736 x) : term594 x.
Proof. exact (proj2 (@lem1714660 x h1)). Qed.
Lemma lem1714664 (x : real) (h1 : term736 x) : term264.
Proof. exact (proj2 (@lem1714662 x h1)). Qed.
Lemma lem1714667 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714668 : term264 = term718.
Proof. exact (@lem1714667 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714669 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714670 : term264 = False.
Proof. exact (TRANS (@lem1714668) (@lem1714669)). Qed.
Lemma lem1714671 (x : real) (h1 : term736 x) : False.
Proof. exact (EQ_MP (@lem1714670) (@lem1714664 x h1)). Qed.
Lemma lem1714672 (x : real) (h1 : term736 x) : term736 x.
Proof. exact (h1). Qed.
Lemma lem1714673 (x : real) (h1 : term736 x) : term650 x.
Proof. exact (proj2 (@lem1714672 x h1)). Qed.
Lemma lem1714675 (x : real) (h1 : term736 x) : term607 x.
Proof. exact (proj2 (@lem1714673 x h1)). Qed.
Lemma lem1714677 (x : real) (h1 : term736 x) : term594 x.
Proof. exact (proj2 (@lem1714675 x h1)). Qed.
Lemma lem1714679 (x : real) (h1 : term736 x) : term264.
Proof. exact (proj2 (@lem1714677 x h1)). Qed.
Lemma lem1714682 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714683 : term264 = term718.
Proof. exact (@lem1714682 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714684 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714685 : term264 = False.
Proof. exact (TRANS (@lem1714683) (@lem1714684)). Qed.
Lemma lem1714686 (x : real) (h1 : term736 x) : False.
Proof. exact (EQ_MP (@lem1714685) (@lem1714679 x h1)). Qed.
Lemma lem1714687 (x : real) (h1 : term649 x) : False.
Proof. exact (or_elim (@lem1714656 x h1) (fun h0 : term736 x => @lem1714671 x h0) (fun h0 : term736 x => @lem1714686 x h0)). Qed.
Lemma lem1714688 (x : real) (h1 : term645 x) : term645 x.
Proof. exact (h1). Qed.
Lemma lem1714689 (x : real) (h1 : term737 x) : term737 x.
Proof. exact (h1). Qed.
Lemma lem1714690 (x : real) (h1 : term737 x) : term646 x.
Proof. exact (proj2 (@lem1714689 x h1)). Qed.
Lemma lem1714692 (x : real) (h1 : term737 x) : term516 x.
Proof. exact (proj2 (@lem1714690 x h1)). Qed.
Lemma lem1714694 (x : real) (h1 : term737 x) : term462 x.
Proof. exact (proj2 (@lem1714692 x h1)). Qed.
Lemma lem1714696 (x : real) (h1 : term737 x) : term314.
Proof. exact (proj2 (@lem1714694 x h1)). Qed.
Lemma lem1714699 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714700 : term314 = False.
Proof. exact (@lem1714699 term183 (NUMERAL 0)). Qed.
Lemma lem1714701 (x : real) (h1 : term737 x) : False.
Proof. exact (EQ_MP (@lem1714700) (@lem1714696 x h1)). Qed.
Lemma lem1714702 (x : real) (h1 : term738 x) : term738 x.
Proof. exact (h1). Qed.
Lemma lem1714703 (x : real) (h1 : term738 x) : term647 x.
Proof. exact (proj2 (@lem1714702 x h1)). Qed.
Lemma lem1714704 (x : real) (h1 : term738 x) : term171 x.
Proof. exact (proj1 (@lem1714702 x h1)). Qed.
Lemma lem1714705 (x : real) (h1 : term738 x) : term517 x.
Proof. exact (proj2 (@lem1714703 x h1)). Qed.
Lemma lem1714707 (x : real) (h1 : term738 x) : term461 x.
Proof. exact (proj2 (@lem1714705 x h1)). Qed.
Lemma lem1714710 (x : real) (h1 : term738 x) : term273 x.
Proof. exact (proj1 (@lem1714707 x h1)). Qed.
Lemma lem1714712 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714713 : term318 = term694.
Proof. exact (@lem1714712 (NUMERAL 0) term183). Qed.
Lemma lem1714714 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714715 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714716 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714715 h1) (fun h1 : term694 = True => @lem1714714)). Qed.
Lemma lem1714717 : term694 = True.
Proof. exact (EQ_MP (@lem1714716) (@lem1714714)). Qed.
Lemma lem1714718 : term318 = True.
Proof. exact (TRANS (@lem1714713) (@lem1714717)). Qed.
Lemma lem1714719 : True = term318.
Proof. exact (SYM (@lem1714718)). Qed.
Lemma lem1714720 : term318.
Proof. exact (EQ_MP (@lem1714719) (@lem0)). Qed.
Lemma lem1714721 (x : real) (h1 : term738 x) : term724 x.
Proof. exact (conj (@lem1714720) (@lem1714710 x h1)). Qed.
Lemma lem1714723 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1714724 (x : real) : term726 x.
Proof. exact (@lem1714723 term24 x). Qed.
Lemma lem1714725 (x : real) (h1 : term738 x) : term727 x.
Proof. exact (@lem1714724 x (@lem1714721 x h1)). Qed.
Lemma lem1714726 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1714727 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1714728 (x : real) : (term728 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1714727) (@lem1714726 x)). Qed.
Lemma lem1714729 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714730 (x : real) : (term727 x) = (term273 x).
Proof. exact (MK_COMB (@lem1714728 x) (@lem1714729)). Qed.
Lemma lem1714731 (x : real) (h1 : term738 x) : term273 x.
Proof. exact (EQ_MP (@lem1714730 x) (@lem1714725 x h1)). Qed.
Lemma lem1714733 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714734 : term318 = term694.
Proof. exact (@lem1714733 (NUMERAL 0) term183). Qed.
Lemma lem1714735 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714736 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714737 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714736 h1) (fun h1 : term694 = True => @lem1714735)). Qed.
Lemma lem1714738 : term694 = True.
Proof. exact (EQ_MP (@lem1714737) (@lem1714735)). Qed.
Lemma lem1714739 : term318 = True.
Proof. exact (TRANS (@lem1714734) (@lem1714738)). Qed.
Lemma lem1714740 : True = term318.
Proof. exact (SYM (@lem1714739)). Qed.
Lemma lem1714741 : term318.
Proof. exact (EQ_MP (@lem1714740) (@lem0)). Qed.
Lemma lem1714742 (x : real) (h1 : term738 x) : term701 x.
Proof. exact (conj (@lem1714741) (@lem1714704 x h1)). Qed.
Lemma lem1714744 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714745 (x : real) : term702 x.
Proof. exact (@lem1714744 term24 (term168 x)). Qed.
Lemma lem1714746 (x : real) (h1 : term738 x) : term703 x.
Proof. exact (@lem1714745 x (@lem1714742 x h1)). Qed.
Lemma lem1714747 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1714748 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714749 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1714748) (@lem1714747 x)). Qed.
Lemma lem1714750 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714751 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1714749 x) (@lem1714750)). Qed.
Lemma lem1714752 (x : real) (h1 : term738 x) : term171 x.
Proof. exact (EQ_MP (@lem1714751 x) (@lem1714746 x h1)). Qed.
Lemma lem1714753 (x : real) (h1 : term738 x) : term729 x.
Proof. exact (conj (@lem1714752 x h1) (@lem1714731 x h1)). Qed.
Lemma lem1714755 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1714756 (x : real) : term731 x.
Proof. exact (@lem1714755 (term168 x) x). Qed.
Lemma lem1714757 (x : real) (h1 : term738 x) : term709 x.
Proof. exact (@lem1714756 x (@lem1714753 x h1)). Qed.
Lemma lem1714758 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1714760 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1714761 : term713 = term75.
Proof. exact (@lem1714760 term183). Qed.
Lemma lem1714762 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1714763 : term714 = term715.
Proof. exact (MK_COMB (@lem1714762) (@lem1714761)). Qed.
Lemma lem1714764 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1714765 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1714763) (@lem1714764 x)). Qed.
Lemma lem1714766 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1714758 x) (@lem1714765 x)). Qed.
Lemma lem1714767 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1714768 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1714766 x) (@lem1714767 x)). Qed.
Lemma lem1714769 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714770 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1714769) (@lem1714768 x)). Qed.
Lemma lem1714771 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714772 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1714770 x) (@lem1714771)). Qed.
Lemma lem1714773 (x : real) (h1 : term738 x) : term264.
Proof. exact (EQ_MP (@lem1714772 x) (@lem1714757 x h1)). Qed.
Lemma lem1714775 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714776 : term264 = term718.
Proof. exact (@lem1714775 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714777 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714778 : term264 = False.
Proof. exact (TRANS (@lem1714776) (@lem1714777)). Qed.
Lemma lem1714779 (x : real) (h1 : term738 x) : False.
Proof. exact (EQ_MP (@lem1714778) (@lem1714773 x h1)). Qed.
Lemma lem1714780 (x : real) (h1 : term645 x) : False.
Proof. exact (or_elim (@lem1714688 x h1) (fun h0 : term737 x => @lem1714701 x h0) (fun h0 : term738 x => @lem1714779 x h0)). Qed.
Lemma lem1714781 (x : real) (h1 : term653 x) : False.
Proof. exact (or_elim (@lem1714655 x h1) (fun h0 : term649 x => @lem1714687 x h0) (fun h0 : term645 x => @lem1714780 x h0)). Qed.
Lemma lem1714782 (x : real) (h1 : term665 x) : False.
Proof. exact (or_elim (@lem1714466 x h1) (fun h0 : term662 x => @lem1714654 x h0) (fun h0 : term653 x => @lem1714781 x h0)). Qed.
Lemma lem1714783 (x : real) (h1 : term687 x) : False.
Proof. exact (or_elim (@lem1714243 x h1) (fun h0 : term684 x => @lem1714465 x h0) (fun h0 : term665 x => @lem1714782 x h0)). Qed.
Lemma lem1714784 (x : real) (h1 : term586 x) : term586 x.
Proof. exact (h1). Qed.
Lemma lem1714785 (x : real) (h1 : term583 x) : term583 x.
Proof. exact (h1). Qed.
Lemma lem1714786 (x : real) (h1 : term578 x) : term578 x.
Proof. exact (h1). Qed.
Lemma lem1714787 (x : real) (h1 : term739 x) : term739 x.
Proof. exact (h1). Qed.
Lemma lem1714788 (x : real) (h1 : term739 x) : term579 x.
Proof. exact (proj2 (@lem1714787 x h1)). Qed.
Lemma lem1714789 (x : real) (h1 : term739 x) : term273 x.
Proof. exact (proj1 (@lem1714787 x h1)). Qed.
Lemma lem1714790 (x : real) (h1 : term739 x) : term494 x.
Proof. exact (proj2 (@lem1714788 x h1)). Qed.
Lemma lem1714792 (x : real) (h1 : term739 x) : term465 x.
Proof. exact (proj2 (@lem1714790 x h1)). Qed.
Lemma lem1714795 (x : real) (h1 : term739 x) : term171 x.
Proof. exact (proj1 (@lem1714792 x h1)). Qed.
Lemma lem1714797 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714798 : term318 = term694.
Proof. exact (@lem1714797 (NUMERAL 0) term183). Qed.
Lemma lem1714799 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714800 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714801 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714800 h1) (fun h1 : term694 = True => @lem1714799)). Qed.
Lemma lem1714802 : term694 = True.
Proof. exact (EQ_MP (@lem1714801) (@lem1714799)). Qed.
Lemma lem1714803 : term318 = True.
Proof. exact (TRANS (@lem1714798) (@lem1714802)). Qed.
Lemma lem1714804 : True = term318.
Proof. exact (SYM (@lem1714803)). Qed.
Lemma lem1714805 : term318.
Proof. exact (EQ_MP (@lem1714804) (@lem0)). Qed.
Lemma lem1714806 (x : real) (h1 : term739 x) : term724 x.
Proof. exact (conj (@lem1714805) (@lem1714789 x h1)). Qed.
Lemma lem1714808 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1714809 (x : real) : term726 x.
Proof. exact (@lem1714808 term24 x). Qed.
Lemma lem1714810 (x : real) (h1 : term739 x) : term727 x.
Proof. exact (@lem1714809 x (@lem1714806 x h1)). Qed.
Lemma lem1714811 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1714812 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1714813 (x : real) : (term728 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1714812) (@lem1714811 x)). Qed.
Lemma lem1714814 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714815 (x : real) : (term727 x) = (term273 x).
Proof. exact (MK_COMB (@lem1714813 x) (@lem1714814)). Qed.
Lemma lem1714816 (x : real) (h1 : term739 x) : term273 x.
Proof. exact (EQ_MP (@lem1714815 x) (@lem1714810 x h1)). Qed.
Lemma lem1714818 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714819 : term318 = term694.
Proof. exact (@lem1714818 (NUMERAL 0) term183). Qed.
Lemma lem1714820 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714821 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714822 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714821 h1) (fun h1 : term694 = True => @lem1714820)). Qed.
Lemma lem1714823 : term694 = True.
Proof. exact (EQ_MP (@lem1714822) (@lem1714820)). Qed.
Lemma lem1714824 : term318 = True.
Proof. exact (TRANS (@lem1714819) (@lem1714823)). Qed.
Lemma lem1714825 : True = term318.
Proof. exact (SYM (@lem1714824)). Qed.
Lemma lem1714826 : term318.
Proof. exact (EQ_MP (@lem1714825) (@lem0)). Qed.
Lemma lem1714827 (x : real) (h1 : term739 x) : term701 x.
Proof. exact (conj (@lem1714826) (@lem1714795 x h1)). Qed.
Lemma lem1714829 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714830 (x : real) : term702 x.
Proof. exact (@lem1714829 term24 (term168 x)). Qed.
Lemma lem1714831 (x : real) (h1 : term739 x) : term703 x.
Proof. exact (@lem1714830 x (@lem1714827 x h1)). Qed.
Lemma lem1714832 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1714833 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714834 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1714833) (@lem1714832 x)). Qed.
Lemma lem1714835 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714836 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1714834 x) (@lem1714835)). Qed.
Lemma lem1714837 (x : real) (h1 : term739 x) : term171 x.
Proof. exact (EQ_MP (@lem1714836 x) (@lem1714831 x h1)). Qed.
Lemma lem1714838 (x : real) (h1 : term739 x) : term729 x.
Proof. exact (conj (@lem1714837 x h1) (@lem1714816 x h1)). Qed.
Lemma lem1714840 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1714841 (x : real) : term731 x.
Proof. exact (@lem1714840 (term168 x) x). Qed.
Lemma lem1714842 (x : real) (h1 : term739 x) : term709 x.
Proof. exact (@lem1714841 x (@lem1714838 x h1)). Qed.
Lemma lem1714843 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1714845 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1714846 : term713 = term75.
Proof. exact (@lem1714845 term183). Qed.
Lemma lem1714847 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1714848 : term714 = term715.
Proof. exact (MK_COMB (@lem1714847) (@lem1714846)). Qed.
Lemma lem1714849 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1714850 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1714848) (@lem1714849 x)). Qed.
Lemma lem1714851 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1714843 x) (@lem1714850 x)). Qed.
Lemma lem1714852 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1714853 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1714851 x) (@lem1714852 x)). Qed.
Lemma lem1714854 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714855 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1714854) (@lem1714853 x)). Qed.
Lemma lem1714856 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714857 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1714855 x) (@lem1714856)). Qed.
Lemma lem1714858 (x : real) (h1 : term739 x) : term264.
Proof. exact (EQ_MP (@lem1714857 x) (@lem1714842 x h1)). Qed.
Lemma lem1714860 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714861 : term264 = term718.
Proof. exact (@lem1714860 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714862 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714863 : term264 = False.
Proof. exact (TRANS (@lem1714861) (@lem1714862)). Qed.
Lemma lem1714864 (x : real) (h1 : term739 x) : False.
Proof. exact (EQ_MP (@lem1714863) (@lem1714858 x h1)). Qed.
Lemma lem1714865 (x : real) (h1 : term740 x) : term740 x.
Proof. exact (h1). Qed.
Lemma lem1714866 (x : real) (h1 : term740 x) : term580 x.
Proof. exact (proj2 (@lem1714865 x h1)). Qed.
Lemma lem1714868 (x : real) (h1 : term740 x) : term495 x.
Proof. exact (proj2 (@lem1714866 x h1)). Qed.
Lemma lem1714870 (x : real) (h1 : term740 x) : term466 x.
Proof. exact (proj2 (@lem1714868 x h1)). Qed.
Lemma lem1714872 (x : real) (h1 : term740 x) : term233.
Proof. exact (proj2 (@lem1714870 x h1)). Qed.
Lemma lem1714875 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714876 : term233 = False.
Proof. exact (@lem1714875 term218 (NUMERAL 0)). Qed.
Lemma lem1714877 (x : real) (h1 : term740 x) : False.
Proof. exact (EQ_MP (@lem1714876) (@lem1714872 x h1)). Qed.
Lemma lem1714878 (x : real) (h1 : term578 x) : False.
Proof. exact (or_elim (@lem1714786 x h1) (fun h0 : term739 x => @lem1714864 x h0) (fun h0 : term740 x => @lem1714877 x h0)). Qed.
Lemma lem1714879 (x : real) (h1 : term576 x) : term576 x.
Proof. exact (h1). Qed.
Lemma lem1714880 (x : real) (h1 : term571 x) : term571 x.
Proof. exact (h1). Qed.
Lemma lem1714881 (x : real) (h1 : term741 x) : term741 x.
Proof. exact (h1). Qed.
Lemma lem1714882 (x : real) (h1 : term741 x) : term572 x.
Proof. exact (proj2 (@lem1714881 x h1)). Qed.
Lemma lem1714883 (x : real) (h1 : term741 x) : term273 x.
Proof. exact (proj1 (@lem1714881 x h1)). Qed.
Lemma lem1714884 (x : real) (h1 : term741 x) : term481 x.
Proof. exact (proj2 (@lem1714882 x h1)). Qed.
Lemma lem1714886 (x : real) (h1 : term741 x) : term448 x.
Proof. exact (proj2 (@lem1714884 x h1)). Qed.
Lemma lem1714889 (x : real) (h1 : term741 x) : term171 x.
Proof. exact (proj1 (@lem1714886 x h1)). Qed.
Lemma lem1714891 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714892 : term318 = term694.
Proof. exact (@lem1714891 (NUMERAL 0) term183). Qed.
Lemma lem1714893 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714894 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714895 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714894 h1) (fun h1 : term694 = True => @lem1714893)). Qed.
Lemma lem1714896 : term694 = True.
Proof. exact (EQ_MP (@lem1714895) (@lem1714893)). Qed.
Lemma lem1714897 : term318 = True.
Proof. exact (TRANS (@lem1714892) (@lem1714896)). Qed.
Lemma lem1714898 : True = term318.
Proof. exact (SYM (@lem1714897)). Qed.
Lemma lem1714899 : term318.
Proof. exact (EQ_MP (@lem1714898) (@lem0)). Qed.
Lemma lem1714900 (x : real) (h1 : term741 x) : term724 x.
Proof. exact (conj (@lem1714899) (@lem1714883 x h1)). Qed.
Lemma lem1714902 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1714903 (x : real) : term726 x.
Proof. exact (@lem1714902 term24 x). Qed.
Lemma lem1714904 (x : real) (h1 : term741 x) : term727 x.
Proof. exact (@lem1714903 x (@lem1714900 x h1)). Qed.
Lemma lem1714905 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1714906 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1714907 (x : real) : (term728 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1714906) (@lem1714905 x)). Qed.
Lemma lem1714908 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714909 (x : real) : (term727 x) = (term273 x).
Proof. exact (MK_COMB (@lem1714907 x) (@lem1714908)). Qed.
Lemma lem1714910 (x : real) (h1 : term741 x) : term273 x.
Proof. exact (EQ_MP (@lem1714909 x) (@lem1714904 x h1)). Qed.
Lemma lem1714912 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714913 : term318 = term694.
Proof. exact (@lem1714912 (NUMERAL 0) term183). Qed.
Lemma lem1714914 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1714915 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1714916 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1714915 h1) (fun h1 : term694 = True => @lem1714914)). Qed.
Lemma lem1714917 : term694 = True.
Proof. exact (EQ_MP (@lem1714916) (@lem1714914)). Qed.
Lemma lem1714918 : term318 = True.
Proof. exact (TRANS (@lem1714913) (@lem1714917)). Qed.
Lemma lem1714919 : True = term318.
Proof. exact (SYM (@lem1714918)). Qed.
Lemma lem1714920 : term318.
Proof. exact (EQ_MP (@lem1714919) (@lem0)). Qed.
Lemma lem1714921 (x : real) (h1 : term741 x) : term701 x.
Proof. exact (conj (@lem1714920) (@lem1714889 x h1)). Qed.
Lemma lem1714923 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1714924 (x : real) : term702 x.
Proof. exact (@lem1714923 term24 (term168 x)). Qed.
Lemma lem1714925 (x : real) (h1 : term741 x) : term703 x.
Proof. exact (@lem1714924 x (@lem1714921 x h1)). Qed.
Lemma lem1714926 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1714927 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714928 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1714927) (@lem1714926 x)). Qed.
Lemma lem1714929 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714930 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1714928 x) (@lem1714929)). Qed.
Lemma lem1714931 (x : real) (h1 : term741 x) : term171 x.
Proof. exact (EQ_MP (@lem1714930 x) (@lem1714925 x h1)). Qed.
Lemma lem1714932 (x : real) (h1 : term741 x) : term729 x.
Proof. exact (conj (@lem1714931 x h1) (@lem1714910 x h1)). Qed.
Lemma lem1714934 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1714935 (x : real) : term731 x.
Proof. exact (@lem1714934 (term168 x) x). Qed.
Lemma lem1714936 (x : real) (h1 : term741 x) : term709 x.
Proof. exact (@lem1714935 x (@lem1714932 x h1)). Qed.
Lemma lem1714937 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1714939 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1714940 : term713 = term75.
Proof. exact (@lem1714939 term183). Qed.
Lemma lem1714941 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1714942 : term714 = term715.
Proof. exact (MK_COMB (@lem1714941) (@lem1714940)). Qed.
Lemma lem1714943 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1714944 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1714942) (@lem1714943 x)). Qed.
Lemma lem1714945 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1714937 x) (@lem1714944 x)). Qed.
Lemma lem1714946 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1714947 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1714945 x) (@lem1714946 x)). Qed.
Lemma lem1714948 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1714949 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1714948) (@lem1714947 x)). Qed.
Lemma lem1714950 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1714951 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1714949 x) (@lem1714950)). Qed.
Lemma lem1714952 (x : real) (h1 : term741 x) : term264.
Proof. exact (EQ_MP (@lem1714951 x) (@lem1714936 x h1)). Qed.
Lemma lem1714954 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714955 : term264 = term718.
Proof. exact (@lem1714954 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1714956 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1714957 : term264 = False.
Proof. exact (TRANS (@lem1714955) (@lem1714956)). Qed.
Lemma lem1714958 (x : real) (h1 : term741 x) : False.
Proof. exact (EQ_MP (@lem1714957) (@lem1714952 x h1)). Qed.
Lemma lem1714959 (x : real) (h1 : term742 x) : term742 x.
Proof. exact (h1). Qed.
Lemma lem1714960 (x : real) (h1 : term742 x) : term573 x.
Proof. exact (proj2 (@lem1714959 x h1)). Qed.
Lemma lem1714962 (x : real) (h1 : term742 x) : term482 x.
Proof. exact (proj2 (@lem1714960 x h1)). Qed.
Lemma lem1714964 (x : real) (h1 : term742 x) : term449 x.
Proof. exact (proj2 (@lem1714962 x h1)). Qed.
Lemma lem1714966 (x : real) (h1 : term742 x) : term314.
Proof. exact (proj2 (@lem1714964 x h1)). Qed.
Lemma lem1714969 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714970 : term314 = False.
Proof. exact (@lem1714969 term183 (NUMERAL 0)). Qed.
Lemma lem1714971 (x : real) (h1 : term742 x) : False.
Proof. exact (EQ_MP (@lem1714970) (@lem1714966 x h1)). Qed.
Lemma lem1714972 (x : real) (h1 : term571 x) : False.
Proof. exact (or_elim (@lem1714880 x h1) (fun h0 : term741 x => @lem1714958 x h0) (fun h0 : term742 x => @lem1714971 x h0)). Qed.
Lemma lem1714973 (x : real) (h1 : term567 x) : term567 x.
Proof. exact (h1). Qed.
Lemma lem1714974 (x : real) (h1 : term743 x) : term743 x.
Proof. exact (h1). Qed.
Lemma lem1714975 (x : real) (h1 : term743 x) : term568 x.
Proof. exact (proj2 (@lem1714974 x h1)). Qed.
Lemma lem1714977 (x : real) (h1 : term743 x) : term516 x.
Proof. exact (proj2 (@lem1714975 x h1)). Qed.
Lemma lem1714979 (x : real) (h1 : term743 x) : term462 x.
Proof. exact (proj2 (@lem1714977 x h1)). Qed.
Lemma lem1714981 (x : real) (h1 : term743 x) : term314.
Proof. exact (proj2 (@lem1714979 x h1)). Qed.
Lemma lem1714984 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1714985 : term314 = False.
Proof. exact (@lem1714984 term183 (NUMERAL 0)). Qed.
Lemma lem1714986 (x : real) (h1 : term743 x) : False.
Proof. exact (EQ_MP (@lem1714985) (@lem1714981 x h1)). Qed.
Lemma lem1714987 (x : real) (h1 : term744 x) : term744 x.
Proof. exact (h1). Qed.
Lemma lem1714988 (x : real) (h1 : term744 x) : term569 x.
Proof. exact (proj2 (@lem1714987 x h1)). Qed.
Lemma lem1714990 (x : real) (h1 : term744 x) : term517 x.
Proof. exact (proj2 (@lem1714988 x h1)). Qed.
Lemma lem1714991 (x : real) (h1 : term744 x) : term192 x.
Proof. exact (proj1 (@lem1714988 x h1)). Qed.
Lemma lem1714993 (x : real) (h1 : term744 x) : term249 x.
Proof. exact (proj1 (@lem1714990 x h1)). Qed.
Lemma lem1714997 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1714998 : term318 = term694.
Proof. exact (@lem1714997 (NUMERAL 0) term183). Qed.
Lemma lem1714999 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715000 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715001 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715000 h1) (fun h1 : term694 = True => @lem1714999)). Qed.
Lemma lem1715002 : term694 = True.
Proof. exact (EQ_MP (@lem1715001) (@lem1714999)). Qed.
Lemma lem1715003 : term318 = True.
Proof. exact (TRANS (@lem1714998) (@lem1715002)). Qed.
Lemma lem1715004 : True = term318.
Proof. exact (SYM (@lem1715003)). Qed.
Lemma lem1715005 : term318.
Proof. exact (EQ_MP (@lem1715004) (@lem0)). Qed.
Lemma lem1715006 (x : real) (h1 : term744 x) : term745 x.
Proof. exact (conj (@lem1715005) (@lem1714993 x h1)). Qed.
Lemma lem1715008 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1715009 (x : real) : term746 x.
Proof. exact (@lem1715008 term24 (term168 x)). Qed.
Lemma lem1715010 (x : real) (h1 : term744 x) : term747 x.
Proof. exact (@lem1715009 x (@lem1715006 x h1)). Qed.
Lemma lem1715011 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1715012 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1715013 (x : real) : (term748 x) = (term248 x).
Proof. exact (MK_COMB (@lem1715012) (@lem1715011 x)). Qed.
Lemma lem1715014 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715015 (x : real) : (term747 x) = (term249 x).
Proof. exact (MK_COMB (@lem1715013 x) (@lem1715014)). Qed.
Lemma lem1715016 (x : real) (h1 : term744 x) : term249 x.
Proof. exact (EQ_MP (@lem1715015 x) (@lem1715010 x h1)). Qed.
Lemma lem1715018 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715019 : term318 = term694.
Proof. exact (@lem1715018 (NUMERAL 0) term183). Qed.
Lemma lem1715020 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715021 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715022 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715021 h1) (fun h1 : term694 = True => @lem1715020)). Qed.
Lemma lem1715023 : term694 = True.
Proof. exact (EQ_MP (@lem1715022) (@lem1715020)). Qed.
Lemma lem1715024 : term318 = True.
Proof. exact (TRANS (@lem1715019) (@lem1715023)). Qed.
Lemma lem1715025 : True = term318.
Proof. exact (SYM (@lem1715024)). Qed.
Lemma lem1715026 : term318.
Proof. exact (EQ_MP (@lem1715025) (@lem0)). Qed.
Lemma lem1715027 (x : real) (h1 : term744 x) : term696 x.
Proof. exact (conj (@lem1715026) (@lem1714991 x h1)). Qed.
Lemma lem1715029 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1715030 (x : real) : term698 x.
Proof. exact (@lem1715029 term24 x). Qed.
Lemma lem1715031 (x : real) (h1 : term744 x) : term699 x.
Proof. exact (@lem1715030 x (@lem1715027 x h1)). Qed.
Lemma lem1715032 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1715033 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715034 (x : real) : (term700 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1715033) (@lem1715032 x)). Qed.
Lemma lem1715035 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715036 (x : real) : (term699 x) = (term192 x).
Proof. exact (MK_COMB (@lem1715034 x) (@lem1715035)). Qed.
Lemma lem1715037 (x : real) (h1 : term744 x) : term192 x.
Proof. exact (EQ_MP (@lem1715036 x) (@lem1715031 x h1)). Qed.
Lemma lem1715038 (x : real) (h1 : term744 x) : term749 x.
Proof. exact (conj (@lem1715037 x h1) (@lem1715016 x h1)). Qed.
Lemma lem1715040 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1715041 (x : real) : term750 x.
Proof. exact (@lem1715040 x (term168 x)). Qed.
Lemma lem1715042 (x : real) (h1 : term744 x) : term751 x.
Proof. exact (@lem1715041 x (@lem1715038 x h1)). Qed.
Lemma lem1715043 (x : real) : (term752 x) = (term711 x).
Proof. exact (@lem1483442 term60 x). Qed.
Lemma lem1715045 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1715046 : term713 = term75.
Proof. exact (@lem1715045 term183). Qed.
Lemma lem1715047 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715048 : term714 = term715.
Proof. exact (MK_COMB (@lem1715047) (@lem1715046)). Qed.
Lemma lem1715049 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715050 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1715048) (@lem1715049 x)). Qed.
Lemma lem1715051 (x : real) : (term752 x) = (term716 x).
Proof. exact (TRANS (@lem1715043 x) (@lem1715050 x)). Qed.
Lemma lem1715052 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1715053 (x : real) : (term752 x) = term75.
Proof. exact (TRANS (@lem1715051 x) (@lem1715052 x)). Qed.
Lemma lem1715054 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715055 (x : real) : (term753 x) = term262.
Proof. exact (MK_COMB (@lem1715054) (@lem1715053 x)). Qed.
Lemma lem1715056 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715057 (x : real) : (term751 x) = term264.
Proof. exact (MK_COMB (@lem1715055 x) (@lem1715056)). Qed.
Lemma lem1715058 (x : real) (h1 : term744 x) : term264.
Proof. exact (EQ_MP (@lem1715057 x) (@lem1715042 x h1)). Qed.
Lemma lem1715060 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715061 : term264 = term718.
Proof. exact (@lem1715060 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1715062 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1715063 : term264 = False.
Proof. exact (TRANS (@lem1715061) (@lem1715062)). Qed.
Lemma lem1715064 (x : real) (h1 : term744 x) : False.
Proof. exact (EQ_MP (@lem1715063) (@lem1715058 x h1)). Qed.
Lemma lem1715065 (x : real) (h1 : term567 x) : False.
Proof. exact (or_elim (@lem1714973 x h1) (fun h0 : term743 x => @lem1714986 x h0) (fun h0 : term744 x => @lem1715064 x h0)). Qed.
Lemma lem1715066 (x : real) (h1 : term576 x) : False.
Proof. exact (or_elim (@lem1714879 x h1) (fun h0 : term571 x => @lem1714972 x h0) (fun h0 : term567 x => @lem1715065 x h0)). Qed.
Lemma lem1715067 (x : real) (h1 : term583 x) : False.
Proof. exact (or_elim (@lem1714785 x h1) (fun h0 : term578 x => @lem1714878 x h0) (fun h0 : term576 x => @lem1715066 x h0)). Qed.
Lemma lem1715068 (x : real) (h1 : term561 x) : term561 x.
Proof. exact (h1). Qed.
Lemma lem1715069 (x : real) (h1 : term558 x) : term558 x.
Proof. exact (h1). Qed.
Lemma lem1715070 (x : real) (h1 : term553 x) : term553 x.
Proof. exact (h1). Qed.
Lemma lem1715071 (x : real) (h1 : term754 x) : term754 x.
Proof. exact (h1). Qed.
Lemma lem1715072 (x : real) (h1 : term754 x) : term554 x.
Proof. exact (proj2 (@lem1715071 x h1)). Qed.
Lemma lem1715073 (x : real) (h1 : term754 x) : term273 x.
Proof. exact (proj1 (@lem1715071 x h1)). Qed.
Lemma lem1715074 (x : real) (h1 : term754 x) : term494 x.
Proof. exact (proj2 (@lem1715072 x h1)). Qed.
Lemma lem1715076 (x : real) (h1 : term754 x) : term465 x.
Proof. exact (proj2 (@lem1715074 x h1)). Qed.
Lemma lem1715079 (x : real) (h1 : term754 x) : term171 x.
Proof. exact (proj1 (@lem1715076 x h1)). Qed.
Lemma lem1715081 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715082 : term318 = term694.
Proof. exact (@lem1715081 (NUMERAL 0) term183). Qed.
Lemma lem1715083 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715084 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715085 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715084 h1) (fun h1 : term694 = True => @lem1715083)). Qed.
Lemma lem1715086 : term694 = True.
Proof. exact (EQ_MP (@lem1715085) (@lem1715083)). Qed.
Lemma lem1715087 : term318 = True.
Proof. exact (TRANS (@lem1715082) (@lem1715086)). Qed.
Lemma lem1715088 : True = term318.
Proof. exact (SYM (@lem1715087)). Qed.
Lemma lem1715089 : term318.
Proof. exact (EQ_MP (@lem1715088) (@lem0)). Qed.
Lemma lem1715090 (x : real) (h1 : term754 x) : term724 x.
Proof. exact (conj (@lem1715089) (@lem1715073 x h1)). Qed.
Lemma lem1715092 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1715093 (x : real) : term726 x.
Proof. exact (@lem1715092 term24 x). Qed.
Lemma lem1715094 (x : real) (h1 : term754 x) : term727 x.
Proof. exact (@lem1715093 x (@lem1715090 x h1)). Qed.
Lemma lem1715095 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1715096 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1715097 (x : real) : (term728 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1715096) (@lem1715095 x)). Qed.
Lemma lem1715098 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715099 (x : real) : (term727 x) = (term273 x).
Proof. exact (MK_COMB (@lem1715097 x) (@lem1715098)). Qed.
Lemma lem1715100 (x : real) (h1 : term754 x) : term273 x.
Proof. exact (EQ_MP (@lem1715099 x) (@lem1715094 x h1)). Qed.
Lemma lem1715102 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715103 : term318 = term694.
Proof. exact (@lem1715102 (NUMERAL 0) term183). Qed.
Lemma lem1715104 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715105 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715106 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715105 h1) (fun h1 : term694 = True => @lem1715104)). Qed.
Lemma lem1715107 : term694 = True.
Proof. exact (EQ_MP (@lem1715106) (@lem1715104)). Qed.
Lemma lem1715108 : term318 = True.
Proof. exact (TRANS (@lem1715103) (@lem1715107)). Qed.
Lemma lem1715109 : True = term318.
Proof. exact (SYM (@lem1715108)). Qed.
Lemma lem1715110 : term318.
Proof. exact (EQ_MP (@lem1715109) (@lem0)). Qed.
Lemma lem1715111 (x : real) (h1 : term754 x) : term701 x.
Proof. exact (conj (@lem1715110) (@lem1715079 x h1)). Qed.
Lemma lem1715113 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1715114 (x : real) : term702 x.
Proof. exact (@lem1715113 term24 (term168 x)). Qed.
Lemma lem1715115 (x : real) (h1 : term754 x) : term703 x.
Proof. exact (@lem1715114 x (@lem1715111 x h1)). Qed.
Lemma lem1715116 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1715117 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715118 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1715117) (@lem1715116 x)). Qed.
Lemma lem1715119 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715120 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1715118 x) (@lem1715119)). Qed.
Lemma lem1715121 (x : real) (h1 : term754 x) : term171 x.
Proof. exact (EQ_MP (@lem1715120 x) (@lem1715115 x h1)). Qed.
Lemma lem1715122 (x : real) (h1 : term754 x) : term729 x.
Proof. exact (conj (@lem1715121 x h1) (@lem1715100 x h1)). Qed.
Lemma lem1715124 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1715125 (x : real) : term731 x.
Proof. exact (@lem1715124 (term168 x) x). Qed.
Lemma lem1715126 (x : real) (h1 : term754 x) : term709 x.
Proof. exact (@lem1715125 x (@lem1715122 x h1)). Qed.
Lemma lem1715127 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1715129 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1715130 : term713 = term75.
Proof. exact (@lem1715129 term183). Qed.
Lemma lem1715131 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715132 : term714 = term715.
Proof. exact (MK_COMB (@lem1715131) (@lem1715130)). Qed.
Lemma lem1715133 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715134 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1715132) (@lem1715133 x)). Qed.
Lemma lem1715135 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1715127 x) (@lem1715134 x)). Qed.
Lemma lem1715136 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1715137 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1715135 x) (@lem1715136 x)). Qed.
Lemma lem1715138 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715139 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1715138) (@lem1715137 x)). Qed.
Lemma lem1715140 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715141 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1715139 x) (@lem1715140)). Qed.
Lemma lem1715142 (x : real) (h1 : term754 x) : term264.
Proof. exact (EQ_MP (@lem1715141 x) (@lem1715126 x h1)). Qed.
Lemma lem1715144 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715145 : term264 = term718.
Proof. exact (@lem1715144 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1715146 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1715147 : term264 = False.
Proof. exact (TRANS (@lem1715145) (@lem1715146)). Qed.
Lemma lem1715148 (x : real) (h1 : term754 x) : False.
Proof. exact (EQ_MP (@lem1715147) (@lem1715142 x h1)). Qed.
Lemma lem1715149 (x : real) (h1 : term755 x) : term755 x.
Proof. exact (h1). Qed.
Lemma lem1715150 (x : real) (h1 : term755 x) : term555 x.
Proof. exact (proj2 (@lem1715149 x h1)). Qed.
Lemma lem1715152 (x : real) (h1 : term755 x) : term495 x.
Proof. exact (proj2 (@lem1715150 x h1)). Qed.
Lemma lem1715154 (x : real) (h1 : term755 x) : term466 x.
Proof. exact (proj2 (@lem1715152 x h1)). Qed.
Lemma lem1715156 (x : real) (h1 : term755 x) : term233.
Proof. exact (proj2 (@lem1715154 x h1)). Qed.
Lemma lem1715159 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1715160 : term233 = False.
Proof. exact (@lem1715159 term218 (NUMERAL 0)). Qed.
Lemma lem1715161 (x : real) (h1 : term755 x) : False.
Proof. exact (EQ_MP (@lem1715160) (@lem1715156 x h1)). Qed.
Lemma lem1715162 (x : real) (h1 : term553 x) : False.
Proof. exact (or_elim (@lem1715070 x h1) (fun h0 : term754 x => @lem1715148 x h0) (fun h0 : term755 x => @lem1715161 x h0)). Qed.
Lemma lem1715163 (x : real) (h1 : term549 x) : term549 x.
Proof. exact (h1). Qed.
Lemma lem1715164 (x : real) (h1 : term756 x) : term756 x.
Proof. exact (h1). Qed.
Lemma lem1715165 (x : real) (h1 : term756 x) : term550 x.
Proof. exact (proj2 (@lem1715164 x h1)). Qed.
Lemma lem1715167 (x : real) (h1 : term756 x) : term490 x.
Proof. exact (proj2 (@lem1715165 x h1)). Qed.
Lemma lem1715168 (x : real) (h1 : term756 x) : term249 x.
Proof. exact (proj1 (@lem1715165 x h1)). Qed.
Lemma lem1715170 (x : real) (h1 : term756 x) : term192 x.
Proof. exact (proj1 (@lem1715167 x h1)). Qed.
Lemma lem1715174 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715175 : term318 = term694.
Proof. exact (@lem1715174 (NUMERAL 0) term183). Qed.
Lemma lem1715176 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715177 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715178 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715177 h1) (fun h1 : term694 = True => @lem1715176)). Qed.
Lemma lem1715179 : term694 = True.
Proof. exact (EQ_MP (@lem1715178) (@lem1715176)). Qed.
Lemma lem1715180 : term318 = True.
Proof. exact (TRANS (@lem1715175) (@lem1715179)). Qed.
Lemma lem1715181 : True = term318.
Proof. exact (SYM (@lem1715180)). Qed.
Lemma lem1715182 : term318.
Proof. exact (EQ_MP (@lem1715181) (@lem0)). Qed.
Lemma lem1715183 (x : real) (h1 : term756 x) : term745 x.
Proof. exact (conj (@lem1715182) (@lem1715168 x h1)). Qed.
Lemma lem1715185 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1715186 (x : real) : term746 x.
Proof. exact (@lem1715185 term24 (term168 x)). Qed.
Lemma lem1715187 (x : real) (h1 : term756 x) : term747 x.
Proof. exact (@lem1715186 x (@lem1715183 x h1)). Qed.
Lemma lem1715188 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1715189 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1715190 (x : real) : (term748 x) = (term248 x).
Proof. exact (MK_COMB (@lem1715189) (@lem1715188 x)). Qed.
Lemma lem1715191 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715192 (x : real) : (term747 x) = (term249 x).
Proof. exact (MK_COMB (@lem1715190 x) (@lem1715191)). Qed.
Lemma lem1715193 (x : real) (h1 : term756 x) : term249 x.
Proof. exact (EQ_MP (@lem1715192 x) (@lem1715187 x h1)). Qed.
Lemma lem1715195 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715196 : term318 = term694.
Proof. exact (@lem1715195 (NUMERAL 0) term183). Qed.
Lemma lem1715197 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715198 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715199 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715198 h1) (fun h1 : term694 = True => @lem1715197)). Qed.
Lemma lem1715200 : term694 = True.
Proof. exact (EQ_MP (@lem1715199) (@lem1715197)). Qed.
Lemma lem1715201 : term318 = True.
Proof. exact (TRANS (@lem1715196) (@lem1715200)). Qed.
Lemma lem1715202 : True = term318.
Proof. exact (SYM (@lem1715201)). Qed.
Lemma lem1715203 : term318.
Proof. exact (EQ_MP (@lem1715202) (@lem0)). Qed.
Lemma lem1715204 (x : real) (h1 : term756 x) : term696 x.
Proof. exact (conj (@lem1715203) (@lem1715170 x h1)). Qed.
Lemma lem1715206 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1715207 (x : real) : term698 x.
Proof. exact (@lem1715206 term24 x). Qed.
Lemma lem1715208 (x : real) (h1 : term756 x) : term699 x.
Proof. exact (@lem1715207 x (@lem1715204 x h1)). Qed.
Lemma lem1715209 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1715210 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715211 (x : real) : (term700 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1715210) (@lem1715209 x)). Qed.
Lemma lem1715212 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715213 (x : real) : (term699 x) = (term192 x).
Proof. exact (MK_COMB (@lem1715211 x) (@lem1715212)). Qed.
Lemma lem1715214 (x : real) (h1 : term756 x) : term192 x.
Proof. exact (EQ_MP (@lem1715213 x) (@lem1715208 x h1)). Qed.
Lemma lem1715215 (x : real) (h1 : term756 x) : term749 x.
Proof. exact (conj (@lem1715214 x h1) (@lem1715193 x h1)). Qed.
Lemma lem1715217 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1715218 (x : real) : term750 x.
Proof. exact (@lem1715217 x (term168 x)). Qed.
Lemma lem1715219 (x : real) (h1 : term756 x) : term751 x.
Proof. exact (@lem1715218 x (@lem1715215 x h1)). Qed.
Lemma lem1715220 (x : real) : (term752 x) = (term711 x).
Proof. exact (@lem1483442 term60 x). Qed.
Lemma lem1715222 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1715223 : term713 = term75.
Proof. exact (@lem1715222 term183). Qed.
Lemma lem1715224 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715225 : term714 = term715.
Proof. exact (MK_COMB (@lem1715224) (@lem1715223)). Qed.
Lemma lem1715226 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715227 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1715225) (@lem1715226 x)). Qed.
Lemma lem1715228 (x : real) : (term752 x) = (term716 x).
Proof. exact (TRANS (@lem1715220 x) (@lem1715227 x)). Qed.
Lemma lem1715229 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1715230 (x : real) : (term752 x) = term75.
Proof. exact (TRANS (@lem1715228 x) (@lem1715229 x)). Qed.
Lemma lem1715231 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715232 (x : real) : (term753 x) = term262.
Proof. exact (MK_COMB (@lem1715231) (@lem1715230 x)). Qed.
Lemma lem1715233 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715234 (x : real) : (term751 x) = term264.
Proof. exact (MK_COMB (@lem1715232 x) (@lem1715233)). Qed.
Lemma lem1715235 (x : real) (h1 : term756 x) : term264.
Proof. exact (EQ_MP (@lem1715234 x) (@lem1715219 x h1)). Qed.
Lemma lem1715237 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715238 : term264 = term718.
Proof. exact (@lem1715237 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1715239 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1715240 : term264 = False.
Proof. exact (TRANS (@lem1715238) (@lem1715239)). Qed.
Lemma lem1715241 (x : real) (h1 : term756 x) : False.
Proof. exact (EQ_MP (@lem1715240) (@lem1715235 x h1)). Qed.
Lemma lem1715242 (x : real) (h1 : term757 x) : term757 x.
Proof. exact (h1). Qed.
Lemma lem1715243 (x : real) (h1 : term757 x) : term551 x.
Proof. exact (proj2 (@lem1715242 x h1)). Qed.
Lemma lem1715245 (x : real) (h1 : term757 x) : term491 x.
Proof. exact (proj2 (@lem1715243 x h1)). Qed.
Lemma lem1715247 (x : real) (h1 : term757 x) : term462 x.
Proof. exact (proj2 (@lem1715245 x h1)). Qed.
Lemma lem1715249 (x : real) (h1 : term757 x) : term314.
Proof. exact (proj2 (@lem1715247 x h1)). Qed.
Lemma lem1715252 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1715253 : term314 = False.
Proof. exact (@lem1715252 term183 (NUMERAL 0)). Qed.
Lemma lem1715254 (x : real) (h1 : term757 x) : False.
Proof. exact (EQ_MP (@lem1715253) (@lem1715249 x h1)). Qed.
Lemma lem1715255 (x : real) (h1 : term549 x) : False.
Proof. exact (or_elim (@lem1715163 x h1) (fun h0 : term756 x => @lem1715241 x h0) (fun h0 : term757 x => @lem1715254 x h0)). Qed.
Lemma lem1715256 (x : real) (h1 : term558 x) : False.
Proof. exact (or_elim (@lem1715069 x h1) (fun h0 : term553 x => @lem1715162 x h0) (fun h0 : term549 x => @lem1715255 x h0)). Qed.
Lemma lem1715257 (x : real) (h1 : term545 x) : term545 x.
Proof. exact (h1). Qed.
Lemma lem1715258 (x : real) (h1 : term540 x) : term540 x.
Proof. exact (h1). Qed.
Lemma lem1715259 (x : real) (h1 : term758 x) : term758 x.
Proof. exact (h1). Qed.
Lemma lem1715260 (x : real) (h1 : term758 x) : term541 x.
Proof. exact (proj2 (@lem1715259 x h1)). Qed.
Lemma lem1715261 (x : real) (h1 : term758 x) : term273 x.
Proof. exact (proj1 (@lem1715259 x h1)). Qed.
Lemma lem1715262 (x : real) (h1 : term758 x) : term481 x.
Proof. exact (proj2 (@lem1715260 x h1)). Qed.
Lemma lem1715264 (x : real) (h1 : term758 x) : term448 x.
Proof. exact (proj2 (@lem1715262 x h1)). Qed.
Lemma lem1715267 (x : real) (h1 : term758 x) : term171 x.
Proof. exact (proj1 (@lem1715264 x h1)). Qed.
Lemma lem1715269 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715270 : term318 = term694.
Proof. exact (@lem1715269 (NUMERAL 0) term183). Qed.
Lemma lem1715271 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715272 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715273 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715272 h1) (fun h1 : term694 = True => @lem1715271)). Qed.
Lemma lem1715274 : term694 = True.
Proof. exact (EQ_MP (@lem1715273) (@lem1715271)). Qed.
Lemma lem1715275 : term318 = True.
Proof. exact (TRANS (@lem1715270) (@lem1715274)). Qed.
Lemma lem1715276 : True = term318.
Proof. exact (SYM (@lem1715275)). Qed.
Lemma lem1715277 : term318.
Proof. exact (EQ_MP (@lem1715276) (@lem0)). Qed.
Lemma lem1715278 (x : real) (h1 : term758 x) : term724 x.
Proof. exact (conj (@lem1715277) (@lem1715261 x h1)). Qed.
Lemma lem1715280 (x : real) (y : real) : term725 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1715281 (x : real) : term726 x.
Proof. exact (@lem1715280 term24 x). Qed.
Lemma lem1715282 (x : real) (h1 : term758 x) : term727 x.
Proof. exact (@lem1715281 x (@lem1715278 x h1)). Qed.
Lemma lem1715283 (x : real) : (term188 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1715284 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1715285 (x : real) : (term728 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1715284) (@lem1715283 x)). Qed.
Lemma lem1715286 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715287 (x : real) : (term727 x) = (term273 x).
Proof. exact (MK_COMB (@lem1715285 x) (@lem1715286)). Qed.
Lemma lem1715288 (x : real) (h1 : term758 x) : term273 x.
Proof. exact (EQ_MP (@lem1715287 x) (@lem1715282 x h1)). Qed.
Lemma lem1715290 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715291 : term318 = term694.
Proof. exact (@lem1715290 (NUMERAL 0) term183). Qed.
Lemma lem1715292 : term695 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1715293 (h1 : term695 = (BIT1 0)) : term694 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1715294 : (term695 = (BIT1 0)) = (term694 = True).
Proof. exact (prop_ext (fun h1 : term695 = (BIT1 0) => @lem1715293 h1) (fun h1 : term694 = True => @lem1715292)). Qed.
Lemma lem1715295 : term694 = True.
Proof. exact (EQ_MP (@lem1715294) (@lem1715292)). Qed.
Lemma lem1715296 : term318 = True.
Proof. exact (TRANS (@lem1715291) (@lem1715295)). Qed.
Lemma lem1715297 : True = term318.
Proof. exact (SYM (@lem1715296)). Qed.
Lemma lem1715298 : term318.
Proof. exact (EQ_MP (@lem1715297) (@lem0)). Qed.
Lemma lem1715299 (x : real) (h1 : term758 x) : term701 x.
Proof. exact (conj (@lem1715298) (@lem1715267 x h1)). Qed.
Lemma lem1715301 (x : real) (y : real) : term697 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1715302 (x : real) : term702 x.
Proof. exact (@lem1715301 term24 (term168 x)). Qed.
Lemma lem1715303 (x : real) (h1 : term758 x) : term703 x.
Proof. exact (@lem1715302 x (@lem1715299 x h1)). Qed.
Lemma lem1715304 (x : real) : (term704 x) = (term168 x).
Proof. exact (@lem1483460 (term168 x)). Qed.
Lemma lem1715305 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715306 (x : real) : (term705 x) = (term170 x).
Proof. exact (MK_COMB (@lem1715305) (@lem1715304 x)). Qed.
Lemma lem1715307 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715308 (x : real) : (term703 x) = (term171 x).
Proof. exact (MK_COMB (@lem1715306 x) (@lem1715307)). Qed.
Lemma lem1715309 (x : real) (h1 : term758 x) : term171 x.
Proof. exact (EQ_MP (@lem1715308 x) (@lem1715303 x h1)). Qed.
Lemma lem1715310 (x : real) (h1 : term758 x) : term729 x.
Proof. exact (conj (@lem1715309 x h1) (@lem1715288 x h1)). Qed.
Lemma lem1715312 (x : real) (y : real) : term730 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1715313 (x : real) : term731 x.
Proof. exact (@lem1715312 (term168 x) x). Qed.
Lemma lem1715314 (x : real) (h1 : term758 x) : term709 x.
Proof. exact (@lem1715313 x (@lem1715310 x h1)). Qed.
Lemma lem1715315 (x : real) : (term710 x) = (term711 x).
Proof. exact (@lem1483440 term60 x). Qed.
Lemma lem1715317 (m : nat) : (term712 m) = term75.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1715318 : term713 = term75.
Proof. exact (@lem1715317 term183). Qed.
Lemma lem1715319 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1715320 : term714 = term715.
Proof. exact (MK_COMB (@lem1715319) (@lem1715318)). Qed.
Lemma lem1715321 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1715322 (x : real) : (term711 x) = (term716 x).
Proof. exact (MK_COMB (@lem1715320) (@lem1715321 x)). Qed.
Lemma lem1715323 (x : real) : (term710 x) = (term716 x).
Proof. exact (TRANS (@lem1715315 x) (@lem1715322 x)). Qed.
Lemma lem1715324 (x : real) : (term716 x) = term75.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1715325 (x : real) : (term710 x) = term75.
Proof. exact (TRANS (@lem1715323 x) (@lem1715324 x)). Qed.
Lemma lem1715326 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1715327 (x : real) : (term717 x) = term262.
Proof. exact (MK_COMB (@lem1715326) (@lem1715325 x)). Qed.
Lemma lem1715328 : term75 = term75.
Proof. exact (eq_refl term75). Qed.
Lemma lem1715329 (x : real) : (term709 x) = term264.
Proof. exact (MK_COMB (@lem1715327 x) (@lem1715328)). Qed.
Lemma lem1715330 (x : real) (h1 : term758 x) : term264.
Proof. exact (EQ_MP (@lem1715329 x) (@lem1715314 x h1)). Qed.
Lemma lem1715332 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715333 : term264 = term718.
Proof. exact (@lem1715332 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1715334 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1715335 : term264 = False.
Proof. exact (TRANS (@lem1715333) (@lem1715334)). Qed.
Lemma lem1715336 (x : real) (h1 : term758 x) : False.
Proof. exact (EQ_MP (@lem1715335) (@lem1715330 x h1)). Qed.
Lemma lem1715337 (x : real) (h1 : term759 x) : term759 x.
Proof. exact (h1). Qed.
Lemma lem1715338 (x : real) (h1 : term759 x) : term542 x.
Proof. exact (proj2 (@lem1715337 x h1)). Qed.
Lemma lem1715340 (x : real) (h1 : term759 x) : term482 x.
Proof. exact (proj2 (@lem1715338 x h1)). Qed.
Lemma lem1715342 (x : real) (h1 : term759 x) : term449 x.
Proof. exact (proj2 (@lem1715340 x h1)). Qed.
Lemma lem1715344 (x : real) (h1 : term759 x) : term314.
Proof. exact (proj2 (@lem1715342 x h1)). Qed.
Lemma lem1715347 (m : nat) (n : nat) : (term720 m n) = False.
Proof. exact (proj1 (@lem1366270 m n)). Qed.
Lemma lem1715348 : term314 = False.
Proof. exact (@lem1715347 term183 (NUMERAL 0)). Qed.
Lemma lem1715349 (x : real) (h1 : term759 x) : False.
Proof. exact (EQ_MP (@lem1715348) (@lem1715344 x h1)). Qed.
Lemma lem1715350 (x : real) (h1 : term540 x) : False.
Proof. exact (or_elim (@lem1715258 x h1) (fun h0 : term758 x => @lem1715336 x h0) (fun h0 : term759 x => @lem1715349 x h0)). Qed.
Lemma lem1715351 (x : real) (h1 : term537 x) : term537 x.
Proof. exact (h1). Qed.
Lemma lem1715352 (x : real) (h1 : term760 x) : term760 x.
Proof. exact (h1). Qed.
Lemma lem1715353 (x : real) (h1 : term760 x) : term538 x.
Proof. exact (proj2 (@lem1715352 x h1)). Qed.
Lemma lem1715355 (x : real) (h1 : term760 x) : term478 x.
Proof. exact (proj2 (@lem1715353 x h1)). Qed.
Lemma lem1715357 (x : real) (h1 : term760 x) : term445 x.
Proof. exact (proj2 (@lem1715355 x h1)). Qed.
Lemma lem1715359 (x : real) (h1 : term760 x) : term264.
Proof. exact (proj2 (@lem1715357 x h1)). Qed.
Lemma lem1715362 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715363 : term264 = term718.
Proof. exact (@lem1715362 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1715364 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1715365 : term264 = False.
Proof. exact (TRANS (@lem1715363) (@lem1715364)). Qed.
Lemma lem1715366 (x : real) (h1 : term760 x) : False.
Proof. exact (EQ_MP (@lem1715365) (@lem1715359 x h1)). Qed.
Lemma lem1715367 (x : real) (h1 : term760 x) : term760 x.
Proof. exact (h1). Qed.
Lemma lem1715368 (x : real) (h1 : term760 x) : term538 x.
Proof. exact (proj2 (@lem1715367 x h1)). Qed.
Lemma lem1715370 (x : real) (h1 : term760 x) : term478 x.
Proof. exact (proj2 (@lem1715368 x h1)). Qed.
Lemma lem1715372 (x : real) (h1 : term760 x) : term445 x.
Proof. exact (proj2 (@lem1715370 x h1)). Qed.
Lemma lem1715374 (x : real) (h1 : term760 x) : term264.
Proof. exact (proj2 (@lem1715372 x h1)). Qed.
Lemma lem1715377 (n : nat) (m : nat) : (term693 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1715378 : term264 = term718.
Proof. exact (@lem1715377 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1715379 : term718 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1715380 : term264 = False.
Proof. exact (TRANS (@lem1715378) (@lem1715379)). Qed.
Lemma lem1715381 (x : real) (h1 : term760 x) : False.
Proof. exact (EQ_MP (@lem1715380) (@lem1715374 x h1)). Qed.
Lemma lem1715382 (x : real) (h1 : term537 x) : False.
Proof. exact (or_elim (@lem1715351 x h1) (fun h0 : term760 x => @lem1715366 x h0) (fun h0 : term760 x => @lem1715381 x h0)). Qed.
Lemma lem1715383 (x : real) (h1 : term545 x) : False.
Proof. exact (or_elim (@lem1715257 x h1) (fun h0 : term540 x => @lem1715350 x h0) (fun h0 : term537 x => @lem1715382 x h0)). Qed.
Lemma lem1715384 (x : real) (h1 : term561 x) : False.
Proof. exact (or_elim (@lem1715068 x h1) (fun h0 : term558 x => @lem1715256 x h0) (fun h0 : term545 x => @lem1715383 x h0)). Qed.
Lemma lem1715385 (x : real) (h1 : term586 x) : False.
Proof. exact (or_elim (@lem1714784 x h1) (fun h0 : term583 x => @lem1715067 x h0) (fun h0 : term561 x => @lem1715384 x h0)). Qed.
Lemma lem1715386 (x : real) (h1 : term689 x) : False.
Proof. exact (or_elim (@lem1714242 x h1) (fun h0 : term687 x => @lem1714783 x h0) (fun h0 : term586 x => @lem1715385 x h0)). Qed.
Lemma lem1715388 (x : real) (h1 : term689 x) : term689 x.
Proof. exact (h1). Qed.
Lemma lem1715389 (x : real) (h1 : term689 x) : (term689 x) = False.
Proof. exact (prop_ext (fun h2 : term689 x => @lem1715386 x h1) (fun h2 : False => @lem1715388 x h1)). Qed.
Lemma lem1715390 (x : real) (h1 : term689 x) : False.
Proof. exact (EQ_MP (@lem1715389 x h1) (@lem1715388 x h1)). Qed.
Lemma lem1715391 (h1 : term691) : term691.
Proof. exact (h1). Qed.
Lemma lem1715392 (h1 : term691) : False.
Proof. exact (ex_elim (@lem1715391 h1) (fun x : real => fun h0 : term690 x => @lem1715390 x h0)). Qed.
Lemma lem1715393 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem1715394 (h1 : term14) : term691.
Proof. exact (EQ_MP (@lem1714076) (@lem1715393 h1)). Qed.
Lemma lem1715395 (h1 : term14) : term691 = False.
Proof. exact (prop_ext (fun h2 : term691 => @lem1715392 h2) (fun h2 : False => @lem1715394 h1)). Qed.
Lemma lem1715396 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem1715395 h1) (@lem1715394 h1)). Qed.
Lemma lem1715397 : term761.
Proof. exact (fun h0 : term14 => @lem1715396 h0). Qed.
Lemma lem1715398 : term762.
Proof. exact (@lem1386578 term11). Qed.
Lemma lem1715399 : term11.
Proof. exact (@lem1715398 (@lem1715397)). Qed.
Lemma lem1715400 : term10.
Proof. exact (EQ_MP (@lem1710452) (@lem1715399)). Qed.
