Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ADD_RDISTRIB_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338712_spec.
Require Import thm1339188_spec.
Require Import thm16474_spec.
Require Import thm18392_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1486352 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1486353 : term1 = term2.
Proof. exact (@lem1486352 term1). Qed.
Lemma lem1486354 : term2 = term1.
Proof. exact (SYM (@lem1486353)). Qed.
Lemma lem1486355 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1486358 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1486359 : term5.
Proof. exact (fun h0 : term4 => @lem1486358 h0). Qed.
Lemma lem1486360 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1486361 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1486362 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1486360 h2 (@lem1486361 h1)). Qed.
Lemma lem1486363 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1486362 h1 h0). Qed.
Lemma lem1486364 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1486365 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1486363 h1 (@lem1486364 h2)). Qed.
Lemma lem1486366 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1486365 h0 h1). Qed.
Lemma lem1486367 : term7.
Proof. exact (fun h0 : term5 => @lem1486366 h0). Qed.
Lemma lem1486370 : term5.
Proof. exact (@lem1486367 (@lem1486359)). Qed.
Lemma lem1486400 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1486401 : term8 = term9.
Proof. exact (@lem1486400 term10). Qed.
Lemma lem1486410 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1486411 : term12 = term13.
Proof. exact (MK_COMB (@lem1486410) (@lem1486401)). Qed.
Lemma lem1486414 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1486421 : term4 = term15.
Proof. exact (MK_COMB (@lem1486414) (@lem1486411)). Qed.
Lemma lem1486422 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1486423 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1486422 y x)). Qed.
Lemma lem1486424 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486425 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1486424) (@lem1486423 x)). Qed.
Lemma lem1486426 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1486425 x)). Qed.
Lemma lem1486427 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486428 : term10 = term10.
Proof. exact (MK_COMB (@lem1486427) (@lem1486426)). Qed.
Lemma lem1486429 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1486430 : term9 = term9.
Proof. exact (MK_COMB (@lem1486429) (@lem1486428)). Qed.
Lemma lem1486431 (y : real) (x : real) (z : real) : ((term19 x y z) = (term20 y x z)) = ((term19 x y z) = (term20 y x z)).
Proof. exact (eq_refl ((term19 x y z) = (term20 y x z))). Qed.
Lemma lem1486432 (y : real) (x : real) : (term21 y x) = (term21 y x).
Proof. exact (fun_ext (fun z : real => @lem1486431 y x z)). Qed.
Lemma lem1486433 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486434 (y : real) (x : real) : (term22 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1486433) (@lem1486432 y x)). Qed.
Lemma lem1486435 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1486434 y x)). Qed.
Lemma lem1486436 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486437 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1486436) (@lem1486435 x)). Qed.
Lemma lem1486438 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1486437 x)). Qed.
Lemma lem1486439 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486440 : term26 = term26.
Proof. exact (MK_COMB (@lem1486439) (@lem1486438)). Qed.
Lemma lem1486441 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1486442 : term11 = term11.
Proof. exact (MK_COMB (@lem1486441) (@lem1486440)). Qed.
Lemma lem1486443 : term13 = term13.
Proof. exact (MK_COMB (@lem1486442) (@lem1486430)). Qed.
Lemma lem1486444 (x : real) (y : real) (z : real) : ((term27 x y z) = (term28 x y z)) = ((term27 x y z) = (term28 x y z)).
Proof. exact (eq_refl ((term27 x y z) = (term28 x y z))). Qed.
Lemma lem1486445 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (fun_ext (fun z : real => @lem1486444 x y z)). Qed.
Lemma lem1486446 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486447 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1486446) (@lem1486445 x y)). Qed.
Lemma lem1486448 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1486447 x y)). Qed.
Lemma lem1486449 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486450 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1486449) (@lem1486448 x)). Qed.
Lemma lem1486451 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1486450 x)). Qed.
Lemma lem1486452 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486453 : term1 = term1.
Proof. exact (MK_COMB (@lem1486452) (@lem1486451)). Qed.
Lemma lem1486454 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1486455 : term3 = term3.
Proof. exact (MK_COMB (@lem1486454) (@lem1486453)). Qed.
Lemma lem1486456 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1486457 : term14 = term14.
Proof. exact (MK_COMB (@lem1486456) (@lem1486455)). Qed.
Lemma lem1486458 : term15 = term15.
Proof. exact (MK_COMB (@lem1486457) (@lem1486443)). Qed.
Lemma lem1486513 : term4 = term15.
Proof. exact (TRANS (@lem1486421) (@lem1486458)). Qed.
Lemma lem1486514 : term15 = term4.
Proof. exact (SYM (@lem1486513)). Qed.
Lemma lem1486515 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1486516 (h1 : term26) : term26.
Proof. exact (h1). Qed.
Lemma lem1486517 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1486519 (P : real -> Prop) : (term34 P) = (term35 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1486520 (x : real) (y : real) : (term36 x y) = (term37 x y).
Proof. exact (@lem1486519 (term29 x y)). Qed.
Lemma lem1486521 (x : real) (y : real) (z : real) : (term38 x y z) = ((term27 x y z) = (term28 x y z)).
Proof. exact (eq_refl (term38 x y z)). Qed.
Lemma lem1486522 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1486524 (x : real) (y : real) (z : real) : (term39 x y z) = (term40 x y z).
Proof. exact (MK_COMB (@lem1486522) (@lem1486521 x y z)). Qed.
Lemma lem1486525 (x : real) (y : real) : (term41 x y) = (term42 x y).
Proof. exact (fun_ext (fun z : real => @lem1486524 x y z)). Qed.
Lemma lem1486526 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1486527 (x : real) (y : real) : (term37 x y) = (term43 x y).
Proof. exact (MK_COMB (@lem1486526) (@lem1486525 x y)). Qed.
Lemma lem1486528 (x : real) (y : real) : (term36 x y) = (term43 x y).
Proof. exact (TRANS (@lem1486520 x y) (@lem1486527 x y)). Qed.
Lemma lem1486529 (P : real -> Prop) : (term34 P) = (term35 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1486530 (x : real) : (term44 x) = (term45 x).
Proof. exact (@lem1486529 (term31 x)). Qed.
Lemma lem1486531 (x : real) (y : real) : (term46 x y) = (term30 x y).
Proof. exact (eq_refl (term46 x y)). Qed.
Lemma lem1486532 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1486533 (x : real) (y : real) : (term47 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1486532) (@lem1486531 x y)). Qed.
Lemma lem1486534 (x : real) (y : real) : (term47 x y) = (term43 x y).
Proof. exact (TRANS (@lem1486533 x y) (@lem1486528 x y)). Qed.
Lemma lem1486535 (x : real) : (term48 x) = (term49 x).
Proof. exact (fun_ext (fun y : real => @lem1486534 x y)). Qed.
Lemma lem1486536 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1486537 (x : real) : (term45 x) = (term50 x).
Proof. exact (MK_COMB (@lem1486536) (@lem1486535 x)). Qed.
Lemma lem1486538 (x : real) : (term44 x) = (term50 x).
Proof. exact (TRANS (@lem1486530 x) (@lem1486537 x)). Qed.
Lemma lem1486539 (P : real -> Prop) : (term34 P) = (term35 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1486540 : term3 = term51.
Proof. exact (@lem1486539 term33). Qed.
Lemma lem1486541 (x : real) : (term52 x) = (term32 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1486542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1486543 (x : real) : (term53 x) = (term44 x).
Proof. exact (MK_COMB (@lem1486542) (@lem1486541 x)). Qed.
Lemma lem1486544 (x : real) : (term53 x) = (term50 x).
Proof. exact (TRANS (@lem1486543 x) (@lem1486538 x)). Qed.
Lemma lem1486545 : term54 = term55.
Proof. exact (fun_ext (fun x : real => @lem1486544 x)). Qed.
Lemma lem1486546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1486547 : term51 = term56.
Proof. exact (MK_COMB (@lem1486546) (@lem1486545)). Qed.
Lemma lem1486564 : term3 = term56.
Proof. exact (TRANS (@lem1486540) (@lem1486547)). Qed.
Lemma lem1486565 (h1 : term3) : term56.
Proof. exact (EQ_MP (@lem1486564) (@lem1486515 h1)). Qed.
Lemma lem1486566 (y : real) (x : real) (z : real) : ((term19 x y z) = (term20 y x z)) = ((term19 x y z) = (term20 y x z)).
Proof. exact (eq_refl ((term19 x y z) = (term20 y x z))). Qed.
Lemma lem1486567 (y : real) (x : real) : (term21 y x) = (term21 y x).
Proof. exact (fun_ext (fun z : real => @lem1486566 y x z)). Qed.
Lemma lem1486568 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486569 (y : real) (x : real) : (term22 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1486568) (@lem1486567 y x)). Qed.
Lemma lem1486570 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1486569 y x)). Qed.
Lemma lem1486571 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486572 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1486571) (@lem1486570 x)). Qed.
Lemma lem1486573 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1486572 x)). Qed.
Lemma lem1486574 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486591 : term26 = term26.
Proof. exact (MK_COMB (@lem1486574) (@lem1486573)). Qed.
Lemma lem1486592 (h1 : term26) : term26.
Proof. exact (EQ_MP (@lem1486591) (@lem1486516 h1)). Qed.
Lemma lem1486593 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1486594 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1486593 y x)). Qed.
Lemma lem1486595 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486596 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1486595) (@lem1486594 x)). Qed.
Lemma lem1486597 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1486596 x)). Qed.
Lemma lem1486598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486611 : term10 = term10.
Proof. exact (MK_COMB (@lem1486598) (@lem1486597)). Qed.
Lemma lem1486612 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1486611) (@lem1486517 h1)). Qed.
Lemma lem1486613 (x : real) (h1 : term50 x) : term50 x.
Proof. exact (h1). Qed.
Lemma lem1486614 (x : real) (y : real) (h1 : term43 x y) : term43 x y.
Proof. exact (h1). Qed.
Lemma lem1486640 (y : real) (x : real) (z : real) : ((term19 x y z) = (term20 y x z)) = ((term19 x y z) = (term20 y x z)).
Proof. exact (eq_refl ((term19 x y z) = (term20 y x z))). Qed.
Lemma lem1486641 (y : real) (x : real) : (term21 y x) = (term21 y x).
Proof. exact (fun_ext (fun z : real => @lem1486640 y x z)). Qed.
Lemma lem1486642 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486643 (y : real) (x : real) : (term22 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1486642) (@lem1486641 y x)). Qed.
Lemma lem1486644 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1486643 y x)). Qed.
Lemma lem1486645 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486646 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1486645) (@lem1486644 x)). Qed.
Lemma lem1486647 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1486646 x)). Qed.
Lemma lem1486648 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486649 : term26 = term26.
Proof. exact (MK_COMB (@lem1486648) (@lem1486647)). Qed.
Lemma lem1486650 (h1 : term26) : term26.
Proof. exact (EQ_MP (@lem1486649) (@lem1486592 h1)). Qed.
Lemma lem1486663 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1486664 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1486663 y x)). Qed.
Lemma lem1486665 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486666 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1486665) (@lem1486664 x)). Qed.
Lemma lem1486667 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1486666 x)). Qed.
Lemma lem1486668 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486669 : term10 = term10.
Proof. exact (MK_COMB (@lem1486668) (@lem1486667)). Qed.
Lemma lem1486670 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1486669) (@lem1486612 h1)). Qed.
Lemma lem1486698 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term40 x y z.
Proof. exact (h1). Qed.
Lemma lem1486700 (y : real) (x : real) (z : real) : ((term19 x y z) = (term20 y x z)) = ((term19 x y z) = (term20 y x z)).
Proof. exact (eq_refl ((term19 x y z) = (term20 y x z))). Qed.
Lemma lem1486701 (y : real) (x : real) : (term21 y x) = (term21 y x).
Proof. exact (fun_ext (fun z : real => @lem1486700 y x z)). Qed.
Lemma lem1486702 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486703 (y : real) (x : real) : (term22 y x) = (term22 y x).
Proof. exact (MK_COMB (@lem1486702) (@lem1486701 y x)). Qed.
Lemma lem1486704 (x : real) : (term23 x) = (term23 x).
Proof. exact (fun_ext (fun y : real => @lem1486703 y x)). Qed.
Lemma lem1486705 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486706 (x : real) : (term24 x) = (term24 x).
Proof. exact (MK_COMB (@lem1486705) (@lem1486704 x)). Qed.
Lemma lem1486707 : term25 = term25.
Proof. exact (fun_ext (fun x : real => @lem1486706 x)). Qed.
Lemma lem1486708 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486710 : term26 = term26.
Proof. exact (MK_COMB (@lem1486708) (@lem1486707)). Qed.
Lemma lem1486711 (h1 : term26) : term26.
Proof. exact (EQ_MP (@lem1486710) (@lem1486650 h1)). Qed.
Lemma lem1486713 (y : real) (x : real) : ((real_mul x y) = (real_mul y x)) = ((real_mul x y) = (real_mul y x)).
Proof. exact (eq_refl ((real_mul x y) = (real_mul y x))). Qed.
Lemma lem1486714 (x : real) : (term16 x) = (term16 x).
Proof. exact (fun_ext (fun y : real => @lem1486713 y x)). Qed.
Lemma lem1486715 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486716 (x : real) : (term17 x) = (term17 x).
Proof. exact (MK_COMB (@lem1486715) (@lem1486714 x)). Qed.
Lemma lem1486717 : term18 = term18.
Proof. exact (fun_ext (fun x : real => @lem1486716 x)). Qed.
Lemma lem1486718 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1486720 : term10 = term10.
Proof. exact (MK_COMB (@lem1486718) (@lem1486717)). Qed.
Lemma lem1486721 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1486720) (@lem1486670 h1)). Qed.
Lemma lem1486725 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term40 x y z.
Proof. exact (h1). Qed.
Lemma lem1486726 (_24830 : real) (h1 : term26) : term57 _24830.
Proof. exact (@lem1486711 h1 _24830). Qed.
Lemma lem1486727 (_24830 : real) : (term57 _24830) = (term24 _24830).
Proof. exact (eq_refl (term57 _24830)). Qed.
Lemma lem1486728 (_24830 : real) (h1 : term26) : term24 _24830.
Proof. exact (EQ_MP (@lem1486727 _24830) (@lem1486726 _24830 h1)). Qed.
Lemma lem1486729 (_24830 : real) (_24831 : real) (h1 : term26) : term58 _24830 _24831.
Proof. exact (@lem1486728 _24830 h1 _24831). Qed.
Lemma lem1486730 (_24831 : real) (_24830 : real) : (term58 _24830 _24831) = (term22 _24831 _24830).
Proof. exact (eq_refl (term58 _24830 _24831)). Qed.
Lemma lem1486731 (_24831 : real) (_24830 : real) (h1 : term26) : term22 _24831 _24830.
Proof. exact (EQ_MP (@lem1486730 _24831 _24830) (@lem1486729 _24830 _24831 h1)). Qed.
Lemma lem1486732 (_24831 : real) (_24830 : real) (_24832 : real) (h1 : term26) : term59 _24831 _24830 _24832.
Proof. exact (@lem1486731 _24831 _24830 h1 _24832). Qed.
Lemma lem1486733 (_24831 : real) (_24830 : real) (_24832 : real) : (term59 _24831 _24830 _24832) = ((term19 _24830 _24831 _24832) = (term20 _24831 _24830 _24832)).
Proof. exact (eq_refl (term59 _24831 _24830 _24832)). Qed.
Lemma lem1486735 (_24833 : real) (h1 : term10) : term60 _24833.
Proof. exact (@lem1486721 h1 _24833). Qed.
Lemma lem1486736 (_24833 : real) : (term60 _24833) = (term17 _24833).
Proof. exact (eq_refl (term60 _24833)). Qed.
Lemma lem1486737 (_24833 : real) (h1 : term10) : term17 _24833.
Proof. exact (EQ_MP (@lem1486736 _24833) (@lem1486735 _24833 h1)). Qed.
Lemma lem1486738 (_24833 : real) (_24834 : real) (h1 : term10) : term61 _24833 _24834.
Proof. exact (@lem1486737 _24833 h1 _24834). Qed.
Lemma lem1486739 (_24834 : real) (_24833 : real) : (term61 _24833 _24834) = ((real_mul _24833 _24834) = (real_mul _24834 _24833)).
Proof. exact (eq_refl (term61 _24833 _24834)). Qed.
Lemma lem1486746 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term40 x y z.
Proof. exact (h1). Qed.
Lemma lem1486762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1486763 (_24839 : real) (_24841 : real) (h1 : _24839 = _24841) : _24839 = _24841.
Proof. exact (h1). Qed.
Lemma lem1486764 (_24840 : real) (_24842 : real) (h1 : _24840 = _24842) : _24840 = _24842.
Proof. exact (h1). Qed.
Lemma lem1486765 (_24839 : real) (_24841 : real) (h1 : _24839 = _24841) : (real_add _24839) = (real_add _24841).
Proof. exact (MK_COMB (@lem1486762) (@lem1486763 _24839 _24841 h1)). Qed.
Lemma lem1486766 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) (h1 : _24839 = _24841) (h2 : _24840 = _24842) : (real_add _24839 _24840) = (real_add _24841 _24842).
Proof. exact (MK_COMB (@lem1486765 _24839 _24841 h1) (@lem1486764 _24840 _24842 h2)). Qed.
Lemma lem1486767 (_24840 : real) (_24842 : real) (_24839 : real) (_24841 : real) (h1 : _24839 = _24841) : term62 _24839 _24840 _24841 _24842.
Proof. exact (fun h0 : _24840 = _24842 => @lem1486766 _24839 _24841 _24840 _24842 h1 h0). Qed.
Lemma lem1486769 (a : Prop) (b : Prop) : (a -> b) = (term63 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1486770 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : (term62 _24839 _24840 _24841 _24842) = (term64 _24839 _24840 _24841 _24842).
Proof. exact (@lem1486769 (_24840 = _24842) ((real_add _24839 _24840) = (real_add _24841 _24842))). Qed.
Lemma lem1486771 (_24840 : real) (_24842 : real) (_24839 : real) (_24841 : real) (h1 : _24839 = _24841) : term64 _24839 _24840 _24841 _24842.
Proof. exact (EQ_MP (@lem1486770 _24839 _24840 _24841 _24842) (@lem1486767 _24840 _24842 _24839 _24841 h1)). Qed.
Lemma lem1486772 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : term65 _24839 _24840 _24841 _24842.
Proof. exact (fun h0 : _24839 = _24841 => @lem1486771 _24840 _24842 _24839 _24841 h0). Qed.
Lemma lem1486774 (a : Prop) (b : Prop) : (a -> b) = (term63 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1486775 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : (term65 _24839 _24840 _24841 _24842) = (term66 _24839 _24840 _24841 _24842).
Proof. exact (@lem1486774 (_24839 = _24841) (term64 _24839 _24840 _24841 _24842)). Qed.
Lemma lem1486776 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : term66 _24839 _24840 _24841 _24842.
Proof. exact (EQ_MP (@lem1486775 _24839 _24840 _24841 _24842) (@lem1486772 _24839 _24840 _24841 _24842)). Qed.
Lemma lem1486778 (x : real) (y : real) (z : real) : term67 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1486780 (_24831 : real) (_24830 : real) (_24832 : real) (h1 : term26) : (term19 _24830 _24831 _24832) = (term20 _24831 _24830 _24832).
Proof. exact (EQ_MP (@lem1486733 _24831 _24830 _24832) (@lem1486732 _24831 _24830 _24832 h1)). Qed.
Lemma lem1486781 (x : real) (z : real) (y : real) (h1 : term26) : (term19 z x y) = (term20 x z y).
Proof. exact (@lem1486780 x z y h1). Qed.
Lemma lem1486782 (x : real) (z : real) (y : real) (h1 : term26) : term68 x z y.
Proof. exact (fun h0 : term69 x z y => @lem1486781 x z y h1). Qed.
Lemma lem1486784 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1486785 (x : real) (z : real) (y : real) : (term68 x z y) = ((term19 z x y) = (term20 x z y)).
Proof. exact (@lem1486784 ((term19 z x y) = (term20 x z y))). Qed.
Lemma lem1486786 (x : real) (z : real) (y : real) (h1 : term26) : (term19 z x y) = (term20 x z y).
Proof. exact (EQ_MP (@lem1486785 x z y) (@lem1486782 x z y h1)). Qed.
Lemma lem1486788 (_24834 : real) (_24833 : real) (h1 : term10) : (real_mul _24833 _24834) = (real_mul _24834 _24833).
Proof. exact (EQ_MP (@lem1486739 _24834 _24833) (@lem1486738 _24833 _24834 h1)). Qed.
Lemma lem1486789 (x : real) (y : real) (z : real) (h1 : term10) : (term19 z x y) = (term27 x y z).
Proof. exact (@lem1486788 (real_add x y) z h1). Qed.
Lemma lem1486790 (x : real) (y : real) (z : real) (h1 : term10) : term71 x y z.
Proof. exact (fun h0 : term72 x y z => @lem1486789 x y z h1). Qed.
Lemma lem1486792 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1486793 (x : real) (y : real) (z : real) : (term71 x y z) = ((term19 z x y) = (term27 x y z)).
Proof. exact (@lem1486792 ((term19 z x y) = (term27 x y z))). Qed.
Lemma lem1486794 (x : real) (y : real) (z : real) (h1 : term10) : (term19 z x y) = (term27 x y z).
Proof. exact (EQ_MP (@lem1486793 x y z) (@lem1486790 x y z h1)). Qed.
Lemma lem1486812 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1486813 (y : real) (x : real) (z : real) : (term73 x y z) = (term74 y x z).
Proof. exact (@lem1486812 (y = z) (term75 x z)). Qed.
Lemma lem1486823 (x : real) (y : real) : (term76 x y) = (term76 x y).
Proof. exact (eq_refl (term76 x y)). Qed.
Lemma lem1486824 (y : real) (x : real) (z : real) : (term67 x y z) = (term77 y x z).
Proof. exact (MK_COMB (@lem1486823 x y) (@lem1486813 y x z)). Qed.
Lemma lem1486828 (q : Prop) (p : Prop) (r : Prop) : (term78 p q r) = (term78 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1486829 (y : real) (x : real) (z : real) : (term77 y x z) = (term79 y x z).
Proof. exact (@lem1486828 (y = z) (term75 x y) (term75 x z)). Qed.
Lemma lem1486851 (y : real) (x : real) (z : real) : (term67 x y z) = (term79 y x z).
Proof. exact (TRANS (@lem1486824 y x z) (@lem1486829 y x z)). Qed.
Lemma lem1486852 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1486853 (y : real) (x : real) (z : real) : (term80 x y z) = (term81 y x z).
Proof. exact (MK_COMB (@lem1486852) (@lem1486851 y x z)). Qed.
Lemma lem1486875 (y : real) (x : real) (z : real) : (term79 y x z) = (term79 y x z).
Proof. exact (eq_refl (term79 y x z)). Qed.
Lemma lem1486876 (y : real) (x : real) (z : real) : ((term67 x y z) = (term79 y x z)) = ((term79 y x z) = (term79 y x z)).
Proof. exact (MK_COMB (@lem1486853 y x z) (@lem1486875 y x z)). Qed.
Lemma lem1486878 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1486879 (x : Prop) : (x = x) = True.
Proof. exact (@lem1486878 Prop x). Qed.
Lemma lem1486880 (y : real) (x : real) (z : real) : ((term79 y x z) = (term79 y x z)) = True.
Proof. exact (@lem1486879 (term79 y x z)). Qed.
Lemma lem1486881 (y : real) (x : real) (z : real) : ((term67 x y z) = (term79 y x z)) = True.
Proof. exact (TRANS (@lem1486876 y x z) (@lem1486880 y x z)). Qed.
Lemma lem1486882 (y : real) (x : real) (z : real) : True = ((term67 x y z) = (term79 y x z)).
Proof. exact (SYM (@lem1486881 y x z)). Qed.
Lemma lem1486883 (y : real) (x : real) (z : real) : (term67 x y z) = (term79 y x z).
Proof. exact (EQ_MP (@lem1486882 y x z) (@lem0)). Qed.
Lemma lem1486884 (y : real) (x : real) (z : real) : term79 y x z.
Proof. exact (EQ_MP (@lem1486883 y x z) (@lem1486778 x y z)). Qed.
Lemma lem1486886 (b : Prop) (a : Prop) : (a \/ b) = (term82 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1486887 (x : real) (y : real) (z : real) : (term79 y x z) = (term83 x y z).
Proof. exact (@lem1486886 (term84 y x z) (y = z)). Qed.
Lemma lem1486889 (a : Prop) (b : Prop) : (term85 a b) = (term86 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1486890 (y : real) (x : real) (z : real) : (term87 y x z) = (term88 y x z).
Proof. exact (@lem1486889 (term75 x y) (term75 x z)). Qed.
Lemma lem1486892 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1486893 (x : real) (y : real) : (term90 x y) = (x = y).
Proof. exact (@lem1486892 (x = y)). Qed.
Lemma lem1486894 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1486895 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1486894) (@lem1486893 x y)). Qed.
Lemma lem1486897 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1486898 (x : real) (z : real) : (term90 x z) = (x = z).
Proof. exact (@lem1486897 (x = z)). Qed.
Lemma lem1486899 (y : real) (x : real) (z : real) : (term88 y x z) = (term93 y x z).
Proof. exact (MK_COMB (@lem1486895 x y) (@lem1486898 x z)). Qed.
Lemma lem1486900 (y : real) (x : real) (z : real) : (term87 y x z) = (term93 y x z).
Proof. exact (TRANS (@lem1486890 y x z) (@lem1486899 y x z)). Qed.
Lemma lem1486901 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1486902 (y : real) (x : real) (z : real) : (term94 y x z) = (term95 y x z).
Proof. exact (MK_COMB (@lem1486901) (@lem1486900 y x z)). Qed.
Lemma lem1486903 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1486904 (x : real) (y : real) (z : real) : (term83 x y z) = (term96 x y z).
Proof. exact (MK_COMB (@lem1486902 y x z) (@lem1486903 y z)). Qed.
Lemma lem1486905 (x : real) (y : real) (z : real) : (term79 y x z) = (term96 x y z).
Proof. exact (TRANS (@lem1486887 x y z) (@lem1486904 x y z)). Qed.
Lemma lem1486907 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : term97 x y z.
Proof. exact (conj (@lem1486786 x z y h1) (@lem1486794 x y z h2)). Qed.
Lemma lem1486909 (x : real) (y : real) (z : real) : term96 x y z.
Proof. exact (EQ_MP (@lem1486905 x y z) (@lem1486884 y x z)). Qed.
Lemma lem1486910 (x : real) (y : real) (z : real) : term98 x y z.
Proof. exact (@lem1486909 (term19 z x y) (term20 x z y) (term27 x y z)). Qed.
Lemma lem1486913 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : (term20 x z y) = (term27 x y z).
Proof. exact (@lem1486910 x y z (@lem1486907 x y z h1 h2)). Qed.
Lemma lem1486914 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : term99 x y z.
Proof. exact (fun h0 : term100 x y z => @lem1486913 x y z h1 h2). Qed.
Lemma lem1486916 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1486917 (x : real) (y : real) (z : real) : (term99 x y z) = ((term20 x z y) = (term27 x y z)).
Proof. exact (@lem1486916 ((term20 x z y) = (term27 x y z))). Qed.
Lemma lem1486918 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : (term20 x z y) = (term27 x y z).
Proof. exact (EQ_MP (@lem1486917 x y z) (@lem1486914 x y z h1 h2)). Qed.
Lemma lem1486920 (_24834 : real) (_24833 : real) (h1 : term10) : (real_mul _24833 _24834) = (real_mul _24834 _24833).
Proof. exact (EQ_MP (@lem1486739 _24834 _24833) (@lem1486738 _24833 _24834 h1)). Qed.
Lemma lem1486921 (z : real) (x : real) (h1 : term10) : (real_mul x z) = (real_mul z x).
Proof. exact (@lem1486920 z x h1). Qed.
Lemma lem1486922 (z : real) (x : real) (h1 : term10) : term101 z x.
Proof. exact (fun h0 : term102 z x => @lem1486921 z x h1). Qed.
Lemma lem1486924 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1486925 (z : real) (x : real) : (term101 z x) = ((real_mul x z) = (real_mul z x)).
Proof. exact (@lem1486924 ((real_mul x z) = (real_mul z x))). Qed.
Lemma lem1486926 (z : real) (x : real) (h1 : term10) : (real_mul x z) = (real_mul z x).
Proof. exact (EQ_MP (@lem1486925 z x) (@lem1486922 z x h1)). Qed.
Lemma lem1486928 (_24834 : real) (_24833 : real) (h1 : term10) : (real_mul _24833 _24834) = (real_mul _24834 _24833).
Proof. exact (EQ_MP (@lem1486739 _24834 _24833) (@lem1486738 _24833 _24834 h1)). Qed.
Lemma lem1486929 (z : real) (y : real) (h1 : term10) : (real_mul y z) = (real_mul z y).
Proof. exact (@lem1486928 z y h1). Qed.
Lemma lem1486930 (z : real) (y : real) (h1 : term10) : term101 z y.
Proof. exact (fun h0 : term102 z y => @lem1486929 z y h1). Qed.
Lemma lem1486932 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1486933 (z : real) (y : real) : (term101 z y) = ((real_mul y z) = (real_mul z y)).
Proof. exact (@lem1486932 ((real_mul y z) = (real_mul z y))). Qed.
Lemma lem1486934 (z : real) (y : real) (h1 : term10) : (real_mul y z) = (real_mul z y).
Proof. exact (EQ_MP (@lem1486933 z y) (@lem1486930 z y h1)). Qed.
Lemma lem1486952 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1486953 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term64 _24839 _24840 _24841 _24842) = (term103 _24839 _24841 _24840 _24842).
Proof. exact (@lem1486952 ((real_add _24839 _24840) = (real_add _24841 _24842)) (term75 _24840 _24842)). Qed.
Lemma lem1486963 (_24839 : real) (_24841 : real) : (term76 _24839 _24841) = (term76 _24839 _24841).
Proof. exact (eq_refl (term76 _24839 _24841)). Qed.
Lemma lem1486964 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term66 _24839 _24840 _24841 _24842) = (term104 _24839 _24841 _24840 _24842).
Proof. exact (MK_COMB (@lem1486963 _24839 _24841) (@lem1486953 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1486968 (q : Prop) (p : Prop) (r : Prop) : (term78 p q r) = (term78 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1486969 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term104 _24839 _24841 _24840 _24842) = (term105 _24839 _24841 _24840 _24842).
Proof. exact (@lem1486968 ((real_add _24839 _24840) = (real_add _24841 _24842)) (term75 _24839 _24841) (term75 _24840 _24842)). Qed.
Lemma lem1486991 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term66 _24839 _24840 _24841 _24842) = (term105 _24839 _24841 _24840 _24842).
Proof. exact (TRANS (@lem1486964 _24839 _24841 _24840 _24842) (@lem1486969 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1486992 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1486993 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term106 _24839 _24840 _24841 _24842) = (term107 _24839 _24841 _24840 _24842).
Proof. exact (MK_COMB (@lem1486992) (@lem1486991 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487015 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term105 _24839 _24841 _24840 _24842) = (term105 _24839 _24841 _24840 _24842).
Proof. exact (eq_refl (term105 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487016 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : ((term66 _24839 _24840 _24841 _24842) = (term105 _24839 _24841 _24840 _24842)) = ((term105 _24839 _24841 _24840 _24842) = (term105 _24839 _24841 _24840 _24842)).
Proof. exact (MK_COMB (@lem1486993 _24839 _24841 _24840 _24842) (@lem1487015 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487018 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1487019 (x : Prop) : (x = x) = True.
Proof. exact (@lem1487018 Prop x). Qed.
Lemma lem1487020 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : ((term105 _24839 _24841 _24840 _24842) = (term105 _24839 _24841 _24840 _24842)) = True.
Proof. exact (@lem1487019 (term105 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487021 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : ((term66 _24839 _24840 _24841 _24842) = (term105 _24839 _24841 _24840 _24842)) = True.
Proof. exact (TRANS (@lem1487016 _24839 _24841 _24840 _24842) (@lem1487020 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487022 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : True = ((term66 _24839 _24840 _24841 _24842) = (term105 _24839 _24841 _24840 _24842)).
Proof. exact (SYM (@lem1487021 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487023 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term66 _24839 _24840 _24841 _24842) = (term105 _24839 _24841 _24840 _24842).
Proof. exact (EQ_MP (@lem1487022 _24839 _24841 _24840 _24842) (@lem0)). Qed.
Lemma lem1487024 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : term105 _24839 _24841 _24840 _24842.
Proof. exact (EQ_MP (@lem1487023 _24839 _24841 _24840 _24842) (@lem1486776 _24839 _24840 _24841 _24842)). Qed.
Lemma lem1487026 (b : Prop) (a : Prop) : (a \/ b) = (term82 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1487027 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : (term105 _24839 _24841 _24840 _24842) = (term108 _24839 _24840 _24841 _24842).
Proof. exact (@lem1487026 (term109 _24839 _24841 _24840 _24842) ((real_add _24839 _24840) = (real_add _24841 _24842))). Qed.
Lemma lem1487029 (a : Prop) (b : Prop) : (term85 a b) = (term86 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1487030 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term110 _24839 _24841 _24840 _24842) = (term111 _24839 _24841 _24840 _24842).
Proof. exact (@lem1487029 (term75 _24839 _24841) (term75 _24840 _24842)). Qed.
Lemma lem1487032 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1487033 (_24839 : real) (_24841 : real) : (term90 _24839 _24841) = (_24839 = _24841).
Proof. exact (@lem1487032 (_24839 = _24841)). Qed.
Lemma lem1487034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1487035 (_24839 : real) (_24841 : real) : (term91 _24839 _24841) = (term92 _24839 _24841).
Proof. exact (MK_COMB (@lem1487034) (@lem1487033 _24839 _24841)). Qed.
Lemma lem1487037 (a : Prop) : (term89 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1487038 (_24840 : real) (_24842 : real) : (term90 _24840 _24842) = (_24840 = _24842).
Proof. exact (@lem1487037 (_24840 = _24842)). Qed.
Lemma lem1487039 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term111 _24839 _24841 _24840 _24842) = (term112 _24839 _24841 _24840 _24842).
Proof. exact (MK_COMB (@lem1487035 _24839 _24841) (@lem1487038 _24840 _24842)). Qed.
Lemma lem1487040 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term110 _24839 _24841 _24840 _24842) = (term112 _24839 _24841 _24840 _24842).
Proof. exact (TRANS (@lem1487030 _24839 _24841 _24840 _24842) (@lem1487039 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487041 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1487042 (_24839 : real) (_24841 : real) (_24840 : real) (_24842 : real) : (term113 _24839 _24841 _24840 _24842) = (term114 _24839 _24841 _24840 _24842).
Proof. exact (MK_COMB (@lem1487041) (@lem1487040 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487043 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : ((real_add _24839 _24840) = (real_add _24841 _24842)) = ((real_add _24839 _24840) = (real_add _24841 _24842)).
Proof. exact (eq_refl ((real_add _24839 _24840) = (real_add _24841 _24842))). Qed.
Lemma lem1487044 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : (term108 _24839 _24840 _24841 _24842) = (term115 _24839 _24840 _24841 _24842).
Proof. exact (MK_COMB (@lem1487042 _24839 _24841 _24840 _24842) (@lem1487043 _24839 _24840 _24841 _24842)). Qed.
Lemma lem1487045 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : (term105 _24839 _24841 _24840 _24842) = (term115 _24839 _24840 _24841 _24842).
Proof. exact (TRANS (@lem1487027 _24839 _24840 _24841 _24842) (@lem1487044 _24839 _24840 _24841 _24842)). Qed.
Lemma lem1487047 (x : real) (z : real) (y : real) (h1 : term10) : term116 x z y.
Proof. exact (conj (@lem1486926 z x h1) (@lem1486934 z y h1)). Qed.
Lemma lem1487049 (_24839 : real) (_24840 : real) (_24841 : real) (_24842 : real) : term115 _24839 _24840 _24841 _24842.
Proof. exact (EQ_MP (@lem1487045 _24839 _24840 _24841 _24842) (@lem1487024 _24839 _24841 _24840 _24842)). Qed.
Lemma lem1487050 (x : real) (z : real) (y : real) : term117 x z y.
Proof. exact (@lem1487049 (real_mul x z) (real_mul y z) (real_mul z x) (real_mul z y)). Qed.
Lemma lem1487053 (x : real) (z : real) (y : real) (h1 : term10) : (term28 x y z) = (term20 x z y).
Proof. exact (@lem1487050 x z y (@lem1487047 x z y h1)). Qed.
Lemma lem1487054 (x : real) (z : real) (y : real) (h1 : term10) : term118 x z y.
Proof. exact (fun h0 : term119 x z y => @lem1487053 x z y h1). Qed.
Lemma lem1487056 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1487057 (x : real) (z : real) (y : real) : (term118 x z y) = ((term28 x y z) = (term20 x z y)).
Proof. exact (@lem1487056 ((term28 x y z) = (term20 x z y))). Qed.
Lemma lem1487058 (x : real) (z : real) (y : real) (h1 : term10) : (term28 x y z) = (term20 x z y).
Proof. exact (EQ_MP (@lem1487057 x z y) (@lem1487054 x z y h1)). Qed.
Lemma lem1487060 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1487061 (x : real) (y : real) (z : real) : (term28 x y z) = (term28 x y z).
Proof. exact (@lem1487060 (term28 x y z)). Qed.
Lemma lem1487062 (x : real) (y : real) (z : real) : term120 x y z.
Proof. exact (fun h0 : term121 x y z => @lem1487061 x y z). Qed.
Lemma lem1487064 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1487065 (x : real) (y : real) (z : real) : (term120 x y z) = ((term28 x y z) = (term28 x y z)).
Proof. exact (@lem1487064 ((term28 x y z) = (term28 x y z))). Qed.
Lemma lem1487066 (x : real) (y : real) (z : real) : (term28 x y z) = (term28 x y z).
Proof. exact (EQ_MP (@lem1487065 x y z) (@lem1487062 x y z)). Qed.
Lemma lem1487067 (x : real) (y : real) (z : real) (h1 : term10) : term122 x y z.
Proof. exact (conj (@lem1487058 x z y h1) (@lem1487066 x y z)). Qed.
Lemma lem1487069 (x : real) (y : real) (z : real) : term96 x y z.
Proof. exact (EQ_MP (@lem1486905 x y z) (@lem1486884 y x z)). Qed.
Lemma lem1487070 (x : real) (y : real) (z : real) : term123 x y z.
Proof. exact (@lem1487069 (term28 x y z) (term20 x z y) (term28 x y z)). Qed.
Lemma lem1487073 (x : real) (y : real) (z : real) (h1 : term10) : (term20 x z y) = (term28 x y z).
Proof. exact (@lem1487070 x y z (@lem1487067 x y z h1)). Qed.
Lemma lem1487074 (x : real) (y : real) (z : real) (h1 : term10) : term124 x y z.
Proof. exact (fun h0 : term125 x y z => @lem1487073 x y z h1). Qed.
Lemma lem1487076 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1487077 (x : real) (y : real) (z : real) : (term124 x y z) = ((term20 x z y) = (term28 x y z)).
Proof. exact (@lem1487076 ((term20 x z y) = (term28 x y z))). Qed.
Lemma lem1487078 (x : real) (y : real) (z : real) (h1 : term10) : (term20 x z y) = (term28 x y z).
Proof. exact (EQ_MP (@lem1487077 x y z) (@lem1487074 x y z h1)). Qed.
Lemma lem1487079 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : term126 x y z.
Proof. exact (conj (@lem1486918 x y z h1 h2) (@lem1487078 x y z h2)). Qed.
Lemma lem1487081 (x : real) (y : real) (z : real) : term96 x y z.
Proof. exact (EQ_MP (@lem1486905 x y z) (@lem1486884 y x z)). Qed.
Lemma lem1487082 (x : real) (y : real) (z : real) : term127 x y z.
Proof. exact (@lem1487081 (term20 x z y) (term27 x y z) (term28 x y z)). Qed.
Lemma lem1487085 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : (term27 x y z) = (term28 x y z).
Proof. exact (@lem1487082 x y z (@lem1487079 x y z h1 h2)). Qed.
Lemma lem1487086 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : term128 x y z.
Proof. exact (fun h0 : term40 x y z => @lem1487085 x y z h1 h2). Qed.
Lemma lem1487088 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1487089 (x : real) (y : real) (z : real) : (term128 x y z) = ((term27 x y z) = (term28 x y z)).
Proof. exact (@lem1487088 ((term27 x y z) = (term28 x y z))). Qed.
Lemma lem1487090 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) : (term27 x y z) = (term28 x y z).
Proof. exact (EQ_MP (@lem1487089 x y z) (@lem1487086 x y z h1 h2)). Qed.
Lemma lem1487093 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1487095 (x : real) (y : real) (z : real) : (term40 x y z) = (term129 x y z).
Proof. exact (@lem1487093 ((term27 x y z) = (term28 x y z))). Qed.
Lemma lem1487098 (x : real) (y : real) (z : real) (h1 : term40 x y z) : term129 x y z.
Proof. exact (EQ_MP (@lem1487095 x y z) (@lem1486746 x y z h1)). Qed.
Lemma lem1487101 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (@lem1487098 x y z h3 (@lem1487090 x y z h1 h2)). Qed.
Lemma lem1487102 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : term130.
Proof. exact (fun h0 : ~ False => @lem1487101 x y z h1 h2 h3). Qed.
Lemma lem1487104 (p : Prop) : (term70 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1487105 : term130 = False.
Proof. exact (@lem1487104 False). Qed.
Lemma lem1487106 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487105) (@lem1487102 x y z h1 h2 h3)). Qed.
Lemma lem1487107 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : (term40 x y z) = False.
Proof. exact (prop_ext (fun h4 : term40 x y z => @lem1487106 x y z h1 h2 h3) (fun h4 : False => @lem1486746 x y z h3)). Qed.
Lemma lem1487108 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487107 x y z h1 h2 h3) (@lem1486746 x y z h3)). Qed.
Lemma lem1487109 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : (term40 x y z) = False.
Proof. exact (prop_ext (fun h4 : term40 x y z => @lem1487108 x y z h1 h2 h3) (fun h4 : False => @lem1486725 x y z h3)). Qed.
Lemma lem1487110 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487109 x y z h1 h2 h3) (@lem1486725 x y z h3)). Qed.
Lemma lem1487111 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : (term40 x y z) = False.
Proof. exact (prop_ext (fun h4 : term40 x y z => @lem1487110 x y z h1 h2 h3) (fun h4 : False => @lem1486725 x y z h3)). Qed.
Lemma lem1487112 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487111 x y z h1 h2 h3) (@lem1486725 x y z h3)). Qed.
Lemma lem1487113 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1487112 x y z h1 h2 h3) (fun h4 : False => @lem1486721 h2)). Qed.
Lemma lem1487114 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487113 x y z h1 h2 h3) (@lem1486721 h2)). Qed.
Lemma lem1487115 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : term26 = False.
Proof. exact (prop_ext (fun h4 : term26 => @lem1487114 x y z h1 h2 h3) (fun h4 : False => @lem1486711 h1)). Qed.
Lemma lem1487116 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487115 x y z h1 h2 h3) (@lem1486711 h1)). Qed.
Lemma lem1487117 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : (term40 x y z) = False.
Proof. exact (prop_ext (fun h4 : term40 x y z => @lem1487116 x y z h1 h2 h3) (fun h4 : False => @lem1486698 x y z h3)). Qed.
Lemma lem1487118 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487117 x y z h1 h2 h3) (@lem1486698 x y z h3)). Qed.
Lemma lem1487119 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1487118 x y z h1 h2 h3) (fun h4 : False => @lem1486670 h2)). Qed.
Lemma lem1487120 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487119 x y z h1 h2 h3) (@lem1486670 h2)). Qed.
Lemma lem1487121 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : term26 = False.
Proof. exact (prop_ext (fun h4 : term26 => @lem1487120 x y z h1 h2 h3) (fun h4 : False => @lem1486650 h1)). Qed.
Lemma lem1487122 (x : real) (y : real) (z : real) (h1 : term26) (h2 : term10) (h3 : term40 x y z) : False.
Proof. exact (EQ_MP (@lem1487121 x y z h1 h2 h3) (@lem1486650 h1)). Qed.
Lemma lem1487123 (x : real) (y : real) (h1 : term26) (h2 : term10) (h3 : term43 x y) : False.
Proof. exact (ex_elim (@lem1486614 x y h3) (fun z : real => fun h0 : term42 x y z => @lem1487122 x y z h1 h2 h0)). Qed.
Lemma lem1487124 (x : real) (h1 : term26) (h2 : term10) (h3 : term50 x) : False.
Proof. exact (ex_elim (@lem1486613 x h3) (fun y : real => fun h0 : term49 x y => @lem1487123 x y h1 h2 h0)). Qed.
Lemma lem1487125 (h1 : term26) (h2 : term10) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1486565 h3) (fun x : real => fun h0 : term55 x => @lem1487124 x h1 h2 h0)). Qed.
Lemma lem1487126 (h1 : term26) (h2 : term10) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1487125 h1 h2 h3) (fun h4 : False => @lem1486612 h2)). Qed.
Lemma lem1487127 (h1 : term26) (h2 : term10) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1487126 h1 h2 h3) (@lem1486612 h2)). Qed.
Lemma lem1487128 (h1 : term26) (h2 : term10) (h3 : term3) : term26 = False.
Proof. exact (prop_ext (fun h4 : term26 => @lem1487127 h1 h2 h3) (fun h4 : False => @lem1486592 h1)). Qed.
Lemma lem1487129 (h1 : term26) (h2 : term10) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1487128 h1 h2 h3) (@lem1486592 h1)). Qed.
Lemma lem1487130 (h1 : term26) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1487129 h1 h0 h2). Qed.
Lemma lem1487131 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1487132 (h1 : term26) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1487131) (@lem1487130 h1 h2)). Qed.
Lemma lem1487133 (h1 : term3) : term13.
Proof. exact (fun h0 : term26 => @lem1487132 h0 h1). Qed.
Lemma lem1487134 : term15.
Proof. exact (fun h0 : term3 => @lem1487133 h0). Qed.
Lemma lem1487135 : term4.
Proof. exact (EQ_MP (@lem1486514) (@lem1487134)). Qed.
Lemma lem1487137 : term4.
Proof. exact (@lem1486370 (@lem1487135)). Qed.
Lemma lem1487138 (h1 : term3) : term12.
Proof. exact (@lem1487137 (@lem1486355 h1)). Qed.
Lemma lem1487139 (h1 : term3) : term8.
Proof. exact (@lem1487138 h1 (@lem1339188)). Qed.
Lemma lem1487140 (h1 : term3) : False.
Proof. exact (@lem1487139 h1 (@lem1338712)). Qed.
Lemma lem1487141 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1487140 h1) (fun h2 : False => @lem1486355 h1)). Qed.
Lemma lem1487142 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1487141 h1) (@lem1486355 h1)). Qed.
Lemma lem1487143 : term2.
Proof. exact (fun h0 : term3 => @lem1487142 h0). Qed.
Lemma lem1487144 : term1.
Proof. exact (EQ_MP (@lem1486354) (@lem1487143)). Qed.
