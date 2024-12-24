Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import int_sub_th_term_abbrevs.
Require Import int_add_th_spec.
Require Import int_neg_th_spec.
Require Import int_sub_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm2267744_spec.
Require Import thm2267745_spec.
Lemma lem2285434 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem2285435 (x : int) (y : int) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem2285434 x y h1)). Qed.
Lemma lem2285436 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2285437 (x : int) (y : int) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem2285436 x y h1)). Qed.
Lemma lem2285438 (x : int) (y : int) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem2285435 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem2285437 x y h1)). Qed.
Lemma lem2285439 (x : int) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : int => @lem2285438 x y)). Qed.
Lemma lem2285440 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2285441 (x : int) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem2285440) (@lem2285439 x)). Qed.
Lemma lem2285442 : term6 = term7.
Proof. exact (fun_ext (fun x : int => @lem2285441 x)). Qed.
Lemma lem2285443 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2285444 : term8 = term9.
Proof. exact (MK_COMB (@lem2285443) (@lem2285442)). Qed.
Lemma lem2285445 : term9.
Proof. exact (EQ_MP (@lem2285444) (@lem2284714)). Qed.
Lemma lem2285447 (x : int) (h1 : (term10 x) = (term11 x)) : (term10 x) = (term11 x).
Proof. exact (h1). Qed.
Lemma lem2285448 (x : int) (h1 : (term10 x) = (term11 x)) : (term11 x) = (term10 x).
Proof. exact (SYM (@lem2285447 x h1)). Qed.
Lemma lem2285449 (x : int) (h1 : (term11 x) = (term10 x)) : (term11 x) = (term10 x).
Proof. exact (h1). Qed.
Lemma lem2285450 (x : int) (h1 : (term11 x) = (term10 x)) : (term10 x) = (term11 x).
Proof. exact (SYM (@lem2285449 x h1)). Qed.
Lemma lem2285451 (x : int) : ((term10 x) = (term11 x)) = ((term11 x) = (term10 x)).
Proof. exact (prop_ext (fun h1 : (term10 x) = (term11 x) => @lem2285448 x h1) (fun h1 : (term11 x) = (term10 x) => @lem2285450 x h1)). Qed.
Lemma lem2285452 : term12 = term13.
Proof. exact (fun_ext (fun x : int => @lem2285451 x)). Qed.
Lemma lem2285453 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2285454 : term14 = term15.
Proof. exact (MK_COMB (@lem2285453) (@lem2285452)). Qed.
Lemma lem2285455 : term15.
Proof. exact (EQ_MP (@lem2285454) (@lem2273074)). Qed.
Lemma lem2285456 (x : int) : term16 x.
Proof. exact (@lem2285445 x). Qed.
Lemma lem2285457 (x : int) : (term16 x) = (term5 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem2285458 (x : int) : term5 x.
Proof. exact (EQ_MP (@lem2285457 x) (@lem2285456 x)). Qed.
Lemma lem2285459 (x : int) (y : int) : term17 x y.
Proof. exact (@lem2285458 x y). Qed.
Lemma lem2285460 (x : int) (y : int) : (term17 x y) = ((term1 x y) = (term0 x y)).
Proof. exact (eq_refl (term17 x y)). Qed.
Lemma lem2285462 (x : int) : term18 x.
Proof. exact (@lem2285455 x). Qed.
Lemma lem2285463 (x : int) : (term18 x) = ((term11 x) = (term10 x)).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem2285465 (x : real) : term19 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem2285466 (x : real) : (term19 x) = (term20 x).
Proof. exact (eq_refl (term19 x)). Qed.
Lemma lem2285467 (x : real) : term20 x.
Proof. exact (EQ_MP (@lem2285466 x) (@lem2285465 x)). Qed.
Lemma lem2285468 (x : real) (y : real) : term21 x y.
Proof. exact (@lem2285467 x y). Qed.
Lemma lem2285469 (x : real) (y : real) : (term21 x y) = ((real_sub x y) = (term22 x y)).
Proof. exact (eq_refl (term21 x y)). Qed.
Lemma lem2285471 (x : int) : term23 x.
Proof. exact (@lem2285431 x). Qed.
Lemma lem2285472 (x : int) : (term23 x) = (term24 x).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem2285473 (x : int) : term24 x.
Proof. exact (EQ_MP (@lem2285472 x) (@lem2285471 x)). Qed.
Lemma lem2285474 (x : int) (y : int) : term25 x y.
Proof. exact (@lem2285473 x y). Qed.
Lemma lem2285475 (x : int) (y : int) : (term25 x y) = ((int_sub x y) = (term26 x y)).
Proof. exact (eq_refl (term25 x y)). Qed.
Lemma lem2285488 (x : int) (y : int) : (int_sub x y) = (term26 x y).
Proof. exact (EQ_MP (@lem2285475 x y) (@lem2285474 x y)). Qed.
Lemma lem2285490 (x : real) (y : real) : (real_sub x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2285469 x y) (@lem2285468 x y)). Qed.
Lemma lem2285491 (x : int) (y : int) : (term27 x y) = (term28 x y).
Proof. exact (@lem2285490 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2285493 (x : int) : (term11 x) = (term10 x).
Proof. exact (EQ_MP (@lem2285463 x) (@lem2285462 x)). Qed.
Lemma lem2285494 (y : int) : (term11 y) = (term10 y).
Proof. exact (@lem2285493 y). Qed.
Lemma lem2285495 (x : int) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem2285496 (x : int) (y : int) : (term28 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem2285495 x) (@lem2285494 y)). Qed.
Lemma lem2285498 (x : int) (y : int) : (term1 x y) = (term0 x y).
Proof. exact (EQ_MP (@lem2285460 x y) (@lem2285459 x y)). Qed.
Lemma lem2285499 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (@lem2285498 x (int_neg y)). Qed.
Lemma lem2285500 (x : int) (y : int) : (term28 x y) = (term31 x y).
Proof. exact (TRANS (@lem2285496 x y) (@lem2285499 x y)). Qed.
Lemma lem2285501 (x : int) (y : int) : (term27 x y) = (term31 x y).
Proof. exact (TRANS (@lem2285491 x y) (@lem2285500 x y)). Qed.
Lemma lem2285502 : int_of_real = int_of_real.
Proof. exact (eq_refl int_of_real). Qed.
Lemma lem2285503 (x : int) (y : int) : (term26 x y) = (term32 x y).
Proof. exact (MK_COMB (@lem2285502) (@lem2285501 x y)). Qed.
Lemma lem2285504 (x : int) (y : int) : (int_sub x y) = (term32 x y).
Proof. exact (TRANS (@lem2285488 x y) (@lem2285503 x y)). Qed.
Lemma lem2285505 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2285506 (x : int) (y : int) : (term33 x y) = (term34 x y).
Proof. exact (MK_COMB (@lem2285505) (@lem2285504 x y)). Qed.
Lemma lem2285507 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2285508 (x : int) (y : int) : (term35 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem2285507) (@lem2285506 x y)). Qed.
Lemma lem2285510 (x : real) (y : real) : (real_sub x y) = (term22 x y).
Proof. exact (EQ_MP (@lem2285469 x y) (@lem2285468 x y)). Qed.
Lemma lem2285511 (x : int) (y : int) : (term27 x y) = (term28 x y).
Proof. exact (@lem2285510 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2285513 (x : int) : (term11 x) = (term10 x).
Proof. exact (EQ_MP (@lem2285463 x) (@lem2285462 x)). Qed.
Lemma lem2285514 (y : int) : (term11 y) = (term10 y).
Proof. exact (@lem2285513 y). Qed.
Lemma lem2285515 (x : int) : (term29 x) = (term29 x).
Proof. exact (eq_refl (term29 x)). Qed.
Lemma lem2285516 (x : int) (y : int) : (term28 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem2285515 x) (@lem2285514 y)). Qed.
Lemma lem2285518 (x : int) (y : int) : (term1 x y) = (term0 x y).
Proof. exact (EQ_MP (@lem2285460 x y) (@lem2285459 x y)). Qed.
Lemma lem2285519 (x : int) (y : int) : (term30 x y) = (term31 x y).
Proof. exact (@lem2285518 x (int_neg y)). Qed.
Lemma lem2285520 (x : int) (y : int) : (term28 x y) = (term31 x y).
Proof. exact (TRANS (@lem2285516 x y) (@lem2285519 x y)). Qed.
Lemma lem2285521 (x : int) (y : int) : (term27 x y) = (term31 x y).
Proof. exact (TRANS (@lem2285511 x y) (@lem2285520 x y)). Qed.
Lemma lem2285522 (x : int) (y : int) : ((term33 x y) = (term27 x y)) = ((term34 x y) = (term31 x y)).
Proof. exact (MK_COMB (@lem2285508 x y) (@lem2285521 x y)). Qed.
Lemma lem2285525 (x : int) : (term37 x) = (term38 x).
Proof. exact (fun_ext (fun y : int => @lem2285522 x y)). Qed.
Lemma lem2285526 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2285527 (x : int) : (term39 x) = (term40 x).
Proof. exact (MK_COMB (@lem2285526) (@lem2285525 x)). Qed.
Lemma lem2285532 : term41 = term42.
Proof. exact (fun_ext (fun x : int => @lem2285527 x)). Qed.
Lemma lem2285533 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2285534 : term43 = term44.
Proof. exact (MK_COMB (@lem2285533) (@lem2285532)). Qed.
Lemma lem2285539 : term44 = term43.
Proof. exact (SYM (@lem2285534)). Qed.
Lemma lem2285551 (a : int) : (term45 a) = a.
Proof. exact (EQ_MP (@lem2267745 a) (@lem2267744 a)). Qed.
Lemma lem2285552 (x : int) (y : int) : (term32 x y) = (term46 x y).
Proof. exact (@lem2285551 (term46 x y)). Qed.
Lemma lem2285553 : real_of_int = real_of_int.
Proof. exact (eq_refl real_of_int). Qed.
Lemma lem2285554 (x : int) (y : int) : (term34 x y) = (term31 x y).
Proof. exact (MK_COMB (@lem2285553) (@lem2285552 x y)). Qed.
Lemma lem2285555 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem2285556 (x : int) (y : int) : (term36 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem2285555) (@lem2285554 x y)). Qed.
Lemma lem2285557 (x : int) (y : int) : (term31 x y) = (term31 x y).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem2285558 (x : int) (y : int) : ((term34 x y) = (term31 x y)) = ((term31 x y) = (term31 x y)).
Proof. exact (MK_COMB (@lem2285556 x y) (@lem2285557 x y)). Qed.
Lemma lem2285560 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2285561 (x : real) : (x = x) = True.
Proof. exact (@lem2285560 real x). Qed.
Lemma lem2285562 (x : int) (y : int) : ((term31 x y) = (term31 x y)) = True.
Proof. exact (@lem2285561 (term31 x y)). Qed.
Lemma lem2285563 (x : int) (y : int) : ((term34 x y) = (term31 x y)) = True.
Proof. exact (TRANS (@lem2285558 x y) (@lem2285562 x y)). Qed.
Lemma lem2285564 (x : int) : (term38 x) = term48.
Proof. exact (fun_ext (fun y : int => @lem2285563 x y)). Qed.
Lemma lem2285565 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2285566 (x : int) : (term40 x) = term49.
Proof. exact (MK_COMB (@lem2285565) (@lem2285564 x)). Qed.
Lemma lem2285568 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2285569 (t : Prop) : (term51 t) = t.
Proof. exact (@lem2285568 int t). Qed.
Lemma lem2285570 : term49 = True.
Proof. exact (@lem2285569 True). Qed.
Lemma lem2285571 (x : int) : (term40 x) = True.
Proof. exact (TRANS (@lem2285566 x) (@lem2285570)). Qed.
Lemma lem2285572 : term42 = term48.
Proof. exact (fun_ext (fun x : int => @lem2285571 x)). Qed.
Lemma lem2285573 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2285574 : term44 = term49.
Proof. exact (MK_COMB (@lem2285573) (@lem2285572)). Qed.
Lemma lem2285576 {A : Type'} (t : Prop) : (term50 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2285577 (t : Prop) : (term51 t) = t.
Proof. exact (@lem2285576 int t). Qed.
Lemma lem2285578 : term49 = True.
Proof. exact (@lem2285577 True). Qed.
Lemma lem2285579 : term44 = True.
Proof. exact (TRANS (@lem2285574) (@lem2285578)). Qed.
Lemma lem2285580 : True = term44.
Proof. exact (SYM (@lem2285579)). Qed.
Lemma lem2285581 : term44.
Proof. exact (EQ_MP (@lem2285580) (@lem0)). Qed.
Lemma lem2285582 : term43.
Proof. exact (EQ_MP (@lem2285539) (@lem2285581)). Qed.
