Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_NEG2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem1525396 (y : real) (x : real) : (term0 y x) = (term1 y x).
Proof. exact (@lem17646 (term2 x y) (real_lt y x)). Qed.
Lemma lem1525397 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1525398 (x : real) : (term5 x) = (term6 x).
Proof. exact (@lem1525397 (term7 x)). Qed.
Lemma lem1525399 (y : real) (x : real) : (term8 x y) = ((term2 x y) = (real_lt y x)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1525400 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1525401 (y : real) (x : real) : (term9 x y) = (term0 y x).
Proof. exact (MK_COMB (@lem1525400) (@lem1525399 y x)). Qed.
Lemma lem1525402 (y : real) (x : real) : (term9 x y) = (term1 y x).
Proof. exact (TRANS (@lem1525401 y x) (@lem1525396 y x)). Qed.
Lemma lem1525403 (x : real) : (term10 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1525402 y x)). Qed.
Lemma lem1525404 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525405 (x : real) : (term6 x) = (term12 x).
Proof. exact (MK_COMB (@lem1525404) (@lem1525403 x)). Qed.
Lemma lem1525406 (x : real) : (term5 x) = (term12 x).
Proof. exact (TRANS (@lem1525398 x) (@lem1525405 x)). Qed.
Lemma lem1525407 (P : real -> Prop) : (term3 P) = (term4 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1525408 : term13 = term14.
Proof. exact (@lem1525407 term15). Qed.
Lemma lem1525409 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1525410 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1525411 (x : real) : (term18 x) = (term5 x).
Proof. exact (MK_COMB (@lem1525410) (@lem1525409 x)). Qed.
Lemma lem1525412 (x : real) : (term18 x) = (term12 x).
Proof. exact (TRANS (@lem1525411 x) (@lem1525406 x)). Qed.
Lemma lem1525413 : term19 = term20.
Proof. exact (fun_ext (fun x : real => @lem1525412 x)). Qed.
Lemma lem1525414 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525415 : term14 = term21.
Proof. exact (MK_COMB (@lem1525414) (@lem1525413)). Qed.
Lemma lem1525417 : term13 = term21.
Proof. exact (TRANS (@lem1525408) (@lem1525415)). Qed.
Lemma lem1525434 (y : real) (x : real) : (term1 y x) = (term1 y x).
Proof. exact (eq_refl (term1 y x)). Qed.
Lemma lem1525435 (x : real) : (term11 x) = (term11 x).
Proof. exact (fun_ext (fun y : real => @lem1525434 y x)). Qed.
Lemma lem1525436 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525437 (x : real) : (term12 x) = (term12 x).
Proof. exact (MK_COMB (@lem1525436) (@lem1525435 x)). Qed.
Lemma lem1525438 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1525437 x)). Qed.
Lemma lem1525439 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525440 : term21 = term21.
Proof. exact (MK_COMB (@lem1525439) (@lem1525438)). Qed.
Lemma lem1525441 : term13 = term21.
Proof. exact (TRANS (@lem1525417) (@lem1525440)). Qed.
Lemma lem1525442 (y : real) (x : real) : (term2 x y) = (term22 y x).
Proof. exact (@lem1483521 (real_neg y) (real_neg x)). Qed.
Lemma lem1525449 (x : real) : (real_neg x) = (term23 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1525456 (y : real) : (real_neg y) = (term23 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1525457 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1525458 (y : real) : (term24 y) = (term25 y).
Proof. exact (MK_COMB (@lem1525457) (@lem1525456 y)). Qed.
Lemma lem1525459 (y : real) (x : real) : (term26 y x) = (term27 y x).
Proof. exact (MK_COMB (@lem1525458 y) (@lem1525449 x)). Qed.
Lemma lem1525460 (y : real) (x : real) : (term27 y x) = (term28 y x).
Proof. exact (@lem1483519 (term23 y) (term23 x)). Qed.
Lemma lem1525461 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1483476 term31 term31 x). Qed.
Lemma lem1525463 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1525464 : term34 = term35.
Proof. exact (@lem1525463 term36 term36). Qed.
Lemma lem1525465 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1525466 : term38 = term36.
Proof. exact (EQ_MP (@lem1525465) (@lem940073)). Qed.
Lemma lem1525467 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1525468 : term35 = term39.
Proof. exact (MK_COMB (@lem1525467) (@lem1525466)). Qed.
Lemma lem1525469 : term34 = term39.
Proof. exact (TRANS (@lem1525464) (@lem1525468)). Qed.
Lemma lem1525470 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525471 : term40 = term41.
Proof. exact (MK_COMB (@lem1525470) (@lem1525469)). Qed.
Lemma lem1525472 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1525473 (x : real) : (term30 x) = (term42 x).
Proof. exact (MK_COMB (@lem1525471) (@lem1525472 x)). Qed.
Lemma lem1525474 (x : real) : (term29 x) = (term42 x).
Proof. exact (TRANS (@lem1525461 x) (@lem1525473 x)). Qed.
Lemma lem1525475 (x : real) : (term42 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1525476 (x : real) : (term29 x) = x.
Proof. exact (TRANS (@lem1525474 x) (@lem1525475 x)). Qed.
Lemma lem1525477 (y : real) : (term43 y) = (term43 y).
Proof. exact (eq_refl (term43 y)). Qed.
Lemma lem1525478 (y : real) (x : real) : (term28 y x) = (term44 y x).
Proof. exact (MK_COMB (@lem1525477 y) (@lem1525476 x)). Qed.
Lemma lem1525479 (x : real) (y : real) : (term44 y x) = (term45 x y).
Proof. exact (@lem1483488 x (term23 y)). Qed.
Lemma lem1525480 (x : real) (y : real) : (term28 y x) = (term45 x y).
Proof. exact (TRANS (@lem1525478 y x) (@lem1525479 x y)). Qed.
Lemma lem1525481 (x : real) (y : real) : (term27 y x) = (term45 x y).
Proof. exact (TRANS (@lem1525460 y x) (@lem1525480 x y)). Qed.
Lemma lem1525482 (x : real) (y : real) : (term26 y x) = (term45 x y).
Proof. exact (TRANS (@lem1525459 y x) (@lem1525481 x y)). Qed.
Lemma lem1525483 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525484 (x : real) (y : real) : (term46 y x) = (term47 x y).
Proof. exact (MK_COMB (@lem1525483) (@lem1525482 x y)). Qed.
Lemma lem1525485 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1525486 (x : real) (y : real) : (term22 y x) = (term49 x y).
Proof. exact (MK_COMB (@lem1525484 x y) (@lem1525485)). Qed.
Lemma lem1525487 (x : real) (y : real) : (term2 x y) = (term49 x y).
Proof. exact (TRANS (@lem1525442 y x) (@lem1525486 x y)). Qed.
Lemma lem1525488 (y : real) (x : real) : (term50 y x) = (term51 y x).
Proof. exact (@lem1483531 y x). Qed.
Lemma lem1525494 (y : real) (x : real) : (real_sub y x) = (term45 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1525499 (x : real) (y : real) : (term45 y x) = (term44 x y).
Proof. exact (@lem1483488 (term23 x) y). Qed.
Lemma lem1525501 (x : real) (y : real) : (real_sub y x) = (term44 x y).
Proof. exact (TRANS (@lem1525494 y x) (@lem1525499 x y)). Qed.
Lemma lem1525502 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1525503 (x : real) (y : real) : (term52 y x) = (term53 x y).
Proof. exact (MK_COMB (@lem1525502) (@lem1525501 x y)). Qed.
Lemma lem1525504 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1525505 (x : real) (y : real) : (term51 y x) = (term54 x y).
Proof. exact (MK_COMB (@lem1525503 x y) (@lem1525504)). Qed.
Lemma lem1525506 (x : real) (y : real) : (term50 y x) = (term54 x y).
Proof. exact (TRANS (@lem1525488 y x) (@lem1525505 x y)). Qed.
Lemma lem1525507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1525508 (x : real) (y : real) : (term55 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1525507) (@lem1525487 x y)). Qed.
Lemma lem1525509 (x : real) (y : real) : (term57 y x) = (term58 x y).
Proof. exact (MK_COMB (@lem1525508 x y) (@lem1525506 x y)). Qed.
Lemma lem1525510 (x : real) (y : real) : (term59 x y) = (term60 x y).
Proof. exact (@lem1483531 (real_neg x) (real_neg y)). Qed.
Lemma lem1525517 (y : real) : (real_neg y) = (term23 y).
Proof. exact (@lem1483512 y). Qed.
Lemma lem1525524 (x : real) : (real_neg x) = (term23 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1525525 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1525526 (x : real) : (term24 x) = (term25 x).
Proof. exact (MK_COMB (@lem1525525) (@lem1525524 x)). Qed.
Lemma lem1525527 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (MK_COMB (@lem1525526 x) (@lem1525517 y)). Qed.
Lemma lem1525528 (x : real) (y : real) : (term27 x y) = (term28 x y).
Proof. exact (@lem1483519 (term23 x) (term23 y)). Qed.
Lemma lem1525529 (y : real) : (term29 y) = (term30 y).
Proof. exact (@lem1483476 term31 term31 y). Qed.
Lemma lem1525531 (m : nat) (n : nat) : (term32 m n) = (term33 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1525532 : term34 = term35.
Proof. exact (@lem1525531 term36 term36). Qed.
Lemma lem1525533 : (term37 = (BIT1 0)) = (term38 = term36).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1525534 : term38 = term36.
Proof. exact (EQ_MP (@lem1525533) (@lem940073)). Qed.
Lemma lem1525535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1525536 : term35 = term39.
Proof. exact (MK_COMB (@lem1525535) (@lem1525534)). Qed.
Lemma lem1525537 : term34 = term39.
Proof. exact (TRANS (@lem1525532) (@lem1525536)). Qed.
Lemma lem1525538 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1525539 : term40 = term41.
Proof. exact (MK_COMB (@lem1525538) (@lem1525537)). Qed.
Lemma lem1525540 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1525541 (y : real) : (term30 y) = (term42 y).
Proof. exact (MK_COMB (@lem1525539) (@lem1525540 y)). Qed.
Lemma lem1525542 (y : real) : (term29 y) = (term42 y).
Proof. exact (TRANS (@lem1525529 y) (@lem1525541 y)). Qed.
Lemma lem1525543 (y : real) : (term42 y) = y.
Proof. exact (@lem1483436 y). Qed.
Lemma lem1525544 (y : real) : (term29 y) = y.
Proof. exact (TRANS (@lem1525542 y) (@lem1525543 y)). Qed.
Lemma lem1525545 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1525548 (x : real) (y : real) : (term28 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem1525545 x) (@lem1525544 y)). Qed.
Lemma lem1525549 (x : real) (y : real) : (term27 x y) = (term44 x y).
Proof. exact (TRANS (@lem1525528 x y) (@lem1525548 x y)). Qed.
Lemma lem1525550 (x : real) (y : real) : (term26 x y) = (term44 x y).
Proof. exact (TRANS (@lem1525527 x y) (@lem1525549 x y)). Qed.
Lemma lem1525551 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1525552 (x : real) (y : real) : (term61 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1525551) (@lem1525550 x y)). Qed.
Lemma lem1525553 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1525554 (x : real) (y : real) : (term60 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1525552 x y) (@lem1525553)). Qed.
Lemma lem1525555 (x : real) (y : real) : (term59 x y) = (term54 x y).
Proof. exact (TRANS (@lem1525510 x y) (@lem1525554 x y)). Qed.
Lemma lem1525556 (x : real) (y : real) : (real_lt y x) = (term62 x y).
Proof. exact (@lem1483521 x y). Qed.
Lemma lem1525569 (x : real) (y : real) : (real_sub x y) = (term45 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1525570 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525571 (x : real) (y : real) : (term63 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1525570) (@lem1525569 x y)). Qed.
Lemma lem1525572 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1525573 (x : real) (y : real) : (term62 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1525571 x y) (@lem1525572)). Qed.
Lemma lem1525574 (x : real) (y : real) : (real_lt y x) = (term49 x y).
Proof. exact (TRANS (@lem1525556 x y) (@lem1525573 x y)). Qed.
Lemma lem1525575 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1525576 (x : real) (y : real) : (term64 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1525575) (@lem1525555 x y)). Qed.
Lemma lem1525577 (x : real) (y : real) : (term66 y x) = (term67 x y).
Proof. exact (MK_COMB (@lem1525576 x y) (@lem1525574 x y)). Qed.
Lemma lem1525578 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525579 (x : real) (y : real) : (term68 y x) = (term69 x y).
Proof. exact (MK_COMB (@lem1525578) (@lem1525509 x y)). Qed.
Lemma lem1525580 (x : real) (y : real) : (term1 y x) = (term70 x y).
Proof. exact (MK_COMB (@lem1525579 x y) (@lem1525577 x y)). Qed.
Lemma lem1525581 (x : real) : (term11 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1525580 x y)). Qed.
Lemma lem1525582 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525583 (x : real) : (term12 x) = (term72 x).
Proof. exact (MK_COMB (@lem1525582) (@lem1525581 x)). Qed.
Lemma lem1525584 : term20 = term73.
Proof. exact (fun_ext (fun x : real => @lem1525583 x)). Qed.
Lemma lem1525585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525586 : term21 = term74.
Proof. exact (MK_COMB (@lem1525585) (@lem1525584)). Qed.
Lemma lem1525587 : term13 = term74.
Proof. exact (TRANS (@lem1525441) (@lem1525586)). Qed.
Lemma lem1525593 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1525594 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem1525593 real P Q). Qed.
Lemma lem1525595 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1525594 (term81 x) (term82 x)). Qed.
Lemma lem1525596 (x : real) (y : real) : (term83 x y) = (term58 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem1525597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525598 (x : real) (y : real) : (term84 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1525597) (@lem1525596 x y)). Qed.
Lemma lem1525599 (x : real) (y : real) : (term85 x y) = (term67 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1525600 (x : real) (y : real) : (term86 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1525598 x y) (@lem1525599 x y)). Qed.
Lemma lem1525601 (x : real) : (term87 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1525600 x y)). Qed.
Lemma lem1525602 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525603 (x : real) : (term79 x) = (term72 x).
Proof. exact (MK_COMB (@lem1525602) (@lem1525601 x)). Qed.
Lemma lem1525604 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1525605 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1525604) (@lem1525603 x)). Qed.
Lemma lem1525606 (x : real) (y : real) : (term83 x y) = (term58 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem1525607 (x : real) : (term90 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1525606 x y)). Qed.
Lemma lem1525608 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525609 (x : real) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1525608) (@lem1525607 x)). Qed.
Lemma lem1525610 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525611 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1525610) (@lem1525609 x)). Qed.
Lemma lem1525612 (x : real) (y : real) : (term85 x y) = (term67 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1525613 (x : real) : (term95 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1525612 x y)). Qed.
Lemma lem1525614 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525615 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1525614) (@lem1525613 x)). Qed.
Lemma lem1525616 (x : real) : (term80 x) = (term98 x).
Proof. exact (MK_COMB (@lem1525611 x) (@lem1525615 x)). Qed.
Lemma lem1525617 (x : real) : ((term79 x) = (term80 x)) = ((term72 x) = (term98 x)).
Proof. exact (MK_COMB (@lem1525605 x) (@lem1525616 x)). Qed.
Lemma lem1525618 (x : real) : (term72 x) = (term98 x).
Proof. exact (EQ_MP (@lem1525617 x) (@lem1525595 x)). Qed.
Lemma lem1525715 : term73 = term99.
Proof. exact (fun_ext (fun x : real => @lem1525618 x)). Qed.
Lemma lem1525716 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525717 : term74 = term100.
Proof. exact (MK_COMB (@lem1525716) (@lem1525715)). Qed.
Lemma lem1525719 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1525720 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term78 P Q).
Proof. exact (@lem1525719 real P Q). Qed.
Lemma lem1525721 : term101 = term102.
Proof. exact (@lem1525720 term103 term104). Qed.
Lemma lem1525722 (x : real) : (term105 x) = (term92 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1525723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525724 (x : real) : (term106 x) = (term94 x).
Proof. exact (MK_COMB (@lem1525723) (@lem1525722 x)). Qed.
Lemma lem1525725 (x : real) : (term107 x) = (term97 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1525726 (x : real) : (term108 x) = (term98 x).
Proof. exact (MK_COMB (@lem1525724 x) (@lem1525725 x)). Qed.
Lemma lem1525727 : term109 = term99.
Proof. exact (fun_ext (fun x : real => @lem1525726 x)). Qed.
Lemma lem1525728 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525729 : term101 = term100.
Proof. exact (MK_COMB (@lem1525728) (@lem1525727)). Qed.
Lemma lem1525730 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1525731 : term110 = term111.
Proof. exact (MK_COMB (@lem1525730) (@lem1525729)). Qed.
Lemma lem1525732 (x : real) : (term105 x) = (term92 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1525733 : term112 = term103.
Proof. exact (fun_ext (fun x : real => @lem1525732 x)). Qed.
Lemma lem1525734 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525735 : term113 = term114.
Proof. exact (MK_COMB (@lem1525734) (@lem1525733)). Qed.
Lemma lem1525736 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525737 : term115 = term116.
Proof. exact (MK_COMB (@lem1525736) (@lem1525735)). Qed.
Lemma lem1525738 (x : real) : (term107 x) = (term97 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1525739 : term117 = term104.
Proof. exact (fun_ext (fun x : real => @lem1525738 x)). Qed.
Lemma lem1525740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525741 : term118 = term119.
Proof. exact (MK_COMB (@lem1525740) (@lem1525739)). Qed.
Lemma lem1525742 : term102 = term120.
Proof. exact (MK_COMB (@lem1525737) (@lem1525741)). Qed.
Lemma lem1525743 : (term101 = term102) = (term100 = term120).
Proof. exact (MK_COMB (@lem1525731) (@lem1525742)). Qed.
Lemma lem1525744 : term100 = term120.
Proof. exact (EQ_MP (@lem1525743) (@lem1525721)). Qed.
Lemma lem1525849 : term74 = term120.
Proof. exact (TRANS (@lem1525717) (@lem1525744)). Qed.
Lemma lem1525851 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1525852 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term77 P Q).
Proof. exact (@lem1525851 real P Q). Qed.
Lemma lem1525853 : term102 = term101.
Proof. exact (@lem1525852 term103 term104). Qed.
Lemma lem1525854 (x : real) : (term105 x) = (term92 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1525855 : term112 = term103.
Proof. exact (fun_ext (fun x : real => @lem1525854 x)). Qed.
Lemma lem1525856 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525857 : term113 = term114.
Proof. exact (MK_COMB (@lem1525856) (@lem1525855)). Qed.
Lemma lem1525858 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525859 : term115 = term116.
Proof. exact (MK_COMB (@lem1525858) (@lem1525857)). Qed.
Lemma lem1525860 (x : real) : (term107 x) = (term97 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1525861 : term117 = term104.
Proof. exact (fun_ext (fun x : real => @lem1525860 x)). Qed.
Lemma lem1525862 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525863 : term118 = term119.
Proof. exact (MK_COMB (@lem1525862) (@lem1525861)). Qed.
Lemma lem1525864 : term102 = term120.
Proof. exact (MK_COMB (@lem1525859) (@lem1525863)). Qed.
Lemma lem1525865 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1525866 : term121 = term122.
Proof. exact (MK_COMB (@lem1525865) (@lem1525864)). Qed.
Lemma lem1525867 (x : real) : (term105 x) = (term92 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem1525868 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525869 (x : real) : (term106 x) = (term94 x).
Proof. exact (MK_COMB (@lem1525868) (@lem1525867 x)). Qed.
Lemma lem1525870 (x : real) : (term107 x) = (term97 x).
Proof. exact (eq_refl (term107 x)). Qed.
Lemma lem1525871 (x : real) : (term108 x) = (term98 x).
Proof. exact (MK_COMB (@lem1525869 x) (@lem1525870 x)). Qed.
Lemma lem1525872 : term109 = term99.
Proof. exact (fun_ext (fun x : real => @lem1525871 x)). Qed.
Lemma lem1525873 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525874 : term101 = term100.
Proof. exact (MK_COMB (@lem1525873) (@lem1525872)). Qed.
Lemma lem1525875 : (term102 = term101) = (term120 = term100).
Proof. exact (MK_COMB (@lem1525866) (@lem1525874)). Qed.
Lemma lem1525876 : term120 = term100.
Proof. exact (EQ_MP (@lem1525875) (@lem1525853)). Qed.
Lemma lem1525878 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1525879 (P : real -> Prop) (Q : real -> Prop) : (term78 P Q) = (term77 P Q).
Proof. exact (@lem1525878 real P Q). Qed.
Lemma lem1525880 (x : real) : (term80 x) = (term79 x).
Proof. exact (@lem1525879 (term81 x) (term82 x)). Qed.
Lemma lem1525881 (x : real) (y : real) : (term83 x y) = (term58 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem1525882 (x : real) : (term90 x) = (term81 x).
Proof. exact (fun_ext (fun y : real => @lem1525881 x y)). Qed.
Lemma lem1525883 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525884 (x : real) : (term91 x) = (term92 x).
Proof. exact (MK_COMB (@lem1525883) (@lem1525882 x)). Qed.
Lemma lem1525885 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525886 (x : real) : (term93 x) = (term94 x).
Proof. exact (MK_COMB (@lem1525885) (@lem1525884 x)). Qed.
Lemma lem1525887 (x : real) (y : real) : (term85 x y) = (term67 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1525888 (x : real) : (term95 x) = (term82 x).
Proof. exact (fun_ext (fun y : real => @lem1525887 x y)). Qed.
Lemma lem1525889 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525890 (x : real) : (term96 x) = (term97 x).
Proof. exact (MK_COMB (@lem1525889) (@lem1525888 x)). Qed.
Lemma lem1525891 (x : real) : (term80 x) = (term98 x).
Proof. exact (MK_COMB (@lem1525886 x) (@lem1525890 x)). Qed.
Lemma lem1525892 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1525893 (x : real) : (term123 x) = (term124 x).
Proof. exact (MK_COMB (@lem1525892) (@lem1525891 x)). Qed.
Lemma lem1525894 (x : real) (y : real) : (term83 x y) = (term58 x y).
Proof. exact (eq_refl (term83 x y)). Qed.
Lemma lem1525895 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1525896 (x : real) (y : real) : (term84 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1525895) (@lem1525894 x y)). Qed.
Lemma lem1525897 (x : real) (y : real) : (term85 x y) = (term67 x y).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1525898 (x : real) (y : real) : (term86 x y) = (term70 x y).
Proof. exact (MK_COMB (@lem1525896 x y) (@lem1525897 x y)). Qed.
Lemma lem1525899 (x : real) : (term87 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1525898 x y)). Qed.
Lemma lem1525900 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525901 (x : real) : (term79 x) = (term72 x).
Proof. exact (MK_COMB (@lem1525900) (@lem1525899 x)). Qed.
Lemma lem1525902 (x : real) : ((term80 x) = (term79 x)) = ((term98 x) = (term72 x)).
Proof. exact (MK_COMB (@lem1525893 x) (@lem1525901 x)). Qed.
Lemma lem1525903 (x : real) : (term98 x) = (term72 x).
Proof. exact (EQ_MP (@lem1525902 x) (@lem1525880 x)). Qed.
Lemma lem1525904 : term99 = term73.
Proof. exact (fun_ext (fun x : real => @lem1525903 x)). Qed.
Lemma lem1525905 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525906 : term100 = term74.
Proof. exact (MK_COMB (@lem1525905) (@lem1525904)). Qed.
Lemma lem1525907 : term120 = term74.
Proof. exact (TRANS (@lem1525876) (@lem1525906)). Qed.
Lemma lem1525908 : term74 = term74.
Proof. exact (TRANS (@lem1525849) (@lem1525907)). Qed.
Lemma lem1525911 : term13 = term74.
Proof. exact (TRANS (@lem1525587) (@lem1525908)). Qed.
Lemma lem1525928 (x : real) (y : real) : (term70 x y) = (term70 x y).
Proof. exact (eq_refl (term70 x y)). Qed.
Lemma lem1525929 (x : real) : (term71 x) = (term71 x).
Proof. exact (fun_ext (fun y : real => @lem1525928 x y)). Qed.
Lemma lem1525930 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525931 (x : real) : (term72 x) = (term72 x).
Proof. exact (MK_COMB (@lem1525930) (@lem1525929 x)). Qed.
Lemma lem1525932 : term73 = term73.
Proof. exact (fun_ext (fun x : real => @lem1525931 x)). Qed.
Lemma lem1525933 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1525934 : term74 = term74.
Proof. exact (MK_COMB (@lem1525933) (@lem1525932)). Qed.
Lemma lem1525935 : term13 = term74.
Proof. exact (TRANS (@lem1525911) (@lem1525934)). Qed.
Lemma lem1525945 (x : real) (y : real) (h1 : term70 x y) : term70 x y.
Proof. exact (h1). Qed.
Lemma lem1525946 (x : real) (y : real) (h1 : term58 x y) : term58 x y.
Proof. exact (h1). Qed.
Lemma lem1525947 (x : real) (y : real) (h1 : term58 x y) : term54 x y.
Proof. exact (proj2 (@lem1525946 x y h1)). Qed.
Lemma lem1525948 (x : real) (y : real) (h1 : term58 x y) : term49 x y.
Proof. exact (proj1 (@lem1525946 x y h1)). Qed.
Lemma lem1525950 (n : nat) (m : nat) : (term125 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525951 : term126 = term127.
Proof. exact (@lem1525950 (NUMERAL 0) term36). Qed.
Lemma lem1525952 : term128 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1525953 (h1 : term128 = (BIT1 0)) : term127 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1525954 : (term128 = (BIT1 0)) = (term127 = True).
Proof. exact (prop_ext (fun h1 : term128 = (BIT1 0) => @lem1525953 h1) (fun h1 : term127 = True => @lem1525952)). Qed.
Lemma lem1525955 : term127 = True.
Proof. exact (EQ_MP (@lem1525954) (@lem1525952)). Qed.
Lemma lem1525956 : term126 = True.
Proof. exact (TRANS (@lem1525951) (@lem1525955)). Qed.
Lemma lem1525957 : True = term126.
Proof. exact (SYM (@lem1525956)). Qed.
Lemma lem1525958 : term126.
Proof. exact (EQ_MP (@lem1525957) (@lem0)). Qed.
Lemma lem1525959 (x : real) (y : real) (h1 : term58 x y) : term129 x y.
Proof. exact (conj (@lem1525958) (@lem1525947 x y h1)). Qed.
Lemma lem1525961 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1525962 (x : real) (y : real) : term131 x y.
Proof. exact (@lem1525961 term39 (term44 x y)). Qed.
Lemma lem1525963 (x : real) (y : real) (h1 : term58 x y) : term132 x y.
Proof. exact (@lem1525962 x y (@lem1525959 x y h1)). Qed.
Lemma lem1525964 (x : real) (y : real) : (term133 x y) = (term44 x y).
Proof. exact (@lem1483460 (term44 x y)). Qed.
Lemma lem1525965 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1525966 (x : real) (y : real) : (term134 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1525965) (@lem1525964 x y)). Qed.
Lemma lem1525967 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1525968 (x : real) (y : real) : (term132 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1525966 x y) (@lem1525967)). Qed.
Lemma lem1525969 (x : real) (y : real) (h1 : term58 x y) : term54 x y.
Proof. exact (EQ_MP (@lem1525968 x y) (@lem1525963 x y h1)). Qed.
Lemma lem1525971 (n : nat) (m : nat) : (term125 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1525972 : term126 = term127.
Proof. exact (@lem1525971 (NUMERAL 0) term36). Qed.
Lemma lem1525973 : term128 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1525974 (h1 : term128 = (BIT1 0)) : term127 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1525975 : (term128 = (BIT1 0)) = (term127 = True).
Proof. exact (prop_ext (fun h1 : term128 = (BIT1 0) => @lem1525974 h1) (fun h1 : term127 = True => @lem1525973)). Qed.
Lemma lem1525976 : term127 = True.
Proof. exact (EQ_MP (@lem1525975) (@lem1525973)). Qed.
Lemma lem1525977 : term126 = True.
Proof. exact (TRANS (@lem1525972) (@lem1525976)). Qed.
Lemma lem1525978 : True = term126.
Proof. exact (SYM (@lem1525977)). Qed.
Lemma lem1525979 : term126.
Proof. exact (EQ_MP (@lem1525978) (@lem0)). Qed.
Lemma lem1525980 (x : real) (y : real) (h1 : term58 x y) : term135 x y.
Proof. exact (conj (@lem1525979) (@lem1525948 x y h1)). Qed.
Lemma lem1525982 (x : real) (y : real) : term136 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1525983 (x : real) (y : real) : term137 x y.
Proof. exact (@lem1525982 term39 (term45 x y)). Qed.
Lemma lem1525984 (x : real) (y : real) (h1 : term58 x y) : term138 x y.
Proof. exact (@lem1525983 x y (@lem1525980 x y h1)). Qed.
Lemma lem1525985 (x : real) (y : real) : (term139 x y) = (term45 x y).
Proof. exact (@lem1483460 (term45 x y)). Qed.
Lemma lem1525986 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1525987 (x : real) (y : real) : (term140 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1525986) (@lem1525985 x y)). Qed.
Lemma lem1525988 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1525989 (x : real) (y : real) : (term138 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1525987 x y) (@lem1525988)). Qed.
Lemma lem1525990 (x : real) (y : real) (h1 : term58 x y) : term49 x y.
Proof. exact (EQ_MP (@lem1525989 x y) (@lem1525984 x y h1)). Qed.
Lemma lem1525991 (x : real) (y : real) (h1 : term58 x y) : term58 x y.
Proof. exact (conj (@lem1525990 x y h1) (@lem1525969 x y h1)). Qed.
Lemma lem1525993 (x : real) (y : real) : term141 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1525994 (x : real) (y : real) : term142 x y.
Proof. exact (@lem1525993 (term45 x y) (term44 x y)). Qed.
Lemma lem1525995 (x : real) (y : real) (h1 : term58 x y) : term143 x y.
Proof. exact (@lem1525994 x y (@lem1525991 x y h1)). Qed.
Lemma lem1525996 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (@lem1483480 x (term23 x) (term23 y) y). Qed.
Lemma lem1525997 (x : real) : (term146 x) = (term147 x).
Proof. exact (@lem1483442 term31 x). Qed.
Lemma lem1525999 (m : nat) : (term148 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526000 : term149 = term48.
Proof. exact (@lem1525999 term36). Qed.
Lemma lem1526001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526002 : term150 = term151.
Proof. exact (MK_COMB (@lem1526001) (@lem1526000)). Qed.
Lemma lem1526003 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1526004 (x : real) : (term147 x) = (term152 x).
Proof. exact (MK_COMB (@lem1526002) (@lem1526003 x)). Qed.
Lemma lem1526005 (x : real) : (term146 x) = (term152 x).
Proof. exact (TRANS (@lem1525997 x) (@lem1526004 x)). Qed.
Lemma lem1526006 (x : real) : (term152 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1526007 (x : real) : (term146 x) = term48.
Proof. exact (TRANS (@lem1526005 x) (@lem1526006 x)). Qed.
Lemma lem1526008 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1526009 (x : real) : (term153 x) = term154.
Proof. exact (MK_COMB (@lem1526008) (@lem1526007 x)). Qed.
Lemma lem1526010 (y : real) : (term155 y) = (term147 y).
Proof. exact (@lem1483440 term31 y). Qed.
Lemma lem1526012 (m : nat) : (term148 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526013 : term149 = term48.
Proof. exact (@lem1526012 term36). Qed.
Lemma lem1526014 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526015 : term150 = term151.
Proof. exact (MK_COMB (@lem1526014) (@lem1526013)). Qed.
Lemma lem1526016 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1526017 (y : real) : (term147 y) = (term152 y).
Proof. exact (MK_COMB (@lem1526015) (@lem1526016 y)). Qed.
Lemma lem1526018 (y : real) : (term155 y) = (term152 y).
Proof. exact (TRANS (@lem1526010 y) (@lem1526017 y)). Qed.
Lemma lem1526019 (y : real) : (term152 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1526020 (y : real) : (term155 y) = term48.
Proof. exact (TRANS (@lem1526018 y) (@lem1526019 y)). Qed.
Lemma lem1526021 (x : real) (y : real) : (term145 x y) = term156.
Proof. exact (MK_COMB (@lem1526009 x) (@lem1526020 y)). Qed.
Lemma lem1526022 (x : real) (y : real) : (term144 x y) = term156.
Proof. exact (TRANS (@lem1525996 x y) (@lem1526021 x y)). Qed.
Lemma lem1526023 : term156 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1526024 (x : real) (y : real) : (term144 x y) = term48.
Proof. exact (TRANS (@lem1526022 x y) (@lem1526023)). Qed.
Lemma lem1526025 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526026 (x : real) (y : real) : (term157 x y) = term158.
Proof. exact (MK_COMB (@lem1526025) (@lem1526024 x y)). Qed.
Lemma lem1526027 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1526028 (x : real) (y : real) : (term143 x y) = term159.
Proof. exact (MK_COMB (@lem1526026 x y) (@lem1526027)). Qed.
Lemma lem1526029 (x : real) (y : real) (h1 : term58 x y) : term159.
Proof. exact (EQ_MP (@lem1526028 x y) (@lem1525995 x y h1)). Qed.
Lemma lem1526031 (n : nat) (m : nat) : (term125 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526032 : term159 = term160.
Proof. exact (@lem1526031 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1526033 : term160 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1526034 : term159 = False.
Proof. exact (TRANS (@lem1526032) (@lem1526033)). Qed.
Lemma lem1526035 (x : real) (y : real) (h1 : term58 x y) : False.
Proof. exact (EQ_MP (@lem1526034) (@lem1526029 x y h1)). Qed.
Lemma lem1526036 (x : real) (y : real) (h1 : term67 x y) : term67 x y.
Proof. exact (h1). Qed.
Lemma lem1526037 (x : real) (y : real) (h1 : term67 x y) : term49 x y.
Proof. exact (proj2 (@lem1526036 x y h1)). Qed.
Lemma lem1526038 (x : real) (y : real) (h1 : term67 x y) : term54 x y.
Proof. exact (proj1 (@lem1526036 x y h1)). Qed.
Lemma lem1526040 (n : nat) (m : nat) : (term125 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526041 : term126 = term127.
Proof. exact (@lem1526040 (NUMERAL 0) term36). Qed.
Lemma lem1526042 : term128 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1526043 (h1 : term128 = (BIT1 0)) : term127 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1526044 : (term128 = (BIT1 0)) = (term127 = True).
Proof. exact (prop_ext (fun h1 : term128 = (BIT1 0) => @lem1526043 h1) (fun h1 : term127 = True => @lem1526042)). Qed.
Lemma lem1526045 : term127 = True.
Proof. exact (EQ_MP (@lem1526044) (@lem1526042)). Qed.
Lemma lem1526046 : term126 = True.
Proof. exact (TRANS (@lem1526041) (@lem1526045)). Qed.
Lemma lem1526047 : True = term126.
Proof. exact (SYM (@lem1526046)). Qed.
Lemma lem1526048 : term126.
Proof. exact (EQ_MP (@lem1526047) (@lem0)). Qed.
Lemma lem1526049 (x : real) (y : real) (h1 : term67 x y) : term129 x y.
Proof. exact (conj (@lem1526048) (@lem1526038 x y h1)). Qed.
Lemma lem1526051 (x : real) (y : real) : term130 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1526052 (x : real) (y : real) : term131 x y.
Proof. exact (@lem1526051 term39 (term44 x y)). Qed.
Lemma lem1526053 (x : real) (y : real) (h1 : term67 x y) : term132 x y.
Proof. exact (@lem1526052 x y (@lem1526049 x y h1)). Qed.
Lemma lem1526054 (x : real) (y : real) : (term133 x y) = (term44 x y).
Proof. exact (@lem1483460 (term44 x y)). Qed.
Lemma lem1526055 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1526056 (x : real) (y : real) : (term134 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1526055) (@lem1526054 x y)). Qed.
Lemma lem1526057 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1526058 (x : real) (y : real) : (term132 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1526056 x y) (@lem1526057)). Qed.
Lemma lem1526059 (x : real) (y : real) (h1 : term67 x y) : term54 x y.
Proof. exact (EQ_MP (@lem1526058 x y) (@lem1526053 x y h1)). Qed.
Lemma lem1526061 (n : nat) (m : nat) : (term125 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526062 : term126 = term127.
Proof. exact (@lem1526061 (NUMERAL 0) term36). Qed.
Lemma lem1526063 : term128 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1526064 (h1 : term128 = (BIT1 0)) : term127 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1526065 : (term128 = (BIT1 0)) = (term127 = True).
Proof. exact (prop_ext (fun h1 : term128 = (BIT1 0) => @lem1526064 h1) (fun h1 : term127 = True => @lem1526063)). Qed.
Lemma lem1526066 : term127 = True.
Proof. exact (EQ_MP (@lem1526065) (@lem1526063)). Qed.
Lemma lem1526067 : term126 = True.
Proof. exact (TRANS (@lem1526062) (@lem1526066)). Qed.
Lemma lem1526068 : True = term126.
Proof. exact (SYM (@lem1526067)). Qed.
Lemma lem1526069 : term126.
Proof. exact (EQ_MP (@lem1526068) (@lem0)). Qed.
Lemma lem1526070 (x : real) (y : real) (h1 : term67 x y) : term135 x y.
Proof. exact (conj (@lem1526069) (@lem1526037 x y h1)). Qed.
Lemma lem1526072 (x : real) (y : real) : term136 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1526073 (x : real) (y : real) : term137 x y.
Proof. exact (@lem1526072 term39 (term45 x y)). Qed.
Lemma lem1526074 (x : real) (y : real) (h1 : term67 x y) : term138 x y.
Proof. exact (@lem1526073 x y (@lem1526070 x y h1)). Qed.
Lemma lem1526075 (x : real) (y : real) : (term139 x y) = (term45 x y).
Proof. exact (@lem1483460 (term45 x y)). Qed.
Lemma lem1526076 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526077 (x : real) (y : real) : (term140 x y) = (term47 x y).
Proof. exact (MK_COMB (@lem1526076) (@lem1526075 x y)). Qed.
Lemma lem1526078 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1526079 (x : real) (y : real) : (term138 x y) = (term49 x y).
Proof. exact (MK_COMB (@lem1526077 x y) (@lem1526078)). Qed.
Lemma lem1526080 (x : real) (y : real) (h1 : term67 x y) : term49 x y.
Proof. exact (EQ_MP (@lem1526079 x y) (@lem1526074 x y h1)). Qed.
Lemma lem1526081 (x : real) (y : real) (h1 : term67 x y) : term58 x y.
Proof. exact (conj (@lem1526080 x y h1) (@lem1526059 x y h1)). Qed.
Lemma lem1526083 (x : real) (y : real) : term141 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1526084 (x : real) (y : real) : term142 x y.
Proof. exact (@lem1526083 (term45 x y) (term44 x y)). Qed.
Lemma lem1526085 (x : real) (y : real) (h1 : term67 x y) : term143 x y.
Proof. exact (@lem1526084 x y (@lem1526081 x y h1)). Qed.
Lemma lem1526086 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (@lem1483480 x (term23 x) (term23 y) y). Qed.
Lemma lem1526087 (x : real) : (term146 x) = (term147 x).
Proof. exact (@lem1483442 term31 x). Qed.
Lemma lem1526089 (m : nat) : (term148 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526090 : term149 = term48.
Proof. exact (@lem1526089 term36). Qed.
Lemma lem1526091 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526092 : term150 = term151.
Proof. exact (MK_COMB (@lem1526091) (@lem1526090)). Qed.
Lemma lem1526093 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1526094 (x : real) : (term147 x) = (term152 x).
Proof. exact (MK_COMB (@lem1526092) (@lem1526093 x)). Qed.
Lemma lem1526095 (x : real) : (term146 x) = (term152 x).
Proof. exact (TRANS (@lem1526087 x) (@lem1526094 x)). Qed.
Lemma lem1526096 (x : real) : (term152 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1526097 (x : real) : (term146 x) = term48.
Proof. exact (TRANS (@lem1526095 x) (@lem1526096 x)). Qed.
Lemma lem1526098 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1526099 (x : real) : (term153 x) = term154.
Proof. exact (MK_COMB (@lem1526098) (@lem1526097 x)). Qed.
Lemma lem1526100 (y : real) : (term155 y) = (term147 y).
Proof. exact (@lem1483440 term31 y). Qed.
Lemma lem1526102 (m : nat) : (term148 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1526103 : term149 = term48.
Proof. exact (@lem1526102 term36). Qed.
Lemma lem1526104 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1526105 : term150 = term151.
Proof. exact (MK_COMB (@lem1526104) (@lem1526103)). Qed.
Lemma lem1526106 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1526107 (y : real) : (term147 y) = (term152 y).
Proof. exact (MK_COMB (@lem1526105) (@lem1526106 y)). Qed.
Lemma lem1526108 (y : real) : (term155 y) = (term152 y).
Proof. exact (TRANS (@lem1526100 y) (@lem1526107 y)). Qed.
Lemma lem1526109 (y : real) : (term152 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1526110 (y : real) : (term155 y) = term48.
Proof. exact (TRANS (@lem1526108 y) (@lem1526109 y)). Qed.
Lemma lem1526111 (x : real) (y : real) : (term145 x y) = term156.
Proof. exact (MK_COMB (@lem1526099 x) (@lem1526110 y)). Qed.
Lemma lem1526112 (x : real) (y : real) : (term144 x y) = term156.
Proof. exact (TRANS (@lem1526086 x y) (@lem1526111 x y)). Qed.
Lemma lem1526113 : term156 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1526114 (x : real) (y : real) : (term144 x y) = term48.
Proof. exact (TRANS (@lem1526112 x y) (@lem1526113)). Qed.
Lemma lem1526115 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1526116 (x : real) (y : real) : (term157 x y) = term158.
Proof. exact (MK_COMB (@lem1526115) (@lem1526114 x y)). Qed.
Lemma lem1526117 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1526118 (x : real) (y : real) : (term143 x y) = term159.
Proof. exact (MK_COMB (@lem1526116 x y) (@lem1526117)). Qed.
Lemma lem1526119 (x : real) (y : real) (h1 : term67 x y) : term159.
Proof. exact (EQ_MP (@lem1526118 x y) (@lem1526085 x y h1)). Qed.
Lemma lem1526121 (n : nat) (m : nat) : (term125 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1526122 : term159 = term160.
Proof. exact (@lem1526121 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1526123 : term160 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1526124 : term159 = False.
Proof. exact (TRANS (@lem1526122) (@lem1526123)). Qed.
Lemma lem1526125 (x : real) (y : real) (h1 : term67 x y) : False.
Proof. exact (EQ_MP (@lem1526124) (@lem1526119 x y h1)). Qed.
Lemma lem1526126 (x : real) (y : real) (h1 : term70 x y) : False.
Proof. exact (or_elim (@lem1525945 x y h1) (fun h0 : term58 x y => @lem1526035 x y h0) (fun h0 : term67 x y => @lem1526125 x y h0)). Qed.
Lemma lem1526128 (x : real) (y : real) (h1 : term70 x y) : term70 x y.
Proof. exact (h1). Qed.
Lemma lem1526129 (x : real) (y : real) (h1 : term70 x y) : (term70 x y) = False.
Proof. exact (prop_ext (fun h2 : term70 x y => @lem1526126 x y h1) (fun h2 : False => @lem1526128 x y h1)). Qed.
Lemma lem1526130 (x : real) (y : real) (h1 : term70 x y) : False.
Proof. exact (EQ_MP (@lem1526129 x y h1) (@lem1526128 x y h1)). Qed.
Lemma lem1526131 (x : real) (h1 : term72 x) : term72 x.
Proof. exact (h1). Qed.
Lemma lem1526132 (x : real) (h1 : term72 x) : False.
Proof. exact (ex_elim (@lem1526131 x h1) (fun y : real => fun h0 : term71 x y => @lem1526130 x y h0)). Qed.
Lemma lem1526133 (h1 : term74) : term74.
Proof. exact (h1). Qed.
Lemma lem1526134 (h1 : term74) : False.
Proof. exact (ex_elim (@lem1526133 h1) (fun x : real => fun h0 : term73 x => @lem1526132 x h0)). Qed.
Lemma lem1526135 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem1526136 (h1 : term13) : term74.
Proof. exact (EQ_MP (@lem1525935) (@lem1526135 h1)). Qed.
Lemma lem1526137 (h1 : term13) : term74 = False.
Proof. exact (prop_ext (fun h2 : term74 => @lem1526134 h2) (fun h2 : False => @lem1526136 h1)). Qed.
Lemma lem1526138 (h1 : term13) : False.
Proof. exact (EQ_MP (@lem1526137 h1) (@lem1526136 h1)). Qed.
Lemma lem1526139 : term161.
Proof. exact (fun h0 : term13 => @lem1526138 h0). Qed.
Lemma lem1526140 : term162.
Proof. exact (@lem1386578 term163). Qed.
Lemma lem1526141 : term163.
Proof. exact (@lem1526140 (@lem1526139)). Qed.
