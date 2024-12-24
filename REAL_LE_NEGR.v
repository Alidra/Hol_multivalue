Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_NEGR_term_abbrevs.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1483436_spec.
Require Import thm1483438_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483476_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483523_spec.
Require Import thm1483533_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Lemma lem1506398 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17646 (term2 x) (term3 x)). Qed.
Lemma lem1506399 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1506400 : term6 = term7.
Proof. exact (@lem1506399 term8). Qed.
Lemma lem1506401 (x : real) : (term9 x) = ((term2 x) = (term3 x)).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1506402 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1506403 (x : real) : (term10 x) = (term0 x).
Proof. exact (MK_COMB (@lem1506402) (@lem1506401 x)). Qed.
Lemma lem1506404 (x : real) : (term10 x) = (term1 x).
Proof. exact (TRANS (@lem1506403 x) (@lem1506398 x)). Qed.
Lemma lem1506405 : term11 = term12.
Proof. exact (fun_ext (fun x : real => @lem1506404 x)). Qed.
Lemma lem1506406 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506407 : term7 = term13.
Proof. exact (MK_COMB (@lem1506406) (@lem1506405)). Qed.
Lemma lem1506409 : term6 = term13.
Proof. exact (TRANS (@lem1506400) (@lem1506407)). Qed.
Lemma lem1506426 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1506427 : term12 = term12.
Proof. exact (fun_ext (fun x : real => @lem1506426 x)). Qed.
Lemma lem1506428 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506429 : term13 = term13.
Proof. exact (MK_COMB (@lem1506428) (@lem1506427)). Qed.
Lemma lem1506430 : term6 = term13.
Proof. exact (TRANS (@lem1506409) (@lem1506429)). Qed.
Lemma lem1506431 (x : real) : (term2 x) = (term14 x).
Proof. exact (@lem1483523 (real_neg x) x). Qed.
Lemma lem1506432 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506439 (x : real) : (real_neg x) = (term15 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1506440 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1506441 (x : real) : (term16 x) = (term17 x).
Proof. exact (MK_COMB (@lem1506440) (@lem1506439 x)). Qed.
Lemma lem1506442 (x : real) : (term18 x) = (term19 x).
Proof. exact (MK_COMB (@lem1506441 x) (@lem1506432 x)). Qed.
Lemma lem1506443 (x : real) : (term19 x) = (term20 x).
Proof. exact (@lem1483519 (term15 x) x). Qed.
Lemma lem1506447 (x : real) : (term20 x) = (term21 x).
Proof. exact (@lem1483438 term22 term22 x). Qed.
Lemma lem1506448 : term23 = term24.
Proof. exact (@lem1367763 term25 term25). Qed.
Lemma lem1506449 : term26 = term27.
Proof. exact (@lem706885). Qed.
Lemma lem1506450 : (term26 = term27) = (term28 = term29).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term27). Qed.
Lemma lem1506451 : term28 = term29.
Proof. exact (EQ_MP (@lem1506450) (@lem1506449)). Qed.
Lemma lem1506452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1506453 : term30 = term31.
Proof. exact (MK_COMB (@lem1506452) (@lem1506451)). Qed.
Lemma lem1506454 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1506455 : term24 = term32.
Proof. exact (MK_COMB (@lem1506454) (@lem1506453)). Qed.
Lemma lem1506456 : term23 = term32.
Proof. exact (TRANS (@lem1506448) (@lem1506455)). Qed.
Lemma lem1506457 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506458 : term33 = term34.
Proof. exact (MK_COMB (@lem1506457) (@lem1506456)). Qed.
Lemma lem1506459 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506460 (x : real) : (term21 x) = (term35 x).
Proof. exact (MK_COMB (@lem1506458) (@lem1506459 x)). Qed.
Lemma lem1506462 (x : real) : (term20 x) = (term35 x).
Proof. exact (TRANS (@lem1506447 x) (@lem1506460 x)). Qed.
Lemma lem1506463 (x : real) : (term19 x) = (term35 x).
Proof. exact (TRANS (@lem1506443 x) (@lem1506462 x)). Qed.
Lemma lem1506464 (x : real) : (term18 x) = (term35 x).
Proof. exact (TRANS (@lem1506442 x) (@lem1506463 x)). Qed.
Lemma lem1506465 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1506466 (x : real) : (term36 x) = (term37 x).
Proof. exact (MK_COMB (@lem1506465) (@lem1506464 x)). Qed.
Lemma lem1506467 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506468 (x : real) : (term14 x) = (term39 x).
Proof. exact (MK_COMB (@lem1506466 x) (@lem1506467)). Qed.
Lemma lem1506469 (x : real) : (term2 x) = (term39 x).
Proof. exact (TRANS (@lem1506431 x) (@lem1506468 x)). Qed.
Lemma lem1506470 (x : real) : (term40 x) = (term41 x).
Proof. exact (@lem1483533 x term38). Qed.
Lemma lem1506476 (x : real) : (term42 x) = (term43 x).
Proof. exact (@lem1483519 x term38). Qed.
Lemma lem1506478 (x : nat) : (term44 x) = term38.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1506479 : term45 = term38.
Proof. exact (@lem1506478 term25). Qed.
Lemma lem1506480 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1506481 (x : real) : (term43 x) = (term46 x).
Proof. exact (MK_COMB (@lem1506480 x) (@lem1506479)). Qed.
Lemma lem1506482 (x : real) : (term46 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1506483 (x : real) : (term43 x) = x.
Proof. exact (TRANS (@lem1506481 x) (@lem1506482 x)). Qed.
Lemma lem1506485 (x : real) : (term42 x) = x.
Proof. exact (TRANS (@lem1506476 x) (@lem1506483 x)). Qed.
Lemma lem1506486 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506487 (x : real) : (term47 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1506486) (@lem1506485 x)). Qed.
Lemma lem1506488 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506489 (x : real) : (term41 x) = (term48 x).
Proof. exact (MK_COMB (@lem1506487 x) (@lem1506488)). Qed.
Lemma lem1506490 (x : real) : (term40 x) = (term48 x).
Proof. exact (TRANS (@lem1506470 x) (@lem1506489 x)). Qed.
Lemma lem1506491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1506492 (x : real) : (term49 x) = (term50 x).
Proof. exact (MK_COMB (@lem1506491) (@lem1506469 x)). Qed.
Lemma lem1506493 (x : real) : (term51 x) = (term52 x).
Proof. exact (MK_COMB (@lem1506492 x) (@lem1506490 x)). Qed.
Lemma lem1506494 (x : real) : (term53 x) = (term54 x).
Proof. exact (@lem1483533 x (real_neg x)). Qed.
Lemma lem1506501 (x : real) : (real_neg x) = (term15 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1506504 (x : real) : (real_sub x) = (real_sub x).
Proof. exact (eq_refl (real_sub x)). Qed.
Lemma lem1506505 (x : real) : (term55 x) = (term56 x).
Proof. exact (MK_COMB (@lem1506504 x) (@lem1506501 x)). Qed.
Lemma lem1506506 (x : real) : (term56 x) = (term57 x).
Proof. exact (@lem1483519 x (term15 x)). Qed.
Lemma lem1506507 (x : real) : (term58 x) = (term59 x).
Proof. exact (@lem1483476 term22 term22 x). Qed.
Lemma lem1506509 (m : nat) (n : nat) : (term60 m n) = (term61 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1506510 : term62 = term63.
Proof. exact (@lem1506509 term25 term25). Qed.
Lemma lem1506511 : (term64 = (BIT1 0)) = (term65 = term25).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1506512 : term65 = term25.
Proof. exact (EQ_MP (@lem1506511) (@lem940073)). Qed.
Lemma lem1506513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1506514 : term63 = term66.
Proof. exact (MK_COMB (@lem1506513) (@lem1506512)). Qed.
Lemma lem1506515 : term62 = term66.
Proof. exact (TRANS (@lem1506510) (@lem1506514)). Qed.
Lemma lem1506516 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506517 : term67 = term68.
Proof. exact (MK_COMB (@lem1506516) (@lem1506515)). Qed.
Lemma lem1506518 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506519 (x : real) : (term59 x) = (term69 x).
Proof. exact (MK_COMB (@lem1506517) (@lem1506518 x)). Qed.
Lemma lem1506520 (x : real) : (term58 x) = (term69 x).
Proof. exact (TRANS (@lem1506507 x) (@lem1506519 x)). Qed.
Lemma lem1506521 (x : real) : (term69 x) = x.
Proof. exact (@lem1483436 x). Qed.
Lemma lem1506522 (x : real) : (term58 x) = x.
Proof. exact (TRANS (@lem1506520 x) (@lem1506521 x)). Qed.
Lemma lem1506523 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1506524 (x : real) : (term57 x) = (real_add x x).
Proof. exact (MK_COMB (@lem1506523 x) (@lem1506522 x)). Qed.
Lemma lem1506525 (x : real) : (real_add x x) = (term70 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1506526 : term71 = term30.
Proof. exact (@lem1367770 term25 term25). Qed.
Lemma lem1506527 : term26 = term27.
Proof. exact (@lem706885). Qed.
Lemma lem1506528 : (term26 = term27) = (term28 = term29).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term27). Qed.
Lemma lem1506529 : term28 = term29.
Proof. exact (EQ_MP (@lem1506528) (@lem1506527)). Qed.
Lemma lem1506530 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1506531 : term30 = term31.
Proof. exact (MK_COMB (@lem1506530) (@lem1506529)). Qed.
Lemma lem1506532 : term71 = term31.
Proof. exact (TRANS (@lem1506526) (@lem1506531)). Qed.
Lemma lem1506533 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506534 : term72 = term73.
Proof. exact (MK_COMB (@lem1506533) (@lem1506532)). Qed.
Lemma lem1506535 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506536 (x : real) : (term70 x) = (term74 x).
Proof. exact (MK_COMB (@lem1506534) (@lem1506535 x)). Qed.
Lemma lem1506537 (x : real) : (real_add x x) = (term74 x).
Proof. exact (TRANS (@lem1506525 x) (@lem1506536 x)). Qed.
Lemma lem1506538 (x : real) : (term57 x) = (term74 x).
Proof. exact (TRANS (@lem1506524 x) (@lem1506537 x)). Qed.
Lemma lem1506539 (x : real) : (term56 x) = (term74 x).
Proof. exact (TRANS (@lem1506506 x) (@lem1506538 x)). Qed.
Lemma lem1506540 (x : real) : (term55 x) = (term74 x).
Proof. exact (TRANS (@lem1506505 x) (@lem1506539 x)). Qed.
Lemma lem1506541 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506542 (x : real) : (term75 x) = (term76 x).
Proof. exact (MK_COMB (@lem1506541) (@lem1506540 x)). Qed.
Lemma lem1506543 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506544 (x : real) : (term54 x) = (term77 x).
Proof. exact (MK_COMB (@lem1506542 x) (@lem1506543)). Qed.
Lemma lem1506545 (x : real) : (term53 x) = (term77 x).
Proof. exact (TRANS (@lem1506494 x) (@lem1506544 x)). Qed.
Lemma lem1506546 (x : real) : (term3 x) = (term78 x).
Proof. exact (@lem1483523 term38 x). Qed.
Lemma lem1506552 (x : real) : (term79 x) = (term80 x).
Proof. exact (@lem1483519 term38 x). Qed.
Lemma lem1506557 (x : real) : (term80 x) = (term15 x).
Proof. exact (@lem1483448 (term15 x)). Qed.
Lemma lem1506559 (x : real) : (term79 x) = (term15 x).
Proof. exact (TRANS (@lem1506552 x) (@lem1506557 x)). Qed.
Lemma lem1506560 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1506561 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1506560) (@lem1506559 x)). Qed.
Lemma lem1506562 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506563 (x : real) : (term78 x) = (term83 x).
Proof. exact (MK_COMB (@lem1506561 x) (@lem1506562)). Qed.
Lemma lem1506564 (x : real) : (term3 x) = (term83 x).
Proof. exact (TRANS (@lem1506546 x) (@lem1506563 x)). Qed.
Lemma lem1506565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1506566 (x : real) : (term84 x) = (term85 x).
Proof. exact (MK_COMB (@lem1506565) (@lem1506545 x)). Qed.
Lemma lem1506567 (x : real) : (term86 x) = (term87 x).
Proof. exact (MK_COMB (@lem1506566 x) (@lem1506564 x)). Qed.
Lemma lem1506568 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506569 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1506568) (@lem1506493 x)). Qed.
Lemma lem1506570 (x : real) : (term1 x) = (term90 x).
Proof. exact (MK_COMB (@lem1506569 x) (@lem1506567 x)). Qed.
Lemma lem1506571 : term12 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506570 x)). Qed.
Lemma lem1506572 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506573 : term13 = term92.
Proof. exact (MK_COMB (@lem1506572) (@lem1506571)). Qed.
Lemma lem1506574 : term6 = term92.
Proof. exact (TRANS (@lem1506430) (@lem1506573)). Qed.
Lemma lem1506576 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term94 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1506577 (P : real -> Prop) (Q : real -> Prop) : (term95 P Q) = (term96 P Q).
Proof. exact (@lem1506576 real P Q). Qed.
Lemma lem1506578 : term97 = term98.
Proof. exact (@lem1506577 term99 term100). Qed.
Lemma lem1506579 (x : real) : (term101 x) = (term52 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506581 (x : real) : (term102 x) = (term89 x).
Proof. exact (MK_COMB (@lem1506580) (@lem1506579 x)). Qed.
Lemma lem1506582 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506583 (x : real) : (term104 x) = (term90 x).
Proof. exact (MK_COMB (@lem1506581 x) (@lem1506582 x)). Qed.
Lemma lem1506584 : term105 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506583 x)). Qed.
Lemma lem1506585 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506586 : term97 = term92.
Proof. exact (MK_COMB (@lem1506585) (@lem1506584)). Qed.
Lemma lem1506587 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1506588 : term106 = term107.
Proof. exact (MK_COMB (@lem1506587) (@lem1506586)). Qed.
Lemma lem1506589 (x : real) : (term101 x) = (term52 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506590 : term108 = term99.
Proof. exact (fun_ext (fun x : real => @lem1506589 x)). Qed.
Lemma lem1506591 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506592 : term109 = term110.
Proof. exact (MK_COMB (@lem1506591) (@lem1506590)). Qed.
Lemma lem1506593 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506594 : term111 = term112.
Proof. exact (MK_COMB (@lem1506593) (@lem1506592)). Qed.
Lemma lem1506595 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506596 : term113 = term100.
Proof. exact (fun_ext (fun x : real => @lem1506595 x)). Qed.
Lemma lem1506597 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506598 : term114 = term115.
Proof. exact (MK_COMB (@lem1506597) (@lem1506596)). Qed.
Lemma lem1506599 : term98 = term116.
Proof. exact (MK_COMB (@lem1506594) (@lem1506598)). Qed.
Lemma lem1506600 : (term97 = term98) = (term92 = term116).
Proof. exact (MK_COMB (@lem1506588) (@lem1506599)). Qed.
Lemma lem1506601 : term92 = term116.
Proof. exact (EQ_MP (@lem1506600) (@lem1506578)). Qed.
Lemma lem1506699 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term94 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1506700 (P : real -> Prop) (Q : real -> Prop) : (term96 P Q) = (term95 P Q).
Proof. exact (@lem1506699 real P Q). Qed.
Lemma lem1506701 : term98 = term97.
Proof. exact (@lem1506700 term99 term100). Qed.
Lemma lem1506702 (x : real) : (term101 x) = (term52 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506703 : term108 = term99.
Proof. exact (fun_ext (fun x : real => @lem1506702 x)). Qed.
Lemma lem1506704 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506705 : term109 = term110.
Proof. exact (MK_COMB (@lem1506704) (@lem1506703)). Qed.
Lemma lem1506706 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506707 : term111 = term112.
Proof. exact (MK_COMB (@lem1506706) (@lem1506705)). Qed.
Lemma lem1506708 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506709 : term113 = term100.
Proof. exact (fun_ext (fun x : real => @lem1506708 x)). Qed.
Lemma lem1506710 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506711 : term114 = term115.
Proof. exact (MK_COMB (@lem1506710) (@lem1506709)). Qed.
Lemma lem1506712 : term98 = term116.
Proof. exact (MK_COMB (@lem1506707) (@lem1506711)). Qed.
Lemma lem1506713 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1506714 : term117 = term118.
Proof. exact (MK_COMB (@lem1506713) (@lem1506712)). Qed.
Lemma lem1506715 (x : real) : (term101 x) = (term52 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1506716 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1506717 (x : real) : (term102 x) = (term89 x).
Proof. exact (MK_COMB (@lem1506716) (@lem1506715 x)). Qed.
Lemma lem1506718 (x : real) : (term103 x) = (term87 x).
Proof. exact (eq_refl (term103 x)). Qed.
Lemma lem1506719 (x : real) : (term104 x) = (term90 x).
Proof. exact (MK_COMB (@lem1506717 x) (@lem1506718 x)). Qed.
Lemma lem1506720 : term105 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506719 x)). Qed.
Lemma lem1506721 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506722 : term97 = term92.
Proof. exact (MK_COMB (@lem1506721) (@lem1506720)). Qed.
Lemma lem1506723 : (term98 = term97) = (term116 = term92).
Proof. exact (MK_COMB (@lem1506714) (@lem1506722)). Qed.
Lemma lem1506724 : term116 = term92.
Proof. exact (EQ_MP (@lem1506723) (@lem1506701)). Qed.
Lemma lem1506725 : term92 = term92.
Proof. exact (TRANS (@lem1506601) (@lem1506724)). Qed.
Lemma lem1506728 : term6 = term92.
Proof. exact (TRANS (@lem1506574) (@lem1506725)). Qed.
Lemma lem1506745 (x : real) : (term90 x) = (term90 x).
Proof. exact (eq_refl (term90 x)). Qed.
Lemma lem1506746 : term91 = term91.
Proof. exact (fun_ext (fun x : real => @lem1506745 x)). Qed.
Lemma lem1506747 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1506748 : term92 = term92.
Proof. exact (MK_COMB (@lem1506747) (@lem1506746)). Qed.
Lemma lem1506749 : term6 = term92.
Proof. exact (TRANS (@lem1506728) (@lem1506748)). Qed.
Lemma lem1506759 (x : real) (h1 : term90 x) : term90 x.
Proof. exact (h1). Qed.
Lemma lem1506760 (x : real) (h1 : term52 x) : term52 x.
Proof. exact (h1). Qed.
Lemma lem1506761 (x : real) (h1 : term52 x) : term48 x.
Proof. exact (proj2 (@lem1506760 x h1)). Qed.
Lemma lem1506762 (x : real) (h1 : term52 x) : term39 x.
Proof. exact (proj1 (@lem1506760 x h1)). Qed.
Lemma lem1506764 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506765 : term120 = term121.
Proof. exact (@lem1506764 (NUMERAL 0) term25). Qed.
Lemma lem1506766 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1506767 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1506768 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem1506767 h1) (fun h1 : term121 = True => @lem1506766)). Qed.
Lemma lem1506769 : term121 = True.
Proof. exact (EQ_MP (@lem1506768) (@lem1506766)). Qed.
Lemma lem1506770 : term120 = True.
Proof. exact (TRANS (@lem1506765) (@lem1506769)). Qed.
Lemma lem1506771 : True = term120.
Proof. exact (SYM (@lem1506770)). Qed.
Lemma lem1506772 : term120.
Proof. exact (EQ_MP (@lem1506771) (@lem0)). Qed.
Lemma lem1506773 (x : real) (h1 : term52 x) : term123 x.
Proof. exact (conj (@lem1506772) (@lem1506762 x h1)). Qed.
Lemma lem1506775 (x : real) (y : real) : term124 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1506776 (x : real) : term125 x.
Proof. exact (@lem1506775 term66 (term35 x)). Qed.
Lemma lem1506777 (x : real) (h1 : term52 x) : term126 x.
Proof. exact (@lem1506776 x (@lem1506773 x h1)). Qed.
Lemma lem1506778 (x : real) : (term127 x) = (term35 x).
Proof. exact (@lem1483460 (term35 x)). Qed.
Lemma lem1506779 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1506780 (x : real) : (term128 x) = (term37 x).
Proof. exact (MK_COMB (@lem1506779) (@lem1506778 x)). Qed.
Lemma lem1506781 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506782 (x : real) : (term126 x) = (term39 x).
Proof. exact (MK_COMB (@lem1506780 x) (@lem1506781)). Qed.
Lemma lem1506783 (x : real) (h1 : term52 x) : term39 x.
Proof. exact (EQ_MP (@lem1506782 x) (@lem1506777 x h1)). Qed.
Lemma lem1506785 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506786 : term129 = term130.
Proof. exact (@lem1506785 (NUMERAL 0) term29). Qed.
Lemma lem1506787 : term131 = term27.
Proof. exact (@lem912803). Qed.
Lemma lem1506788 (h1 : term131 = term27) : term130 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term27 h1). Qed.
Lemma lem1506789 : (term131 = term27) = (term130 = True).
Proof. exact (prop_ext (fun h1 : term131 = term27 => @lem1506788 h1) (fun h1 : term130 = True => @lem1506787)). Qed.
Lemma lem1506790 : term130 = True.
Proof. exact (EQ_MP (@lem1506789) (@lem1506787)). Qed.
Lemma lem1506791 : term129 = True.
Proof. exact (TRANS (@lem1506786) (@lem1506790)). Qed.
Lemma lem1506792 : True = term129.
Proof. exact (SYM (@lem1506791)). Qed.
Lemma lem1506793 : term129.
Proof. exact (EQ_MP (@lem1506792) (@lem0)). Qed.
Lemma lem1506794 (x : real) (h1 : term52 x) : term132 x.
Proof. exact (conj (@lem1506793) (@lem1506761 x h1)). Qed.
Lemma lem1506796 (x : real) (y : real) : term133 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1506797 (x : real) : term134 x.
Proof. exact (@lem1506796 term31 x). Qed.
Lemma lem1506804 (x : real) (h1 : term52 x) : term77 x.
Proof. exact (@lem1506797 x (@lem1506794 x h1)). Qed.
Lemma lem1506805 (x : real) (h1 : term52 x) : term135 x.
Proof. exact (conj (@lem1506804 x h1) (@lem1506783 x h1)). Qed.
Lemma lem1506807 (x : real) (y : real) : term136 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1506808 (x : real) : term137 x.
Proof. exact (@lem1506807 (term74 x) (term35 x)). Qed.
Lemma lem1506809 (x : real) (h1 : term52 x) : term138 x.
Proof. exact (@lem1506808 x (@lem1506805 x h1)). Qed.
Lemma lem1506810 (x : real) : (term139 x) = (term140 x).
Proof. exact (@lem1483438 term31 term32 x). Qed.
Lemma lem1506812 (m : nat) : (term141 m) = term38.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1506813 : term142 = term38.
Proof. exact (@lem1506812 term29). Qed.
Lemma lem1506814 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506815 : term143 = term144.
Proof. exact (MK_COMB (@lem1506814) (@lem1506813)). Qed.
Lemma lem1506816 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506817 (x : real) : (term140 x) = (term145 x).
Proof. exact (MK_COMB (@lem1506815) (@lem1506816 x)). Qed.
Lemma lem1506818 (x : real) : (term139 x) = (term145 x).
Proof. exact (TRANS (@lem1506810 x) (@lem1506817 x)). Qed.
Lemma lem1506819 (x : real) : (term145 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1506820 (x : real) : (term139 x) = term38.
Proof. exact (TRANS (@lem1506818 x) (@lem1506819 x)). Qed.
Lemma lem1506821 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506822 (x : real) : (term146 x) = term147.
Proof. exact (MK_COMB (@lem1506821) (@lem1506820 x)). Qed.
Lemma lem1506823 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506824 (x : real) : (term138 x) = term148.
Proof. exact (MK_COMB (@lem1506822 x) (@lem1506823)). Qed.
Lemma lem1506825 (x : real) (h1 : term52 x) : term148.
Proof. exact (EQ_MP (@lem1506824 x) (@lem1506809 x h1)). Qed.
Lemma lem1506827 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506828 : term148 = term149.
Proof. exact (@lem1506827 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1506829 : term149 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1506830 : term148 = False.
Proof. exact (TRANS (@lem1506828) (@lem1506829)). Qed.
Lemma lem1506831 (x : real) (h1 : term52 x) : False.
Proof. exact (EQ_MP (@lem1506830) (@lem1506825 x h1)). Qed.
Lemma lem1506832 (x : real) (h1 : term87 x) : term87 x.
Proof. exact (h1). Qed.
Lemma lem1506833 (x : real) (h1 : term87 x) : term83 x.
Proof. exact (proj2 (@lem1506832 x h1)). Qed.
Lemma lem1506834 (x : real) (h1 : term87 x) : term77 x.
Proof. exact (proj1 (@lem1506832 x h1)). Qed.
Lemma lem1506836 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506837 : term129 = term130.
Proof. exact (@lem1506836 (NUMERAL 0) term29). Qed.
Lemma lem1506838 : term131 = term27.
Proof. exact (@lem912803). Qed.
Lemma lem1506839 (h1 : term131 = term27) : term130 = True.
Proof. exact (@lem1009824 (BIT1 0) 0 term27 h1). Qed.
Lemma lem1506840 : (term131 = term27) = (term130 = True).
Proof. exact (prop_ext (fun h1 : term131 = term27 => @lem1506839 h1) (fun h1 : term130 = True => @lem1506838)). Qed.
Lemma lem1506841 : term130 = True.
Proof. exact (EQ_MP (@lem1506840) (@lem1506838)). Qed.
Lemma lem1506842 : term129 = True.
Proof. exact (TRANS (@lem1506837) (@lem1506841)). Qed.
Lemma lem1506843 : True = term129.
Proof. exact (SYM (@lem1506842)). Qed.
Lemma lem1506844 : term129.
Proof. exact (EQ_MP (@lem1506843) (@lem0)). Qed.
Lemma lem1506845 (x : real) (h1 : term87 x) : term150 x.
Proof. exact (conj (@lem1506844) (@lem1506833 x h1)). Qed.
Lemma lem1506847 (x : real) (y : real) : term124 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1506848 (x : real) : term151 x.
Proof. exact (@lem1506847 term31 (term15 x)). Qed.
Lemma lem1506849 (x : real) (h1 : term87 x) : term152 x.
Proof. exact (@lem1506848 x (@lem1506845 x h1)). Qed.
Lemma lem1506850 (x : real) : (term153 x) = (term154 x).
Proof. exact (@lem1483476 term31 term22 x). Qed.
Lemma lem1506852 (m : nat) (n : nat) : (term155 m n) = (term156 m n).
Proof. exact (proj2 (@lem1367247 m n)). Qed.
Lemma lem1506853 : term157 = term158.
Proof. exact (@lem1506852 term29 term25). Qed.
Lemma lem1506854 : term159 = term27.
Proof. exact (@lem996237 term27). Qed.
Lemma lem1506855 : (term159 = term27) = (term160 = term29).
Proof. exact (@lem1007663 term27 (BIT1 0) term27). Qed.
Lemma lem1506856 : term160 = term29.
Proof. exact (EQ_MP (@lem1506855) (@lem1506854)). Qed.
Lemma lem1506857 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1506858 : term161 = term31.
Proof. exact (MK_COMB (@lem1506857) (@lem1506856)). Qed.
Lemma lem1506859 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1506860 : term158 = term32.
Proof. exact (MK_COMB (@lem1506859) (@lem1506858)). Qed.
Lemma lem1506861 : term157 = term32.
Proof. exact (TRANS (@lem1506853) (@lem1506860)). Qed.
Lemma lem1506862 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506863 : term162 = term34.
Proof. exact (MK_COMB (@lem1506862) (@lem1506861)). Qed.
Lemma lem1506864 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506865 (x : real) : (term154 x) = (term35 x).
Proof. exact (MK_COMB (@lem1506863) (@lem1506864 x)). Qed.
Lemma lem1506866 (x : real) : (term153 x) = (term35 x).
Proof. exact (TRANS (@lem1506850 x) (@lem1506865 x)). Qed.
Lemma lem1506867 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1506868 (x : real) : (term163 x) = (term37 x).
Proof. exact (MK_COMB (@lem1506867) (@lem1506866 x)). Qed.
Lemma lem1506869 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506870 (x : real) : (term152 x) = (term39 x).
Proof. exact (MK_COMB (@lem1506868 x) (@lem1506869)). Qed.
Lemma lem1506871 (x : real) (h1 : term87 x) : term39 x.
Proof. exact (EQ_MP (@lem1506870 x) (@lem1506849 x h1)). Qed.
Lemma lem1506873 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506874 : term120 = term121.
Proof. exact (@lem1506873 (NUMERAL 0) term25). Qed.
Lemma lem1506875 : term122 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1506876 (h1 : term122 = (BIT1 0)) : term121 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1506877 : (term122 = (BIT1 0)) = (term121 = True).
Proof. exact (prop_ext (fun h1 : term122 = (BIT1 0) => @lem1506876 h1) (fun h1 : term121 = True => @lem1506875)). Qed.
Lemma lem1506878 : term121 = True.
Proof. exact (EQ_MP (@lem1506877) (@lem1506875)). Qed.
Lemma lem1506879 : term120 = True.
Proof. exact (TRANS (@lem1506874) (@lem1506878)). Qed.
Lemma lem1506880 : True = term120.
Proof. exact (SYM (@lem1506879)). Qed.
Lemma lem1506881 : term120.
Proof. exact (EQ_MP (@lem1506880) (@lem0)). Qed.
Lemma lem1506882 (x : real) (h1 : term87 x) : term164 x.
Proof. exact (conj (@lem1506881) (@lem1506834 x h1)). Qed.
Lemma lem1506884 (x : real) (y : real) : term133 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1506885 (x : real) : term165 x.
Proof. exact (@lem1506884 term66 (term74 x)). Qed.
Lemma lem1506886 (x : real) (h1 : term87 x) : term166 x.
Proof. exact (@lem1506885 x (@lem1506882 x h1)). Qed.
Lemma lem1506887 (x : real) : (term167 x) = (term74 x).
Proof. exact (@lem1483460 (term74 x)). Qed.
Lemma lem1506888 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506889 (x : real) : (term168 x) = (term76 x).
Proof. exact (MK_COMB (@lem1506888) (@lem1506887 x)). Qed.
Lemma lem1506890 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506891 (x : real) : (term166 x) = (term77 x).
Proof. exact (MK_COMB (@lem1506889 x) (@lem1506890)). Qed.
Lemma lem1506892 (x : real) (h1 : term87 x) : term77 x.
Proof. exact (EQ_MP (@lem1506891 x) (@lem1506886 x h1)). Qed.
Lemma lem1506893 (x : real) (h1 : term87 x) : term135 x.
Proof. exact (conj (@lem1506892 x h1) (@lem1506871 x h1)). Qed.
Lemma lem1506895 (x : real) (y : real) : term136 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1506896 (x : real) : term137 x.
Proof. exact (@lem1506895 (term74 x) (term35 x)). Qed.
Lemma lem1506897 (x : real) (h1 : term87 x) : term138 x.
Proof. exact (@lem1506896 x (@lem1506893 x h1)). Qed.
Lemma lem1506898 (x : real) : (term139 x) = (term140 x).
Proof. exact (@lem1483438 term31 term32 x). Qed.
Lemma lem1506900 (m : nat) : (term141 m) = term38.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem1506901 : term142 = term38.
Proof. exact (@lem1506900 term29). Qed.
Lemma lem1506902 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1506903 : term143 = term144.
Proof. exact (MK_COMB (@lem1506902) (@lem1506901)). Qed.
Lemma lem1506904 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1506905 (x : real) : (term140 x) = (term145 x).
Proof. exact (MK_COMB (@lem1506903) (@lem1506904 x)). Qed.
Lemma lem1506906 (x : real) : (term139 x) = (term145 x).
Proof. exact (TRANS (@lem1506898 x) (@lem1506905 x)). Qed.
Lemma lem1506907 (x : real) : (term145 x) = term38.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1506908 (x : real) : (term139 x) = term38.
Proof. exact (TRANS (@lem1506906 x) (@lem1506907 x)). Qed.
Lemma lem1506909 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1506910 (x : real) : (term146 x) = term147.
Proof. exact (MK_COMB (@lem1506909) (@lem1506908 x)). Qed.
Lemma lem1506911 : term38 = term38.
Proof. exact (eq_refl term38). Qed.
Lemma lem1506912 (x : real) : (term138 x) = term148.
Proof. exact (MK_COMB (@lem1506910 x) (@lem1506911)). Qed.
Lemma lem1506913 (x : real) (h1 : term87 x) : term148.
Proof. exact (EQ_MP (@lem1506912 x) (@lem1506897 x h1)). Qed.
Lemma lem1506915 (n : nat) (m : nat) : (term119 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1506916 : term148 = term149.
Proof. exact (@lem1506915 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1506917 : term149 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1506918 : term148 = False.
Proof. exact (TRANS (@lem1506916) (@lem1506917)). Qed.
Lemma lem1506919 (x : real) (h1 : term87 x) : False.
Proof. exact (EQ_MP (@lem1506918) (@lem1506913 x h1)). Qed.
Lemma lem1506920 (x : real) (h1 : term90 x) : False.
Proof. exact (or_elim (@lem1506759 x h1) (fun h0 : term52 x => @lem1506831 x h0) (fun h0 : term87 x => @lem1506919 x h0)). Qed.
Lemma lem1506922 (x : real) (h1 : term90 x) : term90 x.
Proof. exact (h1). Qed.
Lemma lem1506923 (x : real) (h1 : term90 x) : (term90 x) = False.
Proof. exact (prop_ext (fun h2 : term90 x => @lem1506920 x h1) (fun h2 : False => @lem1506922 x h1)). Qed.
Lemma lem1506924 (x : real) (h1 : term90 x) : False.
Proof. exact (EQ_MP (@lem1506923 x h1) (@lem1506922 x h1)). Qed.
Lemma lem1506925 (h1 : term92) : term92.
Proof. exact (h1). Qed.
Lemma lem1506926 (h1 : term92) : False.
Proof. exact (ex_elim (@lem1506925 h1) (fun x : real => fun h0 : term91 x => @lem1506924 x h0)). Qed.
Lemma lem1506927 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1506928 (h1 : term6) : term92.
Proof. exact (EQ_MP (@lem1506749) (@lem1506927 h1)). Qed.
Lemma lem1506929 (h1 : term6) : term92 = False.
Proof. exact (prop_ext (fun h2 : term92 => @lem1506926 h2) (fun h2 : False => @lem1506928 h1)). Qed.
Lemma lem1506930 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1506929 h1) (@lem1506928 h1)). Qed.
Lemma lem1506931 : term169.
Proof. exact (fun h0 : term6 => @lem1506930 h0). Qed.
Lemma lem1506932 : term170.
Proof. exact (@lem1386578 term171). Qed.
Lemma lem1506933 : term171.
Proof. exact (@lem1506932 (@lem1506931)). Qed.
