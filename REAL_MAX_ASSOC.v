Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MAX_ASSOC_term_abbrevs.
Require Import thm1008952_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482686_spec.
Require Import thm1482709_spec.
Require Import thm1482710_spec.
Require Import thm1483205_spec.
Require Import thm1483436_spec.
Require Import thm1483440_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483476_spec.
Require Import thm1483488_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483554_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm940073_spec.
Lemma lem1571480 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1571481 (x : real) (y : real) : (term2 x y) = (term3 x y).
Proof. exact (@lem1571480 (term4 x y)). Qed.
Lemma lem1571482 (x : real) (y : real) (z : real) : (term5 x y z) = ((term6 x y z) = (term7 x y z)).
Proof. exact (eq_refl (term5 x y z)). Qed.
Lemma lem1571483 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1571485 (x : real) (y : real) (z : real) : (term8 x y z) = (term9 x y z).
Proof. exact (MK_COMB (@lem1571483) (@lem1571482 x y z)). Qed.
Lemma lem1571486 (x : real) (y : real) : (term10 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1571485 x y z)). Qed.
Lemma lem1571487 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571488 (x : real) (y : real) : (term3 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1571487) (@lem1571486 x y)). Qed.
Lemma lem1571489 (x : real) (y : real) : (term2 x y) = (term12 x y).
Proof. exact (TRANS (@lem1571481 x y) (@lem1571488 x y)). Qed.
Lemma lem1571490 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1571491 (x : real) : (term13 x) = (term14 x).
Proof. exact (@lem1571490 (term15 x)). Qed.
Lemma lem1571492 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (eq_refl (term16 x y)). Qed.
Lemma lem1571493 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1571494 (x : real) (y : real) : (term18 x y) = (term2 x y).
Proof. exact (MK_COMB (@lem1571493) (@lem1571492 x y)). Qed.
Lemma lem1571495 (x : real) (y : real) : (term18 x y) = (term12 x y).
Proof. exact (TRANS (@lem1571494 x y) (@lem1571489 x y)). Qed.
Lemma lem1571496 (x : real) : (term19 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1571495 x y)). Qed.
Lemma lem1571497 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571498 (x : real) : (term14 x) = (term21 x).
Proof. exact (MK_COMB (@lem1571497) (@lem1571496 x)). Qed.
Lemma lem1571499 (x : real) : (term13 x) = (term21 x).
Proof. exact (TRANS (@lem1571491 x) (@lem1571498 x)). Qed.
Lemma lem1571500 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1571501 : term22 = term23.
Proof. exact (@lem1571500 term24). Qed.
Lemma lem1571502 (x : real) : (term25 x) = (term26 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1571503 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1571504 (x : real) : (term27 x) = (term13 x).
Proof. exact (MK_COMB (@lem1571503) (@lem1571502 x)). Qed.
Lemma lem1571505 (x : real) : (term27 x) = (term21 x).
Proof. exact (TRANS (@lem1571504 x) (@lem1571499 x)). Qed.
Lemma lem1571506 : term28 = term29.
Proof. exact (fun_ext (fun x : real => @lem1571505 x)). Qed.
Lemma lem1571507 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571508 : term23 = term30.
Proof. exact (MK_COMB (@lem1571507) (@lem1571506)). Qed.
Lemma lem1571510 : term22 = term30.
Proof. exact (TRANS (@lem1571501) (@lem1571508)). Qed.
Lemma lem1571513 (x : real) (y : real) (z : real) : (term9 x y z) = (term9 x y z).
Proof. exact (eq_refl (term9 x y z)). Qed.
Lemma lem1571514 (x : real) (y : real) : (term11 x y) = (term11 x y).
Proof. exact (fun_ext (fun z : real => @lem1571513 x y z)). Qed.
Lemma lem1571515 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571516 (x : real) (y : real) : (term12 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1571515) (@lem1571514 x y)). Qed.
Lemma lem1571517 (x : real) : (term20 x) = (term20 x).
Proof. exact (fun_ext (fun y : real => @lem1571516 x y)). Qed.
Lemma lem1571518 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571519 (x : real) : (term21 x) = (term21 x).
Proof. exact (MK_COMB (@lem1571518) (@lem1571517 x)). Qed.
Lemma lem1571520 : term29 = term29.
Proof. exact (fun_ext (fun x : real => @lem1571519 x)). Qed.
Lemma lem1571521 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571522 : term30 = term30.
Proof. exact (MK_COMB (@lem1571521) (@lem1571520)). Qed.
Lemma lem1571523 : term22 = term30.
Proof. exact (TRANS (@lem1571510) (@lem1571522)). Qed.
Lemma lem1571524 (x : real) (y : real) (z : real) : (term9 x y z) = (term31 x y z).
Proof. exact (@lem1483554 (term6 x y z) (term7 x y z)). Qed.
Lemma lem1571537 (x : real) (y : real) (z : real) : (term32 x y z) = (term33 x y z).
Proof. exact (@lem1483519 (term6 x y z) (term7 x y z)). Qed.
Lemma lem1571538 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1571539 (x : real) (y : real) (z : real) : (term34 x y z) = (term35 x y z).
Proof. exact (MK_COMB (@lem1571538) (@lem1571537 x y z)). Qed.
Lemma lem1571540 (x : real) (y : real) (z : real) : (term35 x y z) = (term36 x y z).
Proof. exact (@lem1483512 (term33 x y z)). Qed.
Lemma lem1571541 (x : real) (y : real) (z : real) : (term36 x y z) = (term37 x y z).
Proof. exact (@lem1483508 (term6 x y z) term38 (term39 x y z)). Qed.
Lemma lem1571542 (x : real) (y : real) (z : real) : (term40 x y z) = (term41 x y z).
Proof. exact (@lem1483476 term38 term38 (term7 x y z)). Qed.
Lemma lem1571544 (m : nat) (n : nat) : (term42 m n) = (term43 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem1571545 : term44 = term45.
Proof. exact (@lem1571544 term46 term46). Qed.
Lemma lem1571546 : (term47 = (BIT1 0)) = (term48 = term46).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem1571547 : term48 = term46.
Proof. exact (EQ_MP (@lem1571546) (@lem940073)). Qed.
Lemma lem1571548 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1571549 : term45 = term49.
Proof. exact (MK_COMB (@lem1571548) (@lem1571547)). Qed.
Lemma lem1571550 : term44 = term49.
Proof. exact (TRANS (@lem1571545) (@lem1571549)). Qed.
Lemma lem1571551 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1571552 : term50 = term51.
Proof. exact (MK_COMB (@lem1571551) (@lem1571550)). Qed.
Lemma lem1571553 (x : real) (y : real) (z : real) : (term7 x y z) = (term7 x y z).
Proof. exact (eq_refl (term7 x y z)). Qed.
Lemma lem1571554 (x : real) (y : real) (z : real) : (term41 x y z) = (term52 x y z).
Proof. exact (MK_COMB (@lem1571552) (@lem1571553 x y z)). Qed.
Lemma lem1571555 (x : real) (y : real) (z : real) : (term40 x y z) = (term52 x y z).
Proof. exact (TRANS (@lem1571542 x y z) (@lem1571554 x y z)). Qed.
Lemma lem1571556 (x : real) (y : real) (z : real) : (term52 x y z) = (term7 x y z).
Proof. exact (@lem1483436 (term7 x y z)). Qed.
Lemma lem1571557 (x : real) (y : real) (z : real) : (term40 x y z) = (term7 x y z).
Proof. exact (TRANS (@lem1571555 x y z) (@lem1571556 x y z)). Qed.
Lemma lem1571560 (x : real) (y : real) (z : real) : (term53 x y z) = (term53 x y z).
Proof. exact (eq_refl (term53 x y z)). Qed.
Lemma lem1571561 (x : real) (y : real) (z : real) : (term37 x y z) = (term54 x y z).
Proof. exact (MK_COMB (@lem1571560 x y z) (@lem1571557 x y z)). Qed.
Lemma lem1571562 (x : real) (y : real) (z : real) : (term36 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1571541 x y z) (@lem1571561 x y z)). Qed.
Lemma lem1571563 (x : real) (y : real) (z : real) : (term35 x y z) = (term54 x y z).
Proof. exact (TRANS (@lem1571540 x y z) (@lem1571562 x y z)). Qed.
Lemma lem1571564 (x : real) (y : real) (z : real) : (term55 x y z) = (term55 x y z).
Proof. exact (eq_refl (term55 x y z)). Qed.
Lemma lem1571565 (x : real) (y : real) (z : real) : ((term34 x y z) = (term35 x y z)) = ((term34 x y z) = (term54 x y z)).
Proof. exact (MK_COMB (@lem1571564 x y z) (@lem1571563 x y z)). Qed.
Lemma lem1571566 (x : real) (y : real) (z : real) : (term34 x y z) = (term54 x y z).
Proof. exact (EQ_MP (@lem1571565 x y z) (@lem1571539 x y z)). Qed.
Lemma lem1571567 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571568 (x : real) (y : real) (z : real) : (term56 x y z) = (term57 x y z).
Proof. exact (MK_COMB (@lem1571567) (@lem1571566 x y z)). Qed.
Lemma lem1571569 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571570 (x : real) (y : real) (z : real) : (term59 x y z) = (term60 x y z).
Proof. exact (MK_COMB (@lem1571568 x y z) (@lem1571569)). Qed.
Lemma lem1571571 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571572 (x : real) (y : real) (z : real) : (term61 x y z) = (term62 x y z).
Proof. exact (MK_COMB (@lem1571571) (@lem1571537 x y z)). Qed.
Lemma lem1571573 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571574 (x : real) (y : real) (z : real) : (term63 x y z) = (term64 x y z).
Proof. exact (MK_COMB (@lem1571572 x y z) (@lem1571573)). Qed.
Lemma lem1571575 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571576 (x : real) (y : real) (z : real) : (term65 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1571575) (@lem1571574 x y z)). Qed.
Lemma lem1571577 (x : real) (y : real) (z : real) : (term31 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1571576 x y z) (@lem1571570 x y z)). Qed.
Lemma lem1571578 (x : real) (y : real) (z : real) : (term9 x y z) = (term67 x y z).
Proof. exact (TRANS (@lem1571524 x y z) (@lem1571577 x y z)). Qed.
Lemma lem1571579 (x : real) (y : real) : (term11 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1571578 x y z)). Qed.
Lemma lem1571580 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571581 (x : real) (y : real) : (term12 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1571580) (@lem1571579 x y)). Qed.
Lemma lem1571582 (x : real) : (term20 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1571581 x y)). Qed.
Lemma lem1571583 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571584 (x : real) : (term21 x) = (term71 x).
Proof. exact (MK_COMB (@lem1571583) (@lem1571582 x)). Qed.
Lemma lem1571585 : term29 = term72.
Proof. exact (fun_ext (fun x : real => @lem1571584 x)). Qed.
Lemma lem1571586 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571587 : term30 = term73.
Proof. exact (MK_COMB (@lem1571586) (@lem1571585)). Qed.
Lemma lem1571588 : term22 = term73.
Proof. exact (TRANS (@lem1571523) (@lem1571587)). Qed.
Lemma lem1571598 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1571599 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1571598 real P Q). Qed.
Lemma lem1571600 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (@lem1571599 (term80 x y) (term81 x y)). Qed.
Lemma lem1571601 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1571602 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571603 (x : real) (y : real) (z : real) : (term83 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1571602) (@lem1571601 x y z)). Qed.
Lemma lem1571604 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1571605 (x : real) (y : real) (z : real) : (term85 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1571603 x y z) (@lem1571604 x y z)). Qed.
Lemma lem1571606 (x : real) (y : real) : (term86 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1571605 x y z)). Qed.
Lemma lem1571607 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571608 (x : real) (y : real) : (term78 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1571607) (@lem1571606 x y)). Qed.
Lemma lem1571609 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1571610 (x : real) (y : real) : (term87 x y) = (term88 x y).
Proof. exact (MK_COMB (@lem1571609) (@lem1571608 x y)). Qed.
Lemma lem1571611 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1571612 (x : real) (y : real) : (term89 x y) = (term80 x y).
Proof. exact (fun_ext (fun z : real => @lem1571611 x y z)). Qed.
Lemma lem1571613 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571614 (x : real) (y : real) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1571613) (@lem1571612 x y)). Qed.
Lemma lem1571615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571616 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1571615) (@lem1571614 x y)). Qed.
Lemma lem1571617 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1571618 (x : real) (y : real) : (term94 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1571617 x y z)). Qed.
Lemma lem1571619 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571620 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1571619) (@lem1571618 x y)). Qed.
Lemma lem1571621 (x : real) (y : real) : (term79 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1571616 x y) (@lem1571620 x y)). Qed.
Lemma lem1571622 (x : real) (y : real) : ((term78 x y) = (term79 x y)) = ((term69 x y) = (term97 x y)).
Proof. exact (MK_COMB (@lem1571610 x y) (@lem1571621 x y)). Qed.
Lemma lem1571623 (x : real) (y : real) : (term69 x y) = (term97 x y).
Proof. exact (EQ_MP (@lem1571622 x y) (@lem1571600 x y)). Qed.
Lemma lem1571632 (x : real) : (term70 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1571623 x y)). Qed.
Lemma lem1571633 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571634 (x : real) : (term71 x) = (term99 x).
Proof. exact (MK_COMB (@lem1571633) (@lem1571632 x)). Qed.
Lemma lem1571636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1571637 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1571636 real P Q). Qed.
Lemma lem1571638 (x : real) : (term100 x) = (term101 x).
Proof. exact (@lem1571637 (term102 x) (term103 x)). Qed.
Lemma lem1571639 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1571640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571641 (x : real) (y : real) : (term105 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1571640) (@lem1571639 x y)). Qed.
Lemma lem1571642 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1571643 (x : real) (y : real) : (term107 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1571641 x y) (@lem1571642 x y)). Qed.
Lemma lem1571644 (x : real) : (term108 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1571643 x y)). Qed.
Lemma lem1571645 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571646 (x : real) : (term100 x) = (term99 x).
Proof. exact (MK_COMB (@lem1571645) (@lem1571644 x)). Qed.
Lemma lem1571647 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1571648 (x : real) : (term109 x) = (term110 x).
Proof. exact (MK_COMB (@lem1571647) (@lem1571646 x)). Qed.
Lemma lem1571649 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1571650 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1571649 x y)). Qed.
Lemma lem1571651 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571652 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1571651) (@lem1571650 x)). Qed.
Lemma lem1571653 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571654 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1571653) (@lem1571652 x)). Qed.
Lemma lem1571655 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1571656 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1571655 x y)). Qed.
Lemma lem1571657 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571658 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1571657) (@lem1571656 x)). Qed.
Lemma lem1571659 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1571654 x) (@lem1571658 x)). Qed.
Lemma lem1571660 (x : real) : ((term100 x) = (term101 x)) = ((term99 x) = (term119 x)).
Proof. exact (MK_COMB (@lem1571648 x) (@lem1571659 x)). Qed.
Lemma lem1571661 (x : real) : (term99 x) = (term119 x).
Proof. exact (EQ_MP (@lem1571660 x) (@lem1571638 x)). Qed.
Lemma lem1571678 (x : real) : (term71 x) = (term119 x).
Proof. exact (TRANS (@lem1571634 x) (@lem1571661 x)). Qed.
Lemma lem1571679 : term72 = term120.
Proof. exact (fun_ext (fun x : real => @lem1571678 x)). Qed.
Lemma lem1571680 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571681 : term73 = term121.
Proof. exact (MK_COMB (@lem1571680) (@lem1571679)). Qed.
Lemma lem1571683 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term74 A P Q) = (term75 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1571684 (P : real -> Prop) (Q : real -> Prop) : (term76 P Q) = (term77 P Q).
Proof. exact (@lem1571683 real P Q). Qed.
Lemma lem1571685 : term122 = term123.
Proof. exact (@lem1571684 term124 term125). Qed.
Lemma lem1571686 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1571687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571688 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1571687) (@lem1571686 x)). Qed.
Lemma lem1571689 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1571690 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1571688 x) (@lem1571689 x)). Qed.
Lemma lem1571691 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1571690 x)). Qed.
Lemma lem1571692 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571693 : term122 = term121.
Proof. exact (MK_COMB (@lem1571692) (@lem1571691)). Qed.
Lemma lem1571694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1571695 : term131 = term132.
Proof. exact (MK_COMB (@lem1571694) (@lem1571693)). Qed.
Lemma lem1571696 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1571697 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1571696 x)). Qed.
Lemma lem1571698 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571699 : term134 = term135.
Proof. exact (MK_COMB (@lem1571698) (@lem1571697)). Qed.
Lemma lem1571700 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571701 : term136 = term137.
Proof. exact (MK_COMB (@lem1571700) (@lem1571699)). Qed.
Lemma lem1571702 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1571703 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1571702 x)). Qed.
Lemma lem1571704 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571705 : term139 = term140.
Proof. exact (MK_COMB (@lem1571704) (@lem1571703)). Qed.
Lemma lem1571706 : term123 = term141.
Proof. exact (MK_COMB (@lem1571701) (@lem1571705)). Qed.
Lemma lem1571707 : (term122 = term123) = (term121 = term141).
Proof. exact (MK_COMB (@lem1571695) (@lem1571706)). Qed.
Lemma lem1571708 : term121 = term141.
Proof. exact (EQ_MP (@lem1571707) (@lem1571685)). Qed.
Lemma lem1571733 : term73 = term141.
Proof. exact (TRANS (@lem1571681) (@lem1571708)). Qed.
Lemma lem1571735 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1571736 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1571735 real P Q). Qed.
Lemma lem1571737 : term123 = term122.
Proof. exact (@lem1571736 term124 term125). Qed.
Lemma lem1571738 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1571739 : term133 = term124.
Proof. exact (fun_ext (fun x : real => @lem1571738 x)). Qed.
Lemma lem1571740 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571741 : term134 = term135.
Proof. exact (MK_COMB (@lem1571740) (@lem1571739)). Qed.
Lemma lem1571742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571743 : term136 = term137.
Proof. exact (MK_COMB (@lem1571742) (@lem1571741)). Qed.
Lemma lem1571744 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1571745 : term138 = term125.
Proof. exact (fun_ext (fun x : real => @lem1571744 x)). Qed.
Lemma lem1571746 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571747 : term139 = term140.
Proof. exact (MK_COMB (@lem1571746) (@lem1571745)). Qed.
Lemma lem1571748 : term123 = term141.
Proof. exact (MK_COMB (@lem1571743) (@lem1571747)). Qed.
Lemma lem1571749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1571750 : term142 = term143.
Proof. exact (MK_COMB (@lem1571749) (@lem1571748)). Qed.
Lemma lem1571751 (x : real) : (term126 x) = (term113 x).
Proof. exact (eq_refl (term126 x)). Qed.
Lemma lem1571752 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571753 (x : real) : (term127 x) = (term115 x).
Proof. exact (MK_COMB (@lem1571752) (@lem1571751 x)). Qed.
Lemma lem1571754 (x : real) : (term128 x) = (term118 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1571755 (x : real) : (term129 x) = (term119 x).
Proof. exact (MK_COMB (@lem1571753 x) (@lem1571754 x)). Qed.
Lemma lem1571756 : term130 = term120.
Proof. exact (fun_ext (fun x : real => @lem1571755 x)). Qed.
Lemma lem1571757 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571758 : term122 = term121.
Proof. exact (MK_COMB (@lem1571757) (@lem1571756)). Qed.
Lemma lem1571759 : (term123 = term122) = (term141 = term121).
Proof. exact (MK_COMB (@lem1571750) (@lem1571758)). Qed.
Lemma lem1571760 : term141 = term121.
Proof. exact (EQ_MP (@lem1571759) (@lem1571737)). Qed.
Lemma lem1571762 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1571763 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1571762 real P Q). Qed.
Lemma lem1571764 (x : real) : (term101 x) = (term100 x).
Proof. exact (@lem1571763 (term102 x) (term103 x)). Qed.
Lemma lem1571765 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1571766 (x : real) : (term111 x) = (term102 x).
Proof. exact (fun_ext (fun y : real => @lem1571765 x y)). Qed.
Lemma lem1571767 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571768 (x : real) : (term112 x) = (term113 x).
Proof. exact (MK_COMB (@lem1571767) (@lem1571766 x)). Qed.
Lemma lem1571769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571770 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1571769) (@lem1571768 x)). Qed.
Lemma lem1571771 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1571772 (x : real) : (term116 x) = (term103 x).
Proof. exact (fun_ext (fun y : real => @lem1571771 x y)). Qed.
Lemma lem1571773 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571774 (x : real) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1571773) (@lem1571772 x)). Qed.
Lemma lem1571775 (x : real) : (term101 x) = (term119 x).
Proof. exact (MK_COMB (@lem1571770 x) (@lem1571774 x)). Qed.
Lemma lem1571776 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1571777 (x : real) : (term144 x) = (term145 x).
Proof. exact (MK_COMB (@lem1571776) (@lem1571775 x)). Qed.
Lemma lem1571778 (x : real) (y : real) : (term104 x y) = (term91 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1571779 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571780 (x : real) (y : real) : (term105 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1571779) (@lem1571778 x y)). Qed.
Lemma lem1571781 (x : real) (y : real) : (term106 x y) = (term96 x y).
Proof. exact (eq_refl (term106 x y)). Qed.
Lemma lem1571782 (x : real) (y : real) : (term107 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1571780 x y) (@lem1571781 x y)). Qed.
Lemma lem1571783 (x : real) : (term108 x) = (term98 x).
Proof. exact (fun_ext (fun y : real => @lem1571782 x y)). Qed.
Lemma lem1571784 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571785 (x : real) : (term100 x) = (term99 x).
Proof. exact (MK_COMB (@lem1571784) (@lem1571783 x)). Qed.
Lemma lem1571786 (x : real) : ((term101 x) = (term100 x)) = ((term119 x) = (term99 x)).
Proof. exact (MK_COMB (@lem1571777 x) (@lem1571785 x)). Qed.
Lemma lem1571787 (x : real) : (term119 x) = (term99 x).
Proof. exact (EQ_MP (@lem1571786 x) (@lem1571764 x)). Qed.
Lemma lem1571789 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term75 A P Q) = (term74 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1571790 (P : real -> Prop) (Q : real -> Prop) : (term77 P Q) = (term76 P Q).
Proof. exact (@lem1571789 real P Q). Qed.
Lemma lem1571791 (x : real) (y : real) : (term79 x y) = (term78 x y).
Proof. exact (@lem1571790 (term80 x y) (term81 x y)). Qed.
Lemma lem1571792 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1571793 (x : real) (y : real) : (term89 x y) = (term80 x y).
Proof. exact (fun_ext (fun z : real => @lem1571792 x y z)). Qed.
Lemma lem1571794 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571795 (x : real) (y : real) : (term90 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1571794) (@lem1571793 x y)). Qed.
Lemma lem1571796 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571797 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1571796) (@lem1571795 x y)). Qed.
Lemma lem1571798 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1571799 (x : real) (y : real) : (term94 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1571798 x y z)). Qed.
Lemma lem1571800 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571801 (x : real) (y : real) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1571800) (@lem1571799 x y)). Qed.
Lemma lem1571802 (x : real) (y : real) : (term79 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem1571797 x y) (@lem1571801 x y)). Qed.
Lemma lem1571803 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1571804 (x : real) (y : real) : (term146 x y) = (term147 x y).
Proof. exact (MK_COMB (@lem1571803) (@lem1571802 x y)). Qed.
Lemma lem1571805 (x : real) (y : real) (z : real) : (term82 x y z) = (term64 x y z).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1571806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571807 (x : real) (y : real) (z : real) : (term83 x y z) = (term66 x y z).
Proof. exact (MK_COMB (@lem1571806) (@lem1571805 x y z)). Qed.
Lemma lem1571808 (x : real) (y : real) (z : real) : (term84 x y z) = (term60 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1571809 (x : real) (y : real) (z : real) : (term85 x y z) = (term67 x y z).
Proof. exact (MK_COMB (@lem1571807 x y z) (@lem1571808 x y z)). Qed.
Lemma lem1571810 (x : real) (y : real) : (term86 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1571809 x y z)). Qed.
Lemma lem1571811 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571812 (x : real) (y : real) : (term78 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1571811) (@lem1571810 x y)). Qed.
Lemma lem1571813 (x : real) (y : real) : ((term79 x y) = (term78 x y)) = ((term97 x y) = (term69 x y)).
Proof. exact (MK_COMB (@lem1571804 x y) (@lem1571812 x y)). Qed.
Lemma lem1571814 (x : real) (y : real) : (term97 x y) = (term69 x y).
Proof. exact (EQ_MP (@lem1571813 x y) (@lem1571791 x y)). Qed.
Lemma lem1571815 (x : real) : (term98 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1571814 x y)). Qed.
Lemma lem1571816 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571817 (x : real) : (term99 x) = (term71 x).
Proof. exact (MK_COMB (@lem1571816) (@lem1571815 x)). Qed.
Lemma lem1571818 (x : real) : (term119 x) = (term71 x).
Proof. exact (TRANS (@lem1571787 x) (@lem1571817 x)). Qed.
Lemma lem1571819 : term120 = term72.
Proof. exact (fun_ext (fun x : real => @lem1571818 x)). Qed.
Lemma lem1571820 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571821 : term121 = term73.
Proof. exact (MK_COMB (@lem1571820) (@lem1571819)). Qed.
Lemma lem1571822 : term141 = term73.
Proof. exact (TRANS (@lem1571760) (@lem1571821)). Qed.
Lemma lem1571823 : term73 = term73.
Proof. exact (TRANS (@lem1571733) (@lem1571822)). Qed.
Lemma lem1571826 : term22 = term73.
Proof. exact (TRANS (@lem1571588) (@lem1571823)). Qed.
Lemma lem1571831 (x : real) (y : real) (z : real) : (term67 x y z) = (term67 x y z).
Proof. exact (eq_refl (term67 x y z)). Qed.
Lemma lem1571832 (x : real) (y : real) : (term68 x y) = (term68 x y).
Proof. exact (fun_ext (fun z : real => @lem1571831 x y z)). Qed.
Lemma lem1571833 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571834 (x : real) (y : real) : (term69 x y) = (term69 x y).
Proof. exact (MK_COMB (@lem1571833) (@lem1571832 x y)). Qed.
Lemma lem1571835 (x : real) : (term70 x) = (term70 x).
Proof. exact (fun_ext (fun y : real => @lem1571834 x y)). Qed.
Lemma lem1571836 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571837 (x : real) : (term71 x) = (term71 x).
Proof. exact (MK_COMB (@lem1571836) (@lem1571835 x)). Qed.
Lemma lem1571838 : term72 = term72.
Proof. exact (fun_ext (fun x : real => @lem1571837 x)). Qed.
Lemma lem1571839 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1571840 : term73 = term73.
Proof. exact (MK_COMB (@lem1571839) (@lem1571838)). Qed.
Lemma lem1571841 : term22 = term73.
Proof. exact (TRANS (@lem1571826) (@lem1571840)). Qed.
Lemma lem1571843 (x : real) (a : real) (y : real) (r : real) : (term148 a x y r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1571844 (x : real) (y : real) (z : real) : (term64 x y z) = (term150 x y z).
Proof. exact (@lem1571843 (real_max x y) (term6 x y z) z term58). Qed.
Lemma lem1571857 (x : real) (y : real) (z : real) : (term151 x y z) = (term152 x y z).
Proof. exact (@lem1483488 (term153 z) (term6 x y z)). Qed.
Lemma lem1571858 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571859 (x : real) (y : real) (z : real) : (term154 x y z) = (term155 x y z).
Proof. exact (MK_COMB (@lem1571858) (@lem1571857 x y z)). Qed.
Lemma lem1571860 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571861 (x : real) (y : real) (z : real) : (term156 x y z) = (term157 x y z).
Proof. exact (MK_COMB (@lem1571859 x y z) (@lem1571860)). Qed.
Lemma lem1571874 (x : real) (y : real) (z : real) : (term158 z x y) = (term159 x y z).
Proof. exact (@lem1483488 (term160 x y) (term6 x y z)). Qed.
Lemma lem1571875 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571876 (x : real) (y : real) (z : real) : (term161 z x y) = (term162 x y z).
Proof. exact (MK_COMB (@lem1571875) (@lem1571874 x y z)). Qed.
Lemma lem1571877 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571878 (x : real) (y : real) (z : real) : (term163 z x y) = (term164 x y z).
Proof. exact (MK_COMB (@lem1571876 x y z) (@lem1571877)). Qed.
Lemma lem1571879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1571880 (x : real) (y : real) (z : real) : (term165 z x y) = (term166 x y z).
Proof. exact (MK_COMB (@lem1571879) (@lem1571878 x y z)). Qed.
Lemma lem1571881 (x : real) (y : real) (z : real) : (term150 x y z) = (term167 x y z).
Proof. exact (MK_COMB (@lem1571880 x y z) (@lem1571861 x y z)). Qed.
Lemma lem1571882 (x : real) (y : real) (z : real) : (term64 x y z) = (term167 x y z).
Proof. exact (TRANS (@lem1571844 x y z) (@lem1571881 x y z)). Qed.
Lemma lem1571884 (x : real) (a : real) (y : real) (r : real) : (term168 x y a r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1571885 (x : real) (z : real) (y : real) : (term164 x y z) = (term169 x z y).
Proof. exact (@lem1571884 x (term6 x y z) y term58). Qed.
Lemma lem1571898 (x : real) (y : real) (z : real) : (term170 x z y) = (term171 x y z).
Proof. exact (@lem1483488 (term153 y) (term6 x y z)). Qed.
Lemma lem1571899 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571900 (x : real) (y : real) (z : real) : (term172 x z y) = (term173 x y z).
Proof. exact (MK_COMB (@lem1571899) (@lem1571898 x y z)). Qed.
Lemma lem1571901 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571902 (x : real) (y : real) (z : real) : (term174 x z y) = (term175 x y z).
Proof. exact (MK_COMB (@lem1571900 x y z) (@lem1571901)). Qed.
Lemma lem1571915 (x : real) (y : real) (z : real) : (term176 y z x) = (term177 x y z).
Proof. exact (@lem1483488 (term153 x) (term6 x y z)). Qed.
Lemma lem1571916 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571917 (x : real) (y : real) (z : real) : (term178 y z x) = (term179 x y z).
Proof. exact (MK_COMB (@lem1571916) (@lem1571915 x y z)). Qed.
Lemma lem1571918 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571919 (x : real) (y : real) (z : real) : (term180 y z x) = (term181 x y z).
Proof. exact (MK_COMB (@lem1571917 x y z) (@lem1571918)). Qed.
Lemma lem1571920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1571921 (x : real) (y : real) (z : real) : (term182 y z x) = (term183 x y z).
Proof. exact (MK_COMB (@lem1571920) (@lem1571919 x y z)). Qed.
Lemma lem1571922 (x : real) (y : real) (z : real) : (term169 x z y) = (term184 x y z).
Proof. exact (MK_COMB (@lem1571921 x y z) (@lem1571902 x y z)). Qed.
Lemma lem1571923 (x : real) (y : real) (z : real) : (term164 x y z) = (term184 x y z).
Proof. exact (TRANS (@lem1571885 x z y) (@lem1571922 x y z)). Qed.
Lemma lem1571924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1571925 (x : real) (y : real) (z : real) : (term166 x y z) = (term185 x y z).
Proof. exact (MK_COMB (@lem1571924) (@lem1571923 x y z)). Qed.
Lemma lem1571926 (x : real) (y : real) (z : real) : (term157 x y z) = (term157 x y z).
Proof. exact (eq_refl (term157 x y z)). Qed.
Lemma lem1571927 (x : real) (y : real) (z : real) : (term167 x y z) = (term186 x y z).
Proof. exact (MK_COMB (@lem1571925 x y z) (@lem1571926 x y z)). Qed.
Lemma lem1571928 (x : real) (y : real) (z : real) : (term64 x y z) = (term186 x y z).
Proof. exact (TRANS (@lem1571882 x y z) (@lem1571927 x y z)). Qed.
Lemma lem1571929 (x : real) (y : real) (z : real) : (term187 x y z) = (term186 x y z).
Proof. exact (eq_refl (term187 x y z)). Qed.
Lemma lem1571930 (x : real) (y : real) (z : real) : (term186 x y z) = (term187 x y z).
Proof. exact (SYM (@lem1571929 x y z)). Qed.
Lemma lem1571931 (y : real) (z : real) (x : real) : (term187 x y z) = (term188 y z x).
Proof. exact (@lem1483205 (real_max y z) (term189 x y z) x). Qed.
Lemma lem1571932 (y : real) (z : real) (x : real) : (term186 x y z) = (term188 y z x).
Proof. exact (TRANS (@lem1571930 x y z) (@lem1571931 y z x)). Qed.
Lemma lem1571933 (y : real) (z : real) (x : real) : (term190 y z x) = (term191 y z x).
Proof. exact (eq_refl (term190 y z x)). Qed.
Lemma lem1571934 (x : real) (y : real) (z : real) : (term192 x y z) = (term192 x y z).
Proof. exact (eq_refl (term192 x y z)). Qed.
Lemma lem1571935 (y : real) (z : real) (x : real) : (term193 y z x) = (term194 y z x).
Proof. exact (MK_COMB (@lem1571934 x y z) (@lem1571933 y z x)). Qed.
Lemma lem1571936 (x : real) (y : real) (z : real) : (term195 x y z) = (term196 x y z).
Proof. exact (eq_refl (term195 x y z)). Qed.
Lemma lem1571937 (y : real) (z : real) (x : real) : (term197 y z x) = (term197 y z x).
Proof. exact (eq_refl (term197 y z x)). Qed.
Lemma lem1571938 (x : real) (y : real) (z : real) : (term198 x y z) = (term199 x y z).
Proof. exact (MK_COMB (@lem1571937 y z x) (@lem1571936 x y z)). Qed.
Lemma lem1571939 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1571940 (x : real) (y : real) (z : real) : (term200 x y z) = (term201 x y z).
Proof. exact (MK_COMB (@lem1571939) (@lem1571938 x y z)). Qed.
Lemma lem1571941 (y : real) (z : real) (x : real) : (term188 y z x) = (term202 y z x).
Proof. exact (MK_COMB (@lem1571940 x y z) (@lem1571935 y z x)). Qed.
Lemma lem1571942 (x : real) (y : real) (z : real) : (term203 x y z) = (term203 x y z).
Proof. exact (eq_refl (term203 x y z)). Qed.
Lemma lem1571943 (y : real) (z : real) (x : real) : ((term186 x y z) = (term188 y z x)) = ((term186 x y z) = (term202 y z x)).
Proof. exact (MK_COMB (@lem1571942 x y z) (@lem1571941 y z x)). Qed.
Lemma lem1571944 (y : real) (z : real) (x : real) : (term186 x y z) = (term202 y z x).
Proof. exact (EQ_MP (@lem1571943 y z x) (@lem1571932 y z x)). Qed.
Lemma lem1571945 (y : real) (z : real) (x : real) : (term204 y z x) = (term205 y z x).
Proof. exact (@lem1483527 (real_max y z) x). Qed.
Lemma lem1571951 (y : real) (z : real) (x : real) : (term206 y z x) = (term207 y z x).
Proof. exact (@lem1483519 (real_max y z) x). Qed.
Lemma lem1571956 (x : real) (y : real) (z : real) : (term207 y z x) = (term208 x y z).
Proof. exact (@lem1483488 (term153 x) (real_max y z)). Qed.
Lemma lem1571958 (x : real) (y : real) (z : real) : (term206 y z x) = (term208 x y z).
Proof. exact (TRANS (@lem1571951 y z x) (@lem1571956 x y z)). Qed.
Lemma lem1571959 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1571960 (x : real) (y : real) (z : real) : (term209 y z x) = (term210 x y z).
Proof. exact (MK_COMB (@lem1571959) (@lem1571958 x y z)). Qed.
Lemma lem1571961 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571962 (x : real) (y : real) (z : real) : (term205 y z x) = (term211 x y z).
Proof. exact (MK_COMB (@lem1571960 x y z) (@lem1571961)). Qed.
Lemma lem1571963 (x : real) (y : real) (z : real) : (term204 y z x) = (term211 x y z).
Proof. exact (TRANS (@lem1571945 y z x) (@lem1571962 x y z)). Qed.
Lemma lem1571964 (x : real) (y : real) (z : real) : (term212 x y z) = (term213 x y z).
Proof. exact (@lem1483525 (term208 x y z) term58). Qed.
Lemma lem1571982 (x : real) (y : real) (z : real) : (term214 x y z) = (term215 x y z).
Proof. exact (@lem1483519 (term208 x y z) term58). Qed.
Lemma lem1571984 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1571985 : term217 = term58.
Proof. exact (@lem1571984 term46). Qed.
Lemma lem1571986 (x : real) (y : real) (z : real) : (term218 x y z) = (term218 x y z).
Proof. exact (eq_refl (term218 x y z)). Qed.
Lemma lem1571987 (x : real) (y : real) (z : real) : (term215 x y z) = (term219 x y z).
Proof. exact (MK_COMB (@lem1571986 x y z) (@lem1571985)). Qed.
Lemma lem1571988 (x : real) (y : real) (z : real) : (term219 x y z) = (term208 x y z).
Proof. exact (@lem1483450 (term208 x y z)). Qed.
Lemma lem1571989 (x : real) (y : real) (z : real) : (term215 x y z) = (term208 x y z).
Proof. exact (TRANS (@lem1571987 x y z) (@lem1571988 x y z)). Qed.
Lemma lem1571991 (x : real) (y : real) (z : real) : (term214 x y z) = (term208 x y z).
Proof. exact (TRANS (@lem1571982 x y z) (@lem1571989 x y z)). Qed.
Lemma lem1571992 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1571993 (x : real) (y : real) (z : real) : (term220 x y z) = (term221 x y z).
Proof. exact (MK_COMB (@lem1571992) (@lem1571991 x y z)). Qed.
Lemma lem1571994 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1571995 (x : real) (y : real) (z : real) : (term213 x y z) = (term212 x y z).
Proof. exact (MK_COMB (@lem1571993 x y z) (@lem1571994)). Qed.
Lemma lem1571996 (x : real) (y : real) (z : real) : (term212 x y z) = (term212 x y z).
Proof. exact (TRANS (@lem1571964 x y z) (@lem1571995 x y z)). Qed.
Lemma lem1571997 (y : real) (z : real) : (term222 y z) = (term223 y z).
Proof. exact (@lem1483525 (term224 y z) term58). Qed.
Lemma lem1572015 (y : real) (z : real) : (term225 y z) = (term226 y z).
Proof. exact (@lem1483519 (term224 y z) term58). Qed.
Lemma lem1572017 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572018 : term217 = term58.
Proof. exact (@lem1572017 term46). Qed.
Lemma lem1572019 (y : real) (z : real) : (term227 y z) = (term227 y z).
Proof. exact (eq_refl (term227 y z)). Qed.
Lemma lem1572020 (y : real) (z : real) : (term226 y z) = (term228 y z).
Proof. exact (MK_COMB (@lem1572019 y z) (@lem1572018)). Qed.
Lemma lem1572021 (y : real) (z : real) : (term228 y z) = (term224 y z).
Proof. exact (@lem1483450 (term224 y z)). Qed.
Lemma lem1572022 (y : real) (z : real) : (term226 y z) = (term224 y z).
Proof. exact (TRANS (@lem1572020 y z) (@lem1572021 y z)). Qed.
Lemma lem1572024 (y : real) (z : real) : (term225 y z) = (term224 y z).
Proof. exact (TRANS (@lem1572015 y z) (@lem1572022 y z)). Qed.
Lemma lem1572025 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572026 (y : real) (z : real) : (term229 y z) = (term230 y z).
Proof. exact (MK_COMB (@lem1572025) (@lem1572024 y z)). Qed.
Lemma lem1572027 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572028 (y : real) (z : real) : (term223 y z) = (term222 y z).
Proof. exact (MK_COMB (@lem1572026 y z) (@lem1572027)). Qed.
Lemma lem1572029 (y : real) (z : real) : (term222 y z) = (term222 y z).
Proof. exact (TRANS (@lem1571997 y z) (@lem1572028 y z)). Qed.
Lemma lem1572030 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572031 (x : real) (y : real) (z : real) : (term231 x y z) = (term231 x y z).
Proof. exact (MK_COMB (@lem1572030) (@lem1571996 x y z)). Qed.
Lemma lem1572032 (x : real) (y : real) (z : real) : (term232 x y z) = (term232 x y z).
Proof. exact (MK_COMB (@lem1572031 x y z) (@lem1572029 y z)). Qed.
Lemma lem1572033 (y : real) (z : real) : (term233 y z) = (term234 y z).
Proof. exact (@lem1483525 (term235 y z) term58). Qed.
Lemma lem1572051 (y : real) (z : real) : (term236 y z) = (term237 y z).
Proof. exact (@lem1483519 (term235 y z) term58). Qed.
Lemma lem1572053 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572054 : term217 = term58.
Proof. exact (@lem1572053 term46). Qed.
Lemma lem1572055 (y : real) (z : real) : (term238 y z) = (term238 y z).
Proof. exact (eq_refl (term238 y z)). Qed.
Lemma lem1572056 (y : real) (z : real) : (term237 y z) = (term239 y z).
Proof. exact (MK_COMB (@lem1572055 y z) (@lem1572054)). Qed.
Lemma lem1572057 (y : real) (z : real) : (term239 y z) = (term235 y z).
Proof. exact (@lem1483450 (term235 y z)). Qed.
Lemma lem1572058 (y : real) (z : real) : (term237 y z) = (term235 y z).
Proof. exact (TRANS (@lem1572056 y z) (@lem1572057 y z)). Qed.
Lemma lem1572060 (y : real) (z : real) : (term236 y z) = (term235 y z).
Proof. exact (TRANS (@lem1572051 y z) (@lem1572058 y z)). Qed.
Lemma lem1572061 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572062 (y : real) (z : real) : (term240 y z) = (term241 y z).
Proof. exact (MK_COMB (@lem1572061) (@lem1572060 y z)). Qed.
Lemma lem1572063 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572064 (y : real) (z : real) : (term234 y z) = (term233 y z).
Proof. exact (MK_COMB (@lem1572062 y z) (@lem1572063)). Qed.
Lemma lem1572065 (y : real) (z : real) : (term233 y z) = (term233 y z).
Proof. exact (TRANS (@lem1572033 y z) (@lem1572064 y z)). Qed.
Lemma lem1572066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572067 (x : real) (y : real) (z : real) : (term242 x y z) = (term242 x y z).
Proof. exact (MK_COMB (@lem1572066) (@lem1572032 x y z)). Qed.
Lemma lem1572068 (x : real) (y : real) (z : real) : (term196 x y z) = (term196 x y z).
Proof. exact (MK_COMB (@lem1572067 x y z) (@lem1572065 y z)). Qed.
Lemma lem1572069 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572070 (x : real) (y : real) (z : real) : (term197 y z x) = (term243 x y z).
Proof. exact (MK_COMB (@lem1572069) (@lem1571963 x y z)). Qed.
Lemma lem1572071 (x : real) (y : real) (z : real) : (term199 x y z) = (term244 x y z).
Proof. exact (MK_COMB (@lem1572070 x y z) (@lem1572068 x y z)). Qed.
Lemma lem1572072 (x : real) (y : real) (z : real) : (term245 x y z) = (term246 x y z).
Proof. exact (@lem1483525 x (real_max y z)). Qed.
Lemma lem1572085 (x : real) (y : real) (z : real) : (term247 x y z) = (term248 x y z).
Proof. exact (@lem1483519 x (real_max y z)). Qed.
Lemma lem1572086 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572087 (x : real) (y : real) (z : real) : (term249 x y z) = (term250 x y z).
Proof. exact (MK_COMB (@lem1572086) (@lem1572085 x y z)). Qed.
Lemma lem1572088 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572089 (x : real) (y : real) (z : real) : (term246 x y z) = (term251 x y z).
Proof. exact (MK_COMB (@lem1572087 x y z) (@lem1572088)). Qed.
Lemma lem1572090 (x : real) (y : real) (z : real) : (term245 x y z) = (term251 x y z).
Proof. exact (TRANS (@lem1572072 x y z) (@lem1572089 x y z)). Qed.
Lemma lem1572091 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483525 (term254 x) term58). Qed.
Lemma lem1572092 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572104 (x : real) : (term254 x) = (term255 x).
Proof. exact (@lem1483440 term38 x). Qed.
Lemma lem1572106 (m : nat) : (term256 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1572107 : term257 = term58.
Proof. exact (@lem1572106 term46). Qed.
Lemma lem1572108 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1572109 : term258 = term259.
Proof. exact (MK_COMB (@lem1572108) (@lem1572107)). Qed.
Lemma lem1572110 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1572111 (x : real) : (term255 x) = (term260 x).
Proof. exact (MK_COMB (@lem1572109) (@lem1572110 x)). Qed.
Lemma lem1572112 (x : real) : (term254 x) = (term260 x).
Proof. exact (TRANS (@lem1572104 x) (@lem1572111 x)). Qed.
Lemma lem1572113 (x : real) : (term260 x) = term58.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1572115 (x : real) : (term254 x) = term58.
Proof. exact (TRANS (@lem1572112 x) (@lem1572113 x)). Qed.
Lemma lem1572116 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1572117 (x : real) : (term261 x) = term262.
Proof. exact (MK_COMB (@lem1572116) (@lem1572115 x)). Qed.
Lemma lem1572118 (x : real) : (term263 x) = term264.
Proof. exact (MK_COMB (@lem1572117 x) (@lem1572092)). Qed.
Lemma lem1572119 : term264 = term265.
Proof. exact (@lem1483519 term58 term58). Qed.
Lemma lem1572121 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572122 : term217 = term58.
Proof. exact (@lem1572121 term46). Qed.
Lemma lem1572123 : term266 = term266.
Proof. exact (eq_refl term266). Qed.
Lemma lem1572124 : term265 = term267.
Proof. exact (MK_COMB (@lem1572123) (@lem1572122)). Qed.
Lemma lem1572125 : term267 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1572126 : term265 = term58.
Proof. exact (TRANS (@lem1572124) (@lem1572125)). Qed.
Lemma lem1572127 : term264 = term58.
Proof. exact (TRANS (@lem1572119) (@lem1572126)). Qed.
Lemma lem1572128 (x : real) : (term263 x) = term58.
Proof. exact (TRANS (@lem1572118 x) (@lem1572127)). Qed.
Lemma lem1572129 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572130 (x : real) : (term268 x) = term269.
Proof. exact (MK_COMB (@lem1572129) (@lem1572128 x)). Qed.
Lemma lem1572131 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572132 (x : real) : (term253 x) = term270.
Proof. exact (MK_COMB (@lem1572130 x) (@lem1572131)). Qed.
Lemma lem1572133 (x : real) : (term252 x) = term270.
Proof. exact (TRANS (@lem1572091 x) (@lem1572132 x)). Qed.
Lemma lem1572134 (y : real) (x : real) : (term271 y x) = (term272 y x).
Proof. exact (@lem1483525 (term273 y x) term58). Qed.
Lemma lem1572135 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572148 (x : real) (y : real) : (term273 y x) = (term274 x y).
Proof. exact (@lem1483488 x (term153 y)). Qed.
Lemma lem1572149 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1572150 (x : real) (y : real) : (term275 y x) = (term276 x y).
Proof. exact (MK_COMB (@lem1572149) (@lem1572148 x y)). Qed.
Lemma lem1572151 (x : real) (y : real) : (term277 y x) = (term278 x y).
Proof. exact (MK_COMB (@lem1572150 x y) (@lem1572135)). Qed.
Lemma lem1572152 (x : real) (y : real) : (term278 x y) = (term279 x y).
Proof. exact (@lem1483519 (term274 x y) term58). Qed.
Lemma lem1572154 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572155 : term217 = term58.
Proof. exact (@lem1572154 term46). Qed.
Lemma lem1572156 (x : real) (y : real) : (term280 x y) = (term280 x y).
Proof. exact (eq_refl (term280 x y)). Qed.
Lemma lem1572157 (x : real) (y : real) : (term279 x y) = (term281 x y).
Proof. exact (MK_COMB (@lem1572156 x y) (@lem1572155)). Qed.
Lemma lem1572158 (x : real) (y : real) : (term281 x y) = (term274 x y).
Proof. exact (@lem1483450 (term274 x y)). Qed.
Lemma lem1572159 (x : real) (y : real) : (term279 x y) = (term274 x y).
Proof. exact (TRANS (@lem1572157 x y) (@lem1572158 x y)). Qed.
Lemma lem1572160 (x : real) (y : real) : (term278 x y) = (term274 x y).
Proof. exact (TRANS (@lem1572152 x y) (@lem1572159 x y)). Qed.
Lemma lem1572161 (x : real) (y : real) : (term277 y x) = (term274 x y).
Proof. exact (TRANS (@lem1572151 x y) (@lem1572160 x y)). Qed.
Lemma lem1572162 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572163 (x : real) (y : real) : (term282 y x) = (term283 x y).
Proof. exact (MK_COMB (@lem1572162) (@lem1572161 x y)). Qed.
Lemma lem1572164 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572165 (x : real) (y : real) : (term272 y x) = (term284 x y).
Proof. exact (MK_COMB (@lem1572163 x y) (@lem1572164)). Qed.
Lemma lem1572166 (x : real) (y : real) : (term271 y x) = (term284 x y).
Proof. exact (TRANS (@lem1572134 y x) (@lem1572165 x y)). Qed.
Lemma lem1572167 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572168 (x : real) : (term285 x) = term286.
Proof. exact (MK_COMB (@lem1572167) (@lem1572133 x)). Qed.
Lemma lem1572169 (x : real) (y : real) : (term287 y x) = (term288 x y).
Proof. exact (MK_COMB (@lem1572168 x) (@lem1572166 x y)). Qed.
Lemma lem1572170 (z : real) (x : real) : (term271 z x) = (term272 z x).
Proof. exact (@lem1483525 (term273 z x) term58). Qed.
Lemma lem1572171 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572184 (x : real) (z : real) : (term273 z x) = (term274 x z).
Proof. exact (@lem1483488 x (term153 z)). Qed.
Lemma lem1572185 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1572186 (x : real) (z : real) : (term275 z x) = (term276 x z).
Proof. exact (MK_COMB (@lem1572185) (@lem1572184 x z)). Qed.
Lemma lem1572187 (x : real) (z : real) : (term277 z x) = (term278 x z).
Proof. exact (MK_COMB (@lem1572186 x z) (@lem1572171)). Qed.
Lemma lem1572188 (x : real) (z : real) : (term278 x z) = (term279 x z).
Proof. exact (@lem1483519 (term274 x z) term58). Qed.
Lemma lem1572190 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572191 : term217 = term58.
Proof. exact (@lem1572190 term46). Qed.
Lemma lem1572192 (x : real) (z : real) : (term280 x z) = (term280 x z).
Proof. exact (eq_refl (term280 x z)). Qed.
Lemma lem1572193 (x : real) (z : real) : (term279 x z) = (term281 x z).
Proof. exact (MK_COMB (@lem1572192 x z) (@lem1572191)). Qed.
Lemma lem1572194 (x : real) (z : real) : (term281 x z) = (term274 x z).
Proof. exact (@lem1483450 (term274 x z)). Qed.
Lemma lem1572195 (x : real) (z : real) : (term279 x z) = (term274 x z).
Proof. exact (TRANS (@lem1572193 x z) (@lem1572194 x z)). Qed.
Lemma lem1572196 (x : real) (z : real) : (term278 x z) = (term274 x z).
Proof. exact (TRANS (@lem1572188 x z) (@lem1572195 x z)). Qed.
Lemma lem1572197 (x : real) (z : real) : (term277 z x) = (term274 x z).
Proof. exact (TRANS (@lem1572187 x z) (@lem1572196 x z)). Qed.
Lemma lem1572198 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572199 (x : real) (z : real) : (term282 z x) = (term283 x z).
Proof. exact (MK_COMB (@lem1572198) (@lem1572197 x z)). Qed.
Lemma lem1572200 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572201 (x : real) (z : real) : (term272 z x) = (term284 x z).
Proof. exact (MK_COMB (@lem1572199 x z) (@lem1572200)). Qed.
Lemma lem1572202 (x : real) (z : real) : (term271 z x) = (term284 x z).
Proof. exact (TRANS (@lem1572170 z x) (@lem1572201 x z)). Qed.
Lemma lem1572203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572204 (x : real) (y : real) : (term289 y x) = (term290 x y).
Proof. exact (MK_COMB (@lem1572203) (@lem1572169 x y)). Qed.
Lemma lem1572205 (y : real) (x : real) (z : real) : (term191 y z x) = (term291 y x z).
Proof. exact (MK_COMB (@lem1572204 x y) (@lem1572202 x z)). Qed.
Lemma lem1572206 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572207 (x : real) (y : real) (z : real) : (term192 x y z) = (term292 x y z).
Proof. exact (MK_COMB (@lem1572206) (@lem1572090 x y z)). Qed.
Lemma lem1572208 (y : real) (x : real) (z : real) : (term194 y z x) = (term293 y x z).
Proof. exact (MK_COMB (@lem1572207 x y z) (@lem1572205 y x z)). Qed.
Lemma lem1572209 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572210 (x : real) (y : real) (z : real) : (term201 x y z) = (term294 x y z).
Proof. exact (MK_COMB (@lem1572209) (@lem1572071 x y z)). Qed.
Lemma lem1572211 (y : real) (x : real) (z : real) : (term202 y z x) = (term295 y x z).
Proof. exact (MK_COMB (@lem1572210 x y z) (@lem1572208 y x z)). Qed.
Lemma lem1572212 (y : real) (x : real) (z : real) : (term186 x y z) = (term295 y x z).
Proof. exact (TRANS (@lem1571944 y z x) (@lem1572211 y x z)). Qed.
Lemma lem1572214 (x : real) (a : real) (y : real) (r : real) : (term148 a x y r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1572253 (y : real) (x : real) (z : real) : (term251 x y z) = (term296 y x z).
Proof. exact (@lem1572214 y x z term58). Qed.
Lemma lem1572254 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572255 (y : real) (x : real) (z : real) : (term292 x y z) = (term297 y x z).
Proof. exact (MK_COMB (@lem1572254) (@lem1572253 y x z)). Qed.
Lemma lem1572256 (y : real) (x : real) (z : real) : (term291 y x z) = (term291 y x z).
Proof. exact (eq_refl (term291 y x z)). Qed.
Lemma lem1572259 (y : real) (x : real) (z : real) : (term293 y x z) = (term298 y x z).
Proof. exact (MK_COMB (@lem1572255 y x z) (@lem1572256 y x z)). Qed.
Lemma lem1572261 (x : real) (y : real) (z : real) : (term299 x y z) = (term244 x y z).
Proof. exact (eq_refl (term299 x y z)). Qed.
Lemma lem1572262 (x : real) (y : real) (z : real) : (term244 x y z) = (term299 x y z).
Proof. exact (SYM (@lem1572261 x y z)). Qed.
Lemma lem1572263 (x : real) (z : real) (y : real) : (term299 x y z) = (term300 x z y).
Proof. exact (@lem1483205 z (term301 x y z) y). Qed.
Lemma lem1572264 (x : real) (z : real) (y : real) : (term244 x y z) = (term300 x z y).
Proof. exact (TRANS (@lem1572262 x y z) (@lem1572263 x z y)). Qed.
Lemma lem1572265 (x : real) (z : real) (y : real) : (term302 x z y) = (term303 x z y).
Proof. exact (eq_refl (term302 x z y)). Qed.
Lemma lem1572266 (y : real) (z : real) : (term304 y z) = (term304 y z).
Proof. exact (eq_refl (term304 y z)). Qed.
Lemma lem1572267 (x : real) (z : real) (y : real) : (term305 x z y) = (term306 x z y).
Proof. exact (MK_COMB (@lem1572266 y z) (@lem1572265 x z y)). Qed.
Lemma lem1572268 (x : real) (y : real) (z : real) : (term307 x y z) = (term308 x y z).
Proof. exact (eq_refl (term307 x y z)). Qed.
Lemma lem1572269 (z : real) (y : real) : (term309 z y) = (term309 z y).
Proof. exact (eq_refl (term309 z y)). Qed.
Lemma lem1572270 (x : real) (y : real) (z : real) : (term310 x y z) = (term311 x y z).
Proof. exact (MK_COMB (@lem1572269 z y) (@lem1572268 x y z)). Qed.
Lemma lem1572271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572272 (x : real) (y : real) (z : real) : (term312 x y z) = (term313 x y z).
Proof. exact (MK_COMB (@lem1572271) (@lem1572270 x y z)). Qed.
Lemma lem1572273 (x : real) (z : real) (y : real) : (term300 x z y) = (term314 x z y).
Proof. exact (MK_COMB (@lem1572272 x y z) (@lem1572267 x z y)). Qed.
Lemma lem1572274 (x : real) (y : real) (z : real) : (term315 x y z) = (term315 x y z).
Proof. exact (eq_refl (term315 x y z)). Qed.
Lemma lem1572275 (x : real) (z : real) (y : real) : ((term244 x y z) = (term300 x z y)) = ((term244 x y z) = (term314 x z y)).
Proof. exact (MK_COMB (@lem1572274 x y z) (@lem1572273 x z y)). Qed.
Lemma lem1572276 (x : real) (z : real) (y : real) : (term244 x y z) = (term314 x z y).
Proof. exact (EQ_MP (@lem1572275 x z y) (@lem1572264 x z y)). Qed.
Lemma lem1572277 (z : real) (y : real) : (real_ge z y) = (term316 z y).
Proof. exact (@lem1483527 z y). Qed.
Lemma lem1572283 (z : real) (y : real) : (real_sub z y) = (term274 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1572288 (y : real) (z : real) : (term274 z y) = (term273 y z).
Proof. exact (@lem1483488 (term153 y) z). Qed.
Lemma lem1572290 (y : real) (z : real) : (real_sub z y) = (term273 y z).
Proof. exact (TRANS (@lem1572283 z y) (@lem1572288 y z)). Qed.
Lemma lem1572291 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1572292 (y : real) (z : real) : (term317 z y) = (term318 y z).
Proof. exact (MK_COMB (@lem1572291) (@lem1572290 y z)). Qed.
Lemma lem1572293 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572294 (y : real) (z : real) : (term316 z y) = (term319 y z).
Proof. exact (MK_COMB (@lem1572292 y z) (@lem1572293)). Qed.
Lemma lem1572295 (y : real) (z : real) : (real_ge z y) = (term319 y z).
Proof. exact (TRANS (@lem1572277 z y) (@lem1572294 y z)). Qed.
Lemma lem1572296 (x : real) (z : real) : (term319 x z) = (term320 x z).
Proof. exact (@lem1483527 (term273 x z) term58). Qed.
Lemma lem1572314 (x : real) (z : real) : (term277 x z) = (term321 x z).
Proof. exact (@lem1483519 (term273 x z) term58). Qed.
Lemma lem1572316 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572317 : term217 = term58.
Proof. exact (@lem1572316 term46). Qed.
Lemma lem1572318 (x : real) (z : real) : (term322 x z) = (term322 x z).
Proof. exact (eq_refl (term322 x z)). Qed.
Lemma lem1572319 (x : real) (z : real) : (term321 x z) = (term323 x z).
Proof. exact (MK_COMB (@lem1572318 x z) (@lem1572317)). Qed.
Lemma lem1572320 (x : real) (z : real) : (term323 x z) = (term273 x z).
Proof. exact (@lem1483450 (term273 x z)). Qed.
Lemma lem1572321 (x : real) (z : real) : (term321 x z) = (term273 x z).
Proof. exact (TRANS (@lem1572319 x z) (@lem1572320 x z)). Qed.
Lemma lem1572323 (x : real) (z : real) : (term277 x z) = (term273 x z).
Proof. exact (TRANS (@lem1572314 x z) (@lem1572321 x z)). Qed.
Lemma lem1572324 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1572325 (x : real) (z : real) : (term324 x z) = (term318 x z).
Proof. exact (MK_COMB (@lem1572324) (@lem1572323 x z)). Qed.
Lemma lem1572326 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572327 (x : real) (z : real) : (term320 x z) = (term319 x z).
Proof. exact (MK_COMB (@lem1572325 x z) (@lem1572326)). Qed.
Lemma lem1572328 (x : real) (z : real) : (term319 x z) = (term319 x z).
Proof. exact (TRANS (@lem1572296 x z) (@lem1572327 x z)). Qed.
Lemma lem1572329 (x : real) (z : real) : (term271 x z) = (term272 x z).
Proof. exact (@lem1483525 (term273 x z) term58). Qed.
Lemma lem1572347 (x : real) (z : real) : (term277 x z) = (term321 x z).
Proof. exact (@lem1483519 (term273 x z) term58). Qed.
Lemma lem1572349 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572350 : term217 = term58.
Proof. exact (@lem1572349 term46). Qed.
Lemma lem1572351 (x : real) (z : real) : (term322 x z) = (term322 x z).
Proof. exact (eq_refl (term322 x z)). Qed.
Lemma lem1572352 (x : real) (z : real) : (term321 x z) = (term323 x z).
Proof. exact (MK_COMB (@lem1572351 x z) (@lem1572350)). Qed.
Lemma lem1572353 (x : real) (z : real) : (term323 x z) = (term273 x z).
Proof. exact (@lem1483450 (term273 x z)). Qed.
Lemma lem1572354 (x : real) (z : real) : (term321 x z) = (term273 x z).
Proof. exact (TRANS (@lem1572352 x z) (@lem1572353 x z)). Qed.
Lemma lem1572356 (x : real) (z : real) : (term277 x z) = (term273 x z).
Proof. exact (TRANS (@lem1572347 x z) (@lem1572354 x z)). Qed.
Lemma lem1572357 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572358 (x : real) (z : real) : (term282 x z) = (term325 x z).
Proof. exact (MK_COMB (@lem1572357) (@lem1572356 x z)). Qed.
Lemma lem1572359 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572360 (x : real) (z : real) : (term272 x z) = (term271 x z).
Proof. exact (MK_COMB (@lem1572358 x z) (@lem1572359)). Qed.
Lemma lem1572361 (x : real) (z : real) : (term271 x z) = (term271 x z).
Proof. exact (TRANS (@lem1572329 x z) (@lem1572360 x z)). Qed.
Lemma lem1572362 (y : real) (z : real) : (term271 y z) = (term272 y z).
Proof. exact (@lem1483525 (term273 y z) term58). Qed.
Lemma lem1572380 (y : real) (z : real) : (term277 y z) = (term321 y z).
Proof. exact (@lem1483519 (term273 y z) term58). Qed.
Lemma lem1572382 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572383 : term217 = term58.
Proof. exact (@lem1572382 term46). Qed.
Lemma lem1572384 (y : real) (z : real) : (term322 y z) = (term322 y z).
Proof. exact (eq_refl (term322 y z)). Qed.
Lemma lem1572385 (y : real) (z : real) : (term321 y z) = (term323 y z).
Proof. exact (MK_COMB (@lem1572384 y z) (@lem1572383)). Qed.
Lemma lem1572386 (y : real) (z : real) : (term323 y z) = (term273 y z).
Proof. exact (@lem1483450 (term273 y z)). Qed.
Lemma lem1572387 (y : real) (z : real) : (term321 y z) = (term273 y z).
Proof. exact (TRANS (@lem1572385 y z) (@lem1572386 y z)). Qed.
Lemma lem1572389 (y : real) (z : real) : (term277 y z) = (term273 y z).
Proof. exact (TRANS (@lem1572380 y z) (@lem1572387 y z)). Qed.
Lemma lem1572390 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572391 (y : real) (z : real) : (term282 y z) = (term325 y z).
Proof. exact (MK_COMB (@lem1572390) (@lem1572389 y z)). Qed.
Lemma lem1572392 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572393 (y : real) (z : real) : (term272 y z) = (term271 y z).
Proof. exact (MK_COMB (@lem1572391 y z) (@lem1572392)). Qed.
Lemma lem1572394 (y : real) (z : real) : (term271 y z) = (term271 y z).
Proof. exact (TRANS (@lem1572362 y z) (@lem1572393 y z)). Qed.
Lemma lem1572395 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572396 (x : real) (z : real) : (term326 x z) = (term326 x z).
Proof. exact (MK_COMB (@lem1572395) (@lem1572361 x z)). Qed.
Lemma lem1572397 (x : real) (y : real) (z : real) : (term327 x y z) = (term327 x y z).
Proof. exact (MK_COMB (@lem1572396 x z) (@lem1572394 y z)). Qed.
Lemma lem1572398 (z : real) : (term252 z) = (term253 z).
Proof. exact (@lem1483525 (term254 z) term58). Qed.
Lemma lem1572399 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572411 (z : real) : (term254 z) = (term255 z).
Proof. exact (@lem1483440 term38 z). Qed.
Lemma lem1572413 (m : nat) : (term256 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1572414 : term257 = term58.
Proof. exact (@lem1572413 term46). Qed.
Lemma lem1572415 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1572416 : term258 = term259.
Proof. exact (MK_COMB (@lem1572415) (@lem1572414)). Qed.
Lemma lem1572417 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1572418 (z : real) : (term255 z) = (term260 z).
Proof. exact (MK_COMB (@lem1572416) (@lem1572417 z)). Qed.
Lemma lem1572419 (z : real) : (term254 z) = (term260 z).
Proof. exact (TRANS (@lem1572411 z) (@lem1572418 z)). Qed.
Lemma lem1572420 (z : real) : (term260 z) = term58.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1572422 (z : real) : (term254 z) = term58.
Proof. exact (TRANS (@lem1572419 z) (@lem1572420 z)). Qed.
Lemma lem1572423 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1572424 (z : real) : (term261 z) = term262.
Proof. exact (MK_COMB (@lem1572423) (@lem1572422 z)). Qed.
Lemma lem1572425 (z : real) : (term263 z) = term264.
Proof. exact (MK_COMB (@lem1572424 z) (@lem1572399)). Qed.
Lemma lem1572426 : term264 = term265.
Proof. exact (@lem1483519 term58 term58). Qed.
Lemma lem1572428 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572429 : term217 = term58.
Proof. exact (@lem1572428 term46). Qed.
Lemma lem1572430 : term266 = term266.
Proof. exact (eq_refl term266). Qed.
Lemma lem1572431 : term265 = term267.
Proof. exact (MK_COMB (@lem1572430) (@lem1572429)). Qed.
Lemma lem1572432 : term267 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1572433 : term265 = term58.
Proof. exact (TRANS (@lem1572431) (@lem1572432)). Qed.
Lemma lem1572434 : term264 = term58.
Proof. exact (TRANS (@lem1572426) (@lem1572433)). Qed.
Lemma lem1572435 (z : real) : (term263 z) = term58.
Proof. exact (TRANS (@lem1572425 z) (@lem1572434)). Qed.
Lemma lem1572436 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572437 (z : real) : (term268 z) = term269.
Proof. exact (MK_COMB (@lem1572436) (@lem1572435 z)). Qed.
Lemma lem1572438 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572439 (z : real) : (term253 z) = term270.
Proof. exact (MK_COMB (@lem1572437 z) (@lem1572438)). Qed.
Lemma lem1572440 (z : real) : (term252 z) = term270.
Proof. exact (TRANS (@lem1572398 z) (@lem1572439 z)). Qed.
Lemma lem1572441 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572442 (x : real) (y : real) (z : real) : (term328 x y z) = (term328 x y z).
Proof. exact (MK_COMB (@lem1572441) (@lem1572397 x y z)). Qed.
Lemma lem1572443 (x : real) (y : real) (z : real) : (term329 x y z) = (term330 x y z).
Proof. exact (MK_COMB (@lem1572442 x y z) (@lem1572440 z)). Qed.
Lemma lem1572444 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572445 (x : real) (z : real) : (term331 x z) = (term331 x z).
Proof. exact (MK_COMB (@lem1572444) (@lem1572328 x z)). Qed.
Lemma lem1572446 (x : real) (y : real) (z : real) : (term308 x y z) = (term332 x y z).
Proof. exact (MK_COMB (@lem1572445 x z) (@lem1572443 x y z)). Qed.
Lemma lem1572447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572448 (y : real) (z : real) : (term309 z y) = (term331 y z).
Proof. exact (MK_COMB (@lem1572447) (@lem1572295 y z)). Qed.
Lemma lem1572449 (x : real) (y : real) (z : real) : (term311 x y z) = (term333 x y z).
Proof. exact (MK_COMB (@lem1572448 y z) (@lem1572446 x y z)). Qed.
Lemma lem1572450 (y : real) (z : real) : (real_gt y z) = (term334 y z).
Proof. exact (@lem1483525 y z). Qed.
Lemma lem1572463 (y : real) (z : real) : (real_sub y z) = (term274 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1572464 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572465 (y : real) (z : real) : (term335 y z) = (term283 y z).
Proof. exact (MK_COMB (@lem1572464) (@lem1572463 y z)). Qed.
Lemma lem1572466 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572467 (y : real) (z : real) : (term334 y z) = (term284 y z).
Proof. exact (MK_COMB (@lem1572465 y z) (@lem1572466)). Qed.
Lemma lem1572468 (y : real) (z : real) : (real_gt y z) = (term284 y z).
Proof. exact (TRANS (@lem1572450 y z) (@lem1572467 y z)). Qed.
Lemma lem1572469 (x : real) (y : real) : (term319 x y) = (term320 x y).
Proof. exact (@lem1483527 (term273 x y) term58). Qed.
Lemma lem1572487 (x : real) (y : real) : (term277 x y) = (term321 x y).
Proof. exact (@lem1483519 (term273 x y) term58). Qed.
Lemma lem1572489 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572490 : term217 = term58.
Proof. exact (@lem1572489 term46). Qed.
Lemma lem1572491 (x : real) (y : real) : (term322 x y) = (term322 x y).
Proof. exact (eq_refl (term322 x y)). Qed.
Lemma lem1572492 (x : real) (y : real) : (term321 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1572491 x y) (@lem1572490)). Qed.
Lemma lem1572493 (x : real) (y : real) : (term323 x y) = (term273 x y).
Proof. exact (@lem1483450 (term273 x y)). Qed.
Lemma lem1572494 (x : real) (y : real) : (term321 x y) = (term273 x y).
Proof. exact (TRANS (@lem1572492 x y) (@lem1572493 x y)). Qed.
Lemma lem1572496 (x : real) (y : real) : (term277 x y) = (term273 x y).
Proof. exact (TRANS (@lem1572487 x y) (@lem1572494 x y)). Qed.
Lemma lem1572497 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1572498 (x : real) (y : real) : (term324 x y) = (term318 x y).
Proof. exact (MK_COMB (@lem1572497) (@lem1572496 x y)). Qed.
Lemma lem1572499 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572500 (x : real) (y : real) : (term320 x y) = (term319 x y).
Proof. exact (MK_COMB (@lem1572498 x y) (@lem1572499)). Qed.
Lemma lem1572501 (x : real) (y : real) : (term319 x y) = (term319 x y).
Proof. exact (TRANS (@lem1572469 x y) (@lem1572500 x y)). Qed.
Lemma lem1572502 (x : real) (y : real) : (term271 x y) = (term272 x y).
Proof. exact (@lem1483525 (term273 x y) term58). Qed.
Lemma lem1572520 (x : real) (y : real) : (term277 x y) = (term321 x y).
Proof. exact (@lem1483519 (term273 x y) term58). Qed.
Lemma lem1572522 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572523 : term217 = term58.
Proof. exact (@lem1572522 term46). Qed.
Lemma lem1572524 (x : real) (y : real) : (term322 x y) = (term322 x y).
Proof. exact (eq_refl (term322 x y)). Qed.
Lemma lem1572525 (x : real) (y : real) : (term321 x y) = (term323 x y).
Proof. exact (MK_COMB (@lem1572524 x y) (@lem1572523)). Qed.
Lemma lem1572526 (x : real) (y : real) : (term323 x y) = (term273 x y).
Proof. exact (@lem1483450 (term273 x y)). Qed.
Lemma lem1572527 (x : real) (y : real) : (term321 x y) = (term273 x y).
Proof. exact (TRANS (@lem1572525 x y) (@lem1572526 x y)). Qed.
Lemma lem1572529 (x : real) (y : real) : (term277 x y) = (term273 x y).
Proof. exact (TRANS (@lem1572520 x y) (@lem1572527 x y)). Qed.
Lemma lem1572530 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572531 (x : real) (y : real) : (term282 x y) = (term325 x y).
Proof. exact (MK_COMB (@lem1572530) (@lem1572529 x y)). Qed.
Lemma lem1572532 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572533 (x : real) (y : real) : (term272 x y) = (term271 x y).
Proof. exact (MK_COMB (@lem1572531 x y) (@lem1572532)). Qed.
Lemma lem1572534 (x : real) (y : real) : (term271 x y) = (term271 x y).
Proof. exact (TRANS (@lem1572502 x y) (@lem1572533 x y)). Qed.
Lemma lem1572535 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483525 (term254 y) term58). Qed.
Lemma lem1572536 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572548 (y : real) : (term254 y) = (term255 y).
Proof. exact (@lem1483440 term38 y). Qed.
Lemma lem1572550 (m : nat) : (term256 m) = term58.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1572551 : term257 = term58.
Proof. exact (@lem1572550 term46). Qed.
Lemma lem1572552 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1572553 : term258 = term259.
Proof. exact (MK_COMB (@lem1572552) (@lem1572551)). Qed.
Lemma lem1572554 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1572555 (y : real) : (term255 y) = (term260 y).
Proof. exact (MK_COMB (@lem1572553) (@lem1572554 y)). Qed.
Lemma lem1572556 (y : real) : (term254 y) = (term260 y).
Proof. exact (TRANS (@lem1572548 y) (@lem1572555 y)). Qed.
Lemma lem1572557 (y : real) : (term260 y) = term58.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1572559 (y : real) : (term254 y) = term58.
Proof. exact (TRANS (@lem1572556 y) (@lem1572557 y)). Qed.
Lemma lem1572560 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1572561 (y : real) : (term261 y) = term262.
Proof. exact (MK_COMB (@lem1572560) (@lem1572559 y)). Qed.
Lemma lem1572562 (y : real) : (term263 y) = term264.
Proof. exact (MK_COMB (@lem1572561 y) (@lem1572536)). Qed.
Lemma lem1572563 : term264 = term265.
Proof. exact (@lem1483519 term58 term58). Qed.
Lemma lem1572565 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572566 : term217 = term58.
Proof. exact (@lem1572565 term46). Qed.
Lemma lem1572567 : term266 = term266.
Proof. exact (eq_refl term266). Qed.
Lemma lem1572568 : term265 = term267.
Proof. exact (MK_COMB (@lem1572567) (@lem1572566)). Qed.
Lemma lem1572569 : term267 = term58.
Proof. exact (@lem1483448 term58). Qed.
Lemma lem1572570 : term265 = term58.
Proof. exact (TRANS (@lem1572568) (@lem1572569)). Qed.
Lemma lem1572571 : term264 = term58.
Proof. exact (TRANS (@lem1572563) (@lem1572570)). Qed.
Lemma lem1572572 (y : real) : (term263 y) = term58.
Proof. exact (TRANS (@lem1572562 y) (@lem1572571)). Qed.
Lemma lem1572573 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572574 (y : real) : (term268 y) = term269.
Proof. exact (MK_COMB (@lem1572573) (@lem1572572 y)). Qed.
Lemma lem1572575 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572576 (y : real) : (term253 y) = term270.
Proof. exact (MK_COMB (@lem1572574 y) (@lem1572575)). Qed.
Lemma lem1572577 (y : real) : (term252 y) = term270.
Proof. exact (TRANS (@lem1572535 y) (@lem1572576 y)). Qed.
Lemma lem1572578 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572579 (x : real) (y : real) : (term326 x y) = (term326 x y).
Proof. exact (MK_COMB (@lem1572578) (@lem1572534 x y)). Qed.
Lemma lem1572580 (x : real) (y : real) : (term336 x y) = (term337 x y).
Proof. exact (MK_COMB (@lem1572579 x y) (@lem1572577 y)). Qed.
Lemma lem1572581 (z : real) (y : real) : (term271 z y) = (term272 z y).
Proof. exact (@lem1483525 (term273 z y) term58). Qed.
Lemma lem1572582 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572595 (y : real) (z : real) : (term273 z y) = (term274 y z).
Proof. exact (@lem1483488 y (term153 z)). Qed.
Lemma lem1572596 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1572597 (y : real) (z : real) : (term275 z y) = (term276 y z).
Proof. exact (MK_COMB (@lem1572596) (@lem1572595 y z)). Qed.
Lemma lem1572598 (y : real) (z : real) : (term277 z y) = (term278 y z).
Proof. exact (MK_COMB (@lem1572597 y z) (@lem1572582)). Qed.
Lemma lem1572599 (y : real) (z : real) : (term278 y z) = (term279 y z).
Proof. exact (@lem1483519 (term274 y z) term58). Qed.
Lemma lem1572601 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572602 : term217 = term58.
Proof. exact (@lem1572601 term46). Qed.
Lemma lem1572603 (y : real) (z : real) : (term280 y z) = (term280 y z).
Proof. exact (eq_refl (term280 y z)). Qed.
Lemma lem1572604 (y : real) (z : real) : (term279 y z) = (term281 y z).
Proof. exact (MK_COMB (@lem1572603 y z) (@lem1572602)). Qed.
Lemma lem1572605 (y : real) (z : real) : (term281 y z) = (term274 y z).
Proof. exact (@lem1483450 (term274 y z)). Qed.
Lemma lem1572606 (y : real) (z : real) : (term279 y z) = (term274 y z).
Proof. exact (TRANS (@lem1572604 y z) (@lem1572605 y z)). Qed.
Lemma lem1572607 (y : real) (z : real) : (term278 y z) = (term274 y z).
Proof. exact (TRANS (@lem1572599 y z) (@lem1572606 y z)). Qed.
Lemma lem1572608 (y : real) (z : real) : (term277 z y) = (term274 y z).
Proof. exact (TRANS (@lem1572598 y z) (@lem1572607 y z)). Qed.
Lemma lem1572609 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572610 (y : real) (z : real) : (term282 z y) = (term283 y z).
Proof. exact (MK_COMB (@lem1572609) (@lem1572608 y z)). Qed.
Lemma lem1572611 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572612 (y : real) (z : real) : (term272 z y) = (term284 y z).
Proof. exact (MK_COMB (@lem1572610 y z) (@lem1572611)). Qed.
Lemma lem1572613 (y : real) (z : real) : (term271 z y) = (term284 y z).
Proof. exact (TRANS (@lem1572581 z y) (@lem1572612 y z)). Qed.
Lemma lem1572614 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572615 (x : real) (y : real) : (term338 x y) = (term339 x y).
Proof. exact (MK_COMB (@lem1572614) (@lem1572580 x y)). Qed.
Lemma lem1572616 (x : real) (y : real) (z : real) : (term340 x z y) = (term341 x y z).
Proof. exact (MK_COMB (@lem1572615 x y) (@lem1572613 y z)). Qed.
Lemma lem1572617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572618 (x : real) (y : real) : (term331 x y) = (term331 x y).
Proof. exact (MK_COMB (@lem1572617) (@lem1572501 x y)). Qed.
Lemma lem1572619 (x : real) (y : real) (z : real) : (term303 x z y) = (term342 x y z).
Proof. exact (MK_COMB (@lem1572618 x y) (@lem1572616 x y z)). Qed.
Lemma lem1572620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572621 (y : real) (z : real) : (term304 y z) = (term343 y z).
Proof. exact (MK_COMB (@lem1572620) (@lem1572468 y z)). Qed.
Lemma lem1572622 (x : real) (y : real) (z : real) : (term306 x z y) = (term344 x y z).
Proof. exact (MK_COMB (@lem1572621 y z) (@lem1572619 x y z)). Qed.
Lemma lem1572623 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572624 (x : real) (y : real) (z : real) : (term313 x y z) = (term345 x y z).
Proof. exact (MK_COMB (@lem1572623) (@lem1572449 x y z)). Qed.
Lemma lem1572625 (x : real) (y : real) (z : real) : (term314 x z y) = (term346 x y z).
Proof. exact (MK_COMB (@lem1572624 x y z) (@lem1572622 x y z)). Qed.
Lemma lem1572637 (x : real) (y : real) (z : real) : (term244 x y z) = (term346 x y z).
Proof. exact (TRANS (@lem1572276 x z y) (@lem1572625 x y z)). Qed.
Lemma lem1572638 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572639 (x : real) (y : real) (z : real) : (term294 x y z) = (term347 x y z).
Proof. exact (MK_COMB (@lem1572638) (@lem1572637 x y z)). Qed.
Lemma lem1572640 (y : real) (x : real) (z : real) : (term295 y x z) = (term348 y x z).
Proof. exact (MK_COMB (@lem1572639 x y z) (@lem1572259 y x z)). Qed.
Lemma lem1572641 (y : real) (x : real) (z : real) : (term186 x y z) = (term348 y x z).
Proof. exact (TRANS (@lem1572212 y x z) (@lem1572640 y x z)). Qed.
Lemma lem1572642 (y : real) (x : real) (z : real) : (term64 x y z) = (term348 y x z).
Proof. exact (TRANS (@lem1571928 x y z) (@lem1572641 y x z)). Qed.
Lemma lem1572644 (x : real) (a : real) (y : real) (r : real) : (term168 x y a r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1572645 (x : real) (y : real) (z : real) : (term60 x y z) = (term349 x y z).
Proof. exact (@lem1572644 x (term7 x y z) (real_max y z) term58). Qed.
Lemma lem1572658 (x : real) (y : real) (z : real) : (term350 x y z) = (term351 x y z).
Proof. exact (@lem1483488 (term160 y z) (term7 x y z)). Qed.
Lemma lem1572659 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572660 (x : real) (y : real) (z : real) : (term352 x y z) = (term353 x y z).
Proof. exact (MK_COMB (@lem1572659) (@lem1572658 x y z)). Qed.
Lemma lem1572661 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572662 (x : real) (y : real) (z : real) : (term354 x y z) = (term355 x y z).
Proof. exact (MK_COMB (@lem1572660 x y z) (@lem1572661)). Qed.
Lemma lem1572675 (x : real) (y : real) (z : real) : (term356 y z x) = (term357 x y z).
Proof. exact (@lem1483488 (term153 x) (term7 x y z)). Qed.
Lemma lem1572676 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572677 (x : real) (y : real) (z : real) : (term358 y z x) = (term359 x y z).
Proof. exact (MK_COMB (@lem1572676) (@lem1572675 x y z)). Qed.
Lemma lem1572678 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572679 (x : real) (y : real) (z : real) : (term360 y z x) = (term361 x y z).
Proof. exact (MK_COMB (@lem1572677 x y z) (@lem1572678)). Qed.
Lemma lem1572680 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572681 (x : real) (y : real) (z : real) : (term362 y z x) = (term363 x y z).
Proof. exact (MK_COMB (@lem1572680) (@lem1572679 x y z)). Qed.
Lemma lem1572682 (x : real) (y : real) (z : real) : (term349 x y z) = (term364 x y z).
Proof. exact (MK_COMB (@lem1572681 x y z) (@lem1572662 x y z)). Qed.
Lemma lem1572683 (x : real) (y : real) (z : real) : (term60 x y z) = (term364 x y z).
Proof. exact (TRANS (@lem1572645 x y z) (@lem1572682 x y z)). Qed.
Lemma lem1572685 (x : real) (a : real) (y : real) (r : real) : (term168 x y a r) = (term149 x a y r).
Proof. exact (proj1 (@lem1482709 x a (@el real) y (@el real) r)). Qed.
Lemma lem1572686 (x : real) (y : real) (z : real) : (term355 x y z) = (term365 x y z).
Proof. exact (@lem1572685 y (term7 x y z) z term58). Qed.
Lemma lem1572699 (x : real) (y : real) (z : real) : (term366 x y z) = (term367 x y z).
Proof. exact (@lem1483488 (term153 z) (term7 x y z)). Qed.
Lemma lem1572700 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572701 (x : real) (y : real) (z : real) : (term368 x y z) = (term369 x y z).
Proof. exact (MK_COMB (@lem1572700) (@lem1572699 x y z)). Qed.
Lemma lem1572702 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572703 (x : real) (y : real) (z : real) : (term370 x y z) = (term371 x y z).
Proof. exact (MK_COMB (@lem1572701 x y z) (@lem1572702)). Qed.
Lemma lem1572716 (x : real) (y : real) (z : real) : (term372 x z y) = (term373 x y z).
Proof. exact (@lem1483488 (term153 y) (term7 x y z)). Qed.
Lemma lem1572717 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572718 (x : real) (y : real) (z : real) : (term374 x z y) = (term375 x y z).
Proof. exact (MK_COMB (@lem1572717) (@lem1572716 x y z)). Qed.
Lemma lem1572719 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572720 (x : real) (y : real) (z : real) : (term376 x z y) = (term377 x y z).
Proof. exact (MK_COMB (@lem1572718 x y z) (@lem1572719)). Qed.
Lemma lem1572721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572722 (x : real) (y : real) (z : real) : (term378 x z y) = (term379 x y z).
Proof. exact (MK_COMB (@lem1572721) (@lem1572720 x y z)). Qed.
Lemma lem1572723 (x : real) (y : real) (z : real) : (term365 x y z) = (term380 x y z).
Proof. exact (MK_COMB (@lem1572722 x y z) (@lem1572703 x y z)). Qed.
Lemma lem1572724 (x : real) (y : real) (z : real) : (term355 x y z) = (term380 x y z).
Proof. exact (TRANS (@lem1572686 x y z) (@lem1572723 x y z)). Qed.
Lemma lem1572725 (x : real) (y : real) (z : real) : (term363 x y z) = (term363 x y z).
Proof. exact (eq_refl (term363 x y z)). Qed.
Lemma lem1572726 (x : real) (y : real) (z : real) : (term364 x y z) = (term381 x y z).
Proof. exact (MK_COMB (@lem1572725 x y z) (@lem1572724 x y z)). Qed.
Lemma lem1572727 (x : real) (y : real) (z : real) : (term60 x y z) = (term381 x y z).
Proof. exact (TRANS (@lem1572683 x y z) (@lem1572726 x y z)). Qed.
Lemma lem1572728 (x : real) (y : real) (z : real) : (term382 x y z) = (term381 x y z).
Proof. exact (eq_refl (term382 x y z)). Qed.
Lemma lem1572729 (x : real) (y : real) (z : real) : (term381 x y z) = (term382 x y z).
Proof. exact (SYM (@lem1572728 x y z)). Qed.
Lemma lem1572730 (z : real) (x : real) (y : real) : (term382 x y z) = (term383 z x y).
Proof. exact (@lem1483205 z (term384 x y z) (real_max x y)). Qed.
Lemma lem1572731 (z : real) (x : real) (y : real) : (term381 x y z) = (term383 z x y).
Proof. exact (TRANS (@lem1572729 x y z) (@lem1572730 z x y)). Qed.
Lemma lem1572732 (z : real) (x : real) (y : real) : (term385 z x y) = (term386 z x y).
Proof. exact (eq_refl (term385 z x y)). Qed.
Lemma lem1572733 (x : real) (y : real) (z : real) : (term387 x y z) = (term387 x y z).
Proof. exact (eq_refl (term387 x y z)). Qed.
Lemma lem1572734 (z : real) (x : real) (y : real) : (term388 z x y) = (term389 z x y).
Proof. exact (MK_COMB (@lem1572733 x y z) (@lem1572732 z x y)). Qed.
Lemma lem1572735 (x : real) (y : real) (z : real) : (term390 x y z) = (term391 x y z).
Proof. exact (eq_refl (term390 x y z)). Qed.
Lemma lem1572736 (z : real) (x : real) (y : real) : (term392 z x y) = (term392 z x y).
Proof. exact (eq_refl (term392 z x y)). Qed.
Lemma lem1572737 (x : real) (y : real) (z : real) : (term393 x y z) = (term394 x y z).
Proof. exact (MK_COMB (@lem1572736 z x y) (@lem1572735 x y z)). Qed.
Lemma lem1572738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572739 (x : real) (y : real) (z : real) : (term395 x y z) = (term396 x y z).
Proof. exact (MK_COMB (@lem1572738) (@lem1572737 x y z)). Qed.
Lemma lem1572740 (z : real) (x : real) (y : real) : (term383 z x y) = (term397 z x y).
Proof. exact (MK_COMB (@lem1572739 x y z) (@lem1572734 z x y)). Qed.
Lemma lem1572741 (x : real) (y : real) (z : real) : (term398 x y z) = (term398 x y z).
Proof. exact (eq_refl (term398 x y z)). Qed.
Lemma lem1572742 (z : real) (x : real) (y : real) : ((term381 x y z) = (term383 z x y)) = ((term381 x y z) = (term397 z x y)).
Proof. exact (MK_COMB (@lem1572741 x y z) (@lem1572740 z x y)). Qed.
Lemma lem1572743 (z : real) (x : real) (y : real) : (term381 x y z) = (term397 z x y).
Proof. exact (EQ_MP (@lem1572742 z x y) (@lem1572731 z x y)). Qed.
Lemma lem1572744 (z : real) (x : real) (y : real) : (term399 z x y) = (term400 z x y).
Proof. exact (@lem1483527 z (real_max x y)). Qed.
Lemma lem1572757 (z : real) (x : real) (y : real) : (term247 z x y) = (term248 z x y).
Proof. exact (@lem1483519 z (real_max x y)). Qed.
Lemma lem1572758 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1572759 (z : real) (x : real) (y : real) : (term401 z x y) = (term402 z x y).
Proof. exact (MK_COMB (@lem1572758) (@lem1572757 z x y)). Qed.
Lemma lem1572760 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572761 (z : real) (x : real) (y : real) : (term400 z x y) = (term403 z x y).
Proof. exact (MK_COMB (@lem1572759 z x y) (@lem1572760)). Qed.
Lemma lem1572762 (z : real) (x : real) (y : real) : (term399 z x y) = (term403 z x y).
Proof. exact (TRANS (@lem1572744 z x y) (@lem1572761 z x y)). Qed.
Lemma lem1572763 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572764 (y : real) (z : real) : (term326 y z) = (term326 y z).
Proof. exact (MK_COMB (@lem1572763) (@lem1572394 y z)). Qed.
Lemma lem1572765 (y : real) (z : real) : (term336 y z) = (term337 y z).
Proof. exact (MK_COMB (@lem1572764 y z) (@lem1572440 z)). Qed.
Lemma lem1572766 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572767 (x : real) (z : real) : (term326 x z) = (term326 x z).
Proof. exact (MK_COMB (@lem1572766) (@lem1572361 x z)). Qed.
Lemma lem1572768 (x : real) (y : real) (z : real) : (term391 x y z) = (term404 x y z).
Proof. exact (MK_COMB (@lem1572767 x z) (@lem1572765 y z)). Qed.
Lemma lem1572769 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572770 (z : real) (x : real) (y : real) : (term392 z x y) = (term405 z x y).
Proof. exact (MK_COMB (@lem1572769) (@lem1572762 z x y)). Qed.
Lemma lem1572771 (x : real) (y : real) (z : real) : (term394 x y z) = (term406 x y z).
Proof. exact (MK_COMB (@lem1572770 z x y) (@lem1572768 x y z)). Qed.
Lemma lem1572772 (x : real) (y : real) (z : real) : (term407 x y z) = (term408 x y z).
Proof. exact (@lem1483525 (real_max x y) z). Qed.
Lemma lem1572778 (x : real) (y : real) (z : real) : (term206 x y z) = (term207 x y z).
Proof. exact (@lem1483519 (real_max x y) z). Qed.
Lemma lem1572783 (z : real) (x : real) (y : real) : (term207 x y z) = (term208 z x y).
Proof. exact (@lem1483488 (term153 z) (real_max x y)). Qed.
Lemma lem1572785 (z : real) (x : real) (y : real) : (term206 x y z) = (term208 z x y).
Proof. exact (TRANS (@lem1572778 x y z) (@lem1572783 z x y)). Qed.
Lemma lem1572786 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572787 (z : real) (x : real) (y : real) : (term409 x y z) = (term221 z x y).
Proof. exact (MK_COMB (@lem1572786) (@lem1572785 z x y)). Qed.
Lemma lem1572788 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572789 (z : real) (x : real) (y : real) : (term408 x y z) = (term212 z x y).
Proof. exact (MK_COMB (@lem1572787 z x y) (@lem1572788)). Qed.
Lemma lem1572790 (z : real) (x : real) (y : real) : (term407 x y z) = (term212 z x y).
Proof. exact (TRANS (@lem1572772 x y z) (@lem1572789 z x y)). Qed.
Lemma lem1572791 (x : real) (y : real) : (term222 x y) = (term223 x y).
Proof. exact (@lem1483525 (term224 x y) term58). Qed.
Lemma lem1572809 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (@lem1483519 (term224 x y) term58). Qed.
Lemma lem1572811 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572812 : term217 = term58.
Proof. exact (@lem1572811 term46). Qed.
Lemma lem1572813 (x : real) (y : real) : (term227 x y) = (term227 x y).
Proof. exact (eq_refl (term227 x y)). Qed.
Lemma lem1572814 (x : real) (y : real) : (term226 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem1572813 x y) (@lem1572812)). Qed.
Lemma lem1572815 (x : real) (y : real) : (term228 x y) = (term224 x y).
Proof. exact (@lem1483450 (term224 x y)). Qed.
Lemma lem1572816 (x : real) (y : real) : (term226 x y) = (term224 x y).
Proof. exact (TRANS (@lem1572814 x y) (@lem1572815 x y)). Qed.
Lemma lem1572818 (x : real) (y : real) : (term225 x y) = (term224 x y).
Proof. exact (TRANS (@lem1572809 x y) (@lem1572816 x y)). Qed.
Lemma lem1572819 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572820 (x : real) (y : real) : (term229 x y) = (term230 x y).
Proof. exact (MK_COMB (@lem1572819) (@lem1572818 x y)). Qed.
Lemma lem1572821 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572822 (x : real) (y : real) : (term223 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1572820 x y) (@lem1572821)). Qed.
Lemma lem1572823 (x : real) (y : real) : (term222 x y) = (term222 x y).
Proof. exact (TRANS (@lem1572791 x y) (@lem1572822 x y)). Qed.
Lemma lem1572824 (x : real) (y : real) : (term233 x y) = (term234 x y).
Proof. exact (@lem1483525 (term235 x y) term58). Qed.
Lemma lem1572842 (x : real) (y : real) : (term236 x y) = (term237 x y).
Proof. exact (@lem1483519 (term235 x y) term58). Qed.
Lemma lem1572844 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572845 : term217 = term58.
Proof. exact (@lem1572844 term46). Qed.
Lemma lem1572846 (x : real) (y : real) : (term238 x y) = (term238 x y).
Proof. exact (eq_refl (term238 x y)). Qed.
Lemma lem1572847 (x : real) (y : real) : (term237 x y) = (term239 x y).
Proof. exact (MK_COMB (@lem1572846 x y) (@lem1572845)). Qed.
Lemma lem1572848 (x : real) (y : real) : (term239 x y) = (term235 x y).
Proof. exact (@lem1483450 (term235 x y)). Qed.
Lemma lem1572849 (x : real) (y : real) : (term237 x y) = (term235 x y).
Proof. exact (TRANS (@lem1572847 x y) (@lem1572848 x y)). Qed.
Lemma lem1572851 (x : real) (y : real) : (term236 x y) = (term235 x y).
Proof. exact (TRANS (@lem1572842 x y) (@lem1572849 x y)). Qed.
Lemma lem1572852 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572853 (x : real) (y : real) : (term240 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1572852) (@lem1572851 x y)). Qed.
Lemma lem1572854 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572855 (x : real) (y : real) : (term234 x y) = (term233 x y).
Proof. exact (MK_COMB (@lem1572853 x y) (@lem1572854)). Qed.
Lemma lem1572856 (x : real) (y : real) : (term233 x y) = (term233 x y).
Proof. exact (TRANS (@lem1572824 x y) (@lem1572855 x y)). Qed.
Lemma lem1572857 (z : real) (x : real) (y : real) : (term212 z x y) = (term213 z x y).
Proof. exact (@lem1483525 (term208 z x y) term58). Qed.
Lemma lem1572875 (z : real) (x : real) (y : real) : (term214 z x y) = (term215 z x y).
Proof. exact (@lem1483519 (term208 z x y) term58). Qed.
Lemma lem1572877 (x : nat) : (term216 x) = term58.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1572878 : term217 = term58.
Proof. exact (@lem1572877 term46). Qed.
Lemma lem1572879 (z : real) (x : real) (y : real) : (term218 z x y) = (term218 z x y).
Proof. exact (eq_refl (term218 z x y)). Qed.
Lemma lem1572880 (z : real) (x : real) (y : real) : (term215 z x y) = (term219 z x y).
Proof. exact (MK_COMB (@lem1572879 z x y) (@lem1572878)). Qed.
Lemma lem1572881 (z : real) (x : real) (y : real) : (term219 z x y) = (term208 z x y).
Proof. exact (@lem1483450 (term208 z x y)). Qed.
Lemma lem1572882 (z : real) (x : real) (y : real) : (term215 z x y) = (term208 z x y).
Proof. exact (TRANS (@lem1572880 z x y) (@lem1572881 z x y)). Qed.
Lemma lem1572884 (z : real) (x : real) (y : real) : (term214 z x y) = (term208 z x y).
Proof. exact (TRANS (@lem1572875 z x y) (@lem1572882 z x y)). Qed.
Lemma lem1572885 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572886 (z : real) (x : real) (y : real) : (term220 z x y) = (term221 z x y).
Proof. exact (MK_COMB (@lem1572885) (@lem1572884 z x y)). Qed.
Lemma lem1572887 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572888 (z : real) (x : real) (y : real) : (term213 z x y) = (term212 z x y).
Proof. exact (MK_COMB (@lem1572886 z x y) (@lem1572887)). Qed.
Lemma lem1572889 (z : real) (x : real) (y : real) : (term212 z x y) = (term212 z x y).
Proof. exact (TRANS (@lem1572857 z x y) (@lem1572888 z x y)). Qed.
Lemma lem1572890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572891 (x : real) (y : real) : (term410 x y) = (term410 x y).
Proof. exact (MK_COMB (@lem1572890) (@lem1572856 x y)). Qed.
Lemma lem1572892 (z : real) (x : real) (y : real) : (term411 z x y) = (term411 z x y).
Proof. exact (MK_COMB (@lem1572891 x y) (@lem1572889 z x y)). Qed.
Lemma lem1572893 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572894 (x : real) (y : real) : (term412 x y) = (term412 x y).
Proof. exact (MK_COMB (@lem1572893) (@lem1572823 x y)). Qed.
Lemma lem1572895 (z : real) (x : real) (y : real) : (term386 z x y) = (term386 z x y).
Proof. exact (MK_COMB (@lem1572894 x y) (@lem1572892 z x y)). Qed.
Lemma lem1572896 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572897 (z : real) (x : real) (y : real) : (term387 x y z) = (term231 z x y).
Proof. exact (MK_COMB (@lem1572896) (@lem1572790 z x y)). Qed.
Lemma lem1572898 (z : real) (x : real) (y : real) : (term389 z x y) = (term413 z x y).
Proof. exact (MK_COMB (@lem1572897 z x y) (@lem1572895 z x y)). Qed.
Lemma lem1572899 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572900 (x : real) (y : real) (z : real) : (term396 x y z) = (term414 x y z).
Proof. exact (MK_COMB (@lem1572899) (@lem1572771 x y z)). Qed.
Lemma lem1572901 (z : real) (x : real) (y : real) : (term397 z x y) = (term415 z x y).
Proof. exact (MK_COMB (@lem1572900 x y z) (@lem1572898 z x y)). Qed.
Lemma lem1572902 (z : real) (x : real) (y : real) : (term381 x y z) = (term415 z x y).
Proof. exact (TRANS (@lem1572743 z x y) (@lem1572901 z x y)). Qed.
Lemma lem1572904 (z : real) (x : real) (y : real) : (term416 z x y) = (term413 z x y).
Proof. exact (eq_refl (term416 z x y)). Qed.
Lemma lem1572905 (z : real) (x : real) (y : real) : (term413 z x y) = (term416 z x y).
Proof. exact (SYM (@lem1572904 z x y)). Qed.
Lemma lem1572906 (y : real) (z : real) (x : real) : (term416 z x y) = (term417 y z x).
Proof. exact (@lem1483205 y (term418 x y z) x). Qed.
Lemma lem1572907 (y : real) (z : real) (x : real) : (term413 z x y) = (term417 y z x).
Proof. exact (TRANS (@lem1572905 z x y) (@lem1572906 y z x)). Qed.
Lemma lem1572908 (y : real) (z : real) (x : real) : (term419 y z x) = (term420 y z x).
Proof. exact (eq_refl (term419 y z x)). Qed.
Lemma lem1572909 (x : real) (y : real) : (term304 x y) = (term304 x y).
Proof. exact (eq_refl (term304 x y)). Qed.
Lemma lem1572910 (y : real) (z : real) (x : real) : (term421 y z x) = (term422 y z x).
Proof. exact (MK_COMB (@lem1572909 x y) (@lem1572908 y z x)). Qed.
Lemma lem1572911 (x : real) (z : real) (y : real) : (term423 x z y) = (term424 x z y).
Proof. exact (eq_refl (term423 x z y)). Qed.
Lemma lem1572912 (y : real) (x : real) : (term309 y x) = (term309 y x).
Proof. exact (eq_refl (term309 y x)). Qed.
Lemma lem1572913 (x : real) (z : real) (y : real) : (term425 x z y) = (term426 x z y).
Proof. exact (MK_COMB (@lem1572912 y x) (@lem1572911 x z y)). Qed.
Lemma lem1572914 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572915 (x : real) (z : real) (y : real) : (term427 x z y) = (term428 x z y).
Proof. exact (MK_COMB (@lem1572914) (@lem1572913 x z y)). Qed.
Lemma lem1572916 (y : real) (z : real) (x : real) : (term417 y z x) = (term429 y z x).
Proof. exact (MK_COMB (@lem1572915 x z y) (@lem1572910 y z x)). Qed.
Lemma lem1572917 (z : real) (x : real) (y : real) : (term430 z x y) = (term430 z x y).
Proof. exact (eq_refl (term430 z x y)). Qed.
Lemma lem1572918 (y : real) (z : real) (x : real) : ((term413 z x y) = (term417 y z x)) = ((term413 z x y) = (term429 y z x)).
Proof. exact (MK_COMB (@lem1572917 z x y) (@lem1572916 y z x)). Qed.
Lemma lem1572919 (y : real) (z : real) (x : real) : (term413 z x y) = (term429 y z x).
Proof. exact (EQ_MP (@lem1572918 y z x) (@lem1572907 y z x)). Qed.
Lemma lem1572920 (y : real) (x : real) : (real_ge y x) = (term316 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1572926 (y : real) (x : real) : (real_sub y x) = (term274 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1572931 (x : real) (y : real) : (term274 y x) = (term273 x y).
Proof. exact (@lem1483488 (term153 x) y). Qed.
Lemma lem1572933 (x : real) (y : real) : (real_sub y x) = (term273 x y).
Proof. exact (TRANS (@lem1572926 y x) (@lem1572931 x y)). Qed.
Lemma lem1572934 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1572935 (x : real) (y : real) : (term317 y x) = (term318 x y).
Proof. exact (MK_COMB (@lem1572934) (@lem1572933 x y)). Qed.
Lemma lem1572936 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572937 (x : real) (y : real) : (term316 y x) = (term319 x y).
Proof. exact (MK_COMB (@lem1572935 x y) (@lem1572936)). Qed.
Lemma lem1572938 (x : real) (y : real) : (real_ge y x) = (term319 x y).
Proof. exact (TRANS (@lem1572920 y x) (@lem1572937 x y)). Qed.
Lemma lem1572939 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572940 (y : real) : (term285 y) = term286.
Proof. exact (MK_COMB (@lem1572939) (@lem1572577 y)). Qed.
Lemma lem1572941 (y : real) (z : real) : (term287 z y) = (term288 y z).
Proof. exact (MK_COMB (@lem1572940 y) (@lem1572613 y z)). Qed.
Lemma lem1572942 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572943 (x : real) (y : real) : (term326 x y) = (term326 x y).
Proof. exact (MK_COMB (@lem1572942) (@lem1572534 x y)). Qed.
Lemma lem1572944 (x : real) (y : real) (z : real) : (term431 x z y) = (term432 x y z).
Proof. exact (MK_COMB (@lem1572943 x y) (@lem1572941 y z)). Qed.
Lemma lem1572945 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572946 (y : real) (z : real) : (term326 z y) = (term343 y z).
Proof. exact (MK_COMB (@lem1572945) (@lem1572613 y z)). Qed.
Lemma lem1572947 (x : real) (y : real) (z : real) : (term424 x z y) = (term433 x y z).
Proof. exact (MK_COMB (@lem1572946 y z) (@lem1572944 x y z)). Qed.
Lemma lem1572948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572949 (x : real) (y : real) : (term309 y x) = (term331 x y).
Proof. exact (MK_COMB (@lem1572948) (@lem1572938 x y)). Qed.
Lemma lem1572950 (x : real) (y : real) (z : real) : (term426 x z y) = (term434 x y z).
Proof. exact (MK_COMB (@lem1572949 x y) (@lem1572947 x y z)). Qed.
Lemma lem1572951 (x : real) (y : real) : (real_gt x y) = (term334 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1572964 (x : real) (y : real) : (real_sub x y) = (term274 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1572965 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1572966 (x : real) (y : real) : (term335 x y) = (term283 x y).
Proof. exact (MK_COMB (@lem1572965) (@lem1572964 x y)). Qed.
Lemma lem1572967 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1572968 (x : real) (y : real) : (term334 x y) = (term284 x y).
Proof. exact (MK_COMB (@lem1572966 x y) (@lem1572967)). Qed.
Lemma lem1572969 (x : real) (y : real) : (real_gt x y) = (term284 x y).
Proof. exact (TRANS (@lem1572951 x y) (@lem1572968 x y)). Qed.
Lemma lem1572970 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572971 (x : real) (y : real) : (term326 y x) = (term343 x y).
Proof. exact (MK_COMB (@lem1572970) (@lem1572166 x y)). Qed.
Lemma lem1572972 (y : real) (x : real) (z : real) : (term327 y z x) = (term296 y x z).
Proof. exact (MK_COMB (@lem1572971 x y) (@lem1572202 x z)). Qed.
Lemma lem1572973 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572974 (x : real) : (term285 x) = term286.
Proof. exact (MK_COMB (@lem1572973) (@lem1572133 x)). Qed.
Lemma lem1572975 (y : real) (x : real) (z : real) : (term435 y z x) = (term436 y x z).
Proof. exact (MK_COMB (@lem1572974 x) (@lem1572972 y x z)). Qed.
Lemma lem1572976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572977 (x : real) (z : real) : (term326 z x) = (term343 x z).
Proof. exact (MK_COMB (@lem1572976) (@lem1572202 x z)). Qed.
Lemma lem1572978 (y : real) (x : real) (z : real) : (term420 y z x) = (term437 y x z).
Proof. exact (MK_COMB (@lem1572977 x z) (@lem1572975 y x z)). Qed.
Lemma lem1572979 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1572980 (x : real) (y : real) : (term304 x y) = (term343 x y).
Proof. exact (MK_COMB (@lem1572979) (@lem1572969 x y)). Qed.
Lemma lem1572981 (y : real) (x : real) (z : real) : (term422 y z x) = (term438 y x z).
Proof. exact (MK_COMB (@lem1572980 x y) (@lem1572978 y x z)). Qed.
Lemma lem1572982 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1572983 (x : real) (y : real) (z : real) : (term428 x z y) = (term439 x y z).
Proof. exact (MK_COMB (@lem1572982) (@lem1572950 x y z)). Qed.
Lemma lem1572984 (y : real) (x : real) (z : real) : (term429 y z x) = (term440 y x z).
Proof. exact (MK_COMB (@lem1572983 x y z) (@lem1572981 y x z)). Qed.
Lemma lem1572996 (y : real) (x : real) (z : real) : (term413 z x y) = (term440 y x z).
Proof. exact (TRANS (@lem1572919 y z x) (@lem1572984 y x z)). Qed.
Lemma lem1572998 (x : real) (a : real) (y : real) (r : real) : (term441 a x y r) = (term442 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem1572999 (x : real) (z : real) (y : real) : (term403 z x y) = (term443 x z y).
Proof. exact (@lem1572998 x z y term58). Qed.
Lemma lem1573012 (y : real) (z : real) : (term274 z y) = (term273 y z).
Proof. exact (@lem1483488 (term153 y) z). Qed.
Lemma lem1573013 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1573014 (y : real) (z : real) : (term444 z y) = (term318 y z).
Proof. exact (MK_COMB (@lem1573013) (@lem1573012 y z)). Qed.
Lemma lem1573015 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573016 (y : real) (z : real) : (term445 z y) = (term319 y z).
Proof. exact (MK_COMB (@lem1573014 y z) (@lem1573015)). Qed.
Lemma lem1573029 (x : real) (z : real) : (term274 z x) = (term273 x z).
Proof. exact (@lem1483488 (term153 x) z). Qed.
Lemma lem1573030 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1573031 (x : real) (z : real) : (term444 z x) = (term318 x z).
Proof. exact (MK_COMB (@lem1573030) (@lem1573029 x z)). Qed.
Lemma lem1573032 : term58 = term58.
Proof. exact (eq_refl term58). Qed.
Lemma lem1573033 (x : real) (z : real) : (term445 z x) = (term319 x z).
Proof. exact (MK_COMB (@lem1573031 x z) (@lem1573032)). Qed.
Lemma lem1573034 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573035 (x : real) (z : real) : (term446 z x) = (term331 x z).
Proof. exact (MK_COMB (@lem1573034) (@lem1573033 x z)). Qed.
Lemma lem1573036 (x : real) (y : real) (z : real) : (term443 x z y) = (term447 x y z).
Proof. exact (MK_COMB (@lem1573035 x z) (@lem1573016 y z)). Qed.
Lemma lem1573037 (x : real) (y : real) (z : real) : (term403 z x y) = (term447 x y z).
Proof. exact (TRANS (@lem1572999 x z y) (@lem1573036 x y z)). Qed.
Lemma lem1573038 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1573039 (x : real) (y : real) (z : real) : (term405 z x y) = (term448 x y z).
Proof. exact (MK_COMB (@lem1573038) (@lem1573037 x y z)). Qed.
Lemma lem1573040 (x : real) (y : real) (z : real) : (term404 x y z) = (term404 x y z).
Proof. exact (eq_refl (term404 x y z)). Qed.
Lemma lem1573043 (x : real) (y : real) (z : real) : (term406 x y z) = (term449 x y z).
Proof. exact (MK_COMB (@lem1573039 x y z) (@lem1573040 x y z)). Qed.
Lemma lem1573044 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573045 (x : real) (y : real) (z : real) : (term414 x y z) = (term450 x y z).
Proof. exact (MK_COMB (@lem1573044) (@lem1573043 x y z)). Qed.
Lemma lem1573046 (y : real) (x : real) (z : real) : (term415 z x y) = (term451 y x z).
Proof. exact (MK_COMB (@lem1573045 x y z) (@lem1572996 y x z)). Qed.
Lemma lem1573047 (y : real) (x : real) (z : real) : (term381 x y z) = (term451 y x z).
Proof. exact (TRANS (@lem1572902 z x y) (@lem1573046 y x z)). Qed.
Lemma lem1573048 (y : real) (x : real) (z : real) : (term60 x y z) = (term451 y x z).
Proof. exact (TRANS (@lem1572727 x y z) (@lem1573047 y x z)). Qed.
Lemma lem1573049 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1573050 (y : real) (x : real) (z : real) : (term66 x y z) = (term452 y x z).
Proof. exact (MK_COMB (@lem1573049) (@lem1572642 y x z)). Qed.
Lemma lem1573051 (y : real) (x : real) (z : real) : (term67 x y z) = (term453 y x z).
Proof. exact (MK_COMB (@lem1573050 y x z) (@lem1573048 y x z)). Qed.
Lemma lem1573052 (y : real) (x : real) (z : real) (h1 : term453 y x z) : term453 y x z.
Proof. exact (h1). Qed.
Lemma lem1573053 (y : real) (x : real) (z : real) (h1 : term348 y x z) : term348 y x z.
Proof. exact (h1). Qed.
Lemma lem1573054 (x : real) (y : real) (z : real) (h1 : term346 x y z) : term346 x y z.
Proof. exact (h1). Qed.
Lemma lem1573055 (x : real) (y : real) (z : real) (h1 : term333 x y z) : term333 x y z.
Proof. exact (h1). Qed.
Lemma lem1573056 (x : real) (y : real) (z : real) (h1 : term333 x y z) : term332 x y z.
Proof. exact (proj2 (@lem1573055 x y z h1)). Qed.
Lemma lem1573058 (x : real) (y : real) (z : real) (h1 : term333 x y z) : term330 x y z.
Proof. exact (proj2 (@lem1573056 x y z h1)). Qed.
Lemma lem1573060 (x : real) (y : real) (z : real) (h1 : term333 x y z) : term270.
Proof. exact (proj2 (@lem1573058 x y z h1)). Qed.
Lemma lem1573065 (n : nat) (m : nat) : (term454 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1573066 : term270 = term455.
Proof. exact (@lem1573065 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1573067 : term455 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1573068 : term270 = False.
Proof. exact (TRANS (@lem1573066) (@lem1573067)). Qed.
Lemma lem1573069 (x : real) (y : real) (z : real) (h1 : term333 x y z) : False.
Proof. exact (EQ_MP (@lem1573068) (@lem1573060 x y z h1)). Qed.
Lemma lem1573070 (x : real) (y : real) (z : real) (h1 : term344 x y z) : term344 x y z.
Proof. exact (h1). Qed.
Lemma lem1573071 (x : real) (y : real) (z : real) (h1 : term344 x y z) : term342 x y z.
Proof. exact (proj2 (@lem1573070 x y z h1)). Qed.
Lemma lem1573073 (x : real) (y : real) (z : real) (h1 : term344 x y z) : term341 x y z.
Proof. exact (proj2 (@lem1573071 x y z h1)). Qed.
Lemma lem1573076 (x : real) (y : real) (z : real) (h1 : term344 x y z) : term337 x y.
Proof. exact (proj1 (@lem1573073 x y z h1)). Qed.
Lemma lem1573077 (x : real) (y : real) (z : real) (h1 : term344 x y z) : term270.
Proof. exact (proj2 (@lem1573076 x y z h1)). Qed.
Lemma lem1573080 (n : nat) (m : nat) : (term454 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1573081 : term270 = term455.
Proof. exact (@lem1573080 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1573082 : term455 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1573083 : term270 = False.
Proof. exact (TRANS (@lem1573081) (@lem1573082)). Qed.
Lemma lem1573084 (x : real) (y : real) (z : real) (h1 : term344 x y z) : False.
Proof. exact (EQ_MP (@lem1573083) (@lem1573077 x y z h1)). Qed.
Lemma lem1573085 (x : real) (y : real) (z : real) (h1 : term346 x y z) : False.
Proof. exact (or_elim (@lem1573054 x y z h1) (fun h0 : term333 x y z => @lem1573069 x y z h0) (fun h0 : term344 x y z => @lem1573084 x y z h0)). Qed.
Lemma lem1573086 (y : real) (x : real) (z : real) (h1 : term298 y x z) : term298 y x z.
Proof. exact (h1). Qed.
Lemma lem1573087 (y : real) (x : real) (z : real) (h1 : term298 y x z) : term291 y x z.
Proof. exact (proj2 (@lem1573086 y x z h1)). Qed.
Lemma lem1573092 (y : real) (x : real) (z : real) (h1 : term298 y x z) : term288 x y.
Proof. exact (proj1 (@lem1573087 y x z h1)). Qed.
Lemma lem1573094 (y : real) (x : real) (z : real) (h1 : term298 y x z) : term270.
Proof. exact (proj1 (@lem1573092 y x z h1)). Qed.
Lemma lem1573096 (n : nat) (m : nat) : (term454 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1573097 : term270 = term455.
Proof. exact (@lem1573096 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1573098 : term455 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1573099 : term270 = False.
Proof. exact (TRANS (@lem1573097) (@lem1573098)). Qed.
Lemma lem1573100 (y : real) (x : real) (z : real) (h1 : term298 y x z) : False.
Proof. exact (EQ_MP (@lem1573099) (@lem1573094 y x z h1)). Qed.
Lemma lem1573101 (y : real) (x : real) (z : real) (h1 : term348 y x z) : False.
Proof. exact (or_elim (@lem1573053 y x z h1) (fun h0 : term346 x y z => @lem1573085 x y z h0) (fun h0 : term298 y x z => @lem1573100 y x z h0)). Qed.
Lemma lem1573102 (y : real) (x : real) (z : real) (h1 : term451 y x z) : term451 y x z.
Proof. exact (h1). Qed.
Lemma lem1573103 (x : real) (y : real) (z : real) (h1 : term449 x y z) : term449 x y z.
Proof. exact (h1). Qed.
Lemma lem1573104 (x : real) (y : real) (z : real) (h1 : term449 x y z) : term404 x y z.
Proof. exact (proj2 (@lem1573103 x y z h1)). Qed.
Lemma lem1573108 (x : real) (y : real) (z : real) (h1 : term449 x y z) : term337 y z.
Proof. exact (proj2 (@lem1573104 x y z h1)). Qed.
Lemma lem1573110 (x : real) (y : real) (z : real) (h1 : term449 x y z) : term270.
Proof. exact (proj2 (@lem1573108 x y z h1)). Qed.
Lemma lem1573113 (n : nat) (m : nat) : (term454 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1573114 : term270 = term455.
Proof. exact (@lem1573113 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1573115 : term455 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1573116 : term270 = False.
Proof. exact (TRANS (@lem1573114) (@lem1573115)). Qed.
Lemma lem1573117 (x : real) (y : real) (z : real) (h1 : term449 x y z) : False.
Proof. exact (EQ_MP (@lem1573116) (@lem1573110 x y z h1)). Qed.
Lemma lem1573118 (y : real) (x : real) (z : real) (h1 : term440 y x z) : term440 y x z.
Proof. exact (h1). Qed.
Lemma lem1573119 (x : real) (y : real) (z : real) (h1 : term434 x y z) : term434 x y z.
Proof. exact (h1). Qed.
Lemma lem1573120 (x : real) (y : real) (z : real) (h1 : term434 x y z) : term433 x y z.
Proof. exact (proj2 (@lem1573119 x y z h1)). Qed.
Lemma lem1573122 (x : real) (y : real) (z : real) (h1 : term434 x y z) : term432 x y z.
Proof. exact (proj2 (@lem1573120 x y z h1)). Qed.
Lemma lem1573124 (x : real) (y : real) (z : real) (h1 : term434 x y z) : term288 y z.
Proof. exact (proj2 (@lem1573122 x y z h1)). Qed.
Lemma lem1573127 (x : real) (y : real) (z : real) (h1 : term434 x y z) : term270.
Proof. exact (proj1 (@lem1573124 x y z h1)). Qed.
Lemma lem1573129 (n : nat) (m : nat) : (term454 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1573130 : term270 = term455.
Proof. exact (@lem1573129 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1573131 : term455 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1573132 : term270 = False.
Proof. exact (TRANS (@lem1573130) (@lem1573131)). Qed.
Lemma lem1573133 (x : real) (y : real) (z : real) (h1 : term434 x y z) : False.
Proof. exact (EQ_MP (@lem1573132) (@lem1573127 x y z h1)). Qed.
Lemma lem1573134 (y : real) (x : real) (z : real) (h1 : term438 y x z) : term438 y x z.
Proof. exact (h1). Qed.
Lemma lem1573135 (y : real) (x : real) (z : real) (h1 : term438 y x z) : term437 y x z.
Proof. exact (proj2 (@lem1573134 y x z h1)). Qed.
Lemma lem1573137 (y : real) (x : real) (z : real) (h1 : term438 y x z) : term436 y x z.
Proof. exact (proj2 (@lem1573135 y x z h1)). Qed.
Lemma lem1573140 (y : real) (x : real) (z : real) (h1 : term438 y x z) : term270.
Proof. exact (proj1 (@lem1573137 y x z h1)). Qed.
Lemma lem1573144 (n : nat) (m : nat) : (term454 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1573145 : term270 = term455.
Proof. exact (@lem1573144 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1573146 : term455 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1573147 : term270 = False.
Proof. exact (TRANS (@lem1573145) (@lem1573146)). Qed.
Lemma lem1573148 (y : real) (x : real) (z : real) (h1 : term438 y x z) : False.
Proof. exact (EQ_MP (@lem1573147) (@lem1573140 y x z h1)). Qed.
Lemma lem1573149 (y : real) (x : real) (z : real) (h1 : term440 y x z) : False.
Proof. exact (or_elim (@lem1573118 y x z h1) (fun h0 : term434 x y z => @lem1573133 x y z h0) (fun h0 : term438 y x z => @lem1573148 y x z h0)). Qed.
Lemma lem1573150 (y : real) (x : real) (z : real) (h1 : term451 y x z) : False.
Proof. exact (or_elim (@lem1573102 y x z h1) (fun h0 : term449 x y z => @lem1573117 x y z h0) (fun h0 : term440 y x z => @lem1573149 y x z h0)). Qed.
Lemma lem1573151 (y : real) (x : real) (z : real) (h1 : term453 y x z) : False.
Proof. exact (or_elim (@lem1573052 y x z h1) (fun h0 : term348 y x z => @lem1573101 y x z h0) (fun h0 : term451 y x z => @lem1573150 y x z h0)). Qed.
Lemma lem1573152 (x : real) (y : real) (z : real) (h1 : term67 x y z) : term67 x y z.
Proof. exact (h1). Qed.
Lemma lem1573153 (x : real) (y : real) (z : real) (h1 : term67 x y z) : term453 y x z.
Proof. exact (EQ_MP (@lem1573051 y x z) (@lem1573152 x y z h1)). Qed.
Lemma lem1573154 (x : real) (y : real) (z : real) (h1 : term67 x y z) : (term453 y x z) = False.
Proof. exact (prop_ext (fun h2 : term453 y x z => @lem1573151 y x z h2) (fun h2 : False => @lem1573153 x y z h1)). Qed.
Lemma lem1573155 (x : real) (y : real) (z : real) (h1 : term67 x y z) : False.
Proof. exact (EQ_MP (@lem1573154 x y z h1) (@lem1573153 x y z h1)). Qed.
Lemma lem1573156 (x : real) (y : real) (h1 : term69 x y) : term69 x y.
Proof. exact (h1). Qed.
Lemma lem1573157 (x : real) (y : real) (h1 : term69 x y) : False.
Proof. exact (ex_elim (@lem1573156 x y h1) (fun z : real => fun h0 : term68 x y z => @lem1573155 x y z h0)). Qed.
Lemma lem1573158 (x : real) (h1 : term71 x) : term71 x.
Proof. exact (h1). Qed.
Lemma lem1573159 (x : real) (h1 : term71 x) : False.
Proof. exact (ex_elim (@lem1573158 x h1) (fun y : real => fun h0 : term70 x y => @lem1573157 x y h0)). Qed.
Lemma lem1573160 (h1 : term73) : term73.
Proof. exact (h1). Qed.
Lemma lem1573161 (h1 : term73) : False.
Proof. exact (ex_elim (@lem1573160 h1) (fun x : real => fun h0 : term72 x => @lem1573159 x h0)). Qed.
Lemma lem1573162 (h1 : term22) : term22.
Proof. exact (h1). Qed.
Lemma lem1573163 (h1 : term22) : term73.
Proof. exact (EQ_MP (@lem1571841) (@lem1573162 h1)). Qed.
Lemma lem1573164 (h1 : term22) : term73 = False.
Proof. exact (prop_ext (fun h2 : term73 => @lem1573161 h2) (fun h2 : False => @lem1573163 h1)). Qed.
Lemma lem1573165 (h1 : term22) : False.
Proof. exact (EQ_MP (@lem1573164 h1) (@lem1573163 h1)). Qed.
Lemma lem1573166 : term456.
Proof. exact (fun h0 : term22 => @lem1573165 h0). Qed.
Lemma lem1573167 : term457.
Proof. exact (@lem1386578 term458). Qed.
Lemma lem1573168 : term458.
Proof. exact (@lem1573167 (@lem1573166)). Qed.
