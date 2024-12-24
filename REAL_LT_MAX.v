Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_MAX_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482686_spec.
Require Import thm1483205_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483488_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19158_spec.
Require Import thm912739_spec.
Lemma lem1562437 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17160 (real_lt z x) (real_lt z y)). Qed.
Lemma lem1562443 (x : real) (z : real) (y : real) : (term2 x z y) = (term2 x z y).
Proof. exact (eq_refl (term2 x z y)). Qed.
Lemma lem1562445 (z : real) (x : real) (y : real) : (term3 z x y) = (term3 z x y).
Proof. exact (eq_refl (term3 z x y)). Qed.
Lemma lem1562446 (x : real) (z : real) (y : real) : (term4 x z y) = (term5 x z y).
Proof. exact (MK_COMB (@lem1562445 z x y) (@lem1562437 x z y)). Qed.
Lemma lem1562447 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562448 (x : real) (z : real) (y : real) : (term6 x z y) = (term7 x z y).
Proof. exact (MK_COMB (@lem1562447) (@lem1562446 x z y)). Qed.
Lemma lem1562449 (x : real) (z : real) (y : real) : (term8 x z y) = (term9 x z y).
Proof. exact (MK_COMB (@lem1562448 x z y) (@lem1562443 x z y)). Qed.
Lemma lem1562450 (x : real) (z : real) (y : real) : (term10 x z y) = (term8 x z y).
Proof. exact (@lem17646 (term11 z x y) (term12 x z y)). Qed.
Lemma lem1562451 (x : real) (z : real) (y : real) : (term10 x z y) = (term9 x z y).
Proof. exact (TRANS (@lem1562450 x z y) (@lem1562449 x z y)). Qed.
Lemma lem1562452 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1562453 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1562452 (term17 x y)). Qed.
Lemma lem1562454 (x : real) (z : real) (y : real) : (term18 x y z) = ((term11 z x y) = (term12 x z y)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1562455 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1562456 (x : real) (z : real) (y : real) : (term19 x y z) = (term10 x z y).
Proof. exact (MK_COMB (@lem1562455) (@lem1562454 x z y)). Qed.
Lemma lem1562457 (x : real) (z : real) (y : real) : (term19 x y z) = (term9 x z y).
Proof. exact (TRANS (@lem1562456 x z y) (@lem1562451 x z y)). Qed.
Lemma lem1562458 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1562457 x z y)). Qed.
Lemma lem1562459 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562460 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1562459) (@lem1562458 x y)). Qed.
Lemma lem1562461 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1562453 x y) (@lem1562460 x y)). Qed.
Lemma lem1562462 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1562463 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1562462 (term25 x)). Qed.
Lemma lem1562464 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1562465 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1562466 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1562465) (@lem1562464 x y)). Qed.
Lemma lem1562467 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1562466 x y) (@lem1562461 x y)). Qed.
Lemma lem1562468 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1562467 x y)). Qed.
Lemma lem1562469 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562470 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1562469) (@lem1562468 x)). Qed.
Lemma lem1562471 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1562463 x) (@lem1562470 x)). Qed.
Lemma lem1562472 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1562473 : term32 = term33.
Proof. exact (@lem1562472 term34). Qed.
Lemma lem1562474 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1562475 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1562476 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1562475) (@lem1562474 x)). Qed.
Lemma lem1562477 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1562476 x) (@lem1562471 x)). Qed.
Lemma lem1562478 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1562477 x)). Qed.
Lemma lem1562479 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562480 : term33 = term40.
Proof. exact (MK_COMB (@lem1562479) (@lem1562478)). Qed.
Lemma lem1562482 : term32 = term40.
Proof. exact (TRANS (@lem1562473) (@lem1562480)). Qed.
Lemma lem1562509 (x : real) (z : real) (y : real) : (term9 x z y) = (term9 x z y).
Proof. exact (eq_refl (term9 x z y)). Qed.
Lemma lem1562510 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1562509 x z y)). Qed.
Lemma lem1562511 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562512 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1562511) (@lem1562510 x y)). Qed.
Lemma lem1562513 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1562512 x y)). Qed.
Lemma lem1562514 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562515 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1562514) (@lem1562513 x)). Qed.
Lemma lem1562516 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1562515 x)). Qed.
Lemma lem1562517 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562518 : term40 = term40.
Proof. exact (MK_COMB (@lem1562517) (@lem1562516)). Qed.
Lemma lem1562519 : term32 = term40.
Proof. exact (TRANS (@lem1562482) (@lem1562518)). Qed.
Lemma lem1562520 (x : real) (y : real) (z : real) : (term11 z x y) = (term41 x y z).
Proof. exact (@lem1483521 (real_max x y) z). Qed.
Lemma lem1562526 (x : real) (y : real) (z : real) : (term42 x y z) = (term43 x y z).
Proof. exact (@lem1483519 (real_max x y) z). Qed.
Lemma lem1562531 (z : real) (x : real) (y : real) : (term43 x y z) = (term44 z x y).
Proof. exact (@lem1483488 (term45 z) (real_max x y)). Qed.
Lemma lem1562533 (z : real) (x : real) (y : real) : (term42 x y z) = (term44 z x y).
Proof. exact (TRANS (@lem1562526 x y z) (@lem1562531 z x y)). Qed.
Lemma lem1562534 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562535 (z : real) (x : real) (y : real) : (term46 x y z) = (term47 z x y).
Proof. exact (MK_COMB (@lem1562534) (@lem1562533 z x y)). Qed.
Lemma lem1562536 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562537 (z : real) (x : real) (y : real) : (term41 x y z) = (term49 z x y).
Proof. exact (MK_COMB (@lem1562535 z x y) (@lem1562536)). Qed.
Lemma lem1562538 (z : real) (x : real) (y : real) : (term11 z x y) = (term49 z x y).
Proof. exact (TRANS (@lem1562520 x y z) (@lem1562537 z x y)). Qed.
Lemma lem1562539 (z : real) (x : real) : (term50 z x) = (term51 z x).
Proof. exact (@lem1483531 z x). Qed.
Lemma lem1562545 (z : real) (x : real) : (real_sub z x) = (term52 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1562550 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1562552 (x : real) (z : real) : (real_sub z x) = (term53 x z).
Proof. exact (TRANS (@lem1562545 z x) (@lem1562550 x z)). Qed.
Lemma lem1562553 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1562554 (x : real) (z : real) : (term54 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1562553) (@lem1562552 x z)). Qed.
Lemma lem1562555 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562556 (x : real) (z : real) : (term51 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1562554 x z) (@lem1562555)). Qed.
Lemma lem1562557 (x : real) (z : real) : (term50 z x) = (term56 x z).
Proof. exact (TRANS (@lem1562539 z x) (@lem1562556 x z)). Qed.
Lemma lem1562558 (z : real) (y : real) : (term50 z y) = (term51 z y).
Proof. exact (@lem1483531 z y). Qed.
Lemma lem1562564 (z : real) (y : real) : (real_sub z y) = (term52 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1562569 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1562571 (y : real) (z : real) : (real_sub z y) = (term53 y z).
Proof. exact (TRANS (@lem1562564 z y) (@lem1562569 y z)). Qed.
Lemma lem1562572 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1562573 (y : real) (z : real) : (term54 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1562572) (@lem1562571 y z)). Qed.
Lemma lem1562574 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562575 (y : real) (z : real) : (term51 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1562573 y z) (@lem1562574)). Qed.
Lemma lem1562576 (y : real) (z : real) : (term50 z y) = (term56 y z).
Proof. exact (TRANS (@lem1562558 z y) (@lem1562575 y z)). Qed.
Lemma lem1562577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1562578 (x : real) (z : real) : (term57 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1562577) (@lem1562557 x z)). Qed.
Lemma lem1562579 (x : real) (y : real) (z : real) : (term1 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1562578 x z) (@lem1562576 y z)). Qed.
Lemma lem1562580 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1562581 (z : real) (x : real) (y : real) : (term3 z x y) = (term60 z x y).
Proof. exact (MK_COMB (@lem1562580) (@lem1562538 z x y)). Qed.
Lemma lem1562582 (x : real) (y : real) (z : real) : (term5 x z y) = (term61 x y z).
Proof. exact (MK_COMB (@lem1562581 z x y) (@lem1562579 x y z)). Qed.
Lemma lem1562583 (z : real) (x : real) (y : real) : (term62 z x y) = (term63 z x y).
Proof. exact (@lem1483531 z (real_max x y)). Qed.
Lemma lem1562596 (z : real) (x : real) (y : real) : (term64 z x y) = (term65 z x y).
Proof. exact (@lem1483519 z (real_max x y)). Qed.
Lemma lem1562597 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1562598 (z : real) (x : real) (y : real) : (term66 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1562597) (@lem1562596 z x y)). Qed.
Lemma lem1562599 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562600 (z : real) (x : real) (y : real) : (term63 z x y) = (term68 z x y).
Proof. exact (MK_COMB (@lem1562598 z x y) (@lem1562599)). Qed.
Lemma lem1562601 (z : real) (x : real) (y : real) : (term62 z x y) = (term68 z x y).
Proof. exact (TRANS (@lem1562583 z x y) (@lem1562600 z x y)). Qed.
Lemma lem1562602 (x : real) (z : real) : (real_lt z x) = (term69 x z).
Proof. exact (@lem1483521 x z). Qed.
Lemma lem1562615 (x : real) (z : real) : (real_sub x z) = (term52 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1562616 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562617 (x : real) (z : real) : (term70 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1562616) (@lem1562615 x z)). Qed.
Lemma lem1562618 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562619 (x : real) (z : real) : (term69 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1562617 x z) (@lem1562618)). Qed.
Lemma lem1562620 (x : real) (z : real) : (real_lt z x) = (term72 x z).
Proof. exact (TRANS (@lem1562602 x z) (@lem1562619 x z)). Qed.
Lemma lem1562621 (y : real) (z : real) : (real_lt z y) = (term69 y z).
Proof. exact (@lem1483521 y z). Qed.
Lemma lem1562634 (y : real) (z : real) : (real_sub y z) = (term52 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1562635 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1562636 (y : real) (z : real) : (term70 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1562635) (@lem1562634 y z)). Qed.
Lemma lem1562637 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1562638 (y : real) (z : real) : (term69 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1562636 y z) (@lem1562637)). Qed.
Lemma lem1562639 (y : real) (z : real) : (real_lt z y) = (term72 y z).
Proof. exact (TRANS (@lem1562621 y z) (@lem1562638 y z)). Qed.
Lemma lem1562640 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562641 (x : real) (z : real) : (term73 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1562640) (@lem1562620 x z)). Qed.
Lemma lem1562642 (x : real) (y : real) (z : real) : (term12 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1562641 x z) (@lem1562639 y z)). Qed.
Lemma lem1562643 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1562644 (z : real) (x : real) (y : real) : (term76 z x y) = (term77 z x y).
Proof. exact (MK_COMB (@lem1562643) (@lem1562601 z x y)). Qed.
Lemma lem1562645 (x : real) (y : real) (z : real) : (term2 x z y) = (term78 x y z).
Proof. exact (MK_COMB (@lem1562644 z x y) (@lem1562642 x y z)). Qed.
Lemma lem1562646 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562647 (x : real) (y : real) (z : real) : (term7 x z y) = (term79 x y z).
Proof. exact (MK_COMB (@lem1562646) (@lem1562582 x y z)). Qed.
Lemma lem1562648 (x : real) (y : real) (z : real) : (term9 x z y) = (term80 x y z).
Proof. exact (MK_COMB (@lem1562647 x y z) (@lem1562645 x y z)). Qed.
Lemma lem1562649 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1562648 x y z)). Qed.
Lemma lem1562650 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562651 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1562650) (@lem1562649 x y)). Qed.
Lemma lem1562652 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1562651 x y)). Qed.
Lemma lem1562653 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562654 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1562653) (@lem1562652 x)). Qed.
Lemma lem1562655 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1562654 x)). Qed.
Lemma lem1562656 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562657 : term40 = term86.
Proof. exact (MK_COMB (@lem1562656) (@lem1562655)). Qed.
Lemma lem1562658 : term32 = term86.
Proof. exact (TRANS (@lem1562519) (@lem1562657)). Qed.
Lemma lem1562668 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1562669 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1562668 real P Q). Qed.
Lemma lem1562670 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1562669 (term93 x y) (term94 x y)). Qed.
Lemma lem1562671 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1562672 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562673 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1562672) (@lem1562671 x y z)). Qed.
Lemma lem1562674 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1562675 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1562673 x y z) (@lem1562674 x y z)). Qed.
Lemma lem1562676 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1562675 x y z)). Qed.
Lemma lem1562677 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562678 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1562677) (@lem1562676 x y)). Qed.
Lemma lem1562679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1562680 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1562679) (@lem1562678 x y)). Qed.
Lemma lem1562681 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1562682 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1562681 x y z)). Qed.
Lemma lem1562683 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562684 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1562683) (@lem1562682 x y)). Qed.
Lemma lem1562685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562686 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1562685) (@lem1562684 x y)). Qed.
Lemma lem1562687 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1562688 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1562687 x y z)). Qed.
Lemma lem1562689 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562690 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1562689) (@lem1562688 x y)). Qed.
Lemma lem1562691 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1562686 x y) (@lem1562690 x y)). Qed.
Lemma lem1562692 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1562680 x y) (@lem1562691 x y)). Qed.
Lemma lem1562693 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1562692 x y) (@lem1562670 x y)). Qed.
Lemma lem1562790 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1562693 x y)). Qed.
Lemma lem1562791 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562792 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1562791) (@lem1562790 x)). Qed.
Lemma lem1562794 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1562795 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1562794 real P Q). Qed.
Lemma lem1562796 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1562795 (term115 x) (term116 x)). Qed.
Lemma lem1562797 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1562798 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562799 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1562798) (@lem1562797 x y)). Qed.
Lemma lem1562800 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1562801 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1562799 x y) (@lem1562800 x y)). Qed.
Lemma lem1562802 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1562801 x y)). Qed.
Lemma lem1562803 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562804 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1562803) (@lem1562802 x)). Qed.
Lemma lem1562805 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1562806 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1562805) (@lem1562804 x)). Qed.
Lemma lem1562807 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1562808 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1562807 x y)). Qed.
Lemma lem1562809 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562810 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1562809) (@lem1562808 x)). Qed.
Lemma lem1562811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562812 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1562811) (@lem1562810 x)). Qed.
Lemma lem1562813 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1562814 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1562813 x y)). Qed.
Lemma lem1562815 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562816 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1562815) (@lem1562814 x)). Qed.
Lemma lem1562817 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1562812 x) (@lem1562816 x)). Qed.
Lemma lem1562818 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1562806 x) (@lem1562817 x)). Qed.
Lemma lem1562819 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1562818 x) (@lem1562796 x)). Qed.
Lemma lem1562924 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1562792 x) (@lem1562819 x)). Qed.
Lemma lem1562925 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1562924 x)). Qed.
Lemma lem1562926 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562927 : term86 = term134.
Proof. exact (MK_COMB (@lem1562926) (@lem1562925)). Qed.
Lemma lem1562929 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1562930 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1562929 real P Q). Qed.
Lemma lem1562931 : term135 = term136.
Proof. exact (@lem1562930 term137 term138). Qed.
Lemma lem1562932 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1562933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562934 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1562933) (@lem1562932 x)). Qed.
Lemma lem1562935 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1562936 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1562934 x) (@lem1562935 x)). Qed.
Lemma lem1562937 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1562936 x)). Qed.
Lemma lem1562938 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562939 : term135 = term134.
Proof. exact (MK_COMB (@lem1562938) (@lem1562937)). Qed.
Lemma lem1562940 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1562941 : term144 = term145.
Proof. exact (MK_COMB (@lem1562940) (@lem1562939)). Qed.
Lemma lem1562942 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1562943 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1562942 x)). Qed.
Lemma lem1562944 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562945 : term147 = term148.
Proof. exact (MK_COMB (@lem1562944) (@lem1562943)). Qed.
Lemma lem1562946 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1562947 : term149 = term150.
Proof. exact (MK_COMB (@lem1562946) (@lem1562945)). Qed.
Lemma lem1562948 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1562949 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1562948 x)). Qed.
Lemma lem1562950 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1562951 : term152 = term153.
Proof. exact (MK_COMB (@lem1562950) (@lem1562949)). Qed.
Lemma lem1562952 : term136 = term154.
Proof. exact (MK_COMB (@lem1562947) (@lem1562951)). Qed.
Lemma lem1562953 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1562941) (@lem1562952)). Qed.
Lemma lem1562954 : term134 = term154.
Proof. exact (EQ_MP (@lem1562953) (@lem1562931)). Qed.
Lemma lem1563067 : term86 = term154.
Proof. exact (TRANS (@lem1562927) (@lem1562954)). Qed.
Lemma lem1563069 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1563070 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1563069 real P Q). Qed.
Lemma lem1563071 : term136 = term135.
Proof. exact (@lem1563070 term137 term138). Qed.
Lemma lem1563072 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1563073 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1563072 x)). Qed.
Lemma lem1563074 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563075 : term147 = term148.
Proof. exact (MK_COMB (@lem1563074) (@lem1563073)). Qed.
Lemma lem1563076 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563077 : term149 = term150.
Proof. exact (MK_COMB (@lem1563076) (@lem1563075)). Qed.
Lemma lem1563078 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1563079 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1563078 x)). Qed.
Lemma lem1563080 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563081 : term152 = term153.
Proof. exact (MK_COMB (@lem1563080) (@lem1563079)). Qed.
Lemma lem1563082 : term136 = term154.
Proof. exact (MK_COMB (@lem1563077) (@lem1563081)). Qed.
Lemma lem1563083 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1563084 : term155 = term156.
Proof. exact (MK_COMB (@lem1563083) (@lem1563082)). Qed.
Lemma lem1563085 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1563086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563087 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1563086) (@lem1563085 x)). Qed.
Lemma lem1563088 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1563089 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1563087 x) (@lem1563088 x)). Qed.
Lemma lem1563090 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1563089 x)). Qed.
Lemma lem1563091 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563092 : term135 = term134.
Proof. exact (MK_COMB (@lem1563091) (@lem1563090)). Qed.
Lemma lem1563093 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1563084) (@lem1563092)). Qed.
Lemma lem1563094 : term154 = term134.
Proof. exact (EQ_MP (@lem1563093) (@lem1563071)). Qed.
Lemma lem1563096 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1563097 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1563096 real P Q). Qed.
Lemma lem1563098 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1563097 (term115 x) (term116 x)). Qed.
Lemma lem1563099 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1563100 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1563099 x y)). Qed.
Lemma lem1563101 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563102 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1563101) (@lem1563100 x)). Qed.
Lemma lem1563103 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563104 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1563103) (@lem1563102 x)). Qed.
Lemma lem1563105 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1563106 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1563105 x y)). Qed.
Lemma lem1563107 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563108 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1563107) (@lem1563106 x)). Qed.
Lemma lem1563109 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1563104 x) (@lem1563108 x)). Qed.
Lemma lem1563110 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1563111 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1563110) (@lem1563109 x)). Qed.
Lemma lem1563112 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1563113 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563114 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1563113) (@lem1563112 x y)). Qed.
Lemma lem1563115 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1563116 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1563114 x y) (@lem1563115 x y)). Qed.
Lemma lem1563117 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1563116 x y)). Qed.
Lemma lem1563118 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563119 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1563118) (@lem1563117 x)). Qed.
Lemma lem1563120 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1563111 x) (@lem1563119 x)). Qed.
Lemma lem1563121 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1563120 x) (@lem1563098 x)). Qed.
Lemma lem1563123 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1563124 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1563123 real P Q). Qed.
Lemma lem1563125 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1563124 (term93 x y) (term94 x y)). Qed.
Lemma lem1563126 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1563127 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1563126 x y z)). Qed.
Lemma lem1563128 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563129 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1563128) (@lem1563127 x y)). Qed.
Lemma lem1563130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563131 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1563130) (@lem1563129 x y)). Qed.
Lemma lem1563132 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1563133 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1563132 x y z)). Qed.
Lemma lem1563134 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563135 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1563134) (@lem1563133 x y)). Qed.
Lemma lem1563136 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1563131 x y) (@lem1563135 x y)). Qed.
Lemma lem1563137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1563138 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1563137) (@lem1563136 x y)). Qed.
Lemma lem1563139 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1563140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563141 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1563140) (@lem1563139 x y z)). Qed.
Lemma lem1563142 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1563143 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1563141 x y z) (@lem1563142 x y z)). Qed.
Lemma lem1563144 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1563143 x y z)). Qed.
Lemma lem1563145 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563146 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1563145) (@lem1563144 x y)). Qed.
Lemma lem1563147 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1563138 x y) (@lem1563146 x y)). Qed.
Lemma lem1563148 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1563147 x y) (@lem1563125 x y)). Qed.
Lemma lem1563149 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1563148 x y)). Qed.
Lemma lem1563150 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563151 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1563150) (@lem1563149 x)). Qed.
Lemma lem1563152 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1563121 x) (@lem1563151 x)). Qed.
Lemma lem1563153 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1563152 x)). Qed.
Lemma lem1563154 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563155 : term134 = term86.
Proof. exact (MK_COMB (@lem1563154) (@lem1563153)). Qed.
Lemma lem1563156 : term154 = term86.
Proof. exact (TRANS (@lem1563094) (@lem1563155)). Qed.
Lemma lem1563157 : term86 = term86.
Proof. exact (TRANS (@lem1563067) (@lem1563156)). Qed.
Lemma lem1563160 : term32 = term86.
Proof. exact (TRANS (@lem1562658) (@lem1563157)). Qed.
Lemma lem1563177 (x : real) (y : real) (z : real) : (term78 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term72 x z) (term68 z x y) (term72 y z)). Qed.
Lemma lem1563192 (x : real) (y : real) (z : real) : (term79 x y z) = (term79 x y z).
Proof. exact (eq_refl (term79 x y z)). Qed.
Lemma lem1563193 (x : real) (y : real) (z : real) : (term80 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1563192 x y z) (@lem1563177 x y z)). Qed.
Lemma lem1563194 (x : real) (y : real) : (term81 x y) = (term163 x y).
Proof. exact (fun_ext (fun z : real => @lem1563193 x y z)). Qed.
Lemma lem1563195 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563196 (x : real) (y : real) : (term82 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1563195) (@lem1563194 x y)). Qed.
Lemma lem1563197 (x : real) : (term83 x) = (term165 x).
Proof. exact (fun_ext (fun y : real => @lem1563196 x y)). Qed.
Lemma lem1563198 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563199 (x : real) : (term84 x) = (term166 x).
Proof. exact (MK_COMB (@lem1563198) (@lem1563197 x)). Qed.
Lemma lem1563200 : term85 = term167.
Proof. exact (fun_ext (fun x : real => @lem1563199 x)). Qed.
Lemma lem1563201 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1563202 : term86 = term168.
Proof. exact (MK_COMB (@lem1563201) (@lem1563200)). Qed.
Lemma lem1563203 : term32 = term168.
Proof. exact (TRANS (@lem1563160) (@lem1563202)). Qed.
Lemma lem1563205 (x : real) (y : real) (z : real) : (term169 z x y) = (term61 x y z).
Proof. exact (eq_refl (term169 z x y)). Qed.
Lemma lem1563206 (z : real) (x : real) (y : real) : (term61 x y z) = (term169 z x y).
Proof. exact (SYM (@lem1563205 x y z)). Qed.
Lemma lem1563207 (y : real) (z : real) (x : real) : (term169 z x y) = (term170 y z x).
Proof. exact (@lem1483205 y (term171 x y z) x). Qed.
Lemma lem1563208 (y : real) (z : real) (x : real) : (term61 x y z) = (term170 y z x).
Proof. exact (TRANS (@lem1563206 z x y) (@lem1563207 y z x)). Qed.
Lemma lem1563209 (x : real) (y : real) (z : real) : (term172 y z x) = (term173 x y z).
Proof. exact (eq_refl (term172 y z x)). Qed.
Lemma lem1563210 (x : real) (y : real) : (term174 x y) = (term174 x y).
Proof. exact (eq_refl (term174 x y)). Qed.
Lemma lem1563211 (x : real) (y : real) (z : real) : (term175 y z x) = (term176 x y z).
Proof. exact (MK_COMB (@lem1563210 x y) (@lem1563209 x y z)). Qed.
Lemma lem1563212 (x : real) (y : real) (z : real) : (term177 x z y) = (term178 x y z).
Proof. exact (eq_refl (term177 x z y)). Qed.
Lemma lem1563213 (y : real) (x : real) : (term179 y x) = (term179 y x).
Proof. exact (eq_refl (term179 y x)). Qed.
Lemma lem1563214 (x : real) (y : real) (z : real) : (term180 x z y) = (term181 x y z).
Proof. exact (MK_COMB (@lem1563213 y x) (@lem1563212 x y z)). Qed.
Lemma lem1563215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563216 (x : real) (y : real) (z : real) : (term182 x z y) = (term183 x y z).
Proof. exact (MK_COMB (@lem1563215) (@lem1563214 x y z)). Qed.
Lemma lem1563217 (x : real) (y : real) (z : real) : (term170 y z x) = (term184 x y z).
Proof. exact (MK_COMB (@lem1563216 x y z) (@lem1563211 x y z)). Qed.
Lemma lem1563218 (x : real) (y : real) (z : real) : (term185 x y z) = (term185 x y z).
Proof. exact (eq_refl (term185 x y z)). Qed.
Lemma lem1563219 (x : real) (y : real) (z : real) : ((term61 x y z) = (term170 y z x)) = ((term61 x y z) = (term184 x y z)).
Proof. exact (MK_COMB (@lem1563218 x y z) (@lem1563217 x y z)). Qed.
Lemma lem1563220 (x : real) (y : real) (z : real) : (term61 x y z) = (term184 x y z).
Proof. exact (EQ_MP (@lem1563219 x y z) (@lem1563208 y z x)). Qed.
Lemma lem1563221 (y : real) (x : real) : (real_ge y x) = (term51 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1563227 (y : real) (x : real) : (real_sub y x) = (term52 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1563232 (x : real) (y : real) : (term52 y x) = (term53 x y).
Proof. exact (@lem1483488 (term45 x) y). Qed.
Lemma lem1563234 (x : real) (y : real) : (real_sub y x) = (term53 x y).
Proof. exact (TRANS (@lem1563227 y x) (@lem1563232 x y)). Qed.
Lemma lem1563235 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563236 (x : real) (y : real) : (term54 y x) = (term55 x y).
Proof. exact (MK_COMB (@lem1563235) (@lem1563234 x y)). Qed.
Lemma lem1563237 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563238 (x : real) (y : real) : (term51 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem1563236 x y) (@lem1563237)). Qed.
Lemma lem1563239 (x : real) (y : real) : (real_ge y x) = (term56 x y).
Proof. exact (TRANS (@lem1563221 y x) (@lem1563238 x y)). Qed.
Lemma lem1563240 (z : real) (y : real) : (term186 z y) = (term187 z y).
Proof. exact (@lem1483525 (term53 z y) term48). Qed.
Lemma lem1563241 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563254 (y : real) (z : real) : (term53 z y) = (term52 y z).
Proof. exact (@lem1483488 y (term45 z)). Qed.
Lemma lem1563255 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1563256 (y : real) (z : real) : (term188 z y) = (term189 y z).
Proof. exact (MK_COMB (@lem1563255) (@lem1563254 y z)). Qed.
Lemma lem1563257 (y : real) (z : real) : (term190 z y) = (term191 y z).
Proof. exact (MK_COMB (@lem1563256 y z) (@lem1563241)). Qed.
Lemma lem1563258 (y : real) (z : real) : (term191 y z) = (term192 y z).
Proof. exact (@lem1483519 (term52 y z) term48). Qed.
Lemma lem1563260 (x : nat) : (term193 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1563261 : term194 = term48.
Proof. exact (@lem1563260 term195). Qed.
Lemma lem1563262 (y : real) (z : real) : (term196 y z) = (term196 y z).
Proof. exact (eq_refl (term196 y z)). Qed.
Lemma lem1563263 (y : real) (z : real) : (term192 y z) = (term197 y z).
Proof. exact (MK_COMB (@lem1563262 y z) (@lem1563261)). Qed.
Lemma lem1563264 (y : real) (z : real) : (term197 y z) = (term52 y z).
Proof. exact (@lem1483450 (term52 y z)). Qed.
Lemma lem1563265 (y : real) (z : real) : (term192 y z) = (term52 y z).
Proof. exact (TRANS (@lem1563263 y z) (@lem1563264 y z)). Qed.
Lemma lem1563266 (y : real) (z : real) : (term191 y z) = (term52 y z).
Proof. exact (TRANS (@lem1563258 y z) (@lem1563265 y z)). Qed.
Lemma lem1563267 (y : real) (z : real) : (term190 z y) = (term52 y z).
Proof. exact (TRANS (@lem1563257 y z) (@lem1563266 y z)). Qed.
Lemma lem1563268 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563269 (y : real) (z : real) : (term198 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1563268) (@lem1563267 y z)). Qed.
Lemma lem1563270 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563271 (y : real) (z : real) : (term187 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1563269 y z) (@lem1563270)). Qed.
Lemma lem1563272 (y : real) (z : real) : (term186 z y) = (term72 y z).
Proof. exact (TRANS (@lem1563240 z y) (@lem1563271 y z)). Qed.
Lemma lem1563273 (x : real) (z : real) : (term56 x z) = (term199 x z).
Proof. exact (@lem1483527 (term53 x z) term48). Qed.
Lemma lem1563291 (x : real) (z : real) : (term190 x z) = (term200 x z).
Proof. exact (@lem1483519 (term53 x z) term48). Qed.
Lemma lem1563293 (x : nat) : (term193 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1563294 : term194 = term48.
Proof. exact (@lem1563293 term195). Qed.
Lemma lem1563295 (x : real) (z : real) : (term201 x z) = (term201 x z).
Proof. exact (eq_refl (term201 x z)). Qed.
Lemma lem1563296 (x : real) (z : real) : (term200 x z) = (term202 x z).
Proof. exact (MK_COMB (@lem1563295 x z) (@lem1563294)). Qed.
Lemma lem1563297 (x : real) (z : real) : (term202 x z) = (term53 x z).
Proof. exact (@lem1483450 (term53 x z)). Qed.
Lemma lem1563298 (x : real) (z : real) : (term200 x z) = (term53 x z).
Proof. exact (TRANS (@lem1563296 x z) (@lem1563297 x z)). Qed.
Lemma lem1563300 (x : real) (z : real) : (term190 x z) = (term53 x z).
Proof. exact (TRANS (@lem1563291 x z) (@lem1563298 x z)). Qed.
Lemma lem1563301 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563302 (x : real) (z : real) : (term203 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1563301) (@lem1563300 x z)). Qed.
Lemma lem1563303 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563304 (x : real) (z : real) : (term199 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1563302 x z) (@lem1563303)). Qed.
Lemma lem1563305 (x : real) (z : real) : (term56 x z) = (term56 x z).
Proof. exact (TRANS (@lem1563273 x z) (@lem1563304 x z)). Qed.
Lemma lem1563306 (y : real) (z : real) : (term56 y z) = (term199 y z).
Proof. exact (@lem1483527 (term53 y z) term48). Qed.
Lemma lem1563324 (y : real) (z : real) : (term190 y z) = (term200 y z).
Proof. exact (@lem1483519 (term53 y z) term48). Qed.
Lemma lem1563326 (x : nat) : (term193 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1563327 : term194 = term48.
Proof. exact (@lem1563326 term195). Qed.
Lemma lem1563328 (y : real) (z : real) : (term201 y z) = (term201 y z).
Proof. exact (eq_refl (term201 y z)). Qed.
Lemma lem1563329 (y : real) (z : real) : (term200 y z) = (term202 y z).
Proof. exact (MK_COMB (@lem1563328 y z) (@lem1563327)). Qed.
Lemma lem1563330 (y : real) (z : real) : (term202 y z) = (term53 y z).
Proof. exact (@lem1483450 (term53 y z)). Qed.
Lemma lem1563331 (y : real) (z : real) : (term200 y z) = (term53 y z).
Proof. exact (TRANS (@lem1563329 y z) (@lem1563330 y z)). Qed.
Lemma lem1563333 (y : real) (z : real) : (term190 y z) = (term53 y z).
Proof. exact (TRANS (@lem1563324 y z) (@lem1563331 y z)). Qed.
Lemma lem1563334 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563335 (y : real) (z : real) : (term203 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1563334) (@lem1563333 y z)). Qed.
Lemma lem1563336 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563337 (y : real) (z : real) : (term199 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1563335 y z) (@lem1563336)). Qed.
Lemma lem1563338 (y : real) (z : real) : (term56 y z) = (term56 y z).
Proof. exact (TRANS (@lem1563306 y z) (@lem1563337 y z)). Qed.
Lemma lem1563339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563340 (x : real) (z : real) : (term58 x z) = (term58 x z).
Proof. exact (MK_COMB (@lem1563339) (@lem1563305 x z)). Qed.
Lemma lem1563341 (x : real) (y : real) (z : real) : (term59 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1563340 x z) (@lem1563338 y z)). Qed.
Lemma lem1563342 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563343 (y : real) (z : real) : (term204 z y) = (term205 y z).
Proof. exact (MK_COMB (@lem1563342) (@lem1563272 y z)). Qed.
Lemma lem1563344 (x : real) (y : real) (z : real) : (term178 x y z) = (term206 x y z).
Proof. exact (MK_COMB (@lem1563343 y z) (@lem1563341 x y z)). Qed.
Lemma lem1563345 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563346 (x : real) (y : real) : (term179 y x) = (term58 x y).
Proof. exact (MK_COMB (@lem1563345) (@lem1563239 x y)). Qed.
Lemma lem1563347 (x : real) (y : real) (z : real) : (term181 x y z) = (term207 x y z).
Proof. exact (MK_COMB (@lem1563346 x y) (@lem1563344 x y z)). Qed.
Lemma lem1563348 (x : real) (y : real) : (real_gt x y) = (term69 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1563361 (x : real) (y : real) : (real_sub x y) = (term52 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1563362 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563363 (x : real) (y : real) : (term70 x y) = (term71 x y).
Proof. exact (MK_COMB (@lem1563362) (@lem1563361 x y)). Qed.
Lemma lem1563364 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563365 (x : real) (y : real) : (term69 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1563363 x y) (@lem1563364)). Qed.
Lemma lem1563366 (x : real) (y : real) : (real_gt x y) = (term72 x y).
Proof. exact (TRANS (@lem1563348 x y) (@lem1563365 x y)). Qed.
Lemma lem1563367 (z : real) (x : real) : (term186 z x) = (term187 z x).
Proof. exact (@lem1483525 (term53 z x) term48). Qed.
Lemma lem1563368 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563381 (x : real) (z : real) : (term53 z x) = (term52 x z).
Proof. exact (@lem1483488 x (term45 z)). Qed.
Lemma lem1563382 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1563383 (x : real) (z : real) : (term188 z x) = (term189 x z).
Proof. exact (MK_COMB (@lem1563382) (@lem1563381 x z)). Qed.
Lemma lem1563384 (x : real) (z : real) : (term190 z x) = (term191 x z).
Proof. exact (MK_COMB (@lem1563383 x z) (@lem1563368)). Qed.
Lemma lem1563385 (x : real) (z : real) : (term191 x z) = (term192 x z).
Proof. exact (@lem1483519 (term52 x z) term48). Qed.
Lemma lem1563387 (x : nat) : (term193 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1563388 : term194 = term48.
Proof. exact (@lem1563387 term195). Qed.
Lemma lem1563389 (x : real) (z : real) : (term196 x z) = (term196 x z).
Proof. exact (eq_refl (term196 x z)). Qed.
Lemma lem1563390 (x : real) (z : real) : (term192 x z) = (term197 x z).
Proof. exact (MK_COMB (@lem1563389 x z) (@lem1563388)). Qed.
Lemma lem1563391 (x : real) (z : real) : (term197 x z) = (term52 x z).
Proof. exact (@lem1483450 (term52 x z)). Qed.
Lemma lem1563392 (x : real) (z : real) : (term192 x z) = (term52 x z).
Proof. exact (TRANS (@lem1563390 x z) (@lem1563391 x z)). Qed.
Lemma lem1563393 (x : real) (z : real) : (term191 x z) = (term52 x z).
Proof. exact (TRANS (@lem1563385 x z) (@lem1563392 x z)). Qed.
Lemma lem1563394 (x : real) (z : real) : (term190 z x) = (term52 x z).
Proof. exact (TRANS (@lem1563384 x z) (@lem1563393 x z)). Qed.
Lemma lem1563395 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563396 (x : real) (z : real) : (term198 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1563395) (@lem1563394 x z)). Qed.
Lemma lem1563397 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563398 (x : real) (z : real) : (term187 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1563396 x z) (@lem1563397)). Qed.
Lemma lem1563399 (x : real) (z : real) : (term186 z x) = (term72 x z).
Proof. exact (TRANS (@lem1563367 z x) (@lem1563398 x z)). Qed.
Lemma lem1563400 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563401 (x : real) (z : real) : (term58 x z) = (term58 x z).
Proof. exact (MK_COMB (@lem1563400) (@lem1563305 x z)). Qed.
Lemma lem1563402 (x : real) (y : real) (z : real) : (term59 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1563401 x z) (@lem1563338 y z)). Qed.
Lemma lem1563403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563404 (x : real) (z : real) : (term204 z x) = (term205 x z).
Proof. exact (MK_COMB (@lem1563403) (@lem1563399 x z)). Qed.
Lemma lem1563405 (x : real) (y : real) (z : real) : (term173 x y z) = (term208 x y z).
Proof. exact (MK_COMB (@lem1563404 x z) (@lem1563402 x y z)). Qed.
Lemma lem1563406 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563407 (x : real) (y : real) : (term174 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1563406) (@lem1563366 x y)). Qed.
Lemma lem1563408 (x : real) (y : real) (z : real) : (term176 x y z) = (term209 x y z).
Proof. exact (MK_COMB (@lem1563407 x y) (@lem1563405 x y z)). Qed.
Lemma lem1563409 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563410 (x : real) (y : real) (z : real) : (term183 x y z) = (term210 x y z).
Proof. exact (MK_COMB (@lem1563409) (@lem1563347 x y z)). Qed.
Lemma lem1563411 (x : real) (y : real) (z : real) : (term184 x y z) = (term211 x y z).
Proof. exact (MK_COMB (@lem1563410 x y z) (@lem1563408 x y z)). Qed.
Lemma lem1563423 (x : real) (y : real) (z : real) : (term61 x y z) = (term211 x y z).
Proof. exact (TRANS (@lem1563220 x y z) (@lem1563411 x y z)). Qed.
Lemma lem1563425 (x : real) (a : real) (y : real) (r : real) : (term212 a x y r) = (term213 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem1563426 (x : real) (z : real) (y : real) : (term68 z x y) = (term214 x z y).
Proof. exact (@lem1563425 x z y term48). Qed.
Lemma lem1563439 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1563440 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563441 (y : real) (z : real) : (term215 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1563440) (@lem1563439 y z)). Qed.
Lemma lem1563442 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563443 (y : real) (z : real) : (term216 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1563441 y z) (@lem1563442)). Qed.
Lemma lem1563456 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1563457 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563458 (x : real) (z : real) : (term215 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1563457) (@lem1563456 x z)). Qed.
Lemma lem1563459 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563460 (x : real) (z : real) : (term216 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1563458 x z) (@lem1563459)). Qed.
Lemma lem1563461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563462 (x : real) (z : real) : (term217 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1563461) (@lem1563460 x z)). Qed.
Lemma lem1563463 (x : real) (y : real) (z : real) : (term214 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1563462 x z) (@lem1563443 y z)). Qed.
Lemma lem1563464 (x : real) (y : real) (z : real) : (term68 z x y) = (term59 x y z).
Proof. exact (TRANS (@lem1563426 x z y) (@lem1563463 x y z)). Qed.
Lemma lem1563465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563466 (x : real) (y : real) (z : real) : (term77 z x y) = (term218 x y z).
Proof. exact (MK_COMB (@lem1563465) (@lem1563464 x y z)). Qed.
Lemma lem1563467 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (eq_refl (term72 x z)). Qed.
Lemma lem1563470 (y : real) (x : real) (z : real) : (term219 y x z) = (term220 y x z).
Proof. exact (MK_COMB (@lem1563466 x y z) (@lem1563467 x z)). Qed.
Lemma lem1563472 (x : real) (a : real) (y : real) (r : real) : (term212 a x y r) = (term213 x a y r).
Proof. exact (proj1 (@lem1482686 x a (@el real) y (@el real) r)). Qed.
Lemma lem1563473 (x : real) (z : real) (y : real) : (term68 z x y) = (term214 x z y).
Proof. exact (@lem1563472 x z y term48). Qed.
Lemma lem1563486 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1563487 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563488 (y : real) (z : real) : (term215 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1563487) (@lem1563486 y z)). Qed.
Lemma lem1563489 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563490 (y : real) (z : real) : (term216 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1563488 y z) (@lem1563489)). Qed.
Lemma lem1563503 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1563504 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563505 (x : real) (z : real) : (term215 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1563504) (@lem1563503 x z)). Qed.
Lemma lem1563506 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563507 (x : real) (z : real) : (term216 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1563505 x z) (@lem1563506)). Qed.
Lemma lem1563508 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563509 (x : real) (z : real) : (term217 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1563508) (@lem1563507 x z)). Qed.
Lemma lem1563510 (x : real) (y : real) (z : real) : (term214 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1563509 x z) (@lem1563490 y z)). Qed.
Lemma lem1563511 (x : real) (y : real) (z : real) : (term68 z x y) = (term59 x y z).
Proof. exact (TRANS (@lem1563473 x z y) (@lem1563510 x y z)). Qed.
Lemma lem1563512 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1563513 (x : real) (y : real) (z : real) : (term77 z x y) = (term218 x y z).
Proof. exact (MK_COMB (@lem1563512) (@lem1563511 x y z)). Qed.
Lemma lem1563514 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (eq_refl (term72 y z)). Qed.
Lemma lem1563517 (x : real) (y : real) (z : real) : (term221 x y z) = (term222 x y z).
Proof. exact (MK_COMB (@lem1563513 x y z) (@lem1563514 y z)). Qed.
Lemma lem1563518 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563519 (y : real) (x : real) (z : real) : (term223 y x z) = (term224 y x z).
Proof. exact (MK_COMB (@lem1563518) (@lem1563470 y x z)). Qed.
Lemma lem1563520 (x : real) (y : real) (z : real) : (term161 x y z) = (term225 x y z).
Proof. exact (MK_COMB (@lem1563519 y x z) (@lem1563517 x y z)). Qed.
Lemma lem1563521 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1563522 (x : real) (y : real) (z : real) : (term79 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1563521) (@lem1563423 x y z)). Qed.
Lemma lem1563523 (x : real) (y : real) (z : real) : (term162 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1563522 x y z) (@lem1563520 x y z)). Qed.
Lemma lem1563524 (x : real) (y : real) (z : real) (h1 : term227 x y z) : term227 x y z.
Proof. exact (h1). Qed.
Lemma lem1563525 (x : real) (y : real) (z : real) (h1 : term211 x y z) : term211 x y z.
Proof. exact (h1). Qed.
Lemma lem1563526 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term207 x y z.
Proof. exact (h1). Qed.
Lemma lem1563527 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term206 x y z.
Proof. exact (proj2 (@lem1563526 x y z h1)). Qed.
Lemma lem1563529 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term59 x y z.
Proof. exact (proj2 (@lem1563527 x y z h1)). Qed.
Lemma lem1563530 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term72 y z.
Proof. exact (proj1 (@lem1563527 x y z h1)). Qed.
Lemma lem1563531 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term56 y z.
Proof. exact (proj2 (@lem1563529 x y z h1)). Qed.
Lemma lem1563534 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563535 : term229 = term230.
Proof. exact (@lem1563534 (NUMERAL 0) term195). Qed.
Lemma lem1563536 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563537 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563538 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563537 h1) (fun h1 : term230 = True => @lem1563536)). Qed.
Lemma lem1563539 : term230 = True.
Proof. exact (EQ_MP (@lem1563538) (@lem1563536)). Qed.
Lemma lem1563540 : term229 = True.
Proof. exact (TRANS (@lem1563535) (@lem1563539)). Qed.
Lemma lem1563541 : True = term229.
Proof. exact (SYM (@lem1563540)). Qed.
Lemma lem1563542 : term229.
Proof. exact (EQ_MP (@lem1563541) (@lem0)). Qed.
Lemma lem1563543 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term232 y z.
Proof. exact (conj (@lem1563542) (@lem1563531 x y z h1)). Qed.
Lemma lem1563545 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1563546 (y : real) (z : real) : term234 y z.
Proof. exact (@lem1563545 term235 (term53 y z)). Qed.
Lemma lem1563547 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term236 y z.
Proof. exact (@lem1563546 y z (@lem1563543 x y z h1)). Qed.
Lemma lem1563548 (y : real) (z : real) : (term237 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1563549 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563550 (y : real) (z : real) : (term238 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1563549) (@lem1563548 y z)). Qed.
Lemma lem1563551 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563552 (y : real) (z : real) : (term236 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1563550 y z) (@lem1563551)). Qed.
Lemma lem1563553 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1563552 y z) (@lem1563547 x y z h1)). Qed.
Lemma lem1563555 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563556 : term229 = term230.
Proof. exact (@lem1563555 (NUMERAL 0) term195). Qed.
Lemma lem1563557 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563558 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563559 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563558 h1) (fun h1 : term230 = True => @lem1563557)). Qed.
Lemma lem1563560 : term230 = True.
Proof. exact (EQ_MP (@lem1563559) (@lem1563557)). Qed.
Lemma lem1563561 : term229 = True.
Proof. exact (TRANS (@lem1563556) (@lem1563560)). Qed.
Lemma lem1563562 : True = term229.
Proof. exact (SYM (@lem1563561)). Qed.
Lemma lem1563563 : term229.
Proof. exact (EQ_MP (@lem1563562) (@lem0)). Qed.
Lemma lem1563564 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term239 y z.
Proof. exact (conj (@lem1563563) (@lem1563530 x y z h1)). Qed.
Lemma lem1563566 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1563567 (y : real) (z : real) : term241 y z.
Proof. exact (@lem1563566 term235 (term52 y z)). Qed.
Lemma lem1563568 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term242 y z.
Proof. exact (@lem1563567 y z (@lem1563564 x y z h1)). Qed.
Lemma lem1563569 (y : real) (z : real) : (term243 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1563570 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563571 (y : real) (z : real) : (term244 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1563570) (@lem1563569 y z)). Qed.
Lemma lem1563572 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563573 (y : real) (z : real) : (term242 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1563571 y z) (@lem1563572)). Qed.
Lemma lem1563574 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1563573 y z) (@lem1563568 x y z h1)). Qed.
Lemma lem1563575 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term245 y z.
Proof. exact (conj (@lem1563574 x y z h1) (@lem1563553 x y z h1)). Qed.
Lemma lem1563577 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1563578 (y : real) (z : real) : term247 y z.
Proof. exact (@lem1563577 (term52 y z) (term53 y z)). Qed.
Lemma lem1563579 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term248 y z.
Proof. exact (@lem1563578 y z (@lem1563575 x y z h1)). Qed.
Lemma lem1563580 (y : real) (z : real) : (term249 y z) = (term250 y z).
Proof. exact (@lem1483480 y (term45 y) (term45 z) z). Qed.
Lemma lem1563581 (y : real) : (term251 y) = (term252 y).
Proof. exact (@lem1483442 term253 y). Qed.
Lemma lem1563583 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563584 : term255 = term48.
Proof. exact (@lem1563583 term195). Qed.
Lemma lem1563585 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563586 : term256 = term257.
Proof. exact (MK_COMB (@lem1563585) (@lem1563584)). Qed.
Lemma lem1563587 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1563588 (y : real) : (term252 y) = (term258 y).
Proof. exact (MK_COMB (@lem1563586) (@lem1563587 y)). Qed.
Lemma lem1563589 (y : real) : (term251 y) = (term258 y).
Proof. exact (TRANS (@lem1563581 y) (@lem1563588 y)). Qed.
Lemma lem1563590 (y : real) : (term258 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1563591 (y : real) : (term251 y) = term48.
Proof. exact (TRANS (@lem1563589 y) (@lem1563590 y)). Qed.
Lemma lem1563592 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1563593 (y : real) : (term259 y) = term260.
Proof. exact (MK_COMB (@lem1563592) (@lem1563591 y)). Qed.
Lemma lem1563594 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1563596 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563597 : term255 = term48.
Proof. exact (@lem1563596 term195). Qed.
Lemma lem1563598 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563599 : term256 = term257.
Proof. exact (MK_COMB (@lem1563598) (@lem1563597)). Qed.
Lemma lem1563600 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1563601 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1563599) (@lem1563600 z)). Qed.
Lemma lem1563602 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1563594 z) (@lem1563601 z)). Qed.
Lemma lem1563603 (z : real) : (term258 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1563604 (z : real) : (term261 z) = term48.
Proof. exact (TRANS (@lem1563602 z) (@lem1563603 z)). Qed.
Lemma lem1563605 (y : real) (z : real) : (term250 y z) = term262.
Proof. exact (MK_COMB (@lem1563593 y) (@lem1563604 z)). Qed.
Lemma lem1563606 (y : real) (z : real) : (term249 y z) = term262.
Proof. exact (TRANS (@lem1563580 y z) (@lem1563605 y z)). Qed.
Lemma lem1563607 : term262 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1563608 (y : real) (z : real) : (term249 y z) = term48.
Proof. exact (TRANS (@lem1563606 y z) (@lem1563607)). Qed.
Lemma lem1563609 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563610 (y : real) (z : real) : (term263 y z) = term264.
Proof. exact (MK_COMB (@lem1563609) (@lem1563608 y z)). Qed.
Lemma lem1563611 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563612 (y : real) (z : real) : (term248 y z) = term265.
Proof. exact (MK_COMB (@lem1563610 y z) (@lem1563611)). Qed.
Lemma lem1563613 (x : real) (y : real) (z : real) (h1 : term207 x y z) : term265.
Proof. exact (EQ_MP (@lem1563612 y z) (@lem1563579 x y z h1)). Qed.
Lemma lem1563615 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563616 : term265 = term266.
Proof. exact (@lem1563615 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1563617 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1563618 : term265 = False.
Proof. exact (TRANS (@lem1563616) (@lem1563617)). Qed.
Lemma lem1563619 (x : real) (y : real) (z : real) (h1 : term207 x y z) : False.
Proof. exact (EQ_MP (@lem1563618) (@lem1563613 x y z h1)). Qed.
Lemma lem1563620 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term209 x y z.
Proof. exact (h1). Qed.
Lemma lem1563621 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term208 x y z.
Proof. exact (proj2 (@lem1563620 x y z h1)). Qed.
Lemma lem1563623 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term59 x y z.
Proof. exact (proj2 (@lem1563621 x y z h1)). Qed.
Lemma lem1563624 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term72 x z.
Proof. exact (proj1 (@lem1563621 x y z h1)). Qed.
Lemma lem1563626 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term56 x z.
Proof. exact (proj1 (@lem1563623 x y z h1)). Qed.
Lemma lem1563628 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563629 : term229 = term230.
Proof. exact (@lem1563628 (NUMERAL 0) term195). Qed.
Lemma lem1563630 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563631 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563632 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563631 h1) (fun h1 : term230 = True => @lem1563630)). Qed.
Lemma lem1563633 : term230 = True.
Proof. exact (EQ_MP (@lem1563632) (@lem1563630)). Qed.
Lemma lem1563634 : term229 = True.
Proof. exact (TRANS (@lem1563629) (@lem1563633)). Qed.
Lemma lem1563635 : True = term229.
Proof. exact (SYM (@lem1563634)). Qed.
Lemma lem1563636 : term229.
Proof. exact (EQ_MP (@lem1563635) (@lem0)). Qed.
Lemma lem1563637 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term232 x z.
Proof. exact (conj (@lem1563636) (@lem1563626 x y z h1)). Qed.
Lemma lem1563639 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1563640 (x : real) (z : real) : term234 x z.
Proof. exact (@lem1563639 term235 (term53 x z)). Qed.
Lemma lem1563641 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term236 x z.
Proof. exact (@lem1563640 x z (@lem1563637 x y z h1)). Qed.
Lemma lem1563642 (x : real) (z : real) : (term237 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1563643 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563644 (x : real) (z : real) : (term238 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1563643) (@lem1563642 x z)). Qed.
Lemma lem1563645 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563646 (x : real) (z : real) : (term236 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1563644 x z) (@lem1563645)). Qed.
Lemma lem1563647 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term56 x z.
Proof. exact (EQ_MP (@lem1563646 x z) (@lem1563641 x y z h1)). Qed.
Lemma lem1563649 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563650 : term229 = term230.
Proof. exact (@lem1563649 (NUMERAL 0) term195). Qed.
Lemma lem1563651 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563652 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563653 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563652 h1) (fun h1 : term230 = True => @lem1563651)). Qed.
Lemma lem1563654 : term230 = True.
Proof. exact (EQ_MP (@lem1563653) (@lem1563651)). Qed.
Lemma lem1563655 : term229 = True.
Proof. exact (TRANS (@lem1563650) (@lem1563654)). Qed.
Lemma lem1563656 : True = term229.
Proof. exact (SYM (@lem1563655)). Qed.
Lemma lem1563657 : term229.
Proof. exact (EQ_MP (@lem1563656) (@lem0)). Qed.
Lemma lem1563658 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term239 x z.
Proof. exact (conj (@lem1563657) (@lem1563624 x y z h1)). Qed.
Lemma lem1563660 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1563661 (x : real) (z : real) : term241 x z.
Proof. exact (@lem1563660 term235 (term52 x z)). Qed.
Lemma lem1563662 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term242 x z.
Proof. exact (@lem1563661 x z (@lem1563658 x y z h1)). Qed.
Lemma lem1563663 (x : real) (z : real) : (term243 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1563664 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563665 (x : real) (z : real) : (term244 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1563664) (@lem1563663 x z)). Qed.
Lemma lem1563666 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563667 (x : real) (z : real) : (term242 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1563665 x z) (@lem1563666)). Qed.
Lemma lem1563668 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1563667 x z) (@lem1563662 x y z h1)). Qed.
Lemma lem1563669 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term245 x z.
Proof. exact (conj (@lem1563668 x y z h1) (@lem1563647 x y z h1)). Qed.
Lemma lem1563671 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1563672 (x : real) (z : real) : term247 x z.
Proof. exact (@lem1563671 (term52 x z) (term53 x z)). Qed.
Lemma lem1563673 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term248 x z.
Proof. exact (@lem1563672 x z (@lem1563669 x y z h1)). Qed.
Lemma lem1563674 (x : real) (z : real) : (term249 x z) = (term250 x z).
Proof. exact (@lem1483480 x (term45 x) (term45 z) z). Qed.
Lemma lem1563675 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1483442 term253 x). Qed.
Lemma lem1563677 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563678 : term255 = term48.
Proof. exact (@lem1563677 term195). Qed.
Lemma lem1563679 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563680 : term256 = term257.
Proof. exact (MK_COMB (@lem1563679) (@lem1563678)). Qed.
Lemma lem1563681 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1563682 (x : real) : (term252 x) = (term258 x).
Proof. exact (MK_COMB (@lem1563680) (@lem1563681 x)). Qed.
Lemma lem1563683 (x : real) : (term251 x) = (term258 x).
Proof. exact (TRANS (@lem1563675 x) (@lem1563682 x)). Qed.
Lemma lem1563684 (x : real) : (term258 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1563685 (x : real) : (term251 x) = term48.
Proof. exact (TRANS (@lem1563683 x) (@lem1563684 x)). Qed.
Lemma lem1563686 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1563687 (x : real) : (term259 x) = term260.
Proof. exact (MK_COMB (@lem1563686) (@lem1563685 x)). Qed.
Lemma lem1563688 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1563690 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563691 : term255 = term48.
Proof. exact (@lem1563690 term195). Qed.
Lemma lem1563692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563693 : term256 = term257.
Proof. exact (MK_COMB (@lem1563692) (@lem1563691)). Qed.
Lemma lem1563694 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1563695 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1563693) (@lem1563694 z)). Qed.
Lemma lem1563696 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1563688 z) (@lem1563695 z)). Qed.
Lemma lem1563697 (z : real) : (term258 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1563698 (z : real) : (term261 z) = term48.
Proof. exact (TRANS (@lem1563696 z) (@lem1563697 z)). Qed.
Lemma lem1563699 (x : real) (z : real) : (term250 x z) = term262.
Proof. exact (MK_COMB (@lem1563687 x) (@lem1563698 z)). Qed.
Lemma lem1563700 (x : real) (z : real) : (term249 x z) = term262.
Proof. exact (TRANS (@lem1563674 x z) (@lem1563699 x z)). Qed.
Lemma lem1563701 : term262 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1563702 (x : real) (z : real) : (term249 x z) = term48.
Proof. exact (TRANS (@lem1563700 x z) (@lem1563701)). Qed.
Lemma lem1563703 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563704 (x : real) (z : real) : (term263 x z) = term264.
Proof. exact (MK_COMB (@lem1563703) (@lem1563702 x z)). Qed.
Lemma lem1563705 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563706 (x : real) (z : real) : (term248 x z) = term265.
Proof. exact (MK_COMB (@lem1563704 x z) (@lem1563705)). Qed.
Lemma lem1563707 (x : real) (y : real) (z : real) (h1 : term209 x y z) : term265.
Proof. exact (EQ_MP (@lem1563706 x z) (@lem1563673 x y z h1)). Qed.
Lemma lem1563709 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563710 : term265 = term266.
Proof. exact (@lem1563709 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1563711 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1563712 : term265 = False.
Proof. exact (TRANS (@lem1563710) (@lem1563711)). Qed.
Lemma lem1563713 (x : real) (y : real) (z : real) (h1 : term209 x y z) : False.
Proof. exact (EQ_MP (@lem1563712) (@lem1563707 x y z h1)). Qed.
Lemma lem1563714 (x : real) (y : real) (z : real) (h1 : term211 x y z) : False.
Proof. exact (or_elim (@lem1563525 x y z h1) (fun h0 : term207 x y z => @lem1563619 x y z h0) (fun h0 : term209 x y z => @lem1563713 x y z h0)). Qed.
Lemma lem1563715 (x : real) (y : real) (z : real) (h1 : term225 x y z) : term225 x y z.
Proof. exact (h1). Qed.
Lemma lem1563716 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term220 y x z.
Proof. exact (h1). Qed.
Lemma lem1563717 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term72 x z.
Proof. exact (proj2 (@lem1563716 y x z h1)). Qed.
Lemma lem1563718 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term59 x y z.
Proof. exact (proj1 (@lem1563716 y x z h1)). Qed.
Lemma lem1563720 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term56 x z.
Proof. exact (proj1 (@lem1563718 y x z h1)). Qed.
Lemma lem1563722 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563723 : term229 = term230.
Proof. exact (@lem1563722 (NUMERAL 0) term195). Qed.
Lemma lem1563724 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563725 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563726 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563725 h1) (fun h1 : term230 = True => @lem1563724)). Qed.
Lemma lem1563727 : term230 = True.
Proof. exact (EQ_MP (@lem1563726) (@lem1563724)). Qed.
Lemma lem1563728 : term229 = True.
Proof. exact (TRANS (@lem1563723) (@lem1563727)). Qed.
Lemma lem1563729 : True = term229.
Proof. exact (SYM (@lem1563728)). Qed.
Lemma lem1563730 : term229.
Proof. exact (EQ_MP (@lem1563729) (@lem0)). Qed.
Lemma lem1563731 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term232 x z.
Proof. exact (conj (@lem1563730) (@lem1563720 y x z h1)). Qed.
Lemma lem1563733 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1563734 (x : real) (z : real) : term234 x z.
Proof. exact (@lem1563733 term235 (term53 x z)). Qed.
Lemma lem1563735 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term236 x z.
Proof. exact (@lem1563734 x z (@lem1563731 y x z h1)). Qed.
Lemma lem1563736 (x : real) (z : real) : (term237 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1563737 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563738 (x : real) (z : real) : (term238 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1563737) (@lem1563736 x z)). Qed.
Lemma lem1563739 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563740 (x : real) (z : real) : (term236 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1563738 x z) (@lem1563739)). Qed.
Lemma lem1563741 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term56 x z.
Proof. exact (EQ_MP (@lem1563740 x z) (@lem1563735 y x z h1)). Qed.
Lemma lem1563743 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563744 : term229 = term230.
Proof. exact (@lem1563743 (NUMERAL 0) term195). Qed.
Lemma lem1563745 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563746 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563747 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563746 h1) (fun h1 : term230 = True => @lem1563745)). Qed.
Lemma lem1563748 : term230 = True.
Proof. exact (EQ_MP (@lem1563747) (@lem1563745)). Qed.
Lemma lem1563749 : term229 = True.
Proof. exact (TRANS (@lem1563744) (@lem1563748)). Qed.
Lemma lem1563750 : True = term229.
Proof. exact (SYM (@lem1563749)). Qed.
Lemma lem1563751 : term229.
Proof. exact (EQ_MP (@lem1563750) (@lem0)). Qed.
Lemma lem1563752 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term239 x z.
Proof. exact (conj (@lem1563751) (@lem1563717 y x z h1)). Qed.
Lemma lem1563754 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1563755 (x : real) (z : real) : term241 x z.
Proof. exact (@lem1563754 term235 (term52 x z)). Qed.
Lemma lem1563756 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term242 x z.
Proof. exact (@lem1563755 x z (@lem1563752 y x z h1)). Qed.
Lemma lem1563757 (x : real) (z : real) : (term243 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1563758 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563759 (x : real) (z : real) : (term244 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1563758) (@lem1563757 x z)). Qed.
Lemma lem1563760 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563761 (x : real) (z : real) : (term242 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1563759 x z) (@lem1563760)). Qed.
Lemma lem1563762 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1563761 x z) (@lem1563756 y x z h1)). Qed.
Lemma lem1563763 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term245 x z.
Proof. exact (conj (@lem1563762 y x z h1) (@lem1563741 y x z h1)). Qed.
Lemma lem1563765 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1563766 (x : real) (z : real) : term247 x z.
Proof. exact (@lem1563765 (term52 x z) (term53 x z)). Qed.
Lemma lem1563767 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term248 x z.
Proof. exact (@lem1563766 x z (@lem1563763 y x z h1)). Qed.
Lemma lem1563768 (x : real) (z : real) : (term249 x z) = (term250 x z).
Proof. exact (@lem1483480 x (term45 x) (term45 z) z). Qed.
Lemma lem1563769 (x : real) : (term251 x) = (term252 x).
Proof. exact (@lem1483442 term253 x). Qed.
Lemma lem1563771 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563772 : term255 = term48.
Proof. exact (@lem1563771 term195). Qed.
Lemma lem1563773 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563774 : term256 = term257.
Proof. exact (MK_COMB (@lem1563773) (@lem1563772)). Qed.
Lemma lem1563775 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1563776 (x : real) : (term252 x) = (term258 x).
Proof. exact (MK_COMB (@lem1563774) (@lem1563775 x)). Qed.
Lemma lem1563777 (x : real) : (term251 x) = (term258 x).
Proof. exact (TRANS (@lem1563769 x) (@lem1563776 x)). Qed.
Lemma lem1563778 (x : real) : (term258 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1563779 (x : real) : (term251 x) = term48.
Proof. exact (TRANS (@lem1563777 x) (@lem1563778 x)). Qed.
Lemma lem1563780 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1563781 (x : real) : (term259 x) = term260.
Proof. exact (MK_COMB (@lem1563780) (@lem1563779 x)). Qed.
Lemma lem1563782 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1563784 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563785 : term255 = term48.
Proof. exact (@lem1563784 term195). Qed.
Lemma lem1563786 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563787 : term256 = term257.
Proof. exact (MK_COMB (@lem1563786) (@lem1563785)). Qed.
Lemma lem1563788 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1563789 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1563787) (@lem1563788 z)). Qed.
Lemma lem1563790 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1563782 z) (@lem1563789 z)). Qed.
Lemma lem1563791 (z : real) : (term258 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1563792 (z : real) : (term261 z) = term48.
Proof. exact (TRANS (@lem1563790 z) (@lem1563791 z)). Qed.
Lemma lem1563793 (x : real) (z : real) : (term250 x z) = term262.
Proof. exact (MK_COMB (@lem1563781 x) (@lem1563792 z)). Qed.
Lemma lem1563794 (x : real) (z : real) : (term249 x z) = term262.
Proof. exact (TRANS (@lem1563768 x z) (@lem1563793 x z)). Qed.
Lemma lem1563795 : term262 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1563796 (x : real) (z : real) : (term249 x z) = term48.
Proof. exact (TRANS (@lem1563794 x z) (@lem1563795)). Qed.
Lemma lem1563797 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563798 (x : real) (z : real) : (term263 x z) = term264.
Proof. exact (MK_COMB (@lem1563797) (@lem1563796 x z)). Qed.
Lemma lem1563799 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563800 (x : real) (z : real) : (term248 x z) = term265.
Proof. exact (MK_COMB (@lem1563798 x z) (@lem1563799)). Qed.
Lemma lem1563801 (y : real) (x : real) (z : real) (h1 : term220 y x z) : term265.
Proof. exact (EQ_MP (@lem1563800 x z) (@lem1563767 y x z h1)). Qed.
Lemma lem1563803 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563804 : term265 = term266.
Proof. exact (@lem1563803 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1563805 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1563806 : term265 = False.
Proof. exact (TRANS (@lem1563804) (@lem1563805)). Qed.
Lemma lem1563807 (y : real) (x : real) (z : real) (h1 : term220 y x z) : False.
Proof. exact (EQ_MP (@lem1563806) (@lem1563801 y x z h1)). Qed.
Lemma lem1563808 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term222 x y z.
Proof. exact (h1). Qed.
Lemma lem1563809 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 y z.
Proof. exact (proj2 (@lem1563808 x y z h1)). Qed.
Lemma lem1563810 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term59 x y z.
Proof. exact (proj1 (@lem1563808 x y z h1)). Qed.
Lemma lem1563811 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term56 y z.
Proof. exact (proj2 (@lem1563810 x y z h1)). Qed.
Lemma lem1563814 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563815 : term229 = term230.
Proof. exact (@lem1563814 (NUMERAL 0) term195). Qed.
Lemma lem1563816 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563817 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563818 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563817 h1) (fun h1 : term230 = True => @lem1563816)). Qed.
Lemma lem1563819 : term230 = True.
Proof. exact (EQ_MP (@lem1563818) (@lem1563816)). Qed.
Lemma lem1563820 : term229 = True.
Proof. exact (TRANS (@lem1563815) (@lem1563819)). Qed.
Lemma lem1563821 : True = term229.
Proof. exact (SYM (@lem1563820)). Qed.
Lemma lem1563822 : term229.
Proof. exact (EQ_MP (@lem1563821) (@lem0)). Qed.
Lemma lem1563823 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term232 y z.
Proof. exact (conj (@lem1563822) (@lem1563811 x y z h1)). Qed.
Lemma lem1563825 (x : real) (y : real) : term233 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1563826 (y : real) (z : real) : term234 y z.
Proof. exact (@lem1563825 term235 (term53 y z)). Qed.
Lemma lem1563827 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term236 y z.
Proof. exact (@lem1563826 y z (@lem1563823 x y z h1)). Qed.
Lemma lem1563828 (y : real) (z : real) : (term237 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1563829 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1563830 (y : real) (z : real) : (term238 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1563829) (@lem1563828 y z)). Qed.
Lemma lem1563831 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563832 (y : real) (z : real) : (term236 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1563830 y z) (@lem1563831)). Qed.
Lemma lem1563833 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1563832 y z) (@lem1563827 x y z h1)). Qed.
Lemma lem1563835 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563836 : term229 = term230.
Proof. exact (@lem1563835 (NUMERAL 0) term195). Qed.
Lemma lem1563837 : term231 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1563838 (h1 : term231 = (BIT1 0)) : term230 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1563839 : (term231 = (BIT1 0)) = (term230 = True).
Proof. exact (prop_ext (fun h1 : term231 = (BIT1 0) => @lem1563838 h1) (fun h1 : term230 = True => @lem1563837)). Qed.
Lemma lem1563840 : term230 = True.
Proof. exact (EQ_MP (@lem1563839) (@lem1563837)). Qed.
Lemma lem1563841 : term229 = True.
Proof. exact (TRANS (@lem1563836) (@lem1563840)). Qed.
Lemma lem1563842 : True = term229.
Proof. exact (SYM (@lem1563841)). Qed.
Lemma lem1563843 : term229.
Proof. exact (EQ_MP (@lem1563842) (@lem0)). Qed.
Lemma lem1563844 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term239 y z.
Proof. exact (conj (@lem1563843) (@lem1563809 x y z h1)). Qed.
Lemma lem1563846 (x : real) (y : real) : term240 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1563847 (y : real) (z : real) : term241 y z.
Proof. exact (@lem1563846 term235 (term52 y z)). Qed.
Lemma lem1563848 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term242 y z.
Proof. exact (@lem1563847 y z (@lem1563844 x y z h1)). Qed.
Lemma lem1563849 (y : real) (z : real) : (term243 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1563850 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563851 (y : real) (z : real) : (term244 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1563850) (@lem1563849 y z)). Qed.
Lemma lem1563852 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563853 (y : real) (z : real) : (term242 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1563851 y z) (@lem1563852)). Qed.
Lemma lem1563854 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1563853 y z) (@lem1563848 x y z h1)). Qed.
Lemma lem1563855 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term245 y z.
Proof. exact (conj (@lem1563854 x y z h1) (@lem1563833 x y z h1)). Qed.
Lemma lem1563857 (x : real) (y : real) : term246 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1563858 (y : real) (z : real) : term247 y z.
Proof. exact (@lem1563857 (term52 y z) (term53 y z)). Qed.
Lemma lem1563859 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term248 y z.
Proof. exact (@lem1563858 y z (@lem1563855 x y z h1)). Qed.
Lemma lem1563860 (y : real) (z : real) : (term249 y z) = (term250 y z).
Proof. exact (@lem1483480 y (term45 y) (term45 z) z). Qed.
Lemma lem1563861 (y : real) : (term251 y) = (term252 y).
Proof. exact (@lem1483442 term253 y). Qed.
Lemma lem1563863 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563864 : term255 = term48.
Proof. exact (@lem1563863 term195). Qed.
Lemma lem1563865 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563866 : term256 = term257.
Proof. exact (MK_COMB (@lem1563865) (@lem1563864)). Qed.
Lemma lem1563867 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1563868 (y : real) : (term252 y) = (term258 y).
Proof. exact (MK_COMB (@lem1563866) (@lem1563867 y)). Qed.
Lemma lem1563869 (y : real) : (term251 y) = (term258 y).
Proof. exact (TRANS (@lem1563861 y) (@lem1563868 y)). Qed.
Lemma lem1563870 (y : real) : (term258 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1563871 (y : real) : (term251 y) = term48.
Proof. exact (TRANS (@lem1563869 y) (@lem1563870 y)). Qed.
Lemma lem1563872 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1563873 (y : real) : (term259 y) = term260.
Proof. exact (MK_COMB (@lem1563872) (@lem1563871 y)). Qed.
Lemma lem1563874 (z : real) : (term261 z) = (term252 z).
Proof. exact (@lem1483440 term253 z). Qed.
Lemma lem1563876 (m : nat) : (term254 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1563877 : term255 = term48.
Proof. exact (@lem1563876 term195). Qed.
Lemma lem1563878 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1563879 : term256 = term257.
Proof. exact (MK_COMB (@lem1563878) (@lem1563877)). Qed.
Lemma lem1563880 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1563881 (z : real) : (term252 z) = (term258 z).
Proof. exact (MK_COMB (@lem1563879) (@lem1563880 z)). Qed.
Lemma lem1563882 (z : real) : (term261 z) = (term258 z).
Proof. exact (TRANS (@lem1563874 z) (@lem1563881 z)). Qed.
Lemma lem1563883 (z : real) : (term258 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1563884 (z : real) : (term261 z) = term48.
Proof. exact (TRANS (@lem1563882 z) (@lem1563883 z)). Qed.
Lemma lem1563885 (y : real) (z : real) : (term250 y z) = term262.
Proof. exact (MK_COMB (@lem1563873 y) (@lem1563884 z)). Qed.
Lemma lem1563886 (y : real) (z : real) : (term249 y z) = term262.
Proof. exact (TRANS (@lem1563860 y z) (@lem1563885 y z)). Qed.
Lemma lem1563887 : term262 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1563888 (y : real) (z : real) : (term249 y z) = term48.
Proof. exact (TRANS (@lem1563886 y z) (@lem1563887)). Qed.
Lemma lem1563889 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1563890 (y : real) (z : real) : (term263 y z) = term264.
Proof. exact (MK_COMB (@lem1563889) (@lem1563888 y z)). Qed.
Lemma lem1563891 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1563892 (y : real) (z : real) : (term248 y z) = term265.
Proof. exact (MK_COMB (@lem1563890 y z) (@lem1563891)). Qed.
Lemma lem1563893 (x : real) (y : real) (z : real) (h1 : term222 x y z) : term265.
Proof. exact (EQ_MP (@lem1563892 y z) (@lem1563859 x y z h1)). Qed.
Lemma lem1563895 (n : nat) (m : nat) : (term228 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1563896 : term265 = term266.
Proof. exact (@lem1563895 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1563897 : term266 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1563898 : term265 = False.
Proof. exact (TRANS (@lem1563896) (@lem1563897)). Qed.
Lemma lem1563899 (x : real) (y : real) (z : real) (h1 : term222 x y z) : False.
Proof. exact (EQ_MP (@lem1563898) (@lem1563893 x y z h1)). Qed.
Lemma lem1563900 (x : real) (y : real) (z : real) (h1 : term225 x y z) : False.
Proof. exact (or_elim (@lem1563715 x y z h1) (fun h0 : term220 y x z => @lem1563807 y x z h0) (fun h0 : term222 x y z => @lem1563899 x y z h0)). Qed.
Lemma lem1563901 (x : real) (y : real) (z : real) (h1 : term227 x y z) : False.
Proof. exact (or_elim (@lem1563524 x y z h1) (fun h0 : term211 x y z => @lem1563714 x y z h0) (fun h0 : term225 x y z => @lem1563900 x y z h0)). Qed.
Lemma lem1563902 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term162 x y z.
Proof. exact (h1). Qed.
Lemma lem1563903 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term227 x y z.
Proof. exact (EQ_MP (@lem1563523 x y z) (@lem1563902 x y z h1)). Qed.
Lemma lem1563904 (x : real) (y : real) (z : real) (h1 : term162 x y z) : (term227 x y z) = False.
Proof. exact (prop_ext (fun h2 : term227 x y z => @lem1563901 x y z h2) (fun h2 : False => @lem1563903 x y z h1)). Qed.
Lemma lem1563905 (x : real) (y : real) (z : real) (h1 : term162 x y z) : False.
Proof. exact (EQ_MP (@lem1563904 x y z h1) (@lem1563903 x y z h1)). Qed.
Lemma lem1563906 (x : real) (y : real) (h1 : term164 x y) : term164 x y.
Proof. exact (h1). Qed.
Lemma lem1563907 (x : real) (y : real) (h1 : term164 x y) : False.
Proof. exact (ex_elim (@lem1563906 x y h1) (fun z : real => fun h0 : term163 x y z => @lem1563905 x y z h0)). Qed.
Lemma lem1563908 (x : real) (h1 : term166 x) : term166 x.
Proof. exact (h1). Qed.
Lemma lem1563909 (x : real) (h1 : term166 x) : False.
Proof. exact (ex_elim (@lem1563908 x h1) (fun y : real => fun h0 : term165 x y => @lem1563907 x y h0)). Qed.
Lemma lem1563910 (h1 : term168) : term168.
Proof. exact (h1). Qed.
Lemma lem1563911 (h1 : term168) : False.
Proof. exact (ex_elim (@lem1563910 h1) (fun x : real => fun h0 : term167 x => @lem1563909 x h0)). Qed.
Lemma lem1563912 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1563913 (h1 : term32) : term168.
Proof. exact (EQ_MP (@lem1563203) (@lem1563912 h1)). Qed.
Lemma lem1563914 (h1 : term32) : term168 = False.
Proof. exact (prop_ext (fun h2 : term168 => @lem1563911 h2) (fun h2 : False => @lem1563913 h1)). Qed.
Lemma lem1563915 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1563914 h1) (@lem1563913 h1)). Qed.
Lemma lem1563916 : term267.
Proof. exact (fun h0 : term32 => @lem1563915 h0). Qed.
Lemma lem1563917 : term268.
Proof. exact (@lem1386578 term269). Qed.
Lemma lem1563918 : term269.
Proof. exact (@lem1563917 (@lem1563916)). Qed.
