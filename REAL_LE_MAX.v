Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_MAX_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482710_spec.
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
Require Import thm1483523_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
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
Lemma lem1559419 (x : real) (z : real) (y : real) : (term0 x z y) = (term1 x z y).
Proof. exact (@lem17160 (real_le z x) (real_le z y)). Qed.
Lemma lem1559425 (x : real) (z : real) (y : real) : (term2 x z y) = (term2 x z y).
Proof. exact (eq_refl (term2 x z y)). Qed.
Lemma lem1559427 (z : real) (x : real) (y : real) : (term3 z x y) = (term3 z x y).
Proof. exact (eq_refl (term3 z x y)). Qed.
Lemma lem1559428 (x : real) (z : real) (y : real) : (term4 x z y) = (term5 x z y).
Proof. exact (MK_COMB (@lem1559427 z x y) (@lem1559419 x z y)). Qed.
Lemma lem1559429 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559430 (x : real) (z : real) (y : real) : (term6 x z y) = (term7 x z y).
Proof. exact (MK_COMB (@lem1559429) (@lem1559428 x z y)). Qed.
Lemma lem1559431 (x : real) (z : real) (y : real) : (term8 x z y) = (term9 x z y).
Proof. exact (MK_COMB (@lem1559430 x z y) (@lem1559425 x z y)). Qed.
Lemma lem1559432 (x : real) (z : real) (y : real) : (term10 x z y) = (term8 x z y).
Proof. exact (@lem17646 (term11 z x y) (term12 x z y)). Qed.
Lemma lem1559433 (x : real) (z : real) (y : real) : (term10 x z y) = (term9 x z y).
Proof. exact (TRANS (@lem1559432 x z y) (@lem1559431 x z y)). Qed.
Lemma lem1559434 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1559435 (x : real) (y : real) : (term15 x y) = (term16 x y).
Proof. exact (@lem1559434 (term17 x y)). Qed.
Lemma lem1559436 (x : real) (z : real) (y : real) : (term18 x y z) = ((term11 z x y) = (term12 x z y)).
Proof. exact (eq_refl (term18 x y z)). Qed.
Lemma lem1559437 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1559438 (x : real) (z : real) (y : real) : (term19 x y z) = (term10 x z y).
Proof. exact (MK_COMB (@lem1559437) (@lem1559436 x z y)). Qed.
Lemma lem1559439 (x : real) (z : real) (y : real) : (term19 x y z) = (term9 x z y).
Proof. exact (TRANS (@lem1559438 x z y) (@lem1559433 x z y)). Qed.
Lemma lem1559440 (x : real) (y : real) : (term20 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1559439 x z y)). Qed.
Lemma lem1559441 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559442 (x : real) (y : real) : (term16 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1559441) (@lem1559440 x y)). Qed.
Lemma lem1559443 (x : real) (y : real) : (term15 x y) = (term22 x y).
Proof. exact (TRANS (@lem1559435 x y) (@lem1559442 x y)). Qed.
Lemma lem1559444 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1559445 (x : real) : (term23 x) = (term24 x).
Proof. exact (@lem1559444 (term25 x)). Qed.
Lemma lem1559446 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (eq_refl (term26 x y)). Qed.
Lemma lem1559447 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1559448 (x : real) (y : real) : (term28 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1559447) (@lem1559446 x y)). Qed.
Lemma lem1559449 (x : real) (y : real) : (term28 x y) = (term22 x y).
Proof. exact (TRANS (@lem1559448 x y) (@lem1559443 x y)). Qed.
Lemma lem1559450 (x : real) : (term29 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1559449 x y)). Qed.
Lemma lem1559451 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559452 (x : real) : (term24 x) = (term31 x).
Proof. exact (MK_COMB (@lem1559451) (@lem1559450 x)). Qed.
Lemma lem1559453 (x : real) : (term23 x) = (term31 x).
Proof. exact (TRANS (@lem1559445 x) (@lem1559452 x)). Qed.
Lemma lem1559454 (P : real -> Prop) : (term13 P) = (term14 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1559455 : term32 = term33.
Proof. exact (@lem1559454 term34). Qed.
Lemma lem1559456 (x : real) : (term35 x) = (term36 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1559457 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1559458 (x : real) : (term37 x) = (term23 x).
Proof. exact (MK_COMB (@lem1559457) (@lem1559456 x)). Qed.
Lemma lem1559459 (x : real) : (term37 x) = (term31 x).
Proof. exact (TRANS (@lem1559458 x) (@lem1559453 x)). Qed.
Lemma lem1559460 : term38 = term39.
Proof. exact (fun_ext (fun x : real => @lem1559459 x)). Qed.
Lemma lem1559461 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559462 : term33 = term40.
Proof. exact (MK_COMB (@lem1559461) (@lem1559460)). Qed.
Lemma lem1559464 : term32 = term40.
Proof. exact (TRANS (@lem1559455) (@lem1559462)). Qed.
Lemma lem1559491 (x : real) (z : real) (y : real) : (term9 x z y) = (term9 x z y).
Proof. exact (eq_refl (term9 x z y)). Qed.
Lemma lem1559492 (x : real) (y : real) : (term21 x y) = (term21 x y).
Proof. exact (fun_ext (fun z : real => @lem1559491 x z y)). Qed.
Lemma lem1559493 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559494 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1559493) (@lem1559492 x y)). Qed.
Lemma lem1559495 (x : real) : (term30 x) = (term30 x).
Proof. exact (fun_ext (fun y : real => @lem1559494 x y)). Qed.
Lemma lem1559496 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559497 (x : real) : (term31 x) = (term31 x).
Proof. exact (MK_COMB (@lem1559496) (@lem1559495 x)). Qed.
Lemma lem1559498 : term39 = term39.
Proof. exact (fun_ext (fun x : real => @lem1559497 x)). Qed.
Lemma lem1559499 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559500 : term40 = term40.
Proof. exact (MK_COMB (@lem1559499) (@lem1559498)). Qed.
Lemma lem1559501 : term32 = term40.
Proof. exact (TRANS (@lem1559464) (@lem1559500)). Qed.
Lemma lem1559502 (x : real) (y : real) (z : real) : (term11 z x y) = (term41 x y z).
Proof. exact (@lem1483523 (real_max x y) z). Qed.
Lemma lem1559508 (x : real) (y : real) (z : real) : (term42 x y z) = (term43 x y z).
Proof. exact (@lem1483519 (real_max x y) z). Qed.
Lemma lem1559513 (z : real) (x : real) (y : real) : (term43 x y z) = (term44 z x y).
Proof. exact (@lem1483488 (term45 z) (real_max x y)). Qed.
Lemma lem1559515 (z : real) (x : real) (y : real) : (term42 x y z) = (term44 z x y).
Proof. exact (TRANS (@lem1559508 x y z) (@lem1559513 z x y)). Qed.
Lemma lem1559516 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1559517 (z : real) (x : real) (y : real) : (term46 x y z) = (term47 z x y).
Proof. exact (MK_COMB (@lem1559516) (@lem1559515 z x y)). Qed.
Lemma lem1559518 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1559519 (z : real) (x : real) (y : real) : (term41 x y z) = (term49 z x y).
Proof. exact (MK_COMB (@lem1559517 z x y) (@lem1559518)). Qed.
Lemma lem1559520 (z : real) (x : real) (y : real) : (term11 z x y) = (term49 z x y).
Proof. exact (TRANS (@lem1559502 x y z) (@lem1559519 z x y)). Qed.
Lemma lem1559521 (z : real) (x : real) : (term50 z x) = (term51 z x).
Proof. exact (@lem1483533 z x). Qed.
Lemma lem1559527 (z : real) (x : real) : (real_sub z x) = (term52 z x).
Proof. exact (@lem1483519 z x). Qed.
Lemma lem1559532 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1559534 (x : real) (z : real) : (real_sub z x) = (term53 x z).
Proof. exact (TRANS (@lem1559527 z x) (@lem1559532 x z)). Qed.
Lemma lem1559535 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559536 (x : real) (z : real) : (term54 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1559535) (@lem1559534 x z)). Qed.
Lemma lem1559537 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1559538 (x : real) (z : real) : (term51 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1559536 x z) (@lem1559537)). Qed.
Lemma lem1559539 (x : real) (z : real) : (term50 z x) = (term56 x z).
Proof. exact (TRANS (@lem1559521 z x) (@lem1559538 x z)). Qed.
Lemma lem1559540 (z : real) (y : real) : (term50 z y) = (term51 z y).
Proof. exact (@lem1483533 z y). Qed.
Lemma lem1559546 (z : real) (y : real) : (real_sub z y) = (term52 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1559551 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1559553 (y : real) (z : real) : (real_sub z y) = (term53 y z).
Proof. exact (TRANS (@lem1559546 z y) (@lem1559551 y z)). Qed.
Lemma lem1559554 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559555 (y : real) (z : real) : (term54 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1559554) (@lem1559553 y z)). Qed.
Lemma lem1559556 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1559557 (y : real) (z : real) : (term51 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1559555 y z) (@lem1559556)). Qed.
Lemma lem1559558 (y : real) (z : real) : (term50 z y) = (term56 y z).
Proof. exact (TRANS (@lem1559540 z y) (@lem1559557 y z)). Qed.
Lemma lem1559559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559560 (x : real) (z : real) : (term57 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1559559) (@lem1559539 x z)). Qed.
Lemma lem1559561 (x : real) (y : real) (z : real) : (term1 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1559560 x z) (@lem1559558 y z)). Qed.
Lemma lem1559562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559563 (z : real) (x : real) (y : real) : (term3 z x y) = (term60 z x y).
Proof. exact (MK_COMB (@lem1559562) (@lem1559520 z x y)). Qed.
Lemma lem1559564 (x : real) (y : real) (z : real) : (term5 x z y) = (term61 x y z).
Proof. exact (MK_COMB (@lem1559563 z x y) (@lem1559561 x y z)). Qed.
Lemma lem1559565 (z : real) (x : real) (y : real) : (term62 z x y) = (term63 z x y).
Proof. exact (@lem1483533 z (real_max x y)). Qed.
Lemma lem1559578 (z : real) (x : real) (y : real) : (term64 z x y) = (term65 z x y).
Proof. exact (@lem1483519 z (real_max x y)). Qed.
Lemma lem1559579 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1559580 (z : real) (x : real) (y : real) : (term66 z x y) = (term67 z x y).
Proof. exact (MK_COMB (@lem1559579) (@lem1559578 z x y)). Qed.
Lemma lem1559581 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1559582 (z : real) (x : real) (y : real) : (term63 z x y) = (term68 z x y).
Proof. exact (MK_COMB (@lem1559580 z x y) (@lem1559581)). Qed.
Lemma lem1559583 (z : real) (x : real) (y : real) : (term62 z x y) = (term68 z x y).
Proof. exact (TRANS (@lem1559565 z x y) (@lem1559582 z x y)). Qed.
Lemma lem1559584 (x : real) (z : real) : (real_le z x) = (term69 x z).
Proof. exact (@lem1483523 x z). Qed.
Lemma lem1559597 (x : real) (z : real) : (real_sub x z) = (term52 x z).
Proof. exact (@lem1483519 x z). Qed.
Lemma lem1559598 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1559599 (x : real) (z : real) : (term70 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1559598) (@lem1559597 x z)). Qed.
Lemma lem1559600 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1559601 (x : real) (z : real) : (term69 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1559599 x z) (@lem1559600)). Qed.
Lemma lem1559602 (x : real) (z : real) : (real_le z x) = (term72 x z).
Proof. exact (TRANS (@lem1559584 x z) (@lem1559601 x z)). Qed.
Lemma lem1559603 (y : real) (z : real) : (real_le z y) = (term69 y z).
Proof. exact (@lem1483523 y z). Qed.
Lemma lem1559616 (y : real) (z : real) : (real_sub y z) = (term52 y z).
Proof. exact (@lem1483519 y z). Qed.
Lemma lem1559617 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1559618 (y : real) (z : real) : (term70 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1559617) (@lem1559616 y z)). Qed.
Lemma lem1559619 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1559620 (y : real) (z : real) : (term69 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1559618 y z) (@lem1559619)). Qed.
Lemma lem1559621 (y : real) (z : real) : (real_le z y) = (term72 y z).
Proof. exact (TRANS (@lem1559603 y z) (@lem1559620 y z)). Qed.
Lemma lem1559622 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559623 (x : real) (z : real) : (term73 z x) = (term74 x z).
Proof. exact (MK_COMB (@lem1559622) (@lem1559602 x z)). Qed.
Lemma lem1559624 (x : real) (y : real) (z : real) : (term12 x z y) = (term75 x y z).
Proof. exact (MK_COMB (@lem1559623 x z) (@lem1559621 y z)). Qed.
Lemma lem1559625 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1559626 (z : real) (x : real) (y : real) : (term76 z x y) = (term77 z x y).
Proof. exact (MK_COMB (@lem1559625) (@lem1559583 z x y)). Qed.
Lemma lem1559627 (x : real) (y : real) (z : real) : (term2 x z y) = (term78 x y z).
Proof. exact (MK_COMB (@lem1559626 z x y) (@lem1559624 x y z)). Qed.
Lemma lem1559628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559629 (x : real) (y : real) (z : real) : (term7 x z y) = (term79 x y z).
Proof. exact (MK_COMB (@lem1559628) (@lem1559564 x y z)). Qed.
Lemma lem1559630 (x : real) (y : real) (z : real) : (term9 x z y) = (term80 x y z).
Proof. exact (MK_COMB (@lem1559629 x y z) (@lem1559627 x y z)). Qed.
Lemma lem1559631 (x : real) (y : real) : (term21 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1559630 x y z)). Qed.
Lemma lem1559632 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559633 (x : real) (y : real) : (term22 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1559632) (@lem1559631 x y)). Qed.
Lemma lem1559634 (x : real) : (term30 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1559633 x y)). Qed.
Lemma lem1559635 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559636 (x : real) : (term31 x) = (term84 x).
Proof. exact (MK_COMB (@lem1559635) (@lem1559634 x)). Qed.
Lemma lem1559637 : term39 = term85.
Proof. exact (fun_ext (fun x : real => @lem1559636 x)). Qed.
Lemma lem1559638 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559639 : term40 = term86.
Proof. exact (MK_COMB (@lem1559638) (@lem1559637)). Qed.
Lemma lem1559640 : term32 = term86.
Proof. exact (TRANS (@lem1559501) (@lem1559639)). Qed.
Lemma lem1559650 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1559651 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1559650 real P Q). Qed.
Lemma lem1559652 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (@lem1559651 (term93 x y) (term94 x y)). Qed.
Lemma lem1559653 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1559654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559655 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1559654) (@lem1559653 x y z)). Qed.
Lemma lem1559656 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1559657 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1559655 x y z) (@lem1559656 x y z)). Qed.
Lemma lem1559658 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1559657 x y z)). Qed.
Lemma lem1559659 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559660 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1559659) (@lem1559658 x y)). Qed.
Lemma lem1559661 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1559662 (x : real) (y : real) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1559661) (@lem1559660 x y)). Qed.
Lemma lem1559663 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1559664 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1559663 x y z)). Qed.
Lemma lem1559665 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559666 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1559665) (@lem1559664 x y)). Qed.
Lemma lem1559667 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559668 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1559667) (@lem1559666 x y)). Qed.
Lemma lem1559669 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1559670 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1559669 x y z)). Qed.
Lemma lem1559671 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559672 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1559671) (@lem1559670 x y)). Qed.
Lemma lem1559673 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1559668 x y) (@lem1559672 x y)). Qed.
Lemma lem1559674 (x : real) (y : real) : ((term91 x y) = (term92 x y)) = ((term82 x y) = (term110 x y)).
Proof. exact (MK_COMB (@lem1559662 x y) (@lem1559673 x y)). Qed.
Lemma lem1559675 (x : real) (y : real) : (term82 x y) = (term110 x y).
Proof. exact (EQ_MP (@lem1559674 x y) (@lem1559652 x y)). Qed.
Lemma lem1559772 (x : real) : (term83 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1559675 x y)). Qed.
Lemma lem1559773 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559774 (x : real) : (term84 x) = (term112 x).
Proof. exact (MK_COMB (@lem1559773) (@lem1559772 x)). Qed.
Lemma lem1559776 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1559777 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1559776 real P Q). Qed.
Lemma lem1559778 (x : real) : (term113 x) = (term114 x).
Proof. exact (@lem1559777 (term115 x) (term116 x)). Qed.
Lemma lem1559779 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1559780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559781 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1559780) (@lem1559779 x y)). Qed.
Lemma lem1559782 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1559783 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1559781 x y) (@lem1559782 x y)). Qed.
Lemma lem1559784 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1559783 x y)). Qed.
Lemma lem1559785 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559786 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1559785) (@lem1559784 x)). Qed.
Lemma lem1559787 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1559788 (x : real) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1559787) (@lem1559786 x)). Qed.
Lemma lem1559789 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1559790 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1559789 x y)). Qed.
Lemma lem1559791 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559792 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1559791) (@lem1559790 x)). Qed.
Lemma lem1559793 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559794 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1559793) (@lem1559792 x)). Qed.
Lemma lem1559795 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1559796 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1559795 x y)). Qed.
Lemma lem1559797 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559798 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1559797) (@lem1559796 x)). Qed.
Lemma lem1559799 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1559794 x) (@lem1559798 x)). Qed.
Lemma lem1559800 (x : real) : ((term113 x) = (term114 x)) = ((term112 x) = (term132 x)).
Proof. exact (MK_COMB (@lem1559788 x) (@lem1559799 x)). Qed.
Lemma lem1559801 (x : real) : (term112 x) = (term132 x).
Proof. exact (EQ_MP (@lem1559800 x) (@lem1559778 x)). Qed.
Lemma lem1559906 (x : real) : (term84 x) = (term132 x).
Proof. exact (TRANS (@lem1559774 x) (@lem1559801 x)). Qed.
Lemma lem1559907 : term85 = term133.
Proof. exact (fun_ext (fun x : real => @lem1559906 x)). Qed.
Lemma lem1559908 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559909 : term86 = term134.
Proof. exact (MK_COMB (@lem1559908) (@lem1559907)). Qed.
Lemma lem1559911 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term87 A P Q) = (term88 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1559912 (P : real -> Prop) (Q : real -> Prop) : (term89 P Q) = (term90 P Q).
Proof. exact (@lem1559911 real P Q). Qed.
Lemma lem1559913 : term135 = term136.
Proof. exact (@lem1559912 term137 term138). Qed.
Lemma lem1559914 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1559915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559916 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1559915) (@lem1559914 x)). Qed.
Lemma lem1559917 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1559918 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1559916 x) (@lem1559917 x)). Qed.
Lemma lem1559919 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1559918 x)). Qed.
Lemma lem1559920 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559921 : term135 = term134.
Proof. exact (MK_COMB (@lem1559920) (@lem1559919)). Qed.
Lemma lem1559922 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1559923 : term144 = term145.
Proof. exact (MK_COMB (@lem1559922) (@lem1559921)). Qed.
Lemma lem1559924 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1559925 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1559924 x)). Qed.
Lemma lem1559926 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559927 : term147 = term148.
Proof. exact (MK_COMB (@lem1559926) (@lem1559925)). Qed.
Lemma lem1559928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1559929 : term149 = term150.
Proof. exact (MK_COMB (@lem1559928) (@lem1559927)). Qed.
Lemma lem1559930 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1559931 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1559930 x)). Qed.
Lemma lem1559932 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1559933 : term152 = term153.
Proof. exact (MK_COMB (@lem1559932) (@lem1559931)). Qed.
Lemma lem1559934 : term136 = term154.
Proof. exact (MK_COMB (@lem1559929) (@lem1559933)). Qed.
Lemma lem1559935 : (term135 = term136) = (term134 = term154).
Proof. exact (MK_COMB (@lem1559923) (@lem1559934)). Qed.
Lemma lem1559936 : term134 = term154.
Proof. exact (EQ_MP (@lem1559935) (@lem1559913)). Qed.
Lemma lem1560049 : term86 = term154.
Proof. exact (TRANS (@lem1559909) (@lem1559936)). Qed.
Lemma lem1560051 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1560052 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1560051 real P Q). Qed.
Lemma lem1560053 : term136 = term135.
Proof. exact (@lem1560052 term137 term138). Qed.
Lemma lem1560054 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1560055 : term146 = term137.
Proof. exact (fun_ext (fun x : real => @lem1560054 x)). Qed.
Lemma lem1560056 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560057 : term147 = term148.
Proof. exact (MK_COMB (@lem1560056) (@lem1560055)). Qed.
Lemma lem1560058 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560059 : term149 = term150.
Proof. exact (MK_COMB (@lem1560058) (@lem1560057)). Qed.
Lemma lem1560060 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1560061 : term151 = term138.
Proof. exact (fun_ext (fun x : real => @lem1560060 x)). Qed.
Lemma lem1560062 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560063 : term152 = term153.
Proof. exact (MK_COMB (@lem1560062) (@lem1560061)). Qed.
Lemma lem1560064 : term136 = term154.
Proof. exact (MK_COMB (@lem1560059) (@lem1560063)). Qed.
Lemma lem1560065 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1560066 : term155 = term156.
Proof. exact (MK_COMB (@lem1560065) (@lem1560064)). Qed.
Lemma lem1560067 (x : real) : (term139 x) = (term126 x).
Proof. exact (eq_refl (term139 x)). Qed.
Lemma lem1560068 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560069 (x : real) : (term140 x) = (term128 x).
Proof. exact (MK_COMB (@lem1560068) (@lem1560067 x)). Qed.
Lemma lem1560070 (x : real) : (term141 x) = (term131 x).
Proof. exact (eq_refl (term141 x)). Qed.
Lemma lem1560071 (x : real) : (term142 x) = (term132 x).
Proof. exact (MK_COMB (@lem1560069 x) (@lem1560070 x)). Qed.
Lemma lem1560072 : term143 = term133.
Proof. exact (fun_ext (fun x : real => @lem1560071 x)). Qed.
Lemma lem1560073 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560074 : term135 = term134.
Proof. exact (MK_COMB (@lem1560073) (@lem1560072)). Qed.
Lemma lem1560075 : (term136 = term135) = (term154 = term134).
Proof. exact (MK_COMB (@lem1560066) (@lem1560074)). Qed.
Lemma lem1560076 : term154 = term134.
Proof. exact (EQ_MP (@lem1560075) (@lem1560053)). Qed.
Lemma lem1560078 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1560079 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1560078 real P Q). Qed.
Lemma lem1560080 (x : real) : (term114 x) = (term113 x).
Proof. exact (@lem1560079 (term115 x) (term116 x)). Qed.
Lemma lem1560081 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1560082 (x : real) : (term124 x) = (term115 x).
Proof. exact (fun_ext (fun y : real => @lem1560081 x y)). Qed.
Lemma lem1560083 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560084 (x : real) : (term125 x) = (term126 x).
Proof. exact (MK_COMB (@lem1560083) (@lem1560082 x)). Qed.
Lemma lem1560085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560086 (x : real) : (term127 x) = (term128 x).
Proof. exact (MK_COMB (@lem1560085) (@lem1560084 x)). Qed.
Lemma lem1560087 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1560088 (x : real) : (term129 x) = (term116 x).
Proof. exact (fun_ext (fun y : real => @lem1560087 x y)). Qed.
Lemma lem1560089 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560090 (x : real) : (term130 x) = (term131 x).
Proof. exact (MK_COMB (@lem1560089) (@lem1560088 x)). Qed.
Lemma lem1560091 (x : real) : (term114 x) = (term132 x).
Proof. exact (MK_COMB (@lem1560086 x) (@lem1560090 x)). Qed.
Lemma lem1560092 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1560093 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1560092) (@lem1560091 x)). Qed.
Lemma lem1560094 (x : real) (y : real) : (term117 x y) = (term104 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1560095 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560096 (x : real) (y : real) : (term118 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1560095) (@lem1560094 x y)). Qed.
Lemma lem1560097 (x : real) (y : real) : (term119 x y) = (term109 x y).
Proof. exact (eq_refl (term119 x y)). Qed.
Lemma lem1560098 (x : real) (y : real) : (term120 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1560096 x y) (@lem1560097 x y)). Qed.
Lemma lem1560099 (x : real) : (term121 x) = (term111 x).
Proof. exact (fun_ext (fun y : real => @lem1560098 x y)). Qed.
Lemma lem1560100 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560101 (x : real) : (term113 x) = (term112 x).
Proof. exact (MK_COMB (@lem1560100) (@lem1560099 x)). Qed.
Lemma lem1560102 (x : real) : ((term114 x) = (term113 x)) = ((term132 x) = (term112 x)).
Proof. exact (MK_COMB (@lem1560093 x) (@lem1560101 x)). Qed.
Lemma lem1560103 (x : real) : (term132 x) = (term112 x).
Proof. exact (EQ_MP (@lem1560102 x) (@lem1560080 x)). Qed.
Lemma lem1560105 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term88 A P Q) = (term87 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1560106 (P : real -> Prop) (Q : real -> Prop) : (term90 P Q) = (term89 P Q).
Proof. exact (@lem1560105 real P Q). Qed.
Lemma lem1560107 (x : real) (y : real) : (term92 x y) = (term91 x y).
Proof. exact (@lem1560106 (term93 x y) (term94 x y)). Qed.
Lemma lem1560108 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1560109 (x : real) (y : real) : (term102 x y) = (term93 x y).
Proof. exact (fun_ext (fun z : real => @lem1560108 x y z)). Qed.
Lemma lem1560110 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560111 (x : real) (y : real) : (term103 x y) = (term104 x y).
Proof. exact (MK_COMB (@lem1560110) (@lem1560109 x y)). Qed.
Lemma lem1560112 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560113 (x : real) (y : real) : (term105 x y) = (term106 x y).
Proof. exact (MK_COMB (@lem1560112) (@lem1560111 x y)). Qed.
Lemma lem1560114 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1560115 (x : real) (y : real) : (term107 x y) = (term94 x y).
Proof. exact (fun_ext (fun z : real => @lem1560114 x y z)). Qed.
Lemma lem1560116 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560117 (x : real) (y : real) : (term108 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem1560116) (@lem1560115 x y)). Qed.
Lemma lem1560118 (x : real) (y : real) : (term92 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1560113 x y) (@lem1560117 x y)). Qed.
Lemma lem1560119 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1560120 (x : real) (y : real) : (term159 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1560119) (@lem1560118 x y)). Qed.
Lemma lem1560121 (x : real) (y : real) (z : real) : (term95 x y z) = (term61 x y z).
Proof. exact (eq_refl (term95 x y z)). Qed.
Lemma lem1560122 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560123 (x : real) (y : real) (z : real) : (term96 x y z) = (term79 x y z).
Proof. exact (MK_COMB (@lem1560122) (@lem1560121 x y z)). Qed.
Lemma lem1560124 (x : real) (y : real) (z : real) : (term97 x y z) = (term78 x y z).
Proof. exact (eq_refl (term97 x y z)). Qed.
Lemma lem1560125 (x : real) (y : real) (z : real) : (term98 x y z) = (term80 x y z).
Proof. exact (MK_COMB (@lem1560123 x y z) (@lem1560124 x y z)). Qed.
Lemma lem1560126 (x : real) (y : real) : (term99 x y) = (term81 x y).
Proof. exact (fun_ext (fun z : real => @lem1560125 x y z)). Qed.
Lemma lem1560127 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560128 (x : real) (y : real) : (term91 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1560127) (@lem1560126 x y)). Qed.
Lemma lem1560129 (x : real) (y : real) : ((term92 x y) = (term91 x y)) = ((term110 x y) = (term82 x y)).
Proof. exact (MK_COMB (@lem1560120 x y) (@lem1560128 x y)). Qed.
Lemma lem1560130 (x : real) (y : real) : (term110 x y) = (term82 x y).
Proof. exact (EQ_MP (@lem1560129 x y) (@lem1560107 x y)). Qed.
Lemma lem1560131 (x : real) : (term111 x) = (term83 x).
Proof. exact (fun_ext (fun y : real => @lem1560130 x y)). Qed.
Lemma lem1560132 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560133 (x : real) : (term112 x) = (term84 x).
Proof. exact (MK_COMB (@lem1560132) (@lem1560131 x)). Qed.
Lemma lem1560134 (x : real) : (term132 x) = (term84 x).
Proof. exact (TRANS (@lem1560103 x) (@lem1560133 x)). Qed.
Lemma lem1560135 : term133 = term85.
Proof. exact (fun_ext (fun x : real => @lem1560134 x)). Qed.
Lemma lem1560136 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560137 : term134 = term86.
Proof. exact (MK_COMB (@lem1560136) (@lem1560135)). Qed.
Lemma lem1560138 : term154 = term86.
Proof. exact (TRANS (@lem1560076) (@lem1560137)). Qed.
Lemma lem1560139 : term86 = term86.
Proof. exact (TRANS (@lem1560049) (@lem1560138)). Qed.
Lemma lem1560142 : term32 = term86.
Proof. exact (TRANS (@lem1559640) (@lem1560139)). Qed.
Lemma lem1560159 (x : real) (y : real) (z : real) : (term78 x y z) = (term161 x y z).
Proof. exact (@lem19158 (term72 x z) (term68 z x y) (term72 y z)). Qed.
Lemma lem1560174 (x : real) (y : real) (z : real) : (term79 x y z) = (term79 x y z).
Proof. exact (eq_refl (term79 x y z)). Qed.
Lemma lem1560175 (x : real) (y : real) (z : real) : (term80 x y z) = (term162 x y z).
Proof. exact (MK_COMB (@lem1560174 x y z) (@lem1560159 x y z)). Qed.
Lemma lem1560176 (x : real) (y : real) : (term81 x y) = (term163 x y).
Proof. exact (fun_ext (fun z : real => @lem1560175 x y z)). Qed.
Lemma lem1560177 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560178 (x : real) (y : real) : (term82 x y) = (term164 x y).
Proof. exact (MK_COMB (@lem1560177) (@lem1560176 x y)). Qed.
Lemma lem1560179 (x : real) : (term83 x) = (term165 x).
Proof. exact (fun_ext (fun y : real => @lem1560178 x y)). Qed.
Lemma lem1560180 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560181 (x : real) : (term84 x) = (term166 x).
Proof. exact (MK_COMB (@lem1560180) (@lem1560179 x)). Qed.
Lemma lem1560182 : term85 = term167.
Proof. exact (fun_ext (fun x : real => @lem1560181 x)). Qed.
Lemma lem1560183 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1560184 : term86 = term168.
Proof. exact (MK_COMB (@lem1560183) (@lem1560182)). Qed.
Lemma lem1560185 : term32 = term168.
Proof. exact (TRANS (@lem1560142) (@lem1560184)). Qed.
Lemma lem1560187 (x : real) (y : real) (z : real) : (term169 z x y) = (term61 x y z).
Proof. exact (eq_refl (term169 z x y)). Qed.
Lemma lem1560188 (z : real) (x : real) (y : real) : (term61 x y z) = (term169 z x y).
Proof. exact (SYM (@lem1560187 x y z)). Qed.
Lemma lem1560189 (y : real) (z : real) (x : real) : (term169 z x y) = (term170 y z x).
Proof. exact (@lem1483205 y (term171 x y z) x). Qed.
Lemma lem1560190 (y : real) (z : real) (x : real) : (term61 x y z) = (term170 y z x).
Proof. exact (TRANS (@lem1560188 z x y) (@lem1560189 y z x)). Qed.
Lemma lem1560191 (x : real) (y : real) (z : real) : (term172 y z x) = (term173 x y z).
Proof. exact (eq_refl (term172 y z x)). Qed.
Lemma lem1560192 (x : real) (y : real) : (term174 x y) = (term174 x y).
Proof. exact (eq_refl (term174 x y)). Qed.
Lemma lem1560193 (x : real) (y : real) (z : real) : (term175 y z x) = (term176 x y z).
Proof. exact (MK_COMB (@lem1560192 x y) (@lem1560191 x y z)). Qed.
Lemma lem1560194 (x : real) (y : real) (z : real) : (term177 x z y) = (term178 x y z).
Proof. exact (eq_refl (term177 x z y)). Qed.
Lemma lem1560195 (y : real) (x : real) : (term179 y x) = (term179 y x).
Proof. exact (eq_refl (term179 y x)). Qed.
Lemma lem1560196 (x : real) (y : real) (z : real) : (term180 x z y) = (term181 x y z).
Proof. exact (MK_COMB (@lem1560195 y x) (@lem1560194 x y z)). Qed.
Lemma lem1560197 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560198 (x : real) (y : real) (z : real) : (term182 x z y) = (term183 x y z).
Proof. exact (MK_COMB (@lem1560197) (@lem1560196 x y z)). Qed.
Lemma lem1560199 (x : real) (y : real) (z : real) : (term170 y z x) = (term184 x y z).
Proof. exact (MK_COMB (@lem1560198 x y z) (@lem1560193 x y z)). Qed.
Lemma lem1560200 (x : real) (y : real) (z : real) : (term185 x y z) = (term185 x y z).
Proof. exact (eq_refl (term185 x y z)). Qed.
Lemma lem1560201 (x : real) (y : real) (z : real) : ((term61 x y z) = (term170 y z x)) = ((term61 x y z) = (term184 x y z)).
Proof. exact (MK_COMB (@lem1560200 x y z) (@lem1560199 x y z)). Qed.
Lemma lem1560202 (x : real) (y : real) (z : real) : (term61 x y z) = (term184 x y z).
Proof. exact (EQ_MP (@lem1560201 x y z) (@lem1560190 y z x)). Qed.
Lemma lem1560203 (y : real) (x : real) : (real_ge y x) = (term69 y x).
Proof. exact (@lem1483527 y x). Qed.
Lemma lem1560209 (y : real) (x : real) : (real_sub y x) = (term52 y x).
Proof. exact (@lem1483519 y x). Qed.
Lemma lem1560214 (x : real) (y : real) : (term52 y x) = (term53 x y).
Proof. exact (@lem1483488 (term45 x) y). Qed.
Lemma lem1560216 (x : real) (y : real) : (real_sub y x) = (term53 x y).
Proof. exact (TRANS (@lem1560209 y x) (@lem1560214 x y)). Qed.
Lemma lem1560217 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1560218 (x : real) (y : real) : (term70 y x) = (term186 x y).
Proof. exact (MK_COMB (@lem1560217) (@lem1560216 x y)). Qed.
Lemma lem1560219 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560220 (x : real) (y : real) : (term69 y x) = (term187 x y).
Proof. exact (MK_COMB (@lem1560218 x y) (@lem1560219)). Qed.
Lemma lem1560221 (x : real) (y : real) : (real_ge y x) = (term187 x y).
Proof. exact (TRANS (@lem1560203 y x) (@lem1560220 x y)). Qed.
Lemma lem1560222 (z : real) (y : real) : (term187 z y) = (term188 z y).
Proof. exact (@lem1483527 (term53 z y) term48). Qed.
Lemma lem1560223 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560236 (y : real) (z : real) : (term53 z y) = (term52 y z).
Proof. exact (@lem1483488 y (term45 z)). Qed.
Lemma lem1560237 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1560238 (y : real) (z : real) : (term189 z y) = (term190 y z).
Proof. exact (MK_COMB (@lem1560237) (@lem1560236 y z)). Qed.
Lemma lem1560239 (y : real) (z : real) : (term191 z y) = (term192 y z).
Proof. exact (MK_COMB (@lem1560238 y z) (@lem1560223)). Qed.
Lemma lem1560240 (y : real) (z : real) : (term192 y z) = (term193 y z).
Proof. exact (@lem1483519 (term52 y z) term48). Qed.
Lemma lem1560242 (x : nat) : (term194 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1560243 : term195 = term48.
Proof. exact (@lem1560242 term196). Qed.
Lemma lem1560244 (y : real) (z : real) : (term197 y z) = (term197 y z).
Proof. exact (eq_refl (term197 y z)). Qed.
Lemma lem1560245 (y : real) (z : real) : (term193 y z) = (term198 y z).
Proof. exact (MK_COMB (@lem1560244 y z) (@lem1560243)). Qed.
Lemma lem1560246 (y : real) (z : real) : (term198 y z) = (term52 y z).
Proof. exact (@lem1483450 (term52 y z)). Qed.
Lemma lem1560247 (y : real) (z : real) : (term193 y z) = (term52 y z).
Proof. exact (TRANS (@lem1560245 y z) (@lem1560246 y z)). Qed.
Lemma lem1560248 (y : real) (z : real) : (term192 y z) = (term52 y z).
Proof. exact (TRANS (@lem1560240 y z) (@lem1560247 y z)). Qed.
Lemma lem1560249 (y : real) (z : real) : (term191 z y) = (term52 y z).
Proof. exact (TRANS (@lem1560239 y z) (@lem1560248 y z)). Qed.
Lemma lem1560250 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1560251 (y : real) (z : real) : (term199 z y) = (term71 y z).
Proof. exact (MK_COMB (@lem1560250) (@lem1560249 y z)). Qed.
Lemma lem1560252 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560253 (y : real) (z : real) : (term188 z y) = (term72 y z).
Proof. exact (MK_COMB (@lem1560251 y z) (@lem1560252)). Qed.
Lemma lem1560254 (y : real) (z : real) : (term187 z y) = (term72 y z).
Proof. exact (TRANS (@lem1560222 z y) (@lem1560253 y z)). Qed.
Lemma lem1560255 (x : real) (z : real) : (term56 x z) = (term200 x z).
Proof. exact (@lem1483525 (term53 x z) term48). Qed.
Lemma lem1560273 (x : real) (z : real) : (term191 x z) = (term201 x z).
Proof. exact (@lem1483519 (term53 x z) term48). Qed.
Lemma lem1560275 (x : nat) : (term194 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1560276 : term195 = term48.
Proof. exact (@lem1560275 term196). Qed.
Lemma lem1560277 (x : real) (z : real) : (term202 x z) = (term202 x z).
Proof. exact (eq_refl (term202 x z)). Qed.
Lemma lem1560278 (x : real) (z : real) : (term201 x z) = (term203 x z).
Proof. exact (MK_COMB (@lem1560277 x z) (@lem1560276)). Qed.
Lemma lem1560279 (x : real) (z : real) : (term203 x z) = (term53 x z).
Proof. exact (@lem1483450 (term53 x z)). Qed.
Lemma lem1560280 (x : real) (z : real) : (term201 x z) = (term53 x z).
Proof. exact (TRANS (@lem1560278 x z) (@lem1560279 x z)). Qed.
Lemma lem1560282 (x : real) (z : real) : (term191 x z) = (term53 x z).
Proof. exact (TRANS (@lem1560273 x z) (@lem1560280 x z)). Qed.
Lemma lem1560283 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560284 (x : real) (z : real) : (term204 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1560283) (@lem1560282 x z)). Qed.
Lemma lem1560285 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560286 (x : real) (z : real) : (term200 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1560284 x z) (@lem1560285)). Qed.
Lemma lem1560287 (x : real) (z : real) : (term56 x z) = (term56 x z).
Proof. exact (TRANS (@lem1560255 x z) (@lem1560286 x z)). Qed.
Lemma lem1560288 (y : real) (z : real) : (term56 y z) = (term200 y z).
Proof. exact (@lem1483525 (term53 y z) term48). Qed.
Lemma lem1560306 (y : real) (z : real) : (term191 y z) = (term201 y z).
Proof. exact (@lem1483519 (term53 y z) term48). Qed.
Lemma lem1560308 (x : nat) : (term194 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1560309 : term195 = term48.
Proof. exact (@lem1560308 term196). Qed.
Lemma lem1560310 (y : real) (z : real) : (term202 y z) = (term202 y z).
Proof. exact (eq_refl (term202 y z)). Qed.
Lemma lem1560311 (y : real) (z : real) : (term201 y z) = (term203 y z).
Proof. exact (MK_COMB (@lem1560310 y z) (@lem1560309)). Qed.
Lemma lem1560312 (y : real) (z : real) : (term203 y z) = (term53 y z).
Proof. exact (@lem1483450 (term53 y z)). Qed.
Lemma lem1560313 (y : real) (z : real) : (term201 y z) = (term53 y z).
Proof. exact (TRANS (@lem1560311 y z) (@lem1560312 y z)). Qed.
Lemma lem1560315 (y : real) (z : real) : (term191 y z) = (term53 y z).
Proof. exact (TRANS (@lem1560306 y z) (@lem1560313 y z)). Qed.
Lemma lem1560316 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560317 (y : real) (z : real) : (term204 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1560316) (@lem1560315 y z)). Qed.
Lemma lem1560318 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560319 (y : real) (z : real) : (term200 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1560317 y z) (@lem1560318)). Qed.
Lemma lem1560320 (y : real) (z : real) : (term56 y z) = (term56 y z).
Proof. exact (TRANS (@lem1560288 y z) (@lem1560319 y z)). Qed.
Lemma lem1560321 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560322 (x : real) (z : real) : (term58 x z) = (term58 x z).
Proof. exact (MK_COMB (@lem1560321) (@lem1560287 x z)). Qed.
Lemma lem1560323 (x : real) (y : real) (z : real) : (term59 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1560322 x z) (@lem1560320 y z)). Qed.
Lemma lem1560324 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560325 (y : real) (z : real) : (term205 z y) = (term206 y z).
Proof. exact (MK_COMB (@lem1560324) (@lem1560254 y z)). Qed.
Lemma lem1560326 (x : real) (y : real) (z : real) : (term178 x y z) = (term207 x y z).
Proof. exact (MK_COMB (@lem1560325 y z) (@lem1560323 x y z)). Qed.
Lemma lem1560327 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560328 (x : real) (y : real) : (term179 y x) = (term205 x y).
Proof. exact (MK_COMB (@lem1560327) (@lem1560221 x y)). Qed.
Lemma lem1560329 (x : real) (y : real) (z : real) : (term181 x y z) = (term208 x y z).
Proof. exact (MK_COMB (@lem1560328 x y) (@lem1560326 x y z)). Qed.
Lemma lem1560330 (x : real) (y : real) : (real_gt x y) = (term51 x y).
Proof. exact (@lem1483525 x y). Qed.
Lemma lem1560343 (x : real) (y : real) : (real_sub x y) = (term52 x y).
Proof. exact (@lem1483519 x y). Qed.
Lemma lem1560344 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560345 (x : real) (y : real) : (term54 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem1560344) (@lem1560343 x y)). Qed.
Lemma lem1560346 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560347 (x : real) (y : real) : (term51 x y) = (term210 x y).
Proof. exact (MK_COMB (@lem1560345 x y) (@lem1560346)). Qed.
Lemma lem1560348 (x : real) (y : real) : (real_gt x y) = (term210 x y).
Proof. exact (TRANS (@lem1560330 x y) (@lem1560347 x y)). Qed.
Lemma lem1560349 (z : real) (x : real) : (term187 z x) = (term188 z x).
Proof. exact (@lem1483527 (term53 z x) term48). Qed.
Lemma lem1560350 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560363 (x : real) (z : real) : (term53 z x) = (term52 x z).
Proof. exact (@lem1483488 x (term45 z)). Qed.
Lemma lem1560364 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1560365 (x : real) (z : real) : (term189 z x) = (term190 x z).
Proof. exact (MK_COMB (@lem1560364) (@lem1560363 x z)). Qed.
Lemma lem1560366 (x : real) (z : real) : (term191 z x) = (term192 x z).
Proof. exact (MK_COMB (@lem1560365 x z) (@lem1560350)). Qed.
Lemma lem1560367 (x : real) (z : real) : (term192 x z) = (term193 x z).
Proof. exact (@lem1483519 (term52 x z) term48). Qed.
Lemma lem1560369 (x : nat) : (term194 x) = term48.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1560370 : term195 = term48.
Proof. exact (@lem1560369 term196). Qed.
Lemma lem1560371 (x : real) (z : real) : (term197 x z) = (term197 x z).
Proof. exact (eq_refl (term197 x z)). Qed.
Lemma lem1560372 (x : real) (z : real) : (term193 x z) = (term198 x z).
Proof. exact (MK_COMB (@lem1560371 x z) (@lem1560370)). Qed.
Lemma lem1560373 (x : real) (z : real) : (term198 x z) = (term52 x z).
Proof. exact (@lem1483450 (term52 x z)). Qed.
Lemma lem1560374 (x : real) (z : real) : (term193 x z) = (term52 x z).
Proof. exact (TRANS (@lem1560372 x z) (@lem1560373 x z)). Qed.
Lemma lem1560375 (x : real) (z : real) : (term192 x z) = (term52 x z).
Proof. exact (TRANS (@lem1560367 x z) (@lem1560374 x z)). Qed.
Lemma lem1560376 (x : real) (z : real) : (term191 z x) = (term52 x z).
Proof. exact (TRANS (@lem1560366 x z) (@lem1560375 x z)). Qed.
Lemma lem1560377 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1560378 (x : real) (z : real) : (term199 z x) = (term71 x z).
Proof. exact (MK_COMB (@lem1560377) (@lem1560376 x z)). Qed.
Lemma lem1560379 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560380 (x : real) (z : real) : (term188 z x) = (term72 x z).
Proof. exact (MK_COMB (@lem1560378 x z) (@lem1560379)). Qed.
Lemma lem1560381 (x : real) (z : real) : (term187 z x) = (term72 x z).
Proof. exact (TRANS (@lem1560349 z x) (@lem1560380 x z)). Qed.
Lemma lem1560382 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560383 (x : real) (z : real) : (term58 x z) = (term58 x z).
Proof. exact (MK_COMB (@lem1560382) (@lem1560287 x z)). Qed.
Lemma lem1560384 (x : real) (y : real) (z : real) : (term59 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem1560383 x z) (@lem1560320 y z)). Qed.
Lemma lem1560385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560386 (x : real) (z : real) : (term205 z x) = (term206 x z).
Proof. exact (MK_COMB (@lem1560385) (@lem1560381 x z)). Qed.
Lemma lem1560387 (x : real) (y : real) (z : real) : (term173 x y z) = (term211 x y z).
Proof. exact (MK_COMB (@lem1560386 x z) (@lem1560384 x y z)). Qed.
Lemma lem1560388 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560389 (x : real) (y : real) : (term174 x y) = (term212 x y).
Proof. exact (MK_COMB (@lem1560388) (@lem1560348 x y)). Qed.
Lemma lem1560390 (x : real) (y : real) (z : real) : (term176 x y z) = (term213 x y z).
Proof. exact (MK_COMB (@lem1560389 x y) (@lem1560387 x y z)). Qed.
Lemma lem1560391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560392 (x : real) (y : real) (z : real) : (term183 x y z) = (term214 x y z).
Proof. exact (MK_COMB (@lem1560391) (@lem1560329 x y z)). Qed.
Lemma lem1560393 (x : real) (y : real) (z : real) : (term184 x y z) = (term215 x y z).
Proof. exact (MK_COMB (@lem1560392 x y z) (@lem1560390 x y z)). Qed.
Lemma lem1560405 (x : real) (y : real) (z : real) : (term61 x y z) = (term215 x y z).
Proof. exact (TRANS (@lem1560202 x y z) (@lem1560393 x y z)). Qed.
Lemma lem1560407 (x : real) (a : real) (y : real) (r : real) : (term216 a x y r) = (term217 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1560408 (x : real) (z : real) (y : real) : (term68 z x y) = (term218 x z y).
Proof. exact (@lem1560407 x z y term48). Qed.
Lemma lem1560421 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1560422 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560423 (y : real) (z : real) : (term209 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1560422) (@lem1560421 y z)). Qed.
Lemma lem1560424 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560425 (y : real) (z : real) : (term210 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1560423 y z) (@lem1560424)). Qed.
Lemma lem1560438 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1560439 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560440 (x : real) (z : real) : (term209 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1560439) (@lem1560438 x z)). Qed.
Lemma lem1560441 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560442 (x : real) (z : real) : (term210 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1560440 x z) (@lem1560441)). Qed.
Lemma lem1560443 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560444 (x : real) (z : real) : (term212 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1560443) (@lem1560442 x z)). Qed.
Lemma lem1560445 (x : real) (y : real) (z : real) : (term218 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1560444 x z) (@lem1560425 y z)). Qed.
Lemma lem1560446 (x : real) (y : real) (z : real) : (term68 z x y) = (term59 x y z).
Proof. exact (TRANS (@lem1560408 x z y) (@lem1560445 x y z)). Qed.
Lemma lem1560447 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560448 (x : real) (y : real) (z : real) : (term77 z x y) = (term219 x y z).
Proof. exact (MK_COMB (@lem1560447) (@lem1560446 x y z)). Qed.
Lemma lem1560449 (x : real) (z : real) : (term72 x z) = (term72 x z).
Proof. exact (eq_refl (term72 x z)). Qed.
Lemma lem1560452 (y : real) (x : real) (z : real) : (term220 y x z) = (term221 y x z).
Proof. exact (MK_COMB (@lem1560448 x y z) (@lem1560449 x z)). Qed.
Lemma lem1560454 (x : real) (a : real) (y : real) (r : real) : (term216 a x y r) = (term217 x a y r).
Proof. exact (proj1 (@lem1482710 x a (@el real) y (@el real) r)). Qed.
Lemma lem1560455 (x : real) (z : real) (y : real) : (term68 z x y) = (term218 x z y).
Proof. exact (@lem1560454 x z y term48). Qed.
Lemma lem1560468 (y : real) (z : real) : (term52 z y) = (term53 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1560469 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560470 (y : real) (z : real) : (term209 z y) = (term55 y z).
Proof. exact (MK_COMB (@lem1560469) (@lem1560468 y z)). Qed.
Lemma lem1560471 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560472 (y : real) (z : real) : (term210 z y) = (term56 y z).
Proof. exact (MK_COMB (@lem1560470 y z) (@lem1560471)). Qed.
Lemma lem1560485 (x : real) (z : real) : (term52 z x) = (term53 x z).
Proof. exact (@lem1483488 (term45 x) z). Qed.
Lemma lem1560486 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560487 (x : real) (z : real) : (term209 z x) = (term55 x z).
Proof. exact (MK_COMB (@lem1560486) (@lem1560485 x z)). Qed.
Lemma lem1560488 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560489 (x : real) (z : real) : (term210 z x) = (term56 x z).
Proof. exact (MK_COMB (@lem1560487 x z) (@lem1560488)). Qed.
Lemma lem1560490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560491 (x : real) (z : real) : (term212 z x) = (term58 x z).
Proof. exact (MK_COMB (@lem1560490) (@lem1560489 x z)). Qed.
Lemma lem1560492 (x : real) (y : real) (z : real) : (term218 x z y) = (term59 x y z).
Proof. exact (MK_COMB (@lem1560491 x z) (@lem1560472 y z)). Qed.
Lemma lem1560493 (x : real) (y : real) (z : real) : (term68 z x y) = (term59 x y z).
Proof. exact (TRANS (@lem1560455 x z y) (@lem1560492 x y z)). Qed.
Lemma lem1560494 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1560495 (x : real) (y : real) (z : real) : (term77 z x y) = (term219 x y z).
Proof. exact (MK_COMB (@lem1560494) (@lem1560493 x y z)). Qed.
Lemma lem1560496 (y : real) (z : real) : (term72 y z) = (term72 y z).
Proof. exact (eq_refl (term72 y z)). Qed.
Lemma lem1560499 (x : real) (y : real) (z : real) : (term222 x y z) = (term223 x y z).
Proof. exact (MK_COMB (@lem1560495 x y z) (@lem1560496 y z)). Qed.
Lemma lem1560500 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560501 (y : real) (x : real) (z : real) : (term224 y x z) = (term225 y x z).
Proof. exact (MK_COMB (@lem1560500) (@lem1560452 y x z)). Qed.
Lemma lem1560502 (x : real) (y : real) (z : real) : (term161 x y z) = (term226 x y z).
Proof. exact (MK_COMB (@lem1560501 y x z) (@lem1560499 x y z)). Qed.
Lemma lem1560503 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1560504 (x : real) (y : real) (z : real) : (term79 x y z) = (term227 x y z).
Proof. exact (MK_COMB (@lem1560503) (@lem1560405 x y z)). Qed.
Lemma lem1560505 (x : real) (y : real) (z : real) : (term162 x y z) = (term228 x y z).
Proof. exact (MK_COMB (@lem1560504 x y z) (@lem1560502 x y z)). Qed.
Lemma lem1560506 (x : real) (y : real) (z : real) (h1 : term228 x y z) : term228 x y z.
Proof. exact (h1). Qed.
Lemma lem1560507 (x : real) (y : real) (z : real) (h1 : term215 x y z) : term215 x y z.
Proof. exact (h1). Qed.
Lemma lem1560508 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term208 x y z.
Proof. exact (h1). Qed.
Lemma lem1560509 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term207 x y z.
Proof. exact (proj2 (@lem1560508 x y z h1)). Qed.
Lemma lem1560511 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term59 x y z.
Proof. exact (proj2 (@lem1560509 x y z h1)). Qed.
Lemma lem1560512 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term72 y z.
Proof. exact (proj1 (@lem1560509 x y z h1)). Qed.
Lemma lem1560513 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term56 y z.
Proof. exact (proj2 (@lem1560511 x y z h1)). Qed.
Lemma lem1560516 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560517 : term230 = term231.
Proof. exact (@lem1560516 (NUMERAL 0) term196). Qed.
Lemma lem1560518 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560519 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560520 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560519 h1) (fun h1 : term231 = True => @lem1560518)). Qed.
Lemma lem1560521 : term231 = True.
Proof. exact (EQ_MP (@lem1560520) (@lem1560518)). Qed.
Lemma lem1560522 : term230 = True.
Proof. exact (TRANS (@lem1560517) (@lem1560521)). Qed.
Lemma lem1560523 : True = term230.
Proof. exact (SYM (@lem1560522)). Qed.
Lemma lem1560524 : term230.
Proof. exact (EQ_MP (@lem1560523) (@lem0)). Qed.
Lemma lem1560525 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term233 y z.
Proof. exact (conj (@lem1560524) (@lem1560512 x y z h1)). Qed.
Lemma lem1560527 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1560528 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1560527 term236 (term52 y z)). Qed.
Lemma lem1560529 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term237 y z.
Proof. exact (@lem1560528 y z (@lem1560525 x y z h1)). Qed.
Lemma lem1560530 (y : real) (z : real) : (term238 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1560531 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1560532 (y : real) (z : real) : (term239 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1560531) (@lem1560530 y z)). Qed.
Lemma lem1560533 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560534 (y : real) (z : real) : (term237 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1560532 y z) (@lem1560533)). Qed.
Lemma lem1560535 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1560534 y z) (@lem1560529 x y z h1)). Qed.
Lemma lem1560537 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560538 : term230 = term231.
Proof. exact (@lem1560537 (NUMERAL 0) term196). Qed.
Lemma lem1560539 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560540 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560541 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560540 h1) (fun h1 : term231 = True => @lem1560539)). Qed.
Lemma lem1560542 : term231 = True.
Proof. exact (EQ_MP (@lem1560541) (@lem1560539)). Qed.
Lemma lem1560543 : term230 = True.
Proof. exact (TRANS (@lem1560538) (@lem1560542)). Qed.
Lemma lem1560544 : True = term230.
Proof. exact (SYM (@lem1560543)). Qed.
Lemma lem1560545 : term230.
Proof. exact (EQ_MP (@lem1560544) (@lem0)). Qed.
Lemma lem1560546 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term240 y z.
Proof. exact (conj (@lem1560545) (@lem1560513 x y z h1)). Qed.
Lemma lem1560548 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1560549 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1560548 term236 (term53 y z)). Qed.
Lemma lem1560550 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term243 y z.
Proof. exact (@lem1560549 y z (@lem1560546 x y z h1)). Qed.
Lemma lem1560551 (y : real) (z : real) : (term244 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1560552 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560553 (y : real) (z : real) : (term245 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1560552) (@lem1560551 y z)). Qed.
Lemma lem1560554 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560555 (y : real) (z : real) : (term243 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1560553 y z) (@lem1560554)). Qed.
Lemma lem1560556 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1560555 y z) (@lem1560550 x y z h1)). Qed.
Lemma lem1560557 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term246 y z.
Proof. exact (conj (@lem1560556 x y z h1) (@lem1560535 x y z h1)). Qed.
Lemma lem1560559 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1560560 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1560559 (term53 y z) (term52 y z)). Qed.
Lemma lem1560561 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term249 y z.
Proof. exact (@lem1560560 y z (@lem1560557 x y z h1)). Qed.
Lemma lem1560562 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 (term45 y) y z (term45 z)). Qed.
Lemma lem1560563 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483440 term254 y). Qed.
Lemma lem1560565 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560566 : term256 = term48.
Proof. exact (@lem1560565 term196). Qed.
Lemma lem1560567 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560568 : term257 = term258.
Proof. exact (MK_COMB (@lem1560567) (@lem1560566)). Qed.
Lemma lem1560569 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1560570 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1560568) (@lem1560569 y)). Qed.
Lemma lem1560571 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1560563 y) (@lem1560570 y)). Qed.
Lemma lem1560572 (y : real) : (term259 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1560573 (y : real) : (term252 y) = term48.
Proof. exact (TRANS (@lem1560571 y) (@lem1560572 y)). Qed.
Lemma lem1560574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1560575 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1560574) (@lem1560573 y)). Qed.
Lemma lem1560576 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1560578 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560579 : term256 = term48.
Proof. exact (@lem1560578 term196). Qed.
Lemma lem1560580 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560581 : term257 = term258.
Proof. exact (MK_COMB (@lem1560580) (@lem1560579)). Qed.
Lemma lem1560582 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1560583 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1560581) (@lem1560582 z)). Qed.
Lemma lem1560584 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1560576 z) (@lem1560583 z)). Qed.
Lemma lem1560585 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1560586 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1560584 z) (@lem1560585 z)). Qed.
Lemma lem1560587 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1560575 y) (@lem1560586 z)). Qed.
Lemma lem1560588 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1560562 y z) (@lem1560587 y z)). Qed.
Lemma lem1560589 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1560590 (y : real) (z : real) : (term250 y z) = term48.
Proof. exact (TRANS (@lem1560588 y z) (@lem1560589)). Qed.
Lemma lem1560591 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560592 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1560591) (@lem1560590 y z)). Qed.
Lemma lem1560593 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560594 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1560592 y z) (@lem1560593)). Qed.
Lemma lem1560595 (x : real) (y : real) (z : real) (h1 : term208 x y z) : term266.
Proof. exact (EQ_MP (@lem1560594 y z) (@lem1560561 x y z h1)). Qed.
Lemma lem1560597 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560598 : term266 = term267.
Proof. exact (@lem1560597 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1560599 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1560600 : term266 = False.
Proof. exact (TRANS (@lem1560598) (@lem1560599)). Qed.
Lemma lem1560601 (x : real) (y : real) (z : real) (h1 : term208 x y z) : False.
Proof. exact (EQ_MP (@lem1560600) (@lem1560595 x y z h1)). Qed.
Lemma lem1560602 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term213 x y z.
Proof. exact (h1). Qed.
Lemma lem1560603 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term211 x y z.
Proof. exact (proj2 (@lem1560602 x y z h1)). Qed.
Lemma lem1560605 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term59 x y z.
Proof. exact (proj2 (@lem1560603 x y z h1)). Qed.
Lemma lem1560606 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term72 x z.
Proof. exact (proj1 (@lem1560603 x y z h1)). Qed.
Lemma lem1560608 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term56 x z.
Proof. exact (proj1 (@lem1560605 x y z h1)). Qed.
Lemma lem1560610 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560611 : term230 = term231.
Proof. exact (@lem1560610 (NUMERAL 0) term196). Qed.
Lemma lem1560612 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560613 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560614 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560613 h1) (fun h1 : term231 = True => @lem1560612)). Qed.
Lemma lem1560615 : term231 = True.
Proof. exact (EQ_MP (@lem1560614) (@lem1560612)). Qed.
Lemma lem1560616 : term230 = True.
Proof. exact (TRANS (@lem1560611) (@lem1560615)). Qed.
Lemma lem1560617 : True = term230.
Proof. exact (SYM (@lem1560616)). Qed.
Lemma lem1560618 : term230.
Proof. exact (EQ_MP (@lem1560617) (@lem0)). Qed.
Lemma lem1560619 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term233 x z.
Proof. exact (conj (@lem1560618) (@lem1560606 x y z h1)). Qed.
Lemma lem1560621 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1560622 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1560621 term236 (term52 x z)). Qed.
Lemma lem1560623 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term237 x z.
Proof. exact (@lem1560622 x z (@lem1560619 x y z h1)). Qed.
Lemma lem1560624 (x : real) (z : real) : (term238 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1560625 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1560626 (x : real) (z : real) : (term239 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1560625) (@lem1560624 x z)). Qed.
Lemma lem1560627 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560628 (x : real) (z : real) : (term237 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1560626 x z) (@lem1560627)). Qed.
Lemma lem1560629 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term72 x z.
Proof. exact (EQ_MP (@lem1560628 x z) (@lem1560623 x y z h1)). Qed.
Lemma lem1560631 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560632 : term230 = term231.
Proof. exact (@lem1560631 (NUMERAL 0) term196). Qed.
Lemma lem1560633 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560634 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560635 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560634 h1) (fun h1 : term231 = True => @lem1560633)). Qed.
Lemma lem1560636 : term231 = True.
Proof. exact (EQ_MP (@lem1560635) (@lem1560633)). Qed.
Lemma lem1560637 : term230 = True.
Proof. exact (TRANS (@lem1560632) (@lem1560636)). Qed.
Lemma lem1560638 : True = term230.
Proof. exact (SYM (@lem1560637)). Qed.
Lemma lem1560639 : term230.
Proof. exact (EQ_MP (@lem1560638) (@lem0)). Qed.
Lemma lem1560640 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term240 x z.
Proof. exact (conj (@lem1560639) (@lem1560608 x y z h1)). Qed.
Lemma lem1560642 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1560643 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1560642 term236 (term53 x z)). Qed.
Lemma lem1560644 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term243 x z.
Proof. exact (@lem1560643 x z (@lem1560640 x y z h1)). Qed.
Lemma lem1560645 (x : real) (z : real) : (term244 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1560646 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560647 (x : real) (z : real) : (term245 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1560646) (@lem1560645 x z)). Qed.
Lemma lem1560648 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560649 (x : real) (z : real) : (term243 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1560647 x z) (@lem1560648)). Qed.
Lemma lem1560650 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term56 x z.
Proof. exact (EQ_MP (@lem1560649 x z) (@lem1560644 x y z h1)). Qed.
Lemma lem1560651 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term246 x z.
Proof. exact (conj (@lem1560650 x y z h1) (@lem1560629 x y z h1)). Qed.
Lemma lem1560653 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1560654 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1560653 (term53 x z) (term52 x z)). Qed.
Lemma lem1560655 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term249 x z.
Proof. exact (@lem1560654 x z (@lem1560651 x y z h1)). Qed.
Lemma lem1560656 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 (term45 x) x z (term45 z)). Qed.
Lemma lem1560657 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483440 term254 x). Qed.
Lemma lem1560659 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560660 : term256 = term48.
Proof. exact (@lem1560659 term196). Qed.
Lemma lem1560661 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560662 : term257 = term258.
Proof. exact (MK_COMB (@lem1560661) (@lem1560660)). Qed.
Lemma lem1560663 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1560664 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1560662) (@lem1560663 x)). Qed.
Lemma lem1560665 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1560657 x) (@lem1560664 x)). Qed.
Lemma lem1560666 (x : real) : (term259 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1560667 (x : real) : (term252 x) = term48.
Proof. exact (TRANS (@lem1560665 x) (@lem1560666 x)). Qed.
Lemma lem1560668 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1560669 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1560668) (@lem1560667 x)). Qed.
Lemma lem1560670 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1560672 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560673 : term256 = term48.
Proof. exact (@lem1560672 term196). Qed.
Lemma lem1560674 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560675 : term257 = term258.
Proof. exact (MK_COMB (@lem1560674) (@lem1560673)). Qed.
Lemma lem1560676 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1560677 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1560675) (@lem1560676 z)). Qed.
Lemma lem1560678 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1560670 z) (@lem1560677 z)). Qed.
Lemma lem1560679 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1560680 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1560678 z) (@lem1560679 z)). Qed.
Lemma lem1560681 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1560669 x) (@lem1560680 z)). Qed.
Lemma lem1560682 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1560656 x z) (@lem1560681 x z)). Qed.
Lemma lem1560683 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1560684 (x : real) (z : real) : (term250 x z) = term48.
Proof. exact (TRANS (@lem1560682 x z) (@lem1560683)). Qed.
Lemma lem1560685 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560686 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1560685) (@lem1560684 x z)). Qed.
Lemma lem1560687 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560688 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1560686 x z) (@lem1560687)). Qed.
Lemma lem1560689 (x : real) (y : real) (z : real) (h1 : term213 x y z) : term266.
Proof. exact (EQ_MP (@lem1560688 x z) (@lem1560655 x y z h1)). Qed.
Lemma lem1560691 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560692 : term266 = term267.
Proof. exact (@lem1560691 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1560693 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1560694 : term266 = False.
Proof. exact (TRANS (@lem1560692) (@lem1560693)). Qed.
Lemma lem1560695 (x : real) (y : real) (z : real) (h1 : term213 x y z) : False.
Proof. exact (EQ_MP (@lem1560694) (@lem1560689 x y z h1)). Qed.
Lemma lem1560696 (x : real) (y : real) (z : real) (h1 : term215 x y z) : False.
Proof. exact (or_elim (@lem1560507 x y z h1) (fun h0 : term208 x y z => @lem1560601 x y z h0) (fun h0 : term213 x y z => @lem1560695 x y z h0)). Qed.
Lemma lem1560697 (x : real) (y : real) (z : real) (h1 : term226 x y z) : term226 x y z.
Proof. exact (h1). Qed.
Lemma lem1560698 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term221 y x z.
Proof. exact (h1). Qed.
Lemma lem1560699 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term72 x z.
Proof. exact (proj2 (@lem1560698 y x z h1)). Qed.
Lemma lem1560700 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term59 x y z.
Proof. exact (proj1 (@lem1560698 y x z h1)). Qed.
Lemma lem1560702 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term56 x z.
Proof. exact (proj1 (@lem1560700 y x z h1)). Qed.
Lemma lem1560704 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560705 : term230 = term231.
Proof. exact (@lem1560704 (NUMERAL 0) term196). Qed.
Lemma lem1560706 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560707 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560708 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560707 h1) (fun h1 : term231 = True => @lem1560706)). Qed.
Lemma lem1560709 : term231 = True.
Proof. exact (EQ_MP (@lem1560708) (@lem1560706)). Qed.
Lemma lem1560710 : term230 = True.
Proof. exact (TRANS (@lem1560705) (@lem1560709)). Qed.
Lemma lem1560711 : True = term230.
Proof. exact (SYM (@lem1560710)). Qed.
Lemma lem1560712 : term230.
Proof. exact (EQ_MP (@lem1560711) (@lem0)). Qed.
Lemma lem1560713 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term233 x z.
Proof. exact (conj (@lem1560712) (@lem1560699 y x z h1)). Qed.
Lemma lem1560715 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1560716 (x : real) (z : real) : term235 x z.
Proof. exact (@lem1560715 term236 (term52 x z)). Qed.
Lemma lem1560717 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term237 x z.
Proof. exact (@lem1560716 x z (@lem1560713 y x z h1)). Qed.
Lemma lem1560718 (x : real) (z : real) : (term238 x z) = (term52 x z).
Proof. exact (@lem1483460 (term52 x z)). Qed.
Lemma lem1560719 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1560720 (x : real) (z : real) : (term239 x z) = (term71 x z).
Proof. exact (MK_COMB (@lem1560719) (@lem1560718 x z)). Qed.
Lemma lem1560721 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560722 (x : real) (z : real) : (term237 x z) = (term72 x z).
Proof. exact (MK_COMB (@lem1560720 x z) (@lem1560721)). Qed.
Lemma lem1560723 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term72 x z.
Proof. exact (EQ_MP (@lem1560722 x z) (@lem1560717 y x z h1)). Qed.
Lemma lem1560725 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560726 : term230 = term231.
Proof. exact (@lem1560725 (NUMERAL 0) term196). Qed.
Lemma lem1560727 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560728 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560729 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560728 h1) (fun h1 : term231 = True => @lem1560727)). Qed.
Lemma lem1560730 : term231 = True.
Proof. exact (EQ_MP (@lem1560729) (@lem1560727)). Qed.
Lemma lem1560731 : term230 = True.
Proof. exact (TRANS (@lem1560726) (@lem1560730)). Qed.
Lemma lem1560732 : True = term230.
Proof. exact (SYM (@lem1560731)). Qed.
Lemma lem1560733 : term230.
Proof. exact (EQ_MP (@lem1560732) (@lem0)). Qed.
Lemma lem1560734 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term240 x z.
Proof. exact (conj (@lem1560733) (@lem1560702 y x z h1)). Qed.
Lemma lem1560736 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1560737 (x : real) (z : real) : term242 x z.
Proof. exact (@lem1560736 term236 (term53 x z)). Qed.
Lemma lem1560738 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term243 x z.
Proof. exact (@lem1560737 x z (@lem1560734 y x z h1)). Qed.
Lemma lem1560739 (x : real) (z : real) : (term244 x z) = (term53 x z).
Proof. exact (@lem1483460 (term53 x z)). Qed.
Lemma lem1560740 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560741 (x : real) (z : real) : (term245 x z) = (term55 x z).
Proof. exact (MK_COMB (@lem1560740) (@lem1560739 x z)). Qed.
Lemma lem1560742 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560743 (x : real) (z : real) : (term243 x z) = (term56 x z).
Proof. exact (MK_COMB (@lem1560741 x z) (@lem1560742)). Qed.
Lemma lem1560744 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term56 x z.
Proof. exact (EQ_MP (@lem1560743 x z) (@lem1560738 y x z h1)). Qed.
Lemma lem1560745 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term246 x z.
Proof. exact (conj (@lem1560744 y x z h1) (@lem1560723 y x z h1)). Qed.
Lemma lem1560747 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1560748 (x : real) (z : real) : term248 x z.
Proof. exact (@lem1560747 (term53 x z) (term52 x z)). Qed.
Lemma lem1560749 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term249 x z.
Proof. exact (@lem1560748 x z (@lem1560745 y x z h1)). Qed.
Lemma lem1560750 (x : real) (z : real) : (term250 x z) = (term251 x z).
Proof. exact (@lem1483480 (term45 x) x z (term45 z)). Qed.
Lemma lem1560751 (x : real) : (term252 x) = (term253 x).
Proof. exact (@lem1483440 term254 x). Qed.
Lemma lem1560753 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560754 : term256 = term48.
Proof. exact (@lem1560753 term196). Qed.
Lemma lem1560755 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560756 : term257 = term258.
Proof. exact (MK_COMB (@lem1560755) (@lem1560754)). Qed.
Lemma lem1560757 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1560758 (x : real) : (term253 x) = (term259 x).
Proof. exact (MK_COMB (@lem1560756) (@lem1560757 x)). Qed.
Lemma lem1560759 (x : real) : (term252 x) = (term259 x).
Proof. exact (TRANS (@lem1560751 x) (@lem1560758 x)). Qed.
Lemma lem1560760 (x : real) : (term259 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1560761 (x : real) : (term252 x) = term48.
Proof. exact (TRANS (@lem1560759 x) (@lem1560760 x)). Qed.
Lemma lem1560762 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1560763 (x : real) : (term260 x) = term261.
Proof. exact (MK_COMB (@lem1560762) (@lem1560761 x)). Qed.
Lemma lem1560764 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1560766 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560767 : term256 = term48.
Proof. exact (@lem1560766 term196). Qed.
Lemma lem1560768 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560769 : term257 = term258.
Proof. exact (MK_COMB (@lem1560768) (@lem1560767)). Qed.
Lemma lem1560770 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1560771 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1560769) (@lem1560770 z)). Qed.
Lemma lem1560772 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1560764 z) (@lem1560771 z)). Qed.
Lemma lem1560773 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1560774 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1560772 z) (@lem1560773 z)). Qed.
Lemma lem1560775 (x : real) (z : real) : (term251 x z) = term263.
Proof. exact (MK_COMB (@lem1560763 x) (@lem1560774 z)). Qed.
Lemma lem1560776 (x : real) (z : real) : (term250 x z) = term263.
Proof. exact (TRANS (@lem1560750 x z) (@lem1560775 x z)). Qed.
Lemma lem1560777 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1560778 (x : real) (z : real) : (term250 x z) = term48.
Proof. exact (TRANS (@lem1560776 x z) (@lem1560777)). Qed.
Lemma lem1560779 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560780 (x : real) (z : real) : (term264 x z) = term265.
Proof. exact (MK_COMB (@lem1560779) (@lem1560778 x z)). Qed.
Lemma lem1560781 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560782 (x : real) (z : real) : (term249 x z) = term266.
Proof. exact (MK_COMB (@lem1560780 x z) (@lem1560781)). Qed.
Lemma lem1560783 (y : real) (x : real) (z : real) (h1 : term221 y x z) : term266.
Proof. exact (EQ_MP (@lem1560782 x z) (@lem1560749 y x z h1)). Qed.
Lemma lem1560785 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560786 : term266 = term267.
Proof. exact (@lem1560785 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1560787 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1560788 : term266 = False.
Proof. exact (TRANS (@lem1560786) (@lem1560787)). Qed.
Lemma lem1560789 (y : real) (x : real) (z : real) (h1 : term221 y x z) : False.
Proof. exact (EQ_MP (@lem1560788) (@lem1560783 y x z h1)). Qed.
Lemma lem1560790 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term223 x y z.
Proof. exact (h1). Qed.
Lemma lem1560791 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term72 y z.
Proof. exact (proj2 (@lem1560790 x y z h1)). Qed.
Lemma lem1560792 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term59 x y z.
Proof. exact (proj1 (@lem1560790 x y z h1)). Qed.
Lemma lem1560793 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term56 y z.
Proof. exact (proj2 (@lem1560792 x y z h1)). Qed.
Lemma lem1560796 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560797 : term230 = term231.
Proof. exact (@lem1560796 (NUMERAL 0) term196). Qed.
Lemma lem1560798 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560799 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560800 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560799 h1) (fun h1 : term231 = True => @lem1560798)). Qed.
Lemma lem1560801 : term231 = True.
Proof. exact (EQ_MP (@lem1560800) (@lem1560798)). Qed.
Lemma lem1560802 : term230 = True.
Proof. exact (TRANS (@lem1560797) (@lem1560801)). Qed.
Lemma lem1560803 : True = term230.
Proof. exact (SYM (@lem1560802)). Qed.
Lemma lem1560804 : term230.
Proof. exact (EQ_MP (@lem1560803) (@lem0)). Qed.
Lemma lem1560805 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term233 y z.
Proof. exact (conj (@lem1560804) (@lem1560791 x y z h1)). Qed.
Lemma lem1560807 (x : real) (y : real) : term234 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1560808 (y : real) (z : real) : term235 y z.
Proof. exact (@lem1560807 term236 (term52 y z)). Qed.
Lemma lem1560809 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term237 y z.
Proof. exact (@lem1560808 y z (@lem1560805 x y z h1)). Qed.
Lemma lem1560810 (y : real) (z : real) : (term238 y z) = (term52 y z).
Proof. exact (@lem1483460 (term52 y z)). Qed.
Lemma lem1560811 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1560812 (y : real) (z : real) : (term239 y z) = (term71 y z).
Proof. exact (MK_COMB (@lem1560811) (@lem1560810 y z)). Qed.
Lemma lem1560813 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560814 (y : real) (z : real) : (term237 y z) = (term72 y z).
Proof. exact (MK_COMB (@lem1560812 y z) (@lem1560813)). Qed.
Lemma lem1560815 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term72 y z.
Proof. exact (EQ_MP (@lem1560814 y z) (@lem1560809 x y z h1)). Qed.
Lemma lem1560817 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560818 : term230 = term231.
Proof. exact (@lem1560817 (NUMERAL 0) term196). Qed.
Lemma lem1560819 : term232 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1560820 (h1 : term232 = (BIT1 0)) : term231 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1560821 : (term232 = (BIT1 0)) = (term231 = True).
Proof. exact (prop_ext (fun h1 : term232 = (BIT1 0) => @lem1560820 h1) (fun h1 : term231 = True => @lem1560819)). Qed.
Lemma lem1560822 : term231 = True.
Proof. exact (EQ_MP (@lem1560821) (@lem1560819)). Qed.
Lemma lem1560823 : term230 = True.
Proof. exact (TRANS (@lem1560818) (@lem1560822)). Qed.
Lemma lem1560824 : True = term230.
Proof. exact (SYM (@lem1560823)). Qed.
Lemma lem1560825 : term230.
Proof. exact (EQ_MP (@lem1560824) (@lem0)). Qed.
Lemma lem1560826 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term240 y z.
Proof. exact (conj (@lem1560825) (@lem1560793 x y z h1)). Qed.
Lemma lem1560828 (x : real) (y : real) : term241 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1560829 (y : real) (z : real) : term242 y z.
Proof. exact (@lem1560828 term236 (term53 y z)). Qed.
Lemma lem1560830 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term243 y z.
Proof. exact (@lem1560829 y z (@lem1560826 x y z h1)). Qed.
Lemma lem1560831 (y : real) (z : real) : (term244 y z) = (term53 y z).
Proof. exact (@lem1483460 (term53 y z)). Qed.
Lemma lem1560832 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560833 (y : real) (z : real) : (term245 y z) = (term55 y z).
Proof. exact (MK_COMB (@lem1560832) (@lem1560831 y z)). Qed.
Lemma lem1560834 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560835 (y : real) (z : real) : (term243 y z) = (term56 y z).
Proof. exact (MK_COMB (@lem1560833 y z) (@lem1560834)). Qed.
Lemma lem1560836 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term56 y z.
Proof. exact (EQ_MP (@lem1560835 y z) (@lem1560830 x y z h1)). Qed.
Lemma lem1560837 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term246 y z.
Proof. exact (conj (@lem1560836 x y z h1) (@lem1560815 x y z h1)). Qed.
Lemma lem1560839 (x : real) (y : real) : term247 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1560840 (y : real) (z : real) : term248 y z.
Proof. exact (@lem1560839 (term53 y z) (term52 y z)). Qed.
Lemma lem1560841 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term249 y z.
Proof. exact (@lem1560840 y z (@lem1560837 x y z h1)). Qed.
Lemma lem1560842 (y : real) (z : real) : (term250 y z) = (term251 y z).
Proof. exact (@lem1483480 (term45 y) y z (term45 z)). Qed.
Lemma lem1560843 (y : real) : (term252 y) = (term253 y).
Proof. exact (@lem1483440 term254 y). Qed.
Lemma lem1560845 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560846 : term256 = term48.
Proof. exact (@lem1560845 term196). Qed.
Lemma lem1560847 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560848 : term257 = term258.
Proof. exact (MK_COMB (@lem1560847) (@lem1560846)). Qed.
Lemma lem1560849 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1560850 (y : real) : (term253 y) = (term259 y).
Proof. exact (MK_COMB (@lem1560848) (@lem1560849 y)). Qed.
Lemma lem1560851 (y : real) : (term252 y) = (term259 y).
Proof. exact (TRANS (@lem1560843 y) (@lem1560850 y)). Qed.
Lemma lem1560852 (y : real) : (term259 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1560853 (y : real) : (term252 y) = term48.
Proof. exact (TRANS (@lem1560851 y) (@lem1560852 y)). Qed.
Lemma lem1560854 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1560855 (y : real) : (term260 y) = term261.
Proof. exact (MK_COMB (@lem1560854) (@lem1560853 y)). Qed.
Lemma lem1560856 (z : real) : (term262 z) = (term253 z).
Proof. exact (@lem1483442 term254 z). Qed.
Lemma lem1560858 (m : nat) : (term255 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1560859 : term256 = term48.
Proof. exact (@lem1560858 term196). Qed.
Lemma lem1560860 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1560861 : term257 = term258.
Proof. exact (MK_COMB (@lem1560860) (@lem1560859)). Qed.
Lemma lem1560862 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1560863 (z : real) : (term253 z) = (term259 z).
Proof. exact (MK_COMB (@lem1560861) (@lem1560862 z)). Qed.
Lemma lem1560864 (z : real) : (term262 z) = (term259 z).
Proof. exact (TRANS (@lem1560856 z) (@lem1560863 z)). Qed.
Lemma lem1560865 (z : real) : (term259 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1560866 (z : real) : (term262 z) = term48.
Proof. exact (TRANS (@lem1560864 z) (@lem1560865 z)). Qed.
Lemma lem1560867 (y : real) (z : real) : (term251 y z) = term263.
Proof. exact (MK_COMB (@lem1560855 y) (@lem1560866 z)). Qed.
Lemma lem1560868 (y : real) (z : real) : (term250 y z) = term263.
Proof. exact (TRANS (@lem1560842 y z) (@lem1560867 y z)). Qed.
Lemma lem1560869 : term263 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1560870 (y : real) (z : real) : (term250 y z) = term48.
Proof. exact (TRANS (@lem1560868 y z) (@lem1560869)). Qed.
Lemma lem1560871 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1560872 (y : real) (z : real) : (term264 y z) = term265.
Proof. exact (MK_COMB (@lem1560871) (@lem1560870 y z)). Qed.
Lemma lem1560873 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1560874 (y : real) (z : real) : (term249 y z) = term266.
Proof. exact (MK_COMB (@lem1560872 y z) (@lem1560873)). Qed.
Lemma lem1560875 (x : real) (y : real) (z : real) (h1 : term223 x y z) : term266.
Proof. exact (EQ_MP (@lem1560874 y z) (@lem1560841 x y z h1)). Qed.
Lemma lem1560877 (n : nat) (m : nat) : (term229 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1560878 : term266 = term267.
Proof. exact (@lem1560877 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1560879 : term267 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1560880 : term266 = False.
Proof. exact (TRANS (@lem1560878) (@lem1560879)). Qed.
Lemma lem1560881 (x : real) (y : real) (z : real) (h1 : term223 x y z) : False.
Proof. exact (EQ_MP (@lem1560880) (@lem1560875 x y z h1)). Qed.
Lemma lem1560882 (x : real) (y : real) (z : real) (h1 : term226 x y z) : False.
Proof. exact (or_elim (@lem1560697 x y z h1) (fun h0 : term221 y x z => @lem1560789 y x z h0) (fun h0 : term223 x y z => @lem1560881 x y z h0)). Qed.
Lemma lem1560883 (x : real) (y : real) (z : real) (h1 : term228 x y z) : False.
Proof. exact (or_elim (@lem1560506 x y z h1) (fun h0 : term215 x y z => @lem1560696 x y z h0) (fun h0 : term226 x y z => @lem1560882 x y z h0)). Qed.
Lemma lem1560884 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term162 x y z.
Proof. exact (h1). Qed.
Lemma lem1560885 (x : real) (y : real) (z : real) (h1 : term162 x y z) : term228 x y z.
Proof. exact (EQ_MP (@lem1560505 x y z) (@lem1560884 x y z h1)). Qed.
Lemma lem1560886 (x : real) (y : real) (z : real) (h1 : term162 x y z) : (term228 x y z) = False.
Proof. exact (prop_ext (fun h2 : term228 x y z => @lem1560883 x y z h2) (fun h2 : False => @lem1560885 x y z h1)). Qed.
Lemma lem1560887 (x : real) (y : real) (z : real) (h1 : term162 x y z) : False.
Proof. exact (EQ_MP (@lem1560886 x y z h1) (@lem1560885 x y z h1)). Qed.
Lemma lem1560888 (x : real) (y : real) (h1 : term164 x y) : term164 x y.
Proof. exact (h1). Qed.
Lemma lem1560889 (x : real) (y : real) (h1 : term164 x y) : False.
Proof. exact (ex_elim (@lem1560888 x y h1) (fun z : real => fun h0 : term163 x y z => @lem1560887 x y z h0)). Qed.
Lemma lem1560890 (x : real) (h1 : term166 x) : term166 x.
Proof. exact (h1). Qed.
Lemma lem1560891 (x : real) (h1 : term166 x) : False.
Proof. exact (ex_elim (@lem1560890 x h1) (fun y : real => fun h0 : term165 x y => @lem1560889 x y h0)). Qed.
Lemma lem1560892 (h1 : term168) : term168.
Proof. exact (h1). Qed.
Lemma lem1560893 (h1 : term168) : False.
Proof. exact (ex_elim (@lem1560892 h1) (fun x : real => fun h0 : term167 x => @lem1560891 x h0)). Qed.
Lemma lem1560894 (h1 : term32) : term32.
Proof. exact (h1). Qed.
Lemma lem1560895 (h1 : term32) : term168.
Proof. exact (EQ_MP (@lem1560185) (@lem1560894 h1)). Qed.
Lemma lem1560896 (h1 : term32) : term168 = False.
Proof. exact (prop_ext (fun h2 : term168 => @lem1560893 h2) (fun h2 : False => @lem1560895 h1)). Qed.
Lemma lem1560897 (h1 : term32) : False.
Proof. exact (EQ_MP (@lem1560896 h1) (@lem1560895 h1)). Qed.
Lemma lem1560898 : term268.
Proof. exact (fun h0 : term32 => @lem1560897 h0). Qed.
Lemma lem1560899 : term269.
Proof. exact (@lem1386578 term270). Qed.
Lemma lem1560900 : term270.
Proof. exact (@lem1560899 (@lem1560898)). Qed.
