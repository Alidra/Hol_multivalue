Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_CASES_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1482678_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483531_spec.
Require Import thm1483554_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17160_spec.
Require Import thm18392_spec.
Require Import thm19367_spec.
Require Import thm912739_spec.
Lemma lem1540474 (x : real) : (term0 x) = (term1 x).
Proof. exact (@lem17160 (x = term2) (term3 x)). Qed.
Lemma lem1540475 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1540476 : term6 = term7.
Proof. exact (@lem1540475 term8). Qed.
Lemma lem1540477 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1540478 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1540479 (x : real) : (term11 x) = (term0 x).
Proof. exact (MK_COMB (@lem1540478) (@lem1540477 x)). Qed.
Lemma lem1540480 (x : real) : (term11 x) = (term1 x).
Proof. exact (TRANS (@lem1540479 x) (@lem1540474 x)). Qed.
Lemma lem1540481 : term12 = term13.
Proof. exact (fun_ext (fun x : real => @lem1540480 x)). Qed.
Lemma lem1540482 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540483 : term7 = term14.
Proof. exact (MK_COMB (@lem1540482) (@lem1540481)). Qed.
Lemma lem1540485 : term6 = term14.
Proof. exact (TRANS (@lem1540476) (@lem1540483)). Qed.
Lemma lem1540494 (x : real) : (term1 x) = (term1 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1540495 : term13 = term13.
Proof. exact (fun_ext (fun x : real => @lem1540494 x)). Qed.
Lemma lem1540496 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540497 : term14 = term14.
Proof. exact (MK_COMB (@lem1540496) (@lem1540495)). Qed.
Lemma lem1540498 : term6 = term14.
Proof. exact (TRANS (@lem1540485) (@lem1540497)). Qed.
Lemma lem1540499 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1483554 x term2). Qed.
Lemma lem1540505 (x : real) : (term17 x) = (term18 x).
Proof. exact (@lem1483519 x term2). Qed.
Lemma lem1540507 (x : nat) : (term19 x) = term2.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1540508 : term20 = term2.
Proof. exact (@lem1540507 term21). Qed.
Lemma lem1540509 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1540510 (x : real) : (term18 x) = (term22 x).
Proof. exact (MK_COMB (@lem1540509 x) (@lem1540508)). Qed.
Lemma lem1540511 (x : real) : (term22 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1540512 (x : real) : (term18 x) = x.
Proof. exact (TRANS (@lem1540510 x) (@lem1540511 x)). Qed.
Lemma lem1540514 (x : real) : (term17 x) = x.
Proof. exact (TRANS (@lem1540505 x) (@lem1540512 x)). Qed.
Lemma lem1540515 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1540516 (x : real) : (term23 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1540515) (@lem1540514 x)). Qed.
Lemma lem1540519 (x : real) : (real_neg x) = (term24 x).
Proof. exact (@lem1483512 x). Qed.
Lemma lem1540520 (x : real) : (term25 x) = (term25 x).
Proof. exact (eq_refl (term25 x)). Qed.
Lemma lem1540521 (x : real) : ((term23 x) = (real_neg x)) = ((term23 x) = (term24 x)).
Proof. exact (MK_COMB (@lem1540520 x) (@lem1540519 x)). Qed.
Lemma lem1540522 (x : real) : (term23 x) = (term24 x).
Proof. exact (EQ_MP (@lem1540521 x) (@lem1540516 x)). Qed.
Lemma lem1540523 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540524 (x : real) : (term26 x) = (term27 x).
Proof. exact (MK_COMB (@lem1540523) (@lem1540522 x)). Qed.
Lemma lem1540525 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540526 (x : real) : (term28 x) = (term29 x).
Proof. exact (MK_COMB (@lem1540524 x) (@lem1540525)). Qed.
Lemma lem1540527 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540528 (x : real) : (term30 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1540527) (@lem1540514 x)). Qed.
Lemma lem1540529 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540530 (x : real) : (term31 x) = (term32 x).
Proof. exact (MK_COMB (@lem1540528 x) (@lem1540529)). Qed.
Lemma lem1540531 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1540532 (x : real) : (term33 x) = (term34 x).
Proof. exact (MK_COMB (@lem1540531) (@lem1540530 x)). Qed.
Lemma lem1540533 (x : real) : (term16 x) = (term35 x).
Proof. exact (MK_COMB (@lem1540532 x) (@lem1540526 x)). Qed.
Lemma lem1540534 (x : real) : (term15 x) = (term35 x).
Proof. exact (TRANS (@lem1540499 x) (@lem1540533 x)). Qed.
Lemma lem1540535 (x : real) : (term36 x) = (term37 x).
Proof. exact (@lem1483531 term2 (real_abs x)). Qed.
Lemma lem1540541 (x : real) : (term38 x) = (term39 x).
Proof. exact (@lem1483519 term2 (real_abs x)). Qed.
Lemma lem1540546 (x : real) : (term39 x) = (term40 x).
Proof. exact (@lem1483448 (term40 x)). Qed.
Lemma lem1540548 (x : real) : (term38 x) = (term40 x).
Proof. exact (TRANS (@lem1540541 x) (@lem1540546 x)). Qed.
Lemma lem1540549 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1540550 (x : real) : (term41 x) = (term42 x).
Proof. exact (MK_COMB (@lem1540549) (@lem1540548 x)). Qed.
Lemma lem1540551 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540552 (x : real) : (term37 x) = (term43 x).
Proof. exact (MK_COMB (@lem1540550 x) (@lem1540551)). Qed.
Lemma lem1540553 (x : real) : (term36 x) = (term43 x).
Proof. exact (TRANS (@lem1540535 x) (@lem1540552 x)). Qed.
Lemma lem1540554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1540555 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1540554) (@lem1540534 x)). Qed.
Lemma lem1540556 (x : real) : (term1 x) = (term46 x).
Proof. exact (MK_COMB (@lem1540555 x) (@lem1540553 x)). Qed.
Lemma lem1540557 : term13 = term47.
Proof. exact (fun_ext (fun x : real => @lem1540556 x)). Qed.
Lemma lem1540558 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540559 : term14 = term48.
Proof. exact (MK_COMB (@lem1540558) (@lem1540557)). Qed.
Lemma lem1540614 : term6 = term48.
Proof. exact (TRANS (@lem1540498) (@lem1540559)). Qed.
Lemma lem1540631 (x : real) : (term46 x) = (term49 x).
Proof. exact (@lem19367 (term32 x) (term29 x) (term43 x)). Qed.
Lemma lem1540632 : term47 = term50.
Proof. exact (fun_ext (fun x : real => @lem1540631 x)). Qed.
Lemma lem1540633 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1540634 : term48 = term51.
Proof. exact (MK_COMB (@lem1540633) (@lem1540632)). Qed.
Lemma lem1540635 : term6 = term51.
Proof. exact (TRANS (@lem1540614) (@lem1540634)). Qed.
Lemma lem1540637 (x : real) (r : real) : (term52 x r) = (term53 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1540638 (x : real) : (term43 x) = (term54 x).
Proof. exact (@lem1540637 x term2). Qed.
Lemma lem1540645 (x : real) : (term55 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1540646 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1540647 (x : real) : (term56 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1540646) (@lem1540645 x)). Qed.
Lemma lem1540648 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540649 (x : real) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1540647 x) (@lem1540648)). Qed.
Lemma lem1540662 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1540663 (x : real) : (term54 x) = (term60 x).
Proof. exact (MK_COMB (@lem1540662 x) (@lem1540649 x)). Qed.
Lemma lem1540664 (x : real) : (term43 x) = (term60 x).
Proof. exact (TRANS (@lem1540638 x) (@lem1540663 x)). Qed.
Lemma lem1540665 (x : real) : (term61 x) = (term61 x).
Proof. exact (eq_refl (term61 x)). Qed.
Lemma lem1540668 (x : real) : (term62 x) = (term63 x).
Proof. exact (MK_COMB (@lem1540665 x) (@lem1540664 x)). Qed.
Lemma lem1540670 (x : real) (r : real) : (term52 x r) = (term53 x r).
Proof. exact (proj1 (@lem1482678 x (@el real) (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1540671 (x : real) : (term43 x) = (term54 x).
Proof. exact (@lem1540670 x term2). Qed.
Lemma lem1540678 (x : real) : (term55 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1540679 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1540680 (x : real) : (term56 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1540679) (@lem1540678 x)). Qed.
Lemma lem1540681 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540682 (x : real) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1540680 x) (@lem1540681)). Qed.
Lemma lem1540695 (x : real) : (term59 x) = (term59 x).
Proof. exact (eq_refl (term59 x)). Qed.
Lemma lem1540696 (x : real) : (term54 x) = (term60 x).
Proof. exact (MK_COMB (@lem1540695 x) (@lem1540682 x)). Qed.
Lemma lem1540697 (x : real) : (term43 x) = (term60 x).
Proof. exact (TRANS (@lem1540671 x) (@lem1540696 x)). Qed.
Lemma lem1540698 (x : real) : (term64 x) = (term64 x).
Proof. exact (eq_refl (term64 x)). Qed.
Lemma lem1540701 (x : real) : (term65 x) = (term66 x).
Proof. exact (MK_COMB (@lem1540698 x) (@lem1540697 x)). Qed.
Lemma lem1540702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1540703 (x : real) : (term67 x) = (term68 x).
Proof. exact (MK_COMB (@lem1540702) (@lem1540668 x)). Qed.
Lemma lem1540704 (x : real) : (term49 x) = (term69 x).
Proof. exact (MK_COMB (@lem1540703 x) (@lem1540701 x)). Qed.
Lemma lem1540705 (x : real) (h1 : term69 x) : term69 x.
Proof. exact (h1). Qed.
Lemma lem1540706 (x : real) (h1 : term63 x) : term63 x.
Proof. exact (h1). Qed.
Lemma lem1540707 (x : real) (h1 : term63 x) : term60 x.
Proof. exact (proj2 (@lem1540706 x h1)). Qed.
Lemma lem1540708 (x : real) (h1 : term63 x) : term32 x.
Proof. exact (proj1 (@lem1540706 x h1)). Qed.
Lemma lem1540710 (x : real) (h1 : term63 x) : term70 x.
Proof. exact (proj1 (@lem1540707 x h1)). Qed.
Lemma lem1540712 (n : nat) (m : nat) : (term71 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540713 : term72 = term73.
Proof. exact (@lem1540712 (NUMERAL 0) term21). Qed.
Lemma lem1540714 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1540715 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1540716 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem1540715 h1) (fun h1 : term73 = True => @lem1540714)). Qed.
Lemma lem1540717 : term73 = True.
Proof. exact (EQ_MP (@lem1540716) (@lem1540714)). Qed.
Lemma lem1540718 : term72 = True.
Proof. exact (TRANS (@lem1540713) (@lem1540717)). Qed.
Lemma lem1540719 : True = term72.
Proof. exact (SYM (@lem1540718)). Qed.
Lemma lem1540720 : term72.
Proof. exact (EQ_MP (@lem1540719) (@lem0)). Qed.
Lemma lem1540721 (x : real) (h1 : term63 x) : term75 x.
Proof. exact (conj (@lem1540720) (@lem1540710 x h1)). Qed.
Lemma lem1540723 (x : real) (y : real) : term76 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1540724 (x : real) : term77 x.
Proof. exact (@lem1540723 term78 (term24 x)). Qed.
Lemma lem1540725 (x : real) (h1 : term63 x) : term79 x.
Proof. exact (@lem1540724 x (@lem1540721 x h1)). Qed.
Lemma lem1540726 (x : real) : (term80 x) = (term24 x).
Proof. exact (@lem1483460 (term24 x)). Qed.
Lemma lem1540727 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1540728 (x : real) : (term81 x) = (term82 x).
Proof. exact (MK_COMB (@lem1540727) (@lem1540726 x)). Qed.
Lemma lem1540729 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540730 (x : real) : (term79 x) = (term70 x).
Proof. exact (MK_COMB (@lem1540728 x) (@lem1540729)). Qed.
Lemma lem1540731 (x : real) (h1 : term63 x) : term70 x.
Proof. exact (EQ_MP (@lem1540730 x) (@lem1540725 x h1)). Qed.
Lemma lem1540733 (n : nat) (m : nat) : (term71 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540734 : term72 = term73.
Proof. exact (@lem1540733 (NUMERAL 0) term21). Qed.
Lemma lem1540735 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1540736 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1540737 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem1540736 h1) (fun h1 : term73 = True => @lem1540735)). Qed.
Lemma lem1540738 : term73 = True.
Proof. exact (EQ_MP (@lem1540737) (@lem1540735)). Qed.
Lemma lem1540739 : term72 = True.
Proof. exact (TRANS (@lem1540734) (@lem1540738)). Qed.
Lemma lem1540740 : True = term72.
Proof. exact (SYM (@lem1540739)). Qed.
Lemma lem1540741 : term72.
Proof. exact (EQ_MP (@lem1540740) (@lem0)). Qed.
Lemma lem1540742 (x : real) (h1 : term63 x) : term83 x.
Proof. exact (conj (@lem1540741) (@lem1540708 x h1)). Qed.
Lemma lem1540744 (x : real) (y : real) : term84 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1540745 (x : real) : term85 x.
Proof. exact (@lem1540744 term78 x). Qed.
Lemma lem1540746 (x : real) (h1 : term63 x) : term86 x.
Proof. exact (@lem1540745 x (@lem1540742 x h1)). Qed.
Lemma lem1540747 (x : real) : (term55 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1540748 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540749 (x : real) : (term87 x) = (real_gt x).
Proof. exact (MK_COMB (@lem1540748) (@lem1540747 x)). Qed.
Lemma lem1540750 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540751 (x : real) : (term86 x) = (term32 x).
Proof. exact (MK_COMB (@lem1540749 x) (@lem1540750)). Qed.
Lemma lem1540752 (x : real) (h1 : term63 x) : term32 x.
Proof. exact (EQ_MP (@lem1540751 x) (@lem1540746 x h1)). Qed.
Lemma lem1540753 (x : real) (h1 : term63 x) : term88 x.
Proof. exact (conj (@lem1540752 x h1) (@lem1540731 x h1)). Qed.
Lemma lem1540755 (x : real) (y : real) : term89 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1540756 (x : real) : term90 x.
Proof. exact (@lem1540755 x (term24 x)). Qed.
Lemma lem1540757 (x : real) (h1 : term63 x) : term91 x.
Proof. exact (@lem1540756 x (@lem1540753 x h1)). Qed.
Lemma lem1540758 (x : real) : (term92 x) = (term93 x).
Proof. exact (@lem1483442 term94 x). Qed.
Lemma lem1540760 (m : nat) : (term95 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1540761 : term96 = term2.
Proof. exact (@lem1540760 term21). Qed.
Lemma lem1540762 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1540763 : term97 = term98.
Proof. exact (MK_COMB (@lem1540762) (@lem1540761)). Qed.
Lemma lem1540764 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1540765 (x : real) : (term93 x) = (term99 x).
Proof. exact (MK_COMB (@lem1540763) (@lem1540764 x)). Qed.
Lemma lem1540766 (x : real) : (term92 x) = (term99 x).
Proof. exact (TRANS (@lem1540758 x) (@lem1540765 x)). Qed.
Lemma lem1540767 (x : real) : (term99 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1540768 (x : real) : (term92 x) = term2.
Proof. exact (TRANS (@lem1540766 x) (@lem1540767 x)). Qed.
Lemma lem1540769 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540770 (x : real) : (term100 x) = term101.
Proof. exact (MK_COMB (@lem1540769) (@lem1540768 x)). Qed.
Lemma lem1540771 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540772 (x : real) : (term91 x) = term102.
Proof. exact (MK_COMB (@lem1540770 x) (@lem1540771)). Qed.
Lemma lem1540773 (x : real) (h1 : term63 x) : term102.
Proof. exact (EQ_MP (@lem1540772 x) (@lem1540757 x h1)). Qed.
Lemma lem1540775 (n : nat) (m : nat) : (term71 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540776 : term102 = term103.
Proof. exact (@lem1540775 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1540777 : term103 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1540778 : term102 = False.
Proof. exact (TRANS (@lem1540776) (@lem1540777)). Qed.
Lemma lem1540779 (x : real) (h1 : term63 x) : False.
Proof. exact (EQ_MP (@lem1540778) (@lem1540773 x h1)). Qed.
Lemma lem1540780 (x : real) (h1 : term66 x) : term66 x.
Proof. exact (h1). Qed.
Lemma lem1540781 (x : real) (h1 : term66 x) : term60 x.
Proof. exact (proj2 (@lem1540780 x h1)). Qed.
Lemma lem1540782 (x : real) (h1 : term66 x) : term29 x.
Proof. exact (proj1 (@lem1540780 x h1)). Qed.
Lemma lem1540783 (x : real) (h1 : term66 x) : term58 x.
Proof. exact (proj2 (@lem1540781 x h1)). Qed.
Lemma lem1540786 (n : nat) (m : nat) : (term71 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540787 : term72 = term73.
Proof. exact (@lem1540786 (NUMERAL 0) term21). Qed.
Lemma lem1540788 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1540789 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1540790 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem1540789 h1) (fun h1 : term73 = True => @lem1540788)). Qed.
Lemma lem1540791 : term73 = True.
Proof. exact (EQ_MP (@lem1540790) (@lem1540788)). Qed.
Lemma lem1540792 : term72 = True.
Proof. exact (TRANS (@lem1540787) (@lem1540791)). Qed.
Lemma lem1540793 : True = term72.
Proof. exact (SYM (@lem1540792)). Qed.
Lemma lem1540794 : term72.
Proof. exact (EQ_MP (@lem1540793) (@lem0)). Qed.
Lemma lem1540795 (x : real) (h1 : term66 x) : term104 x.
Proof. exact (conj (@lem1540794) (@lem1540783 x h1)). Qed.
Lemma lem1540797 (x : real) (y : real) : term76 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1540798 (x : real) : term105 x.
Proof. exact (@lem1540797 term78 x). Qed.
Lemma lem1540799 (x : real) (h1 : term66 x) : term57 x.
Proof. exact (@lem1540798 x (@lem1540795 x h1)). Qed.
Lemma lem1540800 (x : real) : (term55 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1540801 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1540802 (x : real) : (term56 x) = (real_ge x).
Proof. exact (MK_COMB (@lem1540801) (@lem1540800 x)). Qed.
Lemma lem1540803 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540804 (x : real) : (term57 x) = (term58 x).
Proof. exact (MK_COMB (@lem1540802 x) (@lem1540803)). Qed.
Lemma lem1540805 (x : real) (h1 : term66 x) : term58 x.
Proof. exact (EQ_MP (@lem1540804 x) (@lem1540799 x h1)). Qed.
Lemma lem1540807 (n : nat) (m : nat) : (term71 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540808 : term72 = term73.
Proof. exact (@lem1540807 (NUMERAL 0) term21). Qed.
Lemma lem1540809 : term74 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1540810 (h1 : term74 = (BIT1 0)) : term73 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1540811 : (term74 = (BIT1 0)) = (term73 = True).
Proof. exact (prop_ext (fun h1 : term74 = (BIT1 0) => @lem1540810 h1) (fun h1 : term73 = True => @lem1540809)). Qed.
Lemma lem1540812 : term73 = True.
Proof. exact (EQ_MP (@lem1540811) (@lem1540809)). Qed.
Lemma lem1540813 : term72 = True.
Proof. exact (TRANS (@lem1540808) (@lem1540812)). Qed.
Lemma lem1540814 : True = term72.
Proof. exact (SYM (@lem1540813)). Qed.
Lemma lem1540815 : term72.
Proof. exact (EQ_MP (@lem1540814) (@lem0)). Qed.
Lemma lem1540816 (x : real) (h1 : term66 x) : term106 x.
Proof. exact (conj (@lem1540815) (@lem1540782 x h1)). Qed.
Lemma lem1540818 (x : real) (y : real) : term84 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1540819 (x : real) : term107 x.
Proof. exact (@lem1540818 term78 (term24 x)). Qed.
Lemma lem1540820 (x : real) (h1 : term66 x) : term108 x.
Proof. exact (@lem1540819 x (@lem1540816 x h1)). Qed.
Lemma lem1540821 (x : real) : (term80 x) = (term24 x).
Proof. exact (@lem1483460 (term24 x)). Qed.
Lemma lem1540822 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540823 (x : real) : (term109 x) = (term27 x).
Proof. exact (MK_COMB (@lem1540822) (@lem1540821 x)). Qed.
Lemma lem1540824 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540825 (x : real) : (term108 x) = (term29 x).
Proof. exact (MK_COMB (@lem1540823 x) (@lem1540824)). Qed.
Lemma lem1540826 (x : real) (h1 : term66 x) : term29 x.
Proof. exact (EQ_MP (@lem1540825 x) (@lem1540820 x h1)). Qed.
Lemma lem1540827 (x : real) (h1 : term66 x) : term110 x.
Proof. exact (conj (@lem1540826 x h1) (@lem1540805 x h1)). Qed.
Lemma lem1540829 (x : real) (y : real) : term89 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1540830 (x : real) : term111 x.
Proof. exact (@lem1540829 (term24 x) x). Qed.
Lemma lem1540831 (x : real) (h1 : term66 x) : term112 x.
Proof. exact (@lem1540830 x (@lem1540827 x h1)). Qed.
Lemma lem1540832 (x : real) : (term113 x) = (term93 x).
Proof. exact (@lem1483440 term94 x). Qed.
Lemma lem1540834 (m : nat) : (term95 m) = term2.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1540835 : term96 = term2.
Proof. exact (@lem1540834 term21). Qed.
Lemma lem1540836 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1540837 : term97 = term98.
Proof. exact (MK_COMB (@lem1540836) (@lem1540835)). Qed.
Lemma lem1540838 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1540839 (x : real) : (term93 x) = (term99 x).
Proof. exact (MK_COMB (@lem1540837) (@lem1540838 x)). Qed.
Lemma lem1540840 (x : real) : (term113 x) = (term99 x).
Proof. exact (TRANS (@lem1540832 x) (@lem1540839 x)). Qed.
Lemma lem1540841 (x : real) : (term99 x) = term2.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1540842 (x : real) : (term113 x) = term2.
Proof. exact (TRANS (@lem1540840 x) (@lem1540841 x)). Qed.
Lemma lem1540843 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1540844 (x : real) : (term114 x) = term101.
Proof. exact (MK_COMB (@lem1540843) (@lem1540842 x)). Qed.
Lemma lem1540845 : term2 = term2.
Proof. exact (eq_refl term2). Qed.
Lemma lem1540846 (x : real) : (term112 x) = term102.
Proof. exact (MK_COMB (@lem1540844 x) (@lem1540845)). Qed.
Lemma lem1540847 (x : real) (h1 : term66 x) : term102.
Proof. exact (EQ_MP (@lem1540846 x) (@lem1540831 x h1)). Qed.
Lemma lem1540849 (n : nat) (m : nat) : (term71 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1540850 : term102 = term103.
Proof. exact (@lem1540849 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1540851 : term103 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1540852 : term102 = False.
Proof. exact (TRANS (@lem1540850) (@lem1540851)). Qed.
Lemma lem1540853 (x : real) (h1 : term66 x) : False.
Proof. exact (EQ_MP (@lem1540852) (@lem1540847 x h1)). Qed.
Lemma lem1540854 (x : real) (h1 : term69 x) : False.
Proof. exact (or_elim (@lem1540705 x h1) (fun h0 : term63 x => @lem1540779 x h0) (fun h0 : term66 x => @lem1540853 x h0)). Qed.
Lemma lem1540855 (x : real) (h1 : term49 x) : term49 x.
Proof. exact (h1). Qed.
Lemma lem1540856 (x : real) (h1 : term49 x) : term69 x.
Proof. exact (EQ_MP (@lem1540704 x) (@lem1540855 x h1)). Qed.
Lemma lem1540857 (x : real) (h1 : term49 x) : (term69 x) = False.
Proof. exact (prop_ext (fun h2 : term69 x => @lem1540854 x h2) (fun h2 : False => @lem1540856 x h1)). Qed.
Lemma lem1540858 (x : real) (h1 : term49 x) : False.
Proof. exact (EQ_MP (@lem1540857 x h1) (@lem1540856 x h1)). Qed.
Lemma lem1540859 (h1 : term51) : term51.
Proof. exact (h1). Qed.
Lemma lem1540860 (h1 : term51) : False.
Proof. exact (ex_elim (@lem1540859 h1) (fun x : real => fun h0 : term50 x => @lem1540858 x h0)). Qed.
Lemma lem1540861 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem1540862 (h1 : term6) : term51.
Proof. exact (EQ_MP (@lem1540635) (@lem1540861 h1)). Qed.
Lemma lem1540863 (h1 : term6) : term51 = False.
Proof. exact (prop_ext (fun h2 : term51 => @lem1540860 h2) (fun h2 : False => @lem1540862 h1)). Qed.
Lemma lem1540864 (h1 : term6) : False.
Proof. exact (EQ_MP (@lem1540863 h1) (@lem1540862 h1)). Qed.
Lemma lem1540865 : term115.
Proof. exact (fun h0 : term6 => @lem1540864 h0). Qed.
Lemma lem1540866 : term116.
Proof. exact (@lem1386578 term117). Qed.
Lemma lem1540867 : term117.
Proof. exact (@lem1540866 (@lem1540865)). Qed.
