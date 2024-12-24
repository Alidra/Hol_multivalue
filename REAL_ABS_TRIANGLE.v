Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_ABS_TRIANGLE_term_abbrevs.
Require Import thm1006570_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1386578_spec.
Require Import thm1482703_spec.
Require Import thm1482705_spec.
Require Import thm1482981_spec.
Require Import thm1483438_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483444_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483450_spec.
Require Import thm1483460_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483512_spec.
Require Import thm1483519_spec.
Require Import thm1483525_spec.
Require Import thm1483527_spec.
Require Import thm1483533_spec.
Require Import thm18392_spec.
Require Import thm706885_spec.
Lemma lem1528545 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1528546 (x : real) : (term2 x) = (term3 x).
Proof. exact (@lem1528545 (term4 x)). Qed.
Lemma lem1528547 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem1528548 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1528550 (x : real) (y : real) : (term7 x y) = (term8 x y).
Proof. exact (MK_COMB (@lem1528548) (@lem1528547 x y)). Qed.
Lemma lem1528551 (x : real) : (term9 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1528550 x y)). Qed.
Lemma lem1528552 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528553 (x : real) : (term3 x) = (term11 x).
Proof. exact (MK_COMB (@lem1528552) (@lem1528551 x)). Qed.
Lemma lem1528554 (x : real) : (term2 x) = (term11 x).
Proof. exact (TRANS (@lem1528546 x) (@lem1528553 x)). Qed.
Lemma lem1528555 (P : real -> Prop) : (term0 P) = (term1 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1528556 : term12 = term13.
Proof. exact (@lem1528555 term14). Qed.
Lemma lem1528557 (x : real) : (term15 x) = (term16 x).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1528558 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1528559 (x : real) : (term17 x) = (term2 x).
Proof. exact (MK_COMB (@lem1528558) (@lem1528557 x)). Qed.
Lemma lem1528560 (x : real) : (term17 x) = (term11 x).
Proof. exact (TRANS (@lem1528559 x) (@lem1528554 x)). Qed.
Lemma lem1528561 : term18 = term19.
Proof. exact (fun_ext (fun x : real => @lem1528560 x)). Qed.
Lemma lem1528562 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528563 : term13 = term20.
Proof. exact (MK_COMB (@lem1528562) (@lem1528561)). Qed.
Lemma lem1528565 : term12 = term20.
Proof. exact (TRANS (@lem1528556) (@lem1528563)). Qed.
Lemma lem1528568 (x : real) (y : real) : (term8 x y) = (term8 x y).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1528569 (x : real) : (term10 x) = (term10 x).
Proof. exact (fun_ext (fun y : real => @lem1528568 x y)). Qed.
Lemma lem1528570 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528571 (x : real) : (term11 x) = (term11 x).
Proof. exact (MK_COMB (@lem1528570) (@lem1528569 x)). Qed.
Lemma lem1528572 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1528571 x)). Qed.
Lemma lem1528573 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528574 : term20 = term20.
Proof. exact (MK_COMB (@lem1528573) (@lem1528572)). Qed.
Lemma lem1528575 : term12 = term20.
Proof. exact (TRANS (@lem1528565) (@lem1528574)). Qed.
Lemma lem1528576 (x : real) (y : real) : (term8 x y) = (term21 x y).
Proof. exact (@lem1483533 (term22 x y) (term23 x y)). Qed.
Lemma lem1528588 (x : real) (y : real) : (term24 x y) = (term25 x y).
Proof. exact (@lem1483519 (term22 x y) (term23 x y)). Qed.
Lemma lem1528595 (x : real) (y : real) : (term26 x y) = (term27 x y).
Proof. exact (@lem1483508 (real_abs x) term28 (real_abs y)). Qed.
Lemma lem1528596 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (eq_refl (term29 x y)). Qed.
Lemma lem1528597 (x : real) (y : real) : (term25 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1528596 x y) (@lem1528595 x y)). Qed.
Lemma lem1528598 (x : real) (y : real) : (term30 x y) = (term31 x y).
Proof. exact (@lem1483484 (term32 x) (term22 x y) (term32 y)). Qed.
Lemma lem1528599 (x : real) (y : real) : (term33 x y) = (term34 x y).
Proof. exact (@lem1483488 (term32 y) (term22 x y)). Qed.
Lemma lem1528600 (x : real) : (term35 x) = (term35 x).
Proof. exact (eq_refl (term35 x)). Qed.
Lemma lem1528601 (x : real) (y : real) : (term31 x y) = (term36 x y).
Proof. exact (MK_COMB (@lem1528600 x) (@lem1528599 x y)). Qed.
Lemma lem1528602 (x : real) (y : real) : (term30 x y) = (term36 x y).
Proof. exact (TRANS (@lem1528598 x y) (@lem1528601 x y)). Qed.
Lemma lem1528603 (x : real) (y : real) : (term25 x y) = (term36 x y).
Proof. exact (TRANS (@lem1528597 x y) (@lem1528602 x y)). Qed.
Lemma lem1528605 (x : real) (y : real) : (term24 x y) = (term36 x y).
Proof. exact (TRANS (@lem1528588 x y) (@lem1528603 x y)). Qed.
Lemma lem1528606 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528607 (x : real) (y : real) : (term37 x y) = (term38 x y).
Proof. exact (MK_COMB (@lem1528606) (@lem1528605 x y)). Qed.
Lemma lem1528608 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528609 (x : real) (y : real) : (term21 x y) = (term40 x y).
Proof. exact (MK_COMB (@lem1528607 x y) (@lem1528608)). Qed.
Lemma lem1528610 (x : real) (y : real) : (term8 x y) = (term40 x y).
Proof. exact (TRANS (@lem1528576 x y) (@lem1528609 x y)). Qed.
Lemma lem1528611 (x : real) : (term10 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1528610 x y)). Qed.
Lemma lem1528612 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528613 (x : real) : (term11 x) = (term42 x).
Proof. exact (MK_COMB (@lem1528612) (@lem1528611 x)). Qed.
Lemma lem1528614 : term19 = term43.
Proof. exact (fun_ext (fun x : real => @lem1528613 x)). Qed.
Lemma lem1528615 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528616 : term20 = term44.
Proof. exact (MK_COMB (@lem1528615) (@lem1528614)). Qed.
Lemma lem1528631 : term12 = term44.
Proof. exact (TRANS (@lem1528575) (@lem1528616)). Qed.
Lemma lem1528632 (x : real) (y : real) : (term40 x y) = (term40 x y).
Proof. exact (eq_refl (term40 x y)). Qed.
Lemma lem1528633 (x : real) : (term41 x) = (term41 x).
Proof. exact (fun_ext (fun y : real => @lem1528632 x y)). Qed.
Lemma lem1528634 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528635 (x : real) : (term42 x) = (term42 x).
Proof. exact (MK_COMB (@lem1528634) (@lem1528633 x)). Qed.
Lemma lem1528636 : term43 = term43.
Proof. exact (fun_ext (fun x : real => @lem1528635 x)). Qed.
Lemma lem1528637 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1528638 : term44 = term44.
Proof. exact (MK_COMB (@lem1528637) (@lem1528636)). Qed.
Lemma lem1528639 : term12 = term44.
Proof. exact (TRANS (@lem1528631) (@lem1528638)). Qed.
Lemma lem1528641 (a : real) (x : real) (r : real) : (term45 x a r) = (term46 a x r).
Proof. exact (proj1 (@lem1482703 x a (@el real) (@el real) (@el real) r)). Qed.
Lemma lem1528642 (y : real) (x : real) : (term40 x y) = (term47 y x).
Proof. exact (@lem1528641 (term34 x y) x term39). Qed.
Lemma lem1528649 (x : real) : (term48 x) = x.
Proof. exact (@lem1483460 x). Qed.
Lemma lem1528664 (x : real) (y : real) : (term49 x y) = (term49 x y).
Proof. exact (eq_refl (term49 x y)). Qed.
Lemma lem1528665 (y : real) (x : real) : (term50 y x) = (term51 y x).
Proof. exact (MK_COMB (@lem1528664 x y) (@lem1528649 x)). Qed.
Lemma lem1528666 (x : real) (y : real) : (term51 y x) = (term52 x y).
Proof. exact (@lem1483488 x (term34 x y)). Qed.
Lemma lem1528667 (x : real) (y : real) : (term50 y x) = (term52 x y).
Proof. exact (TRANS (@lem1528665 y x) (@lem1528666 x y)). Qed.
Lemma lem1528668 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528669 (x : real) (y : real) : (term53 y x) = (term54 x y).
Proof. exact (MK_COMB (@lem1528668) (@lem1528667 x y)). Qed.
Lemma lem1528670 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528671 (x : real) (y : real) : (term55 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem1528669 x y) (@lem1528670)). Qed.
Lemma lem1528696 (x : real) (y : real) : (term57 y x) = (term58 x y).
Proof. exact (@lem1483488 (term59 x) (term34 x y)). Qed.
Lemma lem1528697 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528698 (x : real) (y : real) : (term60 y x) = (term61 x y).
Proof. exact (MK_COMB (@lem1528697) (@lem1528696 x y)). Qed.
Lemma lem1528699 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528700 (x : real) (y : real) : (term62 y x) = (term63 x y).
Proof. exact (MK_COMB (@lem1528698 x y) (@lem1528699)). Qed.
Lemma lem1528701 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528702 (x : real) (y : real) : (term64 y x) = (term65 x y).
Proof. exact (MK_COMB (@lem1528701) (@lem1528700 x y)). Qed.
Lemma lem1528703 (x : real) (y : real) : (term47 y x) = (term66 x y).
Proof. exact (MK_COMB (@lem1528702 x y) (@lem1528671 x y)). Qed.
Lemma lem1528704 (x : real) (y : real) : (term40 x y) = (term66 x y).
Proof. exact (TRANS (@lem1528642 y x) (@lem1528703 x y)). Qed.
Lemma lem1528706 (a : real) (x : real) (b : real) (r : real) : (term67 a x b r) = (term68 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem1528707 (x : real) (y : real) : (term63 x y) = (term69 x y).
Proof. exact (@lem1528706 (term59 x) y (term22 x y) term39). Qed.
Lemma lem1528708 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1528715 (y : real) : (term48 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1528716 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1528717 (y : real) : (term70 y) = (real_add y).
Proof. exact (MK_COMB (@lem1528716) (@lem1528715 y)). Qed.
Lemma lem1528720 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1528717 y) (@lem1528708 x y)). Qed.
Lemma lem1528729 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1528732 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (MK_COMB (@lem1528729 x) (@lem1528720 x y)). Qed.
Lemma lem1528733 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528734 (x : real) (y : real) : (term76 x y) = (term77 x y).
Proof. exact (MK_COMB (@lem1528733) (@lem1528732 x y)). Qed.
Lemma lem1528735 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528736 (x : real) (y : real) : (term78 x y) = (term79 x y).
Proof. exact (MK_COMB (@lem1528734 x y) (@lem1528735)). Qed.
Lemma lem1528767 (x : real) (y : real) : (term80 x y) = (term80 x y).
Proof. exact (eq_refl (term80 x y)). Qed.
Lemma lem1528768 (x : real) (y : real) : (term69 x y) = (term81 x y).
Proof. exact (MK_COMB (@lem1528767 x y) (@lem1528736 x y)). Qed.
Lemma lem1528769 (x : real) (y : real) : (term63 x y) = (term81 x y).
Proof. exact (TRANS (@lem1528707 x y) (@lem1528768 x y)). Qed.
Lemma lem1528770 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1528771 (x : real) (y : real) : (term65 x y) = (term82 x y).
Proof. exact (MK_COMB (@lem1528770) (@lem1528769 x y)). Qed.
Lemma lem1528773 (a : real) (x : real) (b : real) (r : real) : (term67 a x b r) = (term68 a x b r).
Proof. exact (proj1 (@lem1482705 x a b (@el real) (@el real) r)). Qed.
Lemma lem1528774 (x : real) (y : real) : (term56 x y) = (term83 x y).
Proof. exact (@lem1528773 x y (term22 x y) term39). Qed.
Lemma lem1528775 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (eq_refl (term22 x y)). Qed.
Lemma lem1528782 (y : real) : (term48 y) = y.
Proof. exact (@lem1483460 y). Qed.
Lemma lem1528783 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1528784 (y : real) : (term70 y) = (real_add y).
Proof. exact (MK_COMB (@lem1528783) (@lem1528782 y)). Qed.
Lemma lem1528787 (x : real) (y : real) : (term71 x y) = (term72 x y).
Proof. exact (MK_COMB (@lem1528784 y) (@lem1528775 x y)). Qed.
Lemma lem1528790 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1528793 (x : real) (y : real) : (term84 x y) = (term85 x y).
Proof. exact (MK_COMB (@lem1528790 x) (@lem1528787 x y)). Qed.
Lemma lem1528794 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528795 (x : real) (y : real) : (term86 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem1528794) (@lem1528793 x y)). Qed.
Lemma lem1528796 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528797 (x : real) (y : real) : (term88 x y) = (term89 x y).
Proof. exact (MK_COMB (@lem1528795 x y) (@lem1528796)). Qed.
Lemma lem1528822 (x : real) (y : real) : (term90 x y) = (term90 x y).
Proof. exact (eq_refl (term90 x y)). Qed.
Lemma lem1528823 (x : real) (y : real) : (term83 x y) = (term91 x y).
Proof. exact (MK_COMB (@lem1528822 x y) (@lem1528797 x y)). Qed.
Lemma lem1528824 (x : real) (y : real) : (term56 x y) = (term91 x y).
Proof. exact (TRANS (@lem1528774 x y) (@lem1528823 x y)). Qed.
Lemma lem1528825 (x : real) (y : real) : (term66 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1528771 x y) (@lem1528824 x y)). Qed.
Lemma lem1528826 (x : real) (y : real) : (term40 x y) = (term92 x y).
Proof. exact (TRANS (@lem1528704 x y) (@lem1528825 x y)). Qed.
Lemma lem1528827 (x : real) (y : real) : (term93 x y) = (term92 x y).
Proof. exact (eq_refl (term93 x y)). Qed.
Lemma lem1528828 (x : real) (y : real) : (term92 x y) = (term93 x y).
Proof. exact (SYM (@lem1528827 x y)). Qed.
Lemma lem1528829 (x : real) (y : real) : (term93 x y) = (term94 x y).
Proof. exact (@lem1482981 (term95 x y) (real_add x y)). Qed.
Lemma lem1528830 (x : real) (y : real) : (term92 x y) = (term94 x y).
Proof. exact (TRANS (@lem1528828 x y) (@lem1528829 x y)). Qed.
Lemma lem1528831 (x : real) (y : real) : (term96 x y) = (term97 x y).
Proof. exact (eq_refl (term96 x y)). Qed.
Lemma lem1528832 (x : real) (y : real) : (term98 x y) = (term98 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem1528833 (x : real) (y : real) : (term99 x y) = (term100 x y).
Proof. exact (MK_COMB (@lem1528832 x y) (@lem1528831 x y)). Qed.
Lemma lem1528834 (x : real) (y : real) : (term101 x y) = (term102 x y).
Proof. exact (eq_refl (term101 x y)). Qed.
Lemma lem1528835 (x : real) (y : real) : (term103 x y) = (term103 x y).
Proof. exact (eq_refl (term103 x y)). Qed.
Lemma lem1528836 (x : real) (y : real) : (term104 x y) = (term105 x y).
Proof. exact (MK_COMB (@lem1528835 x y) (@lem1528834 x y)). Qed.
Lemma lem1528837 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1528838 (x : real) (y : real) : (term106 x y) = (term107 x y).
Proof. exact (MK_COMB (@lem1528837) (@lem1528836 x y)). Qed.
Lemma lem1528839 (x : real) (y : real) : (term94 x y) = (term108 x y).
Proof. exact (MK_COMB (@lem1528838 x y) (@lem1528833 x y)). Qed.
Lemma lem1528840 (x : real) (y : real) : (term109 x y) = (term109 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem1528841 (x : real) (y : real) : ((term92 x y) = (term94 x y)) = ((term92 x y) = (term108 x y)).
Proof. exact (MK_COMB (@lem1528840 x y) (@lem1528839 x y)). Qed.
Lemma lem1528842 (x : real) (y : real) : (term92 x y) = (term108 x y).
Proof. exact (EQ_MP (@lem1528841 x y) (@lem1528830 x y)). Qed.
Lemma lem1528843 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (@lem1483527 (real_add x y) term39). Qed.
Lemma lem1528855 (x : real) (y : real) : (term112 x y) = (term113 x y).
Proof. exact (@lem1483519 (real_add x y) term39). Qed.
Lemma lem1528857 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528858 : term115 = term39.
Proof. exact (@lem1528857 term116). Qed.
Lemma lem1528859 (x : real) (y : real) : (term117 x y) = (term117 x y).
Proof. exact (eq_refl (term117 x y)). Qed.
Lemma lem1528860 (x : real) (y : real) : (term113 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1528859 x y) (@lem1528858)). Qed.
Lemma lem1528861 (x : real) (y : real) : (term118 x y) = (real_add x y).
Proof. exact (@lem1483450 (real_add x y)). Qed.
Lemma lem1528862 (x : real) (y : real) : (term113 x y) = (real_add x y).
Proof. exact (TRANS (@lem1528860 x y) (@lem1528861 x y)). Qed.
Lemma lem1528864 (x : real) (y : real) : (term112 x y) = (real_add x y).
Proof. exact (TRANS (@lem1528855 x y) (@lem1528862 x y)). Qed.
Lemma lem1528865 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1528866 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (MK_COMB (@lem1528865) (@lem1528864 x y)). Qed.
Lemma lem1528867 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528868 (x : real) (y : real) : (term111 x y) = (term110 x y).
Proof. exact (MK_COMB (@lem1528866 x y) (@lem1528867)). Qed.
Lemma lem1528869 (x : real) (y : real) : (term110 x y) = (term110 x y).
Proof. exact (TRANS (@lem1528843 x y) (@lem1528868 x y)). Qed.
Lemma lem1528870 (x : real) (y : real) : (term121 x y) = (term122 x y).
Proof. exact (@lem1483525 (term123 x y) term39). Qed.
Lemma lem1528871 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528889 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (@lem1483484 x (term59 y) y). Qed.
Lemma lem1528890 (y : real) : (term126 y) = (term127 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1528892 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1528893 : term129 = term39.
Proof. exact (@lem1528892 term116). Qed.
Lemma lem1528894 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1528895 : term130 = term131.
Proof. exact (MK_COMB (@lem1528894) (@lem1528893)). Qed.
Lemma lem1528896 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1528897 (y : real) : (term127 y) = (term132 y).
Proof. exact (MK_COMB (@lem1528895) (@lem1528896 y)). Qed.
Lemma lem1528898 (y : real) : (term126 y) = (term132 y).
Proof. exact (TRANS (@lem1528890 y) (@lem1528897 y)). Qed.
Lemma lem1528899 (y : real) : (term132 y) = term39.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1528900 (y : real) : (term126 y) = term39.
Proof. exact (TRANS (@lem1528898 y) (@lem1528899 y)). Qed.
Lemma lem1528901 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1528902 (y : real) (x : real) : (term125 x y) = (term133 x).
Proof. exact (MK_COMB (@lem1528901 x) (@lem1528900 y)). Qed.
Lemma lem1528903 (y : real) (x : real) : (term124 x y) = (term133 x).
Proof. exact (TRANS (@lem1528889 x y) (@lem1528902 y x)). Qed.
Lemma lem1528904 (x : real) : (term133 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1528906 (y : real) (x : real) : (term124 x y) = x.
Proof. exact (TRANS (@lem1528903 y x) (@lem1528904 x)). Qed.
Lemma lem1528915 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1528916 (y : real) (x : real) : (term123 x y) = (term126 x).
Proof. exact (MK_COMB (@lem1528915 x) (@lem1528906 y x)). Qed.
Lemma lem1528917 (x : real) : (term126 x) = (term127 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1528919 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1528920 : term129 = term39.
Proof. exact (@lem1528919 term116). Qed.
Lemma lem1528921 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1528922 : term130 = term131.
Proof. exact (MK_COMB (@lem1528921) (@lem1528920)). Qed.
Lemma lem1528923 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1528924 (x : real) : (term127 x) = (term132 x).
Proof. exact (MK_COMB (@lem1528922) (@lem1528923 x)). Qed.
Lemma lem1528925 (x : real) : (term126 x) = (term132 x).
Proof. exact (TRANS (@lem1528917 x) (@lem1528924 x)). Qed.
Lemma lem1528926 (x : real) : (term132 x) = term39.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1528927 (x : real) : (term126 x) = term39.
Proof. exact (TRANS (@lem1528925 x) (@lem1528926 x)). Qed.
Lemma lem1528928 (x : real) (y : real) : (term123 x y) = term39.
Proof. exact (TRANS (@lem1528916 y x) (@lem1528927 x)). Qed.
Lemma lem1528929 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1528930 (x : real) (y : real) : (term134 x y) = term135.
Proof. exact (MK_COMB (@lem1528929) (@lem1528928 x y)). Qed.
Lemma lem1528931 (x : real) (y : real) : (term136 x y) = term137.
Proof. exact (MK_COMB (@lem1528930 x y) (@lem1528871)). Qed.
Lemma lem1528932 : term137 = term138.
Proof. exact (@lem1483519 term39 term39). Qed.
Lemma lem1528934 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1528935 : term115 = term39.
Proof. exact (@lem1528934 term116). Qed.
Lemma lem1528936 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem1528937 : term138 = term140.
Proof. exact (MK_COMB (@lem1528936) (@lem1528935)). Qed.
Lemma lem1528938 : term140 = term39.
Proof. exact (@lem1483448 term39). Qed.
Lemma lem1528939 : term138 = term39.
Proof. exact (TRANS (@lem1528937) (@lem1528938)). Qed.
Lemma lem1528940 : term137 = term39.
Proof. exact (TRANS (@lem1528932) (@lem1528939)). Qed.
Lemma lem1528941 (x : real) (y : real) : (term136 x y) = term39.
Proof. exact (TRANS (@lem1528931 x y) (@lem1528940)). Qed.
Lemma lem1528942 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1528943 (x : real) (y : real) : (term141 x y) = term142.
Proof. exact (MK_COMB (@lem1528942) (@lem1528941 x y)). Qed.
Lemma lem1528944 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528945 (x : real) (y : real) : (term122 x y) = term143.
Proof. exact (MK_COMB (@lem1528943 x y) (@lem1528944)). Qed.
Lemma lem1528946 (x : real) (y : real) : (term121 x y) = term143.
Proof. exact (TRANS (@lem1528870 x y) (@lem1528945 x y)). Qed.
Lemma lem1528947 (x : real) (y : real) : (term144 x y) = (term145 x y).
Proof. exact (@lem1483525 (term146 x y) term39). Qed.
Lemma lem1528948 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1528960 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (@lem1483484 x y y). Qed.
Lemma lem1528961 (y : real) : (real_add y y) = (term149 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1528962 : term150 = term151.
Proof. exact (@lem1367770 term116 term116). Qed.
Lemma lem1528963 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1528964 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1528965 : term154 = term155.
Proof. exact (EQ_MP (@lem1528964) (@lem1528963)). Qed.
Lemma lem1528966 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1528967 : term151 = term156.
Proof. exact (MK_COMB (@lem1528966) (@lem1528965)). Qed.
Lemma lem1528968 : term150 = term156.
Proof. exact (TRANS (@lem1528962) (@lem1528967)). Qed.
Lemma lem1528969 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1528970 : term157 = term158.
Proof. exact (MK_COMB (@lem1528969) (@lem1528968)). Qed.
Lemma lem1528971 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1528972 (y : real) : (term149 y) = (term159 y).
Proof. exact (MK_COMB (@lem1528970) (@lem1528971 y)). Qed.
Lemma lem1528973 (y : real) : (real_add y y) = (term159 y).
Proof. exact (TRANS (@lem1528961 y) (@lem1528972 y)). Qed.
Lemma lem1528974 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1528975 (x : real) (y : real) : (term148 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1528974 x) (@lem1528973 y)). Qed.
Lemma lem1528977 (x : real) (y : real) : (term147 x y) = (term160 x y).
Proof. exact (TRANS (@lem1528960 x y) (@lem1528975 x y)). Qed.
Lemma lem1528986 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1528987 (x : real) (y : real) : (term146 x y) = (term161 x y).
Proof. exact (MK_COMB (@lem1528986 x) (@lem1528977 x y)). Qed.
Lemma lem1528988 (x : real) (y : real) : (term161 x y) = (term162 x y).
Proof. exact (@lem1483490 (term59 x) x (term159 y)). Qed.
Lemma lem1528989 (x : real) : (term126 x) = (term127 x).
Proof. exact (@lem1483440 term28 x). Qed.
Lemma lem1528991 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1528992 : term129 = term39.
Proof. exact (@lem1528991 term116). Qed.
Lemma lem1528993 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1528994 : term130 = term131.
Proof. exact (MK_COMB (@lem1528993) (@lem1528992)). Qed.
Lemma lem1528995 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1528996 (x : real) : (term127 x) = (term132 x).
Proof. exact (MK_COMB (@lem1528994) (@lem1528995 x)). Qed.
Lemma lem1528997 (x : real) : (term126 x) = (term132 x).
Proof. exact (TRANS (@lem1528989 x) (@lem1528996 x)). Qed.
Lemma lem1528998 (x : real) : (term132 x) = term39.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1528999 (x : real) : (term126 x) = term39.
Proof. exact (TRANS (@lem1528997 x) (@lem1528998 x)). Qed.
Lemma lem1529000 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1529001 (x : real) : (term163 x) = term139.
Proof. exact (MK_COMB (@lem1529000) (@lem1528999 x)). Qed.
Lemma lem1529002 (y : real) : (term159 y) = (term159 y).
Proof. exact (eq_refl (term159 y)). Qed.
Lemma lem1529003 (x : real) (y : real) : (term162 x y) = (term164 y).
Proof. exact (MK_COMB (@lem1529001 x) (@lem1529002 y)). Qed.
Lemma lem1529004 (x : real) (y : real) : (term161 x y) = (term164 y).
Proof. exact (TRANS (@lem1528988 x y) (@lem1529003 x y)). Qed.
Lemma lem1529005 (y : real) : (term164 y) = (term159 y).
Proof. exact (@lem1483448 (term159 y)). Qed.
Lemma lem1529006 (x : real) (y : real) : (term161 x y) = (term159 y).
Proof. exact (TRANS (@lem1529004 x y) (@lem1529005 y)). Qed.
Lemma lem1529007 (x : real) (y : real) : (term146 x y) = (term159 y).
Proof. exact (TRANS (@lem1528987 x y) (@lem1529006 x y)). Qed.
Lemma lem1529008 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1529009 (x : real) (y : real) : (term165 x y) = (term166 y).
Proof. exact (MK_COMB (@lem1529008) (@lem1529007 x y)). Qed.
Lemma lem1529010 (x : real) (y : real) : (term167 x y) = (term168 y).
Proof. exact (MK_COMB (@lem1529009 x y) (@lem1528948)). Qed.
Lemma lem1529011 (y : real) : (term168 y) = (term169 y).
Proof. exact (@lem1483519 (term159 y) term39). Qed.
Lemma lem1529013 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1529014 : term115 = term39.
Proof. exact (@lem1529013 term116). Qed.
Lemma lem1529015 (y : real) : (term170 y) = (term170 y).
Proof. exact (eq_refl (term170 y)). Qed.
Lemma lem1529016 (y : real) : (term169 y) = (term171 y).
Proof. exact (MK_COMB (@lem1529015 y) (@lem1529014)). Qed.
Lemma lem1529017 (y : real) : (term171 y) = (term159 y).
Proof. exact (@lem1483450 (term159 y)). Qed.
Lemma lem1529018 (y : real) : (term169 y) = (term159 y).
Proof. exact (TRANS (@lem1529016 y) (@lem1529017 y)). Qed.
Lemma lem1529019 (y : real) : (term168 y) = (term159 y).
Proof. exact (TRANS (@lem1529011 y) (@lem1529018 y)). Qed.
Lemma lem1529020 (x : real) (y : real) : (term167 x y) = (term159 y).
Proof. exact (TRANS (@lem1529010 x y) (@lem1529019 y)). Qed.
Lemma lem1529021 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529022 (x : real) (y : real) : (term172 x y) = (term173 y).
Proof. exact (MK_COMB (@lem1529021) (@lem1529020 x y)). Qed.
Lemma lem1529023 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529024 (x : real) (y : real) : (term145 x y) = (term174 y).
Proof. exact (MK_COMB (@lem1529022 x y) (@lem1529023)). Qed.
Lemma lem1529025 (x : real) (y : real) : (term144 x y) = (term174 y).
Proof. exact (TRANS (@lem1528947 x y) (@lem1529024 x y)). Qed.
Lemma lem1529026 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529027 (x : real) (y : real) : (term175 x y) = term176.
Proof. exact (MK_COMB (@lem1529026) (@lem1528946 x y)). Qed.
Lemma lem1529028 (x : real) (y : real) : (term177 x y) = (term178 y).
Proof. exact (MK_COMB (@lem1529027 x y) (@lem1529025 x y)). Qed.
Lemma lem1529029 (x : real) (y : real) : (term179 x y) = (term180 x y).
Proof. exact (@lem1483525 (term181 x y) term39). Qed.
Lemma lem1529030 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529048 (x : real) (y : real) : (term124 x y) = (term125 x y).
Proof. exact (@lem1483484 x (term59 y) y). Qed.
Lemma lem1529049 (y : real) : (term126 y) = (term127 y).
Proof. exact (@lem1483440 term28 y). Qed.
Lemma lem1529051 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1529052 : term129 = term39.
Proof. exact (@lem1529051 term116). Qed.
Lemma lem1529053 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529054 : term130 = term131.
Proof. exact (MK_COMB (@lem1529053) (@lem1529052)). Qed.
Lemma lem1529055 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1529056 (y : real) : (term127 y) = (term132 y).
Proof. exact (MK_COMB (@lem1529054) (@lem1529055 y)). Qed.
Lemma lem1529057 (y : real) : (term126 y) = (term132 y).
Proof. exact (TRANS (@lem1529049 y) (@lem1529056 y)). Qed.
Lemma lem1529058 (y : real) : (term132 y) = term39.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1529059 (y : real) : (term126 y) = term39.
Proof. exact (TRANS (@lem1529057 y) (@lem1529058 y)). Qed.
Lemma lem1529060 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1529061 (y : real) (x : real) : (term125 x y) = (term133 x).
Proof. exact (MK_COMB (@lem1529060 x) (@lem1529059 y)). Qed.
Lemma lem1529062 (y : real) (x : real) : (term124 x y) = (term133 x).
Proof. exact (TRANS (@lem1529048 x y) (@lem1529061 y x)). Qed.
Lemma lem1529063 (x : real) : (term133 x) = x.
Proof. exact (@lem1483450 x). Qed.
Lemma lem1529065 (y : real) (x : real) : (term124 x y) = x.
Proof. exact (TRANS (@lem1529062 y x) (@lem1529063 x)). Qed.
Lemma lem1529068 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1529069 (y : real) (x : real) : (term181 x y) = (real_add x x).
Proof. exact (MK_COMB (@lem1529068 x) (@lem1529065 y x)). Qed.
Lemma lem1529070 (x : real) : (real_add x x) = (term149 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1529071 : term150 = term151.
Proof. exact (@lem1367770 term116 term116). Qed.
Lemma lem1529072 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1529073 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1529074 : term154 = term155.
Proof. exact (EQ_MP (@lem1529073) (@lem1529072)). Qed.
Lemma lem1529075 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529076 : term151 = term156.
Proof. exact (MK_COMB (@lem1529075) (@lem1529074)). Qed.
Lemma lem1529077 : term150 = term156.
Proof. exact (TRANS (@lem1529071) (@lem1529076)). Qed.
Lemma lem1529078 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529079 : term157 = term158.
Proof. exact (MK_COMB (@lem1529078) (@lem1529077)). Qed.
Lemma lem1529080 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1529081 (x : real) : (term149 x) = (term159 x).
Proof. exact (MK_COMB (@lem1529079) (@lem1529080 x)). Qed.
Lemma lem1529082 (x : real) : (real_add x x) = (term159 x).
Proof. exact (TRANS (@lem1529070 x) (@lem1529081 x)). Qed.
Lemma lem1529083 (y : real) (x : real) : (term181 x y) = (term159 x).
Proof. exact (TRANS (@lem1529069 y x) (@lem1529082 x)). Qed.
Lemma lem1529084 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1529085 (y : real) (x : real) : (term182 x y) = (term166 x).
Proof. exact (MK_COMB (@lem1529084) (@lem1529083 y x)). Qed.
Lemma lem1529086 (y : real) (x : real) : (term183 x y) = (term168 x).
Proof. exact (MK_COMB (@lem1529085 y x) (@lem1529030)). Qed.
Lemma lem1529087 (x : real) : (term168 x) = (term169 x).
Proof. exact (@lem1483519 (term159 x) term39). Qed.
Lemma lem1529089 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1529090 : term115 = term39.
Proof. exact (@lem1529089 term116). Qed.
Lemma lem1529091 (x : real) : (term170 x) = (term170 x).
Proof. exact (eq_refl (term170 x)). Qed.
Lemma lem1529092 (x : real) : (term169 x) = (term171 x).
Proof. exact (MK_COMB (@lem1529091 x) (@lem1529090)). Qed.
Lemma lem1529093 (x : real) : (term171 x) = (term159 x).
Proof. exact (@lem1483450 (term159 x)). Qed.
Lemma lem1529094 (x : real) : (term169 x) = (term159 x).
Proof. exact (TRANS (@lem1529092 x) (@lem1529093 x)). Qed.
Lemma lem1529095 (x : real) : (term168 x) = (term159 x).
Proof. exact (TRANS (@lem1529087 x) (@lem1529094 x)). Qed.
Lemma lem1529096 (y : real) (x : real) : (term183 x y) = (term159 x).
Proof. exact (TRANS (@lem1529086 y x) (@lem1529095 x)). Qed.
Lemma lem1529097 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529098 (y : real) (x : real) : (term184 x y) = (term173 x).
Proof. exact (MK_COMB (@lem1529097) (@lem1529096 y x)). Qed.
Lemma lem1529099 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529100 (y : real) (x : real) : (term180 x y) = (term174 x).
Proof. exact (MK_COMB (@lem1529098 y x) (@lem1529099)). Qed.
Lemma lem1529101 (y : real) (x : real) : (term179 x y) = (term174 x).
Proof. exact (TRANS (@lem1529029 x y) (@lem1529100 y x)). Qed.
Lemma lem1529102 (x : real) (y : real) : (term185 x y) = (term186 x y).
Proof. exact (@lem1483525 (term187 x y) term39). Qed.
Lemma lem1529103 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529115 (x : real) (y : real) : (term147 x y) = (term148 x y).
Proof. exact (@lem1483484 x y y). Qed.
Lemma lem1529116 (y : real) : (real_add y y) = (term149 y).
Proof. exact (@lem1483444 y). Qed.
Lemma lem1529117 : term150 = term151.
Proof. exact (@lem1367770 term116 term116). Qed.
Lemma lem1529118 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1529119 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1529120 : term154 = term155.
Proof. exact (EQ_MP (@lem1529119) (@lem1529118)). Qed.
Lemma lem1529121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529122 : term151 = term156.
Proof. exact (MK_COMB (@lem1529121) (@lem1529120)). Qed.
Lemma lem1529123 : term150 = term156.
Proof. exact (TRANS (@lem1529117) (@lem1529122)). Qed.
Lemma lem1529124 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529125 : term157 = term158.
Proof. exact (MK_COMB (@lem1529124) (@lem1529123)). Qed.
Lemma lem1529126 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1529127 (y : real) : (term149 y) = (term159 y).
Proof. exact (MK_COMB (@lem1529125) (@lem1529126 y)). Qed.
Lemma lem1529128 (y : real) : (real_add y y) = (term159 y).
Proof. exact (TRANS (@lem1529116 y) (@lem1529127 y)). Qed.
Lemma lem1529129 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1529130 (x : real) (y : real) : (term148 x y) = (term160 x y).
Proof. exact (MK_COMB (@lem1529129 x) (@lem1529128 y)). Qed.
Lemma lem1529132 (x : real) (y : real) : (term147 x y) = (term160 x y).
Proof. exact (TRANS (@lem1529115 x y) (@lem1529130 x y)). Qed.
Lemma lem1529135 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1529136 (x : real) (y : real) : (term187 x y) = (term188 x y).
Proof. exact (MK_COMB (@lem1529135 x) (@lem1529132 x y)). Qed.
Lemma lem1529137 (x : real) (y : real) : (term188 x y) = (term189 x y).
Proof. exact (@lem1483490 x x (term159 y)). Qed.
Lemma lem1529138 (x : real) : (real_add x x) = (term149 x).
Proof. exact (@lem1483444 x). Qed.
Lemma lem1529139 : term150 = term151.
Proof. exact (@lem1367770 term116 term116). Qed.
Lemma lem1529140 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1529141 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1529142 : term154 = term155.
Proof. exact (EQ_MP (@lem1529141) (@lem1529140)). Qed.
Lemma lem1529143 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529144 : term151 = term156.
Proof. exact (MK_COMB (@lem1529143) (@lem1529142)). Qed.
Lemma lem1529145 : term150 = term156.
Proof. exact (TRANS (@lem1529139) (@lem1529144)). Qed.
Lemma lem1529146 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529147 : term157 = term158.
Proof. exact (MK_COMB (@lem1529146) (@lem1529145)). Qed.
Lemma lem1529148 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1529149 (x : real) : (term149 x) = (term159 x).
Proof. exact (MK_COMB (@lem1529147) (@lem1529148 x)). Qed.
Lemma lem1529150 (x : real) : (real_add x x) = (term159 x).
Proof. exact (TRANS (@lem1529138 x) (@lem1529149 x)). Qed.
Lemma lem1529151 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1529152 (x : real) : (term190 x) = (term170 x).
Proof. exact (MK_COMB (@lem1529151) (@lem1529150 x)). Qed.
Lemma lem1529153 (y : real) : (term159 y) = (term159 y).
Proof. exact (eq_refl (term159 y)). Qed.
Lemma lem1529154 (x : real) (y : real) : (term189 x y) = (term191 x y).
Proof. exact (MK_COMB (@lem1529152 x) (@lem1529153 y)). Qed.
Lemma lem1529155 (x : real) (y : real) : (term188 x y) = (term191 x y).
Proof. exact (TRANS (@lem1529137 x y) (@lem1529154 x y)). Qed.
Lemma lem1529156 (x : real) (y : real) : (term187 x y) = (term191 x y).
Proof. exact (TRANS (@lem1529136 x y) (@lem1529155 x y)). Qed.
Lemma lem1529157 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1529158 (x : real) (y : real) : (term192 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem1529157) (@lem1529156 x y)). Qed.
Lemma lem1529159 (x : real) (y : real) : (term194 x y) = (term195 x y).
Proof. exact (MK_COMB (@lem1529158 x y) (@lem1529103)). Qed.
Lemma lem1529160 (x : real) (y : real) : (term195 x y) = (term196 x y).
Proof. exact (@lem1483519 (term191 x y) term39). Qed.
Lemma lem1529162 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1529163 : term115 = term39.
Proof. exact (@lem1529162 term116). Qed.
Lemma lem1529164 (x : real) (y : real) : (term197 x y) = (term197 x y).
Proof. exact (eq_refl (term197 x y)). Qed.
Lemma lem1529165 (x : real) (y : real) : (term196 x y) = (term198 x y).
Proof. exact (MK_COMB (@lem1529164 x y) (@lem1529163)). Qed.
Lemma lem1529166 (x : real) (y : real) : (term198 x y) = (term191 x y).
Proof. exact (@lem1483450 (term191 x y)). Qed.
Lemma lem1529167 (x : real) (y : real) : (term196 x y) = (term191 x y).
Proof. exact (TRANS (@lem1529165 x y) (@lem1529166 x y)). Qed.
Lemma lem1529168 (x : real) (y : real) : (term195 x y) = (term191 x y).
Proof. exact (TRANS (@lem1529160 x y) (@lem1529167 x y)). Qed.
Lemma lem1529169 (x : real) (y : real) : (term194 x y) = (term191 x y).
Proof. exact (TRANS (@lem1529159 x y) (@lem1529168 x y)). Qed.
Lemma lem1529170 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529171 (x : real) (y : real) : (term199 x y) = (term200 x y).
Proof. exact (MK_COMB (@lem1529170) (@lem1529169 x y)). Qed.
Lemma lem1529172 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529173 (x : real) (y : real) : (term186 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1529171 x y) (@lem1529172)). Qed.
Lemma lem1529174 (x : real) (y : real) : (term185 x y) = (term201 x y).
Proof. exact (TRANS (@lem1529102 x y) (@lem1529173 x y)). Qed.
Lemma lem1529175 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529176 (y : real) (x : real) : (term202 x y) = (term203 x).
Proof. exact (MK_COMB (@lem1529175) (@lem1529101 y x)). Qed.
Lemma lem1529177 (x : real) (y : real) : (term204 x y) = (term205 x y).
Proof. exact (MK_COMB (@lem1529176 y x) (@lem1529174 x y)). Qed.
Lemma lem1529178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529179 (x : real) (y : real) : (term206 x y) = (term207 y).
Proof. exact (MK_COMB (@lem1529178) (@lem1529028 x y)). Qed.
Lemma lem1529180 (x : real) (y : real) : (term102 x y) = (term208 x y).
Proof. exact (MK_COMB (@lem1529179 x y) (@lem1529177 x y)). Qed.
Lemma lem1529181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529182 (x : real) (y : real) : (term103 x y) = (term103 x y).
Proof. exact (MK_COMB (@lem1529181) (@lem1528869 x y)). Qed.
Lemma lem1529183 (x : real) (y : real) : (term105 x y) = (term209 x y).
Proof. exact (MK_COMB (@lem1529182 x y) (@lem1529180 x y)). Qed.
Lemma lem1529184 (x : real) (y : real) : (term210 x y) = (term211 x y).
Proof. exact (@lem1483525 term39 (real_add x y)). Qed.
Lemma lem1529196 (x : real) (y : real) : (term212 x y) = (term213 x y).
Proof. exact (@lem1483519 term39 (real_add x y)). Qed.
Lemma lem1529203 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483508 x term28 y). Qed.
Lemma lem1529204 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem1529205 (x : real) (y : real) : (term213 x y) = (term216 x y).
Proof. exact (MK_COMB (@lem1529204) (@lem1529203 x y)). Qed.
Lemma lem1529206 (x : real) (y : real) : (term216 x y) = (term215 x y).
Proof. exact (@lem1483448 (term215 x y)). Qed.
Lemma lem1529207 (x : real) (y : real) : (term213 x y) = (term215 x y).
Proof. exact (TRANS (@lem1529205 x y) (@lem1529206 x y)). Qed.
Lemma lem1529209 (x : real) (y : real) : (term212 x y) = (term215 x y).
Proof. exact (TRANS (@lem1529196 x y) (@lem1529207 x y)). Qed.
Lemma lem1529210 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529211 (x : real) (y : real) : (term217 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem1529210) (@lem1529209 x y)). Qed.
Lemma lem1529212 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529213 (x : real) (y : real) : (term211 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1529211 x y) (@lem1529212)). Qed.
Lemma lem1529214 (x : real) (y : real) : (term210 x y) = (term219 x y).
Proof. exact (TRANS (@lem1529184 x y) (@lem1529213 x y)). Qed.
Lemma lem1529215 (x : real) (y : real) : (term220 x y) = (term221 x y).
Proof. exact (@lem1483525 (term222 x y) term39). Qed.
Lemma lem1529216 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529226 (x : real) (y : real) : (term223 x y) = (term214 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1529233 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483508 x term28 y). Qed.
Lemma lem1529235 (x : real) (y : real) : (term223 x y) = (term215 x y).
Proof. exact (TRANS (@lem1529226 x y) (@lem1529233 x y)). Qed.
Lemma lem1529244 (y : real) : (term73 y) = (term73 y).
Proof. exact (eq_refl (term73 y)). Qed.
Lemma lem1529245 (x : real) (y : real) : (term224 x y) = (term225 x y).
Proof. exact (MK_COMB (@lem1529244 y) (@lem1529235 x y)). Qed.
Lemma lem1529246 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (@lem1483484 (term59 x) (term59 y) (term59 y)). Qed.
Lemma lem1529247 (y : real) : (term227 y) = (term228 y).
Proof. exact (@lem1483438 term28 term28 y). Qed.
Lemma lem1529248 : term229 = term230.
Proof. exact (@lem1367763 term116 term116). Qed.
Lemma lem1529249 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1529250 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1529251 : term154 = term155.
Proof. exact (EQ_MP (@lem1529250) (@lem1529249)). Qed.
Lemma lem1529252 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529253 : term151 = term156.
Proof. exact (MK_COMB (@lem1529252) (@lem1529251)). Qed.
Lemma lem1529254 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1529255 : term230 = term231.
Proof. exact (MK_COMB (@lem1529254) (@lem1529253)). Qed.
Lemma lem1529256 : term229 = term231.
Proof. exact (TRANS (@lem1529248) (@lem1529255)). Qed.
Lemma lem1529257 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529258 : term232 = term233.
Proof. exact (MK_COMB (@lem1529257) (@lem1529256)). Qed.
Lemma lem1529259 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1529260 (y : real) : (term228 y) = (term234 y).
Proof. exact (MK_COMB (@lem1529258) (@lem1529259 y)). Qed.
Lemma lem1529261 (y : real) : (term227 y) = (term234 y).
Proof. exact (TRANS (@lem1529247 y) (@lem1529260 y)). Qed.
Lemma lem1529262 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1529263 (x : real) (y : real) : (term226 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem1529262 x) (@lem1529261 y)). Qed.
Lemma lem1529264 (x : real) (y : real) : (term225 x y) = (term235 x y).
Proof. exact (TRANS (@lem1529246 x y) (@lem1529263 x y)). Qed.
Lemma lem1529265 (x : real) (y : real) : (term224 x y) = (term235 x y).
Proof. exact (TRANS (@lem1529245 x y) (@lem1529264 x y)). Qed.
Lemma lem1529274 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1529275 (x : real) (y : real) : (term222 x y) = (term236 x y).
Proof. exact (MK_COMB (@lem1529274 x) (@lem1529265 x y)). Qed.
Lemma lem1529276 (x : real) (y : real) : (term236 x y) = (term237 x y).
Proof. exact (@lem1483490 (term59 x) (term59 x) (term234 y)). Qed.
Lemma lem1529277 (x : real) : (term227 x) = (term228 x).
Proof. exact (@lem1483438 term28 term28 x). Qed.
Lemma lem1529278 : term229 = term230.
Proof. exact (@lem1367763 term116 term116). Qed.
Lemma lem1529279 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1529280 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1529281 : term154 = term155.
Proof. exact (EQ_MP (@lem1529280) (@lem1529279)). Qed.
Lemma lem1529282 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529283 : term151 = term156.
Proof. exact (MK_COMB (@lem1529282) (@lem1529281)). Qed.
Lemma lem1529284 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1529285 : term230 = term231.
Proof. exact (MK_COMB (@lem1529284) (@lem1529283)). Qed.
Lemma lem1529286 : term229 = term231.
Proof. exact (TRANS (@lem1529278) (@lem1529285)). Qed.
Lemma lem1529287 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529288 : term232 = term233.
Proof. exact (MK_COMB (@lem1529287) (@lem1529286)). Qed.
Lemma lem1529289 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1529290 (x : real) : (term228 x) = (term234 x).
Proof. exact (MK_COMB (@lem1529288) (@lem1529289 x)). Qed.
Lemma lem1529291 (x : real) : (term227 x) = (term234 x).
Proof. exact (TRANS (@lem1529277 x) (@lem1529290 x)). Qed.
Lemma lem1529292 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1529293 (x : real) : (term238 x) = (term239 x).
Proof. exact (MK_COMB (@lem1529292) (@lem1529291 x)). Qed.
Lemma lem1529294 (y : real) : (term234 y) = (term234 y).
Proof. exact (eq_refl (term234 y)). Qed.
Lemma lem1529295 (x : real) (y : real) : (term237 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1529293 x) (@lem1529294 y)). Qed.
Lemma lem1529296 (x : real) (y : real) : (term236 x y) = (term240 x y).
Proof. exact (TRANS (@lem1529276 x y) (@lem1529295 x y)). Qed.
Lemma lem1529297 (x : real) (y : real) : (term222 x y) = (term240 x y).
Proof. exact (TRANS (@lem1529275 x y) (@lem1529296 x y)). Qed.
Lemma lem1529298 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1529299 (x : real) (y : real) : (term241 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1529298) (@lem1529297 x y)). Qed.
Lemma lem1529300 (x : real) (y : real) : (term243 x y) = (term244 x y).
Proof. exact (MK_COMB (@lem1529299 x y) (@lem1529216)). Qed.
Lemma lem1529301 (x : real) (y : real) : (term244 x y) = (term245 x y).
Proof. exact (@lem1483519 (term240 x y) term39). Qed.
Lemma lem1529303 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1529304 : term115 = term39.
Proof. exact (@lem1529303 term116). Qed.
Lemma lem1529305 (x : real) (y : real) : (term246 x y) = (term246 x y).
Proof. exact (eq_refl (term246 x y)). Qed.
Lemma lem1529306 (x : real) (y : real) : (term245 x y) = (term247 x y).
Proof. exact (MK_COMB (@lem1529305 x y) (@lem1529304)). Qed.
Lemma lem1529307 (x : real) (y : real) : (term247 x y) = (term240 x y).
Proof. exact (@lem1483450 (term240 x y)). Qed.
Lemma lem1529308 (x : real) (y : real) : (term245 x y) = (term240 x y).
Proof. exact (TRANS (@lem1529306 x y) (@lem1529307 x y)). Qed.
Lemma lem1529309 (x : real) (y : real) : (term244 x y) = (term240 x y).
Proof. exact (TRANS (@lem1529301 x y) (@lem1529308 x y)). Qed.
Lemma lem1529310 (x : real) (y : real) : (term243 x y) = (term240 x y).
Proof. exact (TRANS (@lem1529300 x y) (@lem1529309 x y)). Qed.
Lemma lem1529311 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529312 (x : real) (y : real) : (term248 x y) = (term249 x y).
Proof. exact (MK_COMB (@lem1529311) (@lem1529310 x y)). Qed.
Lemma lem1529313 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529314 (x : real) (y : real) : (term221 x y) = (term250 x y).
Proof. exact (MK_COMB (@lem1529312 x y) (@lem1529313)). Qed.
Lemma lem1529315 (x : real) (y : real) : (term220 x y) = (term250 x y).
Proof. exact (TRANS (@lem1529215 x y) (@lem1529314 x y)). Qed.
Lemma lem1529316 (x : real) (y : real) : (term251 x y) = (term252 x y).
Proof. exact (@lem1483525 (term253 x y) term39). Qed.
Lemma lem1529317 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529327 (x : real) (y : real) : (term223 x y) = (term214 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1529334 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483508 x term28 y). Qed.
Lemma lem1529336 (x : real) (y : real) : (term223 x y) = (term215 x y).
Proof. exact (TRANS (@lem1529327 x y) (@lem1529334 x y)). Qed.
Lemma lem1529339 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1529340 (x : real) (y : real) : (term254 x y) = (term255 x y).
Proof. exact (MK_COMB (@lem1529339 y) (@lem1529336 x y)). Qed.
Lemma lem1529341 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (@lem1483484 (term59 x) y (term59 y)). Qed.
Lemma lem1529342 (y : real) : (term257 y) = (term127 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1529344 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1529345 : term129 = term39.
Proof. exact (@lem1529344 term116). Qed.
Lemma lem1529346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529347 : term130 = term131.
Proof. exact (MK_COMB (@lem1529346) (@lem1529345)). Qed.
Lemma lem1529348 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1529349 (y : real) : (term127 y) = (term132 y).
Proof. exact (MK_COMB (@lem1529347) (@lem1529348 y)). Qed.
Lemma lem1529350 (y : real) : (term257 y) = (term132 y).
Proof. exact (TRANS (@lem1529342 y) (@lem1529349 y)). Qed.
Lemma lem1529351 (y : real) : (term132 y) = term39.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1529352 (y : real) : (term257 y) = term39.
Proof. exact (TRANS (@lem1529350 y) (@lem1529351 y)). Qed.
Lemma lem1529353 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1529354 (y : real) (x : real) : (term256 x y) = (term258 x).
Proof. exact (MK_COMB (@lem1529353 x) (@lem1529352 y)). Qed.
Lemma lem1529355 (y : real) (x : real) : (term255 x y) = (term258 x).
Proof. exact (TRANS (@lem1529341 x y) (@lem1529354 y x)). Qed.
Lemma lem1529356 (x : real) : (term258 x) = (term59 x).
Proof. exact (@lem1483450 (term59 x)). Qed.
Lemma lem1529357 (y : real) (x : real) : (term255 x y) = (term59 x).
Proof. exact (TRANS (@lem1529355 y x) (@lem1529356 x)). Qed.
Lemma lem1529358 (y : real) (x : real) : (term254 x y) = (term59 x).
Proof. exact (TRANS (@lem1529340 x y) (@lem1529357 y x)). Qed.
Lemma lem1529367 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1529368 (y : real) (x : real) : (term253 x y) = (term227 x).
Proof. exact (MK_COMB (@lem1529367 x) (@lem1529358 y x)). Qed.
Lemma lem1529369 (x : real) : (term227 x) = (term228 x).
Proof. exact (@lem1483438 term28 term28 x). Qed.
Lemma lem1529370 : term229 = term230.
Proof. exact (@lem1367763 term116 term116). Qed.
Lemma lem1529371 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1529372 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1529373 : term154 = term155.
Proof. exact (EQ_MP (@lem1529372) (@lem1529371)). Qed.
Lemma lem1529374 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529375 : term151 = term156.
Proof. exact (MK_COMB (@lem1529374) (@lem1529373)). Qed.
Lemma lem1529376 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1529377 : term230 = term231.
Proof. exact (MK_COMB (@lem1529376) (@lem1529375)). Qed.
Lemma lem1529378 : term229 = term231.
Proof. exact (TRANS (@lem1529370) (@lem1529377)). Qed.
Lemma lem1529379 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529380 : term232 = term233.
Proof. exact (MK_COMB (@lem1529379) (@lem1529378)). Qed.
Lemma lem1529381 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1529382 (x : real) : (term228 x) = (term234 x).
Proof. exact (MK_COMB (@lem1529380) (@lem1529381 x)). Qed.
Lemma lem1529383 (x : real) : (term227 x) = (term234 x).
Proof. exact (TRANS (@lem1529369 x) (@lem1529382 x)). Qed.
Lemma lem1529384 (y : real) (x : real) : (term253 x y) = (term234 x).
Proof. exact (TRANS (@lem1529368 y x) (@lem1529383 x)). Qed.
Lemma lem1529385 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1529386 (y : real) (x : real) : (term259 x y) = (term260 x).
Proof. exact (MK_COMB (@lem1529385) (@lem1529384 y x)). Qed.
Lemma lem1529387 (y : real) (x : real) : (term261 x y) = (term262 x).
Proof. exact (MK_COMB (@lem1529386 y x) (@lem1529317)). Qed.
Lemma lem1529388 (x : real) : (term262 x) = (term263 x).
Proof. exact (@lem1483519 (term234 x) term39). Qed.
Lemma lem1529390 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1529391 : term115 = term39.
Proof. exact (@lem1529390 term116). Qed.
Lemma lem1529392 (x : real) : (term239 x) = (term239 x).
Proof. exact (eq_refl (term239 x)). Qed.
Lemma lem1529393 (x : real) : (term263 x) = (term264 x).
Proof. exact (MK_COMB (@lem1529392 x) (@lem1529391)). Qed.
Lemma lem1529394 (x : real) : (term264 x) = (term234 x).
Proof. exact (@lem1483450 (term234 x)). Qed.
Lemma lem1529395 (x : real) : (term263 x) = (term234 x).
Proof. exact (TRANS (@lem1529393 x) (@lem1529394 x)). Qed.
Lemma lem1529396 (x : real) : (term262 x) = (term234 x).
Proof. exact (TRANS (@lem1529388 x) (@lem1529395 x)). Qed.
Lemma lem1529397 (y : real) (x : real) : (term261 x y) = (term234 x).
Proof. exact (TRANS (@lem1529387 y x) (@lem1529396 x)). Qed.
Lemma lem1529398 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529399 (y : real) (x : real) : (term265 x y) = (term266 x).
Proof. exact (MK_COMB (@lem1529398) (@lem1529397 y x)). Qed.
Lemma lem1529400 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529401 (y : real) (x : real) : (term252 x y) = (term267 x).
Proof. exact (MK_COMB (@lem1529399 y x) (@lem1529400)). Qed.
Lemma lem1529402 (y : real) (x : real) : (term251 x y) = (term267 x).
Proof. exact (TRANS (@lem1529316 x y) (@lem1529401 y x)). Qed.
Lemma lem1529403 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529404 (x : real) (y : real) : (term268 x y) = (term269 x y).
Proof. exact (MK_COMB (@lem1529403) (@lem1529315 x y)). Qed.
Lemma lem1529405 (y : real) (x : real) : (term270 x y) = (term271 y x).
Proof. exact (MK_COMB (@lem1529404 x y) (@lem1529402 y x)). Qed.
Lemma lem1529406 (x : real) (y : real) : (term272 x y) = (term273 x y).
Proof. exact (@lem1483525 (term274 x y) term39). Qed.
Lemma lem1529407 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529417 (x : real) (y : real) : (term223 x y) = (term214 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1529424 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483508 x term28 y). Qed.
Lemma lem1529426 (x : real) (y : real) : (term223 x y) = (term215 x y).
Proof. exact (TRANS (@lem1529417 x y) (@lem1529424 x y)). Qed.
Lemma lem1529435 (y : real) : (term73 y) = (term73 y).
Proof. exact (eq_refl (term73 y)). Qed.
Lemma lem1529436 (x : real) (y : real) : (term224 x y) = (term225 x y).
Proof. exact (MK_COMB (@lem1529435 y) (@lem1529426 x y)). Qed.
Lemma lem1529437 (x : real) (y : real) : (term225 x y) = (term226 x y).
Proof. exact (@lem1483484 (term59 x) (term59 y) (term59 y)). Qed.
Lemma lem1529438 (y : real) : (term227 y) = (term228 y).
Proof. exact (@lem1483438 term28 term28 y). Qed.
Lemma lem1529439 : term229 = term230.
Proof. exact (@lem1367763 term116 term116). Qed.
Lemma lem1529440 : term152 = term153.
Proof. exact (@lem706885). Qed.
Lemma lem1529441 : (term152 = term153) = (term154 = term155).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term153). Qed.
Lemma lem1529442 : term154 = term155.
Proof. exact (EQ_MP (@lem1529441) (@lem1529440)). Qed.
Lemma lem1529443 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem1529444 : term151 = term156.
Proof. exact (MK_COMB (@lem1529443) (@lem1529442)). Qed.
Lemma lem1529445 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1529446 : term230 = term231.
Proof. exact (MK_COMB (@lem1529445) (@lem1529444)). Qed.
Lemma lem1529447 : term229 = term231.
Proof. exact (TRANS (@lem1529439) (@lem1529446)). Qed.
Lemma lem1529448 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529449 : term232 = term233.
Proof. exact (MK_COMB (@lem1529448) (@lem1529447)). Qed.
Lemma lem1529450 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1529451 (y : real) : (term228 y) = (term234 y).
Proof. exact (MK_COMB (@lem1529449) (@lem1529450 y)). Qed.
Lemma lem1529452 (y : real) : (term227 y) = (term234 y).
Proof. exact (TRANS (@lem1529438 y) (@lem1529451 y)). Qed.
Lemma lem1529453 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1529454 (x : real) (y : real) : (term226 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem1529453 x) (@lem1529452 y)). Qed.
Lemma lem1529455 (x : real) (y : real) : (term225 x y) = (term235 x y).
Proof. exact (TRANS (@lem1529437 x y) (@lem1529454 x y)). Qed.
Lemma lem1529456 (x : real) (y : real) : (term224 x y) = (term235 x y).
Proof. exact (TRANS (@lem1529436 x y) (@lem1529455 x y)). Qed.
Lemma lem1529459 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1529460 (x : real) (y : real) : (term274 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem1529459 x) (@lem1529456 x y)). Qed.
Lemma lem1529461 (x : real) (y : real) : (term275 x y) = (term276 x y).
Proof. exact (@lem1483490 x (term59 x) (term234 y)). Qed.
Lemma lem1529462 (x : real) : (term257 x) = (term127 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1529464 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1529465 : term129 = term39.
Proof. exact (@lem1529464 term116). Qed.
Lemma lem1529466 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529467 : term130 = term131.
Proof. exact (MK_COMB (@lem1529466) (@lem1529465)). Qed.
Lemma lem1529468 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1529469 (x : real) : (term127 x) = (term132 x).
Proof. exact (MK_COMB (@lem1529467) (@lem1529468 x)). Qed.
Lemma lem1529470 (x : real) : (term257 x) = (term132 x).
Proof. exact (TRANS (@lem1529462 x) (@lem1529469 x)). Qed.
Lemma lem1529471 (x : real) : (term132 x) = term39.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1529472 (x : real) : (term257 x) = term39.
Proof. exact (TRANS (@lem1529470 x) (@lem1529471 x)). Qed.
Lemma lem1529473 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1529474 (x : real) : (term277 x) = term139.
Proof. exact (MK_COMB (@lem1529473) (@lem1529472 x)). Qed.
Lemma lem1529475 (y : real) : (term234 y) = (term234 y).
Proof. exact (eq_refl (term234 y)). Qed.
Lemma lem1529476 (x : real) (y : real) : (term276 x y) = (term278 y).
Proof. exact (MK_COMB (@lem1529474 x) (@lem1529475 y)). Qed.
Lemma lem1529477 (x : real) (y : real) : (term275 x y) = (term278 y).
Proof. exact (TRANS (@lem1529461 x y) (@lem1529476 x y)). Qed.
Lemma lem1529478 (y : real) : (term278 y) = (term234 y).
Proof. exact (@lem1483448 (term234 y)). Qed.
Lemma lem1529479 (x : real) (y : real) : (term275 x y) = (term234 y).
Proof. exact (TRANS (@lem1529477 x y) (@lem1529478 y)). Qed.
Lemma lem1529480 (x : real) (y : real) : (term274 x y) = (term234 y).
Proof. exact (TRANS (@lem1529460 x y) (@lem1529479 x y)). Qed.
Lemma lem1529481 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1529482 (x : real) (y : real) : (term279 x y) = (term260 y).
Proof. exact (MK_COMB (@lem1529481) (@lem1529480 x y)). Qed.
Lemma lem1529483 (x : real) (y : real) : (term280 x y) = (term262 y).
Proof. exact (MK_COMB (@lem1529482 x y) (@lem1529407)). Qed.
Lemma lem1529484 (y : real) : (term262 y) = (term263 y).
Proof. exact (@lem1483519 (term234 y) term39). Qed.
Lemma lem1529486 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1529487 : term115 = term39.
Proof. exact (@lem1529486 term116). Qed.
Lemma lem1529488 (y : real) : (term239 y) = (term239 y).
Proof. exact (eq_refl (term239 y)). Qed.
Lemma lem1529489 (y : real) : (term263 y) = (term264 y).
Proof. exact (MK_COMB (@lem1529488 y) (@lem1529487)). Qed.
Lemma lem1529490 (y : real) : (term264 y) = (term234 y).
Proof. exact (@lem1483450 (term234 y)). Qed.
Lemma lem1529491 (y : real) : (term263 y) = (term234 y).
Proof. exact (TRANS (@lem1529489 y) (@lem1529490 y)). Qed.
Lemma lem1529492 (y : real) : (term262 y) = (term234 y).
Proof. exact (TRANS (@lem1529484 y) (@lem1529491 y)). Qed.
Lemma lem1529493 (x : real) (y : real) : (term280 x y) = (term234 y).
Proof. exact (TRANS (@lem1529483 x y) (@lem1529492 y)). Qed.
Lemma lem1529494 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529495 (x : real) (y : real) : (term281 x y) = (term266 y).
Proof. exact (MK_COMB (@lem1529494) (@lem1529493 x y)). Qed.
Lemma lem1529496 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529497 (x : real) (y : real) : (term273 x y) = (term267 y).
Proof. exact (MK_COMB (@lem1529495 x y) (@lem1529496)). Qed.
Lemma lem1529498 (x : real) (y : real) : (term272 x y) = (term267 y).
Proof. exact (TRANS (@lem1529406 x y) (@lem1529497 x y)). Qed.
Lemma lem1529499 (x : real) (y : real) : (term282 x y) = (term283 x y).
Proof. exact (@lem1483525 (term284 x y) term39). Qed.
Lemma lem1529500 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529510 (x : real) (y : real) : (term223 x y) = (term214 x y).
Proof. exact (@lem1483512 (real_add x y)). Qed.
Lemma lem1529517 (x : real) (y : real) : (term214 x y) = (term215 x y).
Proof. exact (@lem1483508 x term28 y). Qed.
Lemma lem1529519 (x : real) (y : real) : (term223 x y) = (term215 x y).
Proof. exact (TRANS (@lem1529510 x y) (@lem1529517 x y)). Qed.
Lemma lem1529522 (y : real) : (real_add y) = (real_add y).
Proof. exact (eq_refl (real_add y)). Qed.
Lemma lem1529523 (x : real) (y : real) : (term254 x y) = (term255 x y).
Proof. exact (MK_COMB (@lem1529522 y) (@lem1529519 x y)). Qed.
Lemma lem1529524 (x : real) (y : real) : (term255 x y) = (term256 x y).
Proof. exact (@lem1483484 (term59 x) y (term59 y)). Qed.
Lemma lem1529525 (y : real) : (term257 y) = (term127 y).
Proof. exact (@lem1483442 term28 y). Qed.
Lemma lem1529527 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1529528 : term129 = term39.
Proof. exact (@lem1529527 term116). Qed.
Lemma lem1529529 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529530 : term130 = term131.
Proof. exact (MK_COMB (@lem1529529) (@lem1529528)). Qed.
Lemma lem1529531 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1529532 (y : real) : (term127 y) = (term132 y).
Proof. exact (MK_COMB (@lem1529530) (@lem1529531 y)). Qed.
Lemma lem1529533 (y : real) : (term257 y) = (term132 y).
Proof. exact (TRANS (@lem1529525 y) (@lem1529532 y)). Qed.
Lemma lem1529534 (y : real) : (term132 y) = term39.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1529535 (y : real) : (term257 y) = term39.
Proof. exact (TRANS (@lem1529533 y) (@lem1529534 y)). Qed.
Lemma lem1529536 (x : real) : (term73 x) = (term73 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1529537 (y : real) (x : real) : (term256 x y) = (term258 x).
Proof. exact (MK_COMB (@lem1529536 x) (@lem1529535 y)). Qed.
Lemma lem1529538 (y : real) (x : real) : (term255 x y) = (term258 x).
Proof. exact (TRANS (@lem1529524 x y) (@lem1529537 y x)). Qed.
Lemma lem1529539 (x : real) : (term258 x) = (term59 x).
Proof. exact (@lem1483450 (term59 x)). Qed.
Lemma lem1529540 (y : real) (x : real) : (term255 x y) = (term59 x).
Proof. exact (TRANS (@lem1529538 y x) (@lem1529539 x)). Qed.
Lemma lem1529541 (y : real) (x : real) : (term254 x y) = (term59 x).
Proof. exact (TRANS (@lem1529523 x y) (@lem1529540 y x)). Qed.
Lemma lem1529544 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1529545 (y : real) (x : real) : (term284 x y) = (term257 x).
Proof. exact (MK_COMB (@lem1529544 x) (@lem1529541 y x)). Qed.
Lemma lem1529546 (x : real) : (term257 x) = (term127 x).
Proof. exact (@lem1483442 term28 x). Qed.
Lemma lem1529548 (m : nat) : (term128 m) = term39.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1529549 : term129 = term39.
Proof. exact (@lem1529548 term116). Qed.
Lemma lem1529550 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1529551 : term130 = term131.
Proof. exact (MK_COMB (@lem1529550) (@lem1529549)). Qed.
Lemma lem1529552 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1529553 (x : real) : (term127 x) = (term132 x).
Proof. exact (MK_COMB (@lem1529551) (@lem1529552 x)). Qed.
Lemma lem1529554 (x : real) : (term257 x) = (term132 x).
Proof. exact (TRANS (@lem1529546 x) (@lem1529553 x)). Qed.
Lemma lem1529555 (x : real) : (term132 x) = term39.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1529556 (x : real) : (term257 x) = term39.
Proof. exact (TRANS (@lem1529554 x) (@lem1529555 x)). Qed.
Lemma lem1529557 (x : real) (y : real) : (term284 x y) = term39.
Proof. exact (TRANS (@lem1529545 y x) (@lem1529556 x)). Qed.
Lemma lem1529558 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem1529559 (x : real) (y : real) : (term285 x y) = term135.
Proof. exact (MK_COMB (@lem1529558) (@lem1529557 x y)). Qed.
Lemma lem1529560 (x : real) (y : real) : (term286 x y) = term137.
Proof. exact (MK_COMB (@lem1529559 x y) (@lem1529500)). Qed.
Lemma lem1529561 : term137 = term138.
Proof. exact (@lem1483519 term39 term39). Qed.
Lemma lem1529563 (x : nat) : (term114 x) = term39.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem1529564 : term115 = term39.
Proof. exact (@lem1529563 term116). Qed.
Lemma lem1529565 : term139 = term139.
Proof. exact (eq_refl term139). Qed.
Lemma lem1529566 : term138 = term140.
Proof. exact (MK_COMB (@lem1529565) (@lem1529564)). Qed.
Lemma lem1529567 : term140 = term39.
Proof. exact (@lem1483448 term39). Qed.
Lemma lem1529568 : term138 = term39.
Proof. exact (TRANS (@lem1529566) (@lem1529567)). Qed.
Lemma lem1529569 : term137 = term39.
Proof. exact (TRANS (@lem1529561) (@lem1529568)). Qed.
Lemma lem1529570 (x : real) (y : real) : (term286 x y) = term39.
Proof. exact (TRANS (@lem1529560 x y) (@lem1529569)). Qed.
Lemma lem1529571 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1529572 (x : real) (y : real) : (term287 x y) = term142.
Proof. exact (MK_COMB (@lem1529571) (@lem1529570 x y)). Qed.
Lemma lem1529573 : term39 = term39.
Proof. exact (eq_refl term39). Qed.
Lemma lem1529574 (x : real) (y : real) : (term283 x y) = term143.
Proof. exact (MK_COMB (@lem1529572 x y) (@lem1529573)). Qed.
Lemma lem1529575 (x : real) (y : real) : (term282 x y) = term143.
Proof. exact (TRANS (@lem1529499 x y) (@lem1529574 x y)). Qed.
Lemma lem1529576 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529577 (x : real) (y : real) : (term288 x y) = (term289 y).
Proof. exact (MK_COMB (@lem1529576) (@lem1529498 x y)). Qed.
Lemma lem1529578 (x : real) (y : real) : (term290 x y) = (term291 y).
Proof. exact (MK_COMB (@lem1529577 x y) (@lem1529575 x y)). Qed.
Lemma lem1529579 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529580 (y : real) (x : real) : (term292 x y) = (term293 y x).
Proof. exact (MK_COMB (@lem1529579) (@lem1529405 y x)). Qed.
Lemma lem1529581 (x : real) (y : real) : (term97 x y) = (term294 x y).
Proof. exact (MK_COMB (@lem1529580 y x) (@lem1529578 x y)). Qed.
Lemma lem1529582 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1529583 (x : real) (y : real) : (term98 x y) = (term295 x y).
Proof. exact (MK_COMB (@lem1529582) (@lem1529214 x y)). Qed.
Lemma lem1529584 (x : real) (y : real) : (term100 x y) = (term296 x y).
Proof. exact (MK_COMB (@lem1529583 x y) (@lem1529581 x y)). Qed.
Lemma lem1529585 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1529586 (x : real) (y : real) : (term107 x y) = (term297 x y).
Proof. exact (MK_COMB (@lem1529585) (@lem1529183 x y)). Qed.
Lemma lem1529587 (x : real) (y : real) : (term108 x y) = (term298 x y).
Proof. exact (MK_COMB (@lem1529586 x y) (@lem1529584 x y)). Qed.
Lemma lem1529598 (x : real) (y : real) : (term92 x y) = (term298 x y).
Proof. exact (TRANS (@lem1528842 x y) (@lem1529587 x y)). Qed.
Lemma lem1529599 (x : real) (y : real) : (term40 x y) = (term298 x y).
Proof. exact (TRANS (@lem1528826 x y) (@lem1529598 x y)). Qed.
Lemma lem1529600 (x : real) (y : real) (h1 : term298 x y) : term298 x y.
Proof. exact (h1). Qed.
Lemma lem1529601 (x : real) (y : real) (h1 : term209 x y) : term209 x y.
Proof. exact (h1). Qed.
Lemma lem1529602 (x : real) (y : real) (h1 : term209 x y) : term208 x y.
Proof. exact (proj2 (@lem1529601 x y h1)). Qed.
Lemma lem1529605 (x : real) (y : real) (h1 : term209 x y) : term178 y.
Proof. exact (proj1 (@lem1529602 x y h1)). Qed.
Lemma lem1529607 (x : real) (y : real) (h1 : term209 x y) : term143.
Proof. exact (proj1 (@lem1529605 x y h1)). Qed.
Lemma lem1529611 (n : nat) (m : nat) : (term299 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1529612 : term143 = term300.
Proof. exact (@lem1529611 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1529613 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1529614 : term143 = False.
Proof. exact (TRANS (@lem1529612) (@lem1529613)). Qed.
Lemma lem1529615 (x : real) (y : real) (h1 : term209 x y) : False.
Proof. exact (EQ_MP (@lem1529614) (@lem1529607 x y h1)). Qed.
Lemma lem1529616 (x : real) (y : real) (h1 : term296 x y) : term296 x y.
Proof. exact (h1). Qed.
Lemma lem1529617 (x : real) (y : real) (h1 : term296 x y) : term294 x y.
Proof. exact (proj2 (@lem1529616 x y h1)). Qed.
Lemma lem1529619 (x : real) (y : real) (h1 : term296 x y) : term291 y.
Proof. exact (proj2 (@lem1529617 x y h1)). Qed.
Lemma lem1529623 (x : real) (y : real) (h1 : term296 x y) : term143.
Proof. exact (proj2 (@lem1529619 x y h1)). Qed.
Lemma lem1529626 (n : nat) (m : nat) : (term299 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1529627 : term143 = term300.
Proof. exact (@lem1529626 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1529628 : term300 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1529629 : term143 = False.
Proof. exact (TRANS (@lem1529627) (@lem1529628)). Qed.
Lemma lem1529630 (x : real) (y : real) (h1 : term296 x y) : False.
Proof. exact (EQ_MP (@lem1529629) (@lem1529623 x y h1)). Qed.
Lemma lem1529631 (x : real) (y : real) (h1 : term298 x y) : False.
Proof. exact (or_elim (@lem1529600 x y h1) (fun h0 : term209 x y => @lem1529615 x y h0) (fun h0 : term296 x y => @lem1529630 x y h0)). Qed.
Lemma lem1529632 (x : real) (y : real) (h1 : term40 x y) : term40 x y.
Proof. exact (h1). Qed.
Lemma lem1529633 (x : real) (y : real) (h1 : term40 x y) : term298 x y.
Proof. exact (EQ_MP (@lem1529599 x y) (@lem1529632 x y h1)). Qed.
Lemma lem1529634 (x : real) (y : real) (h1 : term40 x y) : (term298 x y) = False.
Proof. exact (prop_ext (fun h2 : term298 x y => @lem1529631 x y h2) (fun h2 : False => @lem1529633 x y h1)). Qed.
Lemma lem1529635 (x : real) (y : real) (h1 : term40 x y) : False.
Proof. exact (EQ_MP (@lem1529634 x y h1) (@lem1529633 x y h1)). Qed.
Lemma lem1529636 (x : real) (h1 : term42 x) : term42 x.
Proof. exact (h1). Qed.
Lemma lem1529637 (x : real) (h1 : term42 x) : False.
Proof. exact (ex_elim (@lem1529636 x h1) (fun y : real => fun h0 : term41 x y => @lem1529635 x y h0)). Qed.
Lemma lem1529638 (h1 : term44) : term44.
Proof. exact (h1). Qed.
Lemma lem1529639 (h1 : term44) : False.
Proof. exact (ex_elim (@lem1529638 h1) (fun x : real => fun h0 : term43 x => @lem1529637 x h0)). Qed.
Lemma lem1529640 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1529641 (h1 : term12) : term44.
Proof. exact (EQ_MP (@lem1528639) (@lem1529640 h1)). Qed.
Lemma lem1529642 (h1 : term12) : term44 = False.
Proof. exact (prop_ext (fun h2 : term44 => @lem1529639 h2) (fun h2 : False => @lem1529641 h1)). Qed.
Lemma lem1529643 (h1 : term12) : False.
Proof. exact (EQ_MP (@lem1529642 h1) (@lem1529641 h1)). Qed.
Lemma lem1529644 : term301.
Proof. exact (fun h0 : term12 => @lem1529643 h0). Qed.
Lemma lem1529645 : term302.
Proof. exact (@lem1386578 term303). Qed.
Lemma lem1529646 : term303.
Proof. exact (@lem1529645 (@lem1529644)). Qed.
