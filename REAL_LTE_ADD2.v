Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LTE_ADD2_term_abbrevs.
Require Import thm0_spec.
Require Import thm1009824_spec.
Require Import thm1010765_spec.
Require Import thm1366271_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1483440_spec.
Require Import thm1483442_spec.
Require Import thm1483446_spec.
Require Import thm1483448_spec.
Require Import thm1483460_spec.
Require Import thm1483480_spec.
Require Import thm1483482_spec.
Require Import thm1483484_spec.
Require Import thm1483488_spec.
Require Import thm1483490_spec.
Require Import thm1483508_spec.
Require Import thm1483519_spec.
Require Import thm1483521_spec.
Require Import thm1483523_spec.
Require Import thm1483531_spec.
Require Import thm1483568_spec.
Require Import thm1483584_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm912739_spec.
Lemma lem1518538 (w : real) (y : real) (x : real) (z : real) : (term0 w y x z) = (term1 w y x z).
Proof. exact (@lem17362 (term2 w x y z) (term3 w y x z)). Qed.
Lemma lem1518539 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518540 (w : real) (y : real) (x : real) : (term6 w y x) = (term7 w y x).
Proof. exact (@lem1518539 (term8 w y x)). Qed.
Lemma lem1518541 (w : real) (y : real) (x : real) (z : real) : (term9 w y x z) = (term10 w y x z).
Proof. exact (eq_refl (term9 w y x z)). Qed.
Lemma lem1518542 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518543 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term0 w y x z).
Proof. exact (MK_COMB (@lem1518542) (@lem1518541 w y x z)). Qed.
Lemma lem1518544 (w : real) (y : real) (x : real) (z : real) : (term11 w y x z) = (term1 w y x z).
Proof. exact (TRANS (@lem1518543 w y x z) (@lem1518538 w y x z)). Qed.
Lemma lem1518545 (w : real) (y : real) (x : real) : (term12 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1518544 w y x z)). Qed.
Lemma lem1518546 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518547 (w : real) (y : real) (x : real) : (term7 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1518546) (@lem1518545 w y x)). Qed.
Lemma lem1518548 (w : real) (y : real) (x : real) : (term6 w y x) = (term14 w y x).
Proof. exact (TRANS (@lem1518540 w y x) (@lem1518547 w y x)). Qed.
Lemma lem1518549 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518550 (w : real) (x : real) : (term15 w x) = (term16 w x).
Proof. exact (@lem1518549 (term17 w x)). Qed.
Lemma lem1518551 (w : real) (y : real) (x : real) : (term18 w x y) = (term19 w y x).
Proof. exact (eq_refl (term18 w x y)). Qed.
Lemma lem1518552 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518553 (w : real) (y : real) (x : real) : (term20 w x y) = (term6 w y x).
Proof. exact (MK_COMB (@lem1518552) (@lem1518551 w y x)). Qed.
Lemma lem1518554 (w : real) (y : real) (x : real) : (term20 w x y) = (term14 w y x).
Proof. exact (TRANS (@lem1518553 w y x) (@lem1518548 w y x)). Qed.
Lemma lem1518555 (w : real) (x : real) : (term21 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1518554 w y x)). Qed.
Lemma lem1518556 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518557 (w : real) (x : real) : (term16 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1518556) (@lem1518555 w x)). Qed.
Lemma lem1518558 (w : real) (x : real) : (term15 w x) = (term23 w x).
Proof. exact (TRANS (@lem1518550 w x) (@lem1518557 w x)). Qed.
Lemma lem1518559 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518560 (w : real) : (term24 w) = (term25 w).
Proof. exact (@lem1518559 (term26 w)). Qed.
Lemma lem1518561 (w : real) (x : real) : (term27 w x) = (term28 w x).
Proof. exact (eq_refl (term27 w x)). Qed.
Lemma lem1518562 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518563 (w : real) (x : real) : (term29 w x) = (term15 w x).
Proof. exact (MK_COMB (@lem1518562) (@lem1518561 w x)). Qed.
Lemma lem1518564 (w : real) (x : real) : (term29 w x) = (term23 w x).
Proof. exact (TRANS (@lem1518563 w x) (@lem1518558 w x)). Qed.
Lemma lem1518565 (w : real) : (term30 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1518564 w x)). Qed.
Lemma lem1518566 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518567 (w : real) : (term25 w) = (term32 w).
Proof. exact (MK_COMB (@lem1518566) (@lem1518565 w)). Qed.
Lemma lem1518568 (w : real) : (term24 w) = (term32 w).
Proof. exact (TRANS (@lem1518560 w) (@lem1518567 w)). Qed.
Lemma lem1518569 (P : real -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1518570 : term33 = term34.
Proof. exact (@lem1518569 term35). Qed.
Lemma lem1518571 (w : real) : (term36 w) = (term37 w).
Proof. exact (eq_refl (term36 w)). Qed.
Lemma lem1518572 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1518573 (w : real) : (term38 w) = (term24 w).
Proof. exact (MK_COMB (@lem1518572) (@lem1518571 w)). Qed.
Lemma lem1518574 (w : real) : (term38 w) = (term32 w).
Proof. exact (TRANS (@lem1518573 w) (@lem1518568 w)). Qed.
Lemma lem1518575 : term39 = term40.
Proof. exact (fun_ext (fun w : real => @lem1518574 w)). Qed.
Lemma lem1518576 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518577 : term34 = term41.
Proof. exact (MK_COMB (@lem1518576) (@lem1518575)). Qed.
Lemma lem1518579 : term33 = term41.
Proof. exact (TRANS (@lem1518570) (@lem1518577)). Qed.
Lemma lem1518590 (w : real) (y : real) (x : real) (z : real) : (term1 w y x z) = (term1 w y x z).
Proof. exact (eq_refl (term1 w y x z)). Qed.
Lemma lem1518591 (w : real) (y : real) (x : real) : (term13 w y x) = (term13 w y x).
Proof. exact (fun_ext (fun z : real => @lem1518590 w y x z)). Qed.
Lemma lem1518592 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518593 (w : real) (y : real) (x : real) : (term14 w y x) = (term14 w y x).
Proof. exact (MK_COMB (@lem1518592) (@lem1518591 w y x)). Qed.
Lemma lem1518594 (w : real) (x : real) : (term22 w x) = (term22 w x).
Proof. exact (fun_ext (fun y : real => @lem1518593 w y x)). Qed.
Lemma lem1518595 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518596 (w : real) (x : real) : (term23 w x) = (term23 w x).
Proof. exact (MK_COMB (@lem1518595) (@lem1518594 w x)). Qed.
Lemma lem1518597 (w : real) : (term31 w) = (term31 w).
Proof. exact (fun_ext (fun x : real => @lem1518596 w x)). Qed.
Lemma lem1518598 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518599 (w : real) : (term32 w) = (term32 w).
Proof. exact (MK_COMB (@lem1518598) (@lem1518597 w)). Qed.
Lemma lem1518600 : term40 = term40.
Proof. exact (fun_ext (fun w : real => @lem1518599 w)). Qed.
Lemma lem1518601 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518602 : term41 = term41.
Proof. exact (MK_COMB (@lem1518601) (@lem1518600)). Qed.
Lemma lem1518603 : term33 = term41.
Proof. exact (TRANS (@lem1518579) (@lem1518602)). Qed.
Lemma lem1518604 (x : real) (w : real) : (real_lt w x) = (term42 x w).
Proof. exact (@lem1483521 x w). Qed.
Lemma lem1518610 (x : real) (w : real) : (real_sub x w) = (term43 x w).
Proof. exact (@lem1483519 x w). Qed.
Lemma lem1518615 (w : real) (x : real) : (term43 x w) = (term44 w x).
Proof. exact (@lem1483488 (term45 w) x). Qed.
Lemma lem1518617 (w : real) (x : real) : (real_sub x w) = (term44 w x).
Proof. exact (TRANS (@lem1518610 x w) (@lem1518615 w x)). Qed.
Lemma lem1518618 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518619 (w : real) (x : real) : (term46 x w) = (term47 w x).
Proof. exact (MK_COMB (@lem1518618) (@lem1518617 w x)). Qed.
Lemma lem1518620 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518621 (w : real) (x : real) : (term42 x w) = (term49 w x).
Proof. exact (MK_COMB (@lem1518619 w x) (@lem1518620)). Qed.
Lemma lem1518622 (w : real) (x : real) : (real_lt w x) = (term49 w x).
Proof. exact (TRANS (@lem1518604 x w) (@lem1518621 w x)). Qed.
Lemma lem1518623 (z : real) (y : real) : (real_le y z) = (term50 z y).
Proof. exact (@lem1483523 z y). Qed.
Lemma lem1518629 (z : real) (y : real) : (real_sub z y) = (term43 z y).
Proof. exact (@lem1483519 z y). Qed.
Lemma lem1518634 (y : real) (z : real) : (term43 z y) = (term44 y z).
Proof. exact (@lem1483488 (term45 y) z). Qed.
Lemma lem1518636 (y : real) (z : real) : (real_sub z y) = (term44 y z).
Proof. exact (TRANS (@lem1518629 z y) (@lem1518634 y z)). Qed.
Lemma lem1518637 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518638 (y : real) (z : real) : (term51 z y) = (term52 y z).
Proof. exact (MK_COMB (@lem1518637) (@lem1518636 y z)). Qed.
Lemma lem1518639 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518640 (y : real) (z : real) : (term50 z y) = (term53 y z).
Proof. exact (MK_COMB (@lem1518638 y z) (@lem1518639)). Qed.
Lemma lem1518641 (y : real) (z : real) : (real_le y z) = (term53 y z).
Proof. exact (TRANS (@lem1518623 z y) (@lem1518640 y z)). Qed.
Lemma lem1518642 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1518643 (w : real) (x : real) : (term54 w x) = (term55 w x).
Proof. exact (MK_COMB (@lem1518642) (@lem1518622 w x)). Qed.
Lemma lem1518644 (w : real) (x : real) (y : real) (z : real) : (term2 w x y z) = (term56 w x y z).
Proof. exact (MK_COMB (@lem1518643 w x) (@lem1518641 y z)). Qed.
Lemma lem1518645 (w : real) (y : real) (x : real) (z : real) : (term57 w y x z) = (term58 w y x z).
Proof. exact (@lem1483531 (real_add w y) (real_add x z)). Qed.
Lemma lem1518663 (w : real) (y : real) (x : real) (z : real) : (term59 w y x z) = (term60 w y x z).
Proof. exact (@lem1483519 (real_add w y) (real_add x z)). Qed.
Lemma lem1518670 (x : real) (z : real) : (term61 x z) = (term62 x z).
Proof. exact (@lem1483508 x term63 z). Qed.
Lemma lem1518671 (w : real) (y : real) : (term64 w y) = (term64 w y).
Proof. exact (eq_refl (term64 w y)). Qed.
Lemma lem1518672 (w : real) (y : real) (x : real) (z : real) : (term60 w y x z) = (term65 w y x z).
Proof. exact (MK_COMB (@lem1518671 w y) (@lem1518670 x z)). Qed.
Lemma lem1518673 (w : real) (y : real) (x : real) (z : real) : (term65 w y x z) = (term66 w y x z).
Proof. exact (@lem1483482 w y (term62 x z)). Qed.
Lemma lem1518678 (x : real) (y : real) (z : real) : (term67 y x z) = (term68 x y z).
Proof. exact (@lem1483484 (term45 x) y (term45 z)). Qed.
Lemma lem1518679 (w : real) : (real_add w) = (real_add w).
Proof. exact (eq_refl (real_add w)). Qed.
Lemma lem1518680 (w : real) (x : real) (y : real) (z : real) : (term66 w y x z) = (term69 w x y z).
Proof. exact (MK_COMB (@lem1518679 w) (@lem1518678 x y z)). Qed.
Lemma lem1518681 (w : real) (x : real) (y : real) (z : real) : (term65 w y x z) = (term69 w x y z).
Proof. exact (TRANS (@lem1518673 w y x z) (@lem1518680 w x y z)). Qed.
Lemma lem1518682 (w : real) (x : real) (y : real) (z : real) : (term60 w y x z) = (term69 w x y z).
Proof. exact (TRANS (@lem1518672 w y x z) (@lem1518681 w x y z)). Qed.
Lemma lem1518684 (w : real) (x : real) (y : real) (z : real) : (term59 w y x z) = (term69 w x y z).
Proof. exact (TRANS (@lem1518663 w y x z) (@lem1518682 w x y z)). Qed.
Lemma lem1518685 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518686 (w : real) (x : real) (y : real) (z : real) : (term70 w y x z) = (term71 w x y z).
Proof. exact (MK_COMB (@lem1518685) (@lem1518684 w x y z)). Qed.
Lemma lem1518687 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518688 (w : real) (x : real) (y : real) (z : real) : (term58 w y x z) = (term72 w x y z).
Proof. exact (MK_COMB (@lem1518686 w x y z) (@lem1518687)). Qed.
Lemma lem1518689 (w : real) (x : real) (y : real) (z : real) : (term57 w y x z) = (term72 w x y z).
Proof. exact (TRANS (@lem1518645 w y x z) (@lem1518688 w x y z)). Qed.
Lemma lem1518690 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1518691 (w : real) (x : real) (y : real) (z : real) : (term73 w x y z) = (term74 w x y z).
Proof. exact (MK_COMB (@lem1518690) (@lem1518644 w x y z)). Qed.
Lemma lem1518692 (w : real) (x : real) (y : real) (z : real) : (term1 w y x z) = (term75 w x y z).
Proof. exact (MK_COMB (@lem1518691 w x y z) (@lem1518689 w x y z)). Qed.
Lemma lem1518693 (w : real) (x : real) (y : real) : (term13 w y x) = (term76 w x y).
Proof. exact (fun_ext (fun z : real => @lem1518692 w x y z)). Qed.
Lemma lem1518694 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518695 (w : real) (x : real) (y : real) : (term14 w y x) = (term77 w x y).
Proof. exact (MK_COMB (@lem1518694) (@lem1518693 w x y)). Qed.
Lemma lem1518696 (w : real) (x : real) : (term22 w x) = (term78 w x).
Proof. exact (fun_ext (fun y : real => @lem1518695 w x y)). Qed.
Lemma lem1518697 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518698 (w : real) (x : real) : (term23 w x) = (term79 w x).
Proof. exact (MK_COMB (@lem1518697) (@lem1518696 w x)). Qed.
Lemma lem1518699 (w : real) : (term31 w) = (term80 w).
Proof. exact (fun_ext (fun x : real => @lem1518698 w x)). Qed.
Lemma lem1518700 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518701 (w : real) : (term32 w) = (term81 w).
Proof. exact (MK_COMB (@lem1518700) (@lem1518699 w)). Qed.
Lemma lem1518702 : term40 = term82.
Proof. exact (fun_ext (fun w : real => @lem1518701 w)). Qed.
Lemma lem1518703 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518704 : term41 = term83.
Proof. exact (MK_COMB (@lem1518703) (@lem1518702)). Qed.
Lemma lem1518771 : term33 = term83.
Proof. exact (TRANS (@lem1518603) (@lem1518704)). Qed.
Lemma lem1518784 (w : real) (x : real) (y : real) (z : real) : (term75 w x y z) = (term75 w x y z).
Proof. exact (eq_refl (term75 w x y z)). Qed.
Lemma lem1518785 (w : real) (x : real) (y : real) : (term76 w x y) = (term76 w x y).
Proof. exact (fun_ext (fun z : real => @lem1518784 w x y z)). Qed.
Lemma lem1518786 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518787 (w : real) (x : real) (y : real) : (term77 w x y) = (term77 w x y).
Proof. exact (MK_COMB (@lem1518786) (@lem1518785 w x y)). Qed.
Lemma lem1518788 (w : real) (x : real) : (term78 w x) = (term78 w x).
Proof. exact (fun_ext (fun y : real => @lem1518787 w x y)). Qed.
Lemma lem1518789 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518790 (w : real) (x : real) : (term79 w x) = (term79 w x).
Proof. exact (MK_COMB (@lem1518789) (@lem1518788 w x)). Qed.
Lemma lem1518791 (w : real) : (term80 w) = (term80 w).
Proof. exact (fun_ext (fun x : real => @lem1518790 w x)). Qed.
Lemma lem1518792 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518793 (w : real) : (term81 w) = (term81 w).
Proof. exact (MK_COMB (@lem1518792) (@lem1518791 w)). Qed.
Lemma lem1518794 : term82 = term82.
Proof. exact (fun_ext (fun w : real => @lem1518793 w)). Qed.
Lemma lem1518795 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1518796 : term83 = term83.
Proof. exact (MK_COMB (@lem1518795) (@lem1518794)). Qed.
Lemma lem1518797 : term33 = term83.
Proof. exact (TRANS (@lem1518771) (@lem1518796)). Qed.
Lemma lem1518801 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term75 w x y z.
Proof. exact (h1). Qed.
Lemma lem1518802 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term72 w x y z.
Proof. exact (proj2 (@lem1518801 w x y z h1)). Qed.
Lemma lem1518803 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term56 w x y z.
Proof. exact (proj1 (@lem1518801 w x y z h1)). Qed.
Lemma lem1518804 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term53 y z.
Proof. exact (proj2 (@lem1518803 w x y z h1)). Qed.
Lemma lem1518805 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term49 w x.
Proof. exact (proj1 (@lem1518803 w x y z h1)). Qed.
Lemma lem1518807 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518808 : term85 = term86.
Proof. exact (@lem1518807 (NUMERAL 0) term87). Qed.
Lemma lem1518809 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518810 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518811 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518810 h1) (fun h1 : term86 = True => @lem1518809)). Qed.
Lemma lem1518812 : term86 = True.
Proof. exact (EQ_MP (@lem1518811) (@lem1518809)). Qed.
Lemma lem1518813 : term85 = True.
Proof. exact (TRANS (@lem1518808) (@lem1518812)). Qed.
Lemma lem1518814 : True = term85.
Proof. exact (SYM (@lem1518813)). Qed.
Lemma lem1518815 : term85.
Proof. exact (EQ_MP (@lem1518814) (@lem0)). Qed.
Lemma lem1518816 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term89 y z.
Proof. exact (conj (@lem1518815) (@lem1518804 w x y z h1)). Qed.
Lemma lem1518818 (x : real) (y : real) : term90 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1518819 (y : real) (z : real) : term91 y z.
Proof. exact (@lem1518818 term92 (term44 y z)). Qed.
Lemma lem1518820 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term93 y z.
Proof. exact (@lem1518819 y z (@lem1518816 w x y z h1)). Qed.
Lemma lem1518821 (y : real) (z : real) : (term94 y z) = (term44 y z).
Proof. exact (@lem1483460 (term44 y z)). Qed.
Lemma lem1518822 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518823 (y : real) (z : real) : (term95 y z) = (term52 y z).
Proof. exact (MK_COMB (@lem1518822) (@lem1518821 y z)). Qed.
Lemma lem1518824 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518825 (y : real) (z : real) : (term93 y z) = (term53 y z).
Proof. exact (MK_COMB (@lem1518823 y z) (@lem1518824)). Qed.
Lemma lem1518826 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term53 y z.
Proof. exact (EQ_MP (@lem1518825 y z) (@lem1518820 w x y z h1)). Qed.
Lemma lem1518828 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518829 : term85 = term86.
Proof. exact (@lem1518828 (NUMERAL 0) term87). Qed.
Lemma lem1518830 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518831 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518832 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518831 h1) (fun h1 : term86 = True => @lem1518830)). Qed.
Lemma lem1518833 : term86 = True.
Proof. exact (EQ_MP (@lem1518832) (@lem1518830)). Qed.
Lemma lem1518834 : term85 = True.
Proof. exact (TRANS (@lem1518829) (@lem1518833)). Qed.
Lemma lem1518835 : True = term85.
Proof. exact (SYM (@lem1518834)). Qed.
Lemma lem1518836 : term85.
Proof. exact (EQ_MP (@lem1518835) (@lem0)). Qed.
Lemma lem1518837 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term96 w x y z.
Proof. exact (conj (@lem1518836) (@lem1518802 w x y z h1)). Qed.
Lemma lem1518839 (x : real) (y : real) : term90 x y.
Proof. exact (proj1 (@lem1483568 x y)). Qed.
Lemma lem1518840 (w : real) (x : real) (y : real) (z : real) : term97 w x y z.
Proof. exact (@lem1518839 term92 (term69 w x y z)). Qed.
Lemma lem1518841 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term98 w x y z.
Proof. exact (@lem1518840 w x y z (@lem1518837 w x y z h1)). Qed.
Lemma lem1518842 (w : real) (x : real) (y : real) (z : real) : (term99 w x y z) = (term69 w x y z).
Proof. exact (@lem1483460 (term69 w x y z)). Qed.
Lemma lem1518843 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem1518844 (w : real) (x : real) (y : real) (z : real) : (term100 w x y z) = (term71 w x y z).
Proof. exact (MK_COMB (@lem1518843) (@lem1518842 w x y z)). Qed.
Lemma lem1518845 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518846 (w : real) (x : real) (y : real) (z : real) : (term98 w x y z) = (term72 w x y z).
Proof. exact (MK_COMB (@lem1518844 w x y z) (@lem1518845)). Qed.
Lemma lem1518847 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term72 w x y z.
Proof. exact (EQ_MP (@lem1518846 w x y z) (@lem1518841 w x y z h1)). Qed.
Lemma lem1518849 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518850 : term85 = term86.
Proof. exact (@lem1518849 (NUMERAL 0) term87). Qed.
Lemma lem1518851 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518852 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518853 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518852 h1) (fun h1 : term86 = True => @lem1518851)). Qed.
Lemma lem1518854 : term86 = True.
Proof. exact (EQ_MP (@lem1518853) (@lem1518851)). Qed.
Lemma lem1518855 : term85 = True.
Proof. exact (TRANS (@lem1518850) (@lem1518854)). Qed.
Lemma lem1518856 : True = term85.
Proof. exact (SYM (@lem1518855)). Qed.
Lemma lem1518857 : term85.
Proof. exact (EQ_MP (@lem1518856) (@lem0)). Qed.
Lemma lem1518858 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term101 w x.
Proof. exact (conj (@lem1518857) (@lem1518805 w x y z h1)). Qed.
Lemma lem1518860 (x : real) (y : real) : term102 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1518861 (w : real) (x : real) : term103 w x.
Proof. exact (@lem1518860 term92 (term44 w x)). Qed.
Lemma lem1518862 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term104 w x.
Proof. exact (@lem1518861 w x (@lem1518858 w x y z h1)). Qed.
Lemma lem1518863 (w : real) (x : real) : (term94 w x) = (term44 w x).
Proof. exact (@lem1483460 (term44 w x)). Qed.
Lemma lem1518864 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518865 (w : real) (x : real) : (term105 w x) = (term47 w x).
Proof. exact (MK_COMB (@lem1518864) (@lem1518863 w x)). Qed.
Lemma lem1518866 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518867 (w : real) (x : real) : (term104 w x) = (term49 w x).
Proof. exact (MK_COMB (@lem1518865 w x) (@lem1518866)). Qed.
Lemma lem1518868 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term49 w x.
Proof. exact (EQ_MP (@lem1518867 w x) (@lem1518862 w x y z h1)). Qed.
Lemma lem1518869 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term106 w x y z.
Proof. exact (conj (@lem1518868 w x y z h1) (@lem1518847 w x y z h1)). Qed.
Lemma lem1518871 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1518872 (w : real) (x : real) (y : real) (z : real) : term108 w x y z.
Proof. exact (@lem1518871 (term44 w x) (term69 w x y z)). Qed.
Lemma lem1518873 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term109 w x y z.
Proof. exact (@lem1518872 w x y z (@lem1518869 w x y z h1)). Qed.
Lemma lem1518874 (w : real) (x : real) (y : real) (z : real) : (term110 w x y z) = (term111 w x y z).
Proof. exact (@lem1483480 (term45 w) w x (term68 x y z)). Qed.
Lemma lem1518875 (w : real) : (term112 w) = (term113 w).
Proof. exact (@lem1483440 term63 w). Qed.
Lemma lem1518877 (m : nat) : (term114 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518878 : term115 = term48.
Proof. exact (@lem1518877 term87). Qed.
Lemma lem1518879 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518880 : term116 = term117.
Proof. exact (MK_COMB (@lem1518879) (@lem1518878)). Qed.
Lemma lem1518881 (w : real) : w = w.
Proof. exact (eq_refl w). Qed.
Lemma lem1518882 (w : real) : (term113 w) = (term118 w).
Proof. exact (MK_COMB (@lem1518880) (@lem1518881 w)). Qed.
Lemma lem1518883 (w : real) : (term112 w) = (term118 w).
Proof. exact (TRANS (@lem1518875 w) (@lem1518882 w)). Qed.
Lemma lem1518884 (w : real) : (term118 w) = term48.
Proof. exact (@lem1483446 w). Qed.
Lemma lem1518885 (w : real) : (term112 w) = term48.
Proof. exact (TRANS (@lem1518883 w) (@lem1518884 w)). Qed.
Lemma lem1518886 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1518887 (w : real) : (term119 w) = term120.
Proof. exact (MK_COMB (@lem1518886) (@lem1518885 w)). Qed.
Lemma lem1518888 (x : real) (y : real) (z : real) : (term121 x y z) = (term122 x y z).
Proof. exact (@lem1483490 x (term45 x) (term43 y z)). Qed.
Lemma lem1518889 (x : real) : (term123 x) = (term113 x).
Proof. exact (@lem1483442 term63 x). Qed.
Lemma lem1518891 (m : nat) : (term114 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518892 : term115 = term48.
Proof. exact (@lem1518891 term87). Qed.
Lemma lem1518893 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518894 : term116 = term117.
Proof. exact (MK_COMB (@lem1518893) (@lem1518892)). Qed.
Lemma lem1518895 (x : real) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1518896 (x : real) : (term113 x) = (term118 x).
Proof. exact (MK_COMB (@lem1518894) (@lem1518895 x)). Qed.
Lemma lem1518897 (x : real) : (term123 x) = (term118 x).
Proof. exact (TRANS (@lem1518889 x) (@lem1518896 x)). Qed.
Lemma lem1518898 (x : real) : (term118 x) = term48.
Proof. exact (@lem1483446 x). Qed.
Lemma lem1518899 (x : real) : (term123 x) = term48.
Proof. exact (TRANS (@lem1518897 x) (@lem1518898 x)). Qed.
Lemma lem1518900 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1518901 (x : real) : (term124 x) = term120.
Proof. exact (MK_COMB (@lem1518900) (@lem1518899 x)). Qed.
Lemma lem1518902 (y : real) (z : real) : (term43 y z) = (term43 y z).
Proof. exact (eq_refl (term43 y z)). Qed.
Lemma lem1518903 (x : real) (y : real) (z : real) : (term122 x y z) = (term125 y z).
Proof. exact (MK_COMB (@lem1518901 x) (@lem1518902 y z)). Qed.
Lemma lem1518904 (x : real) (y : real) (z : real) : (term121 x y z) = (term125 y z).
Proof. exact (TRANS (@lem1518888 x y z) (@lem1518903 x y z)). Qed.
Lemma lem1518905 (y : real) (z : real) : (term125 y z) = (term43 y z).
Proof. exact (@lem1483448 (term43 y z)). Qed.
Lemma lem1518906 (x : real) (y : real) (z : real) : (term121 x y z) = (term43 y z).
Proof. exact (TRANS (@lem1518904 x y z) (@lem1518905 y z)). Qed.
Lemma lem1518907 (w : real) (x : real) (y : real) (z : real) : (term111 w x y z) = (term125 y z).
Proof. exact (MK_COMB (@lem1518887 w) (@lem1518906 x y z)). Qed.
Lemma lem1518908 (w : real) (x : real) (y : real) (z : real) : (term110 w x y z) = (term125 y z).
Proof. exact (TRANS (@lem1518874 w x y z) (@lem1518907 w x y z)). Qed.
Lemma lem1518909 (y : real) (z : real) : (term125 y z) = (term43 y z).
Proof. exact (@lem1483448 (term43 y z)). Qed.
Lemma lem1518910 (w : real) (x : real) (y : real) (z : real) : (term110 w x y z) = (term43 y z).
Proof. exact (TRANS (@lem1518908 w x y z) (@lem1518909 y z)). Qed.
Lemma lem1518911 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518912 (w : real) (x : real) (y : real) (z : real) : (term126 w x y z) = (term127 y z).
Proof. exact (MK_COMB (@lem1518911) (@lem1518910 w x y z)). Qed.
Lemma lem1518913 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518914 (w : real) (x : real) (y : real) (z : real) : (term109 w x y z) = (term128 y z).
Proof. exact (MK_COMB (@lem1518912 w x y z) (@lem1518913)). Qed.
Lemma lem1518915 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term128 y z.
Proof. exact (EQ_MP (@lem1518914 w x y z) (@lem1518873 w x y z h1)). Qed.
Lemma lem1518917 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518918 : term85 = term86.
Proof. exact (@lem1518917 (NUMERAL 0) term87). Qed.
Lemma lem1518919 : term88 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem1518920 (h1 : term88 = (BIT1 0)) : term86 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem1518921 : (term88 = (BIT1 0)) = (term86 = True).
Proof. exact (prop_ext (fun h1 : term88 = (BIT1 0) => @lem1518920 h1) (fun h1 : term86 = True => @lem1518919)). Qed.
Lemma lem1518922 : term86 = True.
Proof. exact (EQ_MP (@lem1518921) (@lem1518919)). Qed.
Lemma lem1518923 : term85 = True.
Proof. exact (TRANS (@lem1518918) (@lem1518922)). Qed.
Lemma lem1518924 : True = term85.
Proof. exact (SYM (@lem1518923)). Qed.
Lemma lem1518925 : term85.
Proof. exact (EQ_MP (@lem1518924) (@lem0)). Qed.
Lemma lem1518926 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term129 y z.
Proof. exact (conj (@lem1518925) (@lem1518915 w x y z h1)). Qed.
Lemma lem1518928 (x : real) (y : real) : term102 x y.
Proof. exact (proj2 (@lem1483568 x y)). Qed.
Lemma lem1518929 (y : real) (z : real) : term130 y z.
Proof. exact (@lem1518928 term92 (term43 y z)). Qed.
Lemma lem1518930 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term131 y z.
Proof. exact (@lem1518929 y z (@lem1518926 w x y z h1)). Qed.
Lemma lem1518931 (y : real) (z : real) : (term132 y z) = (term43 y z).
Proof. exact (@lem1483460 (term43 y z)). Qed.
Lemma lem1518932 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518933 (y : real) (z : real) : (term133 y z) = (term127 y z).
Proof. exact (MK_COMB (@lem1518932) (@lem1518931 y z)). Qed.
Lemma lem1518934 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518935 (y : real) (z : real) : (term131 y z) = (term128 y z).
Proof. exact (MK_COMB (@lem1518933 y z) (@lem1518934)). Qed.
Lemma lem1518936 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term128 y z.
Proof. exact (EQ_MP (@lem1518935 y z) (@lem1518930 w x y z h1)). Qed.
Lemma lem1518937 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term134 y z.
Proof. exact (conj (@lem1518936 w x y z h1) (@lem1518826 w x y z h1)). Qed.
Lemma lem1518939 (x : real) (y : real) : term107 x y.
Proof. exact (proj1 (@lem1483584 x y)). Qed.
Lemma lem1518940 (y : real) (z : real) : term135 y z.
Proof. exact (@lem1518939 (term43 y z) (term44 y z)). Qed.
Lemma lem1518941 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term136 y z.
Proof. exact (@lem1518940 y z (@lem1518937 w x y z h1)). Qed.
Lemma lem1518942 (y : real) (z : real) : (term137 y z) = (term138 y z).
Proof. exact (@lem1483480 y (term45 y) (term45 z) z). Qed.
Lemma lem1518943 (y : real) : (term123 y) = (term113 y).
Proof. exact (@lem1483442 term63 y). Qed.
Lemma lem1518945 (m : nat) : (term114 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518946 : term115 = term48.
Proof. exact (@lem1518945 term87). Qed.
Lemma lem1518947 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518948 : term116 = term117.
Proof. exact (MK_COMB (@lem1518947) (@lem1518946)). Qed.
Lemma lem1518949 (y : real) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1518950 (y : real) : (term113 y) = (term118 y).
Proof. exact (MK_COMB (@lem1518948) (@lem1518949 y)). Qed.
Lemma lem1518951 (y : real) : (term123 y) = (term118 y).
Proof. exact (TRANS (@lem1518943 y) (@lem1518950 y)). Qed.
Lemma lem1518952 (y : real) : (term118 y) = term48.
Proof. exact (@lem1483446 y). Qed.
Lemma lem1518953 (y : real) : (term123 y) = term48.
Proof. exact (TRANS (@lem1518951 y) (@lem1518952 y)). Qed.
Lemma lem1518954 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem1518955 (y : real) : (term124 y) = term120.
Proof. exact (MK_COMB (@lem1518954) (@lem1518953 y)). Qed.
Lemma lem1518956 (z : real) : (term112 z) = (term113 z).
Proof. exact (@lem1483440 term63 z). Qed.
Lemma lem1518958 (m : nat) : (term114 m) = term48.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem1518959 : term115 = term48.
Proof. exact (@lem1518958 term87). Qed.
Lemma lem1518960 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1518961 : term116 = term117.
Proof. exact (MK_COMB (@lem1518960) (@lem1518959)). Qed.
Lemma lem1518962 (z : real) : z = z.
Proof. exact (eq_refl z). Qed.
Lemma lem1518963 (z : real) : (term113 z) = (term118 z).
Proof. exact (MK_COMB (@lem1518961) (@lem1518962 z)). Qed.
Lemma lem1518964 (z : real) : (term112 z) = (term118 z).
Proof. exact (TRANS (@lem1518956 z) (@lem1518963 z)). Qed.
Lemma lem1518965 (z : real) : (term118 z) = term48.
Proof. exact (@lem1483446 z). Qed.
Lemma lem1518966 (z : real) : (term112 z) = term48.
Proof. exact (TRANS (@lem1518964 z) (@lem1518965 z)). Qed.
Lemma lem1518967 (y : real) (z : real) : (term138 y z) = term139.
Proof. exact (MK_COMB (@lem1518955 y) (@lem1518966 z)). Qed.
Lemma lem1518968 (y : real) (z : real) : (term137 y z) = term139.
Proof. exact (TRANS (@lem1518942 y z) (@lem1518967 y z)). Qed.
Lemma lem1518969 : term139 = term48.
Proof. exact (@lem1483448 term48). Qed.
Lemma lem1518970 (y : real) (z : real) : (term137 y z) = term48.
Proof. exact (TRANS (@lem1518968 y z) (@lem1518969)). Qed.
Lemma lem1518971 : real_gt = real_gt.
Proof. exact (eq_refl real_gt). Qed.
Lemma lem1518972 (y : real) (z : real) : (term140 y z) = term141.
Proof. exact (MK_COMB (@lem1518971) (@lem1518970 y z)). Qed.
Lemma lem1518973 : term48 = term48.
Proof. exact (eq_refl term48). Qed.
Lemma lem1518974 (y : real) (z : real) : (term136 y z) = term142.
Proof. exact (MK_COMB (@lem1518972 y z) (@lem1518973)). Qed.
Lemma lem1518975 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term142.
Proof. exact (EQ_MP (@lem1518974 y z) (@lem1518941 w x y z h1)). Qed.
Lemma lem1518977 (n : nat) (m : nat) : (term84 m n) = (Peano.lt n m).
Proof. exact (proj1 (@lem1366271 m n)). Qed.
Lemma lem1518978 : term142 = term143.
Proof. exact (@lem1518977 (NUMERAL 0) (NUMERAL 0)). Qed.
Lemma lem1518979 : term143 = False.
Proof. exact (@lem1010765 0). Qed.
Lemma lem1518980 : term142 = False.
Proof. exact (TRANS (@lem1518978) (@lem1518979)). Qed.
Lemma lem1518981 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : False.
Proof. exact (EQ_MP (@lem1518980) (@lem1518975 w x y z h1)). Qed.
Lemma lem1518983 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : term75 w x y z.
Proof. exact (h1). Qed.
Lemma lem1518984 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : (term75 w x y z) = False.
Proof. exact (prop_ext (fun h2 : term75 w x y z => @lem1518981 w x y z h1) (fun h2 : False => @lem1518983 w x y z h1)). Qed.
Lemma lem1518985 (w : real) (x : real) (y : real) (z : real) (h1 : term75 w x y z) : False.
Proof. exact (EQ_MP (@lem1518984 w x y z h1) (@lem1518983 w x y z h1)). Qed.
Lemma lem1518986 (w : real) (x : real) (y : real) (h1 : term77 w x y) : term77 w x y.
Proof. exact (h1). Qed.
Lemma lem1518987 (w : real) (x : real) (y : real) (h1 : term77 w x y) : False.
Proof. exact (ex_elim (@lem1518986 w x y h1) (fun z : real => fun h0 : term76 w x y z => @lem1518985 w x y z h0)). Qed.
Lemma lem1518988 (w : real) (x : real) (h1 : term79 w x) : term79 w x.
Proof. exact (h1). Qed.
Lemma lem1518989 (w : real) (x : real) (h1 : term79 w x) : False.
Proof. exact (ex_elim (@lem1518988 w x h1) (fun y : real => fun h0 : term78 w x y => @lem1518987 w x y h0)). Qed.
Lemma lem1518990 (w : real) (h1 : term81 w) : term81 w.
Proof. exact (h1). Qed.
Lemma lem1518991 (w : real) (h1 : term81 w) : False.
Proof. exact (ex_elim (@lem1518990 w h1) (fun x : real => fun h0 : term80 w x => @lem1518989 w x h0)). Qed.
Lemma lem1518992 (h1 : term83) : term83.
Proof. exact (h1). Qed.
Lemma lem1518993 (h1 : term83) : False.
Proof. exact (ex_elim (@lem1518992 h1) (fun w : real => fun h0 : term82 w => @lem1518991 w h0)). Qed.
Lemma lem1518994 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem1518995 (h1 : term33) : term83.
Proof. exact (EQ_MP (@lem1518797) (@lem1518994 h1)). Qed.
Lemma lem1518996 (h1 : term33) : term83 = False.
Proof. exact (prop_ext (fun h2 : term83 => @lem1518993 h2) (fun h2 : False => @lem1518995 h1)). Qed.
Lemma lem1518997 (h1 : term33) : False.
Proof. exact (EQ_MP (@lem1518996 h1) (@lem1518995 h1)). Qed.
Lemma lem1518998 : term144.
Proof. exact (fun h0 : term33 => @lem1518997 h0). Qed.
Lemma lem1518999 : term145.
Proof. exact (@lem1386578 term146). Qed.
Lemma lem1519000 : term146.
Proof. exact (@lem1518999 (@lem1518998)). Qed.
