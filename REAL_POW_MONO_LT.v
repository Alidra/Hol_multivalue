Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW_MONO_LT_term_abbrevs.
Require Import LT_EXISTS_spec.
Require Import REAL_LT_LMUL_spec.
Require Import REAL_LT_MUL2_spec.
Require Import REAL_LT_TRANS_spec.
Require Import REAL_MUL_RID_spec.
Require Import REAL_OF_NUM_LT_spec.
Require Import REAL_POW_ADD_spec.
Require Import REAL_POW_LT_spec.
Require Import thm0_spec.
Require Import thm1338986_spec.
Require Import thm1340282_spec.
Require Import thm1344310_spec.
Require Import thm1344311_spec.
Require Import thm1344313_spec.
Require Import thm1344314_spec.
Require Import thm1842_spec.
Require Import thm517422_spec.
Require Import thm519779_spec.
Require Import thm520356_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem1638554 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1638555 (w : real) (h1 : term0) : term1 w.
Proof. exact (@lem1638554 h1 w). Qed.
Lemma lem1638556 (w : real) : (term1 w) = (term2 w).
Proof. exact (eq_refl (term1 w)). Qed.
Lemma lem1638557 (w : real) (h1 : term0) : term2 w.
Proof. exact (EQ_MP (@lem1638556 w) (@lem1638555 w h1)). Qed.
Lemma lem1638558 (w : real) (x : real) (h1 : term0) : term3 w x.
Proof. exact (@lem1638557 w h1 x). Qed.
Lemma lem1638559 (w : real) (x : real) : (term3 w x) = (term4 w x).
Proof. exact (eq_refl (term3 w x)). Qed.
Lemma lem1638560 (w : real) (x : real) (h1 : term0) : term4 w x.
Proof. exact (EQ_MP (@lem1638559 w x) (@lem1638558 w x h1)). Qed.
Lemma lem1638561 (w : real) (x : real) (y : real) (h1 : term0) : term5 w x y.
Proof. exact (@lem1638560 w x h1 y). Qed.
Lemma lem1638562 (w : real) (y : real) (x : real) : (term5 w x y) = (term6 w y x).
Proof. exact (eq_refl (term5 w x y)). Qed.
Lemma lem1638563 (w : real) (y : real) (x : real) (h1 : term0) : term6 w y x.
Proof. exact (EQ_MP (@lem1638562 w y x) (@lem1638561 w x y h1)). Qed.
Lemma lem1638564 (w : real) (y : real) (x : real) (z : real) (h1 : term0) : term7 w y x z.
Proof. exact (@lem1638563 w y x h1 z). Qed.
Lemma lem1638565 (w : real) (y : real) (x : real) (z : real) : (term7 w y x z) = (term8 w y x z).
Proof. exact (eq_refl (term7 w y x z)). Qed.
Lemma lem1638566 (w : real) (y : real) (x : real) (z : real) (h1 : term0) : term8 w y x z.
Proof. exact (EQ_MP (@lem1638565 w y x z) (@lem1638564 w y x z h1)). Qed.
Lemma lem1638567 (w : real) (x : real) (y : real) (z : real) (h1 : term9 w x y z) : term9 w x y z.
Proof. exact (h1). Qed.
Lemma lem1638568 (w : real) (x : real) (y : real) (z : real) (h1 : term0) (h2 : term9 w x y z) : term10 w y x z.
Proof. exact (@lem1638566 w y x z h1 (@lem1638567 w x y z h2)). Qed.
Lemma lem1638569 (w : real) (x : real) (y : real) (z : real) (h1 : term9 w x y z) : term11 w y x z.
Proof. exact (fun h0 : term0 => @lem1638568 w x y z h0 h1). Qed.
Lemma lem1638570 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1638571 (w : real) (x : real) (y : real) (z : real) (h1 : term0) (h2 : term9 w x y z) : term10 w y x z.
Proof. exact (@lem1638569 w x y z h2 (@lem1638570 h1)). Qed.
Lemma lem1638572 (w : real) (y : real) (x : real) (z : real) (h1 : term0) : term8 w y x z.
Proof. exact (fun h0 : term9 w x y z => @lem1638571 w x y z h1 h0). Qed.
Lemma lem1638573 (w : real) (y : real) (x : real) (h1 : term0) : term6 w y x.
Proof. exact (fun z : real => @lem1638572 w y x z h1). Qed.
Lemma lem1638574 (w : real) (y : real) (h1 : term0) : term12 w y.
Proof. exact (fun x : real => @lem1638573 w y x h1). Qed.
Lemma lem1638575 (w : real) (h1 : term0) : term13 w.
Proof. exact (fun y : real => @lem1638574 w y h1). Qed.
Lemma lem1638576 (h1 : term0) : term14.
Proof. exact (fun w : real => @lem1638575 w h1). Qed.
Lemma lem1638577 : term15.
Proof. exact (fun h0 : term0 => @lem1638576 h0). Qed.
Lemma lem1638578 : term14.
Proof. exact (@lem1638577 (@lem1630835)). Qed.
Lemma lem1638579 (w : real) : term16 w.
Proof. exact (@lem1638578 w). Qed.
Lemma lem1638580 (w : real) : (term16 w) = (term13 w).
Proof. exact (eq_refl (term16 w)). Qed.
Lemma lem1638581 (w : real) : term13 w.
Proof. exact (EQ_MP (@lem1638580 w) (@lem1638579 w)). Qed.
Lemma lem1638582 (w : real) (y : real) : term17 w y.
Proof. exact (@lem1638581 w y). Qed.
Lemma lem1638583 (w : real) (y : real) : (term17 w y) = (term12 w y).
Proof. exact (eq_refl (term17 w y)). Qed.
Lemma lem1638584 (w : real) (y : real) : term12 w y.
Proof. exact (EQ_MP (@lem1638583 w y) (@lem1638582 w y)). Qed.
Lemma lem1638585 (w : real) (y : real) (x : real) : term18 w y x.
Proof. exact (@lem1638584 w y x). Qed.
Lemma lem1638586 (w : real) (y : real) (x : real) : (term18 w y x) = (term6 w y x).
Proof. exact (eq_refl (term18 w y x)). Qed.
Lemma lem1638587 (w : real) (y : real) (x : real) : term6 w y x.
Proof. exact (EQ_MP (@lem1638586 w y x) (@lem1638585 w y x)). Qed.
Lemma lem1638588 (w : real) (y : real) (x : real) (z : real) : term7 w y x z.
Proof. exact (@lem1638587 w y x z). Qed.
Lemma lem1638589 (w : real) (y : real) (x : real) (z : real) : (term7 w y x z) = (term8 w y x z).
Proof. exact (eq_refl (term7 w y x z)). Qed.
Lemma lem1638592 (x : real) (h1 : (term19 x) = x) : (term19 x) = x.
Proof. exact (h1). Qed.
Lemma lem1638593 (x : real) (h1 : (term19 x) = x) : x = (term19 x).
Proof. exact (SYM (@lem1638592 x h1)). Qed.
Lemma lem1638594 (x : real) (h1 : x = (term19 x)) : x = (term19 x).
Proof. exact (h1). Qed.
Lemma lem1638595 (x : real) (h1 : x = (term19 x)) : (term19 x) = x.
Proof. exact (SYM (@lem1638594 x h1)). Qed.
Lemma lem1638596 (x : real) : ((term19 x) = x) = (x = (term19 x)).
Proof. exact (prop_ext (fun h1 : (term19 x) = x => @lem1638593 x h1) (fun h1 : x = (term19 x) => @lem1638595 x h1)). Qed.
Lemma lem1638597 : term20 = term21.
Proof. exact (fun_ext (fun x : real => @lem1638596 x)). Qed.
Lemma lem1638598 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1638599 : term22 = term23.
Proof. exact (MK_COMB (@lem1638598) (@lem1638597)). Qed.
Lemma lem1638600 : term23.
Proof. exact (EQ_MP (@lem1638599) (@lem1338986)). Qed.
Lemma lem1638601 (x : real) : term24 x.
Proof. exact (@lem1638600 x). Qed.
Lemma lem1638602 (x : real) : (term24 x) = (x = (term19 x)).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1638604 (x : real) : term25 x.
Proof. exact (EQ_MP (@lem1344314 x) (@lem1344313 x)). Qed.
Lemma lem1638605 (x : real) (n : nat) : term26 x n.
Proof. exact (@lem1638604 x n). Qed.
Lemma lem1638606 (x : real) (n : nat) : (term26 x n) = ((term27 x n) = (term28 x n)).
Proof. exact (eq_refl (term26 x n)). Qed.
Lemma lem1638609 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem1638610 (x : real) (h1 : term29) : term30 x.
Proof. exact (@lem1638609 h1 x). Qed.
Lemma lem1638611 (x : real) : (term30 x) = (term31 x).
Proof. exact (eq_refl (term30 x)). Qed.
Lemma lem1638612 (x : real) (h1 : term29) : term31 x.
Proof. exact (EQ_MP (@lem1638611 x) (@lem1638610 x h1)). Qed.
Lemma lem1638613 (x : real) (y : real) (h1 : term29) : term32 x y.
Proof. exact (@lem1638612 x h1 y). Qed.
Lemma lem1638614 (y : real) (x : real) : (term32 x y) = (term33 y x).
Proof. exact (eq_refl (term32 x y)). Qed.
Lemma lem1638615 (y : real) (x : real) (h1 : term29) : term33 y x.
Proof. exact (EQ_MP (@lem1638614 y x) (@lem1638613 x y h1)). Qed.
Lemma lem1638616 (y : real) (x : real) (z : real) (h1 : term29) : term34 y x z.
Proof. exact (@lem1638615 y x h1 z). Qed.
Lemma lem1638617 (y : real) (x : real) (z : real) : (term34 y x z) = (term35 y x z).
Proof. exact (eq_refl (term34 y x z)). Qed.
Lemma lem1638618 (y : real) (x : real) (z : real) (h1 : term29) : term35 y x z.
Proof. exact (EQ_MP (@lem1638617 y x z) (@lem1638616 y x z h1)). Qed.
Lemma lem1638619 (x : real) (y : real) (z : real) (h1 : term36 x y z) : term36 x y z.
Proof. exact (h1). Qed.
Lemma lem1638620 (x : real) (y : real) (z : real) (h1 : term29) (h2 : term36 x y z) : real_lt x z.
Proof. exact (@lem1638618 y x z h1 (@lem1638619 x y z h2)). Qed.
Lemma lem1638621 (x : real) (y : real) (z : real) (h1 : term36 x y z) : term37 x z.
Proof. exact (fun h0 : term29 => @lem1638620 x y z h0 h1). Qed.
Lemma lem1638622 (x : real) (z : real) (h1 : term38 x z) : term38 x z.
Proof. exact (h1). Qed.
Lemma lem1638623 (x : real) (z : real) (h1 : term38 x z) : term37 x z.
Proof. exact (ex_elim (@lem1638622 x z h1) (fun y : real => fun h0 : term39 x z y => @lem1638621 x y z h0)). Qed.
Lemma lem1638624 (h1 : term29) : term29.
Proof. exact (h1). Qed.
Lemma lem1638625 (x : real) (z : real) (h1 : term29) (h2 : term38 x z) : real_lt x z.
Proof. exact (@lem1638623 x z h2 (@lem1638624 h1)). Qed.
Lemma lem1638626 (x : real) (z : real) (h1 : term29) : term40 x z.
Proof. exact (fun h0 : term38 x z => @lem1638625 x z h1 h0). Qed.
Lemma lem1638627 (x : real) (h1 : term29) : term41 x.
Proof. exact (fun z : real => @lem1638626 x z h1). Qed.
Lemma lem1638628 (h1 : term29) : term42.
Proof. exact (fun x : real => @lem1638627 x h1). Qed.
Lemma lem1638629 : term43.
Proof. exact (fun h0 : term29 => @lem1638628 h0). Qed.
Lemma lem1638630 : term42.
Proof. exact (@lem1638629 (@lem1372268)). Qed.
Lemma lem1638631 (x : real) : term44 x.
Proof. exact (@lem1638630 x). Qed.
Lemma lem1638632 (x : real) : (term44 x) = (term41 x).
Proof. exact (eq_refl (term44 x)). Qed.
Lemma lem1638633 (x : real) : term41 x.
Proof. exact (EQ_MP (@lem1638632 x) (@lem1638631 x)). Qed.
Lemma lem1638634 (x : real) (z : real) : term45 x z.
Proof. exact (@lem1638633 x z). Qed.
Lemma lem1638635 (x : real) (z : real) : (term45 x z) = (term40 x z).
Proof. exact (eq_refl (term45 x z)). Qed.
Lemma lem1638637 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1638638 (x : real) (h1 : term46) : term47 x.
Proof. exact (@lem1638637 h1 x). Qed.
Lemma lem1638639 (x : real) : (term47 x) = (term48 x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1638640 (x : real) (h1 : term46) : term48 x.
Proof. exact (EQ_MP (@lem1638639 x) (@lem1638638 x h1)). Qed.
Lemma lem1638641 (x : real) (n : nat) (h1 : term46) : term49 x n.
Proof. exact (@lem1638640 x h1 n). Qed.
Lemma lem1638642 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (eq_refl (term49 x n)). Qed.
Lemma lem1638643 (x : real) (n : nat) (h1 : term46) : term50 x n.
Proof. exact (EQ_MP (@lem1638642 x n) (@lem1638641 x n h1)). Qed.
Lemma lem1638644 (x : real) (h1 : term51 x) : term51 x.
Proof. exact (h1). Qed.
Lemma lem1638645 (n : nat) (x : real) (h1 : term46) (h2 : term51 x) : term52 x n.
Proof. exact (@lem1638643 x n h1 (@lem1638644 x h2)). Qed.
Lemma lem1638646 (n : nat) (x : real) (h1 : term51 x) : term53 x n.
Proof. exact (fun h0 : term46 => @lem1638645 n x h0 h1). Qed.
Lemma lem1638647 (h1 : term46) : term46.
Proof. exact (h1). Qed.
Lemma lem1638648 (n : nat) (x : real) (h1 : term46) (h2 : term51 x) : term52 x n.
Proof. exact (@lem1638646 n x h2 (@lem1638647 h1)). Qed.
Lemma lem1638649 (x : real) (n : nat) (h1 : term46) : term50 x n.
Proof. exact (fun h0 : term51 x => @lem1638648 n x h1 h0). Qed.
Lemma lem1638650 (x : real) (h1 : term46) : term48 x.
Proof. exact (fun n : nat => @lem1638649 x n h1). Qed.
Lemma lem1638651 (h1 : term46) : term46.
Proof. exact (fun x : real => @lem1638650 x h1). Qed.
Lemma lem1638652 : term54.
Proof. exact (fun h0 : term46 => @lem1638651 h0). Qed.
Lemma lem1638653 : term46.
Proof. exact (@lem1638652 (@lem1582551)). Qed.
Lemma lem1638654 (x : real) : term47 x.
Proof. exact (@lem1638653 x). Qed.
Lemma lem1638655 (x : real) : (term47 x) = (term48 x).
Proof. exact (eq_refl (term47 x)). Qed.
Lemma lem1638656 (x : real) : term48 x.
Proof. exact (EQ_MP (@lem1638655 x) (@lem1638654 x)). Qed.
Lemma lem1638657 (x : real) (n : nat) : term49 x n.
Proof. exact (@lem1638656 x n). Qed.
Lemma lem1638658 (x : real) (n : nat) : (term49 x n) = (term50 x n).
Proof. exact (eq_refl (term49 x n)). Qed.
Lemma lem1638660 (h1 : term55) : term55.
Proof. exact (h1). Qed.
Lemma lem1638661 (x : real) (h1 : term55) : term56 x.
Proof. exact (@lem1638660 h1 x). Qed.
Lemma lem1638662 (x : real) : (term56 x) = (term57 x).
Proof. exact (eq_refl (term56 x)). Qed.
Lemma lem1638663 (x : real) (h1 : term55) : term57 x.
Proof. exact (EQ_MP (@lem1638662 x) (@lem1638661 x h1)). Qed.
Lemma lem1638664 (x : real) (y : real) (h1 : term55) : term58 x y.
Proof. exact (@lem1638663 x h1 y). Qed.
Lemma lem1638665 (y : real) (x : real) : (term58 x y) = (term59 y x).
Proof. exact (eq_refl (term58 x y)). Qed.
Lemma lem1638666 (y : real) (x : real) (h1 : term55) : term59 y x.
Proof. exact (EQ_MP (@lem1638665 y x) (@lem1638664 x y h1)). Qed.
Lemma lem1638667 (y : real) (x : real) (z : real) (h1 : term55) : term60 y x z.
Proof. exact (@lem1638666 y x h1 z). Qed.
Lemma lem1638668 (y : real) (x : real) (z : real) : (term60 y x z) = (term61 y x z).
Proof. exact (eq_refl (term60 y x z)). Qed.
Lemma lem1638669 (y : real) (x : real) (z : real) (h1 : term55) : term61 y x z.
Proof. exact (EQ_MP (@lem1638668 y x z) (@lem1638667 y x z h1)). Qed.
Lemma lem1638670 (x : real) (y : real) (z : real) (h1 : term62 x y z) : term62 x y z.
Proof. exact (h1). Qed.
Lemma lem1638671 (x : real) (y : real) (z : real) (h1 : term55) (h2 : term62 x y z) : term63 y x z.
Proof. exact (@lem1638669 y x z h1 (@lem1638670 x y z h2)). Qed.
Lemma lem1638672 (x : real) (y : real) (z : real) (h1 : term62 x y z) : term64 y x z.
Proof. exact (fun h0 : term55 => @lem1638671 x y z h0 h1). Qed.
Lemma lem1638673 (h1 : term55) : term55.
Proof. exact (h1). Qed.
Lemma lem1638674 (x : real) (y : real) (z : real) (h1 : term55) (h2 : term62 x y z) : term63 y x z.
Proof. exact (@lem1638672 x y z h2 (@lem1638673 h1)). Qed.
Lemma lem1638675 (y : real) (x : real) (z : real) (h1 : term55) : term61 y x z.
Proof. exact (fun h0 : term62 x y z => @lem1638674 x y z h1 h0). Qed.
Lemma lem1638676 (y : real) (x : real) (h1 : term55) : term59 y x.
Proof. exact (fun z : real => @lem1638675 y x z h1). Qed.
Lemma lem1638677 (y : real) (h1 : term55) : term65 y.
Proof. exact (fun x : real => @lem1638676 y x h1). Qed.
Lemma lem1638678 (h1 : term55) : term66.
Proof. exact (fun y : real => @lem1638677 y h1). Qed.
Lemma lem1638679 : term67.
Proof. exact (fun h0 : term55 => @lem1638678 h0). Qed.
Lemma lem1638680 : term66.
Proof. exact (@lem1638679 (@lem1584766)). Qed.
Lemma lem1638681 (y : real) : term68 y.
Proof. exact (@lem1638680 y). Qed.
Lemma lem1638682 (y : real) : (term68 y) = (term65 y).
Proof. exact (eq_refl (term68 y)). Qed.
Lemma lem1638683 (y : real) : term65 y.
Proof. exact (EQ_MP (@lem1638682 y) (@lem1638681 y)). Qed.
Lemma lem1638684 (y : real) (x : real) : term69 y x.
Proof. exact (@lem1638683 y x). Qed.
Lemma lem1638685 (y : real) (x : real) : (term69 y x) = (term59 y x).
Proof. exact (eq_refl (term69 y x)). Qed.
Lemma lem1638686 (y : real) (x : real) : term59 y x.
Proof. exact (EQ_MP (@lem1638685 y x) (@lem1638684 y x)). Qed.
Lemma lem1638687 (y : real) (x : real) (z : real) : term60 y x z.
Proof. exact (@lem1638686 y x z). Qed.
Lemma lem1638688 (y : real) (x : real) (z : real) : (term60 y x z) = (term61 y x z).
Proof. exact (eq_refl (term60 y x z)). Qed.
Lemma lem1638691 (x : real) (h1 : (term70 x) = x) : (term70 x) = x.
Proof. exact (h1). Qed.
Lemma lem1638692 (x : real) (h1 : (term70 x) = x) : x = (term70 x).
Proof. exact (SYM (@lem1638691 x h1)). Qed.
Lemma lem1638693 (x : real) (h1 : x = (term70 x)) : x = (term70 x).
Proof. exact (h1). Qed.
Lemma lem1638694 (x : real) (h1 : x = (term70 x)) : (term70 x) = x.
Proof. exact (SYM (@lem1638693 x h1)). Qed.
Lemma lem1638695 (x : real) : ((term70 x) = x) = (x = (term70 x)).
Proof. exact (prop_ext (fun h1 : (term70 x) = x => @lem1638692 x h1) (fun h1 : x = (term70 x) => @lem1638694 x h1)). Qed.
Lemma lem1638696 : term71 = term72.
Proof. exact (fun_ext (fun x : real => @lem1638695 x)). Qed.
Lemma lem1638697 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1638698 : term73 = term74.
Proof. exact (MK_COMB (@lem1638697) (@lem1638696)). Qed.
Lemma lem1638699 : term74.
Proof. exact (EQ_MP (@lem1638698) (@lem1383409)). Qed.
Lemma lem1638700 (x : real) : term75 x.
Proof. exact (@lem1638699 x). Qed.
Lemma lem1638701 (x : real) : (term75 x) = (x = (term70 x)).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem1638703 (x : real) : term76 x.
Proof. exact (@lem1596102 x). Qed.
Lemma lem1638704 (x : real) : (term76 x) = (term77 x).
Proof. exact (eq_refl (term76 x)). Qed.
Lemma lem1638705 (x : real) : term77 x.
Proof. exact (EQ_MP (@lem1638704 x) (@lem1638703 x)). Qed.
Lemma lem1638706 (x : real) (m : nat) : term78 x m.
Proof. exact (@lem1638705 x m). Qed.
Lemma lem1638707 (m : nat) (x : real) : (term78 x m) = (term79 m x).
Proof. exact (eq_refl (term78 x m)). Qed.
Lemma lem1638708 (m : nat) (x : real) : term79 m x.
Proof. exact (EQ_MP (@lem1638707 m x) (@lem1638706 x m)). Qed.
Lemma lem1638709 (m : nat) (x : real) (n : nat) : term80 m x n.
Proof. exact (@lem1638708 m x n). Qed.
Lemma lem1638710 (m : nat) (x : real) (n : nat) : (term80 m x n) = ((term81 x m n) = (term82 m x n)).
Proof. exact (eq_refl (term80 m x n)). Qed.
Lemma lem1638712 (m : nat) : term83 m.
Proof. exact (@lem100361 m). Qed.
Lemma lem1638713 (m : nat) : (term83 m) = (term84 m).
Proof. exact (eq_refl (term83 m)). Qed.
Lemma lem1638714 (m : nat) : term84 m.
Proof. exact (EQ_MP (@lem1638713 m) (@lem1638712 m)). Qed.
Lemma lem1638715 (m : nat) (n : nat) : term85 m n.
Proof. exact (@lem1638714 m n). Qed.
Lemma lem1638716 (n : nat) (m : nat) : (term85 m n) = ((Peano.lt m n) = (term86 n m)).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem1638723 (n : nat) (m : nat) : (Peano.lt m n) = (term86 n m).
Proof. exact (EQ_MP (@lem1638716 n m) (@lem1638715 m n)). Qed.
Lemma lem1638730 (x : real) : (term87 x) = (term87 x).
Proof. exact (eq_refl (term87 x)). Qed.
Lemma lem1638731 (x : real) (n : nat) (m : nat) : (term88 x m n) = (term89 x n m).
Proof. exact (MK_COMB (@lem1638730 x) (@lem1638723 n m)). Qed.
Lemma lem1638734 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1638735 (x : real) (n : nat) (m : nat) : (term90 x m n) = (term91 x n m).
Proof. exact (MK_COMB (@lem1638734) (@lem1638731 x n m)). Qed.
Lemma lem1638736 (m : nat) (x : real) (n : nat) : (term92 m x n) = (term92 m x n).
Proof. exact (eq_refl (term92 m x n)). Qed.
Lemma lem1638737 (m : nat) (x : real) (n : nat) : (term93 m x n) = (term94 m x n).
Proof. exact (MK_COMB (@lem1638735 x n m) (@lem1638736 m x n)). Qed.
Lemma lem1638740 (m : nat) (x : real) (n : nat) : (term94 m x n) = (term93 m x n).
Proof. exact (SYM (@lem1638737 m x n)). Qed.
Lemma lem1638741 (x : real) (n : nat) (m : nat) (h1 : term89 x n m) : term89 x n m.
Proof. exact (h1). Qed.
Lemma lem1638742 (n : nat) (m : nat) (h1 : term86 n m) : term86 n m.
Proof. exact (h1). Qed.
Lemma lem1638743 (x : real) (h1 : term95 x) : term95 x.
Proof. exact (h1). Qed.
Lemma lem1638744 (n : nat) (m : nat) (h1 : term86 n m) : term86 n m.
Proof. exact (h1). Qed.
Lemma lem1638745 (n : nat) (m : nat) (d : nat) (h1 : n = (term96 m d)) : n = (term96 m d).
Proof. exact (h1). Qed.
Lemma lem1638746 (m : nat) (x : real) : (term97 m x) = (term97 m x).
Proof. exact (eq_refl (term97 m x)). Qed.
Lemma lem1638747 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (term96 m d)) : (term98 m x n) = (term99 x m d).
Proof. exact (MK_COMB (@lem1638746 m x) (@lem1638745 n m d h1)). Qed.
Lemma lem1638748 (x : real) (m : nat) (d : nat) : (term99 x m d) = (term100 x m d).
Proof. exact (eq_refl (term99 x m d)). Qed.
Lemma lem1638749 (m : nat) (x : real) (n : nat) : (term101 m x n) = (term101 m x n).
Proof. exact (eq_refl (term101 m x n)). Qed.
Lemma lem1638750 (n : nat) (x : real) (m : nat) (d : nat) : ((term98 m x n) = (term99 x m d)) = ((term98 m x n) = (term100 x m d)).
Proof. exact (MK_COMB (@lem1638749 m x n) (@lem1638748 x m d)). Qed.
Lemma lem1638751 (m : nat) (x : real) (n : nat) : (term98 m x n) = (term92 m x n).
Proof. exact (eq_refl (term98 m x n)). Qed.
Lemma lem1638752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1638753 (m : nat) (x : real) (n : nat) : (term101 m x n) = (term102 m x n).
Proof. exact (MK_COMB (@lem1638752) (@lem1638751 m x n)). Qed.
Lemma lem1638754 (x : real) (m : nat) (d : nat) : (term100 x m d) = (term100 x m d).
Proof. exact (eq_refl (term100 x m d)). Qed.
Lemma lem1638755 (n : nat) (x : real) (m : nat) (d : nat) : ((term98 m x n) = (term100 x m d)) = ((term92 m x n) = (term100 x m d)).
Proof. exact (MK_COMB (@lem1638753 m x n) (@lem1638754 x m d)). Qed.
Lemma lem1638756 (n : nat) (x : real) (m : nat) (d : nat) : ((term98 m x n) = (term99 x m d)) = ((term92 m x n) = (term100 x m d)).
Proof. exact (TRANS (@lem1638750 n x m d) (@lem1638755 n x m d)). Qed.
Lemma lem1638757 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (term96 m d)) : (term92 m x n) = (term100 x m d).
Proof. exact (EQ_MP (@lem1638756 n x m d) (@lem1638747 x n m d h1)). Qed.
Lemma lem1638758 (x : real) (n : nat) (m : nat) (d : nat) (h1 : n = (term96 m d)) : (term100 x m d) = (term92 m x n).
Proof. exact (SYM (@lem1638757 x n m d h1)). Qed.
Lemma lem1638772 (x : real) (h1 : term95 x) : term95 x.
Proof. exact (h1). Qed.
Lemma lem1638774 (m : nat) (x : real) (n : nat) : (term81 x m n) = (term82 m x n).
Proof. exact (EQ_MP (@lem1638710 m x n) (@lem1638709 m x n)). Qed.
Lemma lem1638775 (m : nat) (x : real) (d : nat) : (term103 x m d) = (term104 m x d).
Proof. exact (@lem1638774 m x (S d)). Qed.
Lemma lem1638776 (x : real) (m : nat) : (term105 x m) = (term105 x m).
Proof. exact (eq_refl (term105 x m)). Qed.
Lemma lem1638777 (m : nat) (x : real) (d : nat) : (term100 x m d) = (term106 m x d).
Proof. exact (MK_COMB (@lem1638776 x m) (@lem1638775 m x d)). Qed.
Lemma lem1638778 (x : real) (m : nat) (d : nat) : (term106 m x d) = (term100 x m d).
Proof. exact (SYM (@lem1638777 m x d)). Qed.
Lemma lem1638780 (x : real) : x = (term70 x).
Proof. exact (EQ_MP (@lem1638701 x) (@lem1638700 x)). Qed.
Lemma lem1638781 (x : real) (m : nat) : (real_pow x m) = (term107 x m).
Proof. exact (@lem1638780 (real_pow x m)). Qed.
Lemma lem1638782 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1638783 (x : real) (m : nat) : (term105 x m) = (term108 x m).
Proof. exact (MK_COMB (@lem1638782) (@lem1638781 x m)). Qed.
Lemma lem1638784 (m : nat) (x : real) (d : nat) : (term104 m x d) = (term104 m x d).
Proof. exact (eq_refl (term104 m x d)). Qed.
Lemma lem1638785 (m : nat) (x : real) (d : nat) : (term106 m x d) = (term109 m x d).
Proof. exact (MK_COMB (@lem1638783 x m) (@lem1638784 m x d)). Qed.
Lemma lem1638786 (m : nat) (x : real) (d : nat) : (term109 m x d) = (term106 m x d).
Proof. exact (SYM (@lem1638785 m x d)). Qed.
Lemma lem1638788 (y : real) (x : real) (z : real) : term61 y x z.
Proof. exact (EQ_MP (@lem1638688 y x z) (@lem1638687 y x z)). Qed.
Lemma lem1638789 (m : nat) (x : real) (d : nat) : term110 m x d.
Proof. exact (@lem1638788 term111 (real_pow x m) (term27 x d)). Qed.
Lemma lem1638791 (x : real) (n : nat) : term50 x n.
Proof. exact (EQ_MP (@lem1638658 x n) (@lem1638657 x n)). Qed.
Lemma lem1638792 (x : real) (m : nat) : term50 x m.
Proof. exact (@lem1638791 x m). Qed.
Lemma lem1638794 (x : real) (z : real) : term40 x z.
Proof. exact (EQ_MP (@lem1638635 x z) (@lem1638634 x z)). Qed.
Lemma lem1638795 (x : real) : term112 x.
Proof. exact (@lem1638794 term113 x). Qed.
Lemma lem1639007 : term114.
Proof. exact (EQ_MP (@lem520356) (@lem0)). Qed.
Lemma lem1639008 : term115.
Proof. exact (proj2 (@lem1639007)). Qed.
Lemma lem1639009 : term116.
Proof. exact (proj2 (@lem1639008)). Qed.
Lemma lem1639010 : term117.
Proof. exact (proj2 (@lem1639009)). Qed.
Lemma lem1639011 : term118.
Proof. exact (proj2 (@lem1639010)). Qed.
Lemma lem1639012 : term119.
Proof. exact (proj2 (@lem1639011)). Qed.
Lemma lem1639044 : term120.
Proof. exact (proj1 (@lem1639012)). Qed.
Lemma lem1639045 (n : nat) : term121 n.
Proof. exact (@lem1639044 n). Qed.
Lemma lem1639046 (n : nat) : (term121 n) = ((term122 n) = True).
Proof. exact (eq_refl (term121 n)). Qed.
Lemma lem1639061 : term123.
Proof. exact (proj1 (@lem1639007)). Qed.
Lemma lem1639062 (m : nat) : term124 m.
Proof. exact (@lem1639061 m). Qed.
Lemma lem1639063 (m : nat) : (term124 m) = (term125 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem1639064 (m : nat) : term125 m.
Proof. exact (EQ_MP (@lem1639063 m) (@lem1639062 m)). Qed.
Lemma lem1639065 (m : nat) (n : nat) : term126 m n.
Proof. exact (@lem1639064 m n). Qed.
Lemma lem1639066 (m : nat) (n : nat) : (term126 m n) = ((term127 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term126 m n)). Qed.
Lemma lem1639440 (m : nat) : term128 m.
Proof. exact (@lem1483667 m). Qed.
Lemma lem1639441 (m : nat) : (term128 m) = (term129 m).
Proof. exact (eq_refl (term128 m)). Qed.
Lemma lem1639442 (m : nat) : term129 m.
Proof. exact (EQ_MP (@lem1639441 m) (@lem1639440 m)). Qed.
Lemma lem1639443 (m : nat) (n : nat) : term130 m n.
Proof. exact (@lem1639442 m n). Qed.
Lemma lem1639444 (m : nat) (n : nat) : (term130 m n) = ((term131 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term130 m n)). Qed.
Lemma lem1639446 (x : real) : (term95 x) = ((term95 x) = True).
Proof. exact (@lem7 (term95 x)). Qed.
Lemma lem1639451 (m : nat) (n : nat) : (term131 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1639444 m n) (@lem1639443 m n)). Qed.
Lemma lem1639452 : term132 = term133.
Proof. exact (@lem1639451 (NUMERAL 0) term134). Qed.
Lemma lem1639454 (m : nat) (n : nat) : (term127 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem1639066 m n) (@lem1639065 m n)). Qed.
Lemma lem1639455 : term133 = term135.
Proof. exact (@lem1639454 0 (BIT1 0)). Qed.
Lemma lem1639457 (n : nat) : (term122 n) = True.
Proof. exact (EQ_MP (@lem1639046 n) (@lem1639045 n)). Qed.
Lemma lem1639458 : term135 = True.
Proof. exact (@lem1639457 0). Qed.
Lemma lem1639459 : term133 = True.
Proof. exact (TRANS (@lem1639455) (@lem1639458)). Qed.
Lemma lem1639460 : term132 = True.
Proof. exact (TRANS (@lem1639452) (@lem1639459)). Qed.
Lemma lem1639461 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1639462 : term136 = (and True).
Proof. exact (MK_COMB (@lem1639461) (@lem1639460)). Qed.
Lemma lem1639464 (x : real) (h1 : term95 x) : (term95 x) = True.
Proof. exact (EQ_MP (@lem1639446 x) (@lem1638772 x h1)). Qed.
Lemma lem1639465 (x : real) (h1 : term95 x) : (term137 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1639462) (@lem1639464 x h1)). Qed.
Lemma lem1639467 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1639468 : (True /\ True) = True.
Proof. exact (@lem1639467 True). Qed.
Lemma lem1639469 (x : real) (h1 : term95 x) : (term137 x) = True.
Proof. exact (TRANS (@lem1639465 x h1) (@lem1639468)). Qed.
Lemma lem1639470 (x : real) (h1 : term95 x) : True = (term137 x).
Proof. exact (SYM (@lem1639469 x h1)). Qed.
Lemma lem1639471 (x : real) (h1 : term95 x) : term137 x.
Proof. exact (EQ_MP (@lem1639470 x h1) (@lem0)). Qed.
Lemma lem1639472 (x : real) (h1 : term95 x) : term138 x.
Proof. exact (ex_intro (term139 x) term111 (@lem1639471 x h1)). Qed.
Lemma lem1639473 (x : real) (h1 : term95 x) : term51 x.
Proof. exact (@lem1638795 x (@lem1639472 x h1)). Qed.
Lemma lem1639474 (m : nat) (x : real) (h1 : term95 x) : term52 x m.
Proof. exact (@lem1638792 x m (@lem1639473 x h1)). Qed.
Lemma lem1639476 (P : nat -> Prop) : term140 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem1639477 (x : real) : term141 x.
Proof. exact (@lem1639476 (term142 x)). Qed.
Lemma lem1639478 (x : real) : (term143 x) = (term144 x).
Proof. exact (eq_refl (term143 x)). Qed.
Lemma lem1639479 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1639480 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1639479) (@lem1639478 x)). Qed.
Lemma lem1639481 (x : real) (d : nat) : (term147 x d) = (term148 x d).
Proof. exact (eq_refl (term147 x d)). Qed.
Lemma lem1639482 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1639483 (x : real) (d : nat) : (term149 x d) = (term150 x d).
Proof. exact (MK_COMB (@lem1639482) (@lem1639481 x d)). Qed.
Lemma lem1639484 (x : real) (d : nat) : (term151 x d) = (term152 x d).
Proof. exact (eq_refl (term151 x d)). Qed.
Lemma lem1639485 (x : real) (d : nat) : (term153 x d) = (term154 x d).
Proof. exact (MK_COMB (@lem1639483 x d) (@lem1639484 x d)). Qed.
Lemma lem1639486 (x : real) : (term155 x) = (term156 x).
Proof. exact (fun_ext (fun d : nat => @lem1639485 x d)). Qed.
Lemma lem1639487 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1639488 (x : real) : (term157 x) = (term158 x).
Proof. exact (MK_COMB (@lem1639487) (@lem1639486 x)). Qed.
Lemma lem1639489 (x : real) : (term159 x) = (term160 x).
Proof. exact (MK_COMB (@lem1639480 x) (@lem1639488 x)). Qed.
Lemma lem1639490 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1639491 (x : real) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem1639490) (@lem1639489 x)). Qed.
Lemma lem1639492 (x : real) (d : nat) : (term147 x d) = (term148 x d).
Proof. exact (eq_refl (term147 x d)). Qed.
Lemma lem1639493 (x : real) : (term163 x) = (term142 x).
Proof. exact (fun_ext (fun d : nat => @lem1639492 x d)). Qed.
Lemma lem1639494 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1639495 (x : real) : (term164 x) = (term165 x).
Proof. exact (MK_COMB (@lem1639494) (@lem1639493 x)). Qed.
Lemma lem1639496 (x : real) : (term141 x) = (term166 x).
Proof. exact (MK_COMB (@lem1639491 x) (@lem1639495 x)). Qed.
Lemma lem1639497 (x : real) : term166 x.
Proof. exact (EQ_MP (@lem1639496 x) (@lem1639477 x)). Qed.
Lemma lem1639498 (x : real) (d : nat) (h1 : term148 x d) : term148 x d.
Proof. exact (h1). Qed.
Lemma lem1639500 (x : real) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (EQ_MP (@lem1638606 x n) (@lem1638605 x n)). Qed.
Lemma lem1639501 (x : real) : (term167 x) = (term168 x).
Proof. exact (@lem1639500 x (NUMERAL 0)). Qed.
Lemma lem1639502 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem1639503 (x : real) : (term144 x) = (term170 x).
Proof. exact (MK_COMB (@lem1639502) (@lem1639501 x)). Qed.
Lemma lem1639504 (x : real) : (term170 x) = (term144 x).
Proof. exact (SYM (@lem1639503 x)). Qed.
Lemma lem1639506 (x : real) (n : nat) : (term27 x n) = (term28 x n).
Proof. exact (EQ_MP (@lem1638606 x n) (@lem1638605 x n)). Qed.
Lemma lem1639507 (x : real) (d : nat) : (term171 x d) = (term172 x d).
Proof. exact (@lem1639506 x (S d)). Qed.
Lemma lem1639508 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem1639509 (x : real) (d : nat) : (term152 x d) = (term173 x d).
Proof. exact (MK_COMB (@lem1639508) (@lem1639507 x d)). Qed.
Lemma lem1639510 (x : real) (d : nat) : (term173 x d) = (term152 x d).
Proof. exact (SYM (@lem1639509 x d)). Qed.
Lemma lem1639511 (x : real) : term174 x.
Proof. exact (@lem1383409 x). Qed.
Lemma lem1639512 (x : real) : (term174 x) = ((term70 x) = x).
Proof. exact (eq_refl (term174 x)). Qed.
Lemma lem1639519 (x : real) : (term95 x) = ((term95 x) = True).
Proof. exact (@lem7 (term95 x)). Qed.
Lemma lem1639522 (x : real) : (term175 x) = term111.
Proof. exact (EQ_MP (@lem1344311 x) (@lem1344310 x)). Qed.
Lemma lem1639523 (x : real) : (real_mul x) = (real_mul x).
Proof. exact (eq_refl (real_mul x)). Qed.
Lemma lem1639524 (x : real) : (term168 x) = (term70 x).
Proof. exact (MK_COMB (@lem1639523 x) (@lem1639522 x)). Qed.
Lemma lem1639526 (x : real) : (term70 x) = x.
Proof. exact (EQ_MP (@lem1639512 x) (@lem1639511 x)). Qed.
Lemma lem1639527 (x : real) : (term168 x) = x.
Proof. exact (TRANS (@lem1639524 x) (@lem1639526 x)). Qed.
Lemma lem1639528 : term169 = term169.
Proof. exact (eq_refl term169). Qed.
Lemma lem1639529 (x : real) : (term170 x) = (term95 x).
Proof. exact (MK_COMB (@lem1639528) (@lem1639527 x)). Qed.
Lemma lem1639531 (x : real) (h1 : term95 x) : (term95 x) = True.
Proof. exact (EQ_MP (@lem1639519 x) (@lem1638772 x h1)). Qed.
Lemma lem1639532 (x : real) (h1 : term95 x) : (term170 x) = True.
Proof. exact (TRANS (@lem1639529 x) (@lem1639531 x h1)). Qed.
Lemma lem1639533 (x : real) (h1 : term95 x) : True = (term170 x).
Proof. exact (SYM (@lem1639532 x h1)). Qed.
Lemma lem1639534 (x : real) (h1 : term95 x) : term170 x.
Proof. exact (EQ_MP (@lem1639533 x h1) (@lem0)). Qed.
Lemma lem1639536 (x : real) : x = (term19 x).
Proof. exact (EQ_MP (@lem1638602 x) (@lem1638601 x)). Qed.
Lemma lem1639537 : term111 = term176.
Proof. exact (@lem1639536 term111). Qed.
Lemma lem1639538 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1639539 : term169 = term177.
Proof. exact (MK_COMB (@lem1639538) (@lem1639537)). Qed.
Lemma lem1639540 (x : real) (d : nat) : (term172 x d) = (term172 x d).
Proof. exact (eq_refl (term172 x d)). Qed.
Lemma lem1639541 (x : real) (d : nat) : (term173 x d) = (term178 x d).
Proof. exact (MK_COMB (@lem1639539) (@lem1639540 x d)). Qed.
Lemma lem1639542 (x : real) (d : nat) : (term178 x d) = (term173 x d).
Proof. exact (SYM (@lem1639541 x d)). Qed.
Lemma lem1639544 (w : real) (y : real) (x : real) (z : real) : term8 w y x z.
Proof. exact (EQ_MP (@lem1638589 w y x z) (@lem1638588 w y x z)). Qed.
Lemma lem1639545 (x : real) (d : nat) : term179 x d.
Proof. exact (@lem1639544 term111 term111 x (term27 x d)). Qed.
Lemma lem1639818 : term180.
Proof. exact (EQ_MP (@lem517422) (@lem519779)). Qed.
Lemma lem1639819 : term181.
Proof. exact (proj2 (@lem1639818)). Qed.
Lemma lem1639820 : term182.
Proof. exact (proj2 (@lem1639819)). Qed.
Lemma lem1639821 : term183.
Proof. exact (proj2 (@lem1639820)). Qed.
Lemma lem1639822 : term184.
Proof. exact (proj2 (@lem1639821)). Qed.
Lemma lem1639823 : term185.
Proof. exact (proj2 (@lem1639822)). Qed.
Lemma lem1639855 : term186.
Proof. exact (proj1 (@lem1639823)). Qed.
Lemma lem1639856 (n : nat) : term187 n.
Proof. exact (@lem1639855 n). Qed.
Lemma lem1639857 (n : nat) : (term187 n) = ((term188 n) = True).
Proof. exact (eq_refl (term187 n)). Qed.
Lemma lem1639872 : term189.
Proof. exact (proj1 (@lem1639818)). Qed.
Lemma lem1639873 (m : nat) : term190 m.
Proof. exact (@lem1639872 m). Qed.
Lemma lem1639874 (m : nat) : (term190 m) = (term191 m).
Proof. exact (eq_refl (term190 m)). Qed.
Lemma lem1639875 (m : nat) : term191 m.
Proof. exact (EQ_MP (@lem1639874 m) (@lem1639873 m)). Qed.
Lemma lem1639876 (m : nat) (n : nat) : term192 m n.
Proof. exact (@lem1639875 m n). Qed.
Lemma lem1639877 (m : nat) (n : nat) : (term192 m n) = ((term193 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term192 m n)). Qed.
Lemma lem1640190 (m : nat) : term194 m.
Proof. exact (@lem1340282 m). Qed.
Lemma lem1640191 (m : nat) : (term194 m) = (term195 m).
Proof. exact (eq_refl (term194 m)). Qed.
Lemma lem1640192 (m : nat) : term195 m.
Proof. exact (EQ_MP (@lem1640191 m) (@lem1640190 m)). Qed.
Lemma lem1640193 (m : nat) (n : nat) : term196 m n.
Proof. exact (@lem1640192 m n). Qed.
Lemma lem1640194 (m : nat) (n : nat) : (term196 m n) = ((term197 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term196 m n)). Qed.
Lemma lem1640196 (x : real) : (term95 x) = ((term95 x) = True).
Proof. exact (@lem7 (term95 x)). Qed.
Lemma lem1640198 (x : real) (d : nat) : (term148 x d) = ((term148 x d) = True).
Proof. exact (@lem7 (term148 x d)). Qed.
Lemma lem1640203 (m : nat) (n : nat) : (term197 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1640194 m n) (@lem1640193 m n)). Qed.
Lemma lem1640204 : term198 = term199.
Proof. exact (@lem1640203 (NUMERAL 0) term134). Qed.
Lemma lem1640206 (m : nat) (n : nat) : (term193 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1639877 m n) (@lem1639876 m n)). Qed.
Lemma lem1640207 : term199 = term200.
Proof. exact (@lem1640206 0 (BIT1 0)). Qed.
Lemma lem1640209 (n : nat) : (term188 n) = True.
Proof. exact (EQ_MP (@lem1639857 n) (@lem1639856 n)). Qed.
Lemma lem1640210 : term200 = True.
Proof. exact (@lem1640209 0). Qed.
Lemma lem1640211 : term199 = True.
Proof. exact (TRANS (@lem1640207) (@lem1640210)). Qed.
Lemma lem1640212 : term198 = True.
Proof. exact (TRANS (@lem1640204) (@lem1640211)). Qed.
Lemma lem1640213 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640214 : term201 = (and True).
Proof. exact (MK_COMB (@lem1640213) (@lem1640212)). Qed.
Lemma lem1640218 (x : real) (h1 : term95 x) : (term95 x) = True.
Proof. exact (EQ_MP (@lem1640196 x) (@lem1638772 x h1)). Qed.
Lemma lem1640219 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640220 (x : real) (h1 : term95 x) : (term87 x) = (and True).
Proof. exact (MK_COMB (@lem1640219) (@lem1640218 x h1)). Qed.
Lemma lem1640224 (m : nat) (n : nat) : (term197 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1640194 m n) (@lem1640193 m n)). Qed.
Lemma lem1640225 : term198 = term199.
Proof. exact (@lem1640224 (NUMERAL 0) term134). Qed.
Lemma lem1640227 (m : nat) (n : nat) : (term193 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1639877 m n) (@lem1639876 m n)). Qed.
Lemma lem1640228 : term199 = term200.
Proof. exact (@lem1640227 0 (BIT1 0)). Qed.
Lemma lem1640230 (n : nat) : (term188 n) = True.
Proof. exact (EQ_MP (@lem1639857 n) (@lem1639856 n)). Qed.
Lemma lem1640231 : term200 = True.
Proof. exact (@lem1640230 0). Qed.
Lemma lem1640232 : term199 = True.
Proof. exact (TRANS (@lem1640228) (@lem1640231)). Qed.
Lemma lem1640233 : term198 = True.
Proof. exact (TRANS (@lem1640225) (@lem1640232)). Qed.
Lemma lem1640234 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1640235 : term201 = (and True).
Proof. exact (MK_COMB (@lem1640234) (@lem1640233)). Qed.
Lemma lem1640237 (x : real) (d : nat) (h1 : term148 x d) : (term148 x d) = True.
Proof. exact (EQ_MP (@lem1640198 x d) (@lem1639498 x d h1)). Qed.
Lemma lem1640238 (x : real) (d : nat) (h1 : term148 x d) : (term202 x d) = (True /\ True).
Proof. exact (MK_COMB (@lem1640235) (@lem1640237 x d h1)). Qed.
Lemma lem1640240 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1640241 : (True /\ True) = True.
Proof. exact (@lem1640240 True). Qed.
Lemma lem1640242 (x : real) (d : nat) (h1 : term148 x d) : (term202 x d) = True.
Proof. exact (TRANS (@lem1640238 x d h1) (@lem1640241)). Qed.
Lemma lem1640243 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : (term203 x d) = (True /\ True).
Proof. exact (MK_COMB (@lem1640220 x h1) (@lem1640242 x d h2)). Qed.
Lemma lem1640245 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1640246 : (True /\ True) = True.
Proof. exact (@lem1640245 True). Qed.
Lemma lem1640247 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : (term203 x d) = True.
Proof. exact (TRANS (@lem1640243 x d h1 h2) (@lem1640246)). Qed.
Lemma lem1640248 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : (term204 x d) = (True /\ True).
Proof. exact (MK_COMB (@lem1640214) (@lem1640247 x d h1 h2)). Qed.
Lemma lem1640250 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1640251 : (True /\ True) = True.
Proof. exact (@lem1640250 True). Qed.
Lemma lem1640252 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : (term204 x d) = True.
Proof. exact (TRANS (@lem1640248 x d h1 h2) (@lem1640251)). Qed.
Lemma lem1640253 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : True = (term204 x d).
Proof. exact (SYM (@lem1640252 x d h1 h2)). Qed.
Lemma lem1640254 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : term204 x d.
Proof. exact (EQ_MP (@lem1640253 x d h1 h2) (@lem0)). Qed.
Lemma lem1640255 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : term178 x d.
Proof. exact (@lem1639545 x d (@lem1640254 x d h1 h2)). Qed.
Lemma lem1640256 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : term173 x d.
Proof. exact (EQ_MP (@lem1639542 x d) (@lem1640255 x d h1 h2)). Qed.
Lemma lem1640257 (x : real) (d : nat) (h1 : term95 x) (h2 : term148 x d) : term152 x d.
Proof. exact (EQ_MP (@lem1639510 x d) (@lem1640256 x d h1 h2)). Qed.
Lemma lem1640258 (x : real) (h1 : term95 x) : term144 x.
Proof. exact (EQ_MP (@lem1639504 x) (@lem1639534 x h1)). Qed.
Lemma lem1640259 (d : nat) (x : real) (h1 : term95 x) : term154 x d.
Proof. exact (fun h0 : term148 x d => @lem1640257 x d h1 h0). Qed.
Lemma lem1640264 (x : real) (h1 : term95 x) : term158 x.
Proof. exact (fun d : nat => @lem1640259 d x h1). Qed.
Lemma lem1640265 (x : real) (h1 : term95 x) : term160 x.
Proof. exact (conj (@lem1640258 x h1) (@lem1640264 x h1)). Qed.
Lemma lem1640266 (x : real) (h1 : term95 x) : term165 x.
Proof. exact (@lem1639497 x (@lem1640265 x h1)). Qed.
Lemma lem1640267 (d : nat) (x : real) (h1 : term95 x) : term147 x d.
Proof. exact (@lem1640266 x h1 d). Qed.
Lemma lem1640268 (x : real) (d : nat) : (term147 x d) = (term148 x d).
Proof. exact (eq_refl (term147 x d)). Qed.
Lemma lem1640269 (d : nat) (x : real) (h1 : term95 x) : term148 x d.
Proof. exact (EQ_MP (@lem1640268 x d) (@lem1640267 d x h1)). Qed.
Lemma lem1640270 (m : nat) (d : nat) (x : real) (h1 : term95 x) : term205 m x d.
Proof. exact (conj (@lem1639474 m x h1) (@lem1640269 d x h1)). Qed.
Lemma lem1640271 (m : nat) (d : nat) (x : real) (h1 : term95 x) : term109 m x d.
Proof. exact (@lem1638789 m x d (@lem1640270 m d x h1)). Qed.
Lemma lem1640272 (m : nat) (d : nat) (x : real) (h1 : term95 x) : term106 m x d.
Proof. exact (EQ_MP (@lem1638786 m x d) (@lem1640271 m d x h1)). Qed.
Lemma lem1640273 (m : nat) (d : nat) (x : real) (h1 : term95 x) : term100 x m d.
Proof. exact (EQ_MP (@lem1638778 x m d) (@lem1640272 m d x h1)). Qed.
Lemma lem1640274 (m : nat) (d : nat) (x : real) (h1 : term95 x) : (term95 x) = (term100 x m d).
Proof. exact (prop_ext (fun h2 : term95 x => @lem1640273 m d x h1) (fun h2 : term100 x m d => @lem1638772 x h1)). Qed.
Lemma lem1640275 (m : nat) (d : nat) (x : real) (h1 : term95 x) : term100 x m d.
Proof. exact (EQ_MP (@lem1640274 m d x h1) (@lem1638772 x h1)). Qed.
Lemma lem1640276 (n : nat) (m : nat) (d : nat) (x : real) (h1 : n = (term96 m d)) (h2 : term95 x) : term92 m x n.
Proof. exact (EQ_MP (@lem1638758 x n m d h1) (@lem1640275 m d x h2)). Qed.
Lemma lem1640277 (n : nat) (m : nat) (x : real) (h1 : term86 n m) (h2 : term95 x) : term92 m x n.
Proof. exact (ex_elim (@lem1638744 n m h1) (fun d : nat => fun h0 : term206 n m d => @lem1640276 n m d x h0 h2)). Qed.
Lemma lem1640278 (m : nat) (n : nat) (x : real) (h1 : term95 x) : term207 m x n.
Proof. exact (fun h0 : term86 n m => @lem1640277 n m x h0 h1). Qed.
Lemma lem1640279 (x : real) (n : nat) (m : nat) (h1 : term89 x n m) : term86 n m.
Proof. exact (proj2 (@lem1638741 x n m h1)). Qed.
Lemma lem1640280 (x : real) (n : nat) (m : nat) (h1 : term89 x n m) : term95 x.
Proof. exact (proj1 (@lem1638741 x n m h1)). Qed.
Lemma lem1640281 (n : nat) (m : nat) (x : real) (h1 : term86 n m) (h2 : term95 x) : term92 m x n.
Proof. exact (@lem1640278 m n x h2 (@lem1638742 n m h1)). Qed.
Lemma lem1640282 (n : nat) (m : nat) (x : real) (h1 : term86 n m) (h2 : term95 x) : (term95 x) = (term92 m x n).
Proof. exact (prop_ext (fun h3 : term95 x => @lem1640281 n m x h1 h2) (fun h3 : term92 m x n => @lem1638743 x h2)). Qed.
Lemma lem1640283 (n : nat) (m : nat) (x : real) (h1 : term86 n m) (h2 : term95 x) : term92 m x n.
Proof. exact (EQ_MP (@lem1640282 n m x h1 h2) (@lem1638743 x h2)). Qed.
Lemma lem1640284 (n : nat) (m : nat) (x : real) (h1 : term89 x n m) (h2 : term95 x) : (term86 n m) = (term92 m x n).
Proof. exact (prop_ext (fun h3 : term86 n m => @lem1640283 n m x h3 h2) (fun h3 : term92 m x n => @lem1640279 x n m h1)). Qed.
Lemma lem1640285 (n : nat) (m : nat) (x : real) (h1 : term89 x n m) (h2 : term95 x) : term92 m x n.
Proof. exact (EQ_MP (@lem1640284 n m x h1 h2) (@lem1640279 x n m h1)). Qed.
Lemma lem1640286 (x : real) (n : nat) (m : nat) (h1 : term89 x n m) : (term95 x) = (term92 m x n).
Proof. exact (prop_ext (fun h2 : term95 x => @lem1640285 n m x h1 h2) (fun h2 : term92 m x n => @lem1640280 x n m h1)). Qed.
Lemma lem1640287 (x : real) (n : nat) (m : nat) (h1 : term89 x n m) : term92 m x n.
Proof. exact (EQ_MP (@lem1640286 x n m h1) (@lem1640280 x n m h1)). Qed.
Lemma lem1640288 (m : nat) (x : real) (n : nat) : term94 m x n.
Proof. exact (fun h0 : term89 x n m => @lem1640287 x n m h0). Qed.
Lemma lem1640289 (m : nat) (x : real) (n : nat) : term93 m x n.
Proof. exact (EQ_MP (@lem1638740 m x n) (@lem1640288 m x n)). Qed.
Lemma lem1640294 (m : nat) (n : nat) : term208 m n.
Proof. exact (fun x : real => @lem1640289 m x n). Qed.
Lemma lem1640299 (m : nat) : term209 m.
Proof. exact (fun n : nat => @lem1640294 m n). Qed.
Lemma lem1640304 : term210.
Proof. exact (fun m : nat => @lem1640299 m). Qed.
