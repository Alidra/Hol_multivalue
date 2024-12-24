Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_LE_LADD_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import NADD_ADD_SYM_spec.
Require Import NADD_LE_RADD_spec.
Require Import NADD_LE_WELLDEF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1281483 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1281484 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1281485 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1281484 t1) (@lem1281483 t1)). Qed.
Lemma lem1281486 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1281485 t1 t2). Qed.
Lemma lem1281487 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1281488 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1281487 t1 t2) (@lem1281486 t1 t2)). Qed.
Lemma lem1281489 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1281488 t1 t2 t3). Qed.
Lemma lem1281490 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1281491 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1281490 t1 t2 t3) (@lem1281489 t1 t2 t3)). Qed.
Lemma lem1281492 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1281491 t1 t2 t3)). Qed.
Lemma lem1281494 (p : Prop) : p = (term7 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1281495 : term8 = term9.
Proof. exact (@lem1281494 term8). Qed.
Lemma lem1281496 : term9 = term8.
Proof. exact (SYM (@lem1281495)). Qed.
Lemma lem1281497 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1281500 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1281501 : term12.
Proof. exact (fun h0 : term11 => @lem1281500 h0). Qed.
Lemma lem1281502 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1281503 (h1 : term11) : term11.
Proof. exact (h1). Qed.
Lemma lem1281504 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1281502 h2 (@lem1281503 h1)). Qed.
Lemma lem1281505 (h1 : term11) : term13.
Proof. exact (fun h0 : term12 => @lem1281504 h1 h0). Qed.
Lemma lem1281506 (h1 : term12) : term12.
Proof. exact (h1). Qed.
Lemma lem1281507 (h1 : term11) (h2 : term12) : term11.
Proof. exact (@lem1281505 h1 (@lem1281506 h2)). Qed.
Lemma lem1281508 (h1 : term12) : term12.
Proof. exact (fun h0 : term11 => @lem1281507 h0 h1). Qed.
Lemma lem1281509 : term14.
Proof. exact (fun h0 : term12 => @lem1281508 h0). Qed.
Lemma lem1281512 : term12.
Proof. exact (@lem1281509 (@lem1281501)). Qed.
Lemma lem1281560 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1281561 : term15 = term16.
Proof. exact (@lem1281560 term17). Qed.
Lemma lem1281574 : term18 = term18.
Proof. exact (eq_refl term18). Qed.
Lemma lem1281575 : term19 = term20.
Proof. exact (MK_COMB (@lem1281574) (@lem1281561)). Qed.
Lemma lem1281578 : term21 = term21.
Proof. exact (eq_refl term21). Qed.
Lemma lem1281579 : term22 = term23.
Proof. exact (MK_COMB (@lem1281578) (@lem1281575)). Qed.
Lemma lem1281582 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem1281589 : term11 = term25.
Proof. exact (MK_COMB (@lem1281582) (@lem1281579)). Qed.
Lemma lem1281594 (z : nadd) (x : nadd) (y : nadd) : ((term26 x y z) = (nadd_le x y)) = ((term26 x y z) = (nadd_le x y)).
Proof. exact (eq_refl ((term26 x y z) = (nadd_le x y))). Qed.
Lemma lem1281595 (x : nadd) (y : nadd) : (term27 x y) = (term27 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1281594 z x y)). Qed.
Lemma lem1281596 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281597 (x : nadd) (y : nadd) : (term28 x y) = (term28 x y).
Proof. exact (MK_COMB (@lem1281596) (@lem1281595 x y)). Qed.
Lemma lem1281598 (x : nadd) : (term29 x) = (term29 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281597 x y)). Qed.
Lemma lem1281599 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281600 (x : nadd) : (term30 x) = (term30 x).
Proof. exact (MK_COMB (@lem1281599) (@lem1281598 x)). Qed.
Lemma lem1281601 : term31 = term31.
Proof. exact (fun_ext (fun x : nadd => @lem1281600 x)). Qed.
Lemma lem1281602 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281603 : term17 = term17.
Proof. exact (MK_COMB (@lem1281602) (@lem1281601)). Qed.
Lemma lem1281604 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1281605 : term16 = term16.
Proof. exact (MK_COMB (@lem1281604) (@lem1281603)). Qed.
Lemma lem1281606 (y : nadd) (x : nadd) : (term32 y x) = (term32 y x).
Proof. exact (eq_refl (term32 y x)). Qed.
Lemma lem1281607 (x : nadd) : (term33 x) = (term33 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281606 y x)). Qed.
Lemma lem1281608 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281609 (x : nadd) : (term34 x) = (term34 x).
Proof. exact (MK_COMB (@lem1281608) (@lem1281607 x)). Qed.
Lemma lem1281610 : term35 = term35.
Proof. exact (fun_ext (fun x : nadd => @lem1281609 x)). Qed.
Lemma lem1281611 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281612 : term36 = term36.
Proof. exact (MK_COMB (@lem1281611) (@lem1281610)). Qed.
Lemma lem1281613 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1281614 : term18 = term18.
Proof. exact (MK_COMB (@lem1281613) (@lem1281612)). Qed.
Lemma lem1281615 : term20 = term20.
Proof. exact (MK_COMB (@lem1281614) (@lem1281605)). Qed.
Lemma lem1281628 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term37 x y x' y') = (term37 x y x' y').
Proof. exact (eq_refl (term37 x y x' y')). Qed.
Lemma lem1281629 (x : nadd) (y : nadd) (x' : nadd) : (term38 x y x') = (term38 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1281628 x y x' y')). Qed.
Lemma lem1281630 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281631 (x : nadd) (y : nadd) (x' : nadd) : (term39 x y x') = (term39 x y x').
Proof. exact (MK_COMB (@lem1281630) (@lem1281629 x y x')). Qed.
Lemma lem1281632 (x : nadd) (x' : nadd) : (term40 x x') = (term40 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1281631 x y x')). Qed.
Lemma lem1281633 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281634 (x : nadd) (x' : nadd) : (term41 x x') = (term41 x x').
Proof. exact (MK_COMB (@lem1281633) (@lem1281632 x x')). Qed.
Lemma lem1281635 (x : nadd) : (term42 x) = (term42 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1281634 x x')). Qed.
Lemma lem1281636 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281637 (x : nadd) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1281636) (@lem1281635 x)). Qed.
Lemma lem1281638 : term44 = term44.
Proof. exact (fun_ext (fun x : nadd => @lem1281637 x)). Qed.
Lemma lem1281639 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281640 : term45 = term45.
Proof. exact (MK_COMB (@lem1281639) (@lem1281638)). Qed.
Lemma lem1281641 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1281642 : term21 = term21.
Proof. exact (MK_COMB (@lem1281641) (@lem1281640)). Qed.
Lemma lem1281643 : term23 = term23.
Proof. exact (MK_COMB (@lem1281642) (@lem1281615)). Qed.
Lemma lem1281648 (x : nadd) (y : nadd) (z : nadd) : ((term46 y x z) = (nadd_le y z)) = ((term46 y x z) = (nadd_le y z)).
Proof. exact (eq_refl ((term46 y x z) = (nadd_le y z))). Qed.
Lemma lem1281649 (x : nadd) (y : nadd) : (term47 x y) = (term47 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1281648 x y z)). Qed.
Lemma lem1281650 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281651 (x : nadd) (y : nadd) : (term48 x y) = (term48 x y).
Proof. exact (MK_COMB (@lem1281650) (@lem1281649 x y)). Qed.
Lemma lem1281652 (x : nadd) : (term49 x) = (term49 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281651 x y)). Qed.
Lemma lem1281653 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281654 (x : nadd) : (term50 x) = (term50 x).
Proof. exact (MK_COMB (@lem1281653) (@lem1281652 x)). Qed.
Lemma lem1281655 : term51 = term51.
Proof. exact (fun_ext (fun x : nadd => @lem1281654 x)). Qed.
Lemma lem1281656 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1281657 : term8 = term8.
Proof. exact (MK_COMB (@lem1281656) (@lem1281655)). Qed.
Lemma lem1281658 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1281659 : term10 = term10.
Proof. exact (MK_COMB (@lem1281658) (@lem1281657)). Qed.
Lemma lem1281660 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1281661 : term24 = term24.
Proof. exact (MK_COMB (@lem1281660) (@lem1281659)). Qed.
Lemma lem1281662 : term25 = term25.
Proof. exact (MK_COMB (@lem1281661) (@lem1281643)). Qed.
Lemma lem1281747 : term11 = term25.
Proof. exact (TRANS (@lem1281589) (@lem1281662)). Qed.
Lemma lem1281748 : term25 = term11.
Proof. exact (SYM (@lem1281747)). Qed.
Lemma lem1281749 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1281750 (h1 : term45) : term45.
Proof. exact (h1). Qed.
Lemma lem1281751 (h1 : term36) : term36.
Proof. exact (h1). Qed.
Lemma lem1281752 (h1 : term17) : term17.
Proof. exact (h1). Qed.
Lemma lem1281767 (x : nadd) (y : nadd) (z : nadd) : (term52 x y z) = (term53 x y z).
Proof. exact (@lem17646 (term46 y x z) (nadd_le y z)). Qed.
Lemma lem1281768 (P : nadd -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1281769 (x : nadd) (y : nadd) : (term56 x y) = (term57 x y).
Proof. exact (@lem1281768 (term47 x y)). Qed.
Lemma lem1281770 (x : nadd) (y : nadd) (z : nadd) : (term58 x y z) = ((term46 y x z) = (nadd_le y z)).
Proof. exact (eq_refl (term58 x y z)). Qed.
Lemma lem1281771 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1281772 (x : nadd) (y : nadd) (z : nadd) : (term59 x y z) = (term52 x y z).
Proof. exact (MK_COMB (@lem1281771) (@lem1281770 x y z)). Qed.
Lemma lem1281773 (x : nadd) (y : nadd) (z : nadd) : (term59 x y z) = (term53 x y z).
Proof. exact (TRANS (@lem1281772 x y z) (@lem1281767 x y z)). Qed.
Lemma lem1281774 (x : nadd) (y : nadd) : (term60 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1281773 x y z)). Qed.
Lemma lem1281775 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281776 (x : nadd) (y : nadd) : (term57 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1281775) (@lem1281774 x y)). Qed.
Lemma lem1281777 (x : nadd) (y : nadd) : (term56 x y) = (term62 x y).
Proof. exact (TRANS (@lem1281769 x y) (@lem1281776 x y)). Qed.
Lemma lem1281778 (P : nadd -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1281779 (x : nadd) : (term63 x) = (term64 x).
Proof. exact (@lem1281778 (term49 x)). Qed.
Lemma lem1281780 (x : nadd) (y : nadd) : (term65 x y) = (term48 x y).
Proof. exact (eq_refl (term65 x y)). Qed.
Lemma lem1281781 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1281782 (x : nadd) (y : nadd) : (term66 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem1281781) (@lem1281780 x y)). Qed.
Lemma lem1281783 (x : nadd) (y : nadd) : (term66 x y) = (term62 x y).
Proof. exact (TRANS (@lem1281782 x y) (@lem1281777 x y)). Qed.
Lemma lem1281784 (x : nadd) : (term67 x) = (term68 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281783 x y)). Qed.
Lemma lem1281785 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281786 (x : nadd) : (term64 x) = (term69 x).
Proof. exact (MK_COMB (@lem1281785) (@lem1281784 x)). Qed.
Lemma lem1281787 (x : nadd) : (term63 x) = (term69 x).
Proof. exact (TRANS (@lem1281779 x) (@lem1281786 x)). Qed.
Lemma lem1281788 (P : nadd -> Prop) : (term54 P) = (term55 P).
Proof. exact (@lem18392 nadd P). Qed.
Lemma lem1281789 : term10 = term70.
Proof. exact (@lem1281788 term51). Qed.
Lemma lem1281790 (x : nadd) : (term71 x) = (term50 x).
Proof. exact (eq_refl (term71 x)). Qed.
Lemma lem1281791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1281792 (x : nadd) : (term72 x) = (term63 x).
Proof. exact (MK_COMB (@lem1281791) (@lem1281790 x)). Qed.
Lemma lem1281793 (x : nadd) : (term72 x) = (term69 x).
Proof. exact (TRANS (@lem1281792 x) (@lem1281787 x)). Qed.
Lemma lem1281794 : term73 = term74.
Proof. exact (fun_ext (fun x : nadd => @lem1281793 x)). Qed.
Lemma lem1281795 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281796 : term70 = term75.
Proof. exact (MK_COMB (@lem1281795) (@lem1281794)). Qed.
Lemma lem1281797 : term10 = term75.
Proof. exact (TRANS (@lem1281789) (@lem1281796)). Qed.
Lemma lem1281807 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1281808 (P : nadd -> Prop) (Q : nadd -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1281807 nadd P Q). Qed.
Lemma lem1281809 (x : nadd) (y : nadd) : (term80 x y) = (term81 x y).
Proof. exact (@lem1281808 (term82 x y) (term83 x y)). Qed.
Lemma lem1281810 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1281811 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1281812 (x : nadd) (y : nadd) (z : nadd) : (term86 x y z) = (term87 x y z).
Proof. exact (MK_COMB (@lem1281811) (@lem1281810 x y z)). Qed.
Lemma lem1281813 (x : nadd) (y : nadd) (z : nadd) : (term88 x y z) = (term89 x y z).
Proof. exact (eq_refl (term88 x y z)). Qed.
Lemma lem1281814 (x : nadd) (y : nadd) (z : nadd) : (term90 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1281812 x y z) (@lem1281813 x y z)). Qed.
Lemma lem1281815 (x : nadd) (y : nadd) : (term91 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1281814 x y z)). Qed.
Lemma lem1281816 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281817 (x : nadd) (y : nadd) : (term80 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1281816) (@lem1281815 x y)). Qed.
Lemma lem1281818 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1281819 (x : nadd) (y : nadd) : (term92 x y) = (term93 x y).
Proof. exact (MK_COMB (@lem1281818) (@lem1281817 x y)). Qed.
Lemma lem1281820 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1281821 (x : nadd) (y : nadd) : (term94 x y) = (term82 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1281820 x y z)). Qed.
Lemma lem1281822 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281823 (x : nadd) (y : nadd) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1281822) (@lem1281821 x y)). Qed.
Lemma lem1281824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1281825 (x : nadd) (y : nadd) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1281824) (@lem1281823 x y)). Qed.
Lemma lem1281826 (x : nadd) (y : nadd) (z : nadd) : (term88 x y z) = (term89 x y z).
Proof. exact (eq_refl (term88 x y z)). Qed.
Lemma lem1281827 (x : nadd) (y : nadd) : (term99 x y) = (term83 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1281826 x y z)). Qed.
Lemma lem1281828 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281829 (x : nadd) (y : nadd) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1281828) (@lem1281827 x y)). Qed.
Lemma lem1281830 (x : nadd) (y : nadd) : (term81 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1281825 x y) (@lem1281829 x y)). Qed.
Lemma lem1281831 (x : nadd) (y : nadd) : ((term80 x y) = (term81 x y)) = ((term62 x y) = (term102 x y)).
Proof. exact (MK_COMB (@lem1281819 x y) (@lem1281830 x y)). Qed.
Lemma lem1281832 (x : nadd) (y : nadd) : (term62 x y) = (term102 x y).
Proof. exact (EQ_MP (@lem1281831 x y) (@lem1281809 x y)). Qed.
Lemma lem1281929 (x : nadd) : (term68 x) = (term103 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281832 x y)). Qed.
Lemma lem1281930 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281931 (x : nadd) : (term69 x) = (term104 x).
Proof. exact (MK_COMB (@lem1281930) (@lem1281929 x)). Qed.
Lemma lem1281933 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1281934 (P : nadd -> Prop) (Q : nadd -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1281933 nadd P Q). Qed.
Lemma lem1281935 (x : nadd) : (term105 x) = (term106 x).
Proof. exact (@lem1281934 (term107 x) (term108 x)). Qed.
Lemma lem1281936 (x : nadd) (y : nadd) : (term109 x y) = (term96 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem1281937 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1281938 (x : nadd) (y : nadd) : (term110 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1281937) (@lem1281936 x y)). Qed.
Lemma lem1281939 (x : nadd) (y : nadd) : (term111 x y) = (term101 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1281940 (x : nadd) (y : nadd) : (term112 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1281938 x y) (@lem1281939 x y)). Qed.
Lemma lem1281941 (x : nadd) : (term113 x) = (term103 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281940 x y)). Qed.
Lemma lem1281942 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281943 (x : nadd) : (term105 x) = (term104 x).
Proof. exact (MK_COMB (@lem1281942) (@lem1281941 x)). Qed.
Lemma lem1281944 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1281945 (x : nadd) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1281944) (@lem1281943 x)). Qed.
Lemma lem1281946 (x : nadd) (y : nadd) : (term109 x y) = (term96 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem1281947 (x : nadd) : (term116 x) = (term107 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281946 x y)). Qed.
Lemma lem1281948 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281949 (x : nadd) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1281948) (@lem1281947 x)). Qed.
Lemma lem1281950 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1281951 (x : nadd) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1281950) (@lem1281949 x)). Qed.
Lemma lem1281952 (x : nadd) (y : nadd) : (term111 x y) = (term101 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1281953 (x : nadd) : (term121 x) = (term108 x).
Proof. exact (fun_ext (fun y : nadd => @lem1281952 x y)). Qed.
Lemma lem1281954 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1281955 (x : nadd) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1281954) (@lem1281953 x)). Qed.
Lemma lem1281956 (x : nadd) : (term106 x) = (term124 x).
Proof. exact (MK_COMB (@lem1281951 x) (@lem1281955 x)). Qed.
Lemma lem1281957 (x : nadd) : ((term105 x) = (term106 x)) = ((term104 x) = (term124 x)).
Proof. exact (MK_COMB (@lem1281945 x) (@lem1281956 x)). Qed.
Lemma lem1281958 (x : nadd) : (term104 x) = (term124 x).
Proof. exact (EQ_MP (@lem1281957 x) (@lem1281935 x)). Qed.
Lemma lem1282063 (x : nadd) : (term69 x) = (term124 x).
Proof. exact (TRANS (@lem1281931 x) (@lem1281958 x)). Qed.
Lemma lem1282064 : term74 = term125.
Proof. exact (fun_ext (fun x : nadd => @lem1282063 x)). Qed.
Lemma lem1282065 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282066 : term75 = term126.
Proof. exact (MK_COMB (@lem1282065) (@lem1282064)). Qed.
Lemma lem1282068 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term76 A P Q) = (term77 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1282069 (P : nadd -> Prop) (Q : nadd -> Prop) : (term78 P Q) = (term79 P Q).
Proof. exact (@lem1282068 nadd P Q). Qed.
Lemma lem1282070 : term127 = term128.
Proof. exact (@lem1282069 term129 term130). Qed.
Lemma lem1282071 (x : nadd) : (term131 x) = (term118 x).
Proof. exact (eq_refl (term131 x)). Qed.
Lemma lem1282072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282073 (x : nadd) : (term132 x) = (term120 x).
Proof. exact (MK_COMB (@lem1282072) (@lem1282071 x)). Qed.
Lemma lem1282074 (x : nadd) : (term133 x) = (term123 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1282075 (x : nadd) : (term134 x) = (term124 x).
Proof. exact (MK_COMB (@lem1282073 x) (@lem1282074 x)). Qed.
Lemma lem1282076 : term135 = term125.
Proof. exact (fun_ext (fun x : nadd => @lem1282075 x)). Qed.
Lemma lem1282077 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282078 : term127 = term126.
Proof. exact (MK_COMB (@lem1282077) (@lem1282076)). Qed.
Lemma lem1282079 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282080 : term136 = term137.
Proof. exact (MK_COMB (@lem1282079) (@lem1282078)). Qed.
Lemma lem1282081 (x : nadd) : (term131 x) = (term118 x).
Proof. exact (eq_refl (term131 x)). Qed.
Lemma lem1282082 : term138 = term129.
Proof. exact (fun_ext (fun x : nadd => @lem1282081 x)). Qed.
Lemma lem1282083 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282084 : term139 = term140.
Proof. exact (MK_COMB (@lem1282083) (@lem1282082)). Qed.
Lemma lem1282085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282086 : term141 = term142.
Proof. exact (MK_COMB (@lem1282085) (@lem1282084)). Qed.
Lemma lem1282087 (x : nadd) : (term133 x) = (term123 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1282088 : term143 = term130.
Proof. exact (fun_ext (fun x : nadd => @lem1282087 x)). Qed.
Lemma lem1282089 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282090 : term144 = term145.
Proof. exact (MK_COMB (@lem1282089) (@lem1282088)). Qed.
Lemma lem1282091 : term128 = term146.
Proof. exact (MK_COMB (@lem1282086) (@lem1282090)). Qed.
Lemma lem1282092 : (term127 = term128) = (term126 = term146).
Proof. exact (MK_COMB (@lem1282080) (@lem1282091)). Qed.
Lemma lem1282093 : term126 = term146.
Proof. exact (EQ_MP (@lem1282092) (@lem1282070)). Qed.
Lemma lem1282206 : term75 = term146.
Proof. exact (TRANS (@lem1282066) (@lem1282093)). Qed.
Lemma lem1282208 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1282209 (P : nadd -> Prop) (Q : nadd -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1282208 nadd P Q). Qed.
Lemma lem1282210 : term128 = term127.
Proof. exact (@lem1282209 term129 term130). Qed.
Lemma lem1282211 (x : nadd) : (term131 x) = (term118 x).
Proof. exact (eq_refl (term131 x)). Qed.
Lemma lem1282212 : term138 = term129.
Proof. exact (fun_ext (fun x : nadd => @lem1282211 x)). Qed.
Lemma lem1282213 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282214 : term139 = term140.
Proof. exact (MK_COMB (@lem1282213) (@lem1282212)). Qed.
Lemma lem1282215 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282216 : term141 = term142.
Proof. exact (MK_COMB (@lem1282215) (@lem1282214)). Qed.
Lemma lem1282217 (x : nadd) : (term133 x) = (term123 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1282218 : term143 = term130.
Proof. exact (fun_ext (fun x : nadd => @lem1282217 x)). Qed.
Lemma lem1282219 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282220 : term144 = term145.
Proof. exact (MK_COMB (@lem1282219) (@lem1282218)). Qed.
Lemma lem1282221 : term128 = term146.
Proof. exact (MK_COMB (@lem1282216) (@lem1282220)). Qed.
Lemma lem1282222 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282223 : term147 = term148.
Proof. exact (MK_COMB (@lem1282222) (@lem1282221)). Qed.
Lemma lem1282224 (x : nadd) : (term131 x) = (term118 x).
Proof. exact (eq_refl (term131 x)). Qed.
Lemma lem1282225 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282226 (x : nadd) : (term132 x) = (term120 x).
Proof. exact (MK_COMB (@lem1282225) (@lem1282224 x)). Qed.
Lemma lem1282227 (x : nadd) : (term133 x) = (term123 x).
Proof. exact (eq_refl (term133 x)). Qed.
Lemma lem1282228 (x : nadd) : (term134 x) = (term124 x).
Proof. exact (MK_COMB (@lem1282226 x) (@lem1282227 x)). Qed.
Lemma lem1282229 : term135 = term125.
Proof. exact (fun_ext (fun x : nadd => @lem1282228 x)). Qed.
Lemma lem1282230 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282231 : term127 = term126.
Proof. exact (MK_COMB (@lem1282230) (@lem1282229)). Qed.
Lemma lem1282232 : (term128 = term127) = (term146 = term126).
Proof. exact (MK_COMB (@lem1282223) (@lem1282231)). Qed.
Lemma lem1282233 : term146 = term126.
Proof. exact (EQ_MP (@lem1282232) (@lem1282210)). Qed.
Lemma lem1282235 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1282236 (P : nadd -> Prop) (Q : nadd -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1282235 nadd P Q). Qed.
Lemma lem1282237 (x : nadd) : (term106 x) = (term105 x).
Proof. exact (@lem1282236 (term107 x) (term108 x)). Qed.
Lemma lem1282238 (x : nadd) (y : nadd) : (term109 x y) = (term96 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem1282239 (x : nadd) : (term116 x) = (term107 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282238 x y)). Qed.
Lemma lem1282240 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282241 (x : nadd) : (term117 x) = (term118 x).
Proof. exact (MK_COMB (@lem1282240) (@lem1282239 x)). Qed.
Lemma lem1282242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282243 (x : nadd) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1282242) (@lem1282241 x)). Qed.
Lemma lem1282244 (x : nadd) (y : nadd) : (term111 x y) = (term101 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1282245 (x : nadd) : (term121 x) = (term108 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282244 x y)). Qed.
Lemma lem1282246 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282247 (x : nadd) : (term122 x) = (term123 x).
Proof. exact (MK_COMB (@lem1282246) (@lem1282245 x)). Qed.
Lemma lem1282248 (x : nadd) : (term106 x) = (term124 x).
Proof. exact (MK_COMB (@lem1282243 x) (@lem1282247 x)). Qed.
Lemma lem1282249 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282250 (x : nadd) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1282249) (@lem1282248 x)). Qed.
Lemma lem1282251 (x : nadd) (y : nadd) : (term109 x y) = (term96 x y).
Proof. exact (eq_refl (term109 x y)). Qed.
Lemma lem1282252 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282253 (x : nadd) (y : nadd) : (term110 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1282252) (@lem1282251 x y)). Qed.
Lemma lem1282254 (x : nadd) (y : nadd) : (term111 x y) = (term101 x y).
Proof. exact (eq_refl (term111 x y)). Qed.
Lemma lem1282255 (x : nadd) (y : nadd) : (term112 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1282253 x y) (@lem1282254 x y)). Qed.
Lemma lem1282256 (x : nadd) : (term113 x) = (term103 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282255 x y)). Qed.
Lemma lem1282257 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282258 (x : nadd) : (term105 x) = (term104 x).
Proof. exact (MK_COMB (@lem1282257) (@lem1282256 x)). Qed.
Lemma lem1282259 (x : nadd) : ((term106 x) = (term105 x)) = ((term124 x) = (term104 x)).
Proof. exact (MK_COMB (@lem1282250 x) (@lem1282258 x)). Qed.
Lemma lem1282260 (x : nadd) : (term124 x) = (term104 x).
Proof. exact (EQ_MP (@lem1282259 x) (@lem1282237 x)). Qed.
Lemma lem1282262 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term77 A P Q) = (term76 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1282263 (P : nadd -> Prop) (Q : nadd -> Prop) : (term79 P Q) = (term78 P Q).
Proof. exact (@lem1282262 nadd P Q). Qed.
Lemma lem1282264 (x : nadd) (y : nadd) : (term81 x y) = (term80 x y).
Proof. exact (@lem1282263 (term82 x y) (term83 x y)). Qed.
Lemma lem1282265 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1282266 (x : nadd) (y : nadd) : (term94 x y) = (term82 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282265 x y z)). Qed.
Lemma lem1282267 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282268 (x : nadd) (y : nadd) : (term95 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1282267) (@lem1282266 x y)). Qed.
Lemma lem1282269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282270 (x : nadd) (y : nadd) : (term97 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem1282269) (@lem1282268 x y)). Qed.
Lemma lem1282271 (x : nadd) (y : nadd) (z : nadd) : (term88 x y z) = (term89 x y z).
Proof. exact (eq_refl (term88 x y z)). Qed.
Lemma lem1282272 (x : nadd) (y : nadd) : (term99 x y) = (term83 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282271 x y z)). Qed.
Lemma lem1282273 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282274 (x : nadd) (y : nadd) : (term100 x y) = (term101 x y).
Proof. exact (MK_COMB (@lem1282273) (@lem1282272 x y)). Qed.
Lemma lem1282275 (x : nadd) (y : nadd) : (term81 x y) = (term102 x y).
Proof. exact (MK_COMB (@lem1282270 x y) (@lem1282274 x y)). Qed.
Lemma lem1282276 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282277 (x : nadd) (y : nadd) : (term151 x y) = (term152 x y).
Proof. exact (MK_COMB (@lem1282276) (@lem1282275 x y)). Qed.
Lemma lem1282278 (x : nadd) (y : nadd) (z : nadd) : (term84 x y z) = (term85 x y z).
Proof. exact (eq_refl (term84 x y z)). Qed.
Lemma lem1282279 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282280 (x : nadd) (y : nadd) (z : nadd) : (term86 x y z) = (term87 x y z).
Proof. exact (MK_COMB (@lem1282279) (@lem1282278 x y z)). Qed.
Lemma lem1282281 (x : nadd) (y : nadd) (z : nadd) : (term88 x y z) = (term89 x y z).
Proof. exact (eq_refl (term88 x y z)). Qed.
Lemma lem1282282 (x : nadd) (y : nadd) (z : nadd) : (term90 x y z) = (term53 x y z).
Proof. exact (MK_COMB (@lem1282280 x y z) (@lem1282281 x y z)). Qed.
Lemma lem1282283 (x : nadd) (y : nadd) : (term91 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282282 x y z)). Qed.
Lemma lem1282284 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282285 (x : nadd) (y : nadd) : (term80 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem1282284) (@lem1282283 x y)). Qed.
Lemma lem1282286 (x : nadd) (y : nadd) : ((term81 x y) = (term80 x y)) = ((term102 x y) = (term62 x y)).
Proof. exact (MK_COMB (@lem1282277 x y) (@lem1282285 x y)). Qed.
Lemma lem1282287 (x : nadd) (y : nadd) : (term102 x y) = (term62 x y).
Proof. exact (EQ_MP (@lem1282286 x y) (@lem1282264 x y)). Qed.
Lemma lem1282288 (x : nadd) : (term103 x) = (term68 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282287 x y)). Qed.
Lemma lem1282289 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282290 (x : nadd) : (term104 x) = (term69 x).
Proof. exact (MK_COMB (@lem1282289) (@lem1282288 x)). Qed.
Lemma lem1282291 (x : nadd) : (term124 x) = (term69 x).
Proof. exact (TRANS (@lem1282260 x) (@lem1282290 x)). Qed.
Lemma lem1282292 : term125 = term74.
Proof. exact (fun_ext (fun x : nadd => @lem1282291 x)). Qed.
Lemma lem1282293 : (@ex nadd) = (@ex nadd).
Proof. exact (eq_refl (@ex nadd)). Qed.
Lemma lem1282294 : term126 = term75.
Proof. exact (MK_COMB (@lem1282293) (@lem1282292)). Qed.
Lemma lem1282295 : term146 = term75.
Proof. exact (TRANS (@lem1282233) (@lem1282294)). Qed.
Lemma lem1282296 : term75 = term75.
Proof. exact (TRANS (@lem1282206) (@lem1282295)). Qed.
Lemma lem1282297 : term10 = term75.
Proof. exact (TRANS (@lem1281797) (@lem1282296)). Qed.
Lemma lem1282298 (h1 : term10) : term75.
Proof. exact (EQ_MP (@lem1282297) (@lem1281749 h1)). Qed.
Lemma lem1282305 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term153 x x' y y') = (term154 x x' y y').
Proof. exact (@lem17045 (nadd_eq x x') (nadd_eq y y')). Qed.
Lemma lem1282320 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : ((nadd_le x y) = (nadd_le x' y')) = (term155 x y x' y').
Proof. exact (@lem17784 (nadd_le x y) (nadd_le x' y')). Qed.
Lemma lem1282321 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282322 (x : nadd) (x' : nadd) (y : nadd) (y' : nadd) : (term156 x x' y y') = (term157 x x' y y').
Proof. exact (MK_COMB (@lem1282321) (@lem1282305 x x' y y')). Qed.
Lemma lem1282323 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term158 x y x' y') = (term159 x y x' y').
Proof. exact (MK_COMB (@lem1282322 x x' y y') (@lem1282320 x y x' y')). Qed.
Lemma lem1282324 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term37 x y x' y') = (term158 x y x' y').
Proof. exact (@lem17265 (term160 x x' y y') ((nadd_le x y) = (nadd_le x' y'))). Qed.
Lemma lem1282325 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term37 x y x' y') = (term159 x y x' y').
Proof. exact (TRANS (@lem1282324 x y x' y') (@lem1282323 x y x' y')). Qed.
Lemma lem1282326 (x : nadd) (y : nadd) (x' : nadd) : (term38 x y x') = (term161 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1282325 x y x' y')). Qed.
Lemma lem1282327 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282328 (x : nadd) (y : nadd) (x' : nadd) : (term39 x y x') = (term162 x y x').
Proof. exact (MK_COMB (@lem1282327) (@lem1282326 x y x')). Qed.
Lemma lem1282329 (x : nadd) (x' : nadd) : (term40 x x') = (term163 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1282328 x y x')). Qed.
Lemma lem1282330 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282331 (x : nadd) (x' : nadd) : (term41 x x') = (term164 x x').
Proof. exact (MK_COMB (@lem1282330) (@lem1282329 x x')). Qed.
Lemma lem1282332 (x : nadd) : (term42 x) = (term165 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1282331 x x')). Qed.
Lemma lem1282333 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282334 (x : nadd) : (term43 x) = (term166 x).
Proof. exact (MK_COMB (@lem1282333) (@lem1282332 x)). Qed.
Lemma lem1282335 : term44 = term167.
Proof. exact (fun_ext (fun x : nadd => @lem1282334 x)). Qed.
Lemma lem1282336 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282401 : term45 = term168.
Proof. exact (MK_COMB (@lem1282336) (@lem1282335)). Qed.
Lemma lem1282402 (h1 : term45) : term168.
Proof. exact (EQ_MP (@lem1282401) (@lem1281750 h1)). Qed.
Lemma lem1282403 (y : nadd) (x : nadd) : (term32 y x) = (term32 y x).
Proof. exact (eq_refl (term32 y x)). Qed.
Lemma lem1282404 (x : nadd) : (term33 x) = (term33 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282403 y x)). Qed.
Lemma lem1282405 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282406 (x : nadd) : (term34 x) = (term34 x).
Proof. exact (MK_COMB (@lem1282405) (@lem1282404 x)). Qed.
Lemma lem1282407 : term35 = term35.
Proof. exact (fun_ext (fun x : nadd => @lem1282406 x)). Qed.
Lemma lem1282408 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282421 : term36 = term36.
Proof. exact (MK_COMB (@lem1282408) (@lem1282407)). Qed.
Lemma lem1282422 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1282421) (@lem1281751 h1)). Qed.
Lemma lem1282437 (z : nadd) (x : nadd) (y : nadd) : ((term26 x y z) = (nadd_le x y)) = (term169 z x y).
Proof. exact (@lem17784 (term26 x y z) (nadd_le x y)). Qed.
Lemma lem1282438 (x : nadd) (y : nadd) : (term27 x y) = (term170 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282437 z x y)). Qed.
Lemma lem1282439 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282440 (x : nadd) (y : nadd) : (term28 x y) = (term171 x y).
Proof. exact (MK_COMB (@lem1282439) (@lem1282438 x y)). Qed.
Lemma lem1282441 (x : nadd) : (term29 x) = (term172 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282440 x y)). Qed.
Lemma lem1282442 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282443 (x : nadd) : (term30 x) = (term173 x).
Proof. exact (MK_COMB (@lem1282442) (@lem1282441 x)). Qed.
Lemma lem1282444 : term31 = term174.
Proof. exact (fun_ext (fun x : nadd => @lem1282443 x)). Qed.
Lemma lem1282445 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282446 : term17 = term175.
Proof. exact (MK_COMB (@lem1282445) (@lem1282444)). Qed.
Lemma lem1282456 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1282457 (P : nadd -> Prop) (Q : nadd -> Prop) : (term178 P Q) = (term179 P Q).
Proof. exact (@lem1282456 nadd P Q). Qed.
Lemma lem1282458 (x : nadd) (y : nadd) : (term180 x y) = (term181 x y).
Proof. exact (@lem1282457 (term182 x y) (term183 x y)). Qed.
Lemma lem1282459 (z : nadd) (x : nadd) (y : nadd) : (term184 x y z) = (term185 z x y).
Proof. exact (eq_refl (term184 x y z)). Qed.
Lemma lem1282460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1282461 (z : nadd) (x : nadd) (y : nadd) : (term186 x y z) = (term187 z x y).
Proof. exact (MK_COMB (@lem1282460) (@lem1282459 z x y)). Qed.
Lemma lem1282462 (z : nadd) (x : nadd) (y : nadd) : (term188 x y z) = (term189 z x y).
Proof. exact (eq_refl (term188 x y z)). Qed.
Lemma lem1282463 (z : nadd) (x : nadd) (y : nadd) : (term190 x y z) = (term169 z x y).
Proof. exact (MK_COMB (@lem1282461 z x y) (@lem1282462 z x y)). Qed.
Lemma lem1282464 (x : nadd) (y : nadd) : (term191 x y) = (term170 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282463 z x y)). Qed.
Lemma lem1282465 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282466 (x : nadd) (y : nadd) : (term180 x y) = (term171 x y).
Proof. exact (MK_COMB (@lem1282465) (@lem1282464 x y)). Qed.
Lemma lem1282467 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282468 (x : nadd) (y : nadd) : (term192 x y) = (term193 x y).
Proof. exact (MK_COMB (@lem1282467) (@lem1282466 x y)). Qed.
Lemma lem1282469 (z : nadd) (x : nadd) (y : nadd) : (term184 x y z) = (term185 z x y).
Proof. exact (eq_refl (term184 x y z)). Qed.
Lemma lem1282470 (x : nadd) (y : nadd) : (term194 x y) = (term182 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282469 z x y)). Qed.
Lemma lem1282471 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282472 (x : nadd) (y : nadd) : (term195 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1282471) (@lem1282470 x y)). Qed.
Lemma lem1282473 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1282474 (x : nadd) (y : nadd) : (term197 x y) = (term198 x y).
Proof. exact (MK_COMB (@lem1282473) (@lem1282472 x y)). Qed.
Lemma lem1282475 (z : nadd) (x : nadd) (y : nadd) : (term188 x y z) = (term189 z x y).
Proof. exact (eq_refl (term188 x y z)). Qed.
Lemma lem1282476 (x : nadd) (y : nadd) : (term199 x y) = (term183 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282475 z x y)). Qed.
Lemma lem1282477 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282478 (x : nadd) (y : nadd) : (term200 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1282477) (@lem1282476 x y)). Qed.
Lemma lem1282479 (x : nadd) (y : nadd) : (term181 x y) = (term202 x y).
Proof. exact (MK_COMB (@lem1282474 x y) (@lem1282478 x y)). Qed.
Lemma lem1282480 (x : nadd) (y : nadd) : ((term180 x y) = (term181 x y)) = ((term171 x y) = (term202 x y)).
Proof. exact (MK_COMB (@lem1282468 x y) (@lem1282479 x y)). Qed.
Lemma lem1282481 (x : nadd) (y : nadd) : (term171 x y) = (term202 x y).
Proof. exact (EQ_MP (@lem1282480 x y) (@lem1282458 x y)). Qed.
Lemma lem1282503 {A : Type'} (P : A -> Prop) (Q : Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1282504 (P : nadd -> Prop) (Q : Prop) : (term205 P Q) = (term206 P Q).
Proof. exact (@lem1282503 nadd P Q). Qed.
Lemma lem1282505 (x : nadd) (y : nadd) : (term207 x y) = (term208 x y).
Proof. exact (@lem1282504 (term209 x y) (term210 x y)). Qed.
Lemma lem1282506 (x : nadd) (y : nadd) (z : nadd) : (term211 x y z) = (term26 x y z).
Proof. exact (eq_refl (term211 x y z)). Qed.
Lemma lem1282507 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282508 (x : nadd) (y : nadd) (z : nadd) : (term212 x y z) = (term213 x y z).
Proof. exact (MK_COMB (@lem1282507) (@lem1282506 x y z)). Qed.
Lemma lem1282509 (x : nadd) (y : nadd) : (term210 x y) = (term210 x y).
Proof. exact (eq_refl (term210 x y)). Qed.
Lemma lem1282510 (z : nadd) (x : nadd) (y : nadd) : (term214 z x y) = (term185 z x y).
Proof. exact (MK_COMB (@lem1282508 x y z) (@lem1282509 x y)). Qed.
Lemma lem1282511 (x : nadd) (y : nadd) : (term215 x y) = (term182 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282510 z x y)). Qed.
Lemma lem1282512 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282513 (x : nadd) (y : nadd) : (term207 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1282512) (@lem1282511 x y)). Qed.
Lemma lem1282514 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282515 (x : nadd) (y : nadd) : (term216 x y) = (term217 x y).
Proof. exact (MK_COMB (@lem1282514) (@lem1282513 x y)). Qed.
Lemma lem1282516 (x : nadd) (y : nadd) (z : nadd) : (term211 x y z) = (term26 x y z).
Proof. exact (eq_refl (term211 x y z)). Qed.
Lemma lem1282517 (x : nadd) (y : nadd) : (term218 x y) = (term209 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282516 x y z)). Qed.
Lemma lem1282518 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282519 (x : nadd) (y : nadd) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1282518) (@lem1282517 x y)). Qed.
Lemma lem1282520 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282521 (x : nadd) (y : nadd) : (term221 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1282520) (@lem1282519 x y)). Qed.
Lemma lem1282522 (x : nadd) (y : nadd) : (term210 x y) = (term210 x y).
Proof. exact (eq_refl (term210 x y)). Qed.
Lemma lem1282523 (x : nadd) (y : nadd) : (term208 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1282521 x y) (@lem1282522 x y)). Qed.
Lemma lem1282524 (x : nadd) (y : nadd) : ((term207 x y) = (term208 x y)) = ((term196 x y) = (term223 x y)).
Proof. exact (MK_COMB (@lem1282515 x y) (@lem1282523 x y)). Qed.
Lemma lem1282525 (x : nadd) (y : nadd) : (term196 x y) = (term223 x y).
Proof. exact (EQ_MP (@lem1282524 x y) (@lem1282505 x y)). Qed.
Lemma lem1282530 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1282531 (x : nadd) (y : nadd) : (term198 x y) = (term224 x y).
Proof. exact (MK_COMB (@lem1282530) (@lem1282525 x y)). Qed.
Lemma lem1282553 {A : Type'} (P : A -> Prop) (Q : Prop) : (term203 A P Q) = (term204 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1282554 (P : nadd -> Prop) (Q : Prop) : (term205 P Q) = (term206 P Q).
Proof. exact (@lem1282553 nadd P Q). Qed.
Lemma lem1282555 (x : nadd) (y : nadd) : (term225 x y) = (term226 x y).
Proof. exact (@lem1282554 (term227 x y) (nadd_le x y)). Qed.
Lemma lem1282556 (x : nadd) (y : nadd) (z : nadd) : (term228 x y z) = (term229 x y z).
Proof. exact (eq_refl (term228 x y z)). Qed.
Lemma lem1282557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282558 (x : nadd) (y : nadd) (z : nadd) : (term230 x y z) = (term231 x y z).
Proof. exact (MK_COMB (@lem1282557) (@lem1282556 x y z)). Qed.
Lemma lem1282559 (x : nadd) (y : nadd) : (nadd_le x y) = (nadd_le x y).
Proof. exact (eq_refl (nadd_le x y)). Qed.
Lemma lem1282560 (z : nadd) (x : nadd) (y : nadd) : (term232 z x y) = (term189 z x y).
Proof. exact (MK_COMB (@lem1282558 x y z) (@lem1282559 x y)). Qed.
Lemma lem1282561 (x : nadd) (y : nadd) : (term233 x y) = (term183 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282560 z x y)). Qed.
Lemma lem1282562 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282563 (x : nadd) (y : nadd) : (term225 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1282562) (@lem1282561 x y)). Qed.
Lemma lem1282564 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282565 (x : nadd) (y : nadd) : (term234 x y) = (term235 x y).
Proof. exact (MK_COMB (@lem1282564) (@lem1282563 x y)). Qed.
Lemma lem1282566 (x : nadd) (y : nadd) (z : nadd) : (term228 x y z) = (term229 x y z).
Proof. exact (eq_refl (term228 x y z)). Qed.
Lemma lem1282567 (x : nadd) (y : nadd) : (term236 x y) = (term227 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282566 x y z)). Qed.
Lemma lem1282568 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282569 (x : nadd) (y : nadd) : (term237 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1282568) (@lem1282567 x y)). Qed.
Lemma lem1282570 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282571 (x : nadd) (y : nadd) : (term239 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1282570) (@lem1282569 x y)). Qed.
Lemma lem1282572 (x : nadd) (y : nadd) : (nadd_le x y) = (nadd_le x y).
Proof. exact (eq_refl (nadd_le x y)). Qed.
Lemma lem1282573 (x : nadd) (y : nadd) : (term226 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1282571 x y) (@lem1282572 x y)). Qed.
Lemma lem1282574 (x : nadd) (y : nadd) : ((term225 x y) = (term226 x y)) = ((term201 x y) = (term241 x y)).
Proof. exact (MK_COMB (@lem1282565 x y) (@lem1282573 x y)). Qed.
Lemma lem1282575 (x : nadd) (y : nadd) : (term201 x y) = (term241 x y).
Proof. exact (EQ_MP (@lem1282574 x y) (@lem1282555 x y)). Qed.
Lemma lem1282580 (x : nadd) (y : nadd) : (term202 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1282531 x y) (@lem1282575 x y)). Qed.
Lemma lem1282581 (x : nadd) (y : nadd) : (term171 x y) = (term242 x y).
Proof. exact (TRANS (@lem1282481 x y) (@lem1282580 x y)). Qed.
Lemma lem1282582 (x : nadd) : (term172 x) = (term243 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282581 x y)). Qed.
Lemma lem1282583 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282584 (x : nadd) : (term173 x) = (term244 x).
Proof. exact (MK_COMB (@lem1282583) (@lem1282582 x)). Qed.
Lemma lem1282586 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1282587 (P : nadd -> Prop) (Q : nadd -> Prop) : (term178 P Q) = (term179 P Q).
Proof. exact (@lem1282586 nadd P Q). Qed.
Lemma lem1282588 (x : nadd) : (term245 x) = (term246 x).
Proof. exact (@lem1282587 (term247 x) (term248 x)). Qed.
Lemma lem1282589 (x : nadd) (y : nadd) : (term249 x y) = (term223 x y).
Proof. exact (eq_refl (term249 x y)). Qed.
Lemma lem1282590 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1282591 (x : nadd) (y : nadd) : (term250 x y) = (term224 x y).
Proof. exact (MK_COMB (@lem1282590) (@lem1282589 x y)). Qed.
Lemma lem1282592 (x : nadd) (y : nadd) : (term251 x y) = (term241 x y).
Proof. exact (eq_refl (term251 x y)). Qed.
Lemma lem1282593 (x : nadd) (y : nadd) : (term252 x y) = (term242 x y).
Proof. exact (MK_COMB (@lem1282591 x y) (@lem1282592 x y)). Qed.
Lemma lem1282594 (x : nadd) : (term253 x) = (term243 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282593 x y)). Qed.
Lemma lem1282595 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282596 (x : nadd) : (term245 x) = (term244 x).
Proof. exact (MK_COMB (@lem1282595) (@lem1282594 x)). Qed.
Lemma lem1282597 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282598 (x : nadd) : (term254 x) = (term255 x).
Proof. exact (MK_COMB (@lem1282597) (@lem1282596 x)). Qed.
Lemma lem1282599 (x : nadd) (y : nadd) : (term249 x y) = (term223 x y).
Proof. exact (eq_refl (term249 x y)). Qed.
Lemma lem1282600 (x : nadd) : (term256 x) = (term247 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282599 x y)). Qed.
Lemma lem1282601 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282602 (x : nadd) : (term257 x) = (term258 x).
Proof. exact (MK_COMB (@lem1282601) (@lem1282600 x)). Qed.
Lemma lem1282603 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1282604 (x : nadd) : (term259 x) = (term260 x).
Proof. exact (MK_COMB (@lem1282603) (@lem1282602 x)). Qed.
Lemma lem1282605 (x : nadd) (y : nadd) : (term251 x y) = (term241 x y).
Proof. exact (eq_refl (term251 x y)). Qed.
Lemma lem1282606 (x : nadd) : (term261 x) = (term248 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282605 x y)). Qed.
Lemma lem1282607 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282608 (x : nadd) : (term262 x) = (term263 x).
Proof. exact (MK_COMB (@lem1282607) (@lem1282606 x)). Qed.
Lemma lem1282609 (x : nadd) : (term246 x) = (term264 x).
Proof. exact (MK_COMB (@lem1282604 x) (@lem1282608 x)). Qed.
Lemma lem1282610 (x : nadd) : ((term245 x) = (term246 x)) = ((term244 x) = (term264 x)).
Proof. exact (MK_COMB (@lem1282598 x) (@lem1282609 x)). Qed.
Lemma lem1282611 (x : nadd) : (term244 x) = (term264 x).
Proof. exact (EQ_MP (@lem1282610 x) (@lem1282588 x)). Qed.
Lemma lem1282716 (x : nadd) : (term173 x) = (term264 x).
Proof. exact (TRANS (@lem1282584 x) (@lem1282611 x)). Qed.
Lemma lem1282717 : term174 = term265.
Proof. exact (fun_ext (fun x : nadd => @lem1282716 x)). Qed.
Lemma lem1282718 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282719 : term175 = term266.
Proof. exact (MK_COMB (@lem1282718) (@lem1282717)). Qed.
Lemma lem1282721 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term176 A P Q) = (term177 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1282722 (P : nadd -> Prop) (Q : nadd -> Prop) : (term178 P Q) = (term179 P Q).
Proof. exact (@lem1282721 nadd P Q). Qed.
Lemma lem1282723 : term267 = term268.
Proof. exact (@lem1282722 term269 term270). Qed.
Lemma lem1282724 (x : nadd) : (term271 x) = (term258 x).
Proof. exact (eq_refl (term271 x)). Qed.
Lemma lem1282725 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1282726 (x : nadd) : (term272 x) = (term260 x).
Proof. exact (MK_COMB (@lem1282725) (@lem1282724 x)). Qed.
Lemma lem1282727 (x : nadd) : (term273 x) = (term263 x).
Proof. exact (eq_refl (term273 x)). Qed.
Lemma lem1282728 (x : nadd) : (term274 x) = (term264 x).
Proof. exact (MK_COMB (@lem1282726 x) (@lem1282727 x)). Qed.
Lemma lem1282729 : term275 = term265.
Proof. exact (fun_ext (fun x : nadd => @lem1282728 x)). Qed.
Lemma lem1282730 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282731 : term267 = term266.
Proof. exact (MK_COMB (@lem1282730) (@lem1282729)). Qed.
Lemma lem1282732 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1282733 : term276 = term277.
Proof. exact (MK_COMB (@lem1282732) (@lem1282731)). Qed.
Lemma lem1282734 (x : nadd) : (term271 x) = (term258 x).
Proof. exact (eq_refl (term271 x)). Qed.
Lemma lem1282735 : term278 = term269.
Proof. exact (fun_ext (fun x : nadd => @lem1282734 x)). Qed.
Lemma lem1282736 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282737 : term279 = term280.
Proof. exact (MK_COMB (@lem1282736) (@lem1282735)). Qed.
Lemma lem1282738 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1282739 : term281 = term282.
Proof. exact (MK_COMB (@lem1282738) (@lem1282737)). Qed.
Lemma lem1282740 (x : nadd) : (term273 x) = (term263 x).
Proof. exact (eq_refl (term273 x)). Qed.
Lemma lem1282741 : term283 = term270.
Proof. exact (fun_ext (fun x : nadd => @lem1282740 x)). Qed.
Lemma lem1282742 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282743 : term284 = term285.
Proof. exact (MK_COMB (@lem1282742) (@lem1282741)). Qed.
Lemma lem1282744 : term268 = term286.
Proof. exact (MK_COMB (@lem1282739) (@lem1282743)). Qed.
Lemma lem1282745 : (term267 = term268) = (term266 = term286).
Proof. exact (MK_COMB (@lem1282733) (@lem1282744)). Qed.
Lemma lem1282746 : term266 = term286.
Proof. exact (EQ_MP (@lem1282745) (@lem1282723)). Qed.
Lemma lem1282861 : term175 = term286.
Proof. exact (TRANS (@lem1282719) (@lem1282746)). Qed.
Lemma lem1282862 : term17 = term286.
Proof. exact (TRANS (@lem1282446) (@lem1282861)). Qed.
Lemma lem1282863 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem1282862) (@lem1281752 h1)). Qed.
Lemma lem1282864 (x : nadd) (h1 : term69 x) : term69 x.
Proof. exact (h1). Qed.
Lemma lem1282865 (x : nadd) (y : nadd) (h1 : term62 x y) : term62 x y.
Proof. exact (h1). Qed.
Lemma lem1282919 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term159 x y x' y') = (term159 x y x' y').
Proof. exact (eq_refl (term159 x y x' y')). Qed.
Lemma lem1282920 (x : nadd) (y : nadd) (x' : nadd) : (term161 x y x') = (term161 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1282919 x y x' y')). Qed.
Lemma lem1282921 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282922 (x : nadd) (y : nadd) (x' : nadd) : (term162 x y x') = (term162 x y x').
Proof. exact (MK_COMB (@lem1282921) (@lem1282920 x y x')). Qed.
Lemma lem1282923 (x : nadd) (x' : nadd) : (term163 x x') = (term163 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1282922 x y x')). Qed.
Lemma lem1282924 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282925 (x : nadd) (x' : nadd) : (term164 x x') = (term164 x x').
Proof. exact (MK_COMB (@lem1282924) (@lem1282923 x x')). Qed.
Lemma lem1282926 (x : nadd) : (term165 x) = (term165 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1282925 x x')). Qed.
Lemma lem1282927 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282928 (x : nadd) : (term166 x) = (term166 x).
Proof. exact (MK_COMB (@lem1282927) (@lem1282926 x)). Qed.
Lemma lem1282929 : term167 = term167.
Proof. exact (fun_ext (fun x : nadd => @lem1282928 x)). Qed.
Lemma lem1282930 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282931 : term168 = term168.
Proof. exact (MK_COMB (@lem1282930) (@lem1282929)). Qed.
Lemma lem1282932 (h1 : term45) : term168.
Proof. exact (EQ_MP (@lem1282931) (@lem1282402 h1)). Qed.
Lemma lem1282945 (y : nadd) (x : nadd) : (term32 y x) = (term32 y x).
Proof. exact (eq_refl (term32 y x)). Qed.
Lemma lem1282946 (x : nadd) : (term33 x) = (term33 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282945 y x)). Qed.
Lemma lem1282947 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282948 (x : nadd) : (term34 x) = (term34 x).
Proof. exact (MK_COMB (@lem1282947) (@lem1282946 x)). Qed.
Lemma lem1282949 : term35 = term35.
Proof. exact (fun_ext (fun x : nadd => @lem1282948 x)). Qed.
Lemma lem1282950 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282951 : term36 = term36.
Proof. exact (MK_COMB (@lem1282950) (@lem1282949)). Qed.
Lemma lem1282952 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1282951) (@lem1282422 h1)). Qed.
Lemma lem1282957 (x : nadd) (y : nadd) : (nadd_le x y) = (nadd_le x y).
Proof. exact (eq_refl (nadd_le x y)). Qed.
Lemma lem1282972 (x : nadd) (y : nadd) (z : nadd) : (term229 x y z) = (term229 x y z).
Proof. exact (eq_refl (term229 x y z)). Qed.
Lemma lem1282973 (x : nadd) (y : nadd) : (term227 x y) = (term227 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1282972 x y z)). Qed.
Lemma lem1282974 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282975 (x : nadd) (y : nadd) : (term238 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1282974) (@lem1282973 x y)). Qed.
Lemma lem1282976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1282977 (x : nadd) (y : nadd) : (term240 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1282976) (@lem1282975 x y)). Qed.
Lemma lem1282978 (x : nadd) (y : nadd) : (term241 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1282977 x y) (@lem1282957 x y)). Qed.
Lemma lem1282979 (x : nadd) : (term248 x) = (term248 x).
Proof. exact (fun_ext (fun y : nadd => @lem1282978 x y)). Qed.
Lemma lem1282980 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282981 (x : nadd) : (term263 x) = (term263 x).
Proof. exact (MK_COMB (@lem1282980) (@lem1282979 x)). Qed.
Lemma lem1282982 : term270 = term270.
Proof. exact (fun_ext (fun x : nadd => @lem1282981 x)). Qed.
Lemma lem1282983 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1282984 : term285 = term285.
Proof. exact (MK_COMB (@lem1282983) (@lem1282982)). Qed.
Lemma lem1282991 (x : nadd) (y : nadd) : (term210 x y) = (term210 x y).
Proof. exact (eq_refl (term210 x y)). Qed.
Lemma lem1283004 (x : nadd) (y : nadd) (z : nadd) : (term26 x y z) = (term26 x y z).
Proof. exact (eq_refl (term26 x y z)). Qed.
Lemma lem1283005 (x : nadd) (y : nadd) : (term209 x y) = (term209 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1283004 x y z)). Qed.
Lemma lem1283006 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283007 (x : nadd) (y : nadd) : (term220 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1283006) (@lem1283005 x y)). Qed.
Lemma lem1283008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1283009 (x : nadd) (y : nadd) : (term222 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1283008) (@lem1283007 x y)). Qed.
Lemma lem1283010 (x : nadd) (y : nadd) : (term223 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1283009 x y) (@lem1282991 x y)). Qed.
Lemma lem1283011 (x : nadd) : (term247 x) = (term247 x).
Proof. exact (fun_ext (fun y : nadd => @lem1283010 x y)). Qed.
Lemma lem1283012 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283013 (x : nadd) : (term258 x) = (term258 x).
Proof. exact (MK_COMB (@lem1283012) (@lem1283011 x)). Qed.
Lemma lem1283014 : term269 = term269.
Proof. exact (fun_ext (fun x : nadd => @lem1283013 x)). Qed.
Lemma lem1283015 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283016 : term280 = term280.
Proof. exact (MK_COMB (@lem1283015) (@lem1283014)). Qed.
Lemma lem1283017 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1283018 : term282 = term282.
Proof. exact (MK_COMB (@lem1283017) (@lem1283016)). Qed.
Lemma lem1283019 : term286 = term286.
Proof. exact (MK_COMB (@lem1283018) (@lem1282984)). Qed.
Lemma lem1283020 (h1 : term17) : term286.
Proof. exact (EQ_MP (@lem1283019) (@lem1282863 h1)). Qed.
Lemma lem1283070 (x : nadd) (y : nadd) (z : nadd) (h1 : term53 x y z) : term53 x y z.
Proof. exact (h1). Qed.
Lemma lem1283071 (h1 : term17) : term285.
Proof. exact (proj2 (@lem1283020 h1)). Qed.
Lemma lem1283072 (h1 : term17) : term280.
Proof. exact (proj1 (@lem1283020 h1)). Qed.
Lemma lem1283073 (x : nadd) (y : nadd) (z : nadd) (h1 : term85 x y z) : term85 x y z.
Proof. exact (h1). Qed.
Lemma lem1283074 (x : nadd) (y : nadd) (z : nadd) (h1 : term89 x y z) : term89 x y z.
Proof. exact (h1). Qed.
Lemma lem1283114 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term159 x y x' y') = (term287 x y x' y').
Proof. exact (@lem19490 (term288 x y x' y') (term154 x x' y y') (term289 x y x' y')). Qed.
Lemma lem1283115 (x : nadd) (y : nadd) (x' : nadd) : (term161 x y x') = (term290 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1283114 x y x' y')). Qed.
Lemma lem1283116 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283117 (x : nadd) (y : nadd) (x' : nadd) : (term162 x y x') = (term291 x y x').
Proof. exact (MK_COMB (@lem1283116) (@lem1283115 x y x')). Qed.
Lemma lem1283118 (x : nadd) (x' : nadd) : (term163 x x') = (term292 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1283117 x y x')). Qed.
Lemma lem1283119 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283120 (x : nadd) (x' : nadd) : (term164 x x') = (term293 x x').
Proof. exact (MK_COMB (@lem1283119) (@lem1283118 x x')). Qed.
Lemma lem1283121 (x : nadd) : (term165 x) = (term294 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1283120 x x')). Qed.
Lemma lem1283122 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283123 (x : nadd) : (term166 x) = (term295 x).
Proof. exact (MK_COMB (@lem1283122) (@lem1283121 x)). Qed.
Lemma lem1283124 : term167 = term296.
Proof. exact (fun_ext (fun x : nadd => @lem1283123 x)). Qed.
Lemma lem1283125 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283127 : term168 = term297.
Proof. exact (MK_COMB (@lem1283125) (@lem1283124)). Qed.
Lemma lem1283128 (h1 : term45) : term297.
Proof. exact (EQ_MP (@lem1283127) (@lem1282932 h1)). Qed.
Lemma lem1283130 (y : nadd) (x : nadd) : (term32 y x) = (term32 y x).
Proof. exact (eq_refl (term32 y x)). Qed.
Lemma lem1283131 (x : nadd) : (term33 x) = (term33 x).
Proof. exact (fun_ext (fun y : nadd => @lem1283130 y x)). Qed.
Lemma lem1283132 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283133 (x : nadd) : (term34 x) = (term34 x).
Proof. exact (MK_COMB (@lem1283132) (@lem1283131 x)). Qed.
Lemma lem1283134 : term35 = term35.
Proof. exact (fun_ext (fun x : nadd => @lem1283133 x)). Qed.
Lemma lem1283135 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283137 : term36 = term36.
Proof. exact (MK_COMB (@lem1283135) (@lem1283134)). Qed.
Lemma lem1283138 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1283137) (@lem1282952 h1)). Qed.
Lemma lem1283188 {A : Type'} (P : A -> Prop) (Q : Prop) : (term204 A P Q) = (term203 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1283189 (P : nadd -> Prop) (Q : Prop) : (term206 P Q) = (term205 P Q).
Proof. exact (@lem1283188 nadd P Q). Qed.
Lemma lem1283190 (x : nadd) (y : nadd) : (term226 x y) = (term225 x y).
Proof. exact (@lem1283189 (term227 x y) (nadd_le x y)). Qed.
Lemma lem1283191 (x : nadd) (y : nadd) (z : nadd) : (term228 x y z) = (term229 x y z).
Proof. exact (eq_refl (term228 x y z)). Qed.
Lemma lem1283192 (x : nadd) (y : nadd) : (term236 x y) = (term227 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1283191 x y z)). Qed.
Lemma lem1283193 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283194 (x : nadd) (y : nadd) : (term237 x y) = (term238 x y).
Proof. exact (MK_COMB (@lem1283193) (@lem1283192 x y)). Qed.
Lemma lem1283195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1283196 (x : nadd) (y : nadd) : (term239 x y) = (term240 x y).
Proof. exact (MK_COMB (@lem1283195) (@lem1283194 x y)). Qed.
Lemma lem1283197 (x : nadd) (y : nadd) : (nadd_le x y) = (nadd_le x y).
Proof. exact (eq_refl (nadd_le x y)). Qed.
Lemma lem1283198 (x : nadd) (y : nadd) : (term226 x y) = (term241 x y).
Proof. exact (MK_COMB (@lem1283196 x y) (@lem1283197 x y)). Qed.
Lemma lem1283199 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1283200 (x : nadd) (y : nadd) : (term298 x y) = (term299 x y).
Proof. exact (MK_COMB (@lem1283199) (@lem1283198 x y)). Qed.
Lemma lem1283201 (x : nadd) (y : nadd) (z : nadd) : (term228 x y z) = (term229 x y z).
Proof. exact (eq_refl (term228 x y z)). Qed.
Lemma lem1283202 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1283203 (x : nadd) (y : nadd) (z : nadd) : (term230 x y z) = (term231 x y z).
Proof. exact (MK_COMB (@lem1283202) (@lem1283201 x y z)). Qed.
Lemma lem1283204 (x : nadd) (y : nadd) : (nadd_le x y) = (nadd_le x y).
Proof. exact (eq_refl (nadd_le x y)). Qed.
Lemma lem1283205 (z : nadd) (x : nadd) (y : nadd) : (term232 z x y) = (term189 z x y).
Proof. exact (MK_COMB (@lem1283203 x y z) (@lem1283204 x y)). Qed.
Lemma lem1283206 (x : nadd) (y : nadd) : (term233 x y) = (term183 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1283205 z x y)). Qed.
Lemma lem1283207 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283208 (x : nadd) (y : nadd) : (term225 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1283207) (@lem1283206 x y)). Qed.
Lemma lem1283209 (x : nadd) (y : nadd) : ((term226 x y) = (term225 x y)) = ((term241 x y) = (term201 x y)).
Proof. exact (MK_COMB (@lem1283200 x y) (@lem1283208 x y)). Qed.
Lemma lem1283210 (x : nadd) (y : nadd) : (term241 x y) = (term201 x y).
Proof. exact (EQ_MP (@lem1283209 x y) (@lem1283190 x y)). Qed.
Lemma lem1283211 (x : nadd) : (term248 x) = (term300 x).
Proof. exact (fun_ext (fun y : nadd => @lem1283210 x y)). Qed.
Lemma lem1283212 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283213 (x : nadd) : (term263 x) = (term301 x).
Proof. exact (MK_COMB (@lem1283212) (@lem1283211 x)). Qed.
Lemma lem1283214 : term270 = term302.
Proof. exact (fun_ext (fun x : nadd => @lem1283213 x)). Qed.
Lemma lem1283215 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283216 : term285 = term303.
Proof. exact (MK_COMB (@lem1283215) (@lem1283214)). Qed.
Lemma lem1283223 (z : nadd) (x : nadd) (y : nadd) : (term189 z x y) = (term189 z x y).
Proof. exact (eq_refl (term189 z x y)). Qed.
Lemma lem1283224 (x : nadd) (y : nadd) : (term183 x y) = (term183 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1283223 z x y)). Qed.
Lemma lem1283225 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283226 (x : nadd) (y : nadd) : (term201 x y) = (term201 x y).
Proof. exact (MK_COMB (@lem1283225) (@lem1283224 x y)). Qed.
Lemma lem1283227 (x : nadd) : (term300 x) = (term300 x).
Proof. exact (fun_ext (fun y : nadd => @lem1283226 x y)). Qed.
Lemma lem1283228 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283229 (x : nadd) : (term301 x) = (term301 x).
Proof. exact (MK_COMB (@lem1283228) (@lem1283227 x)). Qed.
Lemma lem1283230 : term302 = term302.
Proof. exact (fun_ext (fun x : nadd => @lem1283229 x)). Qed.
Lemma lem1283231 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283232 : term303 = term303.
Proof. exact (MK_COMB (@lem1283231) (@lem1283230)). Qed.
Lemma lem1283233 : term285 = term303.
Proof. exact (TRANS (@lem1283216) (@lem1283232)). Qed.
Lemma lem1283234 (h1 : term17) : term303.
Proof. exact (EQ_MP (@lem1283233) (@lem1283071 h1)). Qed.
Lemma lem1283278 (x : nadd) (y : nadd) (x' : nadd) (y' : nadd) : (term159 x y x' y') = (term287 x y x' y').
Proof. exact (@lem19490 (term288 x y x' y') (term154 x x' y y') (term289 x y x' y')). Qed.
Lemma lem1283279 (x : nadd) (y : nadd) (x' : nadd) : (term161 x y x') = (term290 x y x').
Proof. exact (fun_ext (fun y' : nadd => @lem1283278 x y x' y')). Qed.
Lemma lem1283280 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283281 (x : nadd) (y : nadd) (x' : nadd) : (term162 x y x') = (term291 x y x').
Proof. exact (MK_COMB (@lem1283280) (@lem1283279 x y x')). Qed.
Lemma lem1283282 (x : nadd) (x' : nadd) : (term163 x x') = (term292 x x').
Proof. exact (fun_ext (fun y : nadd => @lem1283281 x y x')). Qed.
Lemma lem1283283 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283284 (x : nadd) (x' : nadd) : (term164 x x') = (term293 x x').
Proof. exact (MK_COMB (@lem1283283) (@lem1283282 x x')). Qed.
Lemma lem1283285 (x : nadd) : (term165 x) = (term294 x).
Proof. exact (fun_ext (fun x' : nadd => @lem1283284 x x')). Qed.
Lemma lem1283286 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283287 (x : nadd) : (term166 x) = (term295 x).
Proof. exact (MK_COMB (@lem1283286) (@lem1283285 x)). Qed.
Lemma lem1283288 : term167 = term296.
Proof. exact (fun_ext (fun x : nadd => @lem1283287 x)). Qed.
Lemma lem1283289 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283291 : term168 = term297.
Proof. exact (MK_COMB (@lem1283289) (@lem1283288)). Qed.
Lemma lem1283292 (h1 : term45) : term297.
Proof. exact (EQ_MP (@lem1283291) (@lem1282932 h1)). Qed.
Lemma lem1283294 (y : nadd) (x : nadd) : (term32 y x) = (term32 y x).
Proof. exact (eq_refl (term32 y x)). Qed.
Lemma lem1283295 (x : nadd) : (term33 x) = (term33 x).
Proof. exact (fun_ext (fun y : nadd => @lem1283294 y x)). Qed.
Lemma lem1283296 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283297 (x : nadd) : (term34 x) = (term34 x).
Proof. exact (MK_COMB (@lem1283296) (@lem1283295 x)). Qed.
Lemma lem1283298 : term35 = term35.
Proof. exact (fun_ext (fun x : nadd => @lem1283297 x)). Qed.
Lemma lem1283299 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283301 : term36 = term36.
Proof. exact (MK_COMB (@lem1283299) (@lem1283298)). Qed.
Lemma lem1283302 (h1 : term36) : term36.
Proof. exact (EQ_MP (@lem1283301) (@lem1282952 h1)). Qed.
Lemma lem1283304 {A : Type'} (P : A -> Prop) (Q : Prop) : (term204 A P Q) = (term203 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1283305 (P : nadd -> Prop) (Q : Prop) : (term206 P Q) = (term205 P Q).
Proof. exact (@lem1283304 nadd P Q). Qed.
Lemma lem1283306 (x : nadd) (y : nadd) : (term208 x y) = (term207 x y).
Proof. exact (@lem1283305 (term209 x y) (term210 x y)). Qed.
Lemma lem1283307 (x : nadd) (y : nadd) (z : nadd) : (term211 x y z) = (term26 x y z).
Proof. exact (eq_refl (term211 x y z)). Qed.
Lemma lem1283308 (x : nadd) (y : nadd) : (term218 x y) = (term209 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1283307 x y z)). Qed.
Lemma lem1283309 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283310 (x : nadd) (y : nadd) : (term219 x y) = (term220 x y).
Proof. exact (MK_COMB (@lem1283309) (@lem1283308 x y)). Qed.
Lemma lem1283311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1283312 (x : nadd) (y : nadd) : (term221 x y) = (term222 x y).
Proof. exact (MK_COMB (@lem1283311) (@lem1283310 x y)). Qed.
Lemma lem1283313 (x : nadd) (y : nadd) : (term210 x y) = (term210 x y).
Proof. exact (eq_refl (term210 x y)). Qed.
Lemma lem1283314 (x : nadd) (y : nadd) : (term208 x y) = (term223 x y).
Proof. exact (MK_COMB (@lem1283312 x y) (@lem1283313 x y)). Qed.
Lemma lem1283315 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1283316 (x : nadd) (y : nadd) : (term304 x y) = (term305 x y).
Proof. exact (MK_COMB (@lem1283315) (@lem1283314 x y)). Qed.
Lemma lem1283317 (x : nadd) (y : nadd) (z : nadd) : (term211 x y z) = (term26 x y z).
Proof. exact (eq_refl (term211 x y z)). Qed.
Lemma lem1283318 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1283319 (x : nadd) (y : nadd) (z : nadd) : (term212 x y z) = (term213 x y z).
Proof. exact (MK_COMB (@lem1283318) (@lem1283317 x y z)). Qed.
Lemma lem1283320 (x : nadd) (y : nadd) : (term210 x y) = (term210 x y).
Proof. exact (eq_refl (term210 x y)). Qed.
Lemma lem1283321 (z : nadd) (x : nadd) (y : nadd) : (term214 z x y) = (term185 z x y).
Proof. exact (MK_COMB (@lem1283319 x y z) (@lem1283320 x y)). Qed.
Lemma lem1283322 (x : nadd) (y : nadd) : (term215 x y) = (term182 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1283321 z x y)). Qed.
Lemma lem1283323 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283324 (x : nadd) (y : nadd) : (term207 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1283323) (@lem1283322 x y)). Qed.
Lemma lem1283325 (x : nadd) (y : nadd) : ((term208 x y) = (term207 x y)) = ((term223 x y) = (term196 x y)).
Proof. exact (MK_COMB (@lem1283316 x y) (@lem1283324 x y)). Qed.
Lemma lem1283326 (x : nadd) (y : nadd) : (term223 x y) = (term196 x y).
Proof. exact (EQ_MP (@lem1283325 x y) (@lem1283306 x y)). Qed.
Lemma lem1283327 (x : nadd) : (term247 x) = (term306 x).
Proof. exact (fun_ext (fun y : nadd => @lem1283326 x y)). Qed.
Lemma lem1283328 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283329 (x : nadd) : (term258 x) = (term307 x).
Proof. exact (MK_COMB (@lem1283328) (@lem1283327 x)). Qed.
Lemma lem1283330 : term269 = term308.
Proof. exact (fun_ext (fun x : nadd => @lem1283329 x)). Qed.
Lemma lem1283331 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283332 : term280 = term309.
Proof. exact (MK_COMB (@lem1283331) (@lem1283330)). Qed.
Lemma lem1283339 (z : nadd) (x : nadd) (y : nadd) : (term185 z x y) = (term185 z x y).
Proof. exact (eq_refl (term185 z x y)). Qed.
Lemma lem1283340 (x : nadd) (y : nadd) : (term182 x y) = (term182 x y).
Proof. exact (fun_ext (fun z : nadd => @lem1283339 z x y)). Qed.
Lemma lem1283341 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283342 (x : nadd) (y : nadd) : (term196 x y) = (term196 x y).
Proof. exact (MK_COMB (@lem1283341) (@lem1283340 x y)). Qed.
Lemma lem1283343 (x : nadd) : (term306 x) = (term306 x).
Proof. exact (fun_ext (fun y : nadd => @lem1283342 x y)). Qed.
Lemma lem1283344 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283345 (x : nadd) : (term307 x) = (term307 x).
Proof. exact (MK_COMB (@lem1283344) (@lem1283343 x)). Qed.
Lemma lem1283346 : term308 = term308.
Proof. exact (fun_ext (fun x : nadd => @lem1283345 x)). Qed.
Lemma lem1283347 : (@all nadd) = (@all nadd).
Proof. exact (eq_refl (@all nadd)). Qed.
Lemma lem1283348 : term309 = term309.
Proof. exact (MK_COMB (@lem1283347) (@lem1283346)). Qed.
Lemma lem1283349 : term280 = term309.
Proof. exact (TRANS (@lem1283332) (@lem1283348)). Qed.
Lemma lem1283350 (h1 : term17) : term309.
Proof. exact (EQ_MP (@lem1283349) (@lem1283072 h1)). Qed.
Lemma lem1283407 (_23219 : nadd) (h1 : term45) : term310 _23219.
Proof. exact (@lem1283128 h1 _23219). Qed.
Lemma lem1283408 (_23219 : nadd) : (term310 _23219) = (term295 _23219).
Proof. exact (eq_refl (term310 _23219)). Qed.
Lemma lem1283409 (_23219 : nadd) (h1 : term45) : term295 _23219.
Proof. exact (EQ_MP (@lem1283408 _23219) (@lem1283407 _23219 h1)). Qed.
Lemma lem1283410 (_23219 : nadd) (_23220 : nadd) (h1 : term45) : term311 _23219 _23220.
Proof. exact (@lem1283409 _23219 h1 _23220). Qed.
Lemma lem1283411 (_23219 : nadd) (_23220 : nadd) : (term311 _23219 _23220) = (term293 _23219 _23220).
Proof. exact (eq_refl (term311 _23219 _23220)). Qed.
Lemma lem1283412 (_23219 : nadd) (_23220 : nadd) (h1 : term45) : term293 _23219 _23220.
Proof. exact (EQ_MP (@lem1283411 _23219 _23220) (@lem1283410 _23219 _23220 h1)). Qed.
Lemma lem1283413 (_23219 : nadd) (_23220 : nadd) (_23221 : nadd) (h1 : term45) : term312 _23219 _23220 _23221.
Proof. exact (@lem1283412 _23219 _23220 h1 _23221). Qed.
Lemma lem1283414 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) : (term312 _23219 _23220 _23221) = (term291 _23219 _23221 _23220).
Proof. exact (eq_refl (term312 _23219 _23220 _23221)). Qed.
Lemma lem1283415 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (h1 : term45) : term291 _23219 _23221 _23220.
Proof. exact (EQ_MP (@lem1283414 _23219 _23221 _23220) (@lem1283413 _23219 _23220 _23221 h1)). Qed.
Lemma lem1283416 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) (h1 : term45) : term313 _23219 _23221 _23220 _23222.
Proof. exact (@lem1283415 _23219 _23221 _23220 h1 _23222). Qed.
Lemma lem1283417 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) : (term313 _23219 _23221 _23220 _23222) = (term287 _23219 _23221 _23220 _23222).
Proof. exact (eq_refl (term313 _23219 _23221 _23220 _23222)). Qed.
Lemma lem1283418 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) (h1 : term45) : term287 _23219 _23221 _23220 _23222.
Proof. exact (EQ_MP (@lem1283417 _23219 _23221 _23220 _23222) (@lem1283416 _23219 _23221 _23220 _23222 h1)). Qed.
Lemma lem1283419 (_23223 : nadd) (h1 : term36) : term314 _23223.
Proof. exact (@lem1283138 h1 _23223). Qed.
Lemma lem1283420 (_23223 : nadd) : (term314 _23223) = (term34 _23223).
Proof. exact (eq_refl (term314 _23223)). Qed.
Lemma lem1283421 (_23223 : nadd) (h1 : term36) : term34 _23223.
Proof. exact (EQ_MP (@lem1283420 _23223) (@lem1283419 _23223 h1)). Qed.
Lemma lem1283422 (_23223 : nadd) (_23224 : nadd) (h1 : term36) : term315 _23223 _23224.
Proof. exact (@lem1283421 _23223 h1 _23224). Qed.
Lemma lem1283423 (_23224 : nadd) (_23223 : nadd) : (term315 _23223 _23224) = (term32 _23224 _23223).
Proof. exact (eq_refl (term315 _23223 _23224)). Qed.
Lemma lem1283434 (_23228 : nadd) (h1 : term17) : term316 _23228.
Proof. exact (@lem1283234 h1 _23228). Qed.
Lemma lem1283435 (_23228 : nadd) : (term316 _23228) = (term301 _23228).
Proof. exact (eq_refl (term316 _23228)). Qed.
Lemma lem1283436 (_23228 : nadd) (h1 : term17) : term301 _23228.
Proof. exact (EQ_MP (@lem1283435 _23228) (@lem1283434 _23228 h1)). Qed.
Lemma lem1283437 (_23228 : nadd) (_23229 : nadd) (h1 : term17) : term317 _23228 _23229.
Proof. exact (@lem1283436 _23228 h1 _23229). Qed.
Lemma lem1283438 (_23228 : nadd) (_23229 : nadd) : (term317 _23228 _23229) = (term201 _23228 _23229).
Proof. exact (eq_refl (term317 _23228 _23229)). Qed.
Lemma lem1283439 (_23228 : nadd) (_23229 : nadd) (h1 : term17) : term201 _23228 _23229.
Proof. exact (EQ_MP (@lem1283438 _23228 _23229) (@lem1283437 _23228 _23229 h1)). Qed.
Lemma lem1283440 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) (h1 : term17) : term188 _23228 _23229 _23230.
Proof. exact (@lem1283439 _23228 _23229 h1 _23230). Qed.
Lemma lem1283441 (_23230 : nadd) (_23228 : nadd) (_23229 : nadd) : (term188 _23228 _23229 _23230) = (term189 _23230 _23228 _23229).
Proof. exact (eq_refl (term188 _23228 _23229 _23230)). Qed.
Lemma lem1283443 (_23231 : nadd) (h1 : term45) : term310 _23231.
Proof. exact (@lem1283292 h1 _23231). Qed.
Lemma lem1283444 (_23231 : nadd) : (term310 _23231) = (term295 _23231).
Proof. exact (eq_refl (term310 _23231)). Qed.
Lemma lem1283445 (_23231 : nadd) (h1 : term45) : term295 _23231.
Proof. exact (EQ_MP (@lem1283444 _23231) (@lem1283443 _23231 h1)). Qed.
Lemma lem1283446 (_23231 : nadd) (_23232 : nadd) (h1 : term45) : term311 _23231 _23232.
Proof. exact (@lem1283445 _23231 h1 _23232). Qed.
Lemma lem1283447 (_23231 : nadd) (_23232 : nadd) : (term311 _23231 _23232) = (term293 _23231 _23232).
Proof. exact (eq_refl (term311 _23231 _23232)). Qed.
Lemma lem1283448 (_23231 : nadd) (_23232 : nadd) (h1 : term45) : term293 _23231 _23232.
Proof. exact (EQ_MP (@lem1283447 _23231 _23232) (@lem1283446 _23231 _23232 h1)). Qed.
Lemma lem1283449 (_23231 : nadd) (_23232 : nadd) (_23233 : nadd) (h1 : term45) : term312 _23231 _23232 _23233.
Proof. exact (@lem1283448 _23231 _23232 h1 _23233). Qed.
Lemma lem1283450 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) : (term312 _23231 _23232 _23233) = (term291 _23231 _23233 _23232).
Proof. exact (eq_refl (term312 _23231 _23232 _23233)). Qed.
Lemma lem1283451 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (h1 : term45) : term291 _23231 _23233 _23232.
Proof. exact (EQ_MP (@lem1283450 _23231 _23233 _23232) (@lem1283449 _23231 _23232 _23233 h1)). Qed.
Lemma lem1283452 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) (h1 : term45) : term313 _23231 _23233 _23232 _23234.
Proof. exact (@lem1283451 _23231 _23233 _23232 h1 _23234). Qed.
Lemma lem1283453 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) : (term313 _23231 _23233 _23232 _23234) = (term287 _23231 _23233 _23232 _23234).
Proof. exact (eq_refl (term313 _23231 _23233 _23232 _23234)). Qed.
Lemma lem1283454 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) (h1 : term45) : term287 _23231 _23233 _23232 _23234.
Proof. exact (EQ_MP (@lem1283453 _23231 _23233 _23232 _23234) (@lem1283452 _23231 _23233 _23232 _23234 h1)). Qed.
Lemma lem1283455 (_23235 : nadd) (h1 : term36) : term314 _23235.
Proof. exact (@lem1283302 h1 _23235). Qed.
Lemma lem1283456 (_23235 : nadd) : (term314 _23235) = (term34 _23235).
Proof. exact (eq_refl (term314 _23235)). Qed.
Lemma lem1283457 (_23235 : nadd) (h1 : term36) : term34 _23235.
Proof. exact (EQ_MP (@lem1283456 _23235) (@lem1283455 _23235 h1)). Qed.
Lemma lem1283458 (_23235 : nadd) (_23236 : nadd) (h1 : term36) : term315 _23235 _23236.
Proof. exact (@lem1283457 _23235 h1 _23236). Qed.
Lemma lem1283459 (_23236 : nadd) (_23235 : nadd) : (term315 _23235 _23236) = (term32 _23236 _23235).
Proof. exact (eq_refl (term315 _23235 _23236)). Qed.
Lemma lem1283461 (_23237 : nadd) (h1 : term17) : term318 _23237.
Proof. exact (@lem1283350 h1 _23237). Qed.
Lemma lem1283462 (_23237 : nadd) : (term318 _23237) = (term307 _23237).
Proof. exact (eq_refl (term318 _23237)). Qed.
Lemma lem1283463 (_23237 : nadd) (h1 : term17) : term307 _23237.
Proof. exact (EQ_MP (@lem1283462 _23237) (@lem1283461 _23237 h1)). Qed.
Lemma lem1283464 (_23237 : nadd) (_23238 : nadd) (h1 : term17) : term319 _23237 _23238.
Proof. exact (@lem1283463 _23237 h1 _23238). Qed.
Lemma lem1283465 (_23237 : nadd) (_23238 : nadd) : (term319 _23237 _23238) = (term196 _23237 _23238).
Proof. exact (eq_refl (term319 _23237 _23238)). Qed.
Lemma lem1283466 (_23237 : nadd) (_23238 : nadd) (h1 : term17) : term196 _23237 _23238.
Proof. exact (EQ_MP (@lem1283465 _23237 _23238) (@lem1283464 _23237 _23238 h1)). Qed.
Lemma lem1283467 (_23237 : nadd) (_23238 : nadd) (_23239 : nadd) (h1 : term17) : term184 _23237 _23238 _23239.
Proof. exact (@lem1283466 _23237 _23238 h1 _23239). Qed.
Lemma lem1283468 (_23239 : nadd) (_23237 : nadd) (_23238 : nadd) : (term184 _23237 _23238 _23239) = (term185 _23239 _23237 _23238).
Proof. exact (eq_refl (term184 _23237 _23238 _23239)). Qed.
Lemma lem1283479 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) (h1 : term45) : term320 _23219 _23221 _23220 _23222.
Proof. exact (proj2 (@lem1283418 _23219 _23221 _23220 _23222 h1)). Qed.
Lemma lem1283481 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) (h1 : term45) : term320 _23231 _23233 _23232 _23234.
Proof. exact (proj2 (@lem1283454 _23231 _23233 _23232 _23234 h1)). Qed.
Lemma lem1283496 (_23230 : nadd) (_23228 : nadd) (_23229 : nadd) (h1 : term17) : term189 _23230 _23228 _23229.
Proof. exact (EQ_MP (@lem1283441 _23230 _23228 _23229) (@lem1283440 _23228 _23229 _23230 h1)). Qed.
Lemma lem1283500 (x : nadd) (y : nadd) (z : nadd) (h1 : term85 x y z) : term210 y z.
Proof. exact (proj2 (@lem1283073 x y z h1)). Qed.
Lemma lem1283531 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) : (term320 _23219 _23221 _23220 _23222) = (term321 _23219 _23221 _23220 _23222).
Proof. exact (@lem1281492 (term322 _23219 _23220) (term322 _23221 _23222) (term289 _23219 _23221 _23220 _23222)). Qed.
Lemma lem1283532 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) (h1 : term45) : term321 _23219 _23221 _23220 _23222.
Proof. exact (EQ_MP (@lem1283531 _23219 _23221 _23220 _23222) (@lem1283479 _23219 _23221 _23220 _23222 h1)). Qed.
Lemma lem1283540 (_23239 : nadd) (_23237 : nadd) (_23238 : nadd) (h1 : term17) : term185 _23239 _23237 _23238.
Proof. exact (EQ_MP (@lem1283468 _23239 _23237 _23238) (@lem1283467 _23237 _23238 _23239 h1)). Qed.
Lemma lem1283548 (x : nadd) (y : nadd) (z : nadd) (h1 : term89 x y z) : term323 y x z.
Proof. exact (proj1 (@lem1283074 x y z h1)). Qed.
Lemma lem1283581 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) : (term320 _23231 _23233 _23232 _23234) = (term321 _23231 _23233 _23232 _23234).
Proof. exact (@lem1281492 (term322 _23231 _23232) (term322 _23233 _23234) (term289 _23231 _23233 _23232 _23234)). Qed.
Lemma lem1283582 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) (h1 : term45) : term321 _23231 _23233 _23232 _23234.
Proof. exact (EQ_MP (@lem1283581 _23231 _23233 _23232 _23234) (@lem1283481 _23231 _23233 _23232 _23234 h1)). Qed.
Lemma lem1283584 (_23224 : nadd) (_23223 : nadd) (h1 : term36) : term32 _23224 _23223.
Proof. exact (EQ_MP (@lem1283423 _23224 _23223) (@lem1283422 _23223 _23224 h1)). Qed.
Lemma lem1283585 (y : nadd) (x : nadd) (h1 : term36) : term32 y x.
Proof. exact (@lem1283584 y x h1). Qed.
Lemma lem1283586 (y : nadd) (x : nadd) (h1 : term36) : term324 y x.
Proof. exact (fun h0 : term325 y x => @lem1283585 y x h1). Qed.
Lemma lem1283588 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283589 (y : nadd) (x : nadd) : (term324 y x) = (term32 y x).
Proof. exact (@lem1283588 (term32 y x)). Qed.
Lemma lem1283590 (y : nadd) (x : nadd) (h1 : term36) : term32 y x.
Proof. exact (EQ_MP (@lem1283589 y x) (@lem1283586 y x h1)). Qed.
Lemma lem1283592 (_23224 : nadd) (_23223 : nadd) (h1 : term36) : term32 _23224 _23223.
Proof. exact (EQ_MP (@lem1283423 _23224 _23223) (@lem1283422 _23223 _23224 h1)). Qed.
Lemma lem1283593 (z : nadd) (x : nadd) (h1 : term36) : term32 z x.
Proof. exact (@lem1283592 z x h1). Qed.
Lemma lem1283594 (z : nadd) (x : nadd) (h1 : term36) : term324 z x.
Proof. exact (fun h0 : term325 z x => @lem1283593 z x h1). Qed.
Lemma lem1283596 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283597 (z : nadd) (x : nadd) : (term324 z x) = (term32 z x).
Proof. exact (@lem1283596 (term32 z x)). Qed.
Lemma lem1283598 (z : nadd) (x : nadd) (h1 : term36) : term32 z x.
Proof. exact (EQ_MP (@lem1283597 z x) (@lem1283594 z x h1)). Qed.
Lemma lem1283600 (x : nadd) (y : nadd) (z : nadd) (h1 : term85 x y z) : term46 y x z.
Proof. exact (proj1 (@lem1283073 x y z h1)). Qed.
Lemma lem1283601 (x : nadd) (y : nadd) (z : nadd) (h1 : term85 x y z) : term327 y x z.
Proof. exact (fun h0 : term323 y x z => @lem1283600 x y z h1). Qed.
Lemma lem1283603 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283604 (y : nadd) (x : nadd) (z : nadd) : (term327 y x z) = (term46 y x z).
Proof. exact (@lem1283603 (term46 y x z)). Qed.
Lemma lem1283605 (x : nadd) (y : nadd) (z : nadd) (h1 : term85 x y z) : term46 y x z.
Proof. exact (EQ_MP (@lem1283604 y x z) (@lem1283601 x y z h1)). Qed.
Lemma lem1283631 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1283632 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term289 _23219 _23221 _23220 _23222) = (term288 _23220 _23222 _23219 _23221).
Proof. exact (@lem1283631 (nadd_le _23220 _23222) (term210 _23219 _23221)). Qed.
Lemma lem1283638 (_23221 : nadd) (_23222 : nadd) : (term328 _23221 _23222) = (term328 _23221 _23222).
Proof. exact (eq_refl (term328 _23221 _23222)). Qed.
Lemma lem1283639 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term329 _23219 _23221 _23220 _23222) = (term330 _23220 _23222 _23219 _23221).
Proof. exact (MK_COMB (@lem1283638 _23221 _23222) (@lem1283632 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283643 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1283644 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term330 _23220 _23222 _23219 _23221) = (term331 _23220 _23222 _23219 _23221).
Proof. exact (@lem1283643 (nadd_le _23220 _23222) (term322 _23221 _23222) (term210 _23219 _23221)). Qed.
Lemma lem1283660 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term329 _23219 _23221 _23220 _23222) = (term331 _23220 _23222 _23219 _23221).
Proof. exact (TRANS (@lem1283639 _23220 _23222 _23219 _23221) (@lem1283644 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283661 (_23219 : nadd) (_23220 : nadd) : (term328 _23219 _23220) = (term328 _23219 _23220).
Proof. exact (eq_refl (term328 _23219 _23220)). Qed.
Lemma lem1283662 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term321 _23219 _23221 _23220 _23222) = (term332 _23220 _23222 _23219 _23221).
Proof. exact (MK_COMB (@lem1283661 _23219 _23220) (@lem1283660 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283666 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1283667 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term332 _23220 _23222 _23219 _23221) = (term333 _23220 _23222 _23219 _23221).
Proof. exact (@lem1283666 (nadd_le _23220 _23222) (term322 _23219 _23220) (term334 _23222 _23219 _23221)). Qed.
Lemma lem1283693 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term321 _23219 _23221 _23220 _23222) = (term333 _23220 _23222 _23219 _23221).
Proof. exact (TRANS (@lem1283662 _23220 _23222 _23219 _23221) (@lem1283667 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1283695 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term335 _23219 _23221 _23220 _23222) = (term336 _23220 _23222 _23219 _23221).
Proof. exact (MK_COMB (@lem1283694) (@lem1283693 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283721 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term333 _23220 _23222 _23219 _23221) = (term333 _23220 _23222 _23219 _23221).
Proof. exact (eq_refl (term333 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283722 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : ((term321 _23219 _23221 _23220 _23222) = (term333 _23220 _23222 _23219 _23221)) = ((term333 _23220 _23222 _23219 _23221) = (term333 _23220 _23222 _23219 _23221)).
Proof. exact (MK_COMB (@lem1283695 _23220 _23222 _23219 _23221) (@lem1283721 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283724 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1283725 (x : Prop) : (x = x) = True.
Proof. exact (@lem1283724 Prop x). Qed.
Lemma lem1283726 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : ((term333 _23220 _23222 _23219 _23221) = (term333 _23220 _23222 _23219 _23221)) = True.
Proof. exact (@lem1283725 (term333 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283727 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : ((term321 _23219 _23221 _23220 _23222) = (term333 _23220 _23222 _23219 _23221)) = True.
Proof. exact (TRANS (@lem1283722 _23220 _23222 _23219 _23221) (@lem1283726 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283728 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : True = ((term321 _23219 _23221 _23220 _23222) = (term333 _23220 _23222 _23219 _23221)).
Proof. exact (SYM (@lem1283727 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283729 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term321 _23219 _23221 _23220 _23222) = (term333 _23220 _23222 _23219 _23221).
Proof. exact (EQ_MP (@lem1283728 _23220 _23222 _23219 _23221) (@lem0)). Qed.
Lemma lem1283730 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) (h1 : term45) : term333 _23220 _23222 _23219 _23221.
Proof. exact (EQ_MP (@lem1283729 _23220 _23222 _23219 _23221) (@lem1283532 _23219 _23221 _23220 _23222 h1)). Qed.
Lemma lem1283732 (b : Prop) (a : Prop) : (a \/ b) = (term337 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1283733 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) : (term333 _23220 _23222 _23219 _23221) = (term338 _23219 _23221 _23220 _23222).
Proof. exact (@lem1283732 (term339 _23220 _23222 _23219 _23221) (nadd_le _23220 _23222)). Qed.
Lemma lem1283735 (a : Prop) (b : Prop) : (term340 a b) = (term341 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1283736 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term342 _23220 _23222 _23219 _23221) = (term343 _23220 _23222 _23219 _23221).
Proof. exact (@lem1283735 (term322 _23219 _23220) (term334 _23222 _23219 _23221)). Qed.
Lemma lem1283738 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1283739 (_23219 : nadd) (_23220 : nadd) : (term345 _23219 _23220) = (nadd_eq _23219 _23220).
Proof. exact (@lem1283738 (nadd_eq _23219 _23220)). Qed.
Lemma lem1283740 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1283741 (_23219 : nadd) (_23220 : nadd) : (term346 _23219 _23220) = (term347 _23219 _23220).
Proof. exact (MK_COMB (@lem1283740) (@lem1283739 _23219 _23220)). Qed.
Lemma lem1283743 (a : Prop) (b : Prop) : (term340 a b) = (term341 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1283744 (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term348 _23222 _23219 _23221) = (term349 _23222 _23219 _23221).
Proof. exact (@lem1283743 (term322 _23221 _23222) (term210 _23219 _23221)). Qed.
Lemma lem1283746 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1283747 (_23221 : nadd) (_23222 : nadd) : (term345 _23221 _23222) = (nadd_eq _23221 _23222).
Proof. exact (@lem1283746 (nadd_eq _23221 _23222)). Qed.
Lemma lem1283748 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1283749 (_23221 : nadd) (_23222 : nadd) : (term346 _23221 _23222) = (term347 _23221 _23222).
Proof. exact (MK_COMB (@lem1283748) (@lem1283747 _23221 _23222)). Qed.
Lemma lem1283751 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1283752 (_23219 : nadd) (_23221 : nadd) : (term350 _23219 _23221) = (nadd_le _23219 _23221).
Proof. exact (@lem1283751 (nadd_le _23219 _23221)). Qed.
Lemma lem1283753 (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term349 _23222 _23219 _23221) = (term351 _23222 _23219 _23221).
Proof. exact (MK_COMB (@lem1283749 _23221 _23222) (@lem1283752 _23219 _23221)). Qed.
Lemma lem1283754 (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term348 _23222 _23219 _23221) = (term351 _23222 _23219 _23221).
Proof. exact (TRANS (@lem1283744 _23222 _23219 _23221) (@lem1283753 _23222 _23219 _23221)). Qed.
Lemma lem1283755 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term343 _23220 _23222 _23219 _23221) = (term352 _23220 _23222 _23219 _23221).
Proof. exact (MK_COMB (@lem1283741 _23219 _23220) (@lem1283754 _23222 _23219 _23221)). Qed.
Lemma lem1283756 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term342 _23220 _23222 _23219 _23221) = (term352 _23220 _23222 _23219 _23221).
Proof. exact (TRANS (@lem1283736 _23220 _23222 _23219 _23221) (@lem1283755 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283757 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1283758 (_23220 : nadd) (_23222 : nadd) (_23219 : nadd) (_23221 : nadd) : (term353 _23220 _23222 _23219 _23221) = (term354 _23220 _23222 _23219 _23221).
Proof. exact (MK_COMB (@lem1283757) (@lem1283756 _23220 _23222 _23219 _23221)). Qed.
Lemma lem1283759 (_23220 : nadd) (_23222 : nadd) : (nadd_le _23220 _23222) = (nadd_le _23220 _23222).
Proof. exact (eq_refl (nadd_le _23220 _23222)). Qed.
Lemma lem1283760 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) : (term338 _23219 _23221 _23220 _23222) = (term355 _23219 _23221 _23220 _23222).
Proof. exact (MK_COMB (@lem1283758 _23220 _23222 _23219 _23221) (@lem1283759 _23220 _23222)). Qed.
Lemma lem1283761 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) : (term333 _23220 _23222 _23219 _23221) = (term355 _23219 _23221 _23220 _23222).
Proof. exact (TRANS (@lem1283733 _23219 _23221 _23220 _23222) (@lem1283760 _23219 _23221 _23220 _23222)). Qed.
Lemma lem1283763 (x : nadd) (y : nadd) (z : nadd) (h1 : term36) (h2 : term85 x y z) : term356 y x z.
Proof. exact (conj (@lem1283598 z x h1) (@lem1283605 x y z h2)). Qed.
Lemma lem1283764 (x : nadd) (y : nadd) (z : nadd) (h1 : term36) (h2 : term85 x y z) : term357 y x z.
Proof. exact (conj (@lem1283590 y x h1) (@lem1283763 x y z h1 h2)). Qed.
Lemma lem1283766 (_23219 : nadd) (_23221 : nadd) (_23220 : nadd) (_23222 : nadd) (h1 : term45) : term355 _23219 _23221 _23220 _23222.
Proof. exact (EQ_MP (@lem1283761 _23219 _23221 _23220 _23222) (@lem1283730 _23220 _23222 _23219 _23221 h1)). Qed.
Lemma lem1283767 (y : nadd) (z : nadd) (x : nadd) (h1 : term45) : term358 y z x.
Proof. exact (@lem1283766 (nadd_add x y) (nadd_add x z) (nadd_add y x) (nadd_add z x) h1). Qed.
Lemma lem1283770 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term36) (h3 : term85 x y z) : term26 y z x.
Proof. exact (@lem1283767 y z x h1 (@lem1283764 x y z h2 h3)). Qed.
Lemma lem1283771 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term36) (h3 : term85 x y z) : term359 y z x.
Proof. exact (fun h0 : term229 y z x => @lem1283770 x y z h1 h2 h3). Qed.
Lemma lem1283773 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283774 (y : nadd) (z : nadd) (x : nadd) : (term359 y z x) = (term26 y z x).
Proof. exact (@lem1283773 (term26 y z x)). Qed.
Lemma lem1283775 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term36) (h3 : term85 x y z) : term26 y z x.
Proof. exact (EQ_MP (@lem1283774 y z x) (@lem1283771 x y z h1 h2 h3)). Qed.
Lemma lem1283781 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1283782 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : (term189 _23230 _23228 _23229) = (term360 _23228 _23229 _23230).
Proof. exact (@lem1283781 (nadd_le _23228 _23229) (term229 _23228 _23229 _23230)). Qed.
Lemma lem1283788 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1283789 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : (term361 _23230 _23228 _23229) = (term362 _23228 _23229 _23230).
Proof. exact (MK_COMB (@lem1283788) (@lem1283782 _23228 _23229 _23230)). Qed.
Lemma lem1283795 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : (term360 _23228 _23229 _23230) = (term360 _23228 _23229 _23230).
Proof. exact (eq_refl (term360 _23228 _23229 _23230)). Qed.
Lemma lem1283796 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : ((term189 _23230 _23228 _23229) = (term360 _23228 _23229 _23230)) = ((term360 _23228 _23229 _23230) = (term360 _23228 _23229 _23230)).
Proof. exact (MK_COMB (@lem1283789 _23228 _23229 _23230) (@lem1283795 _23228 _23229 _23230)). Qed.
Lemma lem1283798 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1283799 (x : Prop) : (x = x) = True.
Proof. exact (@lem1283798 Prop x). Qed.
Lemma lem1283800 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : ((term360 _23228 _23229 _23230) = (term360 _23228 _23229 _23230)) = True.
Proof. exact (@lem1283799 (term360 _23228 _23229 _23230)). Qed.
Lemma lem1283801 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : ((term189 _23230 _23228 _23229) = (term360 _23228 _23229 _23230)) = True.
Proof. exact (TRANS (@lem1283796 _23228 _23229 _23230) (@lem1283800 _23228 _23229 _23230)). Qed.
Lemma lem1283802 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : True = ((term189 _23230 _23228 _23229) = (term360 _23228 _23229 _23230)).
Proof. exact (SYM (@lem1283801 _23228 _23229 _23230)). Qed.
Lemma lem1283803 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : (term189 _23230 _23228 _23229) = (term360 _23228 _23229 _23230).
Proof. exact (EQ_MP (@lem1283802 _23228 _23229 _23230) (@lem0)). Qed.
Lemma lem1283804 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) (h1 : term17) : term360 _23228 _23229 _23230.
Proof. exact (EQ_MP (@lem1283803 _23228 _23229 _23230) (@lem1283496 _23230 _23228 _23229 h1)). Qed.
Lemma lem1283806 (b : Prop) (a : Prop) : (a \/ b) = (term337 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1283807 (_23230 : nadd) (_23228 : nadd) (_23229 : nadd) : (term360 _23228 _23229 _23230) = (term363 _23230 _23228 _23229).
Proof. exact (@lem1283806 (term229 _23228 _23229 _23230) (nadd_le _23228 _23229)). Qed.
Lemma lem1283809 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1283810 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : (term364 _23228 _23229 _23230) = (term26 _23228 _23229 _23230).
Proof. exact (@lem1283809 (term26 _23228 _23229 _23230)). Qed.
Lemma lem1283811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1283812 (_23228 : nadd) (_23229 : nadd) (_23230 : nadd) : (term365 _23228 _23229 _23230) = (term366 _23228 _23229 _23230).
Proof. exact (MK_COMB (@lem1283811) (@lem1283810 _23228 _23229 _23230)). Qed.
Lemma lem1283813 (_23228 : nadd) (_23229 : nadd) : (nadd_le _23228 _23229) = (nadd_le _23228 _23229).
Proof. exact (eq_refl (nadd_le _23228 _23229)). Qed.
Lemma lem1283814 (_23230 : nadd) (_23228 : nadd) (_23229 : nadd) : (term363 _23230 _23228 _23229) = (term367 _23230 _23228 _23229).
Proof. exact (MK_COMB (@lem1283812 _23228 _23229 _23230) (@lem1283813 _23228 _23229)). Qed.
Lemma lem1283815 (_23230 : nadd) (_23228 : nadd) (_23229 : nadd) : (term360 _23228 _23229 _23230) = (term367 _23230 _23228 _23229).
Proof. exact (TRANS (@lem1283807 _23230 _23228 _23229) (@lem1283814 _23230 _23228 _23229)). Qed.
Lemma lem1283818 (_23230 : nadd) (_23228 : nadd) (_23229 : nadd) (h1 : term17) : term367 _23230 _23228 _23229.
Proof. exact (EQ_MP (@lem1283815 _23230 _23228 _23229) (@lem1283804 _23228 _23229 _23230 h1)). Qed.
Lemma lem1283819 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) : term367 x y z.
Proof. exact (@lem1283818 x y z h1). Qed.
Lemma lem1283822 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : nadd_le y z.
Proof. exact (@lem1283819 x y z h2 (@lem1283775 x y z h1 h3 h4)). Qed.
Lemma lem1283823 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : term368 y z.
Proof. exact (fun h0 : term210 y z => @lem1283822 x y z h1 h2 h3 h4). Qed.
Lemma lem1283825 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283826 (y : nadd) (z : nadd) : (term368 y z) = (nadd_le y z).
Proof. exact (@lem1283825 (nadd_le y z)). Qed.
Lemma lem1283827 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : nadd_le y z.
Proof. exact (EQ_MP (@lem1283826 y z) (@lem1283823 x y z h1 h2 h3 h4)). Qed.
Lemma lem1283830 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1283832 (y : nadd) (z : nadd) : (term210 y z) = (term369 y z).
Proof. exact (@lem1283830 (nadd_le y z)). Qed.
Lemma lem1283835 (x : nadd) (y : nadd) (z : nadd) (h1 : term85 x y z) : term369 y z.
Proof. exact (EQ_MP (@lem1283832 y z) (@lem1283500 x y z h1)). Qed.
Lemma lem1283838 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : False.
Proof. exact (@lem1283835 x y z h4 (@lem1283827 x y z h1 h2 h3 h4)). Qed.
Lemma lem1283839 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : term370.
Proof. exact (fun h0 : ~ False => @lem1283838 x y z h1 h2 h3 h4). Qed.
Lemma lem1283841 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283842 : term370 = False.
Proof. exact (@lem1283841 False). Qed.
Lemma lem1283843 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : False.
Proof. exact (EQ_MP (@lem1283842) (@lem1283839 x y z h1 h2 h3 h4)). Qed.
Lemma lem1283845 (_23236 : nadd) (_23235 : nadd) (h1 : term36) : term32 _23236 _23235.
Proof. exact (EQ_MP (@lem1283459 _23236 _23235) (@lem1283458 _23235 _23236 h1)). Qed.
Lemma lem1283846 (x : nadd) (y : nadd) (h1 : term36) : term32 x y.
Proof. exact (@lem1283845 x y h1). Qed.
Lemma lem1283847 (x : nadd) (y : nadd) (h1 : term36) : term324 x y.
Proof. exact (fun h0 : term325 x y => @lem1283846 x y h1). Qed.
Lemma lem1283849 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283850 (x : nadd) (y : nadd) : (term324 x y) = (term32 x y).
Proof. exact (@lem1283849 (term32 x y)). Qed.
Lemma lem1283851 (x : nadd) (y : nadd) (h1 : term36) : term32 x y.
Proof. exact (EQ_MP (@lem1283850 x y) (@lem1283847 x y h1)). Qed.
Lemma lem1283853 (_23236 : nadd) (_23235 : nadd) (h1 : term36) : term32 _23236 _23235.
Proof. exact (EQ_MP (@lem1283459 _23236 _23235) (@lem1283458 _23235 _23236 h1)). Qed.
Lemma lem1283854 (x : nadd) (z : nadd) (h1 : term36) : term32 x z.
Proof. exact (@lem1283853 x z h1). Qed.
Lemma lem1283855 (x : nadd) (z : nadd) (h1 : term36) : term324 x z.
Proof. exact (fun h0 : term325 x z => @lem1283854 x z h1). Qed.
Lemma lem1283857 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283858 (x : nadd) (z : nadd) : (term324 x z) = (term32 x z).
Proof. exact (@lem1283857 (term32 x z)). Qed.
Lemma lem1283859 (x : nadd) (z : nadd) (h1 : term36) : term32 x z.
Proof. exact (EQ_MP (@lem1283858 x z) (@lem1283855 x z h1)). Qed.
Lemma lem1283861 (x : nadd) (y : nadd) (z : nadd) (h1 : term89 x y z) : nadd_le y z.
Proof. exact (proj2 (@lem1283074 x y z h1)). Qed.
Lemma lem1283862 (x : nadd) (y : nadd) (z : nadd) (h1 : term89 x y z) : term368 y z.
Proof. exact (fun h0 : term210 y z => @lem1283861 x y z h1). Qed.
Lemma lem1283864 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283865 (y : nadd) (z : nadd) : (term368 y z) = (nadd_le y z).
Proof. exact (@lem1283864 (nadd_le y z)). Qed.
Lemma lem1283866 (x : nadd) (y : nadd) (z : nadd) (h1 : term89 x y z) : nadd_le y z.
Proof. exact (EQ_MP (@lem1283865 y z) (@lem1283862 x y z h1)). Qed.
Lemma lem1283868 (b : Prop) (a : Prop) : (a \/ b) = (term337 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1283869 (_23237 : nadd) (_23238 : nadd) (_23239 : nadd) : (term185 _23239 _23237 _23238) = (term371 _23237 _23238 _23239).
Proof. exact (@lem1283868 (term210 _23237 _23238) (term26 _23237 _23238 _23239)). Qed.
Lemma lem1283871 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1283872 (_23237 : nadd) (_23238 : nadd) : (term350 _23237 _23238) = (nadd_le _23237 _23238).
Proof. exact (@lem1283871 (nadd_le _23237 _23238)). Qed.
Lemma lem1283873 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1283874 (_23237 : nadd) (_23238 : nadd) : (term372 _23237 _23238) = (term373 _23237 _23238).
Proof. exact (MK_COMB (@lem1283873) (@lem1283872 _23237 _23238)). Qed.
Lemma lem1283875 (_23237 : nadd) (_23238 : nadd) (_23239 : nadd) : (term26 _23237 _23238 _23239) = (term26 _23237 _23238 _23239).
Proof. exact (eq_refl (term26 _23237 _23238 _23239)). Qed.
Lemma lem1283876 (_23237 : nadd) (_23238 : nadd) (_23239 : nadd) : (term371 _23237 _23238 _23239) = (term374 _23237 _23238 _23239).
Proof. exact (MK_COMB (@lem1283874 _23237 _23238) (@lem1283875 _23237 _23238 _23239)). Qed.
Lemma lem1283877 (_23237 : nadd) (_23238 : nadd) (_23239 : nadd) : (term185 _23239 _23237 _23238) = (term374 _23237 _23238 _23239).
Proof. exact (TRANS (@lem1283869 _23237 _23238 _23239) (@lem1283876 _23237 _23238 _23239)). Qed.
Lemma lem1283880 (_23237 : nadd) (_23238 : nadd) (_23239 : nadd) (h1 : term17) : term374 _23237 _23238 _23239.
Proof. exact (EQ_MP (@lem1283877 _23237 _23238 _23239) (@lem1283540 _23239 _23237 _23238 h1)). Qed.
Lemma lem1283881 (y : nadd) (z : nadd) (_23239 : nadd) (h1 : term17) : term374 y z _23239.
Proof. exact (@lem1283880 y z _23239 h1). Qed.
Lemma lem1283884 (_23239 : nadd) (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term89 x y z) : term26 y z _23239.
Proof. exact (@lem1283881 y z _23239 h1 (@lem1283866 x y z h2)). Qed.
Lemma lem1283885 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term89 x y z) : term26 y z x.
Proof. exact (@lem1283884 x x y z h1 h2). Qed.
Lemma lem1283886 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term89 x y z) : term359 y z x.
Proof. exact (fun h0 : term229 y z x => @lem1283885 x y z h1 h2). Qed.
Lemma lem1283888 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1283889 (y : nadd) (z : nadd) (x : nadd) : (term359 y z x) = (term26 y z x).
Proof. exact (@lem1283888 (term26 y z x)). Qed.
Lemma lem1283890 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term89 x y z) : term26 y z x.
Proof. exact (EQ_MP (@lem1283889 y z x) (@lem1283886 x y z h1 h2)). Qed.
Lemma lem1283916 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1283917 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term289 _23231 _23233 _23232 _23234) = (term288 _23232 _23234 _23231 _23233).
Proof. exact (@lem1283916 (nadd_le _23232 _23234) (term210 _23231 _23233)). Qed.
Lemma lem1283923 (_23233 : nadd) (_23234 : nadd) : (term328 _23233 _23234) = (term328 _23233 _23234).
Proof. exact (eq_refl (term328 _23233 _23234)). Qed.
Lemma lem1283924 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term329 _23231 _23233 _23232 _23234) = (term330 _23232 _23234 _23231 _23233).
Proof. exact (MK_COMB (@lem1283923 _23233 _23234) (@lem1283917 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1283928 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1283929 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term330 _23232 _23234 _23231 _23233) = (term331 _23232 _23234 _23231 _23233).
Proof. exact (@lem1283928 (nadd_le _23232 _23234) (term322 _23233 _23234) (term210 _23231 _23233)). Qed.
Lemma lem1283945 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term329 _23231 _23233 _23232 _23234) = (term331 _23232 _23234 _23231 _23233).
Proof. exact (TRANS (@lem1283924 _23232 _23234 _23231 _23233) (@lem1283929 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1283946 (_23231 : nadd) (_23232 : nadd) : (term328 _23231 _23232) = (term328 _23231 _23232).
Proof. exact (eq_refl (term328 _23231 _23232)). Qed.
Lemma lem1283947 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term321 _23231 _23233 _23232 _23234) = (term332 _23232 _23234 _23231 _23233).
Proof. exact (MK_COMB (@lem1283946 _23231 _23232) (@lem1283945 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1283951 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1283952 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term332 _23232 _23234 _23231 _23233) = (term333 _23232 _23234 _23231 _23233).
Proof. exact (@lem1283951 (nadd_le _23232 _23234) (term322 _23231 _23232) (term334 _23234 _23231 _23233)). Qed.
Lemma lem1283978 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term321 _23231 _23233 _23232 _23234) = (term333 _23232 _23234 _23231 _23233).
Proof. exact (TRANS (@lem1283947 _23232 _23234 _23231 _23233) (@lem1283952 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1283979 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1283980 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term335 _23231 _23233 _23232 _23234) = (term336 _23232 _23234 _23231 _23233).
Proof. exact (MK_COMB (@lem1283979) (@lem1283978 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284006 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term333 _23232 _23234 _23231 _23233) = (term333 _23232 _23234 _23231 _23233).
Proof. exact (eq_refl (term333 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284007 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : ((term321 _23231 _23233 _23232 _23234) = (term333 _23232 _23234 _23231 _23233)) = ((term333 _23232 _23234 _23231 _23233) = (term333 _23232 _23234 _23231 _23233)).
Proof. exact (MK_COMB (@lem1283980 _23232 _23234 _23231 _23233) (@lem1284006 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284009 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1284010 (x : Prop) : (x = x) = True.
Proof. exact (@lem1284009 Prop x). Qed.
Lemma lem1284011 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : ((term333 _23232 _23234 _23231 _23233) = (term333 _23232 _23234 _23231 _23233)) = True.
Proof. exact (@lem1284010 (term333 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284012 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : ((term321 _23231 _23233 _23232 _23234) = (term333 _23232 _23234 _23231 _23233)) = True.
Proof. exact (TRANS (@lem1284007 _23232 _23234 _23231 _23233) (@lem1284011 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284013 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : True = ((term321 _23231 _23233 _23232 _23234) = (term333 _23232 _23234 _23231 _23233)).
Proof. exact (SYM (@lem1284012 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284014 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term321 _23231 _23233 _23232 _23234) = (term333 _23232 _23234 _23231 _23233).
Proof. exact (EQ_MP (@lem1284013 _23232 _23234 _23231 _23233) (@lem0)). Qed.
Lemma lem1284015 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) (h1 : term45) : term333 _23232 _23234 _23231 _23233.
Proof. exact (EQ_MP (@lem1284014 _23232 _23234 _23231 _23233) (@lem1283582 _23231 _23233 _23232 _23234 h1)). Qed.
Lemma lem1284017 (b : Prop) (a : Prop) : (a \/ b) = (term337 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1284018 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) : (term333 _23232 _23234 _23231 _23233) = (term338 _23231 _23233 _23232 _23234).
Proof. exact (@lem1284017 (term339 _23232 _23234 _23231 _23233) (nadd_le _23232 _23234)). Qed.
Lemma lem1284020 (a : Prop) (b : Prop) : (term340 a b) = (term341 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1284021 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term342 _23232 _23234 _23231 _23233) = (term343 _23232 _23234 _23231 _23233).
Proof. exact (@lem1284020 (term322 _23231 _23232) (term334 _23234 _23231 _23233)). Qed.
Lemma lem1284023 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1284024 (_23231 : nadd) (_23232 : nadd) : (term345 _23231 _23232) = (nadd_eq _23231 _23232).
Proof. exact (@lem1284023 (nadd_eq _23231 _23232)). Qed.
Lemma lem1284025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1284026 (_23231 : nadd) (_23232 : nadd) : (term346 _23231 _23232) = (term347 _23231 _23232).
Proof. exact (MK_COMB (@lem1284025) (@lem1284024 _23231 _23232)). Qed.
Lemma lem1284028 (a : Prop) (b : Prop) : (term340 a b) = (term341 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1284029 (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term348 _23234 _23231 _23233) = (term349 _23234 _23231 _23233).
Proof. exact (@lem1284028 (term322 _23233 _23234) (term210 _23231 _23233)). Qed.
Lemma lem1284031 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1284032 (_23233 : nadd) (_23234 : nadd) : (term345 _23233 _23234) = (nadd_eq _23233 _23234).
Proof. exact (@lem1284031 (nadd_eq _23233 _23234)). Qed.
Lemma lem1284033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1284034 (_23233 : nadd) (_23234 : nadd) : (term346 _23233 _23234) = (term347 _23233 _23234).
Proof. exact (MK_COMB (@lem1284033) (@lem1284032 _23233 _23234)). Qed.
Lemma lem1284036 (a : Prop) : (term344 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1284037 (_23231 : nadd) (_23233 : nadd) : (term350 _23231 _23233) = (nadd_le _23231 _23233).
Proof. exact (@lem1284036 (nadd_le _23231 _23233)). Qed.
Lemma lem1284038 (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term349 _23234 _23231 _23233) = (term351 _23234 _23231 _23233).
Proof. exact (MK_COMB (@lem1284034 _23233 _23234) (@lem1284037 _23231 _23233)). Qed.
Lemma lem1284039 (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term348 _23234 _23231 _23233) = (term351 _23234 _23231 _23233).
Proof. exact (TRANS (@lem1284029 _23234 _23231 _23233) (@lem1284038 _23234 _23231 _23233)). Qed.
Lemma lem1284040 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term343 _23232 _23234 _23231 _23233) = (term352 _23232 _23234 _23231 _23233).
Proof. exact (MK_COMB (@lem1284026 _23231 _23232) (@lem1284039 _23234 _23231 _23233)). Qed.
Lemma lem1284041 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term342 _23232 _23234 _23231 _23233) = (term352 _23232 _23234 _23231 _23233).
Proof. exact (TRANS (@lem1284021 _23232 _23234 _23231 _23233) (@lem1284040 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284042 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1284043 (_23232 : nadd) (_23234 : nadd) (_23231 : nadd) (_23233 : nadd) : (term353 _23232 _23234 _23231 _23233) = (term354 _23232 _23234 _23231 _23233).
Proof. exact (MK_COMB (@lem1284042) (@lem1284041 _23232 _23234 _23231 _23233)). Qed.
Lemma lem1284044 (_23232 : nadd) (_23234 : nadd) : (nadd_le _23232 _23234) = (nadd_le _23232 _23234).
Proof. exact (eq_refl (nadd_le _23232 _23234)). Qed.
Lemma lem1284045 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) : (term338 _23231 _23233 _23232 _23234) = (term355 _23231 _23233 _23232 _23234).
Proof. exact (MK_COMB (@lem1284043 _23232 _23234 _23231 _23233) (@lem1284044 _23232 _23234)). Qed.
Lemma lem1284046 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) : (term333 _23232 _23234 _23231 _23233) = (term355 _23231 _23233 _23232 _23234).
Proof. exact (TRANS (@lem1284018 _23231 _23233 _23232 _23234) (@lem1284045 _23231 _23233 _23232 _23234)). Qed.
Lemma lem1284048 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term36) (h3 : term89 x y z) : term375 y z x.
Proof. exact (conj (@lem1283859 x z h2) (@lem1283890 x y z h1 h3)). Qed.
Lemma lem1284049 (x : nadd) (y : nadd) (z : nadd) (h1 : term17) (h2 : term36) (h3 : term89 x y z) : term376 y z x.
Proof. exact (conj (@lem1283851 x y h2) (@lem1284048 x y z h1 h2 h3)). Qed.
Lemma lem1284051 (_23231 : nadd) (_23233 : nadd) (_23232 : nadd) (_23234 : nadd) (h1 : term45) : term355 _23231 _23233 _23232 _23234.
Proof. exact (EQ_MP (@lem1284046 _23231 _23233 _23232 _23234) (@lem1284015 _23232 _23234 _23231 _23233 h1)). Qed.
Lemma lem1284052 (y : nadd) (x : nadd) (z : nadd) (h1 : term45) : term377 y x z.
Proof. exact (@lem1284051 (nadd_add y x) (nadd_add z x) (nadd_add x y) (nadd_add x z) h1). Qed.
Lemma lem1284055 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : term46 y x z.
Proof. exact (@lem1284052 y x z h1 (@lem1284049 x y z h2 h3 h4)). Qed.
Lemma lem1284056 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : term327 y x z.
Proof. exact (fun h0 : term323 y x z => @lem1284055 x y z h1 h2 h3 h4). Qed.
Lemma lem1284058 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1284059 (y : nadd) (x : nadd) (z : nadd) : (term327 y x z) = (term46 y x z).
Proof. exact (@lem1284058 (term46 y x z)). Qed.
Lemma lem1284060 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : term46 y x z.
Proof. exact (EQ_MP (@lem1284059 y x z) (@lem1284056 x y z h1 h2 h3 h4)). Qed.
Lemma lem1284063 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1284065 (y : nadd) (x : nadd) (z : nadd) : (term323 y x z) = (term378 y x z).
Proof. exact (@lem1284063 (term46 y x z)). Qed.
Lemma lem1284068 (x : nadd) (y : nadd) (z : nadd) (h1 : term89 x y z) : term378 y x z.
Proof. exact (EQ_MP (@lem1284065 y x z) (@lem1283548 x y z h1)). Qed.
Lemma lem1284071 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : False.
Proof. exact (@lem1284068 x y z h4 (@lem1284060 x y z h1 h2 h3 h4)). Qed.
Lemma lem1284072 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : term370.
Proof. exact (fun h0 : ~ False => @lem1284071 x y z h1 h2 h3 h4). Qed.
Lemma lem1284074 (p : Prop) : (term326 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1284075 : term370 = False.
Proof. exact (@lem1284074 False). Qed.
Lemma lem1284076 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : False.
Proof. exact (EQ_MP (@lem1284075) (@lem1284072 x y z h1 h2 h3 h4)). Qed.
Lemma lem1284077 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : term36 = False.
Proof. exact (prop_ext (fun h5 : term36 => @lem1284076 x y z h1 h2 h3 h4) (fun h5 : False => @lem1283302 h3)). Qed.
Lemma lem1284078 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term89 x y z) : False.
Proof. exact (EQ_MP (@lem1284077 x y z h1 h2 h3 h4) (@lem1283302 h3)). Qed.
Lemma lem1284079 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : term36 = False.
Proof. exact (prop_ext (fun h5 : term36 => @lem1283843 x y z h1 h2 h3 h4) (fun h5 : False => @lem1283138 h3)). Qed.
Lemma lem1284080 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term85 x y z) : False.
Proof. exact (EQ_MP (@lem1284079 x y z h1 h2 h3 h4) (@lem1283138 h3)). Qed.
Lemma lem1284081 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term53 x y z) : False.
Proof. exact (or_elim (@lem1283070 x y z h4) (fun h0 : term85 x y z => @lem1284080 x y z h1 h2 h3 h0) (fun h0 : term89 x y z => @lem1284078 x y z h1 h2 h3 h0)). Qed.
Lemma lem1284082 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term53 x y z) : (term53 x y z) = False.
Proof. exact (prop_ext (fun h5 : term53 x y z => @lem1284081 x y z h1 h2 h3 h4) (fun h5 : False => @lem1283070 x y z h4)). Qed.
Lemma lem1284083 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term53 x y z) : False.
Proof. exact (EQ_MP (@lem1284082 x y z h1 h2 h3 h4) (@lem1283070 x y z h4)). Qed.
Lemma lem1284084 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term53 x y z) : term36 = False.
Proof. exact (prop_ext (fun h5 : term36 => @lem1284083 x y z h1 h2 h3 h4) (fun h5 : False => @lem1282952 h3)). Qed.
Lemma lem1284085 (x : nadd) (y : nadd) (z : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term53 x y z) : False.
Proof. exact (EQ_MP (@lem1284084 x y z h1 h2 h3 h4) (@lem1282952 h3)). Qed.
Lemma lem1284086 (x : nadd) (y : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term62 x y) : False.
Proof. exact (ex_elim (@lem1282865 x y h4) (fun z : nadd => fun h0 : term61 x y z => @lem1284085 x y z h1 h2 h3 h0)). Qed.
Lemma lem1284087 (x : nadd) (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term69 x) : False.
Proof. exact (ex_elim (@lem1282864 x h4) (fun y : nadd => fun h0 : term68 x y => @lem1284086 x y h1 h2 h3 h0)). Qed.
Lemma lem1284088 (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term10) : False.
Proof. exact (ex_elim (@lem1282298 h4) (fun x : nadd => fun h0 : term74 x => @lem1284087 x h1 h2 h3 h0)). Qed.
Lemma lem1284089 (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term10) : term36 = False.
Proof. exact (prop_ext (fun h5 : term36 => @lem1284088 h1 h2 h3 h4) (fun h5 : False => @lem1282422 h3)). Qed.
Lemma lem1284090 (h1 : term45) (h2 : term17) (h3 : term36) (h4 : term10) : False.
Proof. exact (EQ_MP (@lem1284089 h1 h2 h3 h4) (@lem1282422 h3)). Qed.
Lemma lem1284091 (h1 : term45) (h2 : term36) (h3 : term10) : term15.
Proof. exact (fun h0 : term17 => @lem1284090 h1 h0 h2 h3). Qed.
Lemma lem1284092 : term15 = term16.
Proof. exact (@lem69 term17). Qed.
Lemma lem1284093 (h1 : term45) (h2 : term36) (h3 : term10) : term16.
Proof. exact (EQ_MP (@lem1284092) (@lem1284091 h1 h2 h3)). Qed.
Lemma lem1284094 (h1 : term45) (h2 : term10) : term20.
Proof. exact (fun h0 : term36 => @lem1284093 h1 h0 h2). Qed.
Lemma lem1284095 (h1 : term10) : term23.
Proof. exact (fun h0 : term45 => @lem1284094 h0 h1). Qed.
Lemma lem1284096 : term25.
Proof. exact (fun h0 : term10 => @lem1284095 h0). Qed.
Lemma lem1284097 : term11.
Proof. exact (EQ_MP (@lem1281748) (@lem1284096)). Qed.
Lemma lem1284099 : term11.
Proof. exact (@lem1281512 (@lem1284097)). Qed.
Lemma lem1284100 (h1 : term10) : term22.
Proof. exact (@lem1284099 (@lem1281497 h1)). Qed.
Lemma lem1284101 (h1 : term10) : term19.
Proof. exact (@lem1284100 h1 (@lem1270569)). Qed.
Lemma lem1284102 (h1 : term10) : term15.
Proof. exact (@lem1284101 h1 (@lem1274476)). Qed.
Lemma lem1284103 (h1 : term10) : False.
Proof. exact (@lem1284102 h1 (@lem1281482)). Qed.
Lemma lem1284104 (h1 : term10) : term10 = False.
Proof. exact (prop_ext (fun h2 : term10 => @lem1284103 h1) (fun h2 : False => @lem1281497 h1)). Qed.
Lemma lem1284105 (h1 : term10) : False.
Proof. exact (EQ_MP (@lem1284104 h1) (@lem1281497 h1)). Qed.
Lemma lem1284106 : term9.
Proof. exact (fun h0 : term10 => @lem1284105 h0). Qed.
Lemma lem1284107 : term8.
Proof. exact (EQ_MP (@lem1281496) (@lem1284106)). Qed.
