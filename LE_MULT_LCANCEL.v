Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LE_MULT_LCANCEL_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_CLAUSES_spec.
Require Import LE_0_spec.
Require Import LE_ADD_LCANCEL_spec.
Require Import LE_REFL_spec.
Require Import LE_SUC_spec.
Require Import MULT_CLAUSES_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Lemma lem102615 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem102617 : term1.
Proof. exact (proj2 (@lem102615)). Qed.
Lemma lem102619 : term2.
Proof. exact (proj2 (@lem102617)). Qed.
Lemma lem102621 : term3.
Proof. exact (proj2 (@lem102619)). Qed.
Lemma lem102624 : term4.
Proof. exact (proj1 (@lem102621)). Qed.
Lemma lem102627 (m : nat) (n : nat) (h1 : (term5 m n) = (term6 m n)) : (term5 m n) = (term6 m n).
Proof. exact (h1). Qed.
Lemma lem102628 (m : nat) (n : nat) (h1 : (term5 m n) = (term6 m n)) : (term6 m n) = (term5 m n).
Proof. exact (SYM (@lem102627 m n h1)). Qed.
Lemma lem102629 (m : nat) (n : nat) (h1 : (term6 m n) = (term5 m n)) : (term6 m n) = (term5 m n).
Proof. exact (h1). Qed.
Lemma lem102630 (m : nat) (n : nat) (h1 : (term6 m n) = (term5 m n)) : (term5 m n) = (term6 m n).
Proof. exact (SYM (@lem102629 m n h1)). Qed.
Lemma lem102631 (m : nat) (n : nat) : ((term5 m n) = (term6 m n)) = ((term6 m n) = (term5 m n)).
Proof. exact (prop_ext (fun h1 : (term5 m n) = (term6 m n) => @lem102628 m n h1) (fun h1 : (term6 m n) = (term5 m n) => @lem102630 m n h1)). Qed.
Lemma lem102632 (m : nat) : (term7 m) = (term8 m).
Proof. exact (fun_ext (fun n : nat => @lem102631 m n)). Qed.
Lemma lem102633 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102634 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem102633) (@lem102632 m)). Qed.
Lemma lem102635 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem102634 m)). Qed.
Lemma lem102636 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102637 : term4 = term13.
Proof. exact (MK_COMB (@lem102636) (@lem102635)). Qed.
Lemma lem102638 : term13.
Proof. exact (EQ_MP (@lem102637) (@lem102624)). Qed.
Lemma lem102642 (m : nat) (n : nat) (p : nat) (h1 : (term14 m n p) = (term15 m n p)) : (term14 m n p) = (term15 m n p).
Proof. exact (h1). Qed.
Lemma lem102643 (m : nat) (n : nat) (p : nat) (h1 : (term14 m n p) = (term15 m n p)) : (term15 m n p) = (term14 m n p).
Proof. exact (SYM (@lem102642 m n p h1)). Qed.
Lemma lem102644 (m : nat) (n : nat) (p : nat) (h1 : (term15 m n p) = (term14 m n p)) : (term15 m n p) = (term14 m n p).
Proof. exact (h1). Qed.
Lemma lem102645 (m : nat) (n : nat) (p : nat) (h1 : (term15 m n p) = (term14 m n p)) : (term14 m n p) = (term15 m n p).
Proof. exact (SYM (@lem102644 m n p h1)). Qed.
Lemma lem102646 (m : nat) (n : nat) (p : nat) : ((term14 m n p) = (term15 m n p)) = ((term15 m n p) = (term14 m n p)).
Proof. exact (prop_ext (fun h1 : (term14 m n p) = (term15 m n p) => @lem102643 m n p h1) (fun h1 : (term15 m n p) = (term14 m n p) => @lem102645 m n p h1)). Qed.
Lemma lem102647 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (fun_ext (fun p : nat => @lem102646 m n p)). Qed.
Lemma lem102648 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102649 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (MK_COMB (@lem102648) (@lem102647 m n)). Qed.
Lemma lem102650 (m : nat) : (term20 m) = (term21 m).
Proof. exact (fun_ext (fun n : nat => @lem102649 m n)). Qed.
Lemma lem102651 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102652 (m : nat) : (term22 m) = (term23 m).
Proof. exact (MK_COMB (@lem102651) (@lem102650 m)). Qed.
Lemma lem102653 : term24 = term25.
Proof. exact (fun_ext (fun m : nat => @lem102652 m)). Qed.
Lemma lem102654 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102655 : term26 = term27.
Proof. exact (MK_COMB (@lem102654) (@lem102653)). Qed.
Lemma lem102656 : term27.
Proof. exact (EQ_MP (@lem102655) (@lem77960)). Qed.
Lemma lem102657 (m : nat) : term28 m.
Proof. exact (@lem102656 m). Qed.
Lemma lem102658 (m : nat) : (term28 m) = (term23 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem102659 (m : nat) : term23 m.
Proof. exact (EQ_MP (@lem102658 m) (@lem102657 m)). Qed.
Lemma lem102660 (m : nat) (n : nat) : term29 m n.
Proof. exact (@lem102659 m n). Qed.
Lemma lem102661 (m : nat) (n : nat) : (term29 m n) = (term19 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem102662 (m : nat) (n : nat) : term19 m n.
Proof. exact (EQ_MP (@lem102661 m n) (@lem102660 m n)). Qed.
Lemma lem102663 (m : nat) (n : nat) (p : nat) : term30 m n p.
Proof. exact (@lem102662 m n p). Qed.
Lemma lem102664 (m : nat) (n : nat) (p : nat) : (term30 m n p) = ((term15 m n p) = (term14 m n p)).
Proof. exact (eq_refl (term30 m n p)). Qed.
Lemma lem102666 (m : nat) : term31 m.
Proof. exact (@lem100902 m). Qed.
Lemma lem102667 (m : nat) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem102668 (m : nat) : term32 m.
Proof. exact (EQ_MP (@lem102667 m) (@lem102666 m)). Qed.
Lemma lem102669 (m : nat) (n : nat) : term33 m n.
Proof. exact (@lem102668 m n). Qed.
Lemma lem102670 (m : nat) (n : nat) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem102671 (m : nat) (n : nat) : term34 m n.
Proof. exact (EQ_MP (@lem102670 m n) (@lem102669 m n)). Qed.
Lemma lem102672 (m : nat) (n : nat) (p : nat) : term35 m n p.
Proof. exact (@lem102671 m n p). Qed.
Lemma lem102673 (m : nat) (n : nat) (p : nat) : (term35 m n p) = ((term36 n m p) = (Peano.le n p)).
Proof. exact (eq_refl (term35 m n p)). Qed.
Lemma lem102682 : term37.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem102683 (m : nat) : term38 m.
Proof. exact (@lem102682 m). Qed.
Lemma lem102684 (m : nat) : (term38 m) = ((term39 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem102686 (m : nat) : term40 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem102687 (m : nat) : (term40 m) = (term41 m).
Proof. exact (eq_refl (term40 m)). Qed.
Lemma lem102688 (m : nat) : term41 m.
Proof. exact (EQ_MP (@lem102687 m) (@lem102686 m)). Qed.
Lemma lem102689 (m : nat) (n : nat) : term42 m n.
Proof. exact (@lem102688 m n). Qed.
Lemma lem102690 (m : nat) (n : nat) : (term42 m n) = ((term43 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term42 m n)). Qed.
Lemma lem102693 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102694 : term45.
Proof. exact (@lem102693 term46). Qed.
Lemma lem102695 : term47 = term48.
Proof. exact (eq_refl term47). Qed.
Lemma lem102696 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102697 : term49 = term50.
Proof. exact (MK_COMB (@lem102696) (@lem102695)). Qed.
Lemma lem102698 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem102699 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102700 (m : nat) : (term53 m) = (term54 m).
Proof. exact (MK_COMB (@lem102699) (@lem102698 m)). Qed.
Lemma lem102701 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem102702 (m : nat) : (term57 m) = (term58 m).
Proof. exact (MK_COMB (@lem102700 m) (@lem102701 m)). Qed.
Lemma lem102703 : term59 = term60.
Proof. exact (fun_ext (fun m : nat => @lem102702 m)). Qed.
Lemma lem102704 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102705 : term61 = term62.
Proof. exact (MK_COMB (@lem102704) (@lem102703)). Qed.
Lemma lem102706 : term63 = term64.
Proof. exact (MK_COMB (@lem102697) (@lem102705)). Qed.
Lemma lem102707 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102708 : term65 = term66.
Proof. exact (MK_COMB (@lem102707) (@lem102706)). Qed.
Lemma lem102709 (m : nat) : (term51 m) = (term52 m).
Proof. exact (eq_refl (term51 m)). Qed.
Lemma lem102710 : term67 = term46.
Proof. exact (fun_ext (fun m : nat => @lem102709 m)). Qed.
Lemma lem102711 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102712 : term68 = term69.
Proof. exact (MK_COMB (@lem102711) (@lem102710)). Qed.
Lemma lem102713 : term45 = term70.
Proof. exact (MK_COMB (@lem102708) (@lem102712)). Qed.
Lemma lem102714 : term70.
Proof. exact (EQ_MP (@lem102713) (@lem102694)). Qed.
Lemma lem102717 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102718 : term71.
Proof. exact (@lem102717 term72). Qed.
Lemma lem102719 : term73 = term74.
Proof. exact (eq_refl term73). Qed.
Lemma lem102720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102721 : term75 = term76.
Proof. exact (MK_COMB (@lem102720) (@lem102719)). Qed.
Lemma lem102722 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem102723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102724 (n : nat) : (term79 n) = (term80 n).
Proof. exact (MK_COMB (@lem102723) (@lem102722 n)). Qed.
Lemma lem102725 (n : nat) : (term81 n) = (term82 n).
Proof. exact (eq_refl (term81 n)). Qed.
Lemma lem102726 (n : nat) : (term83 n) = (term84 n).
Proof. exact (MK_COMB (@lem102724 n) (@lem102725 n)). Qed.
Lemma lem102727 : term85 = term86.
Proof. exact (fun_ext (fun n : nat => @lem102726 n)). Qed.
Lemma lem102728 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102729 : term87 = term88.
Proof. exact (MK_COMB (@lem102728) (@lem102727)). Qed.
Lemma lem102730 : term89 = term90.
Proof. exact (MK_COMB (@lem102721) (@lem102729)). Qed.
Lemma lem102731 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102732 : term91 = term92.
Proof. exact (MK_COMB (@lem102731) (@lem102730)). Qed.
Lemma lem102733 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem102734 : term93 = term72.
Proof. exact (fun_ext (fun n : nat => @lem102733 n)). Qed.
Lemma lem102735 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102736 : term94 = term48.
Proof. exact (MK_COMB (@lem102735) (@lem102734)). Qed.
Lemma lem102737 : term71 = term95.
Proof. exact (MK_COMB (@lem102732) (@lem102736)). Qed.
Lemma lem102738 : term95.
Proof. exact (EQ_MP (@lem102737) (@lem102718)). Qed.
Lemma lem102741 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102742 : term96.
Proof. exact (@lem102741 term97). Qed.
Lemma lem102743 : term98 = (term99 = term100).
Proof. exact (eq_refl term98). Qed.
Lemma lem102744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102745 : term101 = term102.
Proof. exact (MK_COMB (@lem102744) (@lem102743)). Qed.
Lemma lem102746 (p : nat) : (term103 p) = ((term104 p) = (term105 p)).
Proof. exact (eq_refl (term103 p)). Qed.
Lemma lem102747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102748 (p : nat) : (term106 p) = (term107 p).
Proof. exact (MK_COMB (@lem102747) (@lem102746 p)). Qed.
Lemma lem102749 (p : nat) : (term108 p) = ((term109 p) = (term110 p)).
Proof. exact (eq_refl (term108 p)). Qed.
Lemma lem102750 (p : nat) : (term111 p) = (term112 p).
Proof. exact (MK_COMB (@lem102748 p) (@lem102749 p)). Qed.
Lemma lem102751 : term113 = term114.
Proof. exact (fun_ext (fun p : nat => @lem102750 p)). Qed.
Lemma lem102752 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102753 : term115 = term116.
Proof. exact (MK_COMB (@lem102752) (@lem102751)). Qed.
Lemma lem102754 : term117 = term118.
Proof. exact (MK_COMB (@lem102745) (@lem102753)). Qed.
Lemma lem102755 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102756 : term119 = term120.
Proof. exact (MK_COMB (@lem102755) (@lem102754)). Qed.
Lemma lem102757 (p : nat) : (term103 p) = ((term104 p) = (term105 p)).
Proof. exact (eq_refl (term103 p)). Qed.
Lemma lem102758 : term121 = term97.
Proof. exact (fun_ext (fun p : nat => @lem102757 p)). Qed.
Lemma lem102759 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102760 : term122 = term74.
Proof. exact (MK_COMB (@lem102759) (@lem102758)). Qed.
Lemma lem102761 : term96 = term123.
Proof. exact (MK_COMB (@lem102756) (@lem102760)). Qed.
Lemma lem102762 : term123.
Proof. exact (EQ_MP (@lem102761) (@lem102742)). Qed.
Lemma lem102769 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102770 (n : nat) : term124 n.
Proof. exact (@lem102769 (term125 n)). Qed.
Lemma lem102771 (n : nat) : (term126 n) = ((term127 n) = (term128 n)).
Proof. exact (eq_refl (term126 n)). Qed.
Lemma lem102772 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102773 (n : nat) : (term129 n) = (term130 n).
Proof. exact (MK_COMB (@lem102772) (@lem102771 n)). Qed.
Lemma lem102774 (n : nat) (p : nat) : (term131 n p) = ((term132 n p) = (term133 n p)).
Proof. exact (eq_refl (term131 n p)). Qed.
Lemma lem102775 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102776 (n : nat) (p : nat) : (term134 n p) = (term135 n p).
Proof. exact (MK_COMB (@lem102775) (@lem102774 n p)). Qed.
Lemma lem102777 (n : nat) (p : nat) : (term136 n p) = ((term137 n p) = (term138 n p)).
Proof. exact (eq_refl (term136 n p)). Qed.
Lemma lem102778 (n : nat) (p : nat) : (term139 n p) = (term140 n p).
Proof. exact (MK_COMB (@lem102776 n p) (@lem102777 n p)). Qed.
Lemma lem102779 (n : nat) : (term141 n) = (term142 n).
Proof. exact (fun_ext (fun p : nat => @lem102778 n p)). Qed.
Lemma lem102780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102781 (n : nat) : (term143 n) = (term144 n).
Proof. exact (MK_COMB (@lem102780) (@lem102779 n)). Qed.
Lemma lem102782 (n : nat) : (term145 n) = (term146 n).
Proof. exact (MK_COMB (@lem102773 n) (@lem102781 n)). Qed.
Lemma lem102783 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102784 (n : nat) : (term147 n) = (term148 n).
Proof. exact (MK_COMB (@lem102783) (@lem102782 n)). Qed.
Lemma lem102785 (n : nat) (p : nat) : (term131 n p) = ((term132 n p) = (term133 n p)).
Proof. exact (eq_refl (term131 n p)). Qed.
Lemma lem102786 (n : nat) : (term149 n) = (term125 n).
Proof. exact (fun_ext (fun p : nat => @lem102785 n p)). Qed.
Lemma lem102787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102788 (n : nat) : (term150 n) = (term82 n).
Proof. exact (MK_COMB (@lem102787) (@lem102786 n)). Qed.
Lemma lem102789 (n : nat) : (term124 n) = (term151 n).
Proof. exact (MK_COMB (@lem102784 n) (@lem102788 n)). Qed.
Lemma lem102790 (n : nat) : term151 n.
Proof. exact (EQ_MP (@lem102789 n) (@lem102770 n)). Qed.
Lemma lem102797 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102798 (m : nat) : term152 m.
Proof. exact (@lem102797 (term153 m)). Qed.
Lemma lem102799 (m : nat) : (term154 m) = (term155 m).
Proof. exact (eq_refl (term154 m)). Qed.
Lemma lem102800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102801 (m : nat) : (term156 m) = (term157 m).
Proof. exact (MK_COMB (@lem102800) (@lem102799 m)). Qed.
Lemma lem102802 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem102803 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102804 (m : nat) (n : nat) : (term160 m n) = (term161 m n).
Proof. exact (MK_COMB (@lem102803) (@lem102802 m n)). Qed.
Lemma lem102805 (m : nat) (n : nat) : (term162 m n) = (term163 m n).
Proof. exact (eq_refl (term162 m n)). Qed.
Lemma lem102806 (m : nat) (n : nat) : (term164 m n) = (term165 m n).
Proof. exact (MK_COMB (@lem102804 m n) (@lem102805 m n)). Qed.
Lemma lem102807 (m : nat) : (term166 m) = (term167 m).
Proof. exact (fun_ext (fun n : nat => @lem102806 m n)). Qed.
Lemma lem102808 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102809 (m : nat) : (term168 m) = (term169 m).
Proof. exact (MK_COMB (@lem102808) (@lem102807 m)). Qed.
Lemma lem102810 (m : nat) : (term170 m) = (term171 m).
Proof. exact (MK_COMB (@lem102801 m) (@lem102809 m)). Qed.
Lemma lem102811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102812 (m : nat) : (term172 m) = (term173 m).
Proof. exact (MK_COMB (@lem102811) (@lem102810 m)). Qed.
Lemma lem102813 (m : nat) (n : nat) : (term158 m n) = (term159 m n).
Proof. exact (eq_refl (term158 m n)). Qed.
Lemma lem102814 (m : nat) : (term174 m) = (term153 m).
Proof. exact (fun_ext (fun n : nat => @lem102813 m n)). Qed.
Lemma lem102815 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102816 (m : nat) : (term175 m) = (term56 m).
Proof. exact (MK_COMB (@lem102815) (@lem102814 m)). Qed.
Lemma lem102817 (m : nat) : (term152 m) = (term176 m).
Proof. exact (MK_COMB (@lem102812 m) (@lem102816 m)). Qed.
Lemma lem102818 (m : nat) : term176 m.
Proof. exact (EQ_MP (@lem102817 m) (@lem102798 m)). Qed.
Lemma lem102819 (m : nat) (n : nat) (h1 : term159 m n) : term159 m n.
Proof. exact (h1). Qed.
Lemma lem102821 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102822 (m : nat) : term177 m.
Proof. exact (@lem102821 (term178 m)). Qed.
Lemma lem102823 (m : nat) : (term179 m) = ((term180 m) = (term181 m)).
Proof. exact (eq_refl (term179 m)). Qed.
Lemma lem102824 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102825 (m : nat) : (term182 m) = (term183 m).
Proof. exact (MK_COMB (@lem102824) (@lem102823 m)). Qed.
Lemma lem102826 (m : nat) (p : nat) : (term184 m p) = ((term185 m p) = (term186 m p)).
Proof. exact (eq_refl (term184 m p)). Qed.
Lemma lem102827 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102828 (m : nat) (p : nat) : (term187 m p) = (term188 m p).
Proof. exact (MK_COMB (@lem102827) (@lem102826 m p)). Qed.
Lemma lem102829 (m : nat) (p : nat) : (term189 m p) = ((term190 m p) = (term191 m p)).
Proof. exact (eq_refl (term189 m p)). Qed.
Lemma lem102830 (m : nat) (p : nat) : (term192 m p) = (term193 m p).
Proof. exact (MK_COMB (@lem102828 m p) (@lem102829 m p)). Qed.
Lemma lem102831 (m : nat) : (term194 m) = (term195 m).
Proof. exact (fun_ext (fun p : nat => @lem102830 m p)). Qed.
Lemma lem102832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102833 (m : nat) : (term196 m) = (term197 m).
Proof. exact (MK_COMB (@lem102832) (@lem102831 m)). Qed.
Lemma lem102834 (m : nat) : (term198 m) = (term199 m).
Proof. exact (MK_COMB (@lem102825 m) (@lem102833 m)). Qed.
Lemma lem102835 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102836 (m : nat) : (term200 m) = (term201 m).
Proof. exact (MK_COMB (@lem102835) (@lem102834 m)). Qed.
Lemma lem102837 (m : nat) (p : nat) : (term184 m p) = ((term185 m p) = (term186 m p)).
Proof. exact (eq_refl (term184 m p)). Qed.
Lemma lem102838 (m : nat) : (term202 m) = (term178 m).
Proof. exact (fun_ext (fun p : nat => @lem102837 m p)). Qed.
Lemma lem102839 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102840 (m : nat) : (term203 m) = (term155 m).
Proof. exact (MK_COMB (@lem102839) (@lem102838 m)). Qed.
Lemma lem102841 (m : nat) : (term177 m) = (term204 m).
Proof. exact (MK_COMB (@lem102836 m) (@lem102840 m)). Qed.
Lemma lem102842 (m : nat) : term204 m.
Proof. exact (EQ_MP (@lem102841 m) (@lem102822 m)). Qed.
Lemma lem102849 (P : nat -> Prop) : term44 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem102850 (m : nat) (n : nat) : term205 m n.
Proof. exact (@lem102849 (term206 m n)). Qed.
Lemma lem102851 (m : nat) (n : nat) : (term207 m n) = ((term208 n m) = (term209 m n)).
Proof. exact (eq_refl (term207 m n)). Qed.
Lemma lem102852 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem102853 (m : nat) (n : nat) : (term210 m n) = (term211 m n).
Proof. exact (MK_COMB (@lem102852) (@lem102851 m n)). Qed.
Lemma lem102854 (m : nat) (n : nat) (p : nat) : (term212 m n p) = ((term213 n m p) = (term214 m n p)).
Proof. exact (eq_refl (term212 m n p)). Qed.
Lemma lem102855 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102856 (m : nat) (n : nat) (p : nat) : (term215 m n p) = (term216 m n p).
Proof. exact (MK_COMB (@lem102855) (@lem102854 m n p)). Qed.
Lemma lem102857 (m : nat) (n : nat) (p : nat) : (term217 m n p) = ((term218 n m p) = (term219 m n p)).
Proof. exact (eq_refl (term217 m n p)). Qed.
Lemma lem102858 (m : nat) (n : nat) (p : nat) : (term220 m n p) = (term221 m n p).
Proof. exact (MK_COMB (@lem102856 m n p) (@lem102857 m n p)). Qed.
Lemma lem102859 (m : nat) (n : nat) : (term222 m n) = (term223 m n).
Proof. exact (fun_ext (fun p : nat => @lem102858 m n p)). Qed.
Lemma lem102860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102861 (m : nat) (n : nat) : (term224 m n) = (term225 m n).
Proof. exact (MK_COMB (@lem102860) (@lem102859 m n)). Qed.
Lemma lem102862 (m : nat) (n : nat) : (term226 m n) = (term227 m n).
Proof. exact (MK_COMB (@lem102853 m n) (@lem102861 m n)). Qed.
Lemma lem102863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem102864 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (MK_COMB (@lem102863) (@lem102862 m n)). Qed.
Lemma lem102865 (m : nat) (n : nat) (p : nat) : (term212 m n p) = ((term213 n m p) = (term214 m n p)).
Proof. exact (eq_refl (term212 m n p)). Qed.
Lemma lem102866 (m : nat) (n : nat) : (term230 m n) = (term206 m n).
Proof. exact (fun_ext (fun p : nat => @lem102865 m n p)). Qed.
Lemma lem102867 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem102868 (m : nat) (n : nat) : (term231 m n) = (term163 m n).
Proof. exact (MK_COMB (@lem102867) (@lem102866 m n)). Qed.
Lemma lem102869 (m : nat) (n : nat) : (term205 m n) = (term232 m n).
Proof. exact (MK_COMB (@lem102864 m n) (@lem102868 m n)). Qed.
Lemma lem102870 (m : nat) (n : nat) : term232 m n.
Proof. exact (EQ_MP (@lem102869 m n) (@lem102850 m n)). Qed.
Lemma lem102892 (n : nat) : term233 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem102893 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem102894 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem102893 n) (@lem102892 n)). Qed.
Lemma lem102895 (n : nat) : (term234 n) = ((term234 n) = True).
Proof. exact (@lem7 (term234 n)). Qed.
Lemma lem102897 (n : nat) : term235 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem102898 (n : nat) : (term235 n) = (Peano.le n n).
Proof. exact (eq_refl (term235 n)). Qed.
Lemma lem102899 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem102898 n) (@lem102897 n)). Qed.
Lemma lem102900 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem102963 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem102900 n) (@lem102899 n)). Qed.
Lemma lem102964 : term99 = True.
Proof. exact (@lem102963 term236). Qed.
Lemma lem102965 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem102966 : term237 = (@eq Prop True).
Proof. exact (MK_COMB (@lem102965) (@lem102964)). Qed.
Lemma lem102970 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem102971 (x : nat) : (x = x) = True.
Proof. exact (@lem102970 nat x). Qed.
Lemma lem102972 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem102971 (NUMERAL 0)). Qed.
Lemma lem102973 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem102974 : term238 = (or True).
Proof. exact (MK_COMB (@lem102973) (@lem102972)). Qed.
Lemma lem102976 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem102895 n) (@lem102894 n)). Qed.
Lemma lem102977 : term239 = True.
Proof. exact (@lem102976 (NUMERAL 0)). Qed.
Lemma lem102978 : term100 = (True \/ True).
Proof. exact (MK_COMB (@lem102974) (@lem102977)). Qed.
Lemma lem102980 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem102981 : (True \/ True) = True.
Proof. exact (@lem102980 True). Qed.
Lemma lem102982 : term100 = True.
Proof. exact (TRANS (@lem102978) (@lem102981)). Qed.
Lemma lem102983 : (term99 = term100) = (True = True).
Proof. exact (MK_COMB (@lem102966) (@lem102982)). Qed.
Lemma lem102985 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem102986 : (True = True) = True.
Proof. exact (@lem102985 True). Qed.
Lemma lem102987 : (term99 = term100) = True.
Proof. exact (TRANS (@lem102983) (@lem102986)). Qed.
Lemma lem102988 : True = (term99 = term100).
Proof. exact (SYM (@lem102987)). Qed.
Lemma lem102989 : term99 = term100.
Proof. exact (EQ_MP (@lem102988) (@lem0)). Qed.
Lemma lem103006 (n : nat) : term233 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem103007 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem103008 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem103007 n) (@lem103006 n)). Qed.
Lemma lem103009 (n : nat) : (term234 n) = ((term234 n) = True).
Proof. exact (@lem7 (term234 n)). Qed.
Lemma lem103070 : term240.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem103071 (n : nat) : term241 n.
Proof. exact (@lem103070 n). Qed.
Lemma lem103072 (n : nat) : (term241 n) = ((term242 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem103079 (n : nat) : (term242 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103072 n) (@lem103071 n)). Qed.
Lemma lem103080 : term236 = (NUMERAL 0).
Proof. exact (@lem103079 (NUMERAL 0)). Qed.
Lemma lem103081 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem103082 : term243 = term244.
Proof. exact (MK_COMB (@lem103081) (@lem103080)). Qed.
Lemma lem103084 (n : nat) : (term242 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103072 n) (@lem103071 n)). Qed.
Lemma lem103085 (p : nat) : (term245 p) = (NUMERAL 0).
Proof. exact (@lem103084 (S p)). Qed.
Lemma lem103086 (p : nat) : (term109 p) = term239.
Proof. exact (MK_COMB (@lem103082) (@lem103085 p)). Qed.
Lemma lem103088 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem103009 n) (@lem103008 n)). Qed.
Lemma lem103089 : term239 = True.
Proof. exact (@lem103088 (NUMERAL 0)). Qed.
Lemma lem103090 (p : nat) : (term109 p) = True.
Proof. exact (TRANS (@lem103086 p) (@lem103089)). Qed.
Lemma lem103091 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103092 (p : nat) : (term246 p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem103091) (@lem103090 p)). Qed.
Lemma lem103096 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem103097 (x : nat) : (x = x) = True.
Proof. exact (@lem103096 nat x). Qed.
Lemma lem103098 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem103097 (NUMERAL 0)). Qed.
Lemma lem103099 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem103100 : term238 = (or True).
Proof. exact (MK_COMB (@lem103099) (@lem103098)). Qed.
Lemma lem103102 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem103009 n) (@lem103008 n)). Qed.
Lemma lem103103 (p : nat) : (term247 p) = True.
Proof. exact (@lem103102 (S p)). Qed.
Lemma lem103104 (p : nat) : (term110 p) = (True \/ True).
Proof. exact (MK_COMB (@lem103100) (@lem103103 p)). Qed.
Lemma lem103106 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem103107 : (True \/ True) = True.
Proof. exact (@lem103106 True). Qed.
Lemma lem103108 (p : nat) : (term110 p) = True.
Proof. exact (TRANS (@lem103104 p) (@lem103107)). Qed.
Lemma lem103109 (p : nat) : ((term109 p) = (term110 p)) = (True = True).
Proof. exact (MK_COMB (@lem103092 p) (@lem103108 p)). Qed.
Lemma lem103111 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem103112 : (True = True) = True.
Proof. exact (@lem103111 True). Qed.
Lemma lem103113 (p : nat) : ((term109 p) = (term110 p)) = True.
Proof. exact (TRANS (@lem103109 p) (@lem103112)). Qed.
Lemma lem103114 (p : nat) : True = ((term109 p) = (term110 p)).
Proof. exact (SYM (@lem103113 p)). Qed.
Lemma lem103115 (p : nat) : (term109 p) = (term110 p).
Proof. exact (EQ_MP (@lem103114 p) (@lem0)). Qed.
Lemma lem103132 (n : nat) : term233 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem103133 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem103134 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem103133 n) (@lem103132 n)). Qed.
Lemma lem103135 (n : nat) : (term234 n) = ((term234 n) = True).
Proof. exact (@lem7 (term234 n)). Qed.
Lemma lem103196 : term240.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem103197 (n : nat) : term241 n.
Proof. exact (@lem103196 n). Qed.
Lemma lem103198 (n : nat) : (term241 n) = ((term242 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem103208 (n : nat) : (term242 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103198 n) (@lem103197 n)). Qed.
Lemma lem103209 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (@lem103208 (S n)). Qed.
Lemma lem103210 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem103211 (n : nat) : (term248 n) = term244.
Proof. exact (MK_COMB (@lem103210) (@lem103209 n)). Qed.
Lemma lem103213 (n : nat) : (term242 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103198 n) (@lem103197 n)). Qed.
Lemma lem103214 : term236 = (NUMERAL 0).
Proof. exact (@lem103213 (NUMERAL 0)). Qed.
Lemma lem103215 (n : nat) : (term127 n) = term239.
Proof. exact (MK_COMB (@lem103211 n) (@lem103214)). Qed.
Lemma lem103217 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem103135 n) (@lem103134 n)). Qed.
Lemma lem103218 : term239 = True.
Proof. exact (@lem103217 (NUMERAL 0)). Qed.
Lemma lem103219 (n : nat) : (term127 n) = True.
Proof. exact (TRANS (@lem103215 n) (@lem103218)). Qed.
Lemma lem103220 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103221 (n : nat) : (term249 n) = (@eq Prop True).
Proof. exact (MK_COMB (@lem103220) (@lem103219 n)). Qed.
Lemma lem103225 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem103226 (x : nat) : (x = x) = True.
Proof. exact (@lem103225 nat x). Qed.
Lemma lem103227 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem103226 (NUMERAL 0)). Qed.
Lemma lem103228 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem103229 : term238 = (or True).
Proof. exact (MK_COMB (@lem103228) (@lem103227)). Qed.
Lemma lem103232 (n : nat) : (term250 n) = (term250 n).
Proof. exact (eq_refl (term250 n)). Qed.
Lemma lem103233 (n : nat) : (term128 n) = (term251 n).
Proof. exact (MK_COMB (@lem103229) (@lem103232 n)). Qed.
Lemma lem103235 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem103236 (n : nat) : (term251 n) = True.
Proof. exact (@lem103235 (term250 n)). Qed.
Lemma lem103237 (n : nat) : (term128 n) = True.
Proof. exact (TRANS (@lem103233 n) (@lem103236 n)). Qed.
Lemma lem103238 (n : nat) : ((term127 n) = (term128 n)) = (True = True).
Proof. exact (MK_COMB (@lem103221 n) (@lem103237 n)). Qed.
Lemma lem103240 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem103241 : (True = True) = True.
Proof. exact (@lem103240 True). Qed.
Lemma lem103242 (n : nat) : ((term127 n) = (term128 n)) = True.
Proof. exact (TRANS (@lem103238 n) (@lem103241)). Qed.
Lemma lem103243 (n : nat) : True = ((term127 n) = (term128 n)).
Proof. exact (SYM (@lem103242 n)). Qed.
Lemma lem103244 (n : nat) : (term127 n) = (term128 n).
Proof. exact (EQ_MP (@lem103243 n) (@lem0)). Qed.
Lemma lem103261 (n : nat) : term233 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem103262 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem103263 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem103262 n) (@lem103261 n)). Qed.
Lemma lem103264 (n : nat) : (term234 n) = ((term234 n) = True).
Proof. exact (@lem7 (term234 n)). Qed.
Lemma lem103325 : term240.
Proof. exact (proj1 (@lem81645)). Qed.
Lemma lem103326 (n : nat) : term241 n.
Proof. exact (@lem103325 n). Qed.
Lemma lem103327 (n : nat) : (term241 n) = ((term242 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term241 n)). Qed.
Lemma lem103337 (n : nat) : (term242 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103327 n) (@lem103326 n)). Qed.
Lemma lem103338 (n : nat) : (term245 n) = (NUMERAL 0).
Proof. exact (@lem103337 (S n)). Qed.
Lemma lem103339 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem103340 (n : nat) : (term248 n) = term244.
Proof. exact (MK_COMB (@lem103339) (@lem103338 n)). Qed.
Lemma lem103342 (n : nat) : (term242 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103327 n) (@lem103326 n)). Qed.
Lemma lem103343 (p : nat) : (term245 p) = (NUMERAL 0).
Proof. exact (@lem103342 (S p)). Qed.
Lemma lem103344 (n : nat) (p : nat) : (term137 n p) = term239.
Proof. exact (MK_COMB (@lem103340 n) (@lem103343 p)). Qed.
Lemma lem103346 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem103264 n) (@lem103263 n)). Qed.
Lemma lem103347 : term239 = True.
Proof. exact (@lem103346 (NUMERAL 0)). Qed.
Lemma lem103348 (n : nat) (p : nat) : (term137 n p) = True.
Proof. exact (TRANS (@lem103344 n p) (@lem103347)). Qed.
Lemma lem103349 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103350 (n : nat) (p : nat) : (term252 n p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem103349) (@lem103348 n p)). Qed.
Lemma lem103354 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem103355 (x : nat) : (x = x) = True.
Proof. exact (@lem103354 nat x). Qed.
Lemma lem103356 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem103355 (NUMERAL 0)). Qed.
Lemma lem103357 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem103358 : term238 = (or True).
Proof. exact (MK_COMB (@lem103357) (@lem103356)). Qed.
Lemma lem103361 (n : nat) (p : nat) : (term43 n p) = (term43 n p).
Proof. exact (eq_refl (term43 n p)). Qed.
Lemma lem103362 (n : nat) (p : nat) : (term138 n p) = (term253 n p).
Proof. exact (MK_COMB (@lem103358) (@lem103361 n p)). Qed.
Lemma lem103364 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem103365 (n : nat) (p : nat) : (term253 n p) = True.
Proof. exact (@lem103364 (term43 n p)). Qed.
Lemma lem103366 (n : nat) (p : nat) : (term138 n p) = True.
Proof. exact (TRANS (@lem103362 n p) (@lem103365 n p)). Qed.
Lemma lem103367 (n : nat) (p : nat) : ((term137 n p) = (term138 n p)) = (True = True).
Proof. exact (MK_COMB (@lem103350 n p) (@lem103366 n p)). Qed.
Lemma lem103369 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem103370 : (True = True) = True.
Proof. exact (@lem103369 True). Qed.
Lemma lem103371 (n : nat) (p : nat) : ((term137 n p) = (term138 n p)) = True.
Proof. exact (TRANS (@lem103367 n p) (@lem103370)). Qed.
Lemma lem103372 (n : nat) (p : nat) : True = ((term137 n p) = (term138 n p)).
Proof. exact (SYM (@lem103371 n p)). Qed.
Lemma lem103373 (n : nat) (p : nat) : (term137 n p) = (term138 n p).
Proof. exact (EQ_MP (@lem103372 n p) (@lem0)). Qed.
Lemma lem103374 (n : nat) : term254 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem103375 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem103376 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem103375 n) (@lem103374 n)). Qed.
Lemma lem103377 (n : nat) : term256 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem103390 (n : nat) : term233 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem103391 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem103392 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem103391 n) (@lem103390 n)). Qed.
Lemma lem103393 (n : nat) : (term234 n) = ((term234 n) = True).
Proof. exact (@lem7 (term234 n)). Qed.
Lemma lem103395 (n : nat) : term235 n.
Proof. exact (@lem91603 n). Qed.
Lemma lem103396 (n : nat) : (term235 n) = (Peano.le n n).
Proof. exact (eq_refl (term235 n)). Qed.
Lemma lem103397 (n : nat) : Peano.le n n.
Proof. exact (EQ_MP (@lem103396 n) (@lem103395 n)). Qed.
Lemma lem103398 (n : nat) : (Peano.le n n) = ((Peano.le n n) = True).
Proof. exact (@lem7 (Peano.le n n)). Qed.
Lemma lem103467 (n : nat) : (Peano.le n n) = True.
Proof. exact (EQ_MP (@lem103398 n) (@lem103397 n)). Qed.
Lemma lem103468 (m : nat) : (term180 m) = True.
Proof. exact (@lem103467 (term257 m)). Qed.
Lemma lem103469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103470 (m : nat) : (term258 m) = (@eq Prop True).
Proof. exact (MK_COMB (@lem103469) (@lem103468 m)). Qed.
Lemma lem103474 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem103377 n (@lem103376 n)). Qed.
Lemma lem103475 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem103474 m). Qed.
Lemma lem103476 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem103477 (m : nat) : (term259 m) = (or False).
Proof. exact (MK_COMB (@lem103476) (@lem103475 m)). Qed.
Lemma lem103479 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem103393 n) (@lem103392 n)). Qed.
Lemma lem103480 : term239 = True.
Proof. exact (@lem103479 (NUMERAL 0)). Qed.
Lemma lem103481 (m : nat) : (term181 m) = (False \/ True).
Proof. exact (MK_COMB (@lem103477 m) (@lem103480)). Qed.
Lemma lem103483 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem103484 : (False \/ True) = True.
Proof. exact (@lem103483 True). Qed.
Lemma lem103485 (m : nat) : (term181 m) = True.
Proof. exact (TRANS (@lem103481 m) (@lem103484)). Qed.
Lemma lem103486 (m : nat) : ((term180 m) = (term181 m)) = (True = True).
Proof. exact (MK_COMB (@lem103470 m) (@lem103485 m)). Qed.
Lemma lem103488 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem103489 : (True = True) = True.
Proof. exact (@lem103488 True). Qed.
Lemma lem103490 (m : nat) : ((term180 m) = (term181 m)) = True.
Proof. exact (TRANS (@lem103486 m) (@lem103489)). Qed.
Lemma lem103491 (m : nat) : True = ((term180 m) = (term181 m)).
Proof. exact (SYM (@lem103490 m)). Qed.
Lemma lem103492 (m : nat) : (term180 m) = (term181 m).
Proof. exact (EQ_MP (@lem103491 m) (@lem0)). Qed.
Lemma lem103493 (n : nat) : term254 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem103494 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem103495 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem103494 n) (@lem103493 n)). Qed.
Lemma lem103496 (n : nat) : term256 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem103509 (n : nat) : term233 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem103510 (n : nat) : (term233 n) = (term234 n).
Proof. exact (eq_refl (term233 n)). Qed.
Lemma lem103511 (n : nat) : term234 n.
Proof. exact (EQ_MP (@lem103510 n) (@lem103509 n)). Qed.
Lemma lem103512 (n : nat) : (term234 n) = ((term234 n) = True).
Proof. exact (@lem7 (term234 n)). Qed.
Lemma lem103519 : term260.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem103520 : term261.
Proof. exact (proj2 (@lem103519)). Qed.
Lemma lem103521 : term262.
Proof. exact (proj2 (@lem103520)). Qed.
Lemma lem103522 (m : nat) : term263 m.
Proof. exact (@lem103521 m). Qed.
Lemma lem103523 (m : nat) : (term263 m) = (term264 m).
Proof. exact (eq_refl (term263 m)). Qed.
Lemma lem103524 (m : nat) : term264 m.
Proof. exact (EQ_MP (@lem103523 m) (@lem103522 m)). Qed.
Lemma lem103525 (m : nat) (n : nat) : term265 m n.
Proof. exact (@lem103524 m n). Qed.
Lemma lem103526 (m : nat) (n : nat) : (term265 m n) = ((term266 m n) = (term267 m n)).
Proof. exact (eq_refl (term265 m n)). Qed.
Lemma lem103535 : term268.
Proof. exact (proj1 (@lem103519)). Qed.
Lemma lem103536 (m : nat) : term269 m.
Proof. exact (@lem103535 m). Qed.
Lemma lem103537 (m : nat) : (term269 m) = ((term270 m) = m).
Proof. exact (eq_refl (term269 m)). Qed.
Lemma lem103543 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem103544 : term1.
Proof. exact (proj2 (@lem103543)). Qed.
Lemma lem103545 : term2.
Proof. exact (proj2 (@lem103544)). Qed.
Lemma lem103546 : term3.
Proof. exact (proj2 (@lem103545)). Qed.
Lemma lem103547 : term271.
Proof. exact (proj2 (@lem103546)). Qed.
Lemma lem103548 (m : nat) : term272 m.
Proof. exact (@lem103547 m). Qed.
Lemma lem103549 (m : nat) : (term272 m) = (term273 m).
Proof. exact (eq_refl (term272 m)). Qed.
Lemma lem103550 (m : nat) : term273 m.
Proof. exact (EQ_MP (@lem103549 m) (@lem103548 m)). Qed.
Lemma lem103551 (m : nat) (n : nat) : term274 m n.
Proof. exact (@lem103550 m n). Qed.
Lemma lem103552 (m : nat) (n : nat) : (term274 m n) = ((term275 m n) = (term276 m n)).
Proof. exact (eq_refl (term274 m n)). Qed.
Lemma lem103554 : term4.
Proof. exact (proj1 (@lem103546)). Qed.
Lemma lem103555 (m : nat) : term277 m.
Proof. exact (@lem103554 m). Qed.
Lemma lem103556 (m : nat) : (term277 m) = (term9 m).
Proof. exact (eq_refl (term277 m)). Qed.
Lemma lem103557 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem103556 m) (@lem103555 m)). Qed.
Lemma lem103558 (m : nat) (n : nat) : term278 m n.
Proof. exact (@lem103557 m n). Qed.
Lemma lem103559 (m : nat) (n : nat) : (term278 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term278 m n)). Qed.
Lemma lem103569 : term279.
Proof. exact (proj1 (@lem103543)). Qed.
Lemma lem103570 (m : nat) : term280 m.
Proof. exact (@lem103569 m). Qed.
Lemma lem103571 (m : nat) : (term280 m) = ((term281 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term280 m)). Qed.
Lemma lem103588 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem103559 m n) (@lem103558 m n)). Qed.
Lemma lem103589 (m : nat) : (term257 m) = (term282 m).
Proof. exact (@lem103588 m (NUMERAL 0)). Qed.
Lemma lem103591 (m : nat) : (term270 m) = m.
Proof. exact (EQ_MP (@lem103537 m) (@lem103536 m)). Qed.
Lemma lem103592 (m : nat) : (term282 m) = (term281 m).
Proof. exact (@lem103591 (term281 m)). Qed.
Lemma lem103594 (m : nat) : (term281 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103571 m) (@lem103570 m)). Qed.
Lemma lem103595 (m : nat) : (term282 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem103592 m) (@lem103594 m)). Qed.
Lemma lem103596 (m : nat) : (term257 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem103589 m) (@lem103595 m)). Qed.
Lemma lem103597 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem103598 (m : nat) : (term283 m) = term244.
Proof. exact (MK_COMB (@lem103597) (@lem103596 m)). Qed.
Lemma lem103600 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem103559 m n) (@lem103558 m n)). Qed.
Lemma lem103601 (m : nat) (p : nat) : (term284 m p) = (term285 m p).
Proof. exact (@lem103600 m (S p)). Qed.
Lemma lem103603 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (EQ_MP (@lem103526 m n) (@lem103525 m n)). Qed.
Lemma lem103604 (m : nat) (p : nat) : (term285 m p) = (term286 m p).
Proof. exact (@lem103603 (term275 m p) p). Qed.
Lemma lem103605 (m : nat) (p : nat) : (term284 m p) = (term286 m p).
Proof. exact (TRANS (@lem103601 m p) (@lem103604 m p)). Qed.
Lemma lem103607 (m : nat) (n : nat) : (term275 m n) = (term276 m n).
Proof. exact (EQ_MP (@lem103552 m n) (@lem103551 m n)). Qed.
Lemma lem103608 (m : nat) (p : nat) : (term275 m p) = (term276 m p).
Proof. exact (@lem103607 m p). Qed.
Lemma lem103609 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem103610 (m : nat) (p : nat) : (term287 m p) = (term288 m p).
Proof. exact (MK_COMB (@lem103609) (@lem103608 m p)). Qed.
Lemma lem103611 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem103612 (m : nat) (p : nat) : (term289 m p) = (term290 m p).
Proof. exact (MK_COMB (@lem103610 m p) (@lem103611 p)). Qed.
Lemma lem103613 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem103614 (m : nat) (p : nat) : (term286 m p) = (term291 m p).
Proof. exact (MK_COMB (@lem103613) (@lem103612 m p)). Qed.
Lemma lem103615 (m : nat) (p : nat) : (term284 m p) = (term291 m p).
Proof. exact (TRANS (@lem103605 m p) (@lem103614 m p)). Qed.
Lemma lem103616 (m : nat) (p : nat) : (term190 m p) = (term292 m p).
Proof. exact (MK_COMB (@lem103598 m) (@lem103615 m p)). Qed.
Lemma lem103618 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem103512 n) (@lem103511 n)). Qed.
Lemma lem103619 (m : nat) (p : nat) : (term292 m p) = True.
Proof. exact (@lem103618 (term291 m p)). Qed.
Lemma lem103620 (m : nat) (p : nat) : (term190 m p) = True.
Proof. exact (TRANS (@lem103616 m p) (@lem103619 m p)). Qed.
Lemma lem103621 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103622 (m : nat) (p : nat) : (term293 m p) = (@eq Prop True).
Proof. exact (MK_COMB (@lem103621) (@lem103620 m p)). Qed.
Lemma lem103626 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem103496 n (@lem103495 n)). Qed.
Lemma lem103627 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem103626 m). Qed.
Lemma lem103628 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem103629 (m : nat) : (term259 m) = (or False).
Proof. exact (MK_COMB (@lem103628) (@lem103627 m)). Qed.
Lemma lem103631 (n : nat) : (term234 n) = True.
Proof. exact (EQ_MP (@lem103512 n) (@lem103511 n)). Qed.
Lemma lem103632 (p : nat) : (term247 p) = True.
Proof. exact (@lem103631 (S p)). Qed.
Lemma lem103633 (m : nat) (p : nat) : (term191 m p) = (False \/ True).
Proof. exact (MK_COMB (@lem103629 m) (@lem103632 p)). Qed.
Lemma lem103635 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem103636 : (False \/ True) = True.
Proof. exact (@lem103635 True). Qed.
Lemma lem103637 (m : nat) (p : nat) : (term191 m p) = True.
Proof. exact (TRANS (@lem103633 m p) (@lem103636)). Qed.
Lemma lem103638 (m : nat) (p : nat) : ((term190 m p) = (term191 m p)) = (True = True).
Proof. exact (MK_COMB (@lem103622 m p) (@lem103637 m p)). Qed.
Lemma lem103640 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem103641 : (True = True) = True.
Proof. exact (@lem103640 True). Qed.
Lemma lem103642 (m : nat) (p : nat) : ((term190 m p) = (term191 m p)) = True.
Proof. exact (TRANS (@lem103638 m p) (@lem103641)). Qed.
Lemma lem103643 (m : nat) (p : nat) : True = ((term190 m p) = (term191 m p)).
Proof. exact (SYM (@lem103642 m p)). Qed.
Lemma lem103644 (m : nat) (p : nat) : (term190 m p) = (term191 m p).
Proof. exact (EQ_MP (@lem103643 m p) (@lem0)). Qed.
Lemma lem103645 (n : nat) : term254 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem103646 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem103647 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem103646 n) (@lem103645 n)). Qed.
Lemma lem103648 (n : nat) : term256 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem103671 : term260.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem103672 : term261.
Proof. exact (proj2 (@lem103671)). Qed.
Lemma lem103673 : term262.
Proof. exact (proj2 (@lem103672)). Qed.
Lemma lem103674 (m : nat) : term263 m.
Proof. exact (@lem103673 m). Qed.
Lemma lem103675 (m : nat) : (term263 m) = (term264 m).
Proof. exact (eq_refl (term263 m)). Qed.
Lemma lem103676 (m : nat) : term264 m.
Proof. exact (EQ_MP (@lem103675 m) (@lem103674 m)). Qed.
Lemma lem103677 (m : nat) (n : nat) : term265 m n.
Proof. exact (@lem103676 m n). Qed.
Lemma lem103678 (m : nat) (n : nat) : (term265 m n) = ((term266 m n) = (term267 m n)).
Proof. exact (eq_refl (term265 m n)). Qed.
Lemma lem103687 : term268.
Proof. exact (proj1 (@lem103671)). Qed.
Lemma lem103688 (m : nat) : term269 m.
Proof. exact (@lem103687 m). Qed.
Lemma lem103689 (m : nat) : (term269 m) = ((term270 m) = m).
Proof. exact (eq_refl (term269 m)). Qed.
Lemma lem103695 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem103696 : term1.
Proof. exact (proj2 (@lem103695)). Qed.
Lemma lem103697 : term2.
Proof. exact (proj2 (@lem103696)). Qed.
Lemma lem103698 : term3.
Proof. exact (proj2 (@lem103697)). Qed.
Lemma lem103699 : term271.
Proof. exact (proj2 (@lem103698)). Qed.
Lemma lem103700 (m : nat) : term272 m.
Proof. exact (@lem103699 m). Qed.
Lemma lem103701 (m : nat) : (term272 m) = (term273 m).
Proof. exact (eq_refl (term272 m)). Qed.
Lemma lem103702 (m : nat) : term273 m.
Proof. exact (EQ_MP (@lem103701 m) (@lem103700 m)). Qed.
Lemma lem103703 (m : nat) (n : nat) : term274 m n.
Proof. exact (@lem103702 m n). Qed.
Lemma lem103704 (m : nat) (n : nat) : (term274 m n) = ((term275 m n) = (term276 m n)).
Proof. exact (eq_refl (term274 m n)). Qed.
Lemma lem103706 : term4.
Proof. exact (proj1 (@lem103698)). Qed.
Lemma lem103707 (m : nat) : term277 m.
Proof. exact (@lem103706 m). Qed.
Lemma lem103708 (m : nat) : (term277 m) = (term9 m).
Proof. exact (eq_refl (term277 m)). Qed.
Lemma lem103709 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem103708 m) (@lem103707 m)). Qed.
Lemma lem103710 (m : nat) (n : nat) : term278 m n.
Proof. exact (@lem103709 m n). Qed.
Lemma lem103711 (m : nat) (n : nat) : (term278 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term278 m n)). Qed.
Lemma lem103721 : term279.
Proof. exact (proj1 (@lem103695)). Qed.
Lemma lem103722 (m : nat) : term280 m.
Proof. exact (@lem103721 m). Qed.
Lemma lem103723 (m : nat) : (term280 m) = ((term281 m) = (NUMERAL 0)).
Proof. exact (eq_refl (term280 m)). Qed.
Lemma lem103743 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem103711 m n) (@lem103710 m n)). Qed.
Lemma lem103744 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (@lem103743 m (S n)). Qed.
Lemma lem103746 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (EQ_MP (@lem103678 m n) (@lem103677 m n)). Qed.
Lemma lem103747 (m : nat) (n : nat) : (term285 m n) = (term286 m n).
Proof. exact (@lem103746 (term275 m n) n). Qed.
Lemma lem103748 (m : nat) (n : nat) : (term284 m n) = (term286 m n).
Proof. exact (TRANS (@lem103744 m n) (@lem103747 m n)). Qed.
Lemma lem103750 (m : nat) (n : nat) : (term275 m n) = (term276 m n).
Proof. exact (EQ_MP (@lem103704 m n) (@lem103703 m n)). Qed.
Lemma lem103751 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem103752 (m : nat) (n : nat) : (term287 m n) = (term288 m n).
Proof. exact (MK_COMB (@lem103751) (@lem103750 m n)). Qed.
Lemma lem103753 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem103754 (m : nat) (n : nat) : (term289 m n) = (term290 m n).
Proof. exact (MK_COMB (@lem103752 m n) (@lem103753 n)). Qed.
Lemma lem103755 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem103756 (m : nat) (n : nat) : (term286 m n) = (term291 m n).
Proof. exact (MK_COMB (@lem103755) (@lem103754 m n)). Qed.
Lemma lem103757 (m : nat) (n : nat) : (term284 m n) = (term291 m n).
Proof. exact (TRANS (@lem103748 m n) (@lem103756 m n)). Qed.
Lemma lem103758 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem103759 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (MK_COMB (@lem103758) (@lem103757 m n)). Qed.
Lemma lem103761 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem103711 m n) (@lem103710 m n)). Qed.
Lemma lem103762 (m : nat) : (term257 m) = (term282 m).
Proof. exact (@lem103761 m (NUMERAL 0)). Qed.
Lemma lem103764 (m : nat) : (term270 m) = m.
Proof. exact (EQ_MP (@lem103689 m) (@lem103688 m)). Qed.
Lemma lem103765 (m : nat) : (term282 m) = (term281 m).
Proof. exact (@lem103764 (term281 m)). Qed.
Lemma lem103767 (m : nat) : (term281 m) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem103723 m) (@lem103722 m)). Qed.
Lemma lem103768 (m : nat) : (term282 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem103765 m) (@lem103767 m)). Qed.
Lemma lem103769 (m : nat) : (term257 m) = (NUMERAL 0).
Proof. exact (TRANS (@lem103762 m) (@lem103768 m)). Qed.
Lemma lem103770 (m : nat) (n : nat) : (term208 n m) = (term296 m n).
Proof. exact (MK_COMB (@lem103759 m n) (@lem103769 m)). Qed.
Lemma lem103773 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103774 (m : nat) (n : nat) : (term297 n m) = (term298 m n).
Proof. exact (MK_COMB (@lem103773) (@lem103770 m n)). Qed.
Lemma lem103778 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem103648 n (@lem103647 n)). Qed.
Lemma lem103779 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem103778 m). Qed.
Lemma lem103780 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem103781 (m : nat) : (term259 m) = (or False).
Proof. exact (MK_COMB (@lem103780) (@lem103779 m)). Qed.
Lemma lem103784 (n : nat) : (term250 n) = (term250 n).
Proof. exact (eq_refl (term250 n)). Qed.
Lemma lem103785 (m : nat) (n : nat) : (term209 m n) = (term299 n).
Proof. exact (MK_COMB (@lem103781 m) (@lem103784 n)). Qed.
Lemma lem103787 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem103788 (n : nat) : (term299 n) = (term250 n).
Proof. exact (@lem103787 (term250 n)). Qed.
Lemma lem103791 (m : nat) (n : nat) : (term209 m n) = (term250 n).
Proof. exact (TRANS (@lem103785 m n) (@lem103788 n)). Qed.
Lemma lem103792 (m : nat) (n : nat) : ((term208 n m) = (term209 m n)) = ((term296 m n) = (term250 n)).
Proof. exact (MK_COMB (@lem103774 m n) (@lem103791 m n)). Qed.
Lemma lem103795 (m : nat) (n : nat) : ((term296 m n) = (term250 n)) = ((term208 n m) = (term209 m n)).
Proof. exact (SYM (@lem103792 m n)). Qed.
Lemma lem103796 (n : nat) : term254 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem103797 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem103798 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem103797 n) (@lem103796 n)). Qed.
Lemma lem103799 (n : nat) : term256 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem103822 : term260.
Proof. exact (proj2 (@lem77629)). Qed.
Lemma lem103823 : term261.
Proof. exact (proj2 (@lem103822)). Qed.
Lemma lem103824 : term262.
Proof. exact (proj2 (@lem103823)). Qed.
Lemma lem103825 (m : nat) : term263 m.
Proof. exact (@lem103824 m). Qed.
Lemma lem103826 (m : nat) : (term263 m) = (term264 m).
Proof. exact (eq_refl (term263 m)). Qed.
Lemma lem103827 (m : nat) : term264 m.
Proof. exact (EQ_MP (@lem103826 m) (@lem103825 m)). Qed.
Lemma lem103828 (m : nat) (n : nat) : term265 m n.
Proof. exact (@lem103827 m n). Qed.
Lemma lem103829 (m : nat) (n : nat) : (term265 m n) = ((term266 m n) = (term267 m n)).
Proof. exact (eq_refl (term265 m n)). Qed.
Lemma lem103846 : term0.
Proof. exact (proj2 (@lem81645)). Qed.
Lemma lem103847 : term1.
Proof. exact (proj2 (@lem103846)). Qed.
Lemma lem103848 : term2.
Proof. exact (proj2 (@lem103847)). Qed.
Lemma lem103849 : term3.
Proof. exact (proj2 (@lem103848)). Qed.
Lemma lem103850 : term271.
Proof. exact (proj2 (@lem103849)). Qed.
Lemma lem103851 (m : nat) : term272 m.
Proof. exact (@lem103850 m). Qed.
Lemma lem103852 (m : nat) : (term272 m) = (term273 m).
Proof. exact (eq_refl (term272 m)). Qed.
Lemma lem103853 (m : nat) : term273 m.
Proof. exact (EQ_MP (@lem103852 m) (@lem103851 m)). Qed.
Lemma lem103854 (m : nat) (n : nat) : term274 m n.
Proof. exact (@lem103853 m n). Qed.
Lemma lem103855 (m : nat) (n : nat) : (term274 m n) = ((term275 m n) = (term276 m n)).
Proof. exact (eq_refl (term274 m n)). Qed.
Lemma lem103857 : term4.
Proof. exact (proj1 (@lem103849)). Qed.
Lemma lem103858 (m : nat) : term277 m.
Proof. exact (@lem103857 m). Qed.
Lemma lem103859 (m : nat) : (term277 m) = (term9 m).
Proof. exact (eq_refl (term277 m)). Qed.
Lemma lem103860 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem103859 m) (@lem103858 m)). Qed.
Lemma lem103861 (m : nat) (n : nat) : term278 m n.
Proof. exact (@lem103860 m n). Qed.
Lemma lem103862 (m : nat) (n : nat) : (term278 m n) = ((term5 m n) = (term6 m n)).
Proof. exact (eq_refl (term278 m n)). Qed.
Lemma lem103894 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem103862 m n) (@lem103861 m n)). Qed.
Lemma lem103895 (m : nat) (n : nat) : (term284 m n) = (term285 m n).
Proof. exact (@lem103894 m (S n)). Qed.
Lemma lem103897 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (EQ_MP (@lem103829 m n) (@lem103828 m n)). Qed.
Lemma lem103898 (m : nat) (n : nat) : (term285 m n) = (term286 m n).
Proof. exact (@lem103897 (term275 m n) n). Qed.
Lemma lem103899 (m : nat) (n : nat) : (term284 m n) = (term286 m n).
Proof. exact (TRANS (@lem103895 m n) (@lem103898 m n)). Qed.
Lemma lem103901 (m : nat) (n : nat) : (term275 m n) = (term276 m n).
Proof. exact (EQ_MP (@lem103855 m n) (@lem103854 m n)). Qed.
Lemma lem103902 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem103903 (m : nat) (n : nat) : (term287 m n) = (term288 m n).
Proof. exact (MK_COMB (@lem103902) (@lem103901 m n)). Qed.
Lemma lem103904 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem103905 (m : nat) (n : nat) : (term289 m n) = (term290 m n).
Proof. exact (MK_COMB (@lem103903 m n) (@lem103904 n)). Qed.
Lemma lem103906 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem103907 (m : nat) (n : nat) : (term286 m n) = (term291 m n).
Proof. exact (MK_COMB (@lem103906) (@lem103905 m n)). Qed.
Lemma lem103908 (m : nat) (n : nat) : (term284 m n) = (term291 m n).
Proof. exact (TRANS (@lem103899 m n) (@lem103907 m n)). Qed.
Lemma lem103909 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem103910 (m : nat) (n : nat) : (term294 m n) = (term295 m n).
Proof. exact (MK_COMB (@lem103909) (@lem103908 m n)). Qed.
Lemma lem103912 (m : nat) (n : nat) : (term5 m n) = (term6 m n).
Proof. exact (EQ_MP (@lem103862 m n) (@lem103861 m n)). Qed.
Lemma lem103913 (m : nat) (p : nat) : (term284 m p) = (term285 m p).
Proof. exact (@lem103912 m (S p)). Qed.
Lemma lem103915 (m : nat) (n : nat) : (term266 m n) = (term267 m n).
Proof. exact (EQ_MP (@lem103829 m n) (@lem103828 m n)). Qed.
Lemma lem103916 (m : nat) (p : nat) : (term285 m p) = (term286 m p).
Proof. exact (@lem103915 (term275 m p) p). Qed.
Lemma lem103917 (m : nat) (p : nat) : (term284 m p) = (term286 m p).
Proof. exact (TRANS (@lem103913 m p) (@lem103916 m p)). Qed.
Lemma lem103919 (m : nat) (n : nat) : (term275 m n) = (term276 m n).
Proof. exact (EQ_MP (@lem103855 m n) (@lem103854 m n)). Qed.
Lemma lem103920 (m : nat) (p : nat) : (term275 m p) = (term276 m p).
Proof. exact (@lem103919 m p). Qed.
Lemma lem103921 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem103922 (m : nat) (p : nat) : (term287 m p) = (term288 m p).
Proof. exact (MK_COMB (@lem103921) (@lem103920 m p)). Qed.
Lemma lem103923 (p : nat) : p = p.
Proof. exact (eq_refl p). Qed.
Lemma lem103924 (m : nat) (p : nat) : (term289 m p) = (term290 m p).
Proof. exact (MK_COMB (@lem103922 m p) (@lem103923 p)). Qed.
Lemma lem103925 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem103926 (m : nat) (p : nat) : (term286 m p) = (term291 m p).
Proof. exact (MK_COMB (@lem103925) (@lem103924 m p)). Qed.
Lemma lem103927 (m : nat) (p : nat) : (term284 m p) = (term291 m p).
Proof. exact (TRANS (@lem103917 m p) (@lem103926 m p)). Qed.
Lemma lem103928 (n : nat) (m : nat) (p : nat) : (term218 n m p) = (term300 n m p).
Proof. exact (MK_COMB (@lem103910 m n) (@lem103927 m p)). Qed.
Lemma lem103931 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103932 (n : nat) (m : nat) (p : nat) : (term301 n m p) = (term302 n m p).
Proof. exact (MK_COMB (@lem103931) (@lem103928 n m p)). Qed.
Lemma lem103936 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem103799 n (@lem103798 n)). Qed.
Lemma lem103937 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem103936 m). Qed.
Lemma lem103938 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem103939 (m : nat) : (term259 m) = (or False).
Proof. exact (MK_COMB (@lem103938) (@lem103937 m)). Qed.
Lemma lem103942 (n : nat) (p : nat) : (term43 n p) = (term43 n p).
Proof. exact (eq_refl (term43 n p)). Qed.
Lemma lem103943 (m : nat) (n : nat) (p : nat) : (term219 m n p) = (term303 n p).
Proof. exact (MK_COMB (@lem103939 m) (@lem103942 n p)). Qed.
Lemma lem103945 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem103946 (n : nat) (p : nat) : (term303 n p) = (term43 n p).
Proof. exact (@lem103945 (term43 n p)). Qed.
Lemma lem103949 (m : nat) (n : nat) (p : nat) : (term219 m n p) = (term43 n p).
Proof. exact (TRANS (@lem103943 m n p) (@lem103946 n p)). Qed.
Lemma lem103950 (m : nat) (n : nat) (p : nat) : ((term218 n m p) = (term219 m n p)) = ((term300 n m p) = (term43 n p)).
Proof. exact (MK_COMB (@lem103932 n m p) (@lem103949 m n p)). Qed.
Lemma lem103953 (m : nat) (n : nat) (p : nat) : ((term300 n m p) = (term43 n p)) = ((term218 n m p) = (term219 m n p)).
Proof. exact (SYM (@lem103950 m n p)). Qed.
Lemma lem103961 (m : nat) (n : nat) : (term43 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem102690 m n) (@lem102689 m n)). Qed.
Lemma lem103962 (n : nat) (m : nat) (p : nat) : (term300 n m p) = (term304 n m p).
Proof. exact (@lem103961 (term290 m n) (term290 m p)). Qed.
Lemma lem103963 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103964 (n : nat) (m : nat) (p : nat) : (term302 n m p) = (term305 n m p).
Proof. exact (MK_COMB (@lem103963) (@lem103962 n m p)). Qed.
Lemma lem103966 (m : nat) (n : nat) : (term43 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem102690 m n) (@lem102689 m n)). Qed.
Lemma lem103967 (n : nat) (p : nat) : (term43 n p) = (Peano.le n p).
Proof. exact (@lem103966 n p). Qed.
Lemma lem103968 (m : nat) (n : nat) (p : nat) : ((term300 n m p) = (term43 n p)) = ((term304 n m p) = (Peano.le n p)).
Proof. exact (MK_COMB (@lem103964 n m p) (@lem103967 n p)). Qed.
Lemma lem103971 (m : nat) (n : nat) (p : nat) : ((term304 n m p) = (Peano.le n p)) = ((term300 n m p) = (term43 n p)).
Proof. exact (SYM (@lem103968 m n p)). Qed.
Lemma lem103975 (m : nat) : (term39 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem102684 m) (@lem102683 m)). Qed.
Lemma lem103976 (m : nat) (n : nat) : (term296 m n) = ((term291 m n) = (NUMERAL 0)).
Proof. exact (@lem103975 (term291 m n)). Qed.
Lemma lem103980 (m : nat) (n : nat) (p : nat) : (term15 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem102664 m n p) (@lem102663 m n p)). Qed.
Lemma lem103981 (m : nat) (n : nat) : (term290 m n) = (term306 m n).
Proof. exact (@lem103980 m (Nat.mul m n) n). Qed.
Lemma lem103982 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem103983 (m : nat) (n : nat) : (term291 m n) = (term307 m n).
Proof. exact (MK_COMB (@lem103982) (@lem103981 m n)). Qed.
Lemma lem103984 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem103985 (m : nat) (n : nat) : (term308 m n) = (term309 m n).
Proof. exact (MK_COMB (@lem103984) (@lem103983 m n)). Qed.
Lemma lem103986 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem103987 (m : nat) (n : nat) : ((term291 m n) = (NUMERAL 0)) = ((term307 m n) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem103985 m n) (@lem103986)). Qed.
Lemma lem103990 (m : nat) (n : nat) : (term296 m n) = ((term307 m n) = (NUMERAL 0)).
Proof. exact (TRANS (@lem103976 m n) (@lem103987 m n)). Qed.
Lemma lem103991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem103992 (m : nat) (n : nat) : (term298 m n) = (term310 m n).
Proof. exact (MK_COMB (@lem103991) (@lem103990 m n)). Qed.
Lemma lem103994 (m : nat) : (term39 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem102684 m) (@lem102683 m)). Qed.
Lemma lem103995 (n : nat) : (term250 n) = ((S n) = (NUMERAL 0)).
Proof. exact (@lem103994 (S n)). Qed.
Lemma lem103998 (m : nat) (n : nat) : ((term296 m n) = (term250 n)) = (((term307 m n) = (NUMERAL 0)) = ((S n) = (NUMERAL 0))).
Proof. exact (MK_COMB (@lem103992 m n) (@lem103995 n)). Qed.
Lemma lem104001 (m : nat) (n : nat) : (((term307 m n) = (NUMERAL 0)) = ((S n) = (NUMERAL 0))) = ((term296 m n) = (term250 n)).
Proof. exact (SYM (@lem103998 m n)). Qed.
Lemma lem104007 (m : nat) (n : nat) (p : nat) : (term15 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem102664 m n p) (@lem102663 m n p)). Qed.
Lemma lem104008 (m : nat) (n : nat) : (term290 m n) = (term306 m n).
Proof. exact (@lem104007 m (Nat.mul m n) n). Qed.
Lemma lem104009 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem104010 (m : nat) (n : nat) : (term311 m n) = (term312 m n).
Proof. exact (MK_COMB (@lem104009) (@lem104008 m n)). Qed.
Lemma lem104012 (m : nat) (n : nat) (p : nat) : (term15 m n p) = (term14 m n p).
Proof. exact (EQ_MP (@lem102664 m n p) (@lem102663 m n p)). Qed.
Lemma lem104013 (m : nat) (p : nat) : (term290 m p) = (term306 m p).
Proof. exact (@lem104012 m (Nat.mul m p) p). Qed.
Lemma lem104014 (n : nat) (m : nat) (p : nat) : (term304 n m p) = (term313 n m p).
Proof. exact (MK_COMB (@lem104010 m n) (@lem104013 m p)). Qed.
Lemma lem104016 (m : nat) (n : nat) (p : nat) : (term36 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem102673 m n p) (@lem102672 m n p)). Qed.
Lemma lem104017 (n : nat) (m : nat) (p : nat) : (term313 n m p) = (term314 n m p).
Proof. exact (@lem104016 m (term6 m n) (term6 m p)). Qed.
Lemma lem104020 (n : nat) (m : nat) (p : nat) : (term304 n m p) = (term314 n m p).
Proof. exact (TRANS (@lem104014 n m p) (@lem104017 n m p)). Qed.
Lemma lem104021 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem104022 (n : nat) (m : nat) (p : nat) : (term305 n m p) = (term315 n m p).
Proof. exact (MK_COMB (@lem104021) (@lem104020 n m p)). Qed.
Lemma lem104023 (n : nat) (p : nat) : (Peano.le n p) = (Peano.le n p).
Proof. exact (eq_refl (Peano.le n p)). Qed.
Lemma lem104024 (m : nat) (n : nat) (p : nat) : ((term304 n m p) = (Peano.le n p)) = ((term314 n m p) = (Peano.le n p)).
Proof. exact (MK_COMB (@lem104022 n m p) (@lem104023 n p)). Qed.
Lemma lem104027 (m : nat) (n : nat) (p : nat) : ((term314 n m p) = (Peano.le n p)) = ((term304 n m p) = (Peano.le n p)).
Proof. exact (SYM (@lem104024 m n p)). Qed.
Lemma lem104028 (n : nat) : term254 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem104029 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem104030 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem104029 n) (@lem104028 n)). Qed.
Lemma lem104031 (n : nat) : term256 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem104062 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem104031 n (@lem104030 n)). Qed.
Lemma lem104063 (m : nat) (n : nat) : ((term307 m n) = (NUMERAL 0)) = False.
Proof. exact (@lem104062 (term306 m n)). Qed.
Lemma lem104064 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem104065 (m : nat) (n : nat) : (term310 m n) = (@eq Prop False).
Proof. exact (MK_COMB (@lem104064) (@lem104063 m n)). Qed.
Lemma lem104067 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem104031 n (@lem104030 n)). Qed.
Lemma lem104068 (m : nat) (n : nat) : (((term307 m n) = (NUMERAL 0)) = ((S n) = (NUMERAL 0))) = (False = False).
Proof. exact (MK_COMB (@lem104065 m n) (@lem104067 n)). Qed.
Lemma lem104070 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem104071 : (False = False) = (~ False).
Proof. exact (@lem104070 False). Qed.
Lemma lem104073 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem104074 : (False = False) = True.
Proof. exact (TRANS (@lem104071) (@lem104073)). Qed.
Lemma lem104075 (m : nat) (n : nat) : (((term307 m n) = (NUMERAL 0)) = ((S n) = (NUMERAL 0))) = True.
Proof. exact (TRANS (@lem104068 m n) (@lem104074)). Qed.
Lemma lem104076 (m : nat) (n : nat) : True = (((term307 m n) = (NUMERAL 0)) = ((S n) = (NUMERAL 0))).
Proof. exact (SYM (@lem104075 m n)). Qed.
Lemma lem104077 (m : nat) (n : nat) : ((term307 m n) = (NUMERAL 0)) = ((S n) = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem104076 m n) (@lem0)). Qed.
Lemma lem104078 (n : nat) : term254 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem104079 (n : nat) : (term254 n) = (term255 n).
Proof. exact (eq_refl (term254 n)). Qed.
Lemma lem104080 (n : nat) : term255 n.
Proof. exact (EQ_MP (@lem104079 n) (@lem104078 n)). Qed.
Lemma lem104081 (n : nat) : term256 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem104094 (m : nat) : term316 m.
Proof. exact (@lem102638 m). Qed.
Lemma lem104095 (m : nat) : (term316 m) = (term10 m).
Proof. exact (eq_refl (term316 m)). Qed.
Lemma lem104096 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem104095 m) (@lem104094 m)). Qed.
Lemma lem104097 (m : nat) (n : nat) : term317 m n.
Proof. exact (@lem104096 m n). Qed.
Lemma lem104098 (m : nat) (n : nat) : (term317 m n) = ((term6 m n) = (term5 m n)).
Proof. exact (eq_refl (term317 m n)). Qed.
Lemma lem104106 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : term318 m n p.
Proof. exact (@lem102819 m n h1 p). Qed.
Lemma lem104107 (m : nat) (n : nat) (p : nat) : (term318 m n p) = ((term319 n m p) = (term320 m n p)).
Proof. exact (eq_refl (term318 m n p)). Qed.
Lemma lem104112 (m : nat) (n : nat) : (term6 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem104098 m n) (@lem104097 m n)). Qed.
Lemma lem104113 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem104114 (m : nat) (n : nat) : (term321 m n) = (term322 m n).
Proof. exact (MK_COMB (@lem104113) (@lem104112 m n)). Qed.
Lemma lem104116 (m : nat) (n : nat) : (term6 m n) = (term5 m n).
Proof. exact (EQ_MP (@lem104098 m n) (@lem104097 m n)). Qed.
Lemma lem104117 (m : nat) (p : nat) : (term6 m p) = (term5 m p).
Proof. exact (@lem104116 m p). Qed.
Lemma lem104118 (n : nat) (m : nat) (p : nat) : (term314 n m p) = (term319 n m p).
Proof. exact (MK_COMB (@lem104114 m n) (@lem104117 m p)). Qed.
Lemma lem104120 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term319 n m p) = (term320 m n p).
Proof. exact (EQ_MP (@lem104107 m n p) (@lem104106 p m n h1)). Qed.
Lemma lem104124 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem104081 n (@lem104080 n)). Qed.
Lemma lem104125 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem104124 m). Qed.
Lemma lem104126 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem104127 (m : nat) : (term259 m) = (or False).
Proof. exact (MK_COMB (@lem104126) (@lem104125 m)). Qed.
Lemma lem104128 (n : nat) (p : nat) : (Peano.le n p) = (Peano.le n p).
Proof. exact (eq_refl (Peano.le n p)). Qed.
Lemma lem104129 (m : nat) (n : nat) (p : nat) : (term320 m n p) = (term323 n p).
Proof. exact (MK_COMB (@lem104127 m) (@lem104128 n p)). Qed.
Lemma lem104131 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem104132 (n : nat) (p : nat) : (term323 n p) = (Peano.le n p).
Proof. exact (@lem104131 (Peano.le n p)). Qed.
Lemma lem104133 (m : nat) (n : nat) (p : nat) : (term320 m n p) = (Peano.le n p).
Proof. exact (TRANS (@lem104129 m n p) (@lem104132 n p)). Qed.
Lemma lem104134 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term319 n m p) = (Peano.le n p).
Proof. exact (TRANS (@lem104120 p m n h1) (@lem104133 m n p)). Qed.
Lemma lem104135 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term314 n m p) = (Peano.le n p).
Proof. exact (TRANS (@lem104118 n m p) (@lem104134 p m n h1)). Qed.
Lemma lem104136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem104137 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term315 n m p) = (term324 n p).
Proof. exact (MK_COMB (@lem104136) (@lem104135 p m n h1)). Qed.
Lemma lem104138 (n : nat) (p : nat) : (Peano.le n p) = (Peano.le n p).
Proof. exact (eq_refl (Peano.le n p)). Qed.
Lemma lem104139 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : ((term314 n m p) = (Peano.le n p)) = ((Peano.le n p) = (Peano.le n p)).
Proof. exact (MK_COMB (@lem104137 p m n h1) (@lem104138 n p)). Qed.
Lemma lem104141 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem104142 (x : Prop) : (x = x) = True.
Proof. exact (@lem104141 Prop x). Qed.
Lemma lem104143 (n : nat) (p : nat) : ((Peano.le n p) = (Peano.le n p)) = True.
Proof. exact (@lem104142 (Peano.le n p)). Qed.
Lemma lem104144 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : ((term314 n m p) = (Peano.le n p)) = True.
Proof. exact (TRANS (@lem104139 p m n h1) (@lem104143 n p)). Qed.
Lemma lem104145 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : True = ((term314 n m p) = (Peano.le n p)).
Proof. exact (SYM (@lem104144 p m n h1)). Qed.
Lemma lem104146 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term314 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem104145 p m n h1) (@lem0)). Qed.
Lemma lem104147 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term304 n m p) = (Peano.le n p).
Proof. exact (EQ_MP (@lem104027 m n p) (@lem104146 p m n h1)). Qed.
Lemma lem104149 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term300 n m p) = (term43 n p).
Proof. exact (EQ_MP (@lem103971 m n p) (@lem104147 p m n h1)). Qed.
Lemma lem104150 (m : nat) (n : nat) : (term296 m n) = (term250 n).
Proof. exact (EQ_MP (@lem104001 m n) (@lem104077 m n)). Qed.
Lemma lem104151 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : (term218 n m p) = (term219 m n p).
Proof. exact (EQ_MP (@lem103953 m n p) (@lem104149 p m n h1)). Qed.
Lemma lem104152 (m : nat) (n : nat) : (term208 n m) = (term209 m n).
Proof. exact (EQ_MP (@lem103795 m n) (@lem104150 m n)). Qed.
Lemma lem104153 (p : nat) (m : nat) (n : nat) (h1 : term159 m n) : term221 m n p.
Proof. exact (fun h0 : (term213 n m p) = (term214 m n p) => @lem104151 p m n h1). Qed.
Lemma lem104158 (m : nat) (n : nat) (h1 : term159 m n) : term225 m n.
Proof. exact (fun p : nat => @lem104153 p m n h1). Qed.
Lemma lem104159 (m : nat) (n : nat) (h1 : term159 m n) : term227 m n.
Proof. exact (conj (@lem104152 m n) (@lem104158 m n h1)). Qed.
Lemma lem104160 (m : nat) (n : nat) (h1 : term159 m n) : term163 m n.
Proof. exact (@lem102870 m n (@lem104159 m n h1)). Qed.
Lemma lem104161 (m : nat) (p : nat) : term193 m p.
Proof. exact (fun h0 : (term185 m p) = (term186 m p) => @lem103644 m p). Qed.
Lemma lem104166 (m : nat) : term197 m.
Proof. exact (fun p : nat => @lem104161 m p). Qed.
Lemma lem104167 (m : nat) : term199 m.
Proof. exact (conj (@lem103492 m) (@lem104166 m)). Qed.
Lemma lem104168 (m : nat) : term155 m.
Proof. exact (@lem102842 m (@lem104167 m)). Qed.
Lemma lem104169 (m : nat) (n : nat) : term165 m n.
Proof. exact (fun h0 : term159 m n => @lem104160 m n h0). Qed.
Lemma lem104174 (m : nat) : term169 m.
Proof. exact (fun n : nat => @lem104169 m n). Qed.
Lemma lem104175 (m : nat) : term171 m.
Proof. exact (conj (@lem104168 m) (@lem104174 m)). Qed.
Lemma lem104176 (m : nat) : term56 m.
Proof. exact (@lem102818 m (@lem104175 m)). Qed.
Lemma lem104177 (n : nat) (p : nat) : term140 n p.
Proof. exact (fun h0 : (term132 n p) = (term133 n p) => @lem103373 n p). Qed.
Lemma lem104182 (n : nat) : term144 n.
Proof. exact (fun p : nat => @lem104177 n p). Qed.
Lemma lem104183 (n : nat) : term146 n.
Proof. exact (conj (@lem103244 n) (@lem104182 n)). Qed.
Lemma lem104184 (n : nat) : term82 n.
Proof. exact (@lem102790 n (@lem104183 n)). Qed.
Lemma lem104185 (p : nat) : term112 p.
Proof. exact (fun h0 : (term104 p) = (term105 p) => @lem103115 p). Qed.
Lemma lem104190 : term116.
Proof. exact (fun p : nat => @lem104185 p). Qed.
Lemma lem104191 : term118.
Proof. exact (conj (@lem102989) (@lem104190)). Qed.
Lemma lem104192 : term74.
Proof. exact (@lem102762 (@lem104191)). Qed.
Lemma lem104193 (n : nat) : term84 n.
Proof. exact (fun h0 : term78 n => @lem104184 n). Qed.
Lemma lem104198 : term88.
Proof. exact (fun n : nat => @lem104193 n). Qed.
Lemma lem104199 : term90.
Proof. exact (conj (@lem104192) (@lem104198)). Qed.
Lemma lem104200 : term48.
Proof. exact (@lem102738 (@lem104199)). Qed.
Lemma lem104201 (m : nat) : term58 m.
Proof. exact (fun h0 : term52 m => @lem104176 m). Qed.
Lemma lem104206 : term62.
Proof. exact (fun m : nat => @lem104201 m). Qed.
Lemma lem104207 : term64.
Proof. exact (conj (@lem104200) (@lem104206)). Qed.
Lemma lem104208 : term69.
Proof. exact (@lem102714 (@lem104207)). Qed.
