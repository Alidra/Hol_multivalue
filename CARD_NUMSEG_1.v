Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_NUMSEG_1_term_abbrevs.
Require Import CARD_NUMSEG_spec.
Require Import INT_POS_spec.
Require Import thm0_spec.
Require Import thm1006570_spec.
Require Import thm1007663_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1367763_spec.
Require Import thm1367770_spec.
Require Import thm1367771_spec.
Require Import thm1386578_spec.
Require Import thm1396750_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17362_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982709_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982749_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm7_spec.
Require Import thm706885_spec.
Require Import thm912739_spec.
Require Import thm912803_spec.
Require Import thm940073_spec.
Require Import thm996237_spec.
Require Import thm996238_spec.
Lemma lem5393578 (m : nat) : term0 m.
Proof. exact (@lem5393502 m). Qed.
Lemma lem5393579 (m : nat) : (term0 m) = (term1 m).
Proof. exact (eq_refl (term0 m)). Qed.
Lemma lem5393580 (m : nat) : term1 m.
Proof. exact (EQ_MP (@lem5393579 m) (@lem5393578 m)). Qed.
Lemma lem5393581 (m : nat) (n : nat) : term2 m n.
Proof. exact (@lem5393580 m n). Qed.
Lemma lem5393582 (n : nat) (m : nat) : (term2 m n) = ((term3 m n) = (term4 n m)).
Proof. exact (eq_refl (term2 m n)). Qed.
Lemma lem5393591 (n : nat) (m : nat) : (term3 m n) = (term4 n m).
Proof. exact (EQ_MP (@lem5393582 n m) (@lem5393581 m n)). Qed.
Lemma lem5393592 (n : nat) : (term5 n) = (term6 n).
Proof. exact (@lem5393591 n term7). Qed.
Lemma lem5393593 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem5393594 (n : nat) : (term8 n) = (term9 n).
Proof. exact (MK_COMB (@lem5393593) (@lem5393592 n)). Qed.
Lemma lem5393595 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem5393596 (n : nat) : ((term5 n) = n) = ((term6 n) = n).
Proof. exact (MK_COMB (@lem5393594 n) (@lem5393595 n)). Qed.
Lemma lem5393599 : term10 = term11.
Proof. exact (fun_ext (fun n : nat => @lem5393596 n)). Qed.
Lemma lem5393600 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393601 : term12 = term13.
Proof. exact (MK_COMB (@lem5393600) (@lem5393599)). Qed.
Lemma lem5393606 : term13 = term12.
Proof. exact (SYM (@lem5393601)). Qed.
Lemma lem5393614 (n : nat) : ((term6 n) = n) = ((term6 n) = n).
Proof. exact (eq_refl ((term6 n) = n)). Qed.
Lemma lem5393615 : term11 = term11.
Proof. exact (fun_ext (fun n : nat => @lem5393614 n)). Qed.
Lemma lem5393616 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393618 : term13 = term13.
Proof. exact (MK_COMB (@lem5393616) (@lem5393615)). Qed.
Lemma lem5393619 (n : nat) : ((term6 n) = n) = ((term6 n) = n).
Proof. exact (eq_refl ((term6 n) = n)). Qed.
Lemma lem5393620 : term11 = term11.
Proof. exact (fun_ext (fun n : nat => @lem5393619 n)). Qed.
Lemma lem5393621 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393622 : term13 = term13.
Proof. exact (MK_COMB (@lem5393621) (@lem5393620)). Qed.
Lemma lem5393623 : term13 = term13.
Proof. exact (TRANS (@lem5393618) (@lem5393622)). Qed.
Lemma lem5393624 (n : nat) : (term14 n) = (term15 n).
Proof. exact (@lem1032781 (term16 n) term7 (term17 n)). Qed.
Lemma lem5393625 (d : nat) (n : nat) : (term18 n d) = (d = n).
Proof. exact (eq_refl (term18 n d)). Qed.
Lemma lem5393626 (n : nat) (d : nat) : (term19 n d) = (term19 n d).
Proof. exact (eq_refl (term19 n d)). Qed.
Lemma lem5393627 (d : nat) (n : nat) : (term20 n d) = (term21 d n).
Proof. exact (MK_COMB (@lem5393626 n d) (@lem5393625 d n)). Qed.
Lemma lem5393628 (n : nat) : (term22 n) = (term23 n).
Proof. exact (fun_ext (fun d : nat => @lem5393627 d n)). Qed.
Lemma lem5393629 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393630 (n : nat) : (term15 n) = (term24 n).
Proof. exact (MK_COMB (@lem5393629) (@lem5393628 n)). Qed.
Lemma lem5393631 (n : nat) : (term14 n) = ((term6 n) = n).
Proof. exact (eq_refl (term14 n)). Qed.
Lemma lem5393632 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5393633 (n : nat) : (term25 n) = (term26 n).
Proof. exact (MK_COMB (@lem5393632) (@lem5393631 n)). Qed.
Lemma lem5393634 (n : nat) : ((term14 n) = (term15 n)) = (((term6 n) = n) = (term24 n)).
Proof. exact (MK_COMB (@lem5393633 n) (@lem5393630 n)). Qed.
Lemma lem5393635 (n : nat) : ((term6 n) = n) = (term24 n).
Proof. exact (EQ_MP (@lem5393634 n) (@lem5393624 n)). Qed.
Lemma lem5393636 (d : nat) (n : nat) : (term21 d n) = (term21 d n).
Proof. exact (eq_refl (term21 d n)). Qed.
Lemma lem5393637 (n : nat) : (term23 n) = (term23 n).
Proof. exact (fun_ext (fun d : nat => @lem5393636 d n)). Qed.
Lemma lem5393638 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393639 (n : nat) : (term24 n) = (term24 n).
Proof. exact (MK_COMB (@lem5393638) (@lem5393637 n)). Qed.
Lemma lem5393640 (n : nat) : (term26 n) = (term26 n).
Proof. exact (eq_refl (term26 n)). Qed.
Lemma lem5393641 (n : nat) : (((term6 n) = n) = (term24 n)) = (((term6 n) = n) = (term24 n)).
Proof. exact (MK_COMB (@lem5393640 n) (@lem5393639 n)). Qed.
Lemma lem5393642 (n : nat) : ((term6 n) = n) = (term24 n).
Proof. exact (EQ_MP (@lem5393641 n) (@lem5393635 n)). Qed.
Lemma lem5393643 : term11 = term27.
Proof. exact (fun_ext (fun n : nat => @lem5393642 n)). Qed.
Lemma lem5393644 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393645 : term13 = term28.
Proof. exact (MK_COMB (@lem5393644) (@lem5393643)). Qed.
Lemma lem5393672 : term13 = term28.
Proof. exact (TRANS (@lem5393623) (@lem5393645)). Qed.
Lemma lem5393677 (d : nat) (n : nat) : (d = n) = (d = n).
Proof. exact (eq_refl (d = n)). Qed.
Lemma lem5393700 (n : nat) (d : nat) : (term29 n d) = (term29 n d).
Proof. exact (eq_refl (term29 n d)). Qed.
Lemma lem5393707 (d : nat) : (term30 d) = (term16 d).
Proof. exact (@lem1032098 d term7). Qed.
Lemma lem5393716 (n : nat) : (term31 n) = (term31 n).
Proof. exact (eq_refl (term31 n)). Qed.
Lemma lem5393717 (n : nat) (d : nat) : ((term16 n) = (term30 d)) = ((term16 n) = (term16 d)).
Proof. exact (MK_COMB (@lem5393716 n) (@lem5393707 d)). Qed.
Lemma lem5393718 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5393719 (n : nat) (d : nat) : (term32 n d) = (term33 n d).
Proof. exact (MK_COMB (@lem5393718) (@lem5393717 n d)). Qed.
Lemma lem5393720 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5393721 (n : nat) (d : nat) : (term34 n d) = (term35 n d).
Proof. exact (MK_COMB (@lem5393720) (@lem5393719 n d)). Qed.
Lemma lem5393722 (n : nat) (d : nat) : (term36 n d) = (term37 n d).
Proof. exact (MK_COMB (@lem5393721 n d) (@lem5393700 n d)). Qed.
Lemma lem5393723 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5393724 (n : nat) (d : nat) : (term19 n d) = (term38 n d).
Proof. exact (MK_COMB (@lem5393723) (@lem5393722 n d)). Qed.
Lemma lem5393725 (d : nat) (n : nat) : (term21 d n) = (term39 d n).
Proof. exact (MK_COMB (@lem5393724 n d) (@lem5393677 d n)). Qed.
Lemma lem5393726 (n : nat) : (term23 n) = (term40 n).
Proof. exact (fun_ext (fun d : nat => @lem5393725 d n)). Qed.
Lemma lem5393727 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393728 (n : nat) : (term24 n) = (term41 n).
Proof. exact (MK_COMB (@lem5393727) (@lem5393726 n)). Qed.
Lemma lem5393729 : term27 = term42.
Proof. exact (fun_ext (fun n : nat => @lem5393728 n)). Qed.
Lemma lem5393730 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393731 : term28 = term43.
Proof. exact (MK_COMB (@lem5393730) (@lem5393729)). Qed.
Lemma lem5393734 : term13 = term43.
Proof. exact (TRANS (@lem5393672) (@lem5393731)). Qed.
Lemma lem5393736 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5393737 (n : nat) (d : nat) : ((term16 n) = (term16 d)) = ((term44 n) = (term44 d)).
Proof. exact (@lem5393736 (term16 n) (term16 d)). Qed.
Lemma lem5393741 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5393742 (n : nat) : (term44 n) = (term47 n).
Proof. exact (@lem5393741 n term7). Qed.
Lemma lem5393743 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem5393744 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem5393743) (@lem5393742 n)). Qed.
Lemma lem5393746 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5393747 (d : nat) : (term44 d) = (term47 d).
Proof. exact (@lem5393746 d term7). Qed.
Lemma lem5393748 (n : nat) (d : nat) : ((term44 n) = (term44 d)) = ((term47 n) = (term47 d)).
Proof. exact (MK_COMB (@lem5393744 n) (@lem5393747 d)). Qed.
Lemma lem5393749 (n : nat) (d : nat) : ((term16 n) = (term16 d)) = ((term47 n) = (term47 d)).
Proof. exact (TRANS (@lem5393737 n d) (@lem5393748 n d)). Qed.
Lemma lem5393750 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5393751 (n : nat) (d : nat) : (term33 n d) = (term50 n d).
Proof. exact (MK_COMB (@lem5393750) (@lem5393749 n d)). Qed.
Lemma lem5393752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5393753 (n : nat) (d : nat) : (term35 n d) = (term51 n d).
Proof. exact (MK_COMB (@lem5393752) (@lem5393751 n d)). Qed.
Lemma lem5393755 (m : nat) (n : nat) : (Peano.lt m n) = (term52 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem5393756 (n : nat) : (term53 n) = (term54 n).
Proof. exact (@lem5393755 (term16 n) term7). Qed.
Lemma lem5393758 (m : nat) (n : nat) : (term45 m n) = (term46 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem5393759 (n : nat) : (term44 n) = (term47 n).
Proof. exact (@lem5393758 n term7). Qed.
Lemma lem5393760 : int_lt = int_lt.
Proof. exact (eq_refl int_lt). Qed.
Lemma lem5393761 (n : nat) : (term55 n) = (term56 n).
Proof. exact (MK_COMB (@lem5393760) (@lem5393759 n)). Qed.
Lemma lem5393762 : term57 = term57.
Proof. exact (eq_refl term57). Qed.
Lemma lem5393763 (n : nat) : (term54 n) = (term58 n).
Proof. exact (MK_COMB (@lem5393761 n) (@lem5393762)). Qed.
Lemma lem5393764 (n : nat) : (term53 n) = (term58 n).
Proof. exact (TRANS (@lem5393756 n) (@lem5393763 n)). Qed.
Lemma lem5393765 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5393766 (n : nat) : (term59 n) = (term60 n).
Proof. exact (MK_COMB (@lem5393765) (@lem5393764 n)). Qed.
Lemma lem5393767 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5393768 (n : nat) : (term61 n) = (term62 n).
Proof. exact (MK_COMB (@lem5393767) (@lem5393766 n)). Qed.
Lemma lem5393770 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5393771 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term63).
Proof. exact (@lem5393770 d (NUMERAL 0)). Qed.
Lemma lem5393774 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5393775 (d : nat) : (term64 d) = (term65 d).
Proof. exact (MK_COMB (@lem5393774) (@lem5393771 d)). Qed.
Lemma lem5393776 (n : nat) (d : nat) : (term29 n d) = (term66 n d).
Proof. exact (MK_COMB (@lem5393768 n) (@lem5393775 d)). Qed.
Lemma lem5393777 (n : nat) (d : nat) : (term37 n d) = (term67 n d).
Proof. exact (MK_COMB (@lem5393753 n d) (@lem5393776 n d)). Qed.
Lemma lem5393778 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5393779 (n : nat) (d : nat) : (term38 n d) = (term68 n d).
Proof. exact (MK_COMB (@lem5393778) (@lem5393777 n d)). Qed.
Lemma lem5393781 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem5393782 (d : nat) (n : nat) : (d = n) = ((int_of_num d) = (int_of_num n)).
Proof. exact (@lem5393781 d n). Qed.
Lemma lem5393785 (d : nat) (n : nat) : (term39 d n) = (term69 d n).
Proof. exact (MK_COMB (@lem5393779 n d) (@lem5393782 d n)). Qed.
Lemma lem5393786 (n : nat) : (term40 n) = (term70 n).
Proof. exact (fun_ext (fun d : nat => @lem5393785 d n)). Qed.
Lemma lem5393787 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393788 (n : nat) : (term41 n) = (term71 n).
Proof. exact (MK_COMB (@lem5393787) (@lem5393786 n)). Qed.
Lemma lem5393789 : term42 = term72.
Proof. exact (fun_ext (fun n : nat => @lem5393788 n)). Qed.
Lemma lem5393790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem5393791 : term43 = term73.
Proof. exact (MK_COMB (@lem5393790) (@lem5393789)). Qed.
Lemma lem5393792 : term13 = term73.
Proof. exact (TRANS (@lem5393734) (@lem5393791)). Qed.
Lemma lem5393793 (d : nat) : term74 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem5393794 (d : nat) : (term74 d) = (term75 d).
Proof. exact (eq_refl (term74 d)). Qed.
Lemma lem5393795 (d : nat) : term75 d.
Proof. exact (EQ_MP (@lem5393794 d) (@lem5393793 d)). Qed.
Lemma lem5393796 (n : nat) : term74 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem5393797 (n : nat) : (term74 n) = (term75 n).
Proof. exact (eq_refl (term74 n)). Qed.
Lemma lem5393798 (n : nat) : term75 n.
Proof. exact (EQ_MP (@lem5393797 n) (@lem5393796 n)). Qed.
Lemma lem5393799 (_69873 : int) (_69874 : int) : (term76 _69873 _69874) = (term77 _69873 _69874).
Proof. exact (@lem2318604 (term77 _69873 _69874)). Qed.
Lemma lem5393819 (_69874 : int) (_69873 : int) : (term78 _69874 _69873) = ((term79 _69874) = (term79 _69873)).
Proof. exact (@lem16933 ((term79 _69874) = (term79 _69873))). Qed.
Lemma lem5393822 (_69874 : int) : (term80 _69874) = (term81 _69874).
Proof. exact (@lem16933 (term81 _69874)). Qed.
Lemma lem5393825 (_69873 : int) : (term82 _69873) = (_69873 = term63).
Proof. exact (@lem16933 (_69873 = term63)). Qed.
Lemma lem5393826 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5393827 (_69874 : int) : (term83 _69874) = (term84 _69874).
Proof. exact (MK_COMB (@lem5393826) (@lem5393822 _69874)). Qed.
Lemma lem5393828 (_69874 : int) (_69873 : int) : (term85 _69874 _69873) = (term86 _69874 _69873).
Proof. exact (MK_COMB (@lem5393827 _69874) (@lem5393825 _69873)). Qed.
Lemma lem5393829 (_69874 : int) (_69873 : int) : (term87 _69874 _69873) = (term85 _69874 _69873).
Proof. exact (@lem17160 (term88 _69874) (term89 _69873)). Qed.
Lemma lem5393830 (_69874 : int) (_69873 : int) : (term87 _69874 _69873) = (term86 _69874 _69873).
Proof. exact (TRANS (@lem5393829 _69874 _69873) (@lem5393828 _69874 _69873)). Qed.
Lemma lem5393831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5393832 (_69874 : int) (_69873 : int) : (term90 _69874 _69873) = (term91 _69874 _69873).
Proof. exact (MK_COMB (@lem5393831) (@lem5393819 _69874 _69873)). Qed.
Lemma lem5393833 (_69874 : int) (_69873 : int) : (term92 _69874 _69873) = (term93 _69874 _69873).
Proof. exact (MK_COMB (@lem5393832 _69874 _69873) (@lem5393830 _69874 _69873)). Qed.
Lemma lem5393834 (_69874 : int) (_69873 : int) : (term94 _69874 _69873) = (term92 _69874 _69873).
Proof. exact (@lem17045 (term95 _69874 _69873) (term96 _69874 _69873)). Qed.
Lemma lem5393835 (_69874 : int) (_69873 : int) : (term94 _69874 _69873) = (term93 _69874 _69873).
Proof. exact (TRANS (@lem5393834 _69874 _69873) (@lem5393833 _69874 _69873)). Qed.
Lemma lem5393836 (_69873 : int) (_69874 : int) : (term97 _69873 _69874) = (term97 _69873 _69874).
Proof. exact (eq_refl (term97 _69873 _69874)). Qed.
Lemma lem5393837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5393838 (_69874 : int) (_69873 : int) : (term98 _69874 _69873) = (term99 _69874 _69873).
Proof. exact (MK_COMB (@lem5393837) (@lem5393835 _69874 _69873)). Qed.
Lemma lem5393839 (_69873 : int) (_69874 : int) : (term100 _69873 _69874) = (term101 _69873 _69874).
Proof. exact (MK_COMB (@lem5393838 _69874 _69873) (@lem5393836 _69873 _69874)). Qed.
Lemma lem5393840 (_69873 : int) (_69874 : int) : (term102 _69873 _69874) = (term100 _69873 _69874).
Proof. exact (@lem17160 (term103 _69874 _69873) (_69873 = _69874)). Qed.
Lemma lem5393841 (_69873 : int) (_69874 : int) : (term102 _69873 _69874) = (term101 _69873 _69874).
Proof. exact (TRANS (@lem5393840 _69873 _69874) (@lem5393839 _69873 _69874)). Qed.
Lemma lem5393843 (_69874 : int) : (term104 _69874) = (term104 _69874).
Proof. exact (eq_refl (term104 _69874)). Qed.
Lemma lem5393844 (_69873 : int) (_69874 : int) : (term105 _69873 _69874) = (term106 _69873 _69874).
Proof. exact (MK_COMB (@lem5393843 _69874) (@lem5393841 _69873 _69874)). Qed.
Lemma lem5393845 (_69873 : int) (_69874 : int) : (term107 _69873 _69874) = (term105 _69873 _69874).
Proof. exact (@lem17362 (term108 _69874) (term109 _69873 _69874)). Qed.
Lemma lem5393846 (_69873 : int) (_69874 : int) : (term107 _69873 _69874) = (term106 _69873 _69874).
Proof. exact (TRANS (@lem5393845 _69873 _69874) (@lem5393844 _69873 _69874)). Qed.
Lemma lem5393848 (_69873 : int) : (term104 _69873) = (term104 _69873).
Proof. exact (eq_refl (term104 _69873)). Qed.
Lemma lem5393849 (_69873 : int) (_69874 : int) : (term110 _69873 _69874) = (term111 _69873 _69874).
Proof. exact (MK_COMB (@lem5393848 _69873) (@lem5393846 _69873 _69874)). Qed.
Lemma lem5393850 (_69873 : int) (_69874 : int) : (term112 _69873 _69874) = (term110 _69873 _69874).
Proof. exact (@lem17362 (term108 _69873) (term113 _69873 _69874)). Qed.
Lemma lem5393876 (_69873 : int) (_69874 : int) : (term112 _69873 _69874) = (term111 _69873 _69874).
Proof. exact (TRANS (@lem5393850 _69873 _69874) (@lem5393849 _69873 _69874)). Qed.
Lemma lem5393879 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5393880 (_69873 : int) : (term108 _69873) = (term115 _69873).
Proof. exact (@lem5393879 term63 _69873). Qed.
Lemma lem5393882 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393883 : term117 = term118.
Proof. exact (@lem5393882 (NUMERAL 0)). Qed.
Lemma lem5393884 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5393885 : term119 = term120.
Proof. exact (MK_COMB (@lem5393884) (@lem5393883)). Qed.
Lemma lem5393886 (_69873 : int) : (real_of_int _69873) = (real_of_int _69873).
Proof. exact (eq_refl (real_of_int _69873)). Qed.
Lemma lem5393887 (_69873 : int) : (term115 _69873) = (term121 _69873).
Proof. exact (MK_COMB (@lem5393885) (@lem5393886 _69873)). Qed.
Lemma lem5393889 (_69873 : int) : (term108 _69873) = (term121 _69873).
Proof. exact (TRANS (@lem5393880 _69873) (@lem5393887 _69873)). Qed.
Lemma lem5393892 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5393893 (_69874 : int) : (term108 _69874) = (term115 _69874).
Proof. exact (@lem5393892 term63 _69874). Qed.
Lemma lem5393895 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393896 : term117 = term118.
Proof. exact (@lem5393895 (NUMERAL 0)). Qed.
Lemma lem5393897 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5393898 : term119 = term120.
Proof. exact (MK_COMB (@lem5393897) (@lem5393896)). Qed.
Lemma lem5393899 (_69874 : int) : (real_of_int _69874) = (real_of_int _69874).
Proof. exact (eq_refl (real_of_int _69874)). Qed.
Lemma lem5393900 (_69874 : int) : (term115 _69874) = (term121 _69874).
Proof. exact (MK_COMB (@lem5393898) (@lem5393899 _69874)). Qed.
Lemma lem5393902 (_69874 : int) : (term108 _69874) = (term121 _69874).
Proof. exact (TRANS (@lem5393893 _69874) (@lem5393900 _69874)). Qed.
Lemma lem5393905 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5393906 (_69874 : int) (_69873 : int) : ((term79 _69874) = (term79 _69873)) = ((term122 _69874) = (term122 _69873)).
Proof. exact (@lem5393905 (term79 _69874) (term79 _69873)). Qed.
Lemma lem5393910 (x : int) (y : int) : (term123 x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5393911 (_69874 : int) : (term122 _69874) = (term125 _69874).
Proof. exact (@lem5393910 _69874 term57). Qed.
Lemma lem5393913 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393914 : term126 = term127.
Proof. exact (@lem5393913 term7). Qed.
Lemma lem5393915 (_69874 : int) : (term128 _69874) = (term128 _69874).
Proof. exact (eq_refl (term128 _69874)). Qed.
Lemma lem5393916 (_69874 : int) : (term125 _69874) = (term129 _69874).
Proof. exact (MK_COMB (@lem5393915 _69874) (@lem5393914)). Qed.
Lemma lem5393917 (_69874 : int) : (term122 _69874) = (term129 _69874).
Proof. exact (TRANS (@lem5393911 _69874) (@lem5393916 _69874)). Qed.
Lemma lem5393918 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5393919 (_69874 : int) : (term130 _69874) = (term131 _69874).
Proof. exact (MK_COMB (@lem5393918) (@lem5393917 _69874)). Qed.
Lemma lem5393921 (x : int) (y : int) : (term123 x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5393922 (_69873 : int) : (term122 _69873) = (term125 _69873).
Proof. exact (@lem5393921 _69873 term57). Qed.
Lemma lem5393924 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393925 : term126 = term127.
Proof. exact (@lem5393924 term7). Qed.
Lemma lem5393926 (_69873 : int) : (term128 _69873) = (term128 _69873).
Proof. exact (eq_refl (term128 _69873)). Qed.
Lemma lem5393927 (_69873 : int) : (term125 _69873) = (term129 _69873).
Proof. exact (MK_COMB (@lem5393926 _69873) (@lem5393925)). Qed.
Lemma lem5393928 (_69873 : int) : (term122 _69873) = (term129 _69873).
Proof. exact (TRANS (@lem5393922 _69873) (@lem5393927 _69873)). Qed.
Lemma lem5393929 (_69874 : int) (_69873 : int) : ((term122 _69874) = (term122 _69873)) = ((term129 _69874) = (term129 _69873)).
Proof. exact (MK_COMB (@lem5393919 _69874) (@lem5393928 _69873)). Qed.
Lemma lem5393931 (_69874 : int) (_69873 : int) : ((term79 _69874) = (term79 _69873)) = ((term129 _69874) = (term129 _69873)).
Proof. exact (TRANS (@lem5393906 _69874 _69873) (@lem5393929 _69874 _69873)). Qed.
Lemma lem5393933 (x : int) (y : int) : (int_lt x y) = (term132 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem5393934 (_69874 : int) : (term81 _69874) = (term133 _69874).
Proof. exact (@lem5393933 (term79 _69874) term57). Qed.
Lemma lem5393936 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5393937 (_69874 : int) : (term133 _69874) = (term134 _69874).
Proof. exact (@lem5393936 (term135 _69874) term57). Qed.
Lemma lem5393939 (x : int) (y : int) : (term123 x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5393940 (_69874 : int) : (term136 _69874) = (term137 _69874).
Proof. exact (@lem5393939 (term79 _69874) term57). Qed.
Lemma lem5393942 (x : int) (y : int) : (term123 x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5393943 (_69874 : int) : (term122 _69874) = (term125 _69874).
Proof. exact (@lem5393942 _69874 term57). Qed.
Lemma lem5393945 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393946 : term126 = term127.
Proof. exact (@lem5393945 term7). Qed.
Lemma lem5393947 (_69874 : int) : (term128 _69874) = (term128 _69874).
Proof. exact (eq_refl (term128 _69874)). Qed.
Lemma lem5393948 (_69874 : int) : (term125 _69874) = (term129 _69874).
Proof. exact (MK_COMB (@lem5393947 _69874) (@lem5393946)). Qed.
Lemma lem5393949 (_69874 : int) : (term122 _69874) = (term129 _69874).
Proof. exact (TRANS (@lem5393943 _69874) (@lem5393948 _69874)). Qed.
Lemma lem5393950 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5393951 (_69874 : int) : (term138 _69874) = (term139 _69874).
Proof. exact (MK_COMB (@lem5393950) (@lem5393949 _69874)). Qed.
Lemma lem5393953 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393954 : term126 = term127.
Proof. exact (@lem5393953 term7). Qed.
Lemma lem5393955 (_69874 : int) : (term137 _69874) = (term140 _69874).
Proof. exact (MK_COMB (@lem5393951 _69874) (@lem5393954)). Qed.
Lemma lem5393956 (_69874 : int) : (term136 _69874) = (term140 _69874).
Proof. exact (TRANS (@lem5393940 _69874) (@lem5393955 _69874)). Qed.
Lemma lem5393957 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5393958 (_69874 : int) : (term141 _69874) = (term142 _69874).
Proof. exact (MK_COMB (@lem5393957) (@lem5393956 _69874)). Qed.
Lemma lem5393960 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393961 : term126 = term127.
Proof. exact (@lem5393960 term7). Qed.
Lemma lem5393962 (_69874 : int) : (term134 _69874) = (term143 _69874).
Proof. exact (MK_COMB (@lem5393958 _69874) (@lem5393961)). Qed.
Lemma lem5393963 (_69874 : int) : (term133 _69874) = (term143 _69874).
Proof. exact (TRANS (@lem5393937 _69874) (@lem5393962 _69874)). Qed.
Lemma lem5393964 (_69874 : int) : (term81 _69874) = (term143 _69874).
Proof. exact (TRANS (@lem5393934 _69874) (@lem5393963 _69874)). Qed.
Lemma lem5393967 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem5393968 (_69873 : int) : (_69873 = term63) = ((real_of_int _69873) = term117).
Proof. exact (@lem5393967 _69873 term63). Qed.
Lemma lem5393972 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393973 : term117 = term118.
Proof. exact (@lem5393972 (NUMERAL 0)). Qed.
Lemma lem5393974 (_69873 : int) : (term144 _69873) = (term144 _69873).
Proof. exact (eq_refl (term144 _69873)). Qed.
Lemma lem5393975 (_69873 : int) : ((real_of_int _69873) = term117) = ((real_of_int _69873) = term118).
Proof. exact (MK_COMB (@lem5393974 _69873) (@lem5393973)). Qed.
Lemma lem5393977 (_69873 : int) : (_69873 = term63) = ((real_of_int _69873) = term118).
Proof. exact (TRANS (@lem5393968 _69873) (@lem5393975 _69873)). Qed.
Lemma lem5393978 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5393979 (_69874 : int) : (term84 _69874) = (term145 _69874).
Proof. exact (MK_COMB (@lem5393978) (@lem5393964 _69874)). Qed.
Lemma lem5393980 (_69874 : int) (_69873 : int) : (term86 _69874 _69873) = (term146 _69874 _69873).
Proof. exact (MK_COMB (@lem5393979 _69874) (@lem5393977 _69873)). Qed.
Lemma lem5393981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5393982 (_69874 : int) (_69873 : int) : (term91 _69874 _69873) = (term147 _69874 _69873).
Proof. exact (MK_COMB (@lem5393981) (@lem5393931 _69874 _69873)). Qed.
Lemma lem5393983 (_69874 : int) (_69873 : int) : (term93 _69874 _69873) = (term148 _69874 _69873).
Proof. exact (MK_COMB (@lem5393982 _69874 _69873) (@lem5393980 _69874 _69873)). Qed.
Lemma lem5393985 (y : int) (x : int) : (term97 x y) = (term149 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem5393986 (_69874 : int) (_69873 : int) : (term97 _69873 _69874) = (term149 _69874 _69873).
Proof. exact (@lem5393985 _69874 _69873). Qed.
Lemma lem5393988 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5393989 (_69873 : int) (_69874 : int) : (term132 _69873 _69874) = (term150 _69873 _69874).
Proof. exact (@lem5393988 (term79 _69873) _69874). Qed.
Lemma lem5393991 (x : int) (y : int) : (term123 x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5393992 (_69873 : int) : (term122 _69873) = (term125 _69873).
Proof. exact (@lem5393991 _69873 term57). Qed.
Lemma lem5393994 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5393995 : term126 = term127.
Proof. exact (@lem5393994 term7). Qed.
Lemma lem5393996 (_69873 : int) : (term128 _69873) = (term128 _69873).
Proof. exact (eq_refl (term128 _69873)). Qed.
Lemma lem5393997 (_69873 : int) : (term125 _69873) = (term129 _69873).
Proof. exact (MK_COMB (@lem5393996 _69873) (@lem5393995)). Qed.
Lemma lem5393998 (_69873 : int) : (term122 _69873) = (term129 _69873).
Proof. exact (TRANS (@lem5393992 _69873) (@lem5393997 _69873)). Qed.
Lemma lem5393999 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5394000 (_69873 : int) : (term151 _69873) = (term152 _69873).
Proof. exact (MK_COMB (@lem5393999) (@lem5393998 _69873)). Qed.
Lemma lem5394001 (_69874 : int) : (real_of_int _69874) = (real_of_int _69874).
Proof. exact (eq_refl (real_of_int _69874)). Qed.
Lemma lem5394002 (_69873 : int) (_69874 : int) : (term150 _69873 _69874) = (term153 _69873 _69874).
Proof. exact (MK_COMB (@lem5394000 _69873) (@lem5394001 _69874)). Qed.
Lemma lem5394003 (_69873 : int) (_69874 : int) : (term132 _69873 _69874) = (term153 _69873 _69874).
Proof. exact (TRANS (@lem5393989 _69873 _69874) (@lem5394002 _69873 _69874)). Qed.
Lemma lem5394004 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5394005 (_69873 : int) (_69874 : int) : (term154 _69873 _69874) = (term155 _69873 _69874).
Proof. exact (MK_COMB (@lem5394004) (@lem5394003 _69873 _69874)). Qed.
Lemma lem5394007 (x : int) (y : int) : (int_le x y) = (term114 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem5394008 (_69874 : int) (_69873 : int) : (term132 _69874 _69873) = (term150 _69874 _69873).
Proof. exact (@lem5394007 (term79 _69874) _69873). Qed.
Lemma lem5394010 (x : int) (y : int) : (term123 x y) = (term124 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem5394011 (_69874 : int) : (term122 _69874) = (term125 _69874).
Proof. exact (@lem5394010 _69874 term57). Qed.
Lemma lem5394013 (n : nat) : (term116 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem5394014 : term126 = term127.
Proof. exact (@lem5394013 term7). Qed.
Lemma lem5394015 (_69874 : int) : (term128 _69874) = (term128 _69874).
Proof. exact (eq_refl (term128 _69874)). Qed.
Lemma lem5394016 (_69874 : int) : (term125 _69874) = (term129 _69874).
Proof. exact (MK_COMB (@lem5394015 _69874) (@lem5394014)). Qed.
Lemma lem5394017 (_69874 : int) : (term122 _69874) = (term129 _69874).
Proof. exact (TRANS (@lem5394011 _69874) (@lem5394016 _69874)). Qed.
Lemma lem5394018 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5394019 (_69874 : int) : (term151 _69874) = (term152 _69874).
Proof. exact (MK_COMB (@lem5394018) (@lem5394017 _69874)). Qed.
Lemma lem5394020 (_69873 : int) : (real_of_int _69873) = (real_of_int _69873).
Proof. exact (eq_refl (real_of_int _69873)). Qed.
Lemma lem5394021 (_69874 : int) (_69873 : int) : (term150 _69874 _69873) = (term153 _69874 _69873).
Proof. exact (MK_COMB (@lem5394019 _69874) (@lem5394020 _69873)). Qed.
Lemma lem5394022 (_69874 : int) (_69873 : int) : (term132 _69874 _69873) = (term153 _69874 _69873).
Proof. exact (TRANS (@lem5394008 _69874 _69873) (@lem5394021 _69874 _69873)). Qed.
Lemma lem5394023 (_69874 : int) (_69873 : int) : (term149 _69874 _69873) = (term156 _69874 _69873).
Proof. exact (MK_COMB (@lem5394005 _69873 _69874) (@lem5394022 _69874 _69873)). Qed.
Lemma lem5394024 (_69874 : int) (_69873 : int) : (term97 _69873 _69874) = (term156 _69874 _69873).
Proof. exact (TRANS (@lem5393986 _69874 _69873) (@lem5394023 _69874 _69873)). Qed.
Lemma lem5394025 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5394026 (_69874 : int) (_69873 : int) : (term99 _69874 _69873) = (term157 _69874 _69873).
Proof. exact (MK_COMB (@lem5394025) (@lem5393983 _69874 _69873)). Qed.
Lemma lem5394027 (_69874 : int) (_69873 : int) : (term101 _69873 _69874) = (term158 _69874 _69873).
Proof. exact (MK_COMB (@lem5394026 _69874 _69873) (@lem5394024 _69874 _69873)). Qed.
Lemma lem5394028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5394029 (_69874 : int) : (term104 _69874) = (term159 _69874).
Proof. exact (MK_COMB (@lem5394028) (@lem5393902 _69874)). Qed.
Lemma lem5394030 (_69874 : int) (_69873 : int) : (term106 _69873 _69874) = (term160 _69874 _69873).
Proof. exact (MK_COMB (@lem5394029 _69874) (@lem5394027 _69874 _69873)). Qed.
Lemma lem5394031 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5394032 (_69873 : int) : (term104 _69873) = (term159 _69873).
Proof. exact (MK_COMB (@lem5394031) (@lem5393889 _69873)). Qed.
Lemma lem5394033 (_69874 : int) (_69873 : int) : (term111 _69873 _69874) = (term161 _69874 _69873).
Proof. exact (MK_COMB (@lem5394032 _69873) (@lem5394030 _69874 _69873)). Qed.
Lemma lem5394034 (_69874 : int) (_69873 : int) : (term112 _69873 _69874) = (term161 _69874 _69873).
Proof. exact (TRANS (@lem5393876 _69873 _69874) (@lem5394033 _69874 _69873)). Qed.
Lemma lem5394038 (t : Prop) : (term162 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5394104 (_69874 : int) (_69873 : int) : (term163 _69874 _69873) = (term161 _69874 _69873).
Proof. exact (@lem5394038 (term161 _69874 _69873)). Qed.
Lemma lem5394105 (_69873 : int) : (term121 _69873) = (term164 _69873).
Proof. exact (@lem1988287 (real_of_int _69873) term118). Qed.
Lemma lem5394111 (_69873 : int) : (term165 _69873) = (term166 _69873).
Proof. exact (@lem1982792 (real_of_int _69873) term118). Qed.
Lemma lem5394113 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394114 : term118 = term168.
Proof. exact (@lem5394113 (NUMERAL 0)). Qed.
Lemma lem5394116 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394117 : term171 = term172.
Proof. exact (@lem5394116 term7). Qed.
Lemma lem5394118 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394119 : term173 = term174.
Proof. exact (MK_COMB (@lem5394118) (@lem5394117)). Qed.
Lemma lem5394120 : term175 = term176.
Proof. exact (MK_COMB (@lem5394119) (@lem5394114)). Qed.
Lemma lem5394121 : term176 = term177.
Proof. exact (@lem1981613 term171 term118 term127 term127). Qed.
Lemma lem5394123 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394124 : term180 = term181.
Proof. exact (@lem5394123 term7 term7). Qed.
Lemma lem5394125 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394126 : term183 = term7.
Proof. exact (EQ_MP (@lem5394125) (@lem940073)). Qed.
Lemma lem5394127 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394128 : term181 = term127.
Proof. exact (MK_COMB (@lem5394127) (@lem5394126)). Qed.
Lemma lem5394129 : term180 = term127.
Proof. exact (TRANS (@lem5394124) (@lem5394128)). Qed.
Lemma lem5394131 (x : nat) : (term184 x) = term118.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5394132 : term175 = term118.
Proof. exact (@lem5394131 term7). Qed.
Lemma lem5394133 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5394134 : term185 = term186.
Proof. exact (MK_COMB (@lem5394133) (@lem5394132)). Qed.
Lemma lem5394135 : term177 = term168.
Proof. exact (MK_COMB (@lem5394134) (@lem5394129)). Qed.
Lemma lem5394136 : term176 = term168.
Proof. exact (TRANS (@lem5394121) (@lem5394135)). Qed.
Lemma lem5394137 : term175 = term168.
Proof. exact (TRANS (@lem5394120) (@lem5394136)). Qed.
Lemma lem5394139 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5394140 : term168 = term118.
Proof. exact (@lem5394139 term118). Qed.
Lemma lem5394141 : term175 = term118.
Proof. exact (TRANS (@lem5394137) (@lem5394140)). Qed.
Lemma lem5394142 (_69873 : int) : (term128 _69873) = (term128 _69873).
Proof. exact (eq_refl (term128 _69873)). Qed.
Lemma lem5394143 (_69873 : int) : (term166 _69873) = (term188 _69873).
Proof. exact (MK_COMB (@lem5394142 _69873) (@lem5394141)). Qed.
Lemma lem5394144 (_69873 : int) : (term188 _69873) = (real_of_int _69873).
Proof. exact (@lem1982723 (real_of_int _69873)). Qed.
Lemma lem5394145 (_69873 : int) : (term166 _69873) = (real_of_int _69873).
Proof. exact (TRANS (@lem5394143 _69873) (@lem5394144 _69873)). Qed.
Lemma lem5394147 (_69873 : int) : (term165 _69873) = (real_of_int _69873).
Proof. exact (TRANS (@lem5394111 _69873) (@lem5394145 _69873)). Qed.
Lemma lem5394148 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5394149 (_69873 : int) : (term189 _69873) = (term190 _69873).
Proof. exact (MK_COMB (@lem5394148) (@lem5394147 _69873)). Qed.
Lemma lem5394150 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5394151 (_69873 : int) : (term164 _69873) = (term191 _69873).
Proof. exact (MK_COMB (@lem5394149 _69873) (@lem5394150)). Qed.
Lemma lem5394152 (_69873 : int) : (term121 _69873) = (term191 _69873).
Proof. exact (TRANS (@lem5394105 _69873) (@lem5394151 _69873)). Qed.
Lemma lem5394153 (_69874 : int) : (term121 _69874) = (term164 _69874).
Proof. exact (@lem1988287 (real_of_int _69874) term118). Qed.
Lemma lem5394159 (_69874 : int) : (term165 _69874) = (term166 _69874).
Proof. exact (@lem1982792 (real_of_int _69874) term118). Qed.
Lemma lem5394161 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394162 : term118 = term168.
Proof. exact (@lem5394161 (NUMERAL 0)). Qed.
Lemma lem5394164 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394165 : term171 = term172.
Proof. exact (@lem5394164 term7). Qed.
Lemma lem5394166 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394167 : term173 = term174.
Proof. exact (MK_COMB (@lem5394166) (@lem5394165)). Qed.
Lemma lem5394168 : term175 = term176.
Proof. exact (MK_COMB (@lem5394167) (@lem5394162)). Qed.
Lemma lem5394169 : term176 = term177.
Proof. exact (@lem1981613 term171 term118 term127 term127). Qed.
Lemma lem5394171 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394172 : term180 = term181.
Proof. exact (@lem5394171 term7 term7). Qed.
Lemma lem5394173 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394174 : term183 = term7.
Proof. exact (EQ_MP (@lem5394173) (@lem940073)). Qed.
Lemma lem5394175 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394176 : term181 = term127.
Proof. exact (MK_COMB (@lem5394175) (@lem5394174)). Qed.
Lemma lem5394177 : term180 = term127.
Proof. exact (TRANS (@lem5394172) (@lem5394176)). Qed.
Lemma lem5394179 (x : nat) : (term184 x) = term118.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5394180 : term175 = term118.
Proof. exact (@lem5394179 term7). Qed.
Lemma lem5394181 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5394182 : term185 = term186.
Proof. exact (MK_COMB (@lem5394181) (@lem5394180)). Qed.
Lemma lem5394183 : term177 = term168.
Proof. exact (MK_COMB (@lem5394182) (@lem5394177)). Qed.
Lemma lem5394184 : term176 = term168.
Proof. exact (TRANS (@lem5394169) (@lem5394183)). Qed.
Lemma lem5394185 : term175 = term168.
Proof. exact (TRANS (@lem5394168) (@lem5394184)). Qed.
Lemma lem5394187 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5394188 : term168 = term118.
Proof. exact (@lem5394187 term118). Qed.
Lemma lem5394189 : term175 = term118.
Proof. exact (TRANS (@lem5394185) (@lem5394188)). Qed.
Lemma lem5394190 (_69874 : int) : (term128 _69874) = (term128 _69874).
Proof. exact (eq_refl (term128 _69874)). Qed.
Lemma lem5394191 (_69874 : int) : (term166 _69874) = (term188 _69874).
Proof. exact (MK_COMB (@lem5394190 _69874) (@lem5394189)). Qed.
Lemma lem5394192 (_69874 : int) : (term188 _69874) = (real_of_int _69874).
Proof. exact (@lem1982723 (real_of_int _69874)). Qed.
Lemma lem5394193 (_69874 : int) : (term166 _69874) = (real_of_int _69874).
Proof. exact (TRANS (@lem5394191 _69874) (@lem5394192 _69874)). Qed.
Lemma lem5394195 (_69874 : int) : (term165 _69874) = (real_of_int _69874).
Proof. exact (TRANS (@lem5394159 _69874) (@lem5394193 _69874)). Qed.
Lemma lem5394196 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5394197 (_69874 : int) : (term189 _69874) = (term190 _69874).
Proof. exact (MK_COMB (@lem5394196) (@lem5394195 _69874)). Qed.
Lemma lem5394198 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5394199 (_69874 : int) : (term164 _69874) = (term191 _69874).
Proof. exact (MK_COMB (@lem5394197 _69874) (@lem5394198)). Qed.
Lemma lem5394200 (_69874 : int) : (term121 _69874) = (term191 _69874).
Proof. exact (TRANS (@lem5394153 _69874) (@lem5394199 _69874)). Qed.
Lemma lem5394201 (_69874 : int) (_69873 : int) : ((term129 _69874) = (term129 _69873)) = ((term192 _69874 _69873) = term118).
Proof. exact (@lem1988293 (term129 _69874) (term129 _69873)). Qed.
Lemma lem5394219 (_69874 : int) (_69873 : int) : (term192 _69874 _69873) = (term193 _69874 _69873).
Proof. exact (@lem1982792 (term129 _69874) (term129 _69873)). Qed.
Lemma lem5394220 (_69873 : int) : (term194 _69873) = (term195 _69873).
Proof. exact (@lem1982781 (real_of_int _69873) term171 term127). Qed.
Lemma lem5394222 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394223 : term127 = term196.
Proof. exact (@lem5394222 term7). Qed.
Lemma lem5394225 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394226 : term171 = term172.
Proof. exact (@lem5394225 term7). Qed.
Lemma lem5394227 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394228 : term173 = term174.
Proof. exact (MK_COMB (@lem5394227) (@lem5394226)). Qed.
Lemma lem5394229 : term197 = term198.
Proof. exact (MK_COMB (@lem5394228) (@lem5394223)). Qed.
Lemma lem5394230 : term198 = term199.
Proof. exact (@lem1981613 term171 term127 term127 term127). Qed.
Lemma lem5394232 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394233 : term180 = term181.
Proof. exact (@lem5394232 term7 term7). Qed.
Lemma lem5394234 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394235 : term183 = term7.
Proof. exact (EQ_MP (@lem5394234) (@lem940073)). Qed.
Lemma lem5394236 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394237 : term181 = term127.
Proof. exact (MK_COMB (@lem5394236) (@lem5394235)). Qed.
Lemma lem5394238 : term180 = term127.
Proof. exact (TRANS (@lem5394233) (@lem5394237)). Qed.
Lemma lem5394240 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394241 : term197 = term202.
Proof. exact (@lem5394240 term7 term7). Qed.
Lemma lem5394242 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394243 : term183 = term7.
Proof. exact (EQ_MP (@lem5394242) (@lem940073)). Qed.
Lemma lem5394244 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394245 : term181 = term127.
Proof. exact (MK_COMB (@lem5394244) (@lem5394243)). Qed.
Lemma lem5394246 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394247 : term202 = term171.
Proof. exact (MK_COMB (@lem5394246) (@lem5394245)). Qed.
Lemma lem5394248 : term197 = term171.
Proof. exact (TRANS (@lem5394241) (@lem5394247)). Qed.
Lemma lem5394249 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5394250 : term203 = term204.
Proof. exact (MK_COMB (@lem5394249) (@lem5394248)). Qed.
Lemma lem5394251 : term199 = term172.
Proof. exact (MK_COMB (@lem5394250) (@lem5394238)). Qed.
Lemma lem5394252 : term198 = term172.
Proof. exact (TRANS (@lem5394230) (@lem5394251)). Qed.
Lemma lem5394253 : term197 = term172.
Proof. exact (TRANS (@lem5394229) (@lem5394252)). Qed.
Lemma lem5394255 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5394256 : term172 = term171.
Proof. exact (@lem5394255 term171). Qed.
Lemma lem5394257 : term197 = term171.
Proof. exact (TRANS (@lem5394253) (@lem5394256)). Qed.
Lemma lem5394260 (_69873 : int) : (term205 _69873) = (term205 _69873).
Proof. exact (eq_refl (term205 _69873)). Qed.
Lemma lem5394261 (_69873 : int) : (term195 _69873) = (term206 _69873).
Proof. exact (MK_COMB (@lem5394260 _69873) (@lem5394257)). Qed.
Lemma lem5394262 (_69873 : int) : (term194 _69873) = (term206 _69873).
Proof. exact (TRANS (@lem5394220 _69873) (@lem5394261 _69873)). Qed.
Lemma lem5394263 (_69874 : int) : (term139 _69874) = (term139 _69874).
Proof. exact (eq_refl (term139 _69874)). Qed.
Lemma lem5394264 (_69874 : int) (_69873 : int) : (term193 _69874 _69873) = (term207 _69874 _69873).
Proof. exact (MK_COMB (@lem5394263 _69874) (@lem5394262 _69873)). Qed.
Lemma lem5394265 (_69873 : int) (_69874 : int) : (term207 _69874 _69873) = (term208 _69873 _69874).
Proof. exact (@lem1982757 (term209 _69873) (term129 _69874) term171). Qed.
Lemma lem5394266 (_69874 : int) : (term210 _69874) = (term211 _69874).
Proof. exact (@lem1982755 (real_of_int _69874) term127 term171). Qed.
Lemma lem5394268 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394269 : term171 = term172.
Proof. exact (@lem5394268 term7). Qed.
Lemma lem5394271 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394272 : term127 = term196.
Proof. exact (@lem5394271 term7). Qed.
Lemma lem5394273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5394274 : term212 = term213.
Proof. exact (MK_COMB (@lem5394273) (@lem5394272)). Qed.
Lemma lem5394275 : term214 = term215.
Proof. exact (MK_COMB (@lem5394274) (@lem5394269)). Qed.
Lemma lem5394276 : term216.
Proof. exact (@lem1981473 term127 term127 term171 term127 term118 term127). Qed.
Lemma lem5394278 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394279 : term218 = term219.
Proof. exact (@lem5394278 (NUMERAL 0) term7). Qed.
Lemma lem5394280 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394281 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394282 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394281 h1) (fun h1 : term219 = True => @lem5394280)). Qed.
Lemma lem5394283 : term219 = True.
Proof. exact (EQ_MP (@lem5394282) (@lem5394280)). Qed.
Lemma lem5394284 : term218 = True.
Proof. exact (TRANS (@lem5394279) (@lem5394283)). Qed.
Lemma lem5394285 : True = term218.
Proof. exact (SYM (@lem5394284)). Qed.
Lemma lem5394286 : term218.
Proof. exact (EQ_MP (@lem5394285) (@lem0)). Qed.
Lemma lem5394287 : term221.
Proof. exact (@lem5394276 (@lem5394286)). Qed.
Lemma lem5394289 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394290 : term218 = term219.
Proof. exact (@lem5394289 (NUMERAL 0) term7). Qed.
Lemma lem5394291 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394292 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394293 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394292 h1) (fun h1 : term219 = True => @lem5394291)). Qed.
Lemma lem5394294 : term219 = True.
Proof. exact (EQ_MP (@lem5394293) (@lem5394291)). Qed.
Lemma lem5394295 : term218 = True.
Proof. exact (TRANS (@lem5394290) (@lem5394294)). Qed.
Lemma lem5394296 : True = term218.
Proof. exact (SYM (@lem5394295)). Qed.
Lemma lem5394297 : term218.
Proof. exact (EQ_MP (@lem5394296) (@lem0)). Qed.
Lemma lem5394298 : term222.
Proof. exact (@lem5394287 (@lem5394297)). Qed.
Lemma lem5394300 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394301 : term218 = term219.
Proof. exact (@lem5394300 (NUMERAL 0) term7). Qed.
Lemma lem5394302 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394303 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394304 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394303 h1) (fun h1 : term219 = True => @lem5394302)). Qed.
Lemma lem5394305 : term219 = True.
Proof. exact (EQ_MP (@lem5394304) (@lem5394302)). Qed.
Lemma lem5394306 : term218 = True.
Proof. exact (TRANS (@lem5394301) (@lem5394305)). Qed.
Lemma lem5394307 : True = term218.
Proof. exact (SYM (@lem5394306)). Qed.
Lemma lem5394308 : term218.
Proof. exact (EQ_MP (@lem5394307) (@lem0)). Qed.
Lemma lem5394309 : term223.
Proof. exact (@lem5394298 (@lem5394308)). Qed.
Lemma lem5394311 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394312 : term197 = term202.
Proof. exact (@lem5394311 term7 term7). Qed.
Lemma lem5394313 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394314 : term183 = term7.
Proof. exact (EQ_MP (@lem5394313) (@lem940073)). Qed.
Lemma lem5394315 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394316 : term181 = term127.
Proof. exact (MK_COMB (@lem5394315) (@lem5394314)). Qed.
Lemma lem5394317 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394318 : term202 = term171.
Proof. exact (MK_COMB (@lem5394317) (@lem5394316)). Qed.
Lemma lem5394319 : term197 = term171.
Proof. exact (TRANS (@lem5394312) (@lem5394318)). Qed.
Lemma lem5394321 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394322 : term180 = term181.
Proof. exact (@lem5394321 term7 term7). Qed.
Lemma lem5394323 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394324 : term183 = term7.
Proof. exact (EQ_MP (@lem5394323) (@lem940073)). Qed.
Lemma lem5394325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394326 : term181 = term127.
Proof. exact (MK_COMB (@lem5394325) (@lem5394324)). Qed.
Lemma lem5394327 : term180 = term127.
Proof. exact (TRANS (@lem5394322) (@lem5394326)). Qed.
Lemma lem5394328 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5394329 : term224 = term212.
Proof. exact (MK_COMB (@lem5394328) (@lem5394327)). Qed.
Lemma lem5394330 : term225 = term214.
Proof. exact (MK_COMB (@lem5394329) (@lem5394319)). Qed.
Lemma lem5394332 (m : nat) : (term226 m) = term118.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem5394333 : term214 = term118.
Proof. exact (@lem5394332 term7). Qed.
Lemma lem5394334 : term225 = term118.
Proof. exact (TRANS (@lem5394330) (@lem5394333)). Qed.
Lemma lem5394335 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394336 : term227 = term228.
Proof. exact (MK_COMB (@lem5394335) (@lem5394334)). Qed.
Lemma lem5394337 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5394338 : term229 = term230.
Proof. exact (MK_COMB (@lem5394336) (@lem5394337)). Qed.
Lemma lem5394340 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5394341 : term230 = term118.
Proof. exact (@lem5394340 term7). Qed.
Lemma lem5394342 : term229 = term118.
Proof. exact (TRANS (@lem5394338) (@lem5394341)). Qed.
Lemma lem5394344 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394345 : term180 = term181.
Proof. exact (@lem5394344 term7 term7). Qed.
Lemma lem5394346 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394347 : term183 = term7.
Proof. exact (EQ_MP (@lem5394346) (@lem940073)). Qed.
Lemma lem5394348 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394349 : term181 = term127.
Proof. exact (MK_COMB (@lem5394348) (@lem5394347)). Qed.
Lemma lem5394350 : term180 = term127.
Proof. exact (TRANS (@lem5394345) (@lem5394349)). Qed.
Lemma lem5394351 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5394352 : term232 = term230.
Proof. exact (MK_COMB (@lem5394351) (@lem5394350)). Qed.
Lemma lem5394354 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5394355 : term230 = term118.
Proof. exact (@lem5394354 term7). Qed.
Lemma lem5394356 : term232 = term118.
Proof. exact (TRANS (@lem5394352) (@lem5394355)). Qed.
Lemma lem5394357 : term118 = term232.
Proof. exact (SYM (@lem5394356)). Qed.
Lemma lem5394358 : term229 = term232.
Proof. exact (TRANS (@lem5394342) (@lem5394357)). Qed.
Lemma lem5394359 : term215 = term168.
Proof. exact (@lem5394309 (@lem5394358)). Qed.
Lemma lem5394360 : term214 = term168.
Proof. exact (TRANS (@lem5394275) (@lem5394359)). Qed.
Lemma lem5394362 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5394363 : term168 = term118.
Proof. exact (@lem5394362 term118). Qed.
Lemma lem5394364 : term214 = term118.
Proof. exact (TRANS (@lem5394360) (@lem5394363)). Qed.
Lemma lem5394365 (_69874 : int) : (term128 _69874) = (term128 _69874).
Proof. exact (eq_refl (term128 _69874)). Qed.
Lemma lem5394366 (_69874 : int) : (term211 _69874) = (term188 _69874).
Proof. exact (MK_COMB (@lem5394365 _69874) (@lem5394364)). Qed.
Lemma lem5394367 (_69874 : int) : (term210 _69874) = (term188 _69874).
Proof. exact (TRANS (@lem5394266 _69874) (@lem5394366 _69874)). Qed.
Lemma lem5394368 (_69874 : int) : (term188 _69874) = (real_of_int _69874).
Proof. exact (@lem1982723 (real_of_int _69874)). Qed.
Lemma lem5394369 (_69874 : int) : (term210 _69874) = (real_of_int _69874).
Proof. exact (TRANS (@lem5394367 _69874) (@lem5394368 _69874)). Qed.
Lemma lem5394370 (_69873 : int) : (term205 _69873) = (term205 _69873).
Proof. exact (eq_refl (term205 _69873)). Qed.
Lemma lem5394371 (_69873 : int) (_69874 : int) : (term208 _69873 _69874) = (term233 _69873 _69874).
Proof. exact (MK_COMB (@lem5394370 _69873) (@lem5394369 _69874)). Qed.
Lemma lem5394372 (_69873 : int) (_69874 : int) : (term207 _69874 _69873) = (term233 _69873 _69874).
Proof. exact (TRANS (@lem5394265 _69873 _69874) (@lem5394371 _69873 _69874)). Qed.
Lemma lem5394373 (_69873 : int) (_69874 : int) : (term193 _69874 _69873) = (term233 _69873 _69874).
Proof. exact (TRANS (@lem5394264 _69874 _69873) (@lem5394372 _69873 _69874)). Qed.
Lemma lem5394375 (_69873 : int) (_69874 : int) : (term192 _69874 _69873) = (term233 _69873 _69874).
Proof. exact (TRANS (@lem5394219 _69874 _69873) (@lem5394373 _69873 _69874)). Qed.
Lemma lem5394376 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5394377 (_69873 : int) (_69874 : int) : (term234 _69874 _69873) = (term235 _69873 _69874).
Proof. exact (MK_COMB (@lem5394376) (@lem5394375 _69873 _69874)). Qed.
Lemma lem5394378 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5394379 (_69873 : int) (_69874 : int) : ((term192 _69874 _69873) = term118) = ((term233 _69873 _69874) = term118).
Proof. exact (MK_COMB (@lem5394377 _69873 _69874) (@lem5394378)). Qed.
Lemma lem5394380 (_69873 : int) (_69874 : int) : ((term129 _69874) = (term129 _69873)) = ((term233 _69873 _69874) = term118).
Proof. exact (TRANS (@lem5394201 _69874 _69873) (@lem5394379 _69873 _69874)). Qed.
Lemma lem5394381 (_69874 : int) : (term143 _69874) = (term236 _69874).
Proof. exact (@lem1988287 term127 (term140 _69874)). Qed.
Lemma lem5394393 (_69874 : int) : (term140 _69874) = (term237 _69874).
Proof. exact (@lem1982755 (real_of_int _69874) term127 term127). Qed.
Lemma lem5394395 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394396 : term127 = term196.
Proof. exact (@lem5394395 term7). Qed.
Lemma lem5394398 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394399 : term127 = term196.
Proof. exact (@lem5394398 term7). Qed.
Lemma lem5394400 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5394401 : term212 = term213.
Proof. exact (MK_COMB (@lem5394400) (@lem5394399)). Qed.
Lemma lem5394402 : term238 = term239.
Proof. exact (MK_COMB (@lem5394401) (@lem5394396)). Qed.
Lemma lem5394403 : term240.
Proof. exact (@lem1981473 term127 term127 term127 term127 term241 term127). Qed.
Lemma lem5394405 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394406 : term218 = term219.
Proof. exact (@lem5394405 (NUMERAL 0) term7). Qed.
Lemma lem5394407 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394408 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394409 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394408 h1) (fun h1 : term219 = True => @lem5394407)). Qed.
Lemma lem5394410 : term219 = True.
Proof. exact (EQ_MP (@lem5394409) (@lem5394407)). Qed.
Lemma lem5394411 : term218 = True.
Proof. exact (TRANS (@lem5394406) (@lem5394410)). Qed.
Lemma lem5394412 : True = term218.
Proof. exact (SYM (@lem5394411)). Qed.
Lemma lem5394413 : term218.
Proof. exact (EQ_MP (@lem5394412) (@lem0)). Qed.
Lemma lem5394414 : term242.
Proof. exact (@lem5394403 (@lem5394413)). Qed.
Lemma lem5394416 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394417 : term218 = term219.
Proof. exact (@lem5394416 (NUMERAL 0) term7). Qed.
Lemma lem5394418 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394419 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394420 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394419 h1) (fun h1 : term219 = True => @lem5394418)). Qed.
Lemma lem5394421 : term219 = True.
Proof. exact (EQ_MP (@lem5394420) (@lem5394418)). Qed.
Lemma lem5394422 : term218 = True.
Proof. exact (TRANS (@lem5394417) (@lem5394421)). Qed.
Lemma lem5394423 : True = term218.
Proof. exact (SYM (@lem5394422)). Qed.
Lemma lem5394424 : term218.
Proof. exact (EQ_MP (@lem5394423) (@lem0)). Qed.
Lemma lem5394425 : term243.
Proof. exact (@lem5394414 (@lem5394424)). Qed.
Lemma lem5394427 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394428 : term218 = term219.
Proof. exact (@lem5394427 (NUMERAL 0) term7). Qed.
Lemma lem5394429 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394430 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394431 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394430 h1) (fun h1 : term219 = True => @lem5394429)). Qed.
Lemma lem5394432 : term219 = True.
Proof. exact (EQ_MP (@lem5394431) (@lem5394429)). Qed.
Lemma lem5394433 : term218 = True.
Proof. exact (TRANS (@lem5394428) (@lem5394432)). Qed.
Lemma lem5394434 : True = term218.
Proof. exact (SYM (@lem5394433)). Qed.
Lemma lem5394435 : term218.
Proof. exact (EQ_MP (@lem5394434) (@lem0)). Qed.
Lemma lem5394436 : term244.
Proof. exact (@lem5394425 (@lem5394435)). Qed.
Lemma lem5394438 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394439 : term180 = term181.
Proof. exact (@lem5394438 term7 term7). Qed.
Lemma lem5394440 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394441 : term183 = term7.
Proof. exact (EQ_MP (@lem5394440) (@lem940073)). Qed.
Lemma lem5394442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394443 : term181 = term127.
Proof. exact (MK_COMB (@lem5394442) (@lem5394441)). Qed.
Lemma lem5394444 : term180 = term127.
Proof. exact (TRANS (@lem5394439) (@lem5394443)). Qed.
Lemma lem5394446 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394447 : term180 = term181.
Proof. exact (@lem5394446 term7 term7). Qed.
Lemma lem5394448 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394449 : term183 = term7.
Proof. exact (EQ_MP (@lem5394448) (@lem940073)). Qed.
Lemma lem5394450 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394451 : term181 = term127.
Proof. exact (MK_COMB (@lem5394450) (@lem5394449)). Qed.
Lemma lem5394452 : term180 = term127.
Proof. exact (TRANS (@lem5394447) (@lem5394451)). Qed.
Lemma lem5394453 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5394454 : term224 = term212.
Proof. exact (MK_COMB (@lem5394453) (@lem5394452)). Qed.
Lemma lem5394455 : term245 = term238.
Proof. exact (MK_COMB (@lem5394454) (@lem5394444)). Qed.
Lemma lem5394456 : term238 = term246.
Proof. exact (@lem1367770 term7 term7). Qed.
Lemma lem5394457 : term247 = term248.
Proof. exact (@lem706885). Qed.
Lemma lem5394458 : (term247 = term248) = (term249 = term250).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term248). Qed.
Lemma lem5394459 : term249 = term250.
Proof. exact (EQ_MP (@lem5394458) (@lem5394457)). Qed.
Lemma lem5394460 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394461 : term246 = term241.
Proof. exact (MK_COMB (@lem5394460) (@lem5394459)). Qed.
Lemma lem5394462 : term238 = term241.
Proof. exact (TRANS (@lem5394456) (@lem5394461)). Qed.
Lemma lem5394463 : term245 = term241.
Proof. exact (TRANS (@lem5394455) (@lem5394462)). Qed.
Lemma lem5394464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394465 : term251 = term252.
Proof. exact (MK_COMB (@lem5394464) (@lem5394463)). Qed.
Lemma lem5394466 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5394467 : term253 = term254.
Proof. exact (MK_COMB (@lem5394465) (@lem5394466)). Qed.
Lemma lem5394469 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394470 : term254 = term255.
Proof. exact (@lem5394469 term250 term7). Qed.
Lemma lem5394471 : term256 = term248.
Proof. exact (@lem996237 term248). Qed.
Lemma lem5394472 : (term256 = term248) = (term257 = term250).
Proof. exact (@lem1007663 term248 (BIT1 0) term248). Qed.
Lemma lem5394473 : term257 = term250.
Proof. exact (EQ_MP (@lem5394472) (@lem5394471)). Qed.
Lemma lem5394474 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394475 : term255 = term241.
Proof. exact (MK_COMB (@lem5394474) (@lem5394473)). Qed.
Lemma lem5394476 : term254 = term241.
Proof. exact (TRANS (@lem5394470) (@lem5394475)). Qed.
Lemma lem5394477 : term253 = term241.
Proof. exact (TRANS (@lem5394467) (@lem5394476)). Qed.
Lemma lem5394479 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394480 : term180 = term181.
Proof. exact (@lem5394479 term7 term7). Qed.
Lemma lem5394481 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394482 : term183 = term7.
Proof. exact (EQ_MP (@lem5394481) (@lem940073)). Qed.
Lemma lem5394483 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394484 : term181 = term127.
Proof. exact (MK_COMB (@lem5394483) (@lem5394482)). Qed.
Lemma lem5394485 : term180 = term127.
Proof. exact (TRANS (@lem5394480) (@lem5394484)). Qed.
Lemma lem5394486 : term252 = term252.
Proof. exact (eq_refl term252). Qed.
Lemma lem5394487 : term258 = term254.
Proof. exact (MK_COMB (@lem5394486) (@lem5394485)). Qed.
Lemma lem5394489 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394490 : term254 = term255.
Proof. exact (@lem5394489 term250 term7). Qed.
Lemma lem5394491 : term256 = term248.
Proof. exact (@lem996237 term248). Qed.
Lemma lem5394492 : (term256 = term248) = (term257 = term250).
Proof. exact (@lem1007663 term248 (BIT1 0) term248). Qed.
Lemma lem5394493 : term257 = term250.
Proof. exact (EQ_MP (@lem5394492) (@lem5394491)). Qed.
Lemma lem5394494 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394495 : term255 = term241.
Proof. exact (MK_COMB (@lem5394494) (@lem5394493)). Qed.
Lemma lem5394496 : term254 = term241.
Proof. exact (TRANS (@lem5394490) (@lem5394495)). Qed.
Lemma lem5394497 : term258 = term241.
Proof. exact (TRANS (@lem5394487) (@lem5394496)). Qed.
Lemma lem5394498 : term241 = term258.
Proof. exact (SYM (@lem5394497)). Qed.
Lemma lem5394499 : term253 = term258.
Proof. exact (TRANS (@lem5394477) (@lem5394498)). Qed.
Lemma lem5394500 : term239 = term259.
Proof. exact (@lem5394436 (@lem5394499)). Qed.
Lemma lem5394501 : term238 = term259.
Proof. exact (TRANS (@lem5394402) (@lem5394500)). Qed.
Lemma lem5394503 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5394504 : term259 = term241.
Proof. exact (@lem5394503 term241). Qed.
Lemma lem5394505 : term238 = term241.
Proof. exact (TRANS (@lem5394501) (@lem5394504)). Qed.
Lemma lem5394506 (_69874 : int) : (term128 _69874) = (term128 _69874).
Proof. exact (eq_refl (term128 _69874)). Qed.
Lemma lem5394507 (_69874 : int) : (term237 _69874) = (term260 _69874).
Proof. exact (MK_COMB (@lem5394506 _69874) (@lem5394505)). Qed.
Lemma lem5394509 (_69874 : int) : (term140 _69874) = (term260 _69874).
Proof. exact (TRANS (@lem5394393 _69874) (@lem5394507 _69874)). Qed.
Lemma lem5394512 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem5394513 (_69874 : int) : (term262 _69874) = (term263 _69874).
Proof. exact (MK_COMB (@lem5394512) (@lem5394509 _69874)). Qed.
Lemma lem5394514 (_69874 : int) : (term263 _69874) = (term264 _69874).
Proof. exact (@lem1982792 term127 (term260 _69874)). Qed.
Lemma lem5394515 (_69874 : int) : (term265 _69874) = (term266 _69874).
Proof. exact (@lem1982781 (real_of_int _69874) term171 term241). Qed.
Lemma lem5394517 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394518 : term241 = term259.
Proof. exact (@lem5394517 term250). Qed.
Lemma lem5394520 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394521 : term171 = term172.
Proof. exact (@lem5394520 term7). Qed.
Lemma lem5394522 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394523 : term173 = term174.
Proof. exact (MK_COMB (@lem5394522) (@lem5394521)). Qed.
Lemma lem5394524 : term267 = term268.
Proof. exact (MK_COMB (@lem5394523) (@lem5394518)). Qed.
Lemma lem5394525 : term268 = term269.
Proof. exact (@lem1981613 term171 term241 term127 term127). Qed.
Lemma lem5394527 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394528 : term180 = term181.
Proof. exact (@lem5394527 term7 term7). Qed.
Lemma lem5394529 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394530 : term183 = term7.
Proof. exact (EQ_MP (@lem5394529) (@lem940073)). Qed.
Lemma lem5394531 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394532 : term181 = term127.
Proof. exact (MK_COMB (@lem5394531) (@lem5394530)). Qed.
Lemma lem5394533 : term180 = term127.
Proof. exact (TRANS (@lem5394528) (@lem5394532)). Qed.
Lemma lem5394535 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394536 : term267 = term270.
Proof. exact (@lem5394535 term7 term250). Qed.
Lemma lem5394537 : term271 = term248.
Proof. exact (@lem996238 term248). Qed.
Lemma lem5394538 : (term271 = term248) = (term272 = term250).
Proof. exact (@lem1007663 (BIT1 0) term248 term248). Qed.
Lemma lem5394539 : term272 = term250.
Proof. exact (EQ_MP (@lem5394538) (@lem5394537)). Qed.
Lemma lem5394540 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394541 : term273 = term241.
Proof. exact (MK_COMB (@lem5394540) (@lem5394539)). Qed.
Lemma lem5394542 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394543 : term270 = term274.
Proof. exact (MK_COMB (@lem5394542) (@lem5394541)). Qed.
Lemma lem5394544 : term267 = term274.
Proof. exact (TRANS (@lem5394536) (@lem5394543)). Qed.
Lemma lem5394545 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5394546 : term275 = term276.
Proof. exact (MK_COMB (@lem5394545) (@lem5394544)). Qed.
Lemma lem5394547 : term269 = term277.
Proof. exact (MK_COMB (@lem5394546) (@lem5394533)). Qed.
Lemma lem5394548 : term268 = term277.
Proof. exact (TRANS (@lem5394525) (@lem5394547)). Qed.
Lemma lem5394549 : term267 = term277.
Proof. exact (TRANS (@lem5394524) (@lem5394548)). Qed.
Lemma lem5394551 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5394552 : term277 = term274.
Proof. exact (@lem5394551 term274). Qed.
Lemma lem5394553 : term267 = term274.
Proof. exact (TRANS (@lem5394549) (@lem5394552)). Qed.
Lemma lem5394556 (_69874 : int) : (term205 _69874) = (term205 _69874).
Proof. exact (eq_refl (term205 _69874)). Qed.
Lemma lem5394557 (_69874 : int) : (term266 _69874) = (term278 _69874).
Proof. exact (MK_COMB (@lem5394556 _69874) (@lem5394553)). Qed.
Lemma lem5394558 (_69874 : int) : (term265 _69874) = (term278 _69874).
Proof. exact (TRANS (@lem5394515 _69874) (@lem5394557 _69874)). Qed.
Lemma lem5394559 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem5394560 (_69874 : int) : (term264 _69874) = (term279 _69874).
Proof. exact (MK_COMB (@lem5394559) (@lem5394558 _69874)). Qed.
Lemma lem5394561 (_69874 : int) : (term279 _69874) = (term280 _69874).
Proof. exact (@lem1982757 (term209 _69874) term127 term274). Qed.
Lemma lem5394563 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394564 : term274 = term277.
Proof. exact (@lem5394563 term250). Qed.
Lemma lem5394566 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394567 : term127 = term196.
Proof. exact (@lem5394566 term7). Qed.
Lemma lem5394568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5394569 : term212 = term213.
Proof. exact (MK_COMB (@lem5394568) (@lem5394567)). Qed.
Lemma lem5394570 : term281 = term282.
Proof. exact (MK_COMB (@lem5394569) (@lem5394564)). Qed.
Lemma lem5394571 : term283.
Proof. exact (@lem1981473 term127 term127 term274 term127 term171 term127). Qed.
Lemma lem5394573 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394574 : term218 = term219.
Proof. exact (@lem5394573 (NUMERAL 0) term7). Qed.
Lemma lem5394575 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394576 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394577 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394576 h1) (fun h1 : term219 = True => @lem5394575)). Qed.
Lemma lem5394578 : term219 = True.
Proof. exact (EQ_MP (@lem5394577) (@lem5394575)). Qed.
Lemma lem5394579 : term218 = True.
Proof. exact (TRANS (@lem5394574) (@lem5394578)). Qed.
Lemma lem5394580 : True = term218.
Proof. exact (SYM (@lem5394579)). Qed.
Lemma lem5394581 : term218.
Proof. exact (EQ_MP (@lem5394580) (@lem0)). Qed.
Lemma lem5394582 : term284.
Proof. exact (@lem5394571 (@lem5394581)). Qed.
Lemma lem5394584 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394585 : term218 = term219.
Proof. exact (@lem5394584 (NUMERAL 0) term7). Qed.
Lemma lem5394586 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394587 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394588 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394587 h1) (fun h1 : term219 = True => @lem5394586)). Qed.
Lemma lem5394589 : term219 = True.
Proof. exact (EQ_MP (@lem5394588) (@lem5394586)). Qed.
Lemma lem5394590 : term218 = True.
Proof. exact (TRANS (@lem5394585) (@lem5394589)). Qed.
Lemma lem5394591 : True = term218.
Proof. exact (SYM (@lem5394590)). Qed.
Lemma lem5394592 : term218.
Proof. exact (EQ_MP (@lem5394591) (@lem0)). Qed.
Lemma lem5394593 : term285.
Proof. exact (@lem5394582 (@lem5394592)). Qed.
Lemma lem5394595 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5394596 : term218 = term219.
Proof. exact (@lem5394595 (NUMERAL 0) term7). Qed.
Lemma lem5394597 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5394598 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5394599 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5394598 h1) (fun h1 : term219 = True => @lem5394597)). Qed.
Lemma lem5394600 : term219 = True.
Proof. exact (EQ_MP (@lem5394599) (@lem5394597)). Qed.
Lemma lem5394601 : term218 = True.
Proof. exact (TRANS (@lem5394596) (@lem5394600)). Qed.
Lemma lem5394602 : True = term218.
Proof. exact (SYM (@lem5394601)). Qed.
Lemma lem5394603 : term218.
Proof. exact (EQ_MP (@lem5394602) (@lem0)). Qed.
Lemma lem5394604 : term286.
Proof. exact (@lem5394593 (@lem5394603)). Qed.
Lemma lem5394606 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394607 : term287 = term288.
Proof. exact (@lem5394606 term250 term7). Qed.
Lemma lem5394608 : term256 = term248.
Proof. exact (@lem996237 term248). Qed.
Lemma lem5394609 : (term256 = term248) = (term257 = term250).
Proof. exact (@lem1007663 term248 (BIT1 0) term248). Qed.
Lemma lem5394610 : term257 = term250.
Proof. exact (EQ_MP (@lem5394609) (@lem5394608)). Qed.
Lemma lem5394611 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394612 : term255 = term241.
Proof. exact (MK_COMB (@lem5394611) (@lem5394610)). Qed.
Lemma lem5394613 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394614 : term288 = term274.
Proof. exact (MK_COMB (@lem5394613) (@lem5394612)). Qed.
Lemma lem5394615 : term287 = term274.
Proof. exact (TRANS (@lem5394607) (@lem5394614)). Qed.
Lemma lem5394617 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394618 : term180 = term181.
Proof. exact (@lem5394617 term7 term7). Qed.
Lemma lem5394619 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394620 : term183 = term7.
Proof. exact (EQ_MP (@lem5394619) (@lem940073)). Qed.
Lemma lem5394621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394622 : term181 = term127.
Proof. exact (MK_COMB (@lem5394621) (@lem5394620)). Qed.
Lemma lem5394623 : term180 = term127.
Proof. exact (TRANS (@lem5394618) (@lem5394622)). Qed.
Lemma lem5394624 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5394625 : term224 = term212.
Proof. exact (MK_COMB (@lem5394624) (@lem5394623)). Qed.
Lemma lem5394626 : term289 = term281.
Proof. exact (MK_COMB (@lem5394625) (@lem5394615)). Qed.
Lemma lem5394629 : term290 = term171.
Proof. exact (@lem1367771 term7 term7). Qed.
Lemma lem5394630 : term247 = term248.
Proof. exact (@lem706885). Qed.
Lemma lem5394631 : (term247 = term248) = (term249 = term250).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term248). Qed.
Lemma lem5394632 : term249 = term250.
Proof. exact (EQ_MP (@lem5394631) (@lem5394630)). Qed.
Lemma lem5394633 : term250 = term249.
Proof. exact (SYM (@lem5394632)). Qed.
Lemma lem5394634 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394635 : term241 = term246.
Proof. exact (MK_COMB (@lem5394634) (@lem5394633)). Qed.
Lemma lem5394636 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394637 : term274 = term291.
Proof. exact (MK_COMB (@lem5394636) (@lem5394635)). Qed.
Lemma lem5394638 : term212 = term212.
Proof. exact (eq_refl term212). Qed.
Lemma lem5394639 : term281 = term290.
Proof. exact (MK_COMB (@lem5394638) (@lem5394637)). Qed.
Lemma lem5394640 : term281 = term171.
Proof. exact (TRANS (@lem5394639) (@lem5394629)). Qed.
Lemma lem5394641 : term289 = term171.
Proof. exact (TRANS (@lem5394626) (@lem5394640)). Qed.
Lemma lem5394642 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394643 : term292 = term173.
Proof. exact (MK_COMB (@lem5394642) (@lem5394641)). Qed.
Lemma lem5394644 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5394645 : term293 = term197.
Proof. exact (MK_COMB (@lem5394643) (@lem5394644)). Qed.
Lemma lem5394647 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394648 : term197 = term202.
Proof. exact (@lem5394647 term7 term7). Qed.
Lemma lem5394649 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394650 : term183 = term7.
Proof. exact (EQ_MP (@lem5394649) (@lem940073)). Qed.
Lemma lem5394651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394652 : term181 = term127.
Proof. exact (MK_COMB (@lem5394651) (@lem5394650)). Qed.
Lemma lem5394653 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394654 : term202 = term171.
Proof. exact (MK_COMB (@lem5394653) (@lem5394652)). Qed.
Lemma lem5394655 : term197 = term171.
Proof. exact (TRANS (@lem5394648) (@lem5394654)). Qed.
Lemma lem5394656 : term293 = term171.
Proof. exact (TRANS (@lem5394645) (@lem5394655)). Qed.
Lemma lem5394658 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394659 : term180 = term181.
Proof. exact (@lem5394658 term7 term7). Qed.
Lemma lem5394660 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394661 : term183 = term7.
Proof. exact (EQ_MP (@lem5394660) (@lem940073)). Qed.
Lemma lem5394662 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394663 : term181 = term127.
Proof. exact (MK_COMB (@lem5394662) (@lem5394661)). Qed.
Lemma lem5394664 : term180 = term127.
Proof. exact (TRANS (@lem5394659) (@lem5394663)). Qed.
Lemma lem5394665 : term173 = term173.
Proof. exact (eq_refl term173). Qed.
Lemma lem5394666 : term294 = term197.
Proof. exact (MK_COMB (@lem5394665) (@lem5394664)). Qed.
Lemma lem5394668 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394669 : term197 = term202.
Proof. exact (@lem5394668 term7 term7). Qed.
Lemma lem5394670 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394671 : term183 = term7.
Proof. exact (EQ_MP (@lem5394670) (@lem940073)). Qed.
Lemma lem5394672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394673 : term181 = term127.
Proof. exact (MK_COMB (@lem5394672) (@lem5394671)). Qed.
Lemma lem5394674 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394675 : term202 = term171.
Proof. exact (MK_COMB (@lem5394674) (@lem5394673)). Qed.
Lemma lem5394676 : term197 = term171.
Proof. exact (TRANS (@lem5394669) (@lem5394675)). Qed.
Lemma lem5394677 : term294 = term171.
Proof. exact (TRANS (@lem5394666) (@lem5394676)). Qed.
Lemma lem5394678 : term171 = term294.
Proof. exact (SYM (@lem5394677)). Qed.
Lemma lem5394679 : term293 = term294.
Proof. exact (TRANS (@lem5394656) (@lem5394678)). Qed.
Lemma lem5394680 : term282 = term172.
Proof. exact (@lem5394604 (@lem5394679)). Qed.
Lemma lem5394681 : term281 = term172.
Proof. exact (TRANS (@lem5394570) (@lem5394680)). Qed.
Lemma lem5394683 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5394684 : term172 = term171.
Proof. exact (@lem5394683 term171). Qed.
Lemma lem5394685 : term281 = term171.
Proof. exact (TRANS (@lem5394681) (@lem5394684)). Qed.
Lemma lem5394686 (_69874 : int) : (term205 _69874) = (term205 _69874).
Proof. exact (eq_refl (term205 _69874)). Qed.
Lemma lem5394687 (_69874 : int) : (term280 _69874) = (term206 _69874).
Proof. exact (MK_COMB (@lem5394686 _69874) (@lem5394685)). Qed.
Lemma lem5394688 (_69874 : int) : (term279 _69874) = (term206 _69874).
Proof. exact (TRANS (@lem5394561 _69874) (@lem5394687 _69874)). Qed.
Lemma lem5394689 (_69874 : int) : (term264 _69874) = (term206 _69874).
Proof. exact (TRANS (@lem5394560 _69874) (@lem5394688 _69874)). Qed.
Lemma lem5394690 (_69874 : int) : (term263 _69874) = (term206 _69874).
Proof. exact (TRANS (@lem5394514 _69874) (@lem5394689 _69874)). Qed.
Lemma lem5394691 (_69874 : int) : (term262 _69874) = (term206 _69874).
Proof. exact (TRANS (@lem5394513 _69874) (@lem5394690 _69874)). Qed.
Lemma lem5394692 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5394693 (_69874 : int) : (term295 _69874) = (term296 _69874).
Proof. exact (MK_COMB (@lem5394692) (@lem5394691 _69874)). Qed.
Lemma lem5394694 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5394695 (_69874 : int) : (term236 _69874) = (term297 _69874).
Proof. exact (MK_COMB (@lem5394693 _69874) (@lem5394694)). Qed.
Lemma lem5394696 (_69874 : int) : (term143 _69874) = (term297 _69874).
Proof. exact (TRANS (@lem5394381 _69874) (@lem5394695 _69874)). Qed.
Lemma lem5394697 (_69873 : int) : ((real_of_int _69873) = term118) = ((term165 _69873) = term118).
Proof. exact (@lem1988293 (real_of_int _69873) term118). Qed.
Lemma lem5394703 (_69873 : int) : (term165 _69873) = (term166 _69873).
Proof. exact (@lem1982792 (real_of_int _69873) term118). Qed.
Lemma lem5394705 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394706 : term118 = term168.
Proof. exact (@lem5394705 (NUMERAL 0)). Qed.
Lemma lem5394708 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394709 : term171 = term172.
Proof. exact (@lem5394708 term7). Qed.
Lemma lem5394710 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394711 : term173 = term174.
Proof. exact (MK_COMB (@lem5394710) (@lem5394709)). Qed.
Lemma lem5394712 : term175 = term176.
Proof. exact (MK_COMB (@lem5394711) (@lem5394706)). Qed.
Lemma lem5394713 : term176 = term177.
Proof. exact (@lem1981613 term171 term118 term127 term127). Qed.
Lemma lem5394715 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394716 : term180 = term181.
Proof. exact (@lem5394715 term7 term7). Qed.
Lemma lem5394717 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394718 : term183 = term7.
Proof. exact (EQ_MP (@lem5394717) (@lem940073)). Qed.
Lemma lem5394719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394720 : term181 = term127.
Proof. exact (MK_COMB (@lem5394719) (@lem5394718)). Qed.
Lemma lem5394721 : term180 = term127.
Proof. exact (TRANS (@lem5394716) (@lem5394720)). Qed.
Lemma lem5394723 (x : nat) : (term184 x) = term118.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem5394724 : term175 = term118.
Proof. exact (@lem5394723 term7). Qed.
Lemma lem5394725 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5394726 : term185 = term186.
Proof. exact (MK_COMB (@lem5394725) (@lem5394724)). Qed.
Lemma lem5394727 : term177 = term168.
Proof. exact (MK_COMB (@lem5394726) (@lem5394721)). Qed.
Lemma lem5394728 : term176 = term168.
Proof. exact (TRANS (@lem5394713) (@lem5394727)). Qed.
Lemma lem5394729 : term175 = term168.
Proof. exact (TRANS (@lem5394712) (@lem5394728)). Qed.
Lemma lem5394731 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5394732 : term168 = term118.
Proof. exact (@lem5394731 term118). Qed.
Lemma lem5394733 : term175 = term118.
Proof. exact (TRANS (@lem5394729) (@lem5394732)). Qed.
Lemma lem5394734 (_69873 : int) : (term128 _69873) = (term128 _69873).
Proof. exact (eq_refl (term128 _69873)). Qed.
Lemma lem5394735 (_69873 : int) : (term166 _69873) = (term188 _69873).
Proof. exact (MK_COMB (@lem5394734 _69873) (@lem5394733)). Qed.
Lemma lem5394736 (_69873 : int) : (term188 _69873) = (real_of_int _69873).
Proof. exact (@lem1982723 (real_of_int _69873)). Qed.
Lemma lem5394737 (_69873 : int) : (term166 _69873) = (real_of_int _69873).
Proof. exact (TRANS (@lem5394735 _69873) (@lem5394736 _69873)). Qed.
Lemma lem5394739 (_69873 : int) : (term165 _69873) = (real_of_int _69873).
Proof. exact (TRANS (@lem5394703 _69873) (@lem5394737 _69873)). Qed.
Lemma lem5394740 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5394741 (_69873 : int) : (term298 _69873) = (term144 _69873).
Proof. exact (MK_COMB (@lem5394740) (@lem5394739 _69873)). Qed.
Lemma lem5394742 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5394743 (_69873 : int) : ((term165 _69873) = term118) = ((real_of_int _69873) = term118).
Proof. exact (MK_COMB (@lem5394741 _69873) (@lem5394742)). Qed.
Lemma lem5394744 (_69873 : int) : ((real_of_int _69873) = term118) = ((real_of_int _69873) = term118).
Proof. exact (TRANS (@lem5394697 _69873) (@lem5394743 _69873)). Qed.
Lemma lem5394745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5394746 (_69874 : int) : (term145 _69874) = (term299 _69874).
Proof. exact (MK_COMB (@lem5394745) (@lem5394696 _69874)). Qed.
Lemma lem5394747 (_69874 : int) (_69873 : int) : (term146 _69874 _69873) = (term300 _69874 _69873).
Proof. exact (MK_COMB (@lem5394746 _69874) (@lem5394744 _69873)). Qed.
Lemma lem5394748 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5394749 (_69873 : int) (_69874 : int) : (term147 _69874 _69873) = (term301 _69873 _69874).
Proof. exact (MK_COMB (@lem5394748) (@lem5394380 _69873 _69874)). Qed.
Lemma lem5394750 (_69874 : int) (_69873 : int) : (term148 _69874 _69873) = (term302 _69874 _69873).
Proof. exact (MK_COMB (@lem5394749 _69873 _69874) (@lem5394747 _69874 _69873)). Qed.
Lemma lem5394751 (_69874 : int) (_69873 : int) : (term153 _69873 _69874) = (term303 _69874 _69873).
Proof. exact (@lem1988287 (real_of_int _69874) (term129 _69873)). Qed.
Lemma lem5394763 (_69874 : int) (_69873 : int) : (term304 _69874 _69873) = (term305 _69874 _69873).
Proof. exact (@lem1982792 (real_of_int _69874) (term129 _69873)). Qed.
Lemma lem5394764 (_69873 : int) : (term194 _69873) = (term195 _69873).
Proof. exact (@lem1982781 (real_of_int _69873) term171 term127). Qed.
Lemma lem5394766 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394767 : term127 = term196.
Proof. exact (@lem5394766 term7). Qed.
Lemma lem5394769 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394770 : term171 = term172.
Proof. exact (@lem5394769 term7). Qed.
Lemma lem5394771 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394772 : term173 = term174.
Proof. exact (MK_COMB (@lem5394771) (@lem5394770)). Qed.
Lemma lem5394773 : term197 = term198.
Proof. exact (MK_COMB (@lem5394772) (@lem5394767)). Qed.
Lemma lem5394774 : term198 = term199.
Proof. exact (@lem1981613 term171 term127 term127 term127). Qed.
Lemma lem5394776 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394777 : term180 = term181.
Proof. exact (@lem5394776 term7 term7). Qed.
Lemma lem5394778 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394779 : term183 = term7.
Proof. exact (EQ_MP (@lem5394778) (@lem940073)). Qed.
Lemma lem5394780 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394781 : term181 = term127.
Proof. exact (MK_COMB (@lem5394780) (@lem5394779)). Qed.
Lemma lem5394782 : term180 = term127.
Proof. exact (TRANS (@lem5394777) (@lem5394781)). Qed.
Lemma lem5394784 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394785 : term197 = term202.
Proof. exact (@lem5394784 term7 term7). Qed.
Lemma lem5394786 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394787 : term183 = term7.
Proof. exact (EQ_MP (@lem5394786) (@lem940073)). Qed.
Lemma lem5394788 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394789 : term181 = term127.
Proof. exact (MK_COMB (@lem5394788) (@lem5394787)). Qed.
Lemma lem5394790 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394791 : term202 = term171.
Proof. exact (MK_COMB (@lem5394790) (@lem5394789)). Qed.
Lemma lem5394792 : term197 = term171.
Proof. exact (TRANS (@lem5394785) (@lem5394791)). Qed.
Lemma lem5394793 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5394794 : term203 = term204.
Proof. exact (MK_COMB (@lem5394793) (@lem5394792)). Qed.
Lemma lem5394795 : term199 = term172.
Proof. exact (MK_COMB (@lem5394794) (@lem5394782)). Qed.
Lemma lem5394796 : term198 = term172.
Proof. exact (TRANS (@lem5394774) (@lem5394795)). Qed.
Lemma lem5394797 : term197 = term172.
Proof. exact (TRANS (@lem5394773) (@lem5394796)). Qed.
Lemma lem5394799 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5394800 : term172 = term171.
Proof. exact (@lem5394799 term171). Qed.
Lemma lem5394801 : term197 = term171.
Proof. exact (TRANS (@lem5394797) (@lem5394800)). Qed.
Lemma lem5394804 (_69873 : int) : (term205 _69873) = (term205 _69873).
Proof. exact (eq_refl (term205 _69873)). Qed.
Lemma lem5394805 (_69873 : int) : (term195 _69873) = (term206 _69873).
Proof. exact (MK_COMB (@lem5394804 _69873) (@lem5394801)). Qed.
Lemma lem5394806 (_69873 : int) : (term194 _69873) = (term206 _69873).
Proof. exact (TRANS (@lem5394764 _69873) (@lem5394805 _69873)). Qed.
Lemma lem5394807 (_69874 : int) : (term128 _69874) = (term128 _69874).
Proof. exact (eq_refl (term128 _69874)). Qed.
Lemma lem5394808 (_69874 : int) (_69873 : int) : (term305 _69874 _69873) = (term306 _69874 _69873).
Proof. exact (MK_COMB (@lem5394807 _69874) (@lem5394806 _69873)). Qed.
Lemma lem5394813 (_69873 : int) (_69874 : int) : (term306 _69874 _69873) = (term307 _69873 _69874).
Proof. exact (@lem1982757 (term209 _69873) (real_of_int _69874) term171). Qed.
Lemma lem5394814 (_69873 : int) (_69874 : int) : (term305 _69874 _69873) = (term307 _69873 _69874).
Proof. exact (TRANS (@lem5394808 _69874 _69873) (@lem5394813 _69873 _69874)). Qed.
Lemma lem5394816 (_69873 : int) (_69874 : int) : (term304 _69874 _69873) = (term307 _69873 _69874).
Proof. exact (TRANS (@lem5394763 _69874 _69873) (@lem5394814 _69873 _69874)). Qed.
Lemma lem5394817 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5394818 (_69873 : int) (_69874 : int) : (term308 _69874 _69873) = (term309 _69873 _69874).
Proof. exact (MK_COMB (@lem5394817) (@lem5394816 _69873 _69874)). Qed.
Lemma lem5394819 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5394820 (_69873 : int) (_69874 : int) : (term303 _69874 _69873) = (term310 _69873 _69874).
Proof. exact (MK_COMB (@lem5394818 _69873 _69874) (@lem5394819)). Qed.
Lemma lem5394821 (_69873 : int) (_69874 : int) : (term153 _69873 _69874) = (term310 _69873 _69874).
Proof. exact (TRANS (@lem5394751 _69874 _69873) (@lem5394820 _69873 _69874)). Qed.
Lemma lem5394822 (_69873 : int) (_69874 : int) : (term153 _69874 _69873) = (term303 _69873 _69874).
Proof. exact (@lem1988287 (real_of_int _69873) (term129 _69874)). Qed.
Lemma lem5394834 (_69873 : int) (_69874 : int) : (term304 _69873 _69874) = (term305 _69873 _69874).
Proof. exact (@lem1982792 (real_of_int _69873) (term129 _69874)). Qed.
Lemma lem5394835 (_69874 : int) : (term194 _69874) = (term195 _69874).
Proof. exact (@lem1982781 (real_of_int _69874) term171 term127). Qed.
Lemma lem5394837 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5394838 : term127 = term196.
Proof. exact (@lem5394837 term7). Qed.
Lemma lem5394840 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5394841 : term171 = term172.
Proof. exact (@lem5394840 term7). Qed.
Lemma lem5394842 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5394843 : term173 = term174.
Proof. exact (MK_COMB (@lem5394842) (@lem5394841)). Qed.
Lemma lem5394844 : term197 = term198.
Proof. exact (MK_COMB (@lem5394843) (@lem5394838)). Qed.
Lemma lem5394845 : term198 = term199.
Proof. exact (@lem1981613 term171 term127 term127 term127). Qed.
Lemma lem5394847 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5394848 : term180 = term181.
Proof. exact (@lem5394847 term7 term7). Qed.
Lemma lem5394849 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394850 : term183 = term7.
Proof. exact (EQ_MP (@lem5394849) (@lem940073)). Qed.
Lemma lem5394851 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394852 : term181 = term127.
Proof. exact (MK_COMB (@lem5394851) (@lem5394850)). Qed.
Lemma lem5394853 : term180 = term127.
Proof. exact (TRANS (@lem5394848) (@lem5394852)). Qed.
Lemma lem5394855 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5394856 : term197 = term202.
Proof. exact (@lem5394855 term7 term7). Qed.
Lemma lem5394857 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5394858 : term183 = term7.
Proof. exact (EQ_MP (@lem5394857) (@lem940073)). Qed.
Lemma lem5394859 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5394860 : term181 = term127.
Proof. exact (MK_COMB (@lem5394859) (@lem5394858)). Qed.
Lemma lem5394861 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5394862 : term202 = term171.
Proof. exact (MK_COMB (@lem5394861) (@lem5394860)). Qed.
Lemma lem5394863 : term197 = term171.
Proof. exact (TRANS (@lem5394856) (@lem5394862)). Qed.
Lemma lem5394864 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5394865 : term203 = term204.
Proof. exact (MK_COMB (@lem5394864) (@lem5394863)). Qed.
Lemma lem5394866 : term199 = term172.
Proof. exact (MK_COMB (@lem5394865) (@lem5394853)). Qed.
Lemma lem5394867 : term198 = term172.
Proof. exact (TRANS (@lem5394845) (@lem5394866)). Qed.
Lemma lem5394868 : term197 = term172.
Proof. exact (TRANS (@lem5394844) (@lem5394867)). Qed.
Lemma lem5394870 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5394871 : term172 = term171.
Proof. exact (@lem5394870 term171). Qed.
Lemma lem5394872 : term197 = term171.
Proof. exact (TRANS (@lem5394868) (@lem5394871)). Qed.
Lemma lem5394875 (_69874 : int) : (term205 _69874) = (term205 _69874).
Proof. exact (eq_refl (term205 _69874)). Qed.
Lemma lem5394876 (_69874 : int) : (term195 _69874) = (term206 _69874).
Proof. exact (MK_COMB (@lem5394875 _69874) (@lem5394872)). Qed.
Lemma lem5394877 (_69874 : int) : (term194 _69874) = (term206 _69874).
Proof. exact (TRANS (@lem5394835 _69874) (@lem5394876 _69874)). Qed.
Lemma lem5394878 (_69873 : int) : (term128 _69873) = (term128 _69873).
Proof. exact (eq_refl (term128 _69873)). Qed.
Lemma lem5394881 (_69873 : int) (_69874 : int) : (term305 _69873 _69874) = (term306 _69873 _69874).
Proof. exact (MK_COMB (@lem5394878 _69873) (@lem5394877 _69874)). Qed.
Lemma lem5394883 (_69873 : int) (_69874 : int) : (term304 _69873 _69874) = (term306 _69873 _69874).
Proof. exact (TRANS (@lem5394834 _69873 _69874) (@lem5394881 _69873 _69874)). Qed.
Lemma lem5394884 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5394885 (_69873 : int) (_69874 : int) : (term308 _69873 _69874) = (term311 _69873 _69874).
Proof. exact (MK_COMB (@lem5394884) (@lem5394883 _69873 _69874)). Qed.
Lemma lem5394886 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5394887 (_69873 : int) (_69874 : int) : (term303 _69873 _69874) = (term312 _69873 _69874).
Proof. exact (MK_COMB (@lem5394885 _69873 _69874) (@lem5394886)). Qed.
Lemma lem5394888 (_69873 : int) (_69874 : int) : (term153 _69874 _69873) = (term312 _69873 _69874).
Proof. exact (TRANS (@lem5394822 _69873 _69874) (@lem5394887 _69873 _69874)). Qed.
Lemma lem5394889 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5394890 (_69873 : int) (_69874 : int) : (term155 _69873 _69874) = (term313 _69873 _69874).
Proof. exact (MK_COMB (@lem5394889) (@lem5394821 _69873 _69874)). Qed.
Lemma lem5394891 (_69873 : int) (_69874 : int) : (term156 _69874 _69873) = (term314 _69873 _69874).
Proof. exact (MK_COMB (@lem5394890 _69873 _69874) (@lem5394888 _69873 _69874)). Qed.
Lemma lem5394892 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5394893 (_69874 : int) (_69873 : int) : (term157 _69874 _69873) = (term315 _69874 _69873).
Proof. exact (MK_COMB (@lem5394892) (@lem5394750 _69874 _69873)). Qed.
Lemma lem5394894 (_69873 : int) (_69874 : int) : (term158 _69874 _69873) = (term316 _69873 _69874).
Proof. exact (MK_COMB (@lem5394893 _69874 _69873) (@lem5394891 _69873 _69874)). Qed.
Lemma lem5394895 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5394896 (_69874 : int) : (term159 _69874) = (term317 _69874).
Proof. exact (MK_COMB (@lem5394895) (@lem5394200 _69874)). Qed.
Lemma lem5394897 (_69873 : int) (_69874 : int) : (term160 _69874 _69873) = (term318 _69873 _69874).
Proof. exact (MK_COMB (@lem5394896 _69874) (@lem5394894 _69873 _69874)). Qed.
Lemma lem5394898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5394899 (_69873 : int) : (term159 _69873) = (term317 _69873).
Proof. exact (MK_COMB (@lem5394898) (@lem5394152 _69873)). Qed.
Lemma lem5394900 (_69873 : int) (_69874 : int) : (term161 _69874 _69873) = (term319 _69873 _69874).
Proof. exact (MK_COMB (@lem5394899 _69873) (@lem5394897 _69873 _69874)). Qed.
Lemma lem5394907 (_69873 : int) (_69874 : int) : (term163 _69874 _69873) = (term319 _69873 _69874).
Proof. exact (TRANS (@lem5394104 _69874 _69873) (@lem5394900 _69873 _69874)). Qed.
Lemma lem5394927 (_69873 : int) (_69874 : int) : (term316 _69873 _69874) = (term320 _69873 _69874).
Proof. exact (@lem19158 (term310 _69873 _69874) (term302 _69874 _69873) (term312 _69873 _69874)). Qed.
Lemma lem5394934 (_69873 : int) (_69874 : int) : (term321 _69873 _69874) = (term322 _69873 _69874).
Proof. exact (@lem19367 ((term233 _69873 _69874) = term118) (term300 _69874 _69873) (term312 _69873 _69874)). Qed.
Lemma lem5394941 (_69873 : int) (_69874 : int) : (term323 _69873 _69874) = (term324 _69873 _69874).
Proof. exact (@lem19367 ((term233 _69873 _69874) = term118) (term300 _69874 _69873) (term310 _69873 _69874)). Qed.
Lemma lem5394942 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5394943 (_69873 : int) (_69874 : int) : (term325 _69873 _69874) = (term326 _69873 _69874).
Proof. exact (MK_COMB (@lem5394942) (@lem5394941 _69873 _69874)). Qed.
Lemma lem5394944 (_69873 : int) (_69874 : int) : (term320 _69873 _69874) = (term327 _69873 _69874).
Proof. exact (MK_COMB (@lem5394943 _69873 _69874) (@lem5394934 _69873 _69874)). Qed.
Lemma lem5394946 (_69873 : int) (_69874 : int) : (term316 _69873 _69874) = (term327 _69873 _69874).
Proof. exact (TRANS (@lem5394927 _69873 _69874) (@lem5394944 _69873 _69874)). Qed.
Lemma lem5394949 (_69874 : int) : (term317 _69874) = (term317 _69874).
Proof. exact (eq_refl (term317 _69874)). Qed.
Lemma lem5394950 (_69873 : int) (_69874 : int) : (term318 _69873 _69874) = (term328 _69873 _69874).
Proof. exact (MK_COMB (@lem5394949 _69874) (@lem5394946 _69873 _69874)). Qed.
Lemma lem5394951 (_69873 : int) (_69874 : int) : (term328 _69873 _69874) = (term329 _69873 _69874).
Proof. exact (@lem19158 (term324 _69873 _69874) (term191 _69874) (term322 _69873 _69874)). Qed.
Lemma lem5394958 (_69873 : int) (_69874 : int) : (term330 _69873 _69874) = (term331 _69873 _69874).
Proof. exact (@lem19158 (term332 _69873 _69874) (term191 _69874) (term333 _69873 _69874)). Qed.
Lemma lem5394965 (_69873 : int) (_69874 : int) : (term334 _69873 _69874) = (term335 _69873 _69874).
Proof. exact (@lem19158 (term336 _69873 _69874) (term191 _69874) (term337 _69873 _69874)). Qed.
Lemma lem5394966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5394967 (_69873 : int) (_69874 : int) : (term338 _69873 _69874) = (term339 _69873 _69874).
Proof. exact (MK_COMB (@lem5394966) (@lem5394965 _69873 _69874)). Qed.
Lemma lem5394968 (_69873 : int) (_69874 : int) : (term329 _69873 _69874) = (term340 _69873 _69874).
Proof. exact (MK_COMB (@lem5394967 _69873 _69874) (@lem5394958 _69873 _69874)). Qed.
Lemma lem5394969 (_69873 : int) (_69874 : int) : (term328 _69873 _69874) = (term340 _69873 _69874).
Proof. exact (TRANS (@lem5394951 _69873 _69874) (@lem5394968 _69873 _69874)). Qed.
Lemma lem5394970 (_69873 : int) (_69874 : int) : (term318 _69873 _69874) = (term340 _69873 _69874).
Proof. exact (TRANS (@lem5394950 _69873 _69874) (@lem5394969 _69873 _69874)). Qed.
Lemma lem5394973 (_69873 : int) : (term317 _69873) = (term317 _69873).
Proof. exact (eq_refl (term317 _69873)). Qed.
Lemma lem5394974 (_69873 : int) (_69874 : int) : (term319 _69873 _69874) = (term341 _69873 _69874).
Proof. exact (MK_COMB (@lem5394973 _69873) (@lem5394970 _69873 _69874)). Qed.
Lemma lem5394975 (_69873 : int) (_69874 : int) : (term341 _69873 _69874) = (term342 _69873 _69874).
Proof. exact (@lem19158 (term335 _69873 _69874) (term191 _69873) (term331 _69873 _69874)). Qed.
Lemma lem5394982 (_69873 : int) (_69874 : int) : (term343 _69873 _69874) = (term344 _69873 _69874).
Proof. exact (@lem19158 (term345 _69873 _69874) (term191 _69873) (term346 _69873 _69874)). Qed.
Lemma lem5394989 (_69873 : int) (_69874 : int) : (term347 _69873 _69874) = (term348 _69873 _69874).
Proof. exact (@lem19158 (term349 _69873 _69874) (term191 _69873) (term350 _69873 _69874)). Qed.
Lemma lem5394990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5394991 (_69873 : int) (_69874 : int) : (term351 _69873 _69874) = (term352 _69873 _69874).
Proof. exact (MK_COMB (@lem5394990) (@lem5394989 _69873 _69874)). Qed.
Lemma lem5394992 (_69873 : int) (_69874 : int) : (term342 _69873 _69874) = (term353 _69873 _69874).
Proof. exact (MK_COMB (@lem5394991 _69873 _69874) (@lem5394982 _69873 _69874)). Qed.
Lemma lem5394993 (_69873 : int) (_69874 : int) : (term341 _69873 _69874) = (term353 _69873 _69874).
Proof. exact (TRANS (@lem5394975 _69873 _69874) (@lem5394992 _69873 _69874)). Qed.
Lemma lem5394994 (_69873 : int) (_69874 : int) : (term319 _69873 _69874) = (term353 _69873 _69874).
Proof. exact (TRANS (@lem5394974 _69873 _69874) (@lem5394993 _69873 _69874)). Qed.
Lemma lem5394995 (_69873 : int) (_69874 : int) : (term163 _69874 _69873) = (term353 _69873 _69874).
Proof. exact (TRANS (@lem5394907 _69873 _69874) (@lem5394994 _69873 _69874)). Qed.
Lemma lem5395017 (_69873 : int) (_69874 : int) (h1 : term353 _69873 _69874) : term353 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5395018 (_69873 : int) (_69874 : int) (h1 : term348 _69873 _69874) : term348 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5395019 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term354 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5395020 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term349 _69873 _69874.
Proof. exact (proj2 (@lem5395019 _69873 _69874 h1)). Qed.
Lemma lem5395022 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term336 _69873 _69874.
Proof. exact (proj2 (@lem5395020 _69873 _69874 h1)). Qed.
Lemma lem5395024 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term310 _69873 _69874.
Proof. exact (proj2 (@lem5395022 _69873 _69874 h1)). Qed.
Lemma lem5395025 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : (term233 _69873 _69874) = term118.
Proof. exact (proj1 (@lem5395022 _69873 _69874 h1)). Qed.
Lemma lem5395027 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5395028 : term355 = term218.
Proof. exact (@lem5395027 term118 term127). Qed.
Lemma lem5395030 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395031 : term127 = term196.
Proof. exact (@lem5395030 term7). Qed.
Lemma lem5395033 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395034 : term118 = term168.
Proof. exact (@lem5395033 (NUMERAL 0)). Qed.
Lemma lem5395035 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395036 : term356 = term357.
Proof. exact (MK_COMB (@lem5395035) (@lem5395034)). Qed.
Lemma lem5395037 : term218 = term358.
Proof. exact (MK_COMB (@lem5395036) (@lem5395031)). Qed.
Lemma lem5395038 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5395040 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395041 : term218 = term219.
Proof. exact (@lem5395040 (NUMERAL 0) term7). Qed.
Lemma lem5395042 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395043 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395044 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395043 h1) (fun h1 : term219 = True => @lem5395042)). Qed.
Lemma lem5395045 : term219 = True.
Proof. exact (EQ_MP (@lem5395044) (@lem5395042)). Qed.
Lemma lem5395046 : term218 = True.
Proof. exact (TRANS (@lem5395041) (@lem5395045)). Qed.
Lemma lem5395047 : True = term218.
Proof. exact (SYM (@lem5395046)). Qed.
Lemma lem5395048 : term218.
Proof. exact (EQ_MP (@lem5395047) (@lem0)). Qed.
Lemma lem5395049 : term360.
Proof. exact (@lem5395038 (@lem5395048)). Qed.
Lemma lem5395051 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395052 : term218 = term219.
Proof. exact (@lem5395051 (NUMERAL 0) term7). Qed.
Lemma lem5395053 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395054 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395055 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395054 h1) (fun h1 : term219 = True => @lem5395053)). Qed.
Lemma lem5395056 : term219 = True.
Proof. exact (EQ_MP (@lem5395055) (@lem5395053)). Qed.
Lemma lem5395057 : term218 = True.
Proof. exact (TRANS (@lem5395052) (@lem5395056)). Qed.
Lemma lem5395058 : True = term218.
Proof. exact (SYM (@lem5395057)). Qed.
Lemma lem5395059 : term218.
Proof. exact (EQ_MP (@lem5395058) (@lem0)). Qed.
Lemma lem5395060 : term358 = term361.
Proof. exact (@lem5395049 (@lem5395059)). Qed.
Lemma lem5395062 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395063 : term180 = term181.
Proof. exact (@lem5395062 term7 term7). Qed.
Lemma lem5395064 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395065 : term183 = term7.
Proof. exact (EQ_MP (@lem5395064) (@lem940073)). Qed.
Lemma lem5395066 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395067 : term181 = term127.
Proof. exact (MK_COMB (@lem5395066) (@lem5395065)). Qed.
Lemma lem5395068 : term180 = term127.
Proof. exact (TRANS (@lem5395063) (@lem5395067)). Qed.
Lemma lem5395070 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395071 : term230 = term118.
Proof. exact (@lem5395070 term7). Qed.
Lemma lem5395072 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395073 : term362 = term356.
Proof. exact (MK_COMB (@lem5395072) (@lem5395071)). Qed.
Lemma lem5395074 : term361 = term218.
Proof. exact (MK_COMB (@lem5395073) (@lem5395068)). Qed.
Lemma lem5395076 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395077 : term218 = term219.
Proof. exact (@lem5395076 (NUMERAL 0) term7). Qed.
Lemma lem5395078 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395079 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395080 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395079 h1) (fun h1 : term219 = True => @lem5395078)). Qed.
Lemma lem5395081 : term219 = True.
Proof. exact (EQ_MP (@lem5395080) (@lem5395078)). Qed.
Lemma lem5395082 : term218 = True.
Proof. exact (TRANS (@lem5395077) (@lem5395081)). Qed.
Lemma lem5395083 : term361 = True.
Proof. exact (TRANS (@lem5395074) (@lem5395082)). Qed.
Lemma lem5395084 : term358 = True.
Proof. exact (TRANS (@lem5395060) (@lem5395083)). Qed.
Lemma lem5395085 : term218 = True.
Proof. exact (TRANS (@lem5395037) (@lem5395084)). Qed.
Lemma lem5395086 : term355 = True.
Proof. exact (TRANS (@lem5395028) (@lem5395085)). Qed.
Lemma lem5395087 : True = term355.
Proof. exact (SYM (@lem5395086)). Qed.
Lemma lem5395088 : term355.
Proof. exact (EQ_MP (@lem5395087) (@lem0)). Qed.
Lemma lem5395089 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term363 _69873 _69874.
Proof. exact (conj (@lem5395088) (@lem5395024 _69873 _69874 h1)). Qed.
Lemma lem5395091 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5395092 (_69873 : int) (_69874 : int) : term365 _69873 _69874.
Proof. exact (@lem5395091 term127 (term307 _69873 _69874)). Qed.
Lemma lem5395093 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term366 _69873 _69874.
Proof. exact (@lem5395092 _69873 _69874 (@lem5395089 _69873 _69874 h1)). Qed.
Lemma lem5395094 (_69873 : int) (_69874 : int) : (term367 _69873 _69874) = (term307 _69873 _69874).
Proof. exact (@lem1982733 (term307 _69873 _69874)). Qed.
Lemma lem5395095 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5395096 (_69873 : int) (_69874 : int) : (term368 _69873 _69874) = (term309 _69873 _69874).
Proof. exact (MK_COMB (@lem5395095) (@lem5395094 _69873 _69874)). Qed.
Lemma lem5395097 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395098 (_69873 : int) (_69874 : int) : (term366 _69873 _69874) = (term310 _69873 _69874).
Proof. exact (MK_COMB (@lem5395096 _69873 _69874) (@lem5395097)). Qed.
Lemma lem5395099 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term310 _69873 _69874.
Proof. exact (EQ_MP (@lem5395098 _69873 _69874) (@lem5395093 _69873 _69874 h1)). Qed.
Lemma lem5395101 (y : real) : term369 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5395102 (_69873 : int) (_69874 : int) : term370 _69873 _69874.
Proof. exact (@lem5395101 (term233 _69873 _69874)). Qed.
Lemma lem5395103 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term371 _69873 _69874.
Proof. exact (@lem5395102 _69873 _69874 (@lem5395025 _69873 _69874 h1)). Qed.
Lemma lem5395104 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term372 _69873 _69874.
Proof. exact (@lem5395103 _69873 _69874 h1 term171). Qed.
Lemma lem5395105 (_69873 : int) (_69874 : int) : (term372 _69873 _69874) = ((term373 _69873 _69874) = term118).
Proof. exact (eq_refl (term372 _69873 _69874)). Qed.
Lemma lem5395106 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : (term373 _69873 _69874) = term118.
Proof. exact (EQ_MP (@lem5395105 _69873 _69874) (@lem5395104 _69873 _69874 h1)). Qed.
Lemma lem5395107 (_69873 : int) (_69874 : int) : (term373 _69873 _69874) = (term374 _69873 _69874).
Proof. exact (@lem1982781 (term209 _69873) term171 (real_of_int _69874)). Qed.
Lemma lem5395108 (_69874 : int) : (term209 _69874) = (term209 _69874).
Proof. exact (eq_refl (term209 _69874)). Qed.
Lemma lem5395109 (_69873 : int) : (term375 _69873) = (term376 _69873).
Proof. exact (@lem1982749 term171 term171 (real_of_int _69873)). Qed.
Lemma lem5395111 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395112 : term171 = term172.
Proof. exact (@lem5395111 term7). Qed.
Lemma lem5395114 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395115 : term171 = term172.
Proof. exact (@lem5395114 term7). Qed.
Lemma lem5395116 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395117 : term173 = term174.
Proof. exact (MK_COMB (@lem5395116) (@lem5395115)). Qed.
Lemma lem5395118 : term377 = term378.
Proof. exact (MK_COMB (@lem5395117) (@lem5395112)). Qed.
Lemma lem5395119 : term378 = term379.
Proof. exact (@lem1981613 term171 term171 term127 term127). Qed.
Lemma lem5395121 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395122 : term180 = term181.
Proof. exact (@lem5395121 term7 term7). Qed.
Lemma lem5395123 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395124 : term183 = term7.
Proof. exact (EQ_MP (@lem5395123) (@lem940073)). Qed.
Lemma lem5395125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395126 : term181 = term127.
Proof. exact (MK_COMB (@lem5395125) (@lem5395124)). Qed.
Lemma lem5395127 : term180 = term127.
Proof. exact (TRANS (@lem5395122) (@lem5395126)). Qed.
Lemma lem5395129 (m : nat) (n : nat) : (term380 m n) = (term179 m n).
Proof. exact (proj2 (@lem1367248 m n)). Qed.
Lemma lem5395130 : term377 = term181.
Proof. exact (@lem5395129 term7 term7). Qed.
Lemma lem5395131 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395132 : term183 = term7.
Proof. exact (EQ_MP (@lem5395131) (@lem940073)). Qed.
Lemma lem5395133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395134 : term181 = term127.
Proof. exact (MK_COMB (@lem5395133) (@lem5395132)). Qed.
Lemma lem5395135 : term377 = term127.
Proof. exact (TRANS (@lem5395130) (@lem5395134)). Qed.
Lemma lem5395136 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem5395137 : term381 = term382.
Proof. exact (MK_COMB (@lem5395136) (@lem5395135)). Qed.
Lemma lem5395138 : term379 = term196.
Proof. exact (MK_COMB (@lem5395137) (@lem5395127)). Qed.
Lemma lem5395139 : term378 = term196.
Proof. exact (TRANS (@lem5395119) (@lem5395138)). Qed.
Lemma lem5395140 : term377 = term196.
Proof. exact (TRANS (@lem5395118) (@lem5395139)). Qed.
Lemma lem5395142 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem5395143 : term196 = term127.
Proof. exact (@lem5395142 term127). Qed.
Lemma lem5395144 : term377 = term127.
Proof. exact (TRANS (@lem5395140) (@lem5395143)). Qed.
Lemma lem5395145 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395146 : term383 = term384.
Proof. exact (MK_COMB (@lem5395145) (@lem5395144)). Qed.
Lemma lem5395147 (_69873 : int) : (real_of_int _69873) = (real_of_int _69873).
Proof. exact (eq_refl (real_of_int _69873)). Qed.
Lemma lem5395148 (_69873 : int) : (term376 _69873) = (term385 _69873).
Proof. exact (MK_COMB (@lem5395146) (@lem5395147 _69873)). Qed.
Lemma lem5395149 (_69873 : int) : (term375 _69873) = (term385 _69873).
Proof. exact (TRANS (@lem5395109 _69873) (@lem5395148 _69873)). Qed.
Lemma lem5395150 (_69873 : int) : (term385 _69873) = (real_of_int _69873).
Proof. exact (@lem1982709 (real_of_int _69873)). Qed.
Lemma lem5395151 (_69873 : int) : (term375 _69873) = (real_of_int _69873).
Proof. exact (TRANS (@lem5395149 _69873) (@lem5395150 _69873)). Qed.
Lemma lem5395152 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395153 (_69873 : int) : (term386 _69873) = (term128 _69873).
Proof. exact (MK_COMB (@lem5395152) (@lem5395151 _69873)). Qed.
Lemma lem5395154 (_69873 : int) (_69874 : int) : (term374 _69873 _69874) = (term387 _69873 _69874).
Proof. exact (MK_COMB (@lem5395153 _69873) (@lem5395108 _69874)). Qed.
Lemma lem5395155 (_69873 : int) (_69874 : int) : (term373 _69873 _69874) = (term387 _69873 _69874).
Proof. exact (TRANS (@lem5395107 _69873 _69874) (@lem5395154 _69873 _69874)). Qed.
Lemma lem5395156 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5395157 (_69873 : int) (_69874 : int) : (term388 _69873 _69874) = (term389 _69873 _69874).
Proof. exact (MK_COMB (@lem5395156) (@lem5395155 _69873 _69874)). Qed.
Lemma lem5395158 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395159 (_69873 : int) (_69874 : int) : ((term373 _69873 _69874) = term118) = ((term387 _69873 _69874) = term118).
Proof. exact (MK_COMB (@lem5395157 _69873 _69874) (@lem5395158)). Qed.
Lemma lem5395160 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : (term387 _69873 _69874) = term118.
Proof. exact (EQ_MP (@lem5395159 _69873 _69874) (@lem5395106 _69873 _69874 h1)). Qed.
Lemma lem5395161 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term390 _69873 _69874.
Proof. exact (conj (@lem5395160 _69873 _69874 h1) (@lem5395099 _69873 _69874 h1)). Qed.
Lemma lem5395163 (x : real) (y : real) : term391 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5395164 (_69873 : int) (_69874 : int) : term392 _69873 _69874.
Proof. exact (@lem5395163 (term387 _69873 _69874) (term307 _69873 _69874)). Qed.
Lemma lem5395165 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term393 _69873 _69874.
Proof. exact (@lem5395164 _69873 _69874 (@lem5395161 _69873 _69874 h1)). Qed.
Lemma lem5395166 (_69873 : int) (_69874 : int) : (term394 _69873 _69874) = (term395 _69873 _69874).
Proof. exact (@lem1982753 (real_of_int _69873) (term209 _69873) (term209 _69874) (term396 _69874)). Qed.
Lemma lem5395167 (_69873 : int) : (term397 _69873) = (term398 _69873).
Proof. exact (@lem1982715 term171 (real_of_int _69873)). Qed.
Lemma lem5395169 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395170 : term127 = term196.
Proof. exact (@lem5395169 term7). Qed.
Lemma lem5395172 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395173 : term171 = term172.
Proof. exact (@lem5395172 term7). Qed.
Lemma lem5395174 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395175 : term399 = term400.
Proof. exact (MK_COMB (@lem5395174) (@lem5395173)). Qed.
Lemma lem5395176 : term401 = term402.
Proof. exact (MK_COMB (@lem5395175) (@lem5395170)). Qed.
Lemma lem5395177 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5395179 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395180 : term218 = term219.
Proof. exact (@lem5395179 (NUMERAL 0) term7). Qed.
Lemma lem5395181 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395182 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395183 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395182 h1) (fun h1 : term219 = True => @lem5395181)). Qed.
Lemma lem5395184 : term219 = True.
Proof. exact (EQ_MP (@lem5395183) (@lem5395181)). Qed.
Lemma lem5395185 : term218 = True.
Proof. exact (TRANS (@lem5395180) (@lem5395184)). Qed.
Lemma lem5395186 : True = term218.
Proof. exact (SYM (@lem5395185)). Qed.
Lemma lem5395187 : term218.
Proof. exact (EQ_MP (@lem5395186) (@lem0)). Qed.
Lemma lem5395188 : term404.
Proof. exact (@lem5395177 (@lem5395187)). Qed.
Lemma lem5395190 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395191 : term218 = term219.
Proof. exact (@lem5395190 (NUMERAL 0) term7). Qed.
Lemma lem5395192 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395193 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395194 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395193 h1) (fun h1 : term219 = True => @lem5395192)). Qed.
Lemma lem5395195 : term219 = True.
Proof. exact (EQ_MP (@lem5395194) (@lem5395192)). Qed.
Lemma lem5395196 : term218 = True.
Proof. exact (TRANS (@lem5395191) (@lem5395195)). Qed.
Lemma lem5395197 : True = term218.
Proof. exact (SYM (@lem5395196)). Qed.
Lemma lem5395198 : term218.
Proof. exact (EQ_MP (@lem5395197) (@lem0)). Qed.
Lemma lem5395199 : term405.
Proof. exact (@lem5395188 (@lem5395198)). Qed.
Lemma lem5395201 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395202 : term218 = term219.
Proof. exact (@lem5395201 (NUMERAL 0) term7). Qed.
Lemma lem5395203 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395204 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395205 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395204 h1) (fun h1 : term219 = True => @lem5395203)). Qed.
Lemma lem5395206 : term219 = True.
Proof. exact (EQ_MP (@lem5395205) (@lem5395203)). Qed.
Lemma lem5395207 : term218 = True.
Proof. exact (TRANS (@lem5395202) (@lem5395206)). Qed.
Lemma lem5395208 : True = term218.
Proof. exact (SYM (@lem5395207)). Qed.
Lemma lem5395209 : term218.
Proof. exact (EQ_MP (@lem5395208) (@lem0)). Qed.
Lemma lem5395210 : term406.
Proof. exact (@lem5395199 (@lem5395209)). Qed.
Lemma lem5395212 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395213 : term180 = term181.
Proof. exact (@lem5395212 term7 term7). Qed.
Lemma lem5395214 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395215 : term183 = term7.
Proof. exact (EQ_MP (@lem5395214) (@lem940073)). Qed.
Lemma lem5395216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395217 : term181 = term127.
Proof. exact (MK_COMB (@lem5395216) (@lem5395215)). Qed.
Lemma lem5395218 : term180 = term127.
Proof. exact (TRANS (@lem5395213) (@lem5395217)). Qed.
Lemma lem5395220 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5395221 : term197 = term202.
Proof. exact (@lem5395220 term7 term7). Qed.
Lemma lem5395222 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395223 : term183 = term7.
Proof. exact (EQ_MP (@lem5395222) (@lem940073)). Qed.
Lemma lem5395224 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395225 : term181 = term127.
Proof. exact (MK_COMB (@lem5395224) (@lem5395223)). Qed.
Lemma lem5395226 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5395227 : term202 = term171.
Proof. exact (MK_COMB (@lem5395226) (@lem5395225)). Qed.
Lemma lem5395228 : term197 = term171.
Proof. exact (TRANS (@lem5395221) (@lem5395227)). Qed.
Lemma lem5395229 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395230 : term407 = term399.
Proof. exact (MK_COMB (@lem5395229) (@lem5395228)). Qed.
Lemma lem5395231 : term408 = term401.
Proof. exact (MK_COMB (@lem5395230) (@lem5395218)). Qed.
Lemma lem5395233 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5395234 : term401 = term118.
Proof. exact (@lem5395233 term7). Qed.
Lemma lem5395235 : term408 = term118.
Proof. exact (TRANS (@lem5395231) (@lem5395234)). Qed.
Lemma lem5395236 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395237 : term410 = term228.
Proof. exact (MK_COMB (@lem5395236) (@lem5395235)). Qed.
Lemma lem5395238 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5395239 : term411 = term230.
Proof. exact (MK_COMB (@lem5395237) (@lem5395238)). Qed.
Lemma lem5395241 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395242 : term230 = term118.
Proof. exact (@lem5395241 term7). Qed.
Lemma lem5395243 : term411 = term118.
Proof. exact (TRANS (@lem5395239) (@lem5395242)). Qed.
Lemma lem5395245 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395246 : term180 = term181.
Proof. exact (@lem5395245 term7 term7). Qed.
Lemma lem5395247 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395248 : term183 = term7.
Proof. exact (EQ_MP (@lem5395247) (@lem940073)). Qed.
Lemma lem5395249 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395250 : term181 = term127.
Proof. exact (MK_COMB (@lem5395249) (@lem5395248)). Qed.
Lemma lem5395251 : term180 = term127.
Proof. exact (TRANS (@lem5395246) (@lem5395250)). Qed.
Lemma lem5395252 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5395253 : term232 = term230.
Proof. exact (MK_COMB (@lem5395252) (@lem5395251)). Qed.
Lemma lem5395255 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395256 : term230 = term118.
Proof. exact (@lem5395255 term7). Qed.
Lemma lem5395257 : term232 = term118.
Proof. exact (TRANS (@lem5395253) (@lem5395256)). Qed.
Lemma lem5395258 : term118 = term232.
Proof. exact (SYM (@lem5395257)). Qed.
Lemma lem5395259 : term411 = term232.
Proof. exact (TRANS (@lem5395243) (@lem5395258)). Qed.
Lemma lem5395260 : term402 = term168.
Proof. exact (@lem5395210 (@lem5395259)). Qed.
Lemma lem5395261 : term401 = term168.
Proof. exact (TRANS (@lem5395176) (@lem5395260)). Qed.
Lemma lem5395263 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5395264 : term168 = term118.
Proof. exact (@lem5395263 term118). Qed.
Lemma lem5395265 : term401 = term118.
Proof. exact (TRANS (@lem5395261) (@lem5395264)). Qed.
Lemma lem5395266 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395267 : term412 = term228.
Proof. exact (MK_COMB (@lem5395266) (@lem5395265)). Qed.
Lemma lem5395268 (_69873 : int) : (real_of_int _69873) = (real_of_int _69873).
Proof. exact (eq_refl (real_of_int _69873)). Qed.
Lemma lem5395269 (_69873 : int) : (term398 _69873) = (term413 _69873).
Proof. exact (MK_COMB (@lem5395267) (@lem5395268 _69873)). Qed.
Lemma lem5395270 (_69873 : int) : (term397 _69873) = (term413 _69873).
Proof. exact (TRANS (@lem5395167 _69873) (@lem5395269 _69873)). Qed.
Lemma lem5395271 (_69873 : int) : (term413 _69873) = term118.
Proof. exact (@lem1982719 (real_of_int _69873)). Qed.
Lemma lem5395272 (_69873 : int) : (term397 _69873) = term118.
Proof. exact (TRANS (@lem5395270 _69873) (@lem5395271 _69873)). Qed.
Lemma lem5395273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395274 (_69873 : int) : (term414 _69873) = term415.
Proof. exact (MK_COMB (@lem5395273) (@lem5395272 _69873)). Qed.
Lemma lem5395275 (_69874 : int) : (term416 _69874) = (term417 _69874).
Proof. exact (@lem1982763 (term209 _69874) (real_of_int _69874) term171). Qed.
Lemma lem5395276 (_69874 : int) : (term418 _69874) = (term398 _69874).
Proof. exact (@lem1982713 term171 (real_of_int _69874)). Qed.
Lemma lem5395278 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395279 : term127 = term196.
Proof. exact (@lem5395278 term7). Qed.
Lemma lem5395281 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395282 : term171 = term172.
Proof. exact (@lem5395281 term7). Qed.
Lemma lem5395283 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395284 : term399 = term400.
Proof. exact (MK_COMB (@lem5395283) (@lem5395282)). Qed.
Lemma lem5395285 : term401 = term402.
Proof. exact (MK_COMB (@lem5395284) (@lem5395279)). Qed.
Lemma lem5395286 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5395288 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395289 : term218 = term219.
Proof. exact (@lem5395288 (NUMERAL 0) term7). Qed.
Lemma lem5395290 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395291 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395292 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395291 h1) (fun h1 : term219 = True => @lem5395290)). Qed.
Lemma lem5395293 : term219 = True.
Proof. exact (EQ_MP (@lem5395292) (@lem5395290)). Qed.
Lemma lem5395294 : term218 = True.
Proof. exact (TRANS (@lem5395289) (@lem5395293)). Qed.
Lemma lem5395295 : True = term218.
Proof. exact (SYM (@lem5395294)). Qed.
Lemma lem5395296 : term218.
Proof. exact (EQ_MP (@lem5395295) (@lem0)). Qed.
Lemma lem5395297 : term404.
Proof. exact (@lem5395286 (@lem5395296)). Qed.
Lemma lem5395299 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395300 : term218 = term219.
Proof. exact (@lem5395299 (NUMERAL 0) term7). Qed.
Lemma lem5395301 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395302 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395303 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395302 h1) (fun h1 : term219 = True => @lem5395301)). Qed.
Lemma lem5395304 : term219 = True.
Proof. exact (EQ_MP (@lem5395303) (@lem5395301)). Qed.
Lemma lem5395305 : term218 = True.
Proof. exact (TRANS (@lem5395300) (@lem5395304)). Qed.
Lemma lem5395306 : True = term218.
Proof. exact (SYM (@lem5395305)). Qed.
Lemma lem5395307 : term218.
Proof. exact (EQ_MP (@lem5395306) (@lem0)). Qed.
Lemma lem5395308 : term405.
Proof. exact (@lem5395297 (@lem5395307)). Qed.
Lemma lem5395310 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395311 : term218 = term219.
Proof. exact (@lem5395310 (NUMERAL 0) term7). Qed.
Lemma lem5395312 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395313 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395314 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395313 h1) (fun h1 : term219 = True => @lem5395312)). Qed.
Lemma lem5395315 : term219 = True.
Proof. exact (EQ_MP (@lem5395314) (@lem5395312)). Qed.
Lemma lem5395316 : term218 = True.
Proof. exact (TRANS (@lem5395311) (@lem5395315)). Qed.
Lemma lem5395317 : True = term218.
Proof. exact (SYM (@lem5395316)). Qed.
Lemma lem5395318 : term218.
Proof. exact (EQ_MP (@lem5395317) (@lem0)). Qed.
Lemma lem5395319 : term406.
Proof. exact (@lem5395308 (@lem5395318)). Qed.
Lemma lem5395321 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395322 : term180 = term181.
Proof. exact (@lem5395321 term7 term7). Qed.
Lemma lem5395323 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395324 : term183 = term7.
Proof. exact (EQ_MP (@lem5395323) (@lem940073)). Qed.
Lemma lem5395325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395326 : term181 = term127.
Proof. exact (MK_COMB (@lem5395325) (@lem5395324)). Qed.
Lemma lem5395327 : term180 = term127.
Proof. exact (TRANS (@lem5395322) (@lem5395326)). Qed.
Lemma lem5395329 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5395330 : term197 = term202.
Proof. exact (@lem5395329 term7 term7). Qed.
Lemma lem5395331 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395332 : term183 = term7.
Proof. exact (EQ_MP (@lem5395331) (@lem940073)). Qed.
Lemma lem5395333 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395334 : term181 = term127.
Proof. exact (MK_COMB (@lem5395333) (@lem5395332)). Qed.
Lemma lem5395335 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5395336 : term202 = term171.
Proof. exact (MK_COMB (@lem5395335) (@lem5395334)). Qed.
Lemma lem5395337 : term197 = term171.
Proof. exact (TRANS (@lem5395330) (@lem5395336)). Qed.
Lemma lem5395338 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395339 : term407 = term399.
Proof. exact (MK_COMB (@lem5395338) (@lem5395337)). Qed.
Lemma lem5395340 : term408 = term401.
Proof. exact (MK_COMB (@lem5395339) (@lem5395327)). Qed.
Lemma lem5395342 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5395343 : term401 = term118.
Proof. exact (@lem5395342 term7). Qed.
Lemma lem5395344 : term408 = term118.
Proof. exact (TRANS (@lem5395340) (@lem5395343)). Qed.
Lemma lem5395345 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395346 : term410 = term228.
Proof. exact (MK_COMB (@lem5395345) (@lem5395344)). Qed.
Lemma lem5395347 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5395348 : term411 = term230.
Proof. exact (MK_COMB (@lem5395346) (@lem5395347)). Qed.
Lemma lem5395350 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395351 : term230 = term118.
Proof. exact (@lem5395350 term7). Qed.
Lemma lem5395352 : term411 = term118.
Proof. exact (TRANS (@lem5395348) (@lem5395351)). Qed.
Lemma lem5395354 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395355 : term180 = term181.
Proof. exact (@lem5395354 term7 term7). Qed.
Lemma lem5395356 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395357 : term183 = term7.
Proof. exact (EQ_MP (@lem5395356) (@lem940073)). Qed.
Lemma lem5395358 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395359 : term181 = term127.
Proof. exact (MK_COMB (@lem5395358) (@lem5395357)). Qed.
Lemma lem5395360 : term180 = term127.
Proof. exact (TRANS (@lem5395355) (@lem5395359)). Qed.
Lemma lem5395361 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5395362 : term232 = term230.
Proof. exact (MK_COMB (@lem5395361) (@lem5395360)). Qed.
Lemma lem5395364 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395365 : term230 = term118.
Proof. exact (@lem5395364 term7). Qed.
Lemma lem5395366 : term232 = term118.
Proof. exact (TRANS (@lem5395362) (@lem5395365)). Qed.
Lemma lem5395367 : term118 = term232.
Proof. exact (SYM (@lem5395366)). Qed.
Lemma lem5395368 : term411 = term232.
Proof. exact (TRANS (@lem5395352) (@lem5395367)). Qed.
Lemma lem5395369 : term402 = term168.
Proof. exact (@lem5395319 (@lem5395368)). Qed.
Lemma lem5395370 : term401 = term168.
Proof. exact (TRANS (@lem5395285) (@lem5395369)). Qed.
Lemma lem5395372 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5395373 : term168 = term118.
Proof. exact (@lem5395372 term118). Qed.
Lemma lem5395374 : term401 = term118.
Proof. exact (TRANS (@lem5395370) (@lem5395373)). Qed.
Lemma lem5395375 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395376 : term412 = term228.
Proof. exact (MK_COMB (@lem5395375) (@lem5395374)). Qed.
Lemma lem5395377 (_69874 : int) : (real_of_int _69874) = (real_of_int _69874).
Proof. exact (eq_refl (real_of_int _69874)). Qed.
Lemma lem5395378 (_69874 : int) : (term398 _69874) = (term413 _69874).
Proof. exact (MK_COMB (@lem5395376) (@lem5395377 _69874)). Qed.
Lemma lem5395379 (_69874 : int) : (term418 _69874) = (term413 _69874).
Proof. exact (TRANS (@lem5395276 _69874) (@lem5395378 _69874)). Qed.
Lemma lem5395380 (_69874 : int) : (term413 _69874) = term118.
Proof. exact (@lem1982719 (real_of_int _69874)). Qed.
Lemma lem5395381 (_69874 : int) : (term418 _69874) = term118.
Proof. exact (TRANS (@lem5395379 _69874) (@lem5395380 _69874)). Qed.
Lemma lem5395382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395383 (_69874 : int) : (term419 _69874) = term415.
Proof. exact (MK_COMB (@lem5395382) (@lem5395381 _69874)). Qed.
Lemma lem5395384 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5395385 (_69874 : int) : (term417 _69874) = term420.
Proof. exact (MK_COMB (@lem5395383 _69874) (@lem5395384)). Qed.
Lemma lem5395386 (_69874 : int) : (term416 _69874) = term420.
Proof. exact (TRANS (@lem5395275 _69874) (@lem5395385 _69874)). Qed.
Lemma lem5395387 : term420 = term171.
Proof. exact (@lem1982721 term171). Qed.
Lemma lem5395388 (_69874 : int) : (term416 _69874) = term171.
Proof. exact (TRANS (@lem5395386 _69874) (@lem5395387)). Qed.
Lemma lem5395389 (_69873 : int) (_69874 : int) : (term395 _69873 _69874) = term420.
Proof. exact (MK_COMB (@lem5395274 _69873) (@lem5395388 _69874)). Qed.
Lemma lem5395390 (_69873 : int) (_69874 : int) : (term394 _69873 _69874) = term420.
Proof. exact (TRANS (@lem5395166 _69873 _69874) (@lem5395389 _69873 _69874)). Qed.
Lemma lem5395391 : term420 = term171.
Proof. exact (@lem1982721 term171). Qed.
Lemma lem5395392 (_69873 : int) (_69874 : int) : (term394 _69873 _69874) = term171.
Proof. exact (TRANS (@lem5395390 _69873 _69874) (@lem5395391)). Qed.
Lemma lem5395393 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5395394 (_69873 : int) (_69874 : int) : (term421 _69873 _69874) = term422.
Proof. exact (MK_COMB (@lem5395393) (@lem5395392 _69873 _69874)). Qed.
Lemma lem5395395 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395396 (_69873 : int) (_69874 : int) : (term393 _69873 _69874) = term423.
Proof. exact (MK_COMB (@lem5395394 _69873 _69874) (@lem5395395)). Qed.
Lemma lem5395397 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : term423.
Proof. exact (EQ_MP (@lem5395396 _69873 _69874) (@lem5395165 _69873 _69874 h1)). Qed.
Lemma lem5395399 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5395400 : term423 = term424.
Proof. exact (@lem5395399 term118 term171). Qed.
Lemma lem5395402 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395403 : term171 = term172.
Proof. exact (@lem5395402 term7). Qed.
Lemma lem5395405 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395406 : term118 = term168.
Proof. exact (@lem5395405 (NUMERAL 0)). Qed.
Lemma lem5395407 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5395408 : term120 = term425.
Proof. exact (MK_COMB (@lem5395407) (@lem5395406)). Qed.
Lemma lem5395409 : term424 = term426.
Proof. exact (MK_COMB (@lem5395408) (@lem5395403)). Qed.
Lemma lem5395410 : term427.
Proof. exact (@lem1980026 term118 term127 term171 term127). Qed.
Lemma lem5395412 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395413 : term218 = term219.
Proof. exact (@lem5395412 (NUMERAL 0) term7). Qed.
Lemma lem5395414 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395415 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395416 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395415 h1) (fun h1 : term219 = True => @lem5395414)). Qed.
Lemma lem5395417 : term219 = True.
Proof. exact (EQ_MP (@lem5395416) (@lem5395414)). Qed.
Lemma lem5395418 : term218 = True.
Proof. exact (TRANS (@lem5395413) (@lem5395417)). Qed.
Lemma lem5395419 : True = term218.
Proof. exact (SYM (@lem5395418)). Qed.
Lemma lem5395420 : term218.
Proof. exact (EQ_MP (@lem5395419) (@lem0)). Qed.
Lemma lem5395421 : term428.
Proof. exact (@lem5395410 (@lem5395420)). Qed.
Lemma lem5395423 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395424 : term218 = term219.
Proof. exact (@lem5395423 (NUMERAL 0) term7). Qed.
Lemma lem5395425 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395426 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395427 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395426 h1) (fun h1 : term219 = True => @lem5395425)). Qed.
Lemma lem5395428 : term219 = True.
Proof. exact (EQ_MP (@lem5395427) (@lem5395425)). Qed.
Lemma lem5395429 : term218 = True.
Proof. exact (TRANS (@lem5395424) (@lem5395428)). Qed.
Lemma lem5395430 : True = term218.
Proof. exact (SYM (@lem5395429)). Qed.
Lemma lem5395431 : term218.
Proof. exact (EQ_MP (@lem5395430) (@lem0)). Qed.
Lemma lem5395432 : term426 = term429.
Proof. exact (@lem5395421 (@lem5395431)). Qed.
Lemma lem5395434 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5395435 : term197 = term202.
Proof. exact (@lem5395434 term7 term7). Qed.
Lemma lem5395436 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395437 : term183 = term7.
Proof. exact (EQ_MP (@lem5395436) (@lem940073)). Qed.
Lemma lem5395438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395439 : term181 = term127.
Proof. exact (MK_COMB (@lem5395438) (@lem5395437)). Qed.
Lemma lem5395440 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5395441 : term202 = term171.
Proof. exact (MK_COMB (@lem5395440) (@lem5395439)). Qed.
Lemma lem5395442 : term197 = term171.
Proof. exact (TRANS (@lem5395435) (@lem5395441)). Qed.
Lemma lem5395444 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395445 : term230 = term118.
Proof. exact (@lem5395444 term7). Qed.
Lemma lem5395446 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5395447 : term430 = term120.
Proof. exact (MK_COMB (@lem5395446) (@lem5395445)). Qed.
Lemma lem5395448 : term429 = term424.
Proof. exact (MK_COMB (@lem5395447) (@lem5395442)). Qed.
Lemma lem5395450 (m : nat) (n : nat) : (term431 m n) = (term432 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5395451 : term424 = term433.
Proof. exact (@lem5395450 (NUMERAL 0) term7). Qed.
Lemma lem5395452 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395453 (h1 : term220 = (BIT1 0)) : (term7 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5395454 : (term220 = (BIT1 0)) = ((term7 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395453 h1) (fun h1 : (term7 = (NUMERAL 0)) = False => @lem5395452)). Qed.
Lemma lem5395455 : (term7 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5395454) (@lem5395452)). Qed.
Lemma lem5395456 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5395457 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5395458 : term434 = (and True).
Proof. exact (MK_COMB (@lem5395457) (@lem5395456)). Qed.
Lemma lem5395459 : term433 = (True /\ False).
Proof. exact (MK_COMB (@lem5395458) (@lem5395455)). Qed.
Lemma lem5395461 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5395462 : term433 = False.
Proof. exact (TRANS (@lem5395459) (@lem5395461)). Qed.
Lemma lem5395463 : term424 = False.
Proof. exact (TRANS (@lem5395451) (@lem5395462)). Qed.
Lemma lem5395464 : term429 = False.
Proof. exact (TRANS (@lem5395448) (@lem5395463)). Qed.
Lemma lem5395465 : term426 = False.
Proof. exact (TRANS (@lem5395432) (@lem5395464)). Qed.
Lemma lem5395466 : term424 = False.
Proof. exact (TRANS (@lem5395409) (@lem5395465)). Qed.
Lemma lem5395467 : term423 = False.
Proof. exact (TRANS (@lem5395400) (@lem5395466)). Qed.
Lemma lem5395468 (_69873 : int) (_69874 : int) (h1 : term354 _69873 _69874) : False.
Proof. exact (EQ_MP (@lem5395467) (@lem5395397 _69873 _69874 h1)). Qed.
Lemma lem5395469 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term435 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5395470 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term350 _69873 _69874.
Proof. exact (proj2 (@lem5395469 _69873 _69874 h1)). Qed.
Lemma lem5395472 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term337 _69873 _69874.
Proof. exact (proj2 (@lem5395470 _69873 _69874 h1)). Qed.
Lemma lem5395474 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term310 _69873 _69874.
Proof. exact (proj2 (@lem5395472 _69873 _69874 h1)). Qed.
Lemma lem5395475 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term300 _69874 _69873.
Proof. exact (proj1 (@lem5395472 _69873 _69874 h1)). Qed.
Lemma lem5395476 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : (real_of_int _69873) = term118.
Proof. exact (proj2 (@lem5395475 _69873 _69874 h1)). Qed.
Lemma lem5395477 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term297 _69874.
Proof. exact (proj1 (@lem5395475 _69873 _69874 h1)). Qed.
Lemma lem5395479 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5395480 : term355 = term218.
Proof. exact (@lem5395479 term118 term127). Qed.
Lemma lem5395482 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395483 : term127 = term196.
Proof. exact (@lem5395482 term7). Qed.
Lemma lem5395485 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395486 : term118 = term168.
Proof. exact (@lem5395485 (NUMERAL 0)). Qed.
Lemma lem5395487 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395488 : term356 = term357.
Proof. exact (MK_COMB (@lem5395487) (@lem5395486)). Qed.
Lemma lem5395489 : term218 = term358.
Proof. exact (MK_COMB (@lem5395488) (@lem5395483)). Qed.
Lemma lem5395490 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5395492 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395493 : term218 = term219.
Proof. exact (@lem5395492 (NUMERAL 0) term7). Qed.
Lemma lem5395494 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395495 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395496 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395495 h1) (fun h1 : term219 = True => @lem5395494)). Qed.
Lemma lem5395497 : term219 = True.
Proof. exact (EQ_MP (@lem5395496) (@lem5395494)). Qed.
Lemma lem5395498 : term218 = True.
Proof. exact (TRANS (@lem5395493) (@lem5395497)). Qed.
Lemma lem5395499 : True = term218.
Proof. exact (SYM (@lem5395498)). Qed.
Lemma lem5395500 : term218.
Proof. exact (EQ_MP (@lem5395499) (@lem0)). Qed.
Lemma lem5395501 : term360.
Proof. exact (@lem5395490 (@lem5395500)). Qed.
Lemma lem5395503 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395504 : term218 = term219.
Proof. exact (@lem5395503 (NUMERAL 0) term7). Qed.
Lemma lem5395505 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395506 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395507 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395506 h1) (fun h1 : term219 = True => @lem5395505)). Qed.
Lemma lem5395508 : term219 = True.
Proof. exact (EQ_MP (@lem5395507) (@lem5395505)). Qed.
Lemma lem5395509 : term218 = True.
Proof. exact (TRANS (@lem5395504) (@lem5395508)). Qed.
Lemma lem5395510 : True = term218.
Proof. exact (SYM (@lem5395509)). Qed.
Lemma lem5395511 : term218.
Proof. exact (EQ_MP (@lem5395510) (@lem0)). Qed.
Lemma lem5395512 : term358 = term361.
Proof. exact (@lem5395501 (@lem5395511)). Qed.
Lemma lem5395514 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395515 : term180 = term181.
Proof. exact (@lem5395514 term7 term7). Qed.
Lemma lem5395516 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395517 : term183 = term7.
Proof. exact (EQ_MP (@lem5395516) (@lem940073)). Qed.
Lemma lem5395518 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395519 : term181 = term127.
Proof. exact (MK_COMB (@lem5395518) (@lem5395517)). Qed.
Lemma lem5395520 : term180 = term127.
Proof. exact (TRANS (@lem5395515) (@lem5395519)). Qed.
Lemma lem5395522 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395523 : term230 = term118.
Proof. exact (@lem5395522 term7). Qed.
Lemma lem5395524 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395525 : term362 = term356.
Proof. exact (MK_COMB (@lem5395524) (@lem5395523)). Qed.
Lemma lem5395526 : term361 = term218.
Proof. exact (MK_COMB (@lem5395525) (@lem5395520)). Qed.
Lemma lem5395528 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395529 : term218 = term219.
Proof. exact (@lem5395528 (NUMERAL 0) term7). Qed.
Lemma lem5395530 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395531 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395532 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395531 h1) (fun h1 : term219 = True => @lem5395530)). Qed.
Lemma lem5395533 : term219 = True.
Proof. exact (EQ_MP (@lem5395532) (@lem5395530)). Qed.
Lemma lem5395534 : term218 = True.
Proof. exact (TRANS (@lem5395529) (@lem5395533)). Qed.
Lemma lem5395535 : term361 = True.
Proof. exact (TRANS (@lem5395526) (@lem5395534)). Qed.
Lemma lem5395536 : term358 = True.
Proof. exact (TRANS (@lem5395512) (@lem5395535)). Qed.
Lemma lem5395537 : term218 = True.
Proof. exact (TRANS (@lem5395489) (@lem5395536)). Qed.
Lemma lem5395538 : term355 = True.
Proof. exact (TRANS (@lem5395480) (@lem5395537)). Qed.
Lemma lem5395539 : True = term355.
Proof. exact (SYM (@lem5395538)). Qed.
Lemma lem5395540 : term355.
Proof. exact (EQ_MP (@lem5395539) (@lem0)). Qed.
Lemma lem5395541 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term363 _69873 _69874.
Proof. exact (conj (@lem5395540) (@lem5395474 _69873 _69874 h1)). Qed.
Lemma lem5395543 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5395544 (_69873 : int) (_69874 : int) : term365 _69873 _69874.
Proof. exact (@lem5395543 term127 (term307 _69873 _69874)). Qed.
Lemma lem5395545 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term366 _69873 _69874.
Proof. exact (@lem5395544 _69873 _69874 (@lem5395541 _69873 _69874 h1)). Qed.
Lemma lem5395546 (_69873 : int) (_69874 : int) : (term367 _69873 _69874) = (term307 _69873 _69874).
Proof. exact (@lem1982733 (term307 _69873 _69874)). Qed.
Lemma lem5395547 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5395548 (_69873 : int) (_69874 : int) : (term368 _69873 _69874) = (term309 _69873 _69874).
Proof. exact (MK_COMB (@lem5395547) (@lem5395546 _69873 _69874)). Qed.
Lemma lem5395549 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395550 (_69873 : int) (_69874 : int) : (term366 _69873 _69874) = (term310 _69873 _69874).
Proof. exact (MK_COMB (@lem5395548 _69873 _69874) (@lem5395549)). Qed.
Lemma lem5395551 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term310 _69873 _69874.
Proof. exact (EQ_MP (@lem5395550 _69873 _69874) (@lem5395545 _69873 _69874 h1)). Qed.
Lemma lem5395553 (y : real) : term369 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5395554 (_69873 : int) : term436 _69873.
Proof. exact (@lem5395553 (real_of_int _69873)). Qed.
Lemma lem5395555 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term437 _69873.
Proof. exact (@lem5395554 _69873 (@lem5395476 _69873 _69874 h1)). Qed.
Lemma lem5395556 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term438 _69873.
Proof. exact (@lem5395555 _69873 _69874 h1 term127). Qed.
Lemma lem5395557 (_69873 : int) : (term438 _69873) = ((term385 _69873) = term118).
Proof. exact (eq_refl (term438 _69873)). Qed.
Lemma lem5395558 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : (term385 _69873) = term118.
Proof. exact (EQ_MP (@lem5395557 _69873) (@lem5395556 _69873 _69874 h1)). Qed.
Lemma lem5395559 (_69873 : int) : (term385 _69873) = (real_of_int _69873).
Proof. exact (@lem1982733 (real_of_int _69873)). Qed.
Lemma lem5395560 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5395561 (_69873 : int) : (term439 _69873) = (term144 _69873).
Proof. exact (MK_COMB (@lem5395560) (@lem5395559 _69873)). Qed.
Lemma lem5395562 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395563 (_69873 : int) : ((term385 _69873) = term118) = ((real_of_int _69873) = term118).
Proof. exact (MK_COMB (@lem5395561 _69873) (@lem5395562)). Qed.
Lemma lem5395564 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : (real_of_int _69873) = term118.
Proof. exact (EQ_MP (@lem5395563 _69873) (@lem5395558 _69873 _69874 h1)). Qed.
Lemma lem5395565 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term440 _69873 _69874.
Proof. exact (conj (@lem5395564 _69873 _69874 h1) (@lem5395551 _69873 _69874 h1)). Qed.
Lemma lem5395567 (x : real) (y : real) : term391 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5395568 (_69873 : int) (_69874 : int) : term441 _69873 _69874.
Proof. exact (@lem5395567 (real_of_int _69873) (term307 _69873 _69874)). Qed.
Lemma lem5395569 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term442 _69873 _69874.
Proof. exact (@lem5395568 _69873 _69874 (@lem5395565 _69873 _69874 h1)). Qed.
Lemma lem5395570 (_69873 : int) (_69874 : int) : (term443 _69873 _69874) = (term444 _69873 _69874).
Proof. exact (@lem1982763 (real_of_int _69873) (term209 _69873) (term396 _69874)). Qed.
Lemma lem5395571 (_69873 : int) : (term397 _69873) = (term398 _69873).
Proof. exact (@lem1982715 term171 (real_of_int _69873)). Qed.
Lemma lem5395573 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395574 : term127 = term196.
Proof. exact (@lem5395573 term7). Qed.
Lemma lem5395576 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395577 : term171 = term172.
Proof. exact (@lem5395576 term7). Qed.
Lemma lem5395578 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395579 : term399 = term400.
Proof. exact (MK_COMB (@lem5395578) (@lem5395577)). Qed.
Lemma lem5395580 : term401 = term402.
Proof. exact (MK_COMB (@lem5395579) (@lem5395574)). Qed.
Lemma lem5395581 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5395583 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395584 : term218 = term219.
Proof. exact (@lem5395583 (NUMERAL 0) term7). Qed.
Lemma lem5395585 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395586 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395587 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395586 h1) (fun h1 : term219 = True => @lem5395585)). Qed.
Lemma lem5395588 : term219 = True.
Proof. exact (EQ_MP (@lem5395587) (@lem5395585)). Qed.
Lemma lem5395589 : term218 = True.
Proof. exact (TRANS (@lem5395584) (@lem5395588)). Qed.
Lemma lem5395590 : True = term218.
Proof. exact (SYM (@lem5395589)). Qed.
Lemma lem5395591 : term218.
Proof. exact (EQ_MP (@lem5395590) (@lem0)). Qed.
Lemma lem5395592 : term404.
Proof. exact (@lem5395581 (@lem5395591)). Qed.
Lemma lem5395594 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395595 : term218 = term219.
Proof. exact (@lem5395594 (NUMERAL 0) term7). Qed.
Lemma lem5395596 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395597 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395598 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395597 h1) (fun h1 : term219 = True => @lem5395596)). Qed.
Lemma lem5395599 : term219 = True.
Proof. exact (EQ_MP (@lem5395598) (@lem5395596)). Qed.
Lemma lem5395600 : term218 = True.
Proof. exact (TRANS (@lem5395595) (@lem5395599)). Qed.
Lemma lem5395601 : True = term218.
Proof. exact (SYM (@lem5395600)). Qed.
Lemma lem5395602 : term218.
Proof. exact (EQ_MP (@lem5395601) (@lem0)). Qed.
Lemma lem5395603 : term405.
Proof. exact (@lem5395592 (@lem5395602)). Qed.
Lemma lem5395605 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395606 : term218 = term219.
Proof. exact (@lem5395605 (NUMERAL 0) term7). Qed.
Lemma lem5395607 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395608 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395609 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395608 h1) (fun h1 : term219 = True => @lem5395607)). Qed.
Lemma lem5395610 : term219 = True.
Proof. exact (EQ_MP (@lem5395609) (@lem5395607)). Qed.
Lemma lem5395611 : term218 = True.
Proof. exact (TRANS (@lem5395606) (@lem5395610)). Qed.
Lemma lem5395612 : True = term218.
Proof. exact (SYM (@lem5395611)). Qed.
Lemma lem5395613 : term218.
Proof. exact (EQ_MP (@lem5395612) (@lem0)). Qed.
Lemma lem5395614 : term406.
Proof. exact (@lem5395603 (@lem5395613)). Qed.
Lemma lem5395616 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395617 : term180 = term181.
Proof. exact (@lem5395616 term7 term7). Qed.
Lemma lem5395618 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395619 : term183 = term7.
Proof. exact (EQ_MP (@lem5395618) (@lem940073)). Qed.
Lemma lem5395620 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395621 : term181 = term127.
Proof. exact (MK_COMB (@lem5395620) (@lem5395619)). Qed.
Lemma lem5395622 : term180 = term127.
Proof. exact (TRANS (@lem5395617) (@lem5395621)). Qed.
Lemma lem5395624 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5395625 : term197 = term202.
Proof. exact (@lem5395624 term7 term7). Qed.
Lemma lem5395626 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395627 : term183 = term7.
Proof. exact (EQ_MP (@lem5395626) (@lem940073)). Qed.
Lemma lem5395628 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395629 : term181 = term127.
Proof. exact (MK_COMB (@lem5395628) (@lem5395627)). Qed.
Lemma lem5395630 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5395631 : term202 = term171.
Proof. exact (MK_COMB (@lem5395630) (@lem5395629)). Qed.
Lemma lem5395632 : term197 = term171.
Proof. exact (TRANS (@lem5395625) (@lem5395631)). Qed.
Lemma lem5395633 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395634 : term407 = term399.
Proof. exact (MK_COMB (@lem5395633) (@lem5395632)). Qed.
Lemma lem5395635 : term408 = term401.
Proof. exact (MK_COMB (@lem5395634) (@lem5395622)). Qed.
Lemma lem5395637 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5395638 : term401 = term118.
Proof. exact (@lem5395637 term7). Qed.
Lemma lem5395639 : term408 = term118.
Proof. exact (TRANS (@lem5395635) (@lem5395638)). Qed.
Lemma lem5395640 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395641 : term410 = term228.
Proof. exact (MK_COMB (@lem5395640) (@lem5395639)). Qed.
Lemma lem5395642 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5395643 : term411 = term230.
Proof. exact (MK_COMB (@lem5395641) (@lem5395642)). Qed.
Lemma lem5395645 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395646 : term230 = term118.
Proof. exact (@lem5395645 term7). Qed.
Lemma lem5395647 : term411 = term118.
Proof. exact (TRANS (@lem5395643) (@lem5395646)). Qed.
Lemma lem5395649 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395650 : term180 = term181.
Proof. exact (@lem5395649 term7 term7). Qed.
Lemma lem5395651 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395652 : term183 = term7.
Proof. exact (EQ_MP (@lem5395651) (@lem940073)). Qed.
Lemma lem5395653 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395654 : term181 = term127.
Proof. exact (MK_COMB (@lem5395653) (@lem5395652)). Qed.
Lemma lem5395655 : term180 = term127.
Proof. exact (TRANS (@lem5395650) (@lem5395654)). Qed.
Lemma lem5395656 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5395657 : term232 = term230.
Proof. exact (MK_COMB (@lem5395656) (@lem5395655)). Qed.
Lemma lem5395659 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395660 : term230 = term118.
Proof. exact (@lem5395659 term7). Qed.
Lemma lem5395661 : term232 = term118.
Proof. exact (TRANS (@lem5395657) (@lem5395660)). Qed.
Lemma lem5395662 : term118 = term232.
Proof. exact (SYM (@lem5395661)). Qed.
Lemma lem5395663 : term411 = term232.
Proof. exact (TRANS (@lem5395647) (@lem5395662)). Qed.
Lemma lem5395664 : term402 = term168.
Proof. exact (@lem5395614 (@lem5395663)). Qed.
Lemma lem5395665 : term401 = term168.
Proof. exact (TRANS (@lem5395580) (@lem5395664)). Qed.
Lemma lem5395667 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5395668 : term168 = term118.
Proof. exact (@lem5395667 term118). Qed.
Lemma lem5395669 : term401 = term118.
Proof. exact (TRANS (@lem5395665) (@lem5395668)). Qed.
Lemma lem5395670 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395671 : term412 = term228.
Proof. exact (MK_COMB (@lem5395670) (@lem5395669)). Qed.
Lemma lem5395672 (_69873 : int) : (real_of_int _69873) = (real_of_int _69873).
Proof. exact (eq_refl (real_of_int _69873)). Qed.
Lemma lem5395673 (_69873 : int) : (term398 _69873) = (term413 _69873).
Proof. exact (MK_COMB (@lem5395671) (@lem5395672 _69873)). Qed.
Lemma lem5395674 (_69873 : int) : (term397 _69873) = (term413 _69873).
Proof. exact (TRANS (@lem5395571 _69873) (@lem5395673 _69873)). Qed.
Lemma lem5395675 (_69873 : int) : (term413 _69873) = term118.
Proof. exact (@lem1982719 (real_of_int _69873)). Qed.
Lemma lem5395676 (_69873 : int) : (term397 _69873) = term118.
Proof. exact (TRANS (@lem5395674 _69873) (@lem5395675 _69873)). Qed.
Lemma lem5395677 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395678 (_69873 : int) : (term414 _69873) = term415.
Proof. exact (MK_COMB (@lem5395677) (@lem5395676 _69873)). Qed.
Lemma lem5395679 (_69874 : int) : (term396 _69874) = (term396 _69874).
Proof. exact (eq_refl (term396 _69874)). Qed.
Lemma lem5395680 (_69873 : int) (_69874 : int) : (term444 _69873 _69874) = (term445 _69874).
Proof. exact (MK_COMB (@lem5395678 _69873) (@lem5395679 _69874)). Qed.
Lemma lem5395681 (_69873 : int) (_69874 : int) : (term443 _69873 _69874) = (term445 _69874).
Proof. exact (TRANS (@lem5395570 _69873 _69874) (@lem5395680 _69873 _69874)). Qed.
Lemma lem5395682 (_69874 : int) : (term445 _69874) = (term396 _69874).
Proof. exact (@lem1982721 (term396 _69874)). Qed.
Lemma lem5395683 (_69873 : int) (_69874 : int) : (term443 _69873 _69874) = (term396 _69874).
Proof. exact (TRANS (@lem5395681 _69873 _69874) (@lem5395682 _69874)). Qed.
Lemma lem5395684 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5395685 (_69873 : int) (_69874 : int) : (term446 _69873 _69874) = (term447 _69874).
Proof. exact (MK_COMB (@lem5395684) (@lem5395683 _69873 _69874)). Qed.
Lemma lem5395686 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395687 (_69873 : int) (_69874 : int) : (term442 _69873 _69874) = (term448 _69874).
Proof. exact (MK_COMB (@lem5395685 _69873 _69874) (@lem5395686)). Qed.
Lemma lem5395688 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term448 _69874.
Proof. exact (EQ_MP (@lem5395687 _69873 _69874) (@lem5395569 _69873 _69874 h1)). Qed.
Lemma lem5395690 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5395691 : term355 = term218.
Proof. exact (@lem5395690 term118 term127). Qed.
Lemma lem5395693 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395694 : term127 = term196.
Proof. exact (@lem5395693 term7). Qed.
Lemma lem5395696 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395697 : term118 = term168.
Proof. exact (@lem5395696 (NUMERAL 0)). Qed.
Lemma lem5395698 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395699 : term356 = term357.
Proof. exact (MK_COMB (@lem5395698) (@lem5395697)). Qed.
Lemma lem5395700 : term218 = term358.
Proof. exact (MK_COMB (@lem5395699) (@lem5395694)). Qed.
Lemma lem5395701 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5395703 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395704 : term218 = term219.
Proof. exact (@lem5395703 (NUMERAL 0) term7). Qed.
Lemma lem5395705 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395706 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395707 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395706 h1) (fun h1 : term219 = True => @lem5395705)). Qed.
Lemma lem5395708 : term219 = True.
Proof. exact (EQ_MP (@lem5395707) (@lem5395705)). Qed.
Lemma lem5395709 : term218 = True.
Proof. exact (TRANS (@lem5395704) (@lem5395708)). Qed.
Lemma lem5395710 : True = term218.
Proof. exact (SYM (@lem5395709)). Qed.
Lemma lem5395711 : term218.
Proof. exact (EQ_MP (@lem5395710) (@lem0)). Qed.
Lemma lem5395712 : term360.
Proof. exact (@lem5395701 (@lem5395711)). Qed.
Lemma lem5395714 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395715 : term218 = term219.
Proof. exact (@lem5395714 (NUMERAL 0) term7). Qed.
Lemma lem5395716 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395717 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395718 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395717 h1) (fun h1 : term219 = True => @lem5395716)). Qed.
Lemma lem5395719 : term219 = True.
Proof. exact (EQ_MP (@lem5395718) (@lem5395716)). Qed.
Lemma lem5395720 : term218 = True.
Proof. exact (TRANS (@lem5395715) (@lem5395719)). Qed.
Lemma lem5395721 : True = term218.
Proof. exact (SYM (@lem5395720)). Qed.
Lemma lem5395722 : term218.
Proof. exact (EQ_MP (@lem5395721) (@lem0)). Qed.
Lemma lem5395723 : term358 = term361.
Proof. exact (@lem5395712 (@lem5395722)). Qed.
Lemma lem5395725 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395726 : term180 = term181.
Proof. exact (@lem5395725 term7 term7). Qed.
Lemma lem5395727 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395728 : term183 = term7.
Proof. exact (EQ_MP (@lem5395727) (@lem940073)). Qed.
Lemma lem5395729 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395730 : term181 = term127.
Proof. exact (MK_COMB (@lem5395729) (@lem5395728)). Qed.
Lemma lem5395731 : term180 = term127.
Proof. exact (TRANS (@lem5395726) (@lem5395730)). Qed.
Lemma lem5395733 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395734 : term230 = term118.
Proof. exact (@lem5395733 term7). Qed.
Lemma lem5395735 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395736 : term362 = term356.
Proof. exact (MK_COMB (@lem5395735) (@lem5395734)). Qed.
Lemma lem5395737 : term361 = term218.
Proof. exact (MK_COMB (@lem5395736) (@lem5395731)). Qed.
Lemma lem5395739 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395740 : term218 = term219.
Proof. exact (@lem5395739 (NUMERAL 0) term7). Qed.
Lemma lem5395741 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395742 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395743 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395742 h1) (fun h1 : term219 = True => @lem5395741)). Qed.
Lemma lem5395744 : term219 = True.
Proof. exact (EQ_MP (@lem5395743) (@lem5395741)). Qed.
Lemma lem5395745 : term218 = True.
Proof. exact (TRANS (@lem5395740) (@lem5395744)). Qed.
Lemma lem5395746 : term361 = True.
Proof. exact (TRANS (@lem5395737) (@lem5395745)). Qed.
Lemma lem5395747 : term358 = True.
Proof. exact (TRANS (@lem5395723) (@lem5395746)). Qed.
Lemma lem5395748 : term218 = True.
Proof. exact (TRANS (@lem5395700) (@lem5395747)). Qed.
Lemma lem5395749 : term355 = True.
Proof. exact (TRANS (@lem5395691) (@lem5395748)). Qed.
Lemma lem5395750 : True = term355.
Proof. exact (SYM (@lem5395749)). Qed.
Lemma lem5395751 : term355.
Proof. exact (EQ_MP (@lem5395750) (@lem0)). Qed.
Lemma lem5395752 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term449 _69874.
Proof. exact (conj (@lem5395751) (@lem5395688 _69873 _69874 h1)). Qed.
Lemma lem5395754 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5395755 (_69874 : int) : term450 _69874.
Proof. exact (@lem5395754 term127 (term396 _69874)). Qed.
Lemma lem5395756 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term451 _69874.
Proof. exact (@lem5395755 _69874 (@lem5395752 _69873 _69874 h1)). Qed.
Lemma lem5395757 (_69874 : int) : (term452 _69874) = (term396 _69874).
Proof. exact (@lem1982733 (term396 _69874)). Qed.
Lemma lem5395758 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5395759 (_69874 : int) : (term453 _69874) = (term447 _69874).
Proof. exact (MK_COMB (@lem5395758) (@lem5395757 _69874)). Qed.
Lemma lem5395760 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395761 (_69874 : int) : (term451 _69874) = (term448 _69874).
Proof. exact (MK_COMB (@lem5395759 _69874) (@lem5395760)). Qed.
Lemma lem5395762 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term448 _69874.
Proof. exact (EQ_MP (@lem5395761 _69874) (@lem5395756 _69873 _69874 h1)). Qed.
Lemma lem5395764 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5395765 : term355 = term218.
Proof. exact (@lem5395764 term118 term127). Qed.
Lemma lem5395767 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395768 : term127 = term196.
Proof. exact (@lem5395767 term7). Qed.
Lemma lem5395770 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395771 : term118 = term168.
Proof. exact (@lem5395770 (NUMERAL 0)). Qed.
Lemma lem5395772 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395773 : term356 = term357.
Proof. exact (MK_COMB (@lem5395772) (@lem5395771)). Qed.
Lemma lem5395774 : term218 = term358.
Proof. exact (MK_COMB (@lem5395773) (@lem5395768)). Qed.
Lemma lem5395775 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5395777 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395778 : term218 = term219.
Proof. exact (@lem5395777 (NUMERAL 0) term7). Qed.
Lemma lem5395779 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395780 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395781 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395780 h1) (fun h1 : term219 = True => @lem5395779)). Qed.
Lemma lem5395782 : term219 = True.
Proof. exact (EQ_MP (@lem5395781) (@lem5395779)). Qed.
Lemma lem5395783 : term218 = True.
Proof. exact (TRANS (@lem5395778) (@lem5395782)). Qed.
Lemma lem5395784 : True = term218.
Proof. exact (SYM (@lem5395783)). Qed.
Lemma lem5395785 : term218.
Proof. exact (EQ_MP (@lem5395784) (@lem0)). Qed.
Lemma lem5395786 : term360.
Proof. exact (@lem5395775 (@lem5395785)). Qed.
Lemma lem5395788 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395789 : term218 = term219.
Proof. exact (@lem5395788 (NUMERAL 0) term7). Qed.
Lemma lem5395790 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395791 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395792 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395791 h1) (fun h1 : term219 = True => @lem5395790)). Qed.
Lemma lem5395793 : term219 = True.
Proof. exact (EQ_MP (@lem5395792) (@lem5395790)). Qed.
Lemma lem5395794 : term218 = True.
Proof. exact (TRANS (@lem5395789) (@lem5395793)). Qed.
Lemma lem5395795 : True = term218.
Proof. exact (SYM (@lem5395794)). Qed.
Lemma lem5395796 : term218.
Proof. exact (EQ_MP (@lem5395795) (@lem0)). Qed.
Lemma lem5395797 : term358 = term361.
Proof. exact (@lem5395786 (@lem5395796)). Qed.
Lemma lem5395799 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395800 : term180 = term181.
Proof. exact (@lem5395799 term7 term7). Qed.
Lemma lem5395801 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395802 : term183 = term7.
Proof. exact (EQ_MP (@lem5395801) (@lem940073)). Qed.
Lemma lem5395803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395804 : term181 = term127.
Proof. exact (MK_COMB (@lem5395803) (@lem5395802)). Qed.
Lemma lem5395805 : term180 = term127.
Proof. exact (TRANS (@lem5395800) (@lem5395804)). Qed.
Lemma lem5395807 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395808 : term230 = term118.
Proof. exact (@lem5395807 term7). Qed.
Lemma lem5395809 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5395810 : term362 = term356.
Proof. exact (MK_COMB (@lem5395809) (@lem5395808)). Qed.
Lemma lem5395811 : term361 = term218.
Proof. exact (MK_COMB (@lem5395810) (@lem5395805)). Qed.
Lemma lem5395813 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395814 : term218 = term219.
Proof. exact (@lem5395813 (NUMERAL 0) term7). Qed.
Lemma lem5395815 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395816 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395817 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395816 h1) (fun h1 : term219 = True => @lem5395815)). Qed.
Lemma lem5395818 : term219 = True.
Proof. exact (EQ_MP (@lem5395817) (@lem5395815)). Qed.
Lemma lem5395819 : term218 = True.
Proof. exact (TRANS (@lem5395814) (@lem5395818)). Qed.
Lemma lem5395820 : term361 = True.
Proof. exact (TRANS (@lem5395811) (@lem5395819)). Qed.
Lemma lem5395821 : term358 = True.
Proof. exact (TRANS (@lem5395797) (@lem5395820)). Qed.
Lemma lem5395822 : term218 = True.
Proof. exact (TRANS (@lem5395774) (@lem5395821)). Qed.
Lemma lem5395823 : term355 = True.
Proof. exact (TRANS (@lem5395765) (@lem5395822)). Qed.
Lemma lem5395824 : True = term355.
Proof. exact (SYM (@lem5395823)). Qed.
Lemma lem5395825 : term355.
Proof. exact (EQ_MP (@lem5395824) (@lem0)). Qed.
Lemma lem5395826 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term454 _69874.
Proof. exact (conj (@lem5395825) (@lem5395477 _69873 _69874 h1)). Qed.
Lemma lem5395828 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5395829 (_69874 : int) : term455 _69874.
Proof. exact (@lem5395828 term127 (term206 _69874)). Qed.
Lemma lem5395830 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term456 _69874.
Proof. exact (@lem5395829 _69874 (@lem5395826 _69873 _69874 h1)). Qed.
Lemma lem5395831 (_69874 : int) : (term457 _69874) = (term206 _69874).
Proof. exact (@lem1982733 (term206 _69874)). Qed.
Lemma lem5395832 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5395833 (_69874 : int) : (term458 _69874) = (term296 _69874).
Proof. exact (MK_COMB (@lem5395832) (@lem5395831 _69874)). Qed.
Lemma lem5395834 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5395835 (_69874 : int) : (term456 _69874) = (term297 _69874).
Proof. exact (MK_COMB (@lem5395833 _69874) (@lem5395834)). Qed.
Lemma lem5395836 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term297 _69874.
Proof. exact (EQ_MP (@lem5395835 _69874) (@lem5395830 _69873 _69874 h1)). Qed.
Lemma lem5395837 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term459 _69874.
Proof. exact (conj (@lem5395836 _69873 _69874 h1) (@lem5395762 _69873 _69874 h1)). Qed.
Lemma lem5395839 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5395840 (_69874 : int) : term461 _69874.
Proof. exact (@lem5395839 (term206 _69874) (term396 _69874)). Qed.
Lemma lem5395841 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term462 _69874.
Proof. exact (@lem5395840 _69874 (@lem5395837 _69873 _69874 h1)). Qed.
Lemma lem5395842 (_69874 : int) : (term463 _69874) = (term464 _69874).
Proof. exact (@lem1982753 (term209 _69874) (real_of_int _69874) term171 term171). Qed.
Lemma lem5395843 (_69874 : int) : (term418 _69874) = (term398 _69874).
Proof. exact (@lem1982713 term171 (real_of_int _69874)). Qed.
Lemma lem5395845 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5395846 : term127 = term196.
Proof. exact (@lem5395845 term7). Qed.
Lemma lem5395848 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395849 : term171 = term172.
Proof. exact (@lem5395848 term7). Qed.
Lemma lem5395850 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395851 : term399 = term400.
Proof. exact (MK_COMB (@lem5395850) (@lem5395849)). Qed.
Lemma lem5395852 : term401 = term402.
Proof. exact (MK_COMB (@lem5395851) (@lem5395846)). Qed.
Lemma lem5395853 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5395855 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395856 : term218 = term219.
Proof. exact (@lem5395855 (NUMERAL 0) term7). Qed.
Lemma lem5395857 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395858 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395859 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395858 h1) (fun h1 : term219 = True => @lem5395857)). Qed.
Lemma lem5395860 : term219 = True.
Proof. exact (EQ_MP (@lem5395859) (@lem5395857)). Qed.
Lemma lem5395861 : term218 = True.
Proof. exact (TRANS (@lem5395856) (@lem5395860)). Qed.
Lemma lem5395862 : True = term218.
Proof. exact (SYM (@lem5395861)). Qed.
Lemma lem5395863 : term218.
Proof. exact (EQ_MP (@lem5395862) (@lem0)). Qed.
Lemma lem5395864 : term404.
Proof. exact (@lem5395853 (@lem5395863)). Qed.
Lemma lem5395866 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395867 : term218 = term219.
Proof. exact (@lem5395866 (NUMERAL 0) term7). Qed.
Lemma lem5395868 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395869 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395870 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395869 h1) (fun h1 : term219 = True => @lem5395868)). Qed.
Lemma lem5395871 : term219 = True.
Proof. exact (EQ_MP (@lem5395870) (@lem5395868)). Qed.
Lemma lem5395872 : term218 = True.
Proof. exact (TRANS (@lem5395867) (@lem5395871)). Qed.
Lemma lem5395873 : True = term218.
Proof. exact (SYM (@lem5395872)). Qed.
Lemma lem5395874 : term218.
Proof. exact (EQ_MP (@lem5395873) (@lem0)). Qed.
Lemma lem5395875 : term405.
Proof. exact (@lem5395864 (@lem5395874)). Qed.
Lemma lem5395877 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395878 : term218 = term219.
Proof. exact (@lem5395877 (NUMERAL 0) term7). Qed.
Lemma lem5395879 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395880 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395881 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395880 h1) (fun h1 : term219 = True => @lem5395879)). Qed.
Lemma lem5395882 : term219 = True.
Proof. exact (EQ_MP (@lem5395881) (@lem5395879)). Qed.
Lemma lem5395883 : term218 = True.
Proof. exact (TRANS (@lem5395878) (@lem5395882)). Qed.
Lemma lem5395884 : True = term218.
Proof. exact (SYM (@lem5395883)). Qed.
Lemma lem5395885 : term218.
Proof. exact (EQ_MP (@lem5395884) (@lem0)). Qed.
Lemma lem5395886 : term406.
Proof. exact (@lem5395875 (@lem5395885)). Qed.
Lemma lem5395888 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395889 : term180 = term181.
Proof. exact (@lem5395888 term7 term7). Qed.
Lemma lem5395890 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395891 : term183 = term7.
Proof. exact (EQ_MP (@lem5395890) (@lem940073)). Qed.
Lemma lem5395892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395893 : term181 = term127.
Proof. exact (MK_COMB (@lem5395892) (@lem5395891)). Qed.
Lemma lem5395894 : term180 = term127.
Proof. exact (TRANS (@lem5395889) (@lem5395893)). Qed.
Lemma lem5395896 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5395897 : term197 = term202.
Proof. exact (@lem5395896 term7 term7). Qed.
Lemma lem5395898 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395899 : term183 = term7.
Proof. exact (EQ_MP (@lem5395898) (@lem940073)). Qed.
Lemma lem5395900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395901 : term181 = term127.
Proof. exact (MK_COMB (@lem5395900) (@lem5395899)). Qed.
Lemma lem5395902 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5395903 : term202 = term171.
Proof. exact (MK_COMB (@lem5395902) (@lem5395901)). Qed.
Lemma lem5395904 : term197 = term171.
Proof. exact (TRANS (@lem5395897) (@lem5395903)). Qed.
Lemma lem5395905 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395906 : term407 = term399.
Proof. exact (MK_COMB (@lem5395905) (@lem5395904)). Qed.
Lemma lem5395907 : term408 = term401.
Proof. exact (MK_COMB (@lem5395906) (@lem5395894)). Qed.
Lemma lem5395909 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5395910 : term401 = term118.
Proof. exact (@lem5395909 term7). Qed.
Lemma lem5395911 : term408 = term118.
Proof. exact (TRANS (@lem5395907) (@lem5395910)). Qed.
Lemma lem5395912 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395913 : term410 = term228.
Proof. exact (MK_COMB (@lem5395912) (@lem5395911)). Qed.
Lemma lem5395914 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5395915 : term411 = term230.
Proof. exact (MK_COMB (@lem5395913) (@lem5395914)). Qed.
Lemma lem5395917 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395918 : term230 = term118.
Proof. exact (@lem5395917 term7). Qed.
Lemma lem5395919 : term411 = term118.
Proof. exact (TRANS (@lem5395915) (@lem5395918)). Qed.
Lemma lem5395921 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5395922 : term180 = term181.
Proof. exact (@lem5395921 term7 term7). Qed.
Lemma lem5395923 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395924 : term183 = term7.
Proof. exact (EQ_MP (@lem5395923) (@lem940073)). Qed.
Lemma lem5395925 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5395926 : term181 = term127.
Proof. exact (MK_COMB (@lem5395925) (@lem5395924)). Qed.
Lemma lem5395927 : term180 = term127.
Proof. exact (TRANS (@lem5395922) (@lem5395926)). Qed.
Lemma lem5395928 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5395929 : term232 = term230.
Proof. exact (MK_COMB (@lem5395928) (@lem5395927)). Qed.
Lemma lem5395931 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5395932 : term230 = term118.
Proof. exact (@lem5395931 term7). Qed.
Lemma lem5395933 : term232 = term118.
Proof. exact (TRANS (@lem5395929) (@lem5395932)). Qed.
Lemma lem5395934 : term118 = term232.
Proof. exact (SYM (@lem5395933)). Qed.
Lemma lem5395935 : term411 = term232.
Proof. exact (TRANS (@lem5395919) (@lem5395934)). Qed.
Lemma lem5395936 : term402 = term168.
Proof. exact (@lem5395886 (@lem5395935)). Qed.
Lemma lem5395937 : term401 = term168.
Proof. exact (TRANS (@lem5395852) (@lem5395936)). Qed.
Lemma lem5395939 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5395940 : term168 = term118.
Proof. exact (@lem5395939 term118). Qed.
Lemma lem5395941 : term401 = term118.
Proof. exact (TRANS (@lem5395937) (@lem5395940)). Qed.
Lemma lem5395942 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5395943 : term412 = term228.
Proof. exact (MK_COMB (@lem5395942) (@lem5395941)). Qed.
Lemma lem5395944 (_69874 : int) : (real_of_int _69874) = (real_of_int _69874).
Proof. exact (eq_refl (real_of_int _69874)). Qed.
Lemma lem5395945 (_69874 : int) : (term398 _69874) = (term413 _69874).
Proof. exact (MK_COMB (@lem5395943) (@lem5395944 _69874)). Qed.
Lemma lem5395946 (_69874 : int) : (term418 _69874) = (term413 _69874).
Proof. exact (TRANS (@lem5395843 _69874) (@lem5395945 _69874)). Qed.
Lemma lem5395947 (_69874 : int) : (term413 _69874) = term118.
Proof. exact (@lem1982719 (real_of_int _69874)). Qed.
Lemma lem5395948 (_69874 : int) : (term418 _69874) = term118.
Proof. exact (TRANS (@lem5395946 _69874) (@lem5395947 _69874)). Qed.
Lemma lem5395949 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395950 (_69874 : int) : (term419 _69874) = term415.
Proof. exact (MK_COMB (@lem5395949) (@lem5395948 _69874)). Qed.
Lemma lem5395952 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395953 : term171 = term172.
Proof. exact (@lem5395952 term7). Qed.
Lemma lem5395955 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5395956 : term171 = term172.
Proof. exact (@lem5395955 term7). Qed.
Lemma lem5395957 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5395958 : term399 = term400.
Proof. exact (MK_COMB (@lem5395957) (@lem5395956)). Qed.
Lemma lem5395959 : term465 = term466.
Proof. exact (MK_COMB (@lem5395958) (@lem5395953)). Qed.
Lemma lem5395960 : term467.
Proof. exact (@lem1981473 term171 term127 term171 term127 term274 term127). Qed.
Lemma lem5395962 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395963 : term218 = term219.
Proof. exact (@lem5395962 (NUMERAL 0) term7). Qed.
Lemma lem5395964 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395965 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395966 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395965 h1) (fun h1 : term219 = True => @lem5395964)). Qed.
Lemma lem5395967 : term219 = True.
Proof. exact (EQ_MP (@lem5395966) (@lem5395964)). Qed.
Lemma lem5395968 : term218 = True.
Proof. exact (TRANS (@lem5395963) (@lem5395967)). Qed.
Lemma lem5395969 : True = term218.
Proof. exact (SYM (@lem5395968)). Qed.
Lemma lem5395970 : term218.
Proof. exact (EQ_MP (@lem5395969) (@lem0)). Qed.
Lemma lem5395971 : term468.
Proof. exact (@lem5395960 (@lem5395970)). Qed.
Lemma lem5395973 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395974 : term218 = term219.
Proof. exact (@lem5395973 (NUMERAL 0) term7). Qed.
Lemma lem5395975 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395976 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395977 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395976 h1) (fun h1 : term219 = True => @lem5395975)). Qed.
Lemma lem5395978 : term219 = True.
Proof. exact (EQ_MP (@lem5395977) (@lem5395975)). Qed.
Lemma lem5395979 : term218 = True.
Proof. exact (TRANS (@lem5395974) (@lem5395978)). Qed.
Lemma lem5395980 : True = term218.
Proof. exact (SYM (@lem5395979)). Qed.
Lemma lem5395981 : term218.
Proof. exact (EQ_MP (@lem5395980) (@lem0)). Qed.
Lemma lem5395982 : term469.
Proof. exact (@lem5395971 (@lem5395981)). Qed.
Lemma lem5395984 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5395985 : term218 = term219.
Proof. exact (@lem5395984 (NUMERAL 0) term7). Qed.
Lemma lem5395986 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5395987 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5395988 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5395987 h1) (fun h1 : term219 = True => @lem5395986)). Qed.
Lemma lem5395989 : term219 = True.
Proof. exact (EQ_MP (@lem5395988) (@lem5395986)). Qed.
Lemma lem5395990 : term218 = True.
Proof. exact (TRANS (@lem5395985) (@lem5395989)). Qed.
Lemma lem5395991 : True = term218.
Proof. exact (SYM (@lem5395990)). Qed.
Lemma lem5395992 : term218.
Proof. exact (EQ_MP (@lem5395991) (@lem0)). Qed.
Lemma lem5395993 : term470.
Proof. exact (@lem5395982 (@lem5395992)). Qed.
Lemma lem5395995 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5395996 : term197 = term202.
Proof. exact (@lem5395995 term7 term7). Qed.
Lemma lem5395997 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5395998 : term183 = term7.
Proof. exact (EQ_MP (@lem5395997) (@lem940073)). Qed.
Lemma lem5395999 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396000 : term181 = term127.
Proof. exact (MK_COMB (@lem5395999) (@lem5395998)). Qed.
Lemma lem5396001 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396002 : term202 = term171.
Proof. exact (MK_COMB (@lem5396001) (@lem5396000)). Qed.
Lemma lem5396003 : term197 = term171.
Proof. exact (TRANS (@lem5395996) (@lem5396002)). Qed.
Lemma lem5396005 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396006 : term197 = term202.
Proof. exact (@lem5396005 term7 term7). Qed.
Lemma lem5396007 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396008 : term183 = term7.
Proof. exact (EQ_MP (@lem5396007) (@lem940073)). Qed.
Lemma lem5396009 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396010 : term181 = term127.
Proof. exact (MK_COMB (@lem5396009) (@lem5396008)). Qed.
Lemma lem5396011 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396012 : term202 = term171.
Proof. exact (MK_COMB (@lem5396011) (@lem5396010)). Qed.
Lemma lem5396013 : term197 = term171.
Proof. exact (TRANS (@lem5396006) (@lem5396012)). Qed.
Lemma lem5396014 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396015 : term407 = term399.
Proof. exact (MK_COMB (@lem5396014) (@lem5396013)). Qed.
Lemma lem5396016 : term471 = term465.
Proof. exact (MK_COMB (@lem5396015) (@lem5396003)). Qed.
Lemma lem5396017 : term465 = term291.
Proof. exact (@lem1367763 term7 term7). Qed.
Lemma lem5396018 : term247 = term248.
Proof. exact (@lem706885). Qed.
Lemma lem5396019 : (term247 = term248) = (term249 = term250).
Proof. exact (@lem1006570 (BIT1 0) (BIT1 0) term248). Qed.
Lemma lem5396020 : term249 = term250.
Proof. exact (EQ_MP (@lem5396019) (@lem5396018)). Qed.
Lemma lem5396021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396022 : term246 = term241.
Proof. exact (MK_COMB (@lem5396021) (@lem5396020)). Qed.
Lemma lem5396023 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396024 : term291 = term274.
Proof. exact (MK_COMB (@lem5396023) (@lem5396022)). Qed.
Lemma lem5396025 : term465 = term274.
Proof. exact (TRANS (@lem5396017) (@lem5396024)). Qed.
Lemma lem5396026 : term471 = term274.
Proof. exact (TRANS (@lem5396016) (@lem5396025)). Qed.
Lemma lem5396027 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5396028 : term472 = term473.
Proof. exact (MK_COMB (@lem5396027) (@lem5396026)). Qed.
Lemma lem5396029 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5396030 : term474 = term287.
Proof. exact (MK_COMB (@lem5396028) (@lem5396029)). Qed.
Lemma lem5396032 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396033 : term287 = term288.
Proof. exact (@lem5396032 term250 term7). Qed.
Lemma lem5396034 : term256 = term248.
Proof. exact (@lem996237 term248). Qed.
Lemma lem5396035 : (term256 = term248) = (term257 = term250).
Proof. exact (@lem1007663 term248 (BIT1 0) term248). Qed.
Lemma lem5396036 : term257 = term250.
Proof. exact (EQ_MP (@lem5396035) (@lem5396034)). Qed.
Lemma lem5396037 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396038 : term255 = term241.
Proof. exact (MK_COMB (@lem5396037) (@lem5396036)). Qed.
Lemma lem5396039 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396040 : term288 = term274.
Proof. exact (MK_COMB (@lem5396039) (@lem5396038)). Qed.
Lemma lem5396041 : term287 = term274.
Proof. exact (TRANS (@lem5396033) (@lem5396040)). Qed.
Lemma lem5396042 : term474 = term274.
Proof. exact (TRANS (@lem5396030) (@lem5396041)). Qed.
Lemma lem5396044 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396045 : term180 = term181.
Proof. exact (@lem5396044 term7 term7). Qed.
Lemma lem5396046 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396047 : term183 = term7.
Proof. exact (EQ_MP (@lem5396046) (@lem940073)). Qed.
Lemma lem5396048 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396049 : term181 = term127.
Proof. exact (MK_COMB (@lem5396048) (@lem5396047)). Qed.
Lemma lem5396050 : term180 = term127.
Proof. exact (TRANS (@lem5396045) (@lem5396049)). Qed.
Lemma lem5396051 : term473 = term473.
Proof. exact (eq_refl term473). Qed.
Lemma lem5396052 : term475 = term287.
Proof. exact (MK_COMB (@lem5396051) (@lem5396050)). Qed.
Lemma lem5396054 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396055 : term287 = term288.
Proof. exact (@lem5396054 term250 term7). Qed.
Lemma lem5396056 : term256 = term248.
Proof. exact (@lem996237 term248). Qed.
Lemma lem5396057 : (term256 = term248) = (term257 = term250).
Proof. exact (@lem1007663 term248 (BIT1 0) term248). Qed.
Lemma lem5396058 : term257 = term250.
Proof. exact (EQ_MP (@lem5396057) (@lem5396056)). Qed.
Lemma lem5396059 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396060 : term255 = term241.
Proof. exact (MK_COMB (@lem5396059) (@lem5396058)). Qed.
Lemma lem5396061 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396062 : term288 = term274.
Proof. exact (MK_COMB (@lem5396061) (@lem5396060)). Qed.
Lemma lem5396063 : term287 = term274.
Proof. exact (TRANS (@lem5396055) (@lem5396062)). Qed.
Lemma lem5396064 : term475 = term274.
Proof. exact (TRANS (@lem5396052) (@lem5396063)). Qed.
Lemma lem5396065 : term274 = term475.
Proof. exact (SYM (@lem5396064)). Qed.
Lemma lem5396066 : term474 = term475.
Proof. exact (TRANS (@lem5396042) (@lem5396065)). Qed.
Lemma lem5396067 : term466 = term277.
Proof. exact (@lem5395993 (@lem5396066)). Qed.
Lemma lem5396068 : term465 = term277.
Proof. exact (TRANS (@lem5395959) (@lem5396067)). Qed.
Lemma lem5396070 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5396071 : term277 = term274.
Proof. exact (@lem5396070 term274). Qed.
Lemma lem5396072 : term465 = term274.
Proof. exact (TRANS (@lem5396068) (@lem5396071)). Qed.
Lemma lem5396073 (_69874 : int) : (term464 _69874) = term476.
Proof. exact (MK_COMB (@lem5395950 _69874) (@lem5396072)). Qed.
Lemma lem5396074 (_69874 : int) : (term463 _69874) = term476.
Proof. exact (TRANS (@lem5395842 _69874) (@lem5396073 _69874)). Qed.
Lemma lem5396075 : term476 = term274.
Proof. exact (@lem1982721 term274). Qed.
Lemma lem5396076 (_69874 : int) : (term463 _69874) = term274.
Proof. exact (TRANS (@lem5396074 _69874) (@lem5396075)). Qed.
Lemma lem5396077 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5396078 (_69874 : int) : (term477 _69874) = term478.
Proof. exact (MK_COMB (@lem5396077) (@lem5396076 _69874)). Qed.
Lemma lem5396079 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396080 (_69874 : int) : (term462 _69874) = term479.
Proof. exact (MK_COMB (@lem5396078 _69874) (@lem5396079)). Qed.
Lemma lem5396081 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : term479.
Proof. exact (EQ_MP (@lem5396080 _69874) (@lem5395841 _69873 _69874 h1)). Qed.
Lemma lem5396083 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5396084 : term479 = term480.
Proof. exact (@lem5396083 term118 term274). Qed.
Lemma lem5396086 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5396087 : term274 = term277.
Proof. exact (@lem5396086 term250). Qed.
Lemma lem5396089 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396090 : term118 = term168.
Proof. exact (@lem5396089 (NUMERAL 0)). Qed.
Lemma lem5396091 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5396092 : term120 = term425.
Proof. exact (MK_COMB (@lem5396091) (@lem5396090)). Qed.
Lemma lem5396093 : term480 = term481.
Proof. exact (MK_COMB (@lem5396092) (@lem5396087)). Qed.
Lemma lem5396094 : term482.
Proof. exact (@lem1980026 term118 term127 term274 term127). Qed.
Lemma lem5396096 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396097 : term218 = term219.
Proof. exact (@lem5396096 (NUMERAL 0) term7). Qed.
Lemma lem5396098 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396099 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396100 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396099 h1) (fun h1 : term219 = True => @lem5396098)). Qed.
Lemma lem5396101 : term219 = True.
Proof. exact (EQ_MP (@lem5396100) (@lem5396098)). Qed.
Lemma lem5396102 : term218 = True.
Proof. exact (TRANS (@lem5396097) (@lem5396101)). Qed.
Lemma lem5396103 : True = term218.
Proof. exact (SYM (@lem5396102)). Qed.
Lemma lem5396104 : term218.
Proof. exact (EQ_MP (@lem5396103) (@lem0)). Qed.
Lemma lem5396105 : term483.
Proof. exact (@lem5396094 (@lem5396104)). Qed.
Lemma lem5396107 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396108 : term218 = term219.
Proof. exact (@lem5396107 (NUMERAL 0) term7). Qed.
Lemma lem5396109 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396110 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396111 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396110 h1) (fun h1 : term219 = True => @lem5396109)). Qed.
Lemma lem5396112 : term219 = True.
Proof. exact (EQ_MP (@lem5396111) (@lem5396109)). Qed.
Lemma lem5396113 : term218 = True.
Proof. exact (TRANS (@lem5396108) (@lem5396112)). Qed.
Lemma lem5396114 : True = term218.
Proof. exact (SYM (@lem5396113)). Qed.
Lemma lem5396115 : term218.
Proof. exact (EQ_MP (@lem5396114) (@lem0)). Qed.
Lemma lem5396116 : term481 = term484.
Proof. exact (@lem5396105 (@lem5396115)). Qed.
Lemma lem5396118 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396119 : term287 = term288.
Proof. exact (@lem5396118 term250 term7). Qed.
Lemma lem5396120 : term256 = term248.
Proof. exact (@lem996237 term248). Qed.
Lemma lem5396121 : (term256 = term248) = (term257 = term250).
Proof. exact (@lem1007663 term248 (BIT1 0) term248). Qed.
Lemma lem5396122 : term257 = term250.
Proof. exact (EQ_MP (@lem5396121) (@lem5396120)). Qed.
Lemma lem5396123 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396124 : term255 = term241.
Proof. exact (MK_COMB (@lem5396123) (@lem5396122)). Qed.
Lemma lem5396125 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396126 : term288 = term274.
Proof. exact (MK_COMB (@lem5396125) (@lem5396124)). Qed.
Lemma lem5396127 : term287 = term274.
Proof. exact (TRANS (@lem5396119) (@lem5396126)). Qed.
Lemma lem5396129 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396130 : term230 = term118.
Proof. exact (@lem5396129 term7). Qed.
Lemma lem5396131 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5396132 : term430 = term120.
Proof. exact (MK_COMB (@lem5396131) (@lem5396130)). Qed.
Lemma lem5396133 : term484 = term480.
Proof. exact (MK_COMB (@lem5396132) (@lem5396127)). Qed.
Lemma lem5396135 (m : nat) (n : nat) : (term431 m n) = (term432 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5396136 : term480 = term485.
Proof. exact (@lem5396135 (NUMERAL 0) term250). Qed.
Lemma lem5396137 : term486 = term248.
Proof. exact (@lem912803). Qed.
Lemma lem5396138 (h1 : term486 = term248) : (term250 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 (BIT1 0) 0 term248 h1). Qed.
Lemma lem5396139 : (term486 = term248) = ((term250 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term486 = term248 => @lem5396138 h1) (fun h1 : (term250 = (NUMERAL 0)) = False => @lem5396137)). Qed.
Lemma lem5396140 : (term250 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5396139) (@lem5396137)). Qed.
Lemma lem5396141 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5396142 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5396143 : term434 = (and True).
Proof. exact (MK_COMB (@lem5396142) (@lem5396141)). Qed.
Lemma lem5396144 : term485 = (True /\ False).
Proof. exact (MK_COMB (@lem5396143) (@lem5396140)). Qed.
Lemma lem5396146 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5396147 : term485 = False.
Proof. exact (TRANS (@lem5396144) (@lem5396146)). Qed.
Lemma lem5396148 : term480 = False.
Proof. exact (TRANS (@lem5396136) (@lem5396147)). Qed.
Lemma lem5396149 : term484 = False.
Proof. exact (TRANS (@lem5396133) (@lem5396148)). Qed.
Lemma lem5396150 : term481 = False.
Proof. exact (TRANS (@lem5396116) (@lem5396149)). Qed.
Lemma lem5396151 : term480 = False.
Proof. exact (TRANS (@lem5396093) (@lem5396150)). Qed.
Lemma lem5396152 : term479 = False.
Proof. exact (TRANS (@lem5396084) (@lem5396151)). Qed.
Lemma lem5396153 (_69873 : int) (_69874 : int) (h1 : term435 _69873 _69874) : False.
Proof. exact (EQ_MP (@lem5396152) (@lem5396081 _69873 _69874 h1)). Qed.
Lemma lem5396154 (_69873 : int) (_69874 : int) (h1 : term348 _69873 _69874) : False.
Proof. exact (or_elim (@lem5395018 _69873 _69874 h1) (fun h0 : term354 _69873 _69874 => @lem5395468 _69873 _69874 h0) (fun h0 : term435 _69873 _69874 => @lem5396153 _69873 _69874 h0)). Qed.
Lemma lem5396155 (_69873 : int) (_69874 : int) (h1 : term344 _69873 _69874) : term344 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5396156 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term487 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5396157 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term345 _69873 _69874.
Proof. exact (proj2 (@lem5396156 _69873 _69874 h1)). Qed.
Lemma lem5396159 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term332 _69873 _69874.
Proof. exact (proj2 (@lem5396157 _69873 _69874 h1)). Qed.
Lemma lem5396161 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term312 _69873 _69874.
Proof. exact (proj2 (@lem5396159 _69873 _69874 h1)). Qed.
Lemma lem5396162 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : (term233 _69873 _69874) = term118.
Proof. exact (proj1 (@lem5396159 _69873 _69874 h1)). Qed.
Lemma lem5396164 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5396165 : term355 = term218.
Proof. exact (@lem5396164 term118 term127). Qed.
Lemma lem5396167 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396168 : term127 = term196.
Proof. exact (@lem5396167 term7). Qed.
Lemma lem5396170 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396171 : term118 = term168.
Proof. exact (@lem5396170 (NUMERAL 0)). Qed.
Lemma lem5396172 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396173 : term356 = term357.
Proof. exact (MK_COMB (@lem5396172) (@lem5396171)). Qed.
Lemma lem5396174 : term218 = term358.
Proof. exact (MK_COMB (@lem5396173) (@lem5396168)). Qed.
Lemma lem5396175 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5396177 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396178 : term218 = term219.
Proof. exact (@lem5396177 (NUMERAL 0) term7). Qed.
Lemma lem5396179 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396180 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396181 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396180 h1) (fun h1 : term219 = True => @lem5396179)). Qed.
Lemma lem5396182 : term219 = True.
Proof. exact (EQ_MP (@lem5396181) (@lem5396179)). Qed.
Lemma lem5396183 : term218 = True.
Proof. exact (TRANS (@lem5396178) (@lem5396182)). Qed.
Lemma lem5396184 : True = term218.
Proof. exact (SYM (@lem5396183)). Qed.
Lemma lem5396185 : term218.
Proof. exact (EQ_MP (@lem5396184) (@lem0)). Qed.
Lemma lem5396186 : term360.
Proof. exact (@lem5396175 (@lem5396185)). Qed.
Lemma lem5396188 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396189 : term218 = term219.
Proof. exact (@lem5396188 (NUMERAL 0) term7). Qed.
Lemma lem5396190 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396191 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396192 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396191 h1) (fun h1 : term219 = True => @lem5396190)). Qed.
Lemma lem5396193 : term219 = True.
Proof. exact (EQ_MP (@lem5396192) (@lem5396190)). Qed.
Lemma lem5396194 : term218 = True.
Proof. exact (TRANS (@lem5396189) (@lem5396193)). Qed.
Lemma lem5396195 : True = term218.
Proof. exact (SYM (@lem5396194)). Qed.
Lemma lem5396196 : term218.
Proof. exact (EQ_MP (@lem5396195) (@lem0)). Qed.
Lemma lem5396197 : term358 = term361.
Proof. exact (@lem5396186 (@lem5396196)). Qed.
Lemma lem5396199 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396200 : term180 = term181.
Proof. exact (@lem5396199 term7 term7). Qed.
Lemma lem5396201 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396202 : term183 = term7.
Proof. exact (EQ_MP (@lem5396201) (@lem940073)). Qed.
Lemma lem5396203 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396204 : term181 = term127.
Proof. exact (MK_COMB (@lem5396203) (@lem5396202)). Qed.
Lemma lem5396205 : term180 = term127.
Proof. exact (TRANS (@lem5396200) (@lem5396204)). Qed.
Lemma lem5396207 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396208 : term230 = term118.
Proof. exact (@lem5396207 term7). Qed.
Lemma lem5396209 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396210 : term362 = term356.
Proof. exact (MK_COMB (@lem5396209) (@lem5396208)). Qed.
Lemma lem5396211 : term361 = term218.
Proof. exact (MK_COMB (@lem5396210) (@lem5396205)). Qed.
Lemma lem5396213 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396214 : term218 = term219.
Proof. exact (@lem5396213 (NUMERAL 0) term7). Qed.
Lemma lem5396215 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396216 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396217 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396216 h1) (fun h1 : term219 = True => @lem5396215)). Qed.
Lemma lem5396218 : term219 = True.
Proof. exact (EQ_MP (@lem5396217) (@lem5396215)). Qed.
Lemma lem5396219 : term218 = True.
Proof. exact (TRANS (@lem5396214) (@lem5396218)). Qed.
Lemma lem5396220 : term361 = True.
Proof. exact (TRANS (@lem5396211) (@lem5396219)). Qed.
Lemma lem5396221 : term358 = True.
Proof. exact (TRANS (@lem5396197) (@lem5396220)). Qed.
Lemma lem5396222 : term218 = True.
Proof. exact (TRANS (@lem5396174) (@lem5396221)). Qed.
Lemma lem5396223 : term355 = True.
Proof. exact (TRANS (@lem5396165) (@lem5396222)). Qed.
Lemma lem5396224 : True = term355.
Proof. exact (SYM (@lem5396223)). Qed.
Lemma lem5396225 : term355.
Proof. exact (EQ_MP (@lem5396224) (@lem0)). Qed.
Lemma lem5396226 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term488 _69873 _69874.
Proof. exact (conj (@lem5396225) (@lem5396161 _69873 _69874 h1)). Qed.
Lemma lem5396228 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5396229 (_69873 : int) (_69874 : int) : term489 _69873 _69874.
Proof. exact (@lem5396228 term127 (term306 _69873 _69874)). Qed.
Lemma lem5396230 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term490 _69873 _69874.
Proof. exact (@lem5396229 _69873 _69874 (@lem5396226 _69873 _69874 h1)). Qed.
Lemma lem5396231 (_69873 : int) (_69874 : int) : (term491 _69873 _69874) = (term306 _69873 _69874).
Proof. exact (@lem1982733 (term306 _69873 _69874)). Qed.
Lemma lem5396232 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5396233 (_69873 : int) (_69874 : int) : (term492 _69873 _69874) = (term311 _69873 _69874).
Proof. exact (MK_COMB (@lem5396232) (@lem5396231 _69873 _69874)). Qed.
Lemma lem5396234 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396235 (_69873 : int) (_69874 : int) : (term490 _69873 _69874) = (term312 _69873 _69874).
Proof. exact (MK_COMB (@lem5396233 _69873 _69874) (@lem5396234)). Qed.
Lemma lem5396236 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term312 _69873 _69874.
Proof. exact (EQ_MP (@lem5396235 _69873 _69874) (@lem5396230 _69873 _69874 h1)). Qed.
Lemma lem5396238 (y : real) : term369 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5396239 (_69873 : int) (_69874 : int) : term370 _69873 _69874.
Proof. exact (@lem5396238 (term233 _69873 _69874)). Qed.
Lemma lem5396240 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term371 _69873 _69874.
Proof. exact (@lem5396239 _69873 _69874 (@lem5396162 _69873 _69874 h1)). Qed.
Lemma lem5396241 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term493 _69873 _69874.
Proof. exact (@lem5396240 _69873 _69874 h1 term127). Qed.
Lemma lem5396242 (_69873 : int) (_69874 : int) : (term493 _69873 _69874) = ((term494 _69873 _69874) = term118).
Proof. exact (eq_refl (term493 _69873 _69874)). Qed.
Lemma lem5396243 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : (term494 _69873 _69874) = term118.
Proof. exact (EQ_MP (@lem5396242 _69873 _69874) (@lem5396241 _69873 _69874 h1)). Qed.
Lemma lem5396244 (_69873 : int) (_69874 : int) : (term494 _69873 _69874) = (term233 _69873 _69874).
Proof. exact (@lem1982733 (term233 _69873 _69874)). Qed.
Lemma lem5396245 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5396246 (_69873 : int) (_69874 : int) : (term495 _69873 _69874) = (term235 _69873 _69874).
Proof. exact (MK_COMB (@lem5396245) (@lem5396244 _69873 _69874)). Qed.
Lemma lem5396247 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396248 (_69873 : int) (_69874 : int) : ((term494 _69873 _69874) = term118) = ((term233 _69873 _69874) = term118).
Proof. exact (MK_COMB (@lem5396246 _69873 _69874) (@lem5396247)). Qed.
Lemma lem5396249 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : (term233 _69873 _69874) = term118.
Proof. exact (EQ_MP (@lem5396248 _69873 _69874) (@lem5396243 _69873 _69874 h1)). Qed.
Lemma lem5396250 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term332 _69873 _69874.
Proof. exact (conj (@lem5396249 _69873 _69874 h1) (@lem5396236 _69873 _69874 h1)). Qed.
Lemma lem5396252 (x : real) (y : real) : term391 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5396253 (_69873 : int) (_69874 : int) : term496 _69873 _69874.
Proof. exact (@lem5396252 (term233 _69873 _69874) (term306 _69873 _69874)). Qed.
Lemma lem5396254 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term497 _69873 _69874.
Proof. exact (@lem5396253 _69873 _69874 (@lem5396250 _69873 _69874 h1)). Qed.
Lemma lem5396255 (_69873 : int) (_69874 : int) : (term498 _69873 _69874) = (term499 _69873 _69874).
Proof. exact (@lem1982753 (term209 _69873) (real_of_int _69873) (real_of_int _69874) (term206 _69874)). Qed.
Lemma lem5396256 (_69873 : int) : (term418 _69873) = (term398 _69873).
Proof. exact (@lem1982713 term171 (real_of_int _69873)). Qed.
Lemma lem5396258 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396259 : term127 = term196.
Proof. exact (@lem5396258 term7). Qed.
Lemma lem5396261 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5396262 : term171 = term172.
Proof. exact (@lem5396261 term7). Qed.
Lemma lem5396263 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396264 : term399 = term400.
Proof. exact (MK_COMB (@lem5396263) (@lem5396262)). Qed.
Lemma lem5396265 : term401 = term402.
Proof. exact (MK_COMB (@lem5396264) (@lem5396259)). Qed.
Lemma lem5396266 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5396268 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396269 : term218 = term219.
Proof. exact (@lem5396268 (NUMERAL 0) term7). Qed.
Lemma lem5396270 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396271 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396272 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396271 h1) (fun h1 : term219 = True => @lem5396270)). Qed.
Lemma lem5396273 : term219 = True.
Proof. exact (EQ_MP (@lem5396272) (@lem5396270)). Qed.
Lemma lem5396274 : term218 = True.
Proof. exact (TRANS (@lem5396269) (@lem5396273)). Qed.
Lemma lem5396275 : True = term218.
Proof. exact (SYM (@lem5396274)). Qed.
Lemma lem5396276 : term218.
Proof. exact (EQ_MP (@lem5396275) (@lem0)). Qed.
Lemma lem5396277 : term404.
Proof. exact (@lem5396266 (@lem5396276)). Qed.
Lemma lem5396279 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396280 : term218 = term219.
Proof. exact (@lem5396279 (NUMERAL 0) term7). Qed.
Lemma lem5396281 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396282 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396283 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396282 h1) (fun h1 : term219 = True => @lem5396281)). Qed.
Lemma lem5396284 : term219 = True.
Proof. exact (EQ_MP (@lem5396283) (@lem5396281)). Qed.
Lemma lem5396285 : term218 = True.
Proof. exact (TRANS (@lem5396280) (@lem5396284)). Qed.
Lemma lem5396286 : True = term218.
Proof. exact (SYM (@lem5396285)). Qed.
Lemma lem5396287 : term218.
Proof. exact (EQ_MP (@lem5396286) (@lem0)). Qed.
Lemma lem5396288 : term405.
Proof. exact (@lem5396277 (@lem5396287)). Qed.
Lemma lem5396290 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396291 : term218 = term219.
Proof. exact (@lem5396290 (NUMERAL 0) term7). Qed.
Lemma lem5396292 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396293 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396294 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396293 h1) (fun h1 : term219 = True => @lem5396292)). Qed.
Lemma lem5396295 : term219 = True.
Proof. exact (EQ_MP (@lem5396294) (@lem5396292)). Qed.
Lemma lem5396296 : term218 = True.
Proof. exact (TRANS (@lem5396291) (@lem5396295)). Qed.
Lemma lem5396297 : True = term218.
Proof. exact (SYM (@lem5396296)). Qed.
Lemma lem5396298 : term218.
Proof. exact (EQ_MP (@lem5396297) (@lem0)). Qed.
Lemma lem5396299 : term406.
Proof. exact (@lem5396288 (@lem5396298)). Qed.
Lemma lem5396301 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396302 : term180 = term181.
Proof. exact (@lem5396301 term7 term7). Qed.
Lemma lem5396303 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396304 : term183 = term7.
Proof. exact (EQ_MP (@lem5396303) (@lem940073)). Qed.
Lemma lem5396305 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396306 : term181 = term127.
Proof. exact (MK_COMB (@lem5396305) (@lem5396304)). Qed.
Lemma lem5396307 : term180 = term127.
Proof. exact (TRANS (@lem5396302) (@lem5396306)). Qed.
Lemma lem5396309 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396310 : term197 = term202.
Proof. exact (@lem5396309 term7 term7). Qed.
Lemma lem5396311 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396312 : term183 = term7.
Proof. exact (EQ_MP (@lem5396311) (@lem940073)). Qed.
Lemma lem5396313 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396314 : term181 = term127.
Proof. exact (MK_COMB (@lem5396313) (@lem5396312)). Qed.
Lemma lem5396315 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396316 : term202 = term171.
Proof. exact (MK_COMB (@lem5396315) (@lem5396314)). Qed.
Lemma lem5396317 : term197 = term171.
Proof. exact (TRANS (@lem5396310) (@lem5396316)). Qed.
Lemma lem5396318 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396319 : term407 = term399.
Proof. exact (MK_COMB (@lem5396318) (@lem5396317)). Qed.
Lemma lem5396320 : term408 = term401.
Proof. exact (MK_COMB (@lem5396319) (@lem5396307)). Qed.
Lemma lem5396322 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5396323 : term401 = term118.
Proof. exact (@lem5396322 term7). Qed.
Lemma lem5396324 : term408 = term118.
Proof. exact (TRANS (@lem5396320) (@lem5396323)). Qed.
Lemma lem5396325 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5396326 : term410 = term228.
Proof. exact (MK_COMB (@lem5396325) (@lem5396324)). Qed.
Lemma lem5396327 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5396328 : term411 = term230.
Proof. exact (MK_COMB (@lem5396326) (@lem5396327)). Qed.
Lemma lem5396330 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396331 : term230 = term118.
Proof. exact (@lem5396330 term7). Qed.
Lemma lem5396332 : term411 = term118.
Proof. exact (TRANS (@lem5396328) (@lem5396331)). Qed.
Lemma lem5396334 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396335 : term180 = term181.
Proof. exact (@lem5396334 term7 term7). Qed.
Lemma lem5396336 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396337 : term183 = term7.
Proof. exact (EQ_MP (@lem5396336) (@lem940073)). Qed.
Lemma lem5396338 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396339 : term181 = term127.
Proof. exact (MK_COMB (@lem5396338) (@lem5396337)). Qed.
Lemma lem5396340 : term180 = term127.
Proof. exact (TRANS (@lem5396335) (@lem5396339)). Qed.
Lemma lem5396341 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5396342 : term232 = term230.
Proof. exact (MK_COMB (@lem5396341) (@lem5396340)). Qed.
Lemma lem5396344 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396345 : term230 = term118.
Proof. exact (@lem5396344 term7). Qed.
Lemma lem5396346 : term232 = term118.
Proof. exact (TRANS (@lem5396342) (@lem5396345)). Qed.
Lemma lem5396347 : term118 = term232.
Proof. exact (SYM (@lem5396346)). Qed.
Lemma lem5396348 : term411 = term232.
Proof. exact (TRANS (@lem5396332) (@lem5396347)). Qed.
Lemma lem5396349 : term402 = term168.
Proof. exact (@lem5396299 (@lem5396348)). Qed.
Lemma lem5396350 : term401 = term168.
Proof. exact (TRANS (@lem5396265) (@lem5396349)). Qed.
Lemma lem5396352 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5396353 : term168 = term118.
Proof. exact (@lem5396352 term118). Qed.
Lemma lem5396354 : term401 = term118.
Proof. exact (TRANS (@lem5396350) (@lem5396353)). Qed.
Lemma lem5396355 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5396356 : term412 = term228.
Proof. exact (MK_COMB (@lem5396355) (@lem5396354)). Qed.
Lemma lem5396357 (_69873 : int) : (real_of_int _69873) = (real_of_int _69873).
Proof. exact (eq_refl (real_of_int _69873)). Qed.
Lemma lem5396358 (_69873 : int) : (term398 _69873) = (term413 _69873).
Proof. exact (MK_COMB (@lem5396356) (@lem5396357 _69873)). Qed.
Lemma lem5396359 (_69873 : int) : (term418 _69873) = (term413 _69873).
Proof. exact (TRANS (@lem5396256 _69873) (@lem5396358 _69873)). Qed.
Lemma lem5396360 (_69873 : int) : (term413 _69873) = term118.
Proof. exact (@lem1982719 (real_of_int _69873)). Qed.
Lemma lem5396361 (_69873 : int) : (term418 _69873) = term118.
Proof. exact (TRANS (@lem5396359 _69873) (@lem5396360 _69873)). Qed.
Lemma lem5396362 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396363 (_69873 : int) : (term419 _69873) = term415.
Proof. exact (MK_COMB (@lem5396362) (@lem5396361 _69873)). Qed.
Lemma lem5396364 (_69874 : int) : (term500 _69874) = (term501 _69874).
Proof. exact (@lem1982763 (real_of_int _69874) (term209 _69874) term171). Qed.
Lemma lem5396365 (_69874 : int) : (term397 _69874) = (term398 _69874).
Proof. exact (@lem1982715 term171 (real_of_int _69874)). Qed.
Lemma lem5396367 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396368 : term127 = term196.
Proof. exact (@lem5396367 term7). Qed.
Lemma lem5396370 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5396371 : term171 = term172.
Proof. exact (@lem5396370 term7). Qed.
Lemma lem5396372 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396373 : term399 = term400.
Proof. exact (MK_COMB (@lem5396372) (@lem5396371)). Qed.
Lemma lem5396374 : term401 = term402.
Proof. exact (MK_COMB (@lem5396373) (@lem5396368)). Qed.
Lemma lem5396375 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5396377 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396378 : term218 = term219.
Proof. exact (@lem5396377 (NUMERAL 0) term7). Qed.
Lemma lem5396379 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396380 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396381 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396380 h1) (fun h1 : term219 = True => @lem5396379)). Qed.
Lemma lem5396382 : term219 = True.
Proof. exact (EQ_MP (@lem5396381) (@lem5396379)). Qed.
Lemma lem5396383 : term218 = True.
Proof. exact (TRANS (@lem5396378) (@lem5396382)). Qed.
Lemma lem5396384 : True = term218.
Proof. exact (SYM (@lem5396383)). Qed.
Lemma lem5396385 : term218.
Proof. exact (EQ_MP (@lem5396384) (@lem0)). Qed.
Lemma lem5396386 : term404.
Proof. exact (@lem5396375 (@lem5396385)). Qed.
Lemma lem5396388 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396389 : term218 = term219.
Proof. exact (@lem5396388 (NUMERAL 0) term7). Qed.
Lemma lem5396390 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396391 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396392 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396391 h1) (fun h1 : term219 = True => @lem5396390)). Qed.
Lemma lem5396393 : term219 = True.
Proof. exact (EQ_MP (@lem5396392) (@lem5396390)). Qed.
Lemma lem5396394 : term218 = True.
Proof. exact (TRANS (@lem5396389) (@lem5396393)). Qed.
Lemma lem5396395 : True = term218.
Proof. exact (SYM (@lem5396394)). Qed.
Lemma lem5396396 : term218.
Proof. exact (EQ_MP (@lem5396395) (@lem0)). Qed.
Lemma lem5396397 : term405.
Proof. exact (@lem5396386 (@lem5396396)). Qed.
Lemma lem5396399 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396400 : term218 = term219.
Proof. exact (@lem5396399 (NUMERAL 0) term7). Qed.
Lemma lem5396401 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396402 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396403 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396402 h1) (fun h1 : term219 = True => @lem5396401)). Qed.
Lemma lem5396404 : term219 = True.
Proof. exact (EQ_MP (@lem5396403) (@lem5396401)). Qed.
Lemma lem5396405 : term218 = True.
Proof. exact (TRANS (@lem5396400) (@lem5396404)). Qed.
Lemma lem5396406 : True = term218.
Proof. exact (SYM (@lem5396405)). Qed.
Lemma lem5396407 : term218.
Proof. exact (EQ_MP (@lem5396406) (@lem0)). Qed.
Lemma lem5396408 : term406.
Proof. exact (@lem5396397 (@lem5396407)). Qed.
Lemma lem5396410 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396411 : term180 = term181.
Proof. exact (@lem5396410 term7 term7). Qed.
Lemma lem5396412 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396413 : term183 = term7.
Proof. exact (EQ_MP (@lem5396412) (@lem940073)). Qed.
Lemma lem5396414 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396415 : term181 = term127.
Proof. exact (MK_COMB (@lem5396414) (@lem5396413)). Qed.
Lemma lem5396416 : term180 = term127.
Proof. exact (TRANS (@lem5396411) (@lem5396415)). Qed.
Lemma lem5396418 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396419 : term197 = term202.
Proof. exact (@lem5396418 term7 term7). Qed.
Lemma lem5396420 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396421 : term183 = term7.
Proof. exact (EQ_MP (@lem5396420) (@lem940073)). Qed.
Lemma lem5396422 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396423 : term181 = term127.
Proof. exact (MK_COMB (@lem5396422) (@lem5396421)). Qed.
Lemma lem5396424 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396425 : term202 = term171.
Proof. exact (MK_COMB (@lem5396424) (@lem5396423)). Qed.
Lemma lem5396426 : term197 = term171.
Proof. exact (TRANS (@lem5396419) (@lem5396425)). Qed.
Lemma lem5396427 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396428 : term407 = term399.
Proof. exact (MK_COMB (@lem5396427) (@lem5396426)). Qed.
Lemma lem5396429 : term408 = term401.
Proof. exact (MK_COMB (@lem5396428) (@lem5396416)). Qed.
Lemma lem5396431 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5396432 : term401 = term118.
Proof. exact (@lem5396431 term7). Qed.
Lemma lem5396433 : term408 = term118.
Proof. exact (TRANS (@lem5396429) (@lem5396432)). Qed.
Lemma lem5396434 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5396435 : term410 = term228.
Proof. exact (MK_COMB (@lem5396434) (@lem5396433)). Qed.
Lemma lem5396436 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5396437 : term411 = term230.
Proof. exact (MK_COMB (@lem5396435) (@lem5396436)). Qed.
Lemma lem5396439 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396440 : term230 = term118.
Proof. exact (@lem5396439 term7). Qed.
Lemma lem5396441 : term411 = term118.
Proof. exact (TRANS (@lem5396437) (@lem5396440)). Qed.
Lemma lem5396443 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396444 : term180 = term181.
Proof. exact (@lem5396443 term7 term7). Qed.
Lemma lem5396445 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396446 : term183 = term7.
Proof. exact (EQ_MP (@lem5396445) (@lem940073)). Qed.
Lemma lem5396447 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396448 : term181 = term127.
Proof. exact (MK_COMB (@lem5396447) (@lem5396446)). Qed.
Lemma lem5396449 : term180 = term127.
Proof. exact (TRANS (@lem5396444) (@lem5396448)). Qed.
Lemma lem5396450 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5396451 : term232 = term230.
Proof. exact (MK_COMB (@lem5396450) (@lem5396449)). Qed.
Lemma lem5396453 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396454 : term230 = term118.
Proof. exact (@lem5396453 term7). Qed.
Lemma lem5396455 : term232 = term118.
Proof. exact (TRANS (@lem5396451) (@lem5396454)). Qed.
Lemma lem5396456 : term118 = term232.
Proof. exact (SYM (@lem5396455)). Qed.
Lemma lem5396457 : term411 = term232.
Proof. exact (TRANS (@lem5396441) (@lem5396456)). Qed.
Lemma lem5396458 : term402 = term168.
Proof. exact (@lem5396408 (@lem5396457)). Qed.
Lemma lem5396459 : term401 = term168.
Proof. exact (TRANS (@lem5396374) (@lem5396458)). Qed.
Lemma lem5396461 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5396462 : term168 = term118.
Proof. exact (@lem5396461 term118). Qed.
Lemma lem5396463 : term401 = term118.
Proof. exact (TRANS (@lem5396459) (@lem5396462)). Qed.
Lemma lem5396464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5396465 : term412 = term228.
Proof. exact (MK_COMB (@lem5396464) (@lem5396463)). Qed.
Lemma lem5396466 (_69874 : int) : (real_of_int _69874) = (real_of_int _69874).
Proof. exact (eq_refl (real_of_int _69874)). Qed.
Lemma lem5396467 (_69874 : int) : (term398 _69874) = (term413 _69874).
Proof. exact (MK_COMB (@lem5396465) (@lem5396466 _69874)). Qed.
Lemma lem5396468 (_69874 : int) : (term397 _69874) = (term413 _69874).
Proof. exact (TRANS (@lem5396365 _69874) (@lem5396467 _69874)). Qed.
Lemma lem5396469 (_69874 : int) : (term413 _69874) = term118.
Proof. exact (@lem1982719 (real_of_int _69874)). Qed.
Lemma lem5396470 (_69874 : int) : (term397 _69874) = term118.
Proof. exact (TRANS (@lem5396468 _69874) (@lem5396469 _69874)). Qed.
Lemma lem5396471 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396472 (_69874 : int) : (term414 _69874) = term415.
Proof. exact (MK_COMB (@lem5396471) (@lem5396470 _69874)). Qed.
Lemma lem5396473 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5396474 (_69874 : int) : (term501 _69874) = term420.
Proof. exact (MK_COMB (@lem5396472 _69874) (@lem5396473)). Qed.
Lemma lem5396475 (_69874 : int) : (term500 _69874) = term420.
Proof. exact (TRANS (@lem5396364 _69874) (@lem5396474 _69874)). Qed.
Lemma lem5396476 : term420 = term171.
Proof. exact (@lem1982721 term171). Qed.
Lemma lem5396477 (_69874 : int) : (term500 _69874) = term171.
Proof. exact (TRANS (@lem5396475 _69874) (@lem5396476)). Qed.
Lemma lem5396478 (_69873 : int) (_69874 : int) : (term499 _69873 _69874) = term420.
Proof. exact (MK_COMB (@lem5396363 _69873) (@lem5396477 _69874)). Qed.
Lemma lem5396479 (_69873 : int) (_69874 : int) : (term498 _69873 _69874) = term420.
Proof. exact (TRANS (@lem5396255 _69873 _69874) (@lem5396478 _69873 _69874)). Qed.
Lemma lem5396480 : term420 = term171.
Proof. exact (@lem1982721 term171). Qed.
Lemma lem5396481 (_69873 : int) (_69874 : int) : (term498 _69873 _69874) = term171.
Proof. exact (TRANS (@lem5396479 _69873 _69874) (@lem5396480)). Qed.
Lemma lem5396482 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5396483 (_69873 : int) (_69874 : int) : (term502 _69873 _69874) = term422.
Proof. exact (MK_COMB (@lem5396482) (@lem5396481 _69873 _69874)). Qed.
Lemma lem5396484 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396485 (_69873 : int) (_69874 : int) : (term497 _69873 _69874) = term423.
Proof. exact (MK_COMB (@lem5396483 _69873 _69874) (@lem5396484)). Qed.
Lemma lem5396486 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : term423.
Proof. exact (EQ_MP (@lem5396485 _69873 _69874) (@lem5396254 _69873 _69874 h1)). Qed.
Lemma lem5396488 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5396489 : term423 = term424.
Proof. exact (@lem5396488 term118 term171). Qed.
Lemma lem5396491 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5396492 : term171 = term172.
Proof. exact (@lem5396491 term7). Qed.
Lemma lem5396494 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396495 : term118 = term168.
Proof. exact (@lem5396494 (NUMERAL 0)). Qed.
Lemma lem5396496 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5396497 : term120 = term425.
Proof. exact (MK_COMB (@lem5396496) (@lem5396495)). Qed.
Lemma lem5396498 : term424 = term426.
Proof. exact (MK_COMB (@lem5396497) (@lem5396492)). Qed.
Lemma lem5396499 : term427.
Proof. exact (@lem1980026 term118 term127 term171 term127). Qed.
Lemma lem5396501 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396502 : term218 = term219.
Proof. exact (@lem5396501 (NUMERAL 0) term7). Qed.
Lemma lem5396503 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396504 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396505 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396504 h1) (fun h1 : term219 = True => @lem5396503)). Qed.
Lemma lem5396506 : term219 = True.
Proof. exact (EQ_MP (@lem5396505) (@lem5396503)). Qed.
Lemma lem5396507 : term218 = True.
Proof. exact (TRANS (@lem5396502) (@lem5396506)). Qed.
Lemma lem5396508 : True = term218.
Proof. exact (SYM (@lem5396507)). Qed.
Lemma lem5396509 : term218.
Proof. exact (EQ_MP (@lem5396508) (@lem0)). Qed.
Lemma lem5396510 : term428.
Proof. exact (@lem5396499 (@lem5396509)). Qed.
Lemma lem5396512 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396513 : term218 = term219.
Proof. exact (@lem5396512 (NUMERAL 0) term7). Qed.
Lemma lem5396514 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396515 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396516 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396515 h1) (fun h1 : term219 = True => @lem5396514)). Qed.
Lemma lem5396517 : term219 = True.
Proof. exact (EQ_MP (@lem5396516) (@lem5396514)). Qed.
Lemma lem5396518 : term218 = True.
Proof. exact (TRANS (@lem5396513) (@lem5396517)). Qed.
Lemma lem5396519 : True = term218.
Proof. exact (SYM (@lem5396518)). Qed.
Lemma lem5396520 : term218.
Proof. exact (EQ_MP (@lem5396519) (@lem0)). Qed.
Lemma lem5396521 : term426 = term429.
Proof. exact (@lem5396510 (@lem5396520)). Qed.
Lemma lem5396523 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396524 : term197 = term202.
Proof. exact (@lem5396523 term7 term7). Qed.
Lemma lem5396525 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396526 : term183 = term7.
Proof. exact (EQ_MP (@lem5396525) (@lem940073)). Qed.
Lemma lem5396527 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396528 : term181 = term127.
Proof. exact (MK_COMB (@lem5396527) (@lem5396526)). Qed.
Lemma lem5396529 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396530 : term202 = term171.
Proof. exact (MK_COMB (@lem5396529) (@lem5396528)). Qed.
Lemma lem5396531 : term197 = term171.
Proof. exact (TRANS (@lem5396524) (@lem5396530)). Qed.
Lemma lem5396533 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396534 : term230 = term118.
Proof. exact (@lem5396533 term7). Qed.
Lemma lem5396535 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5396536 : term430 = term120.
Proof. exact (MK_COMB (@lem5396535) (@lem5396534)). Qed.
Lemma lem5396537 : term429 = term424.
Proof. exact (MK_COMB (@lem5396536) (@lem5396531)). Qed.
Lemma lem5396539 (m : nat) (n : nat) : (term431 m n) = (term432 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5396540 : term424 = term433.
Proof. exact (@lem5396539 (NUMERAL 0) term7). Qed.
Lemma lem5396541 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396542 (h1 : term220 = (BIT1 0)) : (term7 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5396543 : (term220 = (BIT1 0)) = ((term7 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396542 h1) (fun h1 : (term7 = (NUMERAL 0)) = False => @lem5396541)). Qed.
Lemma lem5396544 : (term7 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5396543) (@lem5396541)). Qed.
Lemma lem5396545 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5396546 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5396547 : term434 = (and True).
Proof. exact (MK_COMB (@lem5396546) (@lem5396545)). Qed.
Lemma lem5396548 : term433 = (True /\ False).
Proof. exact (MK_COMB (@lem5396547) (@lem5396544)). Qed.
Lemma lem5396550 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5396551 : term433 = False.
Proof. exact (TRANS (@lem5396548) (@lem5396550)). Qed.
Lemma lem5396552 : term424 = False.
Proof. exact (TRANS (@lem5396540) (@lem5396551)). Qed.
Lemma lem5396553 : term429 = False.
Proof. exact (TRANS (@lem5396537) (@lem5396552)). Qed.
Lemma lem5396554 : term426 = False.
Proof. exact (TRANS (@lem5396521) (@lem5396553)). Qed.
Lemma lem5396555 : term424 = False.
Proof. exact (TRANS (@lem5396498) (@lem5396554)). Qed.
Lemma lem5396556 : term423 = False.
Proof. exact (TRANS (@lem5396489) (@lem5396555)). Qed.
Lemma lem5396557 (_69873 : int) (_69874 : int) (h1 : term487 _69873 _69874) : False.
Proof. exact (EQ_MP (@lem5396556) (@lem5396486 _69873 _69874 h1)). Qed.
Lemma lem5396558 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term503 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5396559 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term346 _69873 _69874.
Proof. exact (proj2 (@lem5396558 _69873 _69874 h1)). Qed.
Lemma lem5396561 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term333 _69873 _69874.
Proof. exact (proj2 (@lem5396559 _69873 _69874 h1)). Qed.
Lemma lem5396562 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term191 _69874.
Proof. exact (proj1 (@lem5396559 _69873 _69874 h1)). Qed.
Lemma lem5396563 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term312 _69873 _69874.
Proof. exact (proj2 (@lem5396561 _69873 _69874 h1)). Qed.
Lemma lem5396564 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term300 _69874 _69873.
Proof. exact (proj1 (@lem5396561 _69873 _69874 h1)). Qed.
Lemma lem5396565 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : (real_of_int _69873) = term118.
Proof. exact (proj2 (@lem5396564 _69873 _69874 h1)). Qed.
Lemma lem5396568 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5396569 : term355 = term218.
Proof. exact (@lem5396568 term118 term127). Qed.
Lemma lem5396571 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396572 : term127 = term196.
Proof. exact (@lem5396571 term7). Qed.
Lemma lem5396574 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396575 : term118 = term168.
Proof. exact (@lem5396574 (NUMERAL 0)). Qed.
Lemma lem5396576 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396577 : term356 = term357.
Proof. exact (MK_COMB (@lem5396576) (@lem5396575)). Qed.
Lemma lem5396578 : term218 = term358.
Proof. exact (MK_COMB (@lem5396577) (@lem5396572)). Qed.
Lemma lem5396579 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5396581 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396582 : term218 = term219.
Proof. exact (@lem5396581 (NUMERAL 0) term7). Qed.
Lemma lem5396583 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396584 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396585 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396584 h1) (fun h1 : term219 = True => @lem5396583)). Qed.
Lemma lem5396586 : term219 = True.
Proof. exact (EQ_MP (@lem5396585) (@lem5396583)). Qed.
Lemma lem5396587 : term218 = True.
Proof. exact (TRANS (@lem5396582) (@lem5396586)). Qed.
Lemma lem5396588 : True = term218.
Proof. exact (SYM (@lem5396587)). Qed.
Lemma lem5396589 : term218.
Proof. exact (EQ_MP (@lem5396588) (@lem0)). Qed.
Lemma lem5396590 : term360.
Proof. exact (@lem5396579 (@lem5396589)). Qed.
Lemma lem5396592 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396593 : term218 = term219.
Proof. exact (@lem5396592 (NUMERAL 0) term7). Qed.
Lemma lem5396594 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396595 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396596 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396595 h1) (fun h1 : term219 = True => @lem5396594)). Qed.
Lemma lem5396597 : term219 = True.
Proof. exact (EQ_MP (@lem5396596) (@lem5396594)). Qed.
Lemma lem5396598 : term218 = True.
Proof. exact (TRANS (@lem5396593) (@lem5396597)). Qed.
Lemma lem5396599 : True = term218.
Proof. exact (SYM (@lem5396598)). Qed.
Lemma lem5396600 : term218.
Proof. exact (EQ_MP (@lem5396599) (@lem0)). Qed.
Lemma lem5396601 : term358 = term361.
Proof. exact (@lem5396590 (@lem5396600)). Qed.
Lemma lem5396603 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396604 : term180 = term181.
Proof. exact (@lem5396603 term7 term7). Qed.
Lemma lem5396605 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396606 : term183 = term7.
Proof. exact (EQ_MP (@lem5396605) (@lem940073)). Qed.
Lemma lem5396607 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396608 : term181 = term127.
Proof. exact (MK_COMB (@lem5396607) (@lem5396606)). Qed.
Lemma lem5396609 : term180 = term127.
Proof. exact (TRANS (@lem5396604) (@lem5396608)). Qed.
Lemma lem5396611 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396612 : term230 = term118.
Proof. exact (@lem5396611 term7). Qed.
Lemma lem5396613 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396614 : term362 = term356.
Proof. exact (MK_COMB (@lem5396613) (@lem5396612)). Qed.
Lemma lem5396615 : term361 = term218.
Proof. exact (MK_COMB (@lem5396614) (@lem5396609)). Qed.
Lemma lem5396617 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396618 : term218 = term219.
Proof. exact (@lem5396617 (NUMERAL 0) term7). Qed.
Lemma lem5396619 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396620 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396621 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396620 h1) (fun h1 : term219 = True => @lem5396619)). Qed.
Lemma lem5396622 : term219 = True.
Proof. exact (EQ_MP (@lem5396621) (@lem5396619)). Qed.
Lemma lem5396623 : term218 = True.
Proof. exact (TRANS (@lem5396618) (@lem5396622)). Qed.
Lemma lem5396624 : term361 = True.
Proof. exact (TRANS (@lem5396615) (@lem5396623)). Qed.
Lemma lem5396625 : term358 = True.
Proof. exact (TRANS (@lem5396601) (@lem5396624)). Qed.
Lemma lem5396626 : term218 = True.
Proof. exact (TRANS (@lem5396578) (@lem5396625)). Qed.
Lemma lem5396627 : term355 = True.
Proof. exact (TRANS (@lem5396569) (@lem5396626)). Qed.
Lemma lem5396628 : True = term355.
Proof. exact (SYM (@lem5396627)). Qed.
Lemma lem5396629 : term355.
Proof. exact (EQ_MP (@lem5396628) (@lem0)). Qed.
Lemma lem5396630 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term504 _69874.
Proof. exact (conj (@lem5396629) (@lem5396562 _69873 _69874 h1)). Qed.
Lemma lem5396632 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5396633 (_69874 : int) : term505 _69874.
Proof. exact (@lem5396632 term127 (real_of_int _69874)). Qed.
Lemma lem5396634 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term506 _69874.
Proof. exact (@lem5396633 _69874 (@lem5396630 _69873 _69874 h1)). Qed.
Lemma lem5396635 (_69874 : int) : (term385 _69874) = (real_of_int _69874).
Proof. exact (@lem1982733 (real_of_int _69874)). Qed.
Lemma lem5396636 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5396637 (_69874 : int) : (term507 _69874) = (term190 _69874).
Proof. exact (MK_COMB (@lem5396636) (@lem5396635 _69874)). Qed.
Lemma lem5396638 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396639 (_69874 : int) : (term506 _69874) = (term191 _69874).
Proof. exact (MK_COMB (@lem5396637 _69874) (@lem5396638)). Qed.
Lemma lem5396640 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term191 _69874.
Proof. exact (EQ_MP (@lem5396639 _69874) (@lem5396634 _69873 _69874 h1)). Qed.
Lemma lem5396642 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5396643 : term355 = term218.
Proof. exact (@lem5396642 term118 term127). Qed.
Lemma lem5396645 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396646 : term127 = term196.
Proof. exact (@lem5396645 term7). Qed.
Lemma lem5396648 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396649 : term118 = term168.
Proof. exact (@lem5396648 (NUMERAL 0)). Qed.
Lemma lem5396650 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396651 : term356 = term357.
Proof. exact (MK_COMB (@lem5396650) (@lem5396649)). Qed.
Lemma lem5396652 : term218 = term358.
Proof. exact (MK_COMB (@lem5396651) (@lem5396646)). Qed.
Lemma lem5396653 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5396655 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396656 : term218 = term219.
Proof. exact (@lem5396655 (NUMERAL 0) term7). Qed.
Lemma lem5396657 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396658 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396659 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396658 h1) (fun h1 : term219 = True => @lem5396657)). Qed.
Lemma lem5396660 : term219 = True.
Proof. exact (EQ_MP (@lem5396659) (@lem5396657)). Qed.
Lemma lem5396661 : term218 = True.
Proof. exact (TRANS (@lem5396656) (@lem5396660)). Qed.
Lemma lem5396662 : True = term218.
Proof. exact (SYM (@lem5396661)). Qed.
Lemma lem5396663 : term218.
Proof. exact (EQ_MP (@lem5396662) (@lem0)). Qed.
Lemma lem5396664 : term360.
Proof. exact (@lem5396653 (@lem5396663)). Qed.
Lemma lem5396666 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396667 : term218 = term219.
Proof. exact (@lem5396666 (NUMERAL 0) term7). Qed.
Lemma lem5396668 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396669 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396670 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396669 h1) (fun h1 : term219 = True => @lem5396668)). Qed.
Lemma lem5396671 : term219 = True.
Proof. exact (EQ_MP (@lem5396670) (@lem5396668)). Qed.
Lemma lem5396672 : term218 = True.
Proof. exact (TRANS (@lem5396667) (@lem5396671)). Qed.
Lemma lem5396673 : True = term218.
Proof. exact (SYM (@lem5396672)). Qed.
Lemma lem5396674 : term218.
Proof. exact (EQ_MP (@lem5396673) (@lem0)). Qed.
Lemma lem5396675 : term358 = term361.
Proof. exact (@lem5396664 (@lem5396674)). Qed.
Lemma lem5396677 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396678 : term180 = term181.
Proof. exact (@lem5396677 term7 term7). Qed.
Lemma lem5396679 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396680 : term183 = term7.
Proof. exact (EQ_MP (@lem5396679) (@lem940073)). Qed.
Lemma lem5396681 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396682 : term181 = term127.
Proof. exact (MK_COMB (@lem5396681) (@lem5396680)). Qed.
Lemma lem5396683 : term180 = term127.
Proof. exact (TRANS (@lem5396678) (@lem5396682)). Qed.
Lemma lem5396685 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396686 : term230 = term118.
Proof. exact (@lem5396685 term7). Qed.
Lemma lem5396687 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396688 : term362 = term356.
Proof. exact (MK_COMB (@lem5396687) (@lem5396686)). Qed.
Lemma lem5396689 : term361 = term218.
Proof. exact (MK_COMB (@lem5396688) (@lem5396683)). Qed.
Lemma lem5396691 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396692 : term218 = term219.
Proof. exact (@lem5396691 (NUMERAL 0) term7). Qed.
Lemma lem5396693 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396694 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396695 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396694 h1) (fun h1 : term219 = True => @lem5396693)). Qed.
Lemma lem5396696 : term219 = True.
Proof. exact (EQ_MP (@lem5396695) (@lem5396693)). Qed.
Lemma lem5396697 : term218 = True.
Proof. exact (TRANS (@lem5396692) (@lem5396696)). Qed.
Lemma lem5396698 : term361 = True.
Proof. exact (TRANS (@lem5396689) (@lem5396697)). Qed.
Lemma lem5396699 : term358 = True.
Proof. exact (TRANS (@lem5396675) (@lem5396698)). Qed.
Lemma lem5396700 : term218 = True.
Proof. exact (TRANS (@lem5396652) (@lem5396699)). Qed.
Lemma lem5396701 : term355 = True.
Proof. exact (TRANS (@lem5396643) (@lem5396700)). Qed.
Lemma lem5396702 : True = term355.
Proof. exact (SYM (@lem5396701)). Qed.
Lemma lem5396703 : term355.
Proof. exact (EQ_MP (@lem5396702) (@lem0)). Qed.
Lemma lem5396704 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term488 _69873 _69874.
Proof. exact (conj (@lem5396703) (@lem5396563 _69873 _69874 h1)). Qed.
Lemma lem5396706 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5396707 (_69873 : int) (_69874 : int) : term489 _69873 _69874.
Proof. exact (@lem5396706 term127 (term306 _69873 _69874)). Qed.
Lemma lem5396708 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term490 _69873 _69874.
Proof. exact (@lem5396707 _69873 _69874 (@lem5396704 _69873 _69874 h1)). Qed.
Lemma lem5396709 (_69873 : int) (_69874 : int) : (term491 _69873 _69874) = (term306 _69873 _69874).
Proof. exact (@lem1982733 (term306 _69873 _69874)). Qed.
Lemma lem5396710 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5396711 (_69873 : int) (_69874 : int) : (term492 _69873 _69874) = (term311 _69873 _69874).
Proof. exact (MK_COMB (@lem5396710) (@lem5396709 _69873 _69874)). Qed.
Lemma lem5396712 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396713 (_69873 : int) (_69874 : int) : (term490 _69873 _69874) = (term312 _69873 _69874).
Proof. exact (MK_COMB (@lem5396711 _69873 _69874) (@lem5396712)). Qed.
Lemma lem5396714 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term312 _69873 _69874.
Proof. exact (EQ_MP (@lem5396713 _69873 _69874) (@lem5396708 _69873 _69874 h1)). Qed.
Lemma lem5396716 (y : real) : term369 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem5396717 (_69873 : int) : term436 _69873.
Proof. exact (@lem5396716 (real_of_int _69873)). Qed.
Lemma lem5396718 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term437 _69873.
Proof. exact (@lem5396717 _69873 (@lem5396565 _69873 _69874 h1)). Qed.
Lemma lem5396719 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term508 _69873.
Proof. exact (@lem5396718 _69873 _69874 h1 term171). Qed.
Lemma lem5396720 (_69873 : int) : (term508 _69873) = ((term209 _69873) = term118).
Proof. exact (eq_refl (term508 _69873)). Qed.
Lemma lem5396727 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : (term209 _69873) = term118.
Proof. exact (EQ_MP (@lem5396720 _69873) (@lem5396719 _69873 _69874 h1)). Qed.
Lemma lem5396728 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term509 _69873 _69874.
Proof. exact (conj (@lem5396727 _69873 _69874 h1) (@lem5396714 _69873 _69874 h1)). Qed.
Lemma lem5396730 (x : real) (y : real) : term391 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem5396731 (_69873 : int) (_69874 : int) : term510 _69873 _69874.
Proof. exact (@lem5396730 (term209 _69873) (term306 _69873 _69874)). Qed.
Lemma lem5396732 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term511 _69873 _69874.
Proof. exact (@lem5396731 _69873 _69874 (@lem5396728 _69873 _69874 h1)). Qed.
Lemma lem5396733 (_69873 : int) (_69874 : int) : (term512 _69873 _69874) = (term513 _69873 _69874).
Proof. exact (@lem1982763 (term209 _69873) (real_of_int _69873) (term206 _69874)). Qed.
Lemma lem5396734 (_69873 : int) : (term418 _69873) = (term398 _69873).
Proof. exact (@lem1982713 term171 (real_of_int _69873)). Qed.
Lemma lem5396736 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396737 : term127 = term196.
Proof. exact (@lem5396736 term7). Qed.
Lemma lem5396739 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5396740 : term171 = term172.
Proof. exact (@lem5396739 term7). Qed.
Lemma lem5396741 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396742 : term399 = term400.
Proof. exact (MK_COMB (@lem5396741) (@lem5396740)). Qed.
Lemma lem5396743 : term401 = term402.
Proof. exact (MK_COMB (@lem5396742) (@lem5396737)). Qed.
Lemma lem5396744 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5396746 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396747 : term218 = term219.
Proof. exact (@lem5396746 (NUMERAL 0) term7). Qed.
Lemma lem5396748 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396749 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396750 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396749 h1) (fun h1 : term219 = True => @lem5396748)). Qed.
Lemma lem5396751 : term219 = True.
Proof. exact (EQ_MP (@lem5396750) (@lem5396748)). Qed.
Lemma lem5396752 : term218 = True.
Proof. exact (TRANS (@lem5396747) (@lem5396751)). Qed.
Lemma lem5396753 : True = term218.
Proof. exact (SYM (@lem5396752)). Qed.
Lemma lem5396754 : term218.
Proof. exact (EQ_MP (@lem5396753) (@lem0)). Qed.
Lemma lem5396755 : term404.
Proof. exact (@lem5396744 (@lem5396754)). Qed.
Lemma lem5396757 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396758 : term218 = term219.
Proof. exact (@lem5396757 (NUMERAL 0) term7). Qed.
Lemma lem5396759 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396760 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396761 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396760 h1) (fun h1 : term219 = True => @lem5396759)). Qed.
Lemma lem5396762 : term219 = True.
Proof. exact (EQ_MP (@lem5396761) (@lem5396759)). Qed.
Lemma lem5396763 : term218 = True.
Proof. exact (TRANS (@lem5396758) (@lem5396762)). Qed.
Lemma lem5396764 : True = term218.
Proof. exact (SYM (@lem5396763)). Qed.
Lemma lem5396765 : term218.
Proof. exact (EQ_MP (@lem5396764) (@lem0)). Qed.
Lemma lem5396766 : term405.
Proof. exact (@lem5396755 (@lem5396765)). Qed.
Lemma lem5396768 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396769 : term218 = term219.
Proof. exact (@lem5396768 (NUMERAL 0) term7). Qed.
Lemma lem5396770 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396771 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396772 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396771 h1) (fun h1 : term219 = True => @lem5396770)). Qed.
Lemma lem5396773 : term219 = True.
Proof. exact (EQ_MP (@lem5396772) (@lem5396770)). Qed.
Lemma lem5396774 : term218 = True.
Proof. exact (TRANS (@lem5396769) (@lem5396773)). Qed.
Lemma lem5396775 : True = term218.
Proof. exact (SYM (@lem5396774)). Qed.
Lemma lem5396776 : term218.
Proof. exact (EQ_MP (@lem5396775) (@lem0)). Qed.
Lemma lem5396777 : term406.
Proof. exact (@lem5396766 (@lem5396776)). Qed.
Lemma lem5396779 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396780 : term180 = term181.
Proof. exact (@lem5396779 term7 term7). Qed.
Lemma lem5396781 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396782 : term183 = term7.
Proof. exact (EQ_MP (@lem5396781) (@lem940073)). Qed.
Lemma lem5396783 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396784 : term181 = term127.
Proof. exact (MK_COMB (@lem5396783) (@lem5396782)). Qed.
Lemma lem5396785 : term180 = term127.
Proof. exact (TRANS (@lem5396780) (@lem5396784)). Qed.
Lemma lem5396787 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396788 : term197 = term202.
Proof. exact (@lem5396787 term7 term7). Qed.
Lemma lem5396789 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396790 : term183 = term7.
Proof. exact (EQ_MP (@lem5396789) (@lem940073)). Qed.
Lemma lem5396791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396792 : term181 = term127.
Proof. exact (MK_COMB (@lem5396791) (@lem5396790)). Qed.
Lemma lem5396793 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396794 : term202 = term171.
Proof. exact (MK_COMB (@lem5396793) (@lem5396792)). Qed.
Lemma lem5396795 : term197 = term171.
Proof. exact (TRANS (@lem5396788) (@lem5396794)). Qed.
Lemma lem5396796 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396797 : term407 = term399.
Proof. exact (MK_COMB (@lem5396796) (@lem5396795)). Qed.
Lemma lem5396798 : term408 = term401.
Proof. exact (MK_COMB (@lem5396797) (@lem5396785)). Qed.
Lemma lem5396800 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5396801 : term401 = term118.
Proof. exact (@lem5396800 term7). Qed.
Lemma lem5396802 : term408 = term118.
Proof. exact (TRANS (@lem5396798) (@lem5396801)). Qed.
Lemma lem5396803 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5396804 : term410 = term228.
Proof. exact (MK_COMB (@lem5396803) (@lem5396802)). Qed.
Lemma lem5396805 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5396806 : term411 = term230.
Proof. exact (MK_COMB (@lem5396804) (@lem5396805)). Qed.
Lemma lem5396808 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396809 : term230 = term118.
Proof. exact (@lem5396808 term7). Qed.
Lemma lem5396810 : term411 = term118.
Proof. exact (TRANS (@lem5396806) (@lem5396809)). Qed.
Lemma lem5396812 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396813 : term180 = term181.
Proof. exact (@lem5396812 term7 term7). Qed.
Lemma lem5396814 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396815 : term183 = term7.
Proof. exact (EQ_MP (@lem5396814) (@lem940073)). Qed.
Lemma lem5396816 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396817 : term181 = term127.
Proof. exact (MK_COMB (@lem5396816) (@lem5396815)). Qed.
Lemma lem5396818 : term180 = term127.
Proof. exact (TRANS (@lem5396813) (@lem5396817)). Qed.
Lemma lem5396819 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5396820 : term232 = term230.
Proof. exact (MK_COMB (@lem5396819) (@lem5396818)). Qed.
Lemma lem5396822 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396823 : term230 = term118.
Proof. exact (@lem5396822 term7). Qed.
Lemma lem5396824 : term232 = term118.
Proof. exact (TRANS (@lem5396820) (@lem5396823)). Qed.
Lemma lem5396825 : term118 = term232.
Proof. exact (SYM (@lem5396824)). Qed.
Lemma lem5396826 : term411 = term232.
Proof. exact (TRANS (@lem5396810) (@lem5396825)). Qed.
Lemma lem5396827 : term402 = term168.
Proof. exact (@lem5396777 (@lem5396826)). Qed.
Lemma lem5396828 : term401 = term168.
Proof. exact (TRANS (@lem5396743) (@lem5396827)). Qed.
Lemma lem5396830 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5396831 : term168 = term118.
Proof. exact (@lem5396830 term118). Qed.
Lemma lem5396832 : term401 = term118.
Proof. exact (TRANS (@lem5396828) (@lem5396831)). Qed.
Lemma lem5396833 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5396834 : term412 = term228.
Proof. exact (MK_COMB (@lem5396833) (@lem5396832)). Qed.
Lemma lem5396835 (_69873 : int) : (real_of_int _69873) = (real_of_int _69873).
Proof. exact (eq_refl (real_of_int _69873)). Qed.
Lemma lem5396836 (_69873 : int) : (term398 _69873) = (term413 _69873).
Proof. exact (MK_COMB (@lem5396834) (@lem5396835 _69873)). Qed.
Lemma lem5396837 (_69873 : int) : (term418 _69873) = (term413 _69873).
Proof. exact (TRANS (@lem5396734 _69873) (@lem5396836 _69873)). Qed.
Lemma lem5396838 (_69873 : int) : (term413 _69873) = term118.
Proof. exact (@lem1982719 (real_of_int _69873)). Qed.
Lemma lem5396839 (_69873 : int) : (term418 _69873) = term118.
Proof. exact (TRANS (@lem5396837 _69873) (@lem5396838 _69873)). Qed.
Lemma lem5396840 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396841 (_69873 : int) : (term419 _69873) = term415.
Proof. exact (MK_COMB (@lem5396840) (@lem5396839 _69873)). Qed.
Lemma lem5396842 (_69874 : int) : (term206 _69874) = (term206 _69874).
Proof. exact (eq_refl (term206 _69874)). Qed.
Lemma lem5396843 (_69873 : int) (_69874 : int) : (term513 _69873 _69874) = (term514 _69874).
Proof. exact (MK_COMB (@lem5396841 _69873) (@lem5396842 _69874)). Qed.
Lemma lem5396844 (_69873 : int) (_69874 : int) : (term512 _69873 _69874) = (term514 _69874).
Proof. exact (TRANS (@lem5396733 _69873 _69874) (@lem5396843 _69873 _69874)). Qed.
Lemma lem5396845 (_69874 : int) : (term514 _69874) = (term206 _69874).
Proof. exact (@lem1982721 (term206 _69874)). Qed.
Lemma lem5396846 (_69873 : int) (_69874 : int) : (term512 _69873 _69874) = (term206 _69874).
Proof. exact (TRANS (@lem5396844 _69873 _69874) (@lem5396845 _69874)). Qed.
Lemma lem5396847 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5396848 (_69873 : int) (_69874 : int) : (term515 _69873 _69874) = (term296 _69874).
Proof. exact (MK_COMB (@lem5396847) (@lem5396846 _69873 _69874)). Qed.
Lemma lem5396849 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396850 (_69873 : int) (_69874 : int) : (term511 _69873 _69874) = (term297 _69874).
Proof. exact (MK_COMB (@lem5396848 _69873 _69874) (@lem5396849)). Qed.
Lemma lem5396851 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term297 _69874.
Proof. exact (EQ_MP (@lem5396850 _69873 _69874) (@lem5396732 _69873 _69874 h1)). Qed.
Lemma lem5396853 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem5396854 : term355 = term218.
Proof. exact (@lem5396853 term118 term127). Qed.
Lemma lem5396856 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396857 : term127 = term196.
Proof. exact (@lem5396856 term7). Qed.
Lemma lem5396859 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396860 : term118 = term168.
Proof. exact (@lem5396859 (NUMERAL 0)). Qed.
Lemma lem5396861 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396862 : term356 = term357.
Proof. exact (MK_COMB (@lem5396861) (@lem5396860)). Qed.
Lemma lem5396863 : term218 = term358.
Proof. exact (MK_COMB (@lem5396862) (@lem5396857)). Qed.
Lemma lem5396864 : term359.
Proof. exact (@lem1980255 term118 term127 term127 term127). Qed.
Lemma lem5396866 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396867 : term218 = term219.
Proof. exact (@lem5396866 (NUMERAL 0) term7). Qed.
Lemma lem5396868 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396869 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396870 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396869 h1) (fun h1 : term219 = True => @lem5396868)). Qed.
Lemma lem5396871 : term219 = True.
Proof. exact (EQ_MP (@lem5396870) (@lem5396868)). Qed.
Lemma lem5396872 : term218 = True.
Proof. exact (TRANS (@lem5396867) (@lem5396871)). Qed.
Lemma lem5396873 : True = term218.
Proof. exact (SYM (@lem5396872)). Qed.
Lemma lem5396874 : term218.
Proof. exact (EQ_MP (@lem5396873) (@lem0)). Qed.
Lemma lem5396875 : term360.
Proof. exact (@lem5396864 (@lem5396874)). Qed.
Lemma lem5396877 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396878 : term218 = term219.
Proof. exact (@lem5396877 (NUMERAL 0) term7). Qed.
Lemma lem5396879 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396880 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396881 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396880 h1) (fun h1 : term219 = True => @lem5396879)). Qed.
Lemma lem5396882 : term219 = True.
Proof. exact (EQ_MP (@lem5396881) (@lem5396879)). Qed.
Lemma lem5396883 : term218 = True.
Proof. exact (TRANS (@lem5396878) (@lem5396882)). Qed.
Lemma lem5396884 : True = term218.
Proof. exact (SYM (@lem5396883)). Qed.
Lemma lem5396885 : term218.
Proof. exact (EQ_MP (@lem5396884) (@lem0)). Qed.
Lemma lem5396886 : term358 = term361.
Proof. exact (@lem5396875 (@lem5396885)). Qed.
Lemma lem5396888 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396889 : term180 = term181.
Proof. exact (@lem5396888 term7 term7). Qed.
Lemma lem5396890 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396891 : term183 = term7.
Proof. exact (EQ_MP (@lem5396890) (@lem940073)). Qed.
Lemma lem5396892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396893 : term181 = term127.
Proof. exact (MK_COMB (@lem5396892) (@lem5396891)). Qed.
Lemma lem5396894 : term180 = term127.
Proof. exact (TRANS (@lem5396889) (@lem5396893)). Qed.
Lemma lem5396896 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5396897 : term230 = term118.
Proof. exact (@lem5396896 term7). Qed.
Lemma lem5396898 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem5396899 : term362 = term356.
Proof. exact (MK_COMB (@lem5396898) (@lem5396897)). Qed.
Lemma lem5396900 : term361 = term218.
Proof. exact (MK_COMB (@lem5396899) (@lem5396894)). Qed.
Lemma lem5396902 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396903 : term218 = term219.
Proof. exact (@lem5396902 (NUMERAL 0) term7). Qed.
Lemma lem5396904 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396905 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396906 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396905 h1) (fun h1 : term219 = True => @lem5396904)). Qed.
Lemma lem5396907 : term219 = True.
Proof. exact (EQ_MP (@lem5396906) (@lem5396904)). Qed.
Lemma lem5396908 : term218 = True.
Proof. exact (TRANS (@lem5396903) (@lem5396907)). Qed.
Lemma lem5396909 : term361 = True.
Proof. exact (TRANS (@lem5396900) (@lem5396908)). Qed.
Lemma lem5396910 : term358 = True.
Proof. exact (TRANS (@lem5396886) (@lem5396909)). Qed.
Lemma lem5396911 : term218 = True.
Proof. exact (TRANS (@lem5396863) (@lem5396910)). Qed.
Lemma lem5396912 : term355 = True.
Proof. exact (TRANS (@lem5396854) (@lem5396911)). Qed.
Lemma lem5396913 : True = term355.
Proof. exact (SYM (@lem5396912)). Qed.
Lemma lem5396914 : term355.
Proof. exact (EQ_MP (@lem5396913) (@lem0)). Qed.
Lemma lem5396915 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term454 _69874.
Proof. exact (conj (@lem5396914) (@lem5396851 _69873 _69874 h1)). Qed.
Lemma lem5396917 (x : real) (y : real) : term364 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem5396918 (_69874 : int) : term455 _69874.
Proof. exact (@lem5396917 term127 (term206 _69874)). Qed.
Lemma lem5396919 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term456 _69874.
Proof. exact (@lem5396918 _69874 (@lem5396915 _69873 _69874 h1)). Qed.
Lemma lem5396920 (_69874 : int) : (term457 _69874) = (term206 _69874).
Proof. exact (@lem1982733 (term206 _69874)). Qed.
Lemma lem5396921 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5396922 (_69874 : int) : (term458 _69874) = (term296 _69874).
Proof. exact (MK_COMB (@lem5396921) (@lem5396920 _69874)). Qed.
Lemma lem5396923 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5396924 (_69874 : int) : (term456 _69874) = (term297 _69874).
Proof. exact (MK_COMB (@lem5396922 _69874) (@lem5396923)). Qed.
Lemma lem5396925 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term297 _69874.
Proof. exact (EQ_MP (@lem5396924 _69874) (@lem5396919 _69873 _69874 h1)). Qed.
Lemma lem5396926 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term516 _69874.
Proof. exact (conj (@lem5396925 _69873 _69874 h1) (@lem5396640 _69873 _69874 h1)). Qed.
Lemma lem5396928 (x : real) (y : real) : term460 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem5396929 (_69874 : int) : term517 _69874.
Proof. exact (@lem5396928 (term206 _69874) (real_of_int _69874)). Qed.
Lemma lem5396930 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term518 _69874.
Proof. exact (@lem5396929 _69874 (@lem5396926 _69873 _69874 h1)). Qed.
Lemma lem5396931 (_69874 : int) : (term519 _69874) = (term417 _69874).
Proof. exact (@lem1982759 (term209 _69874) (real_of_int _69874) term171). Qed.
Lemma lem5396932 (_69874 : int) : (term418 _69874) = (term398 _69874).
Proof. exact (@lem1982713 term171 (real_of_int _69874)). Qed.
Lemma lem5396934 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5396935 : term127 = term196.
Proof. exact (@lem5396934 term7). Qed.
Lemma lem5396937 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5396938 : term171 = term172.
Proof. exact (@lem5396937 term7). Qed.
Lemma lem5396939 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396940 : term399 = term400.
Proof. exact (MK_COMB (@lem5396939) (@lem5396938)). Qed.
Lemma lem5396941 : term401 = term402.
Proof. exact (MK_COMB (@lem5396940) (@lem5396935)). Qed.
Lemma lem5396942 : term403.
Proof. exact (@lem1981473 term171 term127 term127 term127 term118 term127). Qed.
Lemma lem5396944 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396945 : term218 = term219.
Proof. exact (@lem5396944 (NUMERAL 0) term7). Qed.
Lemma lem5396946 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396947 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396948 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396947 h1) (fun h1 : term219 = True => @lem5396946)). Qed.
Lemma lem5396949 : term219 = True.
Proof. exact (EQ_MP (@lem5396948) (@lem5396946)). Qed.
Lemma lem5396950 : term218 = True.
Proof. exact (TRANS (@lem5396945) (@lem5396949)). Qed.
Lemma lem5396951 : True = term218.
Proof. exact (SYM (@lem5396950)). Qed.
Lemma lem5396952 : term218.
Proof. exact (EQ_MP (@lem5396951) (@lem0)). Qed.
Lemma lem5396953 : term404.
Proof. exact (@lem5396942 (@lem5396952)). Qed.
Lemma lem5396955 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396956 : term218 = term219.
Proof. exact (@lem5396955 (NUMERAL 0) term7). Qed.
Lemma lem5396957 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396958 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396959 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396958 h1) (fun h1 : term219 = True => @lem5396957)). Qed.
Lemma lem5396960 : term219 = True.
Proof. exact (EQ_MP (@lem5396959) (@lem5396957)). Qed.
Lemma lem5396961 : term218 = True.
Proof. exact (TRANS (@lem5396956) (@lem5396960)). Qed.
Lemma lem5396962 : True = term218.
Proof. exact (SYM (@lem5396961)). Qed.
Lemma lem5396963 : term218.
Proof. exact (EQ_MP (@lem5396962) (@lem0)). Qed.
Lemma lem5396964 : term405.
Proof. exact (@lem5396953 (@lem5396963)). Qed.
Lemma lem5396966 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5396967 : term218 = term219.
Proof. exact (@lem5396966 (NUMERAL 0) term7). Qed.
Lemma lem5396968 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5396969 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5396970 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5396969 h1) (fun h1 : term219 = True => @lem5396968)). Qed.
Lemma lem5396971 : term219 = True.
Proof. exact (EQ_MP (@lem5396970) (@lem5396968)). Qed.
Lemma lem5396972 : term218 = True.
Proof. exact (TRANS (@lem5396967) (@lem5396971)). Qed.
Lemma lem5396973 : True = term218.
Proof. exact (SYM (@lem5396972)). Qed.
Lemma lem5396974 : term218.
Proof. exact (EQ_MP (@lem5396973) (@lem0)). Qed.
Lemma lem5396975 : term406.
Proof. exact (@lem5396964 (@lem5396974)). Qed.
Lemma lem5396977 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5396978 : term180 = term181.
Proof. exact (@lem5396977 term7 term7). Qed.
Lemma lem5396979 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396980 : term183 = term7.
Proof. exact (EQ_MP (@lem5396979) (@lem940073)). Qed.
Lemma lem5396981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396982 : term181 = term127.
Proof. exact (MK_COMB (@lem5396981) (@lem5396980)). Qed.
Lemma lem5396983 : term180 = term127.
Proof. exact (TRANS (@lem5396978) (@lem5396982)). Qed.
Lemma lem5396985 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5396986 : term197 = term202.
Proof. exact (@lem5396985 term7 term7). Qed.
Lemma lem5396987 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5396988 : term183 = term7.
Proof. exact (EQ_MP (@lem5396987) (@lem940073)). Qed.
Lemma lem5396989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5396990 : term181 = term127.
Proof. exact (MK_COMB (@lem5396989) (@lem5396988)). Qed.
Lemma lem5396991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5396992 : term202 = term171.
Proof. exact (MK_COMB (@lem5396991) (@lem5396990)). Qed.
Lemma lem5396993 : term197 = term171.
Proof. exact (TRANS (@lem5396986) (@lem5396992)). Qed.
Lemma lem5396994 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5396995 : term407 = term399.
Proof. exact (MK_COMB (@lem5396994) (@lem5396993)). Qed.
Lemma lem5396996 : term408 = term401.
Proof. exact (MK_COMB (@lem5396995) (@lem5396983)). Qed.
Lemma lem5396998 (m : nat) : (term409 m) = term118.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem5396999 : term401 = term118.
Proof. exact (@lem5396998 term7). Qed.
Lemma lem5397000 : term408 = term118.
Proof. exact (TRANS (@lem5396996) (@lem5396999)). Qed.
Lemma lem5397001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5397002 : term410 = term228.
Proof. exact (MK_COMB (@lem5397001) (@lem5397000)). Qed.
Lemma lem5397003 : term127 = term127.
Proof. exact (eq_refl term127). Qed.
Lemma lem5397004 : term411 = term230.
Proof. exact (MK_COMB (@lem5397002) (@lem5397003)). Qed.
Lemma lem5397006 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5397007 : term230 = term118.
Proof. exact (@lem5397006 term7). Qed.
Lemma lem5397008 : term411 = term118.
Proof. exact (TRANS (@lem5397004) (@lem5397007)). Qed.
Lemma lem5397010 (m : nat) (n : nat) : (term178 m n) = (term179 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem5397011 : term180 = term181.
Proof. exact (@lem5397010 term7 term7). Qed.
Lemma lem5397012 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397013 : term183 = term7.
Proof. exact (EQ_MP (@lem5397012) (@lem940073)). Qed.
Lemma lem5397014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397015 : term181 = term127.
Proof. exact (MK_COMB (@lem5397014) (@lem5397013)). Qed.
Lemma lem5397016 : term180 = term127.
Proof. exact (TRANS (@lem5397011) (@lem5397015)). Qed.
Lemma lem5397017 : term228 = term228.
Proof. exact (eq_refl term228). Qed.
Lemma lem5397018 : term232 = term230.
Proof. exact (MK_COMB (@lem5397017) (@lem5397016)). Qed.
Lemma lem5397020 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5397021 : term230 = term118.
Proof. exact (@lem5397020 term7). Qed.
Lemma lem5397022 : term232 = term118.
Proof. exact (TRANS (@lem5397018) (@lem5397021)). Qed.
Lemma lem5397023 : term118 = term232.
Proof. exact (SYM (@lem5397022)). Qed.
Lemma lem5397024 : term411 = term232.
Proof. exact (TRANS (@lem5397008) (@lem5397023)). Qed.
Lemma lem5397025 : term402 = term168.
Proof. exact (@lem5396975 (@lem5397024)). Qed.
Lemma lem5397026 : term401 = term168.
Proof. exact (TRANS (@lem5396941) (@lem5397025)). Qed.
Lemma lem5397028 (x : real) : (term187 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem5397029 : term168 = term118.
Proof. exact (@lem5397028 term118). Qed.
Lemma lem5397030 : term401 = term118.
Proof. exact (TRANS (@lem5397026) (@lem5397029)). Qed.
Lemma lem5397031 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem5397032 : term412 = term228.
Proof. exact (MK_COMB (@lem5397031) (@lem5397030)). Qed.
Lemma lem5397033 (_69874 : int) : (real_of_int _69874) = (real_of_int _69874).
Proof. exact (eq_refl (real_of_int _69874)). Qed.
Lemma lem5397034 (_69874 : int) : (term398 _69874) = (term413 _69874).
Proof. exact (MK_COMB (@lem5397032) (@lem5397033 _69874)). Qed.
Lemma lem5397035 (_69874 : int) : (term418 _69874) = (term413 _69874).
Proof. exact (TRANS (@lem5396932 _69874) (@lem5397034 _69874)). Qed.
Lemma lem5397036 (_69874 : int) : (term413 _69874) = term118.
Proof. exact (@lem1982719 (real_of_int _69874)). Qed.
Lemma lem5397037 (_69874 : int) : (term418 _69874) = term118.
Proof. exact (TRANS (@lem5397035 _69874) (@lem5397036 _69874)). Qed.
Lemma lem5397038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem5397039 (_69874 : int) : (term419 _69874) = term415.
Proof. exact (MK_COMB (@lem5397038) (@lem5397037 _69874)). Qed.
Lemma lem5397040 : term171 = term171.
Proof. exact (eq_refl term171). Qed.
Lemma lem5397041 (_69874 : int) : (term417 _69874) = term420.
Proof. exact (MK_COMB (@lem5397039 _69874) (@lem5397040)). Qed.
Lemma lem5397042 (_69874 : int) : (term519 _69874) = term420.
Proof. exact (TRANS (@lem5396931 _69874) (@lem5397041 _69874)). Qed.
Lemma lem5397043 : term420 = term171.
Proof. exact (@lem1982721 term171). Qed.
Lemma lem5397044 (_69874 : int) : (term519 _69874) = term171.
Proof. exact (TRANS (@lem5397042 _69874) (@lem5397043)). Qed.
Lemma lem5397045 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem5397046 (_69874 : int) : (term520 _69874) = term422.
Proof. exact (MK_COMB (@lem5397045) (@lem5397044 _69874)). Qed.
Lemma lem5397047 : term118 = term118.
Proof. exact (eq_refl term118). Qed.
Lemma lem5397048 (_69874 : int) : (term518 _69874) = term423.
Proof. exact (MK_COMB (@lem5397046 _69874) (@lem5397047)). Qed.
Lemma lem5397049 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : term423.
Proof. exact (EQ_MP (@lem5397048 _69874) (@lem5396930 _69873 _69874 h1)). Qed.
Lemma lem5397051 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem5397052 : term423 = term424.
Proof. exact (@lem5397051 term118 term171). Qed.
Lemma lem5397054 (x : nat) : (term169 x) = (term170 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem5397055 : term171 = term172.
Proof. exact (@lem5397054 term7). Qed.
Lemma lem5397057 (x : nat) : (real_of_num x) = (term167 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem5397058 : term118 = term168.
Proof. exact (@lem5397057 (NUMERAL 0)). Qed.
Lemma lem5397059 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5397060 : term120 = term425.
Proof. exact (MK_COMB (@lem5397059) (@lem5397058)). Qed.
Lemma lem5397061 : term424 = term426.
Proof. exact (MK_COMB (@lem5397060) (@lem5397055)). Qed.
Lemma lem5397062 : term427.
Proof. exact (@lem1980026 term118 term127 term171 term127). Qed.
Lemma lem5397064 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5397065 : term218 = term219.
Proof. exact (@lem5397064 (NUMERAL 0) term7). Qed.
Lemma lem5397066 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5397067 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5397068 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5397067 h1) (fun h1 : term219 = True => @lem5397066)). Qed.
Lemma lem5397069 : term219 = True.
Proof. exact (EQ_MP (@lem5397068) (@lem5397066)). Qed.
Lemma lem5397070 : term218 = True.
Proof. exact (TRANS (@lem5397065) (@lem5397069)). Qed.
Lemma lem5397071 : True = term218.
Proof. exact (SYM (@lem5397070)). Qed.
Lemma lem5397072 : term218.
Proof. exact (EQ_MP (@lem5397071) (@lem0)). Qed.
Lemma lem5397073 : term428.
Proof. exact (@lem5397062 (@lem5397072)). Qed.
Lemma lem5397075 (m : nat) (n : nat) : (term217 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem5397076 : term218 = term219.
Proof. exact (@lem5397075 (NUMERAL 0) term7). Qed.
Lemma lem5397077 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5397078 (h1 : term220 = (BIT1 0)) : term219 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem5397079 : (term220 = (BIT1 0)) = (term219 = True).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5397078 h1) (fun h1 : term219 = True => @lem5397077)). Qed.
Lemma lem5397080 : term219 = True.
Proof. exact (EQ_MP (@lem5397079) (@lem5397077)). Qed.
Lemma lem5397081 : term218 = True.
Proof. exact (TRANS (@lem5397076) (@lem5397080)). Qed.
Lemma lem5397082 : True = term218.
Proof. exact (SYM (@lem5397081)). Qed.
Lemma lem5397083 : term218.
Proof. exact (EQ_MP (@lem5397082) (@lem0)). Qed.
Lemma lem5397084 : term426 = term429.
Proof. exact (@lem5397073 (@lem5397083)). Qed.
Lemma lem5397086 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem5397087 : term197 = term202.
Proof. exact (@lem5397086 term7 term7). Qed.
Lemma lem5397088 : (term182 = (BIT1 0)) = (term183 = term7).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem5397089 : term183 = term7.
Proof. exact (EQ_MP (@lem5397088) (@lem940073)). Qed.
Lemma lem5397090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem5397091 : term181 = term127.
Proof. exact (MK_COMB (@lem5397090) (@lem5397089)). Qed.
Lemma lem5397092 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem5397093 : term202 = term171.
Proof. exact (MK_COMB (@lem5397092) (@lem5397091)). Qed.
Lemma lem5397094 : term197 = term171.
Proof. exact (TRANS (@lem5397087) (@lem5397093)). Qed.
Lemma lem5397096 (x : nat) : (term231 x) = term118.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem5397097 : term230 = term118.
Proof. exact (@lem5397096 term7). Qed.
Lemma lem5397098 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem5397099 : term430 = term120.
Proof. exact (MK_COMB (@lem5397098) (@lem5397097)). Qed.
Lemma lem5397100 : term429 = term424.
Proof. exact (MK_COMB (@lem5397099) (@lem5397094)). Qed.
Lemma lem5397102 (m : nat) (n : nat) : (term431 m n) = (term432 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem5397103 : term424 = term433.
Proof. exact (@lem5397102 (NUMERAL 0) term7). Qed.
Lemma lem5397104 : term220 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem5397105 (h1 : term220 = (BIT1 0)) : (term7 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem5397106 : (term220 = (BIT1 0)) = ((term7 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term220 = (BIT1 0) => @lem5397105 h1) (fun h1 : (term7 = (NUMERAL 0)) = False => @lem5397104)). Qed.
Lemma lem5397107 : (term7 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem5397106) (@lem5397104)). Qed.
Lemma lem5397108 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem5397109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5397110 : term434 = (and True).
Proof. exact (MK_COMB (@lem5397109) (@lem5397108)). Qed.
Lemma lem5397111 : term433 = (True /\ False).
Proof. exact (MK_COMB (@lem5397110) (@lem5397107)). Qed.
Lemma lem5397113 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem5397114 : term433 = False.
Proof. exact (TRANS (@lem5397111) (@lem5397113)). Qed.
Lemma lem5397115 : term424 = False.
Proof. exact (TRANS (@lem5397103) (@lem5397114)). Qed.
Lemma lem5397116 : term429 = False.
Proof. exact (TRANS (@lem5397100) (@lem5397115)). Qed.
Lemma lem5397117 : term426 = False.
Proof. exact (TRANS (@lem5397084) (@lem5397116)). Qed.
Lemma lem5397118 : term424 = False.
Proof. exact (TRANS (@lem5397061) (@lem5397117)). Qed.
Lemma lem5397119 : term423 = False.
Proof. exact (TRANS (@lem5397052) (@lem5397118)). Qed.
Lemma lem5397120 (_69873 : int) (_69874 : int) (h1 : term503 _69873 _69874) : False.
Proof. exact (EQ_MP (@lem5397119) (@lem5397049 _69873 _69874 h1)). Qed.
Lemma lem5397121 (_69873 : int) (_69874 : int) (h1 : term344 _69873 _69874) : False.
Proof. exact (or_elim (@lem5396155 _69873 _69874 h1) (fun h0 : term487 _69873 _69874 => @lem5396557 _69873 _69874 h0) (fun h0 : term503 _69873 _69874 => @lem5397120 _69873 _69874 h0)). Qed.
Lemma lem5397122 (_69873 : int) (_69874 : int) (h1 : term353 _69873 _69874) : False.
Proof. exact (or_elim (@lem5395017 _69873 _69874 h1) (fun h0 : term348 _69873 _69874 => @lem5396154 _69873 _69874 h0) (fun h0 : term344 _69873 _69874 => @lem5397121 _69873 _69874 h0)). Qed.
Lemma lem5397124 (_69873 : int) (_69874 : int) (h1 : term353 _69873 _69874) : term353 _69873 _69874.
Proof. exact (h1). Qed.
Lemma lem5397125 (_69873 : int) (_69874 : int) (h1 : term353 _69873 _69874) : (term353 _69873 _69874) = False.
Proof. exact (prop_ext (fun h2 : term353 _69873 _69874 => @lem5397122 _69873 _69874 h1) (fun h2 : False => @lem5397124 _69873 _69874 h1)). Qed.
Lemma lem5397126 (_69873 : int) (_69874 : int) (h1 : term353 _69873 _69874) : False.
Proof. exact (EQ_MP (@lem5397125 _69873 _69874 h1) (@lem5397124 _69873 _69874 h1)). Qed.
Lemma lem5397127 (_69874 : int) (_69873 : int) (h1 : term163 _69874 _69873) : term163 _69874 _69873.
Proof. exact (h1). Qed.
Lemma lem5397128 (_69874 : int) (_69873 : int) (h1 : term163 _69874 _69873) : term353 _69873 _69874.
Proof. exact (EQ_MP (@lem5394995 _69873 _69874) (@lem5397127 _69874 _69873 h1)). Qed.
Lemma lem5397129 (_69874 : int) (_69873 : int) (h1 : term163 _69874 _69873) : (term353 _69873 _69874) = False.
Proof. exact (prop_ext (fun h2 : term353 _69873 _69874 => @lem5397126 _69873 _69874 h2) (fun h2 : False => @lem5397128 _69874 _69873 h1)). Qed.
Lemma lem5397130 (_69874 : int) (_69873 : int) (h1 : term163 _69874 _69873) : False.
Proof. exact (EQ_MP (@lem5397129 _69874 _69873 h1) (@lem5397128 _69874 _69873 h1)). Qed.
Lemma lem5397131 (_69874 : int) (_69873 : int) : term521 _69874 _69873.
Proof. exact (fun h0 : term163 _69874 _69873 => @lem5397130 _69874 _69873 h0). Qed.
Lemma lem5397132 (_69874 : int) (_69873 : int) : term522 _69874 _69873.
Proof. exact (@lem1386578 (term523 _69874 _69873)). Qed.
Lemma lem5397135 (_69874 : int) (_69873 : int) : term523 _69874 _69873.
Proof. exact (@lem5397132 _69874 _69873 (@lem5397131 _69874 _69873)). Qed.
Lemma lem5397136 (_69873 : int) (_69874 : int) : (term161 _69874 _69873) = (term112 _69873 _69874).
Proof. exact (SYM (@lem5394034 _69874 _69873)). Qed.
Lemma lem5397137 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5397138 (_69873 : int) (_69874 : int) : (term523 _69874 _69873) = (term76 _69873 _69874).
Proof. exact (MK_COMB (@lem5397137) (@lem5397136 _69873 _69874)). Qed.
Lemma lem5397139 (_69873 : int) (_69874 : int) : term76 _69873 _69874.
Proof. exact (EQ_MP (@lem5397138 _69873 _69874) (@lem5397135 _69874 _69873)). Qed.
Lemma lem5397140 (_69873 : int) (_69874 : int) : term77 _69873 _69874.
Proof. exact (EQ_MP (@lem5393799 _69873 _69874) (@lem5397139 _69873 _69874)). Qed.
Lemma lem5397141 (d : nat) (n : nat) : term524 d n.
Proof. exact (@lem5397140 (int_of_num d) (int_of_num n)). Qed.
Lemma lem5397142 (d : nat) (n : nat) : term525 d n.
Proof. exact (@lem5397141 d n (@lem5393795 d)). Qed.
Lemma lem5397143 (d : nat) (n : nat) : term69 d n.
Proof. exact (@lem5397142 d n (@lem5393798 n)). Qed.
Lemma lem5397144 (n : nat) : term71 n.
Proof. exact (fun d : nat => @lem5397143 d n). Qed.
Lemma lem5397145 : term73.
Proof. exact (fun n : nat => @lem5397144 n). Qed.
Lemma lem5397146 : term73 = term13.
Proof. exact (SYM (@lem5393792)). Qed.
Lemma lem5397147 : term13.
Proof. exact (EQ_MP (@lem5397146) (@lem5397145)). Qed.
Lemma lem5397148 : term13 = (term13 = True).
Proof. exact (@lem7 term13). Qed.
Lemma lem5397149 : term13 = True.
Proof. exact (EQ_MP (@lem5397148) (@lem5397147)). Qed.
Lemma lem5397150 : True = term13.
Proof. exact (SYM (@lem5397149)). Qed.
Lemma lem5397151 : term13.
Proof. exact (EQ_MP (@lem5397150) (@lem0)). Qed.
Lemma lem5397152 : term12.
Proof. exact (EQ_MP (@lem5393606) (@lem5397151)). Qed.
