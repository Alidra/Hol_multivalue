Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_LT_EQ_LT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import LE_1_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16464_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Require Import thm89994_spec.
Lemma lem165616 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem165628 (p : Prop) : p = (term1 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem165629 : term2 = term3.
Proof. exact (@lem165628 term2). Qed.
Lemma lem165630 : term3 = term2.
Proof. exact (SYM (@lem165629)). Qed.
Lemma lem165631 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem165634 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem165635 : term6.
Proof. exact (fun h0 : term5 => @lem165634 h0). Qed.
Lemma lem165636 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem165637 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem165638 (h1 : term5) (h2 : term6) : term5.
Proof. exact (@lem165636 h2 (@lem165637 h1)). Qed.
Lemma lem165639 (h1 : term5) : term7.
Proof. exact (fun h0 : term6 => @lem165638 h1 h0). Qed.
Lemma lem165640 (h1 : term6) : term6.
Proof. exact (h1). Qed.
Lemma lem165641 (h1 : term5) (h2 : term6) : term5.
Proof. exact (@lem165639 h1 (@lem165640 h2)). Qed.
Lemma lem165642 (h1 : term6) : term6.
Proof. exact (fun h0 : term5 => @lem165641 h0 h1). Qed.
Lemma lem165643 : term8.
Proof. exact (fun h0 : term6 => @lem165642 h0). Qed.
Lemma lem165646 : term6.
Proof. exact (@lem165643 (@lem165635)). Qed.
Lemma lem165664 (t : Prop) : (t = False) = (~ t).
Proof. exact (proj2 (@lem16464 t)). Qed.
Lemma lem165665 (m : nat) : ((term9 m) = False) = (term10 m).
Proof. exact (@lem165664 (term9 m)). Qed.
Lemma lem165666 : term11 = term12.
Proof. exact (fun_ext (fun m : nat => @lem165665 m)). Qed.
Lemma lem165667 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165668 : term0 = term13.
Proof. exact (MK_COMB (@lem165667) (@lem165666)). Qed.
Lemma lem165673 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem165674 : term14 = term15.
Proof. exact (MK_COMB (@lem165673) (@lem165668)). Qed.
Lemma lem165724 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem165725 : term16 = term17.
Proof. exact (@lem165724 term18). Qed.
Lemma lem165738 : term19 = term19.
Proof. exact (eq_refl term19). Qed.
Lemma lem165739 : term20 = term21.
Proof. exact (MK_COMB (@lem165738) (@lem165725)). Qed.
Lemma lem165742 : term22 = term23.
Proof. exact (MK_COMB (@lem165674) (@lem165739)). Qed.
Lemma lem165745 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem165752 : term5 = term25.
Proof. exact (MK_COMB (@lem165745) (@lem165742)). Qed.
Lemma lem165763 (m : nat) (n : nat) : (term26 m n) = (term26 m n).
Proof. exact (eq_refl (term26 m n)). Qed.
Lemma lem165764 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem165763 m n)). Qed.
Lemma lem165765 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165766 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem165765) (@lem165764 m)). Qed.
Lemma lem165767 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem165766 m)). Qed.
Lemma lem165768 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165769 : term18 = term18.
Proof. exact (MK_COMB (@lem165768) (@lem165767)). Qed.
Lemma lem165770 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem165771 : term17 = term17.
Proof. exact (MK_COMB (@lem165770) (@lem165769)). Qed.
Lemma lem165778 (n : nat) : (term30 n) = (term30 n).
Proof. exact (eq_refl (term30 n)). Qed.
Lemma lem165779 : term31 = term31.
Proof. exact (fun_ext (fun n : nat => @lem165778 n)). Qed.
Lemma lem165780 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165781 : term32 = term32.
Proof. exact (MK_COMB (@lem165780) (@lem165779)). Qed.
Lemma lem165786 (n : nat) : (term33 n) = (term33 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem165787 : term34 = term34.
Proof. exact (fun_ext (fun n : nat => @lem165786 n)). Qed.
Lemma lem165788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165789 : term35 = term35.
Proof. exact (MK_COMB (@lem165788) (@lem165787)). Qed.
Lemma lem165790 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem165791 : term36 = term36.
Proof. exact (MK_COMB (@lem165790) (@lem165789)). Qed.
Lemma lem165792 : term37 = term37.
Proof. exact (MK_COMB (@lem165791) (@lem165781)). Qed.
Lemma lem165797 (n : nat) : (term38 n) = (term38 n).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem165798 : term39 = term39.
Proof. exact (fun_ext (fun n : nat => @lem165797 n)). Qed.
Lemma lem165799 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165800 : term40 = term40.
Proof. exact (MK_COMB (@lem165799) (@lem165798)). Qed.
Lemma lem165801 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem165802 : term41 = term41.
Proof. exact (MK_COMB (@lem165801) (@lem165800)). Qed.
Lemma lem165803 : term42 = term42.
Proof. exact (MK_COMB (@lem165802) (@lem165792)). Qed.
Lemma lem165810 (n : nat) : (term43 n) = (term43 n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem165811 : term44 = term44.
Proof. exact (fun_ext (fun n : nat => @lem165810 n)). Qed.
Lemma lem165812 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165813 : term45 = term45.
Proof. exact (MK_COMB (@lem165812) (@lem165811)). Qed.
Lemma lem165814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem165815 : term46 = term46.
Proof. exact (MK_COMB (@lem165814) (@lem165813)). Qed.
Lemma lem165816 : term47 = term47.
Proof. exact (MK_COMB (@lem165815) (@lem165803)). Qed.
Lemma lem165823 (n : nat) : (term48 n) = (term48 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem165824 : term49 = term49.
Proof. exact (fun_ext (fun n : nat => @lem165823 n)). Qed.
Lemma lem165825 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165826 : term50 = term50.
Proof. exact (MK_COMB (@lem165825) (@lem165824)). Qed.
Lemma lem165827 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem165828 : term51 = term51.
Proof. exact (MK_COMB (@lem165827) (@lem165826)). Qed.
Lemma lem165829 : term52 = term52.
Proof. exact (MK_COMB (@lem165828) (@lem165816)). Qed.
Lemma lem165836 (n : nat) : (term53 n) = (term53 n).
Proof. exact (eq_refl (term53 n)). Qed.
Lemma lem165837 : term54 = term54.
Proof. exact (fun_ext (fun n : nat => @lem165836 n)). Qed.
Lemma lem165838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165839 : term55 = term55.
Proof. exact (MK_COMB (@lem165838) (@lem165837)). Qed.
Lemma lem165840 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem165841 : term56 = term56.
Proof. exact (MK_COMB (@lem165840) (@lem165839)). Qed.
Lemma lem165842 : term57 = term57.
Proof. exact (MK_COMB (@lem165841) (@lem165829)). Qed.
Lemma lem165843 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem165844 : term19 = term19.
Proof. exact (MK_COMB (@lem165843) (@lem165842)). Qed.
Lemma lem165845 : term21 = term21.
Proof. exact (MK_COMB (@lem165844) (@lem165771)). Qed.
Lemma lem165848 (m : nat) : (term10 m) = (term10 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem165849 : term12 = term12.
Proof. exact (fun_ext (fun m : nat => @lem165848 m)). Qed.
Lemma lem165850 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165851 : term13 = term13.
Proof. exact (MK_COMB (@lem165850) (@lem165849)). Qed.
Lemma lem165852 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem165853 : term15 = term15.
Proof. exact (MK_COMB (@lem165852) (@lem165851)). Qed.
Lemma lem165854 : term23 = term23.
Proof. exact (MK_COMB (@lem165853) (@lem165845)). Qed.
Lemma lem165859 (m : nat) (n : nat) : ((term58 m n) = (term59 n)) = ((term58 m n) = (term59 n)).
Proof. exact (eq_refl ((term58 m n) = (term59 n))). Qed.
Lemma lem165860 (m : nat) : (term60 m) = (term60 m).
Proof. exact (fun_ext (fun n : nat => @lem165859 m n)). Qed.
Lemma lem165861 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165862 (m : nat) : (term61 m) = (term61 m).
Proof. exact (MK_COMB (@lem165861) (@lem165860 m)). Qed.
Lemma lem165863 : term62 = term62.
Proof. exact (fun_ext (fun m : nat => @lem165862 m)). Qed.
Lemma lem165864 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem165865 : term2 = term2.
Proof. exact (MK_COMB (@lem165864) (@lem165863)). Qed.
Lemma lem165866 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem165867 : term4 = term4.
Proof. exact (MK_COMB (@lem165866) (@lem165865)). Qed.
Lemma lem165868 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem165869 : term24 = term24.
Proof. exact (MK_COMB (@lem165868) (@lem165867)). Qed.
Lemma lem165870 : term25 = term25.
Proof. exact (MK_COMB (@lem165869) (@lem165854)). Qed.
Lemma lem165971 : term5 = term25.
Proof. exact (TRANS (@lem165752) (@lem165870)). Qed.
Lemma lem165972 : term25 = term5.
Proof. exact (SYM (@lem165971)). Qed.
Lemma lem165973 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem165974 (h1 : term13) : term13.
Proof. exact (h1). Qed.
Lemma lem165975 (h1 : term57) : term57.
Proof. exact (h1). Qed.
Lemma lem165976 (h1 : term18) : term18.
Proof. exact (h1). Qed.
Lemma lem165991 (m : nat) (n : nat) : (term63 m n) = (term64 m n).
Proof. exact (@lem17646 (term58 m n) (term59 n)). Qed.
Lemma lem165992 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem165993 (m : nat) : (term67 m) = (term68 m).
Proof. exact (@lem165992 (term60 m)). Qed.
Lemma lem165994 (m : nat) (n : nat) : (term69 m n) = ((term58 m n) = (term59 n)).
Proof. exact (eq_refl (term69 m n)). Qed.
Lemma lem165995 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem165996 (m : nat) (n : nat) : (term70 m n) = (term63 m n).
Proof. exact (MK_COMB (@lem165995) (@lem165994 m n)). Qed.
Lemma lem165997 (m : nat) (n : nat) : (term70 m n) = (term64 m n).
Proof. exact (TRANS (@lem165996 m n) (@lem165991 m n)). Qed.
Lemma lem165998 (m : nat) : (term71 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem165997 m n)). Qed.
Lemma lem165999 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166000 (m : nat) : (term68 m) = (term73 m).
Proof. exact (MK_COMB (@lem165999) (@lem165998 m)). Qed.
Lemma lem166001 (m : nat) : (term67 m) = (term73 m).
Proof. exact (TRANS (@lem165993 m) (@lem166000 m)). Qed.
Lemma lem166002 (P : nat -> Prop) : (term65 P) = (term66 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem166003 : term4 = term74.
Proof. exact (@lem166002 term62). Qed.
Lemma lem166004 (m : nat) : (term75 m) = (term61 m).
Proof. exact (eq_refl (term75 m)). Qed.
Lemma lem166005 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem166006 (m : nat) : (term76 m) = (term67 m).
Proof. exact (MK_COMB (@lem166005) (@lem166004 m)). Qed.
Lemma lem166007 (m : nat) : (term76 m) = (term73 m).
Proof. exact (TRANS (@lem166006 m) (@lem166001 m)). Qed.
Lemma lem166008 : term77 = term78.
Proof. exact (fun_ext (fun m : nat => @lem166007 m)). Qed.
Lemma lem166009 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166010 : term74 = term79.
Proof. exact (MK_COMB (@lem166009) (@lem166008)). Qed.
Lemma lem166011 : term4 = term79.
Proof. exact (TRANS (@lem166003) (@lem166010)). Qed.
Lemma lem166017 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem166018 (P : nat -> Prop) (Q : nat -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem166017 nat P Q). Qed.
Lemma lem166019 (m : nat) : (term84 m) = (term85 m).
Proof. exact (@lem166018 (term86 m) (term87 m)). Qed.
Lemma lem166020 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem166021 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166022 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem166021) (@lem166020 m n)). Qed.
Lemma lem166023 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem166024 (m : nat) (n : nat) : (term94 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem166022 m n) (@lem166023 m n)). Qed.
Lemma lem166025 (m : nat) : (term95 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem166024 m n)). Qed.
Lemma lem166026 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166027 (m : nat) : (term84 m) = (term73 m).
Proof. exact (MK_COMB (@lem166026) (@lem166025 m)). Qed.
Lemma lem166028 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem166029 (m : nat) : (term96 m) = (term97 m).
Proof. exact (MK_COMB (@lem166028) (@lem166027 m)). Qed.
Lemma lem166030 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem166031 (m : nat) : (term98 m) = (term86 m).
Proof. exact (fun_ext (fun n : nat => @lem166030 m n)). Qed.
Lemma lem166032 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166033 (m : nat) : (term99 m) = (term100 m).
Proof. exact (MK_COMB (@lem166032) (@lem166031 m)). Qed.
Lemma lem166034 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166035 (m : nat) : (term101 m) = (term102 m).
Proof. exact (MK_COMB (@lem166034) (@lem166033 m)). Qed.
Lemma lem166036 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem166037 (m : nat) : (term103 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem166036 m n)). Qed.
Lemma lem166038 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166039 (m : nat) : (term104 m) = (term105 m).
Proof. exact (MK_COMB (@lem166038) (@lem166037 m)). Qed.
Lemma lem166040 (m : nat) : (term85 m) = (term106 m).
Proof. exact (MK_COMB (@lem166035 m) (@lem166039 m)). Qed.
Lemma lem166041 (m : nat) : ((term84 m) = (term85 m)) = ((term73 m) = (term106 m)).
Proof. exact (MK_COMB (@lem166029 m) (@lem166040 m)). Qed.
Lemma lem166042 (m : nat) : (term73 m) = (term106 m).
Proof. exact (EQ_MP (@lem166041 m) (@lem166019 m)). Qed.
Lemma lem166139 : term78 = term107.
Proof. exact (fun_ext (fun m : nat => @lem166042 m)). Qed.
Lemma lem166140 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166141 : term79 = term108.
Proof. exact (MK_COMB (@lem166140) (@lem166139)). Qed.
Lemma lem166143 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term80 A P Q) = (term81 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem166144 (P : nat -> Prop) (Q : nat -> Prop) : (term82 P Q) = (term83 P Q).
Proof. exact (@lem166143 nat P Q). Qed.
Lemma lem166145 : term109 = term110.
Proof. exact (@lem166144 term111 term112). Qed.
Lemma lem166146 (m : nat) : (term113 m) = (term100 m).
Proof. exact (eq_refl (term113 m)). Qed.
Lemma lem166147 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166148 (m : nat) : (term114 m) = (term102 m).
Proof. exact (MK_COMB (@lem166147) (@lem166146 m)). Qed.
Lemma lem166149 (m : nat) : (term115 m) = (term105 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem166150 (m : nat) : (term116 m) = (term106 m).
Proof. exact (MK_COMB (@lem166148 m) (@lem166149 m)). Qed.
Lemma lem166151 : term117 = term107.
Proof. exact (fun_ext (fun m : nat => @lem166150 m)). Qed.
Lemma lem166152 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166153 : term109 = term108.
Proof. exact (MK_COMB (@lem166152) (@lem166151)). Qed.
Lemma lem166154 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem166155 : term118 = term119.
Proof. exact (MK_COMB (@lem166154) (@lem166153)). Qed.
Lemma lem166156 (m : nat) : (term113 m) = (term100 m).
Proof. exact (eq_refl (term113 m)). Qed.
Lemma lem166157 : term120 = term111.
Proof. exact (fun_ext (fun m : nat => @lem166156 m)). Qed.
Lemma lem166158 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166159 : term121 = term122.
Proof. exact (MK_COMB (@lem166158) (@lem166157)). Qed.
Lemma lem166160 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166161 : term123 = term124.
Proof. exact (MK_COMB (@lem166160) (@lem166159)). Qed.
Lemma lem166162 (m : nat) : (term115 m) = (term105 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem166163 : term125 = term112.
Proof. exact (fun_ext (fun m : nat => @lem166162 m)). Qed.
Lemma lem166164 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166165 : term126 = term127.
Proof. exact (MK_COMB (@lem166164) (@lem166163)). Qed.
Lemma lem166166 : term110 = term128.
Proof. exact (MK_COMB (@lem166161) (@lem166165)). Qed.
Lemma lem166167 : (term109 = term110) = (term108 = term128).
Proof. exact (MK_COMB (@lem166155) (@lem166166)). Qed.
Lemma lem166168 : term108 = term128.
Proof. exact (EQ_MP (@lem166167) (@lem166145)). Qed.
Lemma lem166273 : term79 = term128.
Proof. exact (TRANS (@lem166141) (@lem166168)). Qed.
Lemma lem166275 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem166276 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term82 P Q).
Proof. exact (@lem166275 nat P Q). Qed.
Lemma lem166277 : term110 = term109.
Proof. exact (@lem166276 term111 term112). Qed.
Lemma lem166278 (m : nat) : (term113 m) = (term100 m).
Proof. exact (eq_refl (term113 m)). Qed.
Lemma lem166279 : term120 = term111.
Proof. exact (fun_ext (fun m : nat => @lem166278 m)). Qed.
Lemma lem166280 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166281 : term121 = term122.
Proof. exact (MK_COMB (@lem166280) (@lem166279)). Qed.
Lemma lem166282 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166283 : term123 = term124.
Proof. exact (MK_COMB (@lem166282) (@lem166281)). Qed.
Lemma lem166284 (m : nat) : (term115 m) = (term105 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem166285 : term125 = term112.
Proof. exact (fun_ext (fun m : nat => @lem166284 m)). Qed.
Lemma lem166286 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166287 : term126 = term127.
Proof. exact (MK_COMB (@lem166286) (@lem166285)). Qed.
Lemma lem166288 : term110 = term128.
Proof. exact (MK_COMB (@lem166283) (@lem166287)). Qed.
Lemma lem166289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem166290 : term129 = term130.
Proof. exact (MK_COMB (@lem166289) (@lem166288)). Qed.
Lemma lem166291 (m : nat) : (term113 m) = (term100 m).
Proof. exact (eq_refl (term113 m)). Qed.
Lemma lem166292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166293 (m : nat) : (term114 m) = (term102 m).
Proof. exact (MK_COMB (@lem166292) (@lem166291 m)). Qed.
Lemma lem166294 (m : nat) : (term115 m) = (term105 m).
Proof. exact (eq_refl (term115 m)). Qed.
Lemma lem166295 (m : nat) : (term116 m) = (term106 m).
Proof. exact (MK_COMB (@lem166293 m) (@lem166294 m)). Qed.
Lemma lem166296 : term117 = term107.
Proof. exact (fun_ext (fun m : nat => @lem166295 m)). Qed.
Lemma lem166297 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166298 : term109 = term108.
Proof. exact (MK_COMB (@lem166297) (@lem166296)). Qed.
Lemma lem166299 : (term110 = term109) = (term128 = term108).
Proof. exact (MK_COMB (@lem166290) (@lem166298)). Qed.
Lemma lem166300 : term128 = term108.
Proof. exact (EQ_MP (@lem166299) (@lem166277)). Qed.
Lemma lem166302 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem166303 (P : nat -> Prop) (Q : nat -> Prop) : (term83 P Q) = (term82 P Q).
Proof. exact (@lem166302 nat P Q). Qed.
Lemma lem166304 (m : nat) : (term85 m) = (term84 m).
Proof. exact (@lem166303 (term86 m) (term87 m)). Qed.
Lemma lem166305 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem166306 (m : nat) : (term98 m) = (term86 m).
Proof. exact (fun_ext (fun n : nat => @lem166305 m n)). Qed.
Lemma lem166307 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166308 (m : nat) : (term99 m) = (term100 m).
Proof. exact (MK_COMB (@lem166307) (@lem166306 m)). Qed.
Lemma lem166309 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166310 (m : nat) : (term101 m) = (term102 m).
Proof. exact (MK_COMB (@lem166309) (@lem166308 m)). Qed.
Lemma lem166311 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem166312 (m : nat) : (term103 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem166311 m n)). Qed.
Lemma lem166313 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166314 (m : nat) : (term104 m) = (term105 m).
Proof. exact (MK_COMB (@lem166313) (@lem166312 m)). Qed.
Lemma lem166315 (m : nat) : (term85 m) = (term106 m).
Proof. exact (MK_COMB (@lem166310 m) (@lem166314 m)). Qed.
Lemma lem166316 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem166317 (m : nat) : (term131 m) = (term132 m).
Proof. exact (MK_COMB (@lem166316) (@lem166315 m)). Qed.
Lemma lem166318 (m : nat) (n : nat) : (term88 m n) = (term89 m n).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem166319 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166320 (m : nat) (n : nat) : (term90 m n) = (term91 m n).
Proof. exact (MK_COMB (@lem166319) (@lem166318 m n)). Qed.
Lemma lem166321 (m : nat) (n : nat) : (term92 m n) = (term93 m n).
Proof. exact (eq_refl (term92 m n)). Qed.
Lemma lem166322 (m : nat) (n : nat) : (term94 m n) = (term64 m n).
Proof. exact (MK_COMB (@lem166320 m n) (@lem166321 m n)). Qed.
Lemma lem166323 (m : nat) : (term95 m) = (term72 m).
Proof. exact (fun_ext (fun n : nat => @lem166322 m n)). Qed.
Lemma lem166324 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166325 (m : nat) : (term84 m) = (term73 m).
Proof. exact (MK_COMB (@lem166324) (@lem166323 m)). Qed.
Lemma lem166326 (m : nat) : ((term85 m) = (term84 m)) = ((term106 m) = (term73 m)).
Proof. exact (MK_COMB (@lem166317 m) (@lem166325 m)). Qed.
Lemma lem166327 (m : nat) : (term106 m) = (term73 m).
Proof. exact (EQ_MP (@lem166326 m) (@lem166304 m)). Qed.
Lemma lem166328 : term107 = term78.
Proof. exact (fun_ext (fun m : nat => @lem166327 m)). Qed.
Lemma lem166329 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem166330 : term108 = term79.
Proof. exact (MK_COMB (@lem166329) (@lem166328)). Qed.
Lemma lem166331 : term128 = term79.
Proof. exact (TRANS (@lem166300) (@lem166330)). Qed.
Lemma lem166332 : term79 = term79.
Proof. exact (TRANS (@lem166273) (@lem166331)). Qed.
Lemma lem166333 : term4 = term79.
Proof. exact (TRANS (@lem166011) (@lem166332)). Qed.
Lemma lem166334 (h1 : term4) : term79.
Proof. exact (EQ_MP (@lem166333) (@lem165973 h1)). Qed.
Lemma lem166335 (m : nat) : (term10 m) = (term10 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem166336 : term12 = term12.
Proof. exact (fun_ext (fun m : nat => @lem166335 m)). Qed.
Lemma lem166337 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166346 : term13 = term13.
Proof. exact (MK_COMB (@lem166337) (@lem166336)). Qed.
Lemma lem166347 (h1 : term13) : term13.
Proof. exact (EQ_MP (@lem166346) (@lem165974 h1)). Qed.
Lemma lem166350 (n : nat) : (term133 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem166351 (n : nat) : (term59 n) = (term59 n).
Proof. exact (eq_refl (term59 n)). Qed.
Lemma lem166352 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166353 (n : nat) : (term134 n) = (term135 n).
Proof. exact (MK_COMB (@lem166352) (@lem166350 n)). Qed.
Lemma lem166354 (n : nat) : (term136 n) = (term137 n).
Proof. exact (MK_COMB (@lem166353 n) (@lem166351 n)). Qed.
Lemma lem166355 (n : nat) : (term53 n) = (term136 n).
Proof. exact (@lem17265 (term138 n) (term59 n)). Qed.
Lemma lem166356 (n : nat) : (term53 n) = (term137 n).
Proof. exact (TRANS (@lem166355 n) (@lem166354 n)). Qed.
Lemma lem166357 : term54 = term139.
Proof. exact (fun_ext (fun n : nat => @lem166356 n)). Qed.
Lemma lem166358 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166359 : term55 = term140.
Proof. exact (MK_COMB (@lem166358) (@lem166357)). Qed.
Lemma lem166362 (n : nat) : (term133 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem166363 (n : nat) : (term141 n) = (term141 n).
Proof. exact (eq_refl (term141 n)). Qed.
Lemma lem166364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166365 (n : nat) : (term134 n) = (term135 n).
Proof. exact (MK_COMB (@lem166364) (@lem166362 n)). Qed.
Lemma lem166366 (n : nat) : (term142 n) = (term143 n).
Proof. exact (MK_COMB (@lem166365 n) (@lem166363 n)). Qed.
Lemma lem166367 (n : nat) : (term48 n) = (term142 n).
Proof. exact (@lem17265 (term138 n) (term141 n)). Qed.
Lemma lem166368 (n : nat) : (term48 n) = (term143 n).
Proof. exact (TRANS (@lem166367 n) (@lem166366 n)). Qed.
Lemma lem166369 : term49 = term144.
Proof. exact (fun_ext (fun n : nat => @lem166368 n)). Qed.
Lemma lem166370 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166371 : term50 = term145.
Proof. exact (MK_COMB (@lem166370) (@lem166369)). Qed.
Lemma lem166378 (n : nat) : (term43 n) = (term146 n).
Proof. exact (@lem17265 (term59 n) (term138 n)). Qed.
Lemma lem166379 : term44 = term147.
Proof. exact (fun_ext (fun n : nat => @lem166378 n)). Qed.
Lemma lem166380 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166381 : term45 = term148.
Proof. exact (MK_COMB (@lem166380) (@lem166379)). Qed.
Lemma lem166388 (n : nat) : (term38 n) = (term149 n).
Proof. exact (@lem17265 (term59 n) (term141 n)). Qed.
Lemma lem166389 : term39 = term150.
Proof. exact (fun_ext (fun n : nat => @lem166388 n)). Qed.
Lemma lem166390 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166391 : term40 = term151.
Proof. exact (MK_COMB (@lem166390) (@lem166389)). Qed.
Lemma lem166398 (n : nat) : (term33 n) = (term152 n).
Proof. exact (@lem17265 (term141 n) (term59 n)). Qed.
Lemma lem166399 : term34 = term153.
Proof. exact (fun_ext (fun n : nat => @lem166398 n)). Qed.
Lemma lem166400 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166401 : term35 = term154.
Proof. exact (MK_COMB (@lem166400) (@lem166399)). Qed.
Lemma lem166408 (n : nat) : (term30 n) = (term155 n).
Proof. exact (@lem17265 (term141 n) (term138 n)). Qed.
Lemma lem166409 : term31 = term156.
Proof. exact (fun_ext (fun n : nat => @lem166408 n)). Qed.
Lemma lem166410 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166411 : term32 = term157.
Proof. exact (MK_COMB (@lem166410) (@lem166409)). Qed.
Lemma lem166412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166413 : term36 = term158.
Proof. exact (MK_COMB (@lem166412) (@lem166401)). Qed.
Lemma lem166414 : term37 = term159.
Proof. exact (MK_COMB (@lem166413) (@lem166411)). Qed.
Lemma lem166415 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166416 : term41 = term160.
Proof. exact (MK_COMB (@lem166415) (@lem166391)). Qed.
Lemma lem166417 : term42 = term161.
Proof. exact (MK_COMB (@lem166416) (@lem166414)). Qed.
Lemma lem166418 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166419 : term46 = term162.
Proof. exact (MK_COMB (@lem166418) (@lem166381)). Qed.
Lemma lem166420 : term47 = term163.
Proof. exact (MK_COMB (@lem166419) (@lem166417)). Qed.
Lemma lem166421 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166422 : term51 = term164.
Proof. exact (MK_COMB (@lem166421) (@lem166371)). Qed.
Lemma lem166423 : term52 = term165.
Proof. exact (MK_COMB (@lem166422) (@lem166420)). Qed.
Lemma lem166424 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166425 : term56 = term166.
Proof. exact (MK_COMB (@lem166424) (@lem166359)). Qed.
Lemma lem166718 : term57 = term167.
Proof. exact (MK_COMB (@lem166425) (@lem166423)). Qed.
Lemma lem166719 (h1 : term57) : term167.
Proof. exact (EQ_MP (@lem166718) (@lem165975 h1)). Qed.
Lemma lem166722 (n : nat) : (term133 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem166727 (m : nat) (n : nat) : (term168 m n) = (term168 m n).
Proof. exact (eq_refl (term168 m n)). Qed.
Lemma lem166728 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem166729 (n : nat) : (term134 n) = (term135 n).
Proof. exact (MK_COMB (@lem166728) (@lem166722 n)). Qed.
Lemma lem166730 (m : nat) (n : nat) : (term169 m n) = (term170 m n).
Proof. exact (MK_COMB (@lem166729 n) (@lem166727 m n)). Qed.
Lemma lem166731 (m : nat) (n : nat) : (term26 m n) = (term169 m n).
Proof. exact (@lem17265 (term138 n) (term168 m n)). Qed.
Lemma lem166732 (m : nat) (n : nat) : (term26 m n) = (term170 m n).
Proof. exact (TRANS (@lem166731 m n) (@lem166730 m n)). Qed.
Lemma lem166733 (m : nat) : (term27 m) = (term171 m).
Proof. exact (fun_ext (fun n : nat => @lem166732 m n)). Qed.
Lemma lem166734 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166735 (m : nat) : (term28 m) = (term172 m).
Proof. exact (MK_COMB (@lem166734) (@lem166733 m)). Qed.
Lemma lem166736 : term29 = term173.
Proof. exact (fun_ext (fun m : nat => @lem166735 m)). Qed.
Lemma lem166737 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166794 : term18 = term174.
Proof. exact (MK_COMB (@lem166737) (@lem166736)). Qed.
Lemma lem166795 (h1 : term18) : term174.
Proof. exact (EQ_MP (@lem166794) (@lem165976 h1)). Qed.
Lemma lem166796 (m : nat) (h1 : term73 m) : term73 m.
Proof. exact (h1). Qed.
Lemma lem166806 (m : nat) : (term10 m) = (term10 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem166807 : term12 = term12.
Proof. exact (fun_ext (fun m : nat => @lem166806 m)). Qed.
Lemma lem166808 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166809 : term13 = term13.
Proof. exact (MK_COMB (@lem166808) (@lem166807)). Qed.
Lemma lem166810 (h1 : term13) : term13.
Proof. exact (EQ_MP (@lem166809) (@lem166347 h1)). Qed.
Lemma lem166833 (n : nat) : (term155 n) = (term155 n).
Proof. exact (eq_refl (term155 n)). Qed.
Lemma lem166834 : term156 = term156.
Proof. exact (fun_ext (fun n : nat => @lem166833 n)). Qed.
Lemma lem166835 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166836 : term157 = term157.
Proof. exact (MK_COMB (@lem166835) (@lem166834)). Qed.
Lemma lem166857 (n : nat) : (term152 n) = (term152 n).
Proof. exact (eq_refl (term152 n)). Qed.
Lemma lem166858 : term153 = term153.
Proof. exact (fun_ext (fun n : nat => @lem166857 n)). Qed.
Lemma lem166859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166860 : term154 = term154.
Proof. exact (MK_COMB (@lem166859) (@lem166858)). Qed.
Lemma lem166861 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166862 : term158 = term158.
Proof. exact (MK_COMB (@lem166861) (@lem166860)). Qed.
Lemma lem166863 : term159 = term159.
Proof. exact (MK_COMB (@lem166862) (@lem166836)). Qed.
Lemma lem166884 (n : nat) : (term149 n) = (term149 n).
Proof. exact (eq_refl (term149 n)). Qed.
Lemma lem166885 : term150 = term150.
Proof. exact (fun_ext (fun n : nat => @lem166884 n)). Qed.
Lemma lem166886 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166887 : term151 = term151.
Proof. exact (MK_COMB (@lem166886) (@lem166885)). Qed.
Lemma lem166888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166889 : term160 = term160.
Proof. exact (MK_COMB (@lem166888) (@lem166887)). Qed.
Lemma lem166890 : term161 = term161.
Proof. exact (MK_COMB (@lem166889) (@lem166863)). Qed.
Lemma lem166911 (n : nat) : (term146 n) = (term146 n).
Proof. exact (eq_refl (term146 n)). Qed.
Lemma lem166912 : term147 = term147.
Proof. exact (fun_ext (fun n : nat => @lem166911 n)). Qed.
Lemma lem166913 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166914 : term148 = term148.
Proof. exact (MK_COMB (@lem166913) (@lem166912)). Qed.
Lemma lem166915 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166916 : term162 = term162.
Proof. exact (MK_COMB (@lem166915) (@lem166914)). Qed.
Lemma lem166917 : term163 = term163.
Proof. exact (MK_COMB (@lem166916) (@lem166890)). Qed.
Lemma lem166936 (n : nat) : (term143 n) = (term143 n).
Proof. exact (eq_refl (term143 n)). Qed.
Lemma lem166937 : term144 = term144.
Proof. exact (fun_ext (fun n : nat => @lem166936 n)). Qed.
Lemma lem166938 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166939 : term145 = term145.
Proof. exact (MK_COMB (@lem166938) (@lem166937)). Qed.
Lemma lem166940 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166941 : term164 = term164.
Proof. exact (MK_COMB (@lem166940) (@lem166939)). Qed.
Lemma lem166942 : term165 = term165.
Proof. exact (MK_COMB (@lem166941) (@lem166917)). Qed.
Lemma lem166959 (n : nat) : (term137 n) = (term137 n).
Proof. exact (eq_refl (term137 n)). Qed.
Lemma lem166960 : term139 = term139.
Proof. exact (fun_ext (fun n : nat => @lem166959 n)). Qed.
Lemma lem166961 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem166962 : term140 = term140.
Proof. exact (MK_COMB (@lem166961) (@lem166960)). Qed.
Lemma lem166963 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem166964 : term166 = term166.
Proof. exact (MK_COMB (@lem166963) (@lem166962)). Qed.
Lemma lem166965 : term167 = term167.
Proof. exact (MK_COMB (@lem166964) (@lem166942)). Qed.
Lemma lem166966 (h1 : term57) : term167.
Proof. exact (EQ_MP (@lem166965) (@lem166719 h1)). Qed.
Lemma lem167009 (m : nat) (n : nat) : (term170 m n) = (term170 m n).
Proof. exact (eq_refl (term170 m n)). Qed.
Lemma lem167010 (m : nat) : (term171 m) = (term171 m).
Proof. exact (fun_ext (fun n : nat => @lem167009 m n)). Qed.
Lemma lem167011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem167012 (m : nat) : (term172 m) = (term172 m).
Proof. exact (MK_COMB (@lem167011) (@lem167010 m)). Qed.
Lemma lem167013 : term173 = term173.
Proof. exact (fun_ext (fun m : nat => @lem167012 m)). Qed.
Lemma lem167014 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem167015 : term174 = term174.
Proof. exact (MK_COMB (@lem167014) (@lem167013)). Qed.
Lemma lem167016 (h1 : term18) : term174.
Proof. exact (EQ_MP (@lem167015) (@lem166795 h1)). Qed.
Lemma lem167062 (m : nat) (n : nat) (h1 : term64 m n) : term64 m n.
Proof. exact (h1). Qed.
Lemma lem167063 (h1 : term57) : term165.
Proof. exact (proj2 (@lem166966 h1)). Qed.
Lemma lem167064 (h1 : term57) : term140.
Proof. exact (proj1 (@lem166966 h1)). Qed.
Lemma lem167065 (h1 : term57) : term163.
Proof. exact (proj2 (@lem167063 h1)). Qed.
Lemma lem167068 (h1 : term57) : term148.
Proof. exact (proj1 (@lem167065 h1)). Qed.
Lemma lem167073 (m : nat) (n : nat) (h1 : term89 m n) : term89 m n.
Proof. exact (h1). Qed.
Lemma lem167074 (m : nat) (n : nat) (h1 : term93 m n) : term93 m n.
Proof. exact (h1). Qed.
Lemma lem167080 (m : nat) : (term10 m) = (term10 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem167081 : term12 = term12.
Proof. exact (fun_ext (fun m : nat => @lem167080 m)). Qed.
Lemma lem167082 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem167084 : term13 = term13.
Proof. exact (MK_COMB (@lem167082) (@lem167081)). Qed.
Lemma lem167085 (h1 : term13) : term13.
Proof. exact (EQ_MP (@lem167084) (@lem166810 h1)). Qed.
Lemma lem167119 (n : nat) : (term137 n) = (term137 n).
Proof. exact (eq_refl (term137 n)). Qed.
Lemma lem167120 : term139 = term139.
Proof. exact (fun_ext (fun n : nat => @lem167119 n)). Qed.
Lemma lem167121 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem167123 : term140 = term140.
Proof. exact (MK_COMB (@lem167121) (@lem167120)). Qed.
Lemma lem167124 (h1 : term57) : term140.
Proof. exact (EQ_MP (@lem167123) (@lem167064 h1)). Qed.
Lemma lem167222 (m : nat) (n : nat) : (term170 m n) = (term175 m n).
Proof. exact (@lem19490 (m = (term176 m n)) (n = (NUMERAL 0)) (term58 m n)). Qed.
Lemma lem167223 (m : nat) : (term171 m) = (term177 m).
Proof. exact (fun_ext (fun n : nat => @lem167222 m n)). Qed.
Lemma lem167224 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem167225 (m : nat) : (term172 m) = (term178 m).
Proof. exact (MK_COMB (@lem167224) (@lem167223 m)). Qed.
Lemma lem167226 : term173 = term179.
Proof. exact (fun_ext (fun m : nat => @lem167225 m)). Qed.
Lemma lem167227 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem167229 : term174 = term180.
Proof. exact (MK_COMB (@lem167227) (@lem167226)). Qed.
Lemma lem167230 (h1 : term18) : term180.
Proof. exact (EQ_MP (@lem167229) (@lem167016 h1)). Qed.
Lemma lem167264 (n : nat) : (term146 n) = (term146 n).
Proof. exact (eq_refl (term146 n)). Qed.
Lemma lem167265 : term147 = term147.
Proof. exact (fun_ext (fun n : nat => @lem167264 n)). Qed.
Lemma lem167266 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem167268 : term148 = term148.
Proof. exact (MK_COMB (@lem167266) (@lem167265)). Qed.
Lemma lem167269 (h1 : term57) : term148.
Proof. exact (EQ_MP (@lem167268) (@lem167068 h1)). Qed.
Lemma lem167317 (_3416 : nat) (h1 : term13) : term181 _3416.
Proof. exact (@lem167085 h1 _3416). Qed.
Lemma lem167318 (_3416 : nat) : (term181 _3416) = (term10 _3416).
Proof. exact (eq_refl (term181 _3416)). Qed.
Lemma lem167326 (_3419 : nat) (h1 : term57) : term182 _3419.
Proof. exact (@lem167124 h1 _3419). Qed.
Lemma lem167327 (_3419 : nat) : (term182 _3419) = (term137 _3419).
Proof. exact (eq_refl (term182 _3419)). Qed.
Lemma lem167347 (_3426 : nat) (h1 : term18) : term183 _3426.
Proof. exact (@lem167230 h1 _3426). Qed.
Lemma lem167348 (_3426 : nat) : (term183 _3426) = (term178 _3426).
Proof. exact (eq_refl (term183 _3426)). Qed.
Lemma lem167349 (_3426 : nat) (h1 : term18) : term178 _3426.
Proof. exact (EQ_MP (@lem167348 _3426) (@lem167347 _3426 h1)). Qed.
Lemma lem167350 (_3426 : nat) (_3427 : nat) (h1 : term18) : term184 _3426 _3427.
Proof. exact (@lem167349 _3426 h1 _3427). Qed.
Lemma lem167351 (_3426 : nat) (_3427 : nat) : (term184 _3426 _3427) = (term175 _3426 _3427).
Proof. exact (eq_refl (term184 _3426 _3427)). Qed.
Lemma lem167352 (_3426 : nat) (_3427 : nat) (h1 : term18) : term175 _3426 _3427.
Proof. exact (EQ_MP (@lem167351 _3426 _3427) (@lem167350 _3426 _3427 h1)). Qed.
Lemma lem167359 (_3430 : nat) (h1 : term57) : term185 _3430.
Proof. exact (@lem167269 h1 _3430). Qed.
Lemma lem167360 (_3430 : nat) : (term185 _3430) = (term146 _3430).
Proof. exact (eq_refl (term185 _3430)). Qed.
Lemma lem167382 (_3419 : nat) (h1 : term57) : term137 _3419.
Proof. exact (EQ_MP (@lem167327 _3419) (@lem167326 _3419 h1)). Qed.
Lemma lem167416 (m : nat) (n : nat) (h1 : term89 m n) : term186 n.
Proof. exact (proj2 (@lem167073 m n h1)). Qed.
Lemma lem167448 (_3430 : nat) (h1 : term57) : term146 _3430.
Proof. exact (EQ_MP (@lem167360 _3430) (@lem167359 _3430 h1)). Qed.
Lemma lem167468 (m : nat) (n : nat) (h1 : term93 m n) : term187 m n.
Proof. exact (proj1 (@lem167074 m n h1)). Qed.
Lemma lem167482 (_3426 : nat) (_3427 : nat) (h1 : term18) : term188 _3426 _3427.
Proof. exact (proj2 (@lem167352 _3426 _3427 h1)). Qed.
Lemma lem167502 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem167503 (_3438 : nat) (_3440 : nat) (h1 : _3438 = _3440) : _3438 = _3440.
Proof. exact (h1). Qed.
Lemma lem167504 (_3439 : nat) (_3441 : nat) (h1 : _3439 = _3441) : _3439 = _3441.
Proof. exact (h1). Qed.
Lemma lem167505 (_3438 : nat) (_3440 : nat) (h1 : _3438 = _3440) : (Peano.lt _3438) = (Peano.lt _3440).
Proof. exact (MK_COMB (@lem167502) (@lem167503 _3438 _3440 h1)). Qed.
Lemma lem167506 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) (h1 : _3438 = _3440) (h2 : _3439 = _3441) : (Peano.lt _3438 _3439) = (Peano.lt _3440 _3441).
Proof. exact (MK_COMB (@lem167505 _3438 _3440 h1) (@lem167504 _3439 _3441 h2)). Qed.
Lemma lem167508 (b : Prop) (a : Prop) : term189 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem167509 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : term190 _3440 _3441 _3438 _3439.
Proof. exact (@lem167508 (Peano.lt _3440 _3441) (Peano.lt _3438 _3439)). Qed.
Lemma lem167510 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) (h1 : _3438 = _3440) (h2 : _3439 = _3441) : term191 _3440 _3441 _3438 _3439.
Proof. exact (@lem167509 _3440 _3441 _3438 _3439 (@lem167506 _3438 _3440 _3439 _3441 h1 h2)). Qed.
Lemma lem167511 (_3441 : nat) (_3439 : nat) (_3438 : nat) (_3440 : nat) (h1 : _3438 = _3440) : term192 _3440 _3441 _3438 _3439.
Proof. exact (fun h0 : _3439 = _3441 => @lem167510 _3438 _3440 _3439 _3441 h1 h0). Qed.
Lemma lem167513 (a : Prop) (b : Prop) : (a -> b) = (term193 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem167514 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term192 _3440 _3441 _3438 _3439) = (term194 _3440 _3441 _3438 _3439).
Proof. exact (@lem167513 (_3439 = _3441) (term191 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167515 (_3441 : nat) (_3439 : nat) (_3438 : nat) (_3440 : nat) (h1 : _3438 = _3440) : term194 _3440 _3441 _3438 _3439.
Proof. exact (EQ_MP (@lem167514 _3440 _3441 _3438 _3439) (@lem167511 _3441 _3439 _3438 _3440 h1)). Qed.
Lemma lem167516 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : term195 _3440 _3441 _3438 _3439.
Proof. exact (fun h0 : _3438 = _3440 => @lem167515 _3441 _3439 _3438 _3440 h0). Qed.
Lemma lem167518 (a : Prop) (b : Prop) : (a -> b) = (term193 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem167519 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term195 _3440 _3441 _3438 _3439) = (term196 _3440 _3441 _3438 _3439).
Proof. exact (@lem167518 (_3438 = _3440) (term194 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167520 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : term196 _3440 _3441 _3438 _3439.
Proof. exact (EQ_MP (@lem167519 _3440 _3441 _3438 _3439) (@lem167516 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167600 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem167601 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (@lem167600 (Nat.modulo m n)). Qed.
Lemma lem167602 (m : nat) (n : nat) : term197 m n.
Proof. exact (fun h0 : term198 m n => @lem167601 m n). Qed.
Lemma lem167604 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem167605 (m : nat) (n : nat) : (term197 m n) = ((Nat.modulo m n) = (Nat.modulo m n)).
Proof. exact (@lem167604 ((Nat.modulo m n) = (Nat.modulo m n))). Qed.
Lemma lem167606 (m : nat) (n : nat) : (Nat.modulo m n) = (Nat.modulo m n).
Proof. exact (EQ_MP (@lem167605 m n) (@lem167602 m n)). Qed.
Lemma lem167608 (_3416 : nat) (h1 : term13) : term10 _3416.
Proof. exact (EQ_MP (@lem167318 _3416) (@lem167317 _3416 h1)). Qed.
Lemma lem167609 (m : nat) (n : nat) (h1 : term13) : term200 m n.
Proof. exact (@lem167608 (Nat.modulo m n) h1). Qed.
Lemma lem167610 (m : nat) (n : nat) (h1 : term13) : term201 m n.
Proof. exact (fun h0 : term202 m n => @lem167609 m n h1). Qed.
Lemma lem167612 (p : Prop) : (term203 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem167613 (m : nat) (n : nat) : (term201 m n) = (term200 m n).
Proof. exact (@lem167612 (term202 m n)). Qed.
Lemma lem167614 (m : nat) (n : nat) (h1 : term13) : term200 m n.
Proof. exact (EQ_MP (@lem167613 m n) (@lem167610 m n h1)). Qed.
Lemma lem167616 (m : nat) (n : nat) (h1 : term89 m n) : term58 m n.
Proof. exact (proj1 (@lem167073 m n h1)). Qed.
Lemma lem167617 (m : nat) (n : nat) (h1 : term89 m n) : term204 m n.
Proof. exact (fun h0 : term187 m n => @lem167616 m n h1). Qed.
Lemma lem167619 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem167620 (m : nat) (n : nat) : (term204 m n) = (term58 m n).
Proof. exact (@lem167619 (term58 m n)). Qed.
Lemma lem167621 (m : nat) (n : nat) (h1 : term89 m n) : term58 m n.
Proof. exact (EQ_MP (@lem167620 m n) (@lem167617 m n h1)). Qed.
Lemma lem167639 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem167640 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term194 _3440 _3441 _3438 _3439) = (term206 _3440 _3441 _3438 _3439).
Proof. exact (@lem167639 (Peano.lt _3440 _3441) (term207 _3439 _3441) (term208 _3438 _3439)). Qed.
Lemma lem167654 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem167655 (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term209 _3441 _3438 _3439) = (term210 _3438 _3439 _3441).
Proof. exact (@lem167654 (term208 _3438 _3439) (term207 _3439 _3441)). Qed.
Lemma lem167663 (_3440 : nat) (_3441 : nat) : (term211 _3440 _3441) = (term211 _3440 _3441).
Proof. exact (eq_refl (term211 _3440 _3441)). Qed.
Lemma lem167664 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term206 _3440 _3441 _3438 _3439) = (term212 _3440 _3438 _3439 _3441).
Proof. exact (MK_COMB (@lem167663 _3440 _3441) (@lem167655 _3438 _3439 _3441)). Qed.
Lemma lem167675 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term194 _3440 _3441 _3438 _3439) = (term212 _3440 _3438 _3439 _3441).
Proof. exact (TRANS (@lem167640 _3440 _3441 _3438 _3439) (@lem167664 _3440 _3438 _3439 _3441)). Qed.
Lemma lem167676 (_3438 : nat) (_3440 : nat) : (term213 _3438 _3440) = (term213 _3438 _3440).
Proof. exact (eq_refl (term213 _3438 _3440)). Qed.
Lemma lem167677 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term196 _3440 _3441 _3438 _3439) = (term214 _3440 _3438 _3439 _3441).
Proof. exact (MK_COMB (@lem167676 _3438 _3440) (@lem167675 _3440 _3438 _3439 _3441)). Qed.
Lemma lem167681 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem167682 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term214 _3440 _3438 _3439 _3441) = (term215 _3440 _3438 _3439 _3441).
Proof. exact (@lem167681 (Peano.lt _3440 _3441) (term207 _3438 _3440) (term210 _3438 _3439 _3441)). Qed.
Lemma lem167696 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem167697 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term216 _3440 _3438 _3439 _3441) = (term217 _3438 _3440 _3439 _3441).
Proof. exact (@lem167696 (term208 _3438 _3439) (term207 _3438 _3440) (term207 _3439 _3441)). Qed.
Lemma lem167717 (_3440 : nat) (_3441 : nat) : (term211 _3440 _3441) = (term211 _3440 _3441).
Proof. exact (eq_refl (term211 _3440 _3441)). Qed.
Lemma lem167718 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term215 _3440 _3438 _3439 _3441) = (term218 _3438 _3440 _3439 _3441).
Proof. exact (MK_COMB (@lem167717 _3440 _3441) (@lem167697 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167729 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term214 _3440 _3438 _3439 _3441) = (term218 _3438 _3440 _3439 _3441).
Proof. exact (TRANS (@lem167682 _3440 _3438 _3439 _3441) (@lem167718 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167730 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term196 _3440 _3441 _3438 _3439) = (term218 _3438 _3440 _3439 _3441).
Proof. exact (TRANS (@lem167677 _3440 _3438 _3439 _3441) (@lem167729 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167731 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem167732 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term219 _3440 _3441 _3438 _3439) = (term220 _3438 _3440 _3439 _3441).
Proof. exact (MK_COMB (@lem167731) (@lem167730 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167736 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem167737 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term221 _3440 _3441 _3438 _3439) = (term196 _3440 _3441 _3438 _3439).
Proof. exact (@lem167736 (term207 _3438 _3440) (term207 _3439 _3441) (term191 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167753 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem167754 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term194 _3440 _3441 _3438 _3439) = (term206 _3440 _3441 _3438 _3439).
Proof. exact (@lem167753 (Peano.lt _3440 _3441) (term207 _3439 _3441) (term208 _3438 _3439)). Qed.
Lemma lem167768 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem167769 (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term209 _3441 _3438 _3439) = (term210 _3438 _3439 _3441).
Proof. exact (@lem167768 (term208 _3438 _3439) (term207 _3439 _3441)). Qed.
Lemma lem167777 (_3440 : nat) (_3441 : nat) : (term211 _3440 _3441) = (term211 _3440 _3441).
Proof. exact (eq_refl (term211 _3440 _3441)). Qed.
Lemma lem167778 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term206 _3440 _3441 _3438 _3439) = (term212 _3440 _3438 _3439 _3441).
Proof. exact (MK_COMB (@lem167777 _3440 _3441) (@lem167769 _3438 _3439 _3441)). Qed.
Lemma lem167789 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term194 _3440 _3441 _3438 _3439) = (term212 _3440 _3438 _3439 _3441).
Proof. exact (TRANS (@lem167754 _3440 _3441 _3438 _3439) (@lem167778 _3440 _3438 _3439 _3441)). Qed.
Lemma lem167790 (_3438 : nat) (_3440 : nat) : (term213 _3438 _3440) = (term213 _3438 _3440).
Proof. exact (eq_refl (term213 _3438 _3440)). Qed.
Lemma lem167791 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term196 _3440 _3441 _3438 _3439) = (term214 _3440 _3438 _3439 _3441).
Proof. exact (MK_COMB (@lem167790 _3438 _3440) (@lem167789 _3440 _3438 _3439 _3441)). Qed.
Lemma lem167795 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem167796 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term214 _3440 _3438 _3439 _3441) = (term215 _3440 _3438 _3439 _3441).
Proof. exact (@lem167795 (Peano.lt _3440 _3441) (term207 _3438 _3440) (term210 _3438 _3439 _3441)). Qed.
Lemma lem167810 (q : Prop) (p : Prop) (r : Prop) : (term205 p q r) = (term205 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem167811 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term216 _3440 _3438 _3439 _3441) = (term217 _3438 _3440 _3439 _3441).
Proof. exact (@lem167810 (term208 _3438 _3439) (term207 _3438 _3440) (term207 _3439 _3441)). Qed.
Lemma lem167831 (_3440 : nat) (_3441 : nat) : (term211 _3440 _3441) = (term211 _3440 _3441).
Proof. exact (eq_refl (term211 _3440 _3441)). Qed.
Lemma lem167832 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term215 _3440 _3438 _3439 _3441) = (term218 _3438 _3440 _3439 _3441).
Proof. exact (MK_COMB (@lem167831 _3440 _3441) (@lem167811 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167843 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term214 _3440 _3438 _3439 _3441) = (term218 _3438 _3440 _3439 _3441).
Proof. exact (TRANS (@lem167796 _3440 _3438 _3439 _3441) (@lem167832 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167844 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term196 _3440 _3441 _3438 _3439) = (term218 _3438 _3440 _3439 _3441).
Proof. exact (TRANS (@lem167791 _3440 _3438 _3439 _3441) (@lem167843 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167845 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : (term221 _3440 _3441 _3438 _3439) = (term218 _3438 _3440 _3439 _3441).
Proof. exact (TRANS (@lem167737 _3440 _3441 _3438 _3439) (@lem167844 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167846 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : ((term196 _3440 _3441 _3438 _3439) = (term221 _3440 _3441 _3438 _3439)) = ((term218 _3438 _3440 _3439 _3441) = (term218 _3438 _3440 _3439 _3441)).
Proof. exact (MK_COMB (@lem167732 _3438 _3440 _3439 _3441) (@lem167845 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167848 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem167849 (x : Prop) : (x = x) = True.
Proof. exact (@lem167848 Prop x). Qed.
Lemma lem167850 (_3438 : nat) (_3440 : nat) (_3439 : nat) (_3441 : nat) : ((term218 _3438 _3440 _3439 _3441) = (term218 _3438 _3440 _3439 _3441)) = True.
Proof. exact (@lem167849 (term218 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167851 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : ((term196 _3440 _3441 _3438 _3439) = (term221 _3440 _3441 _3438 _3439)) = True.
Proof. exact (TRANS (@lem167846 _3438 _3440 _3439 _3441) (@lem167850 _3438 _3440 _3439 _3441)). Qed.
Lemma lem167852 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : True = ((term196 _3440 _3441 _3438 _3439) = (term221 _3440 _3441 _3438 _3439)).
Proof. exact (SYM (@lem167851 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167853 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term196 _3440 _3441 _3438 _3439) = (term221 _3440 _3441 _3438 _3439).
Proof. exact (EQ_MP (@lem167852 _3440 _3441 _3438 _3439) (@lem0)). Qed.
Lemma lem167854 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : term221 _3440 _3441 _3438 _3439.
Proof. exact (EQ_MP (@lem167853 _3440 _3441 _3438 _3439) (@lem167520 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167856 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem167857 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term221 _3440 _3441 _3438 _3439) = (term223 _3440 _3438 _3439 _3441).
Proof. exact (@lem167856 (term224 _3440 _3441 _3438 _3439) (term207 _3439 _3441)). Qed.
Lemma lem167859 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem167860 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term227 _3440 _3441 _3438 _3439) = (term228 _3440 _3441 _3438 _3439).
Proof. exact (@lem167859 (term207 _3438 _3440) (term191 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167862 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem167863 (_3438 : nat) (_3440 : nat) : (term230 _3438 _3440) = (_3438 = _3440).
Proof. exact (@lem167862 (_3438 = _3440)). Qed.
Lemma lem167864 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem167865 (_3438 : nat) (_3440 : nat) : (term231 _3438 _3440) = (term232 _3438 _3440).
Proof. exact (MK_COMB (@lem167864) (@lem167863 _3438 _3440)). Qed.
Lemma lem167867 (a : Prop) (b : Prop) : (term225 a b) = (term226 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem167868 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term233 _3440 _3441 _3438 _3439) = (term234 _3440 _3441 _3438 _3439).
Proof. exact (@lem167867 (Peano.lt _3440 _3441) (term208 _3438 _3439)). Qed.
Lemma lem167870 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem167871 (_3438 : nat) (_3439 : nat) : (term235 _3438 _3439) = (Peano.lt _3438 _3439).
Proof. exact (@lem167870 (Peano.lt _3438 _3439)). Qed.
Lemma lem167872 (_3440 : nat) (_3441 : nat) : (term236 _3440 _3441) = (term236 _3440 _3441).
Proof. exact (eq_refl (term236 _3440 _3441)). Qed.
Lemma lem167873 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term234 _3440 _3441 _3438 _3439) = (term237 _3440 _3441 _3438 _3439).
Proof. exact (MK_COMB (@lem167872 _3440 _3441) (@lem167871 _3438 _3439)). Qed.
Lemma lem167874 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term233 _3440 _3441 _3438 _3439) = (term237 _3440 _3441 _3438 _3439).
Proof. exact (TRANS (@lem167868 _3440 _3441 _3438 _3439) (@lem167873 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167875 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term228 _3440 _3441 _3438 _3439) = (term238 _3440 _3441 _3438 _3439).
Proof. exact (MK_COMB (@lem167865 _3438 _3440) (@lem167874 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167876 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term227 _3440 _3441 _3438 _3439) = (term238 _3440 _3441 _3438 _3439).
Proof. exact (TRANS (@lem167860 _3440 _3441 _3438 _3439) (@lem167875 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167877 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem167878 (_3440 : nat) (_3441 : nat) (_3438 : nat) (_3439 : nat) : (term239 _3440 _3441 _3438 _3439) = (term240 _3440 _3441 _3438 _3439).
Proof. exact (MK_COMB (@lem167877) (@lem167876 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167879 (_3439 : nat) (_3441 : nat) : (term207 _3439 _3441) = (term207 _3439 _3441).
Proof. exact (eq_refl (term207 _3439 _3441)). Qed.
Lemma lem167880 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term223 _3440 _3438 _3439 _3441) = (term241 _3440 _3438 _3439 _3441).
Proof. exact (MK_COMB (@lem167878 _3440 _3441 _3438 _3439) (@lem167879 _3439 _3441)). Qed.
Lemma lem167881 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : (term221 _3440 _3441 _3438 _3439) = (term241 _3440 _3438 _3439 _3441).
Proof. exact (TRANS (@lem167857 _3440 _3438 _3439 _3441) (@lem167880 _3440 _3438 _3439 _3441)). Qed.
Lemma lem167883 (m : nat) (n : nat) (h1 : term13) (h2 : term89 m n) : term242 m n.
Proof. exact (conj (@lem167614 m n h1) (@lem167621 m n h2)). Qed.
Lemma lem167884 (m : nat) (n : nat) (h1 : term13) (h2 : term89 m n) : term243 m n.
Proof. exact (conj (@lem167606 m n) (@lem167883 m n h1 h2)). Qed.
Lemma lem167886 (_3440 : nat) (_3438 : nat) (_3439 : nat) (_3441 : nat) : term241 _3440 _3438 _3439 _3441.
Proof. exact (EQ_MP (@lem167881 _3440 _3438 _3439 _3441) (@lem167854 _3440 _3441 _3438 _3439)). Qed.
Lemma lem167887 (m : nat) (n : nat) : term244 m n.
Proof. exact (@lem167886 (Nat.modulo m n) (Nat.modulo m n) n (NUMERAL 0)). Qed.
Lemma lem167890 (m : nat) (n : nat) (h1 : term13) (h2 : term89 m n) : term138 n.
Proof. exact (@lem167887 m n (@lem167884 m n h1 h2)). Qed.
Lemma lem167891 (m : nat) (n : nat) (h1 : term13) (h2 : term89 m n) : term245 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem167890 m n h1 h2). Qed.
Lemma lem167893 (p : Prop) : (term203 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem167894 (n : nat) : (term245 n) = (term138 n).
Proof. exact (@lem167893 (n = (NUMERAL 0))). Qed.
Lemma lem167895 (m : nat) (n : nat) (h1 : term13) (h2 : term89 m n) : term138 n.
Proof. exact (EQ_MP (@lem167894 n) (@lem167891 m n h1 h2)). Qed.
Lemma lem167901 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem167902 (_3419 : nat) : (term137 _3419) = (term246 _3419).
Proof. exact (@lem167901 (term59 _3419) (_3419 = (NUMERAL 0))). Qed.
Lemma lem167910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem167911 (_3419 : nat) : (term247 _3419) = (term248 _3419).
Proof. exact (MK_COMB (@lem167910) (@lem167902 _3419)). Qed.
Lemma lem167919 (_3419 : nat) : (term246 _3419) = (term246 _3419).
Proof. exact (eq_refl (term246 _3419)). Qed.
Lemma lem167920 (_3419 : nat) : ((term137 _3419) = (term246 _3419)) = ((term246 _3419) = (term246 _3419)).
Proof. exact (MK_COMB (@lem167911 _3419) (@lem167919 _3419)). Qed.
Lemma lem167922 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem167923 (x : Prop) : (x = x) = True.
Proof. exact (@lem167922 Prop x). Qed.
Lemma lem167924 (_3419 : nat) : ((term246 _3419) = (term246 _3419)) = True.
Proof. exact (@lem167923 (term246 _3419)). Qed.
Lemma lem167925 (_3419 : nat) : ((term137 _3419) = (term246 _3419)) = True.
Proof. exact (TRANS (@lem167920 _3419) (@lem167924 _3419)). Qed.
Lemma lem167926 (_3419 : nat) : True = ((term137 _3419) = (term246 _3419)).
Proof. exact (SYM (@lem167925 _3419)). Qed.
Lemma lem167927 (_3419 : nat) : (term137 _3419) = (term246 _3419).
Proof. exact (EQ_MP (@lem167926 _3419) (@lem0)). Qed.
Lemma lem167928 (_3419 : nat) (h1 : term57) : term246 _3419.
Proof. exact (EQ_MP (@lem167927 _3419) (@lem167382 _3419 h1)). Qed.
Lemma lem167930 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem167933 (_3419 : nat) : (term246 _3419) = (term53 _3419).
Proof. exact (@lem167930 (_3419 = (NUMERAL 0)) (term59 _3419)). Qed.
Lemma lem167936 (_3419 : nat) (h1 : term57) : term53 _3419.
Proof. exact (EQ_MP (@lem167933 _3419) (@lem167928 _3419 h1)). Qed.
Lemma lem167937 (n : nat) (h1 : term57) : term53 n.
Proof. exact (@lem167936 n h1). Qed.
Lemma lem167940 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : term59 n.
Proof. exact (@lem167937 n h2 (@lem167895 m n h1 h3)). Qed.
Lemma lem167941 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : term249 n.
Proof. exact (fun h0 : term186 n => @lem167940 m n h1 h2 h3). Qed.
Lemma lem167943 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem167944 (n : nat) : (term249 n) = (term59 n).
Proof. exact (@lem167943 (term59 n)). Qed.
Lemma lem167945 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : term59 n.
Proof. exact (EQ_MP (@lem167944 n) (@lem167941 m n h1 h2 h3)). Qed.
Lemma lem167948 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem167950 (n : nat) : (term186 n) = (term250 n).
Proof. exact (@lem167948 (term59 n)). Qed.
Lemma lem167953 (m : nat) (n : nat) (h1 : term89 m n) : term250 n.
Proof. exact (EQ_MP (@lem167950 n) (@lem167416 m n h1)). Qed.
Lemma lem167956 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : False.
Proof. exact (@lem167953 m n h3 (@lem167945 m n h1 h2 h3)). Qed.
Lemma lem167957 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : term251.
Proof. exact (fun h0 : ~ False => @lem167956 m n h1 h2 h3). Qed.
Lemma lem167959 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem167960 : term251 = False.
Proof. exact (@lem167959 False). Qed.
Lemma lem167961 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : False.
Proof. exact (EQ_MP (@lem167960) (@lem167957 m n h1 h2 h3)). Qed.
Lemma lem168079 (m : nat) (n : nat) (h1 : term93 m n) : term59 n.
Proof. exact (proj2 (@lem167074 m n h1)). Qed.
Lemma lem168080 (m : nat) (n : nat) (h1 : term93 m n) : term249 n.
Proof. exact (fun h0 : term186 n => @lem168079 m n h1). Qed.
Lemma lem168082 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem168083 (n : nat) : (term249 n) = (term59 n).
Proof. exact (@lem168082 (term59 n)). Qed.
Lemma lem168084 (m : nat) (n : nat) (h1 : term93 m n) : term59 n.
Proof. exact (EQ_MP (@lem168083 n) (@lem168080 m n h1)). Qed.
Lemma lem168097 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem168098 (_3430 : nat) : (term252 _3430) = (term146 _3430).
Proof. exact (@lem168097 (term186 _3430) (term138 _3430)). Qed.
Lemma lem168106 (_3430 : nat) : (term253 _3430) = (term253 _3430).
Proof. exact (eq_refl (term253 _3430)). Qed.
Lemma lem168107 (_3430 : nat) : ((term146 _3430) = (term252 _3430)) = ((term146 _3430) = (term146 _3430)).
Proof. exact (MK_COMB (@lem168106 _3430) (@lem168098 _3430)). Qed.
Lemma lem168109 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem168110 (x : Prop) : (x = x) = True.
Proof. exact (@lem168109 Prop x). Qed.
Lemma lem168111 (_3430 : nat) : ((term146 _3430) = (term146 _3430)) = True.
Proof. exact (@lem168110 (term146 _3430)). Qed.
Lemma lem168112 (_3430 : nat) : ((term146 _3430) = (term252 _3430)) = True.
Proof. exact (TRANS (@lem168107 _3430) (@lem168111 _3430)). Qed.
Lemma lem168113 (_3430 : nat) : True = ((term146 _3430) = (term252 _3430)).
Proof. exact (SYM (@lem168112 _3430)). Qed.
Lemma lem168114 (_3430 : nat) : (term146 _3430) = (term252 _3430).
Proof. exact (EQ_MP (@lem168113 _3430) (@lem0)). Qed.
Lemma lem168115 (_3430 : nat) (h1 : term57) : term252 _3430.
Proof. exact (EQ_MP (@lem168114 _3430) (@lem167448 _3430 h1)). Qed.
Lemma lem168117 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem168118 (_3430 : nat) : (term252 _3430) = (term254 _3430).
Proof. exact (@lem168117 (term186 _3430) (term138 _3430)). Qed.
Lemma lem168120 (a : Prop) : (term229 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem168121 (_3430 : nat) : (term255 _3430) = (term59 _3430).
Proof. exact (@lem168120 (term59 _3430)). Qed.
Lemma lem168122 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem168123 (_3430 : nat) : (term256 _3430) = (term257 _3430).
Proof. exact (MK_COMB (@lem168122) (@lem168121 _3430)). Qed.
Lemma lem168124 (_3430 : nat) : (term138 _3430) = (term138 _3430).
Proof. exact (eq_refl (term138 _3430)). Qed.
Lemma lem168125 (_3430 : nat) : (term254 _3430) = (term43 _3430).
Proof. exact (MK_COMB (@lem168123 _3430) (@lem168124 _3430)). Qed.
Lemma lem168126 (_3430 : nat) : (term252 _3430) = (term43 _3430).
Proof. exact (TRANS (@lem168118 _3430) (@lem168125 _3430)). Qed.
Lemma lem168129 (_3430 : nat) (h1 : term57) : term43 _3430.
Proof. exact (EQ_MP (@lem168126 _3430) (@lem168115 _3430 h1)). Qed.
Lemma lem168130 (n : nat) (h1 : term57) : term43 n.
Proof. exact (@lem168129 n h1). Qed.
Lemma lem168133 (m : nat) (n : nat) (h1 : term57) (h2 : term93 m n) : term138 n.
Proof. exact (@lem168130 n h1 (@lem168084 m n h2)). Qed.
Lemma lem168134 (m : nat) (n : nat) (h1 : term57) (h2 : term93 m n) : term245 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem168133 m n h1 h2). Qed.
Lemma lem168136 (p : Prop) : (term203 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem168137 (n : nat) : (term245 n) = (term138 n).
Proof. exact (@lem168136 (n = (NUMERAL 0))). Qed.
Lemma lem168138 (m : nat) (n : nat) (h1 : term57) (h2 : term93 m n) : term138 n.
Proof. exact (EQ_MP (@lem168137 n) (@lem168134 m n h1 h2)). Qed.
Lemma lem168144 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem168145 (_3426 : nat) (_3427 : nat) : (term188 _3426 _3427) = (term258 _3426 _3427).
Proof. exact (@lem168144 (term58 _3426 _3427) (_3427 = (NUMERAL 0))). Qed.
Lemma lem168153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem168154 (_3426 : nat) (_3427 : nat) : (term259 _3426 _3427) = (term260 _3426 _3427).
Proof. exact (MK_COMB (@lem168153) (@lem168145 _3426 _3427)). Qed.
Lemma lem168162 (_3426 : nat) (_3427 : nat) : (term258 _3426 _3427) = (term258 _3426 _3427).
Proof. exact (eq_refl (term258 _3426 _3427)). Qed.
Lemma lem168163 (_3426 : nat) (_3427 : nat) : ((term188 _3426 _3427) = (term258 _3426 _3427)) = ((term258 _3426 _3427) = (term258 _3426 _3427)).
Proof. exact (MK_COMB (@lem168154 _3426 _3427) (@lem168162 _3426 _3427)). Qed.
Lemma lem168165 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem168166 (x : Prop) : (x = x) = True.
Proof. exact (@lem168165 Prop x). Qed.
Lemma lem168167 (_3426 : nat) (_3427 : nat) : ((term258 _3426 _3427) = (term258 _3426 _3427)) = True.
Proof. exact (@lem168166 (term258 _3426 _3427)). Qed.
Lemma lem168168 (_3426 : nat) (_3427 : nat) : ((term188 _3426 _3427) = (term258 _3426 _3427)) = True.
Proof. exact (TRANS (@lem168163 _3426 _3427) (@lem168167 _3426 _3427)). Qed.
Lemma lem168169 (_3426 : nat) (_3427 : nat) : True = ((term188 _3426 _3427) = (term258 _3426 _3427)).
Proof. exact (SYM (@lem168168 _3426 _3427)). Qed.
Lemma lem168170 (_3426 : nat) (_3427 : nat) : (term188 _3426 _3427) = (term258 _3426 _3427).
Proof. exact (EQ_MP (@lem168169 _3426 _3427) (@lem0)). Qed.
Lemma lem168171 (_3426 : nat) (_3427 : nat) (h1 : term18) : term258 _3426 _3427.
Proof. exact (EQ_MP (@lem168170 _3426 _3427) (@lem167482 _3426 _3427 h1)). Qed.
Lemma lem168173 (b : Prop) (a : Prop) : (a \/ b) = (term222 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem168176 (_3426 : nat) (_3427 : nat) : (term258 _3426 _3427) = (term261 _3426 _3427).
Proof. exact (@lem168173 (_3427 = (NUMERAL 0)) (term58 _3426 _3427)). Qed.
Lemma lem168179 (_3426 : nat) (_3427 : nat) (h1 : term18) : term261 _3426 _3427.
Proof. exact (EQ_MP (@lem168176 _3426 _3427) (@lem168171 _3426 _3427 h1)). Qed.
Lemma lem168180 (_3426 : nat) (n : nat) (h1 : term18) : term261 _3426 n.
Proof. exact (@lem168179 _3426 n h1). Qed.
Lemma lem168183 (_3426 : nat) (m : nat) (n : nat) (h1 : term18) (h2 : term57) (h3 : term93 m n) : term58 _3426 n.
Proof. exact (@lem168180 _3426 n h1 (@lem168138 m n h2 h3)). Qed.
Lemma lem168184 (m : nat) (n : nat) (h1 : term18) (h2 : term57) (h3 : term93 m n) : term58 m n.
Proof. exact (@lem168183 m m n h1 h2 h3). Qed.
Lemma lem168185 (m : nat) (n : nat) (h1 : term18) (h2 : term57) (h3 : term93 m n) : term204 m n.
Proof. exact (fun h0 : term187 m n => @lem168184 m n h1 h2 h3). Qed.
Lemma lem168187 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem168188 (m : nat) (n : nat) : (term204 m n) = (term58 m n).
Proof. exact (@lem168187 (term58 m n)). Qed.
Lemma lem168189 (m : nat) (n : nat) (h1 : term18) (h2 : term57) (h3 : term93 m n) : term58 m n.
Proof. exact (EQ_MP (@lem168188 m n) (@lem168185 m n h1 h2 h3)). Qed.
Lemma lem168192 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem168194 (m : nat) (n : nat) : (term187 m n) = (term262 m n).
Proof. exact (@lem168192 (term58 m n)). Qed.
Lemma lem168197 (m : nat) (n : nat) (h1 : term93 m n) : term262 m n.
Proof. exact (EQ_MP (@lem168194 m n) (@lem167468 m n h1)). Qed.
Lemma lem168200 (m : nat) (n : nat) (h1 : term18) (h2 : term57) (h3 : term93 m n) : False.
Proof. exact (@lem168197 m n h3 (@lem168189 m n h1 h2 h3)). Qed.
Lemma lem168201 (m : nat) (n : nat) (h1 : term18) (h2 : term57) (h3 : term93 m n) : term251.
Proof. exact (fun h0 : ~ False => @lem168200 m n h1 h2 h3). Qed.
Lemma lem168203 (p : Prop) : (term199 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem168204 : term251 = False.
Proof. exact (@lem168203 False). Qed.
Lemma lem168205 (m : nat) (n : nat) (h1 : term18) (h2 : term57) (h3 : term93 m n) : False.
Proof. exact (EQ_MP (@lem168204) (@lem168201 m n h1 h2 h3)). Qed.
Lemma lem168206 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : term13 = False.
Proof. exact (prop_ext (fun h4 : term13 => @lem167961 m n h1 h2 h3) (fun h4 : False => @lem167085 h1)). Qed.
Lemma lem168207 (m : nat) (n : nat) (h1 : term13) (h2 : term57) (h3 : term89 m n) : False.
Proof. exact (EQ_MP (@lem168206 m n h1 h2 h3) (@lem167085 h1)). Qed.
Lemma lem168208 (m : nat) (n : nat) (h1 : term18) (h2 : term13) (h3 : term57) (h4 : term64 m n) : False.
Proof. exact (or_elim (@lem167062 m n h4) (fun h0 : term89 m n => @lem168207 m n h2 h3 h0) (fun h0 : term93 m n => @lem168205 m n h1 h3 h0)). Qed.
Lemma lem168209 (m : nat) (n : nat) (h1 : term18) (h2 : term13) (h3 : term57) (h4 : term64 m n) : (term64 m n) = False.
Proof. exact (prop_ext (fun h5 : term64 m n => @lem168208 m n h1 h2 h3 h4) (fun h5 : False => @lem167062 m n h4)). Qed.
Lemma lem168210 (m : nat) (n : nat) (h1 : term18) (h2 : term13) (h3 : term57) (h4 : term64 m n) : False.
Proof. exact (EQ_MP (@lem168209 m n h1 h2 h3 h4) (@lem167062 m n h4)). Qed.
Lemma lem168211 (m : nat) (n : nat) (h1 : term18) (h2 : term13) (h3 : term57) (h4 : term64 m n) : term13 = False.
Proof. exact (prop_ext (fun h5 : term13 => @lem168210 m n h1 h2 h3 h4) (fun h5 : False => @lem166810 h2)). Qed.
Lemma lem168212 (m : nat) (n : nat) (h1 : term18) (h2 : term13) (h3 : term57) (h4 : term64 m n) : False.
Proof. exact (EQ_MP (@lem168211 m n h1 h2 h3 h4) (@lem166810 h2)). Qed.
Lemma lem168213 (m : nat) (h1 : term18) (h2 : term13) (h3 : term73 m) (h4 : term57) : False.
Proof. exact (ex_elim (@lem166796 m h3) (fun n : nat => fun h0 : term72 m n => @lem168212 m n h1 h2 h4 h0)). Qed.
Lemma lem168214 (h1 : term18) (h2 : term13) (h3 : term4) (h4 : term57) : False.
Proof. exact (ex_elim (@lem166334 h3) (fun m : nat => fun h0 : term78 m => @lem168213 m h1 h2 h0 h4)). Qed.
Lemma lem168215 (h1 : term18) (h2 : term13) (h3 : term4) (h4 : term57) : term13 = False.
Proof. exact (prop_ext (fun h5 : term13 => @lem168214 h1 h2 h3 h4) (fun h5 : False => @lem166347 h2)). Qed.
Lemma lem168216 (h1 : term18) (h2 : term13) (h3 : term4) (h4 : term57) : False.
Proof. exact (EQ_MP (@lem168215 h1 h2 h3 h4) (@lem166347 h2)). Qed.
Lemma lem168217 (h1 : term13) (h2 : term4) (h3 : term57) : term16.
Proof. exact (fun h0 : term18 => @lem168216 h0 h1 h2 h3). Qed.
Lemma lem168218 : term16 = term17.
Proof. exact (@lem69 term18). Qed.
Lemma lem168219 (h1 : term13) (h2 : term4) (h3 : term57) : term17.
Proof. exact (EQ_MP (@lem168218) (@lem168217 h1 h2 h3)). Qed.
Lemma lem168220 (h1 : term13) (h2 : term4) : term21.
Proof. exact (fun h0 : term57 => @lem168219 h1 h2 h0). Qed.
Lemma lem168221 (h1 : term4) : term23.
Proof. exact (fun h0 : term13 => @lem168220 h0 h1). Qed.
Lemma lem168222 : term25.
Proof. exact (fun h0 : term4 => @lem168221 h0). Qed.
Lemma lem168223 : term5.
Proof. exact (EQ_MP (@lem165972) (@lem168222)). Qed.
Lemma lem168225 : term5.
Proof. exact (@lem165646 (@lem168223)). Qed.
Lemma lem168226 (h1 : term4) : term22.
Proof. exact (@lem168225 (@lem165631 h1)). Qed.
Lemma lem168227 (h1 : term4) : term20.
Proof. exact (@lem168226 h1 (@lem165616)). Qed.
Lemma lem168228 (h1 : term4) : term16.
Proof. exact (@lem168227 h1 (@lem99082)). Qed.
Lemma lem168229 (h1 : term4) : False.
Proof. exact (@lem168228 h1 (@lem157261)). Qed.
Lemma lem168230 (h1 : term4) : term4 = False.
Proof. exact (prop_ext (fun h2 : term4 => @lem168229 h1) (fun h2 : False => @lem165631 h1)). Qed.
Lemma lem168231 (h1 : term4) : False.
Proof. exact (EQ_MP (@lem168230 h1) (@lem165631 h1)). Qed.
Lemma lem168232 : term3.
Proof. exact (fun h0 : term4 => @lem168231 h0). Qed.
Lemma lem168233 : term2.
Proof. exact (EQ_MP (@lem165630) (@lem168232)). Qed.
