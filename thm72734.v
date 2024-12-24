Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm72734_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import NUM_REP_RULES_spec.
Require Import SUC_DEF_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17265_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
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
Require Import thm21385_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm70827_spec.
Require Import thm71260_spec.
Require Import thm71261_spec.
Require Import thm71400_spec.
Require Import thm71414_spec.
Lemma lem71604 : term0.
Proof. exact (fun a : nat => @lem71260 a). Qed.
Lemma lem71605 : term1.
Proof. exact (fun r : ind => @lem71261 r). Qed.
Lemma lem71606 (n : nat) : term2 n.
Proof. exact (@lem71593 n). Qed.
Lemma lem71607 (n : nat) : (term2 n) = ((S n) = (term3 n)).
Proof. exact (eq_refl (term2 n)). Qed.
Lemma lem71616 (n : nat) : (S n) = (term3 n).
Proof. exact (EQ_MP (@lem71607 n) (@lem71606 n)). Qed.
Lemma lem71617 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem71618 (n : nat) : (term4 n) = (term5 n).
Proof. exact (MK_COMB (@lem71617) (@lem71616 n)). Qed.
Lemma lem71620 : 0 = (mk_num IND_0).
Proof. exact (TRANS (@lem71400) (@lem71414)). Qed.
Lemma lem71621 (n : nat) : ((S n) = 0) = ((term3 n) = (mk_num IND_0)).
Proof. exact (MK_COMB (@lem71618 n) (@lem71620)). Qed.
Lemma lem71624 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem71625 (n : nat) : (term6 n) = (term7 n).
Proof. exact (MK_COMB (@lem71624) (@lem71621 n)). Qed.
Lemma lem71626 : term8 = term9.
Proof. exact (fun_ext (fun n : nat => @lem71625 n)). Qed.
Lemma lem71627 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem71628 : term10 = term11.
Proof. exact (MK_COMB (@lem71627) (@lem71626)). Qed.
Lemma lem71633 : term11 = term10.
Proof. exact (SYM (@lem71628)). Qed.
Lemma lem71635 (p : Prop) : p = (term12 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem71636 : term11 = term13.
Proof. exact (@lem71635 term11). Qed.
Lemma lem71637 : term13 = term11.
Proof. exact (SYM (@lem71636)). Qed.
Lemma lem71638 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem71641 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem71642 : term16.
Proof. exact (fun h0 : term15 => @lem71641 h0). Qed.
Lemma lem71643 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem71644 (h1 : term15) : term15.
Proof. exact (h1). Qed.
Lemma lem71645 (h1 : term15) (h2 : term16) : term15.
Proof. exact (@lem71643 h2 (@lem71644 h1)). Qed.
Lemma lem71646 (h1 : term15) : term17.
Proof. exact (fun h0 : term16 => @lem71645 h1 h0). Qed.
Lemma lem71647 (h1 : term16) : term16.
Proof. exact (h1). Qed.
Lemma lem71648 (h1 : term15) (h2 : term16) : term15.
Proof. exact (@lem71646 h1 (@lem71647 h2)). Qed.
Lemma lem71649 (h1 : term16) : term16.
Proof. exact (fun h0 : term15 => @lem71648 h0 h1). Qed.
Lemma lem71650 : term18.
Proof. exact (fun h0 : term16 => @lem71649 h0). Qed.
Lemma lem71653 : term16.
Proof. exact (@lem71650 (@lem71642)). Qed.
Lemma lem71679 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem71680 : term19 = term20.
Proof. exact (@lem71679 term21). Qed.
Lemma lem71689 : term22 = term22.
Proof. exact (eq_refl term22). Qed.
Lemma lem71690 : term23 = term24.
Proof. exact (MK_COMB (@lem71689) (@lem71680)). Qed.
Lemma lem71693 : term25 = term25.
Proof. exact (eq_refl term25). Qed.
Lemma lem71694 : term26 = term27.
Proof. exact (MK_COMB (@lem71693) (@lem71690)). Qed.
Lemma lem71697 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem71698 : term29 = term30.
Proof. exact (MK_COMB (@lem71697) (@lem71694)). Qed.
Lemma lem71701 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem71708 : term15 = term32.
Proof. exact (MK_COMB (@lem71701) (@lem71698)). Qed.
Lemma lem71713 (i : ind) : (term33 i) = (term33 i).
Proof. exact (eq_refl (term33 i)). Qed.
Lemma lem71714 : term34 = term34.
Proof. exact (fun_ext (fun i : ind => @lem71713 i)). Qed.
Lemma lem71715 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71716 : term35 = term35.
Proof. exact (MK_COMB (@lem71715) (@lem71714)). Qed.
Lemma lem71719 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem71720 : term21 = term21.
Proof. exact (MK_COMB (@lem71719) (@lem71716)). Qed.
Lemma lem71721 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem71722 : term20 = term20.
Proof. exact (MK_COMB (@lem71721) (@lem71720)). Qed.
Lemma lem71723 (a : nat) : ((term37 a) = a) = ((term37 a) = a).
Proof. exact (eq_refl ((term37 a) = a)). Qed.
Lemma lem71724 : term38 = term38.
Proof. exact (fun_ext (fun a : nat => @lem71723 a)). Qed.
Lemma lem71725 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem71726 : term0 = term0.
Proof. exact (MK_COMB (@lem71725) (@lem71724)). Qed.
Lemma lem71727 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71728 : term22 = term22.
Proof. exact (MK_COMB (@lem71727) (@lem71726)). Qed.
Lemma lem71729 : term24 = term24.
Proof. exact (MK_COMB (@lem71728) (@lem71722)). Qed.
Lemma lem71734 (r : ind) : ((NUM_REP r) = ((term39 r) = r)) = ((NUM_REP r) = ((term39 r) = r)).
Proof. exact (eq_refl ((NUM_REP r) = ((term39 r) = r))). Qed.
Lemma lem71735 : term40 = term40.
Proof. exact (fun_ext (fun r : ind => @lem71734 r)). Qed.
Lemma lem71736 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71737 : term1 = term1.
Proof. exact (MK_COMB (@lem71736) (@lem71735)). Qed.
Lemma lem71738 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71739 : term25 = term25.
Proof. exact (MK_COMB (@lem71738) (@lem71737)). Qed.
Lemma lem71740 : term27 = term27.
Proof. exact (MK_COMB (@lem71739) (@lem71729)). Qed.
Lemma lem71743 (x : ind) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem71744 : term42 = term42.
Proof. exact (fun_ext (fun x : ind => @lem71743 x)). Qed.
Lemma lem71745 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71746 : term43 = term43.
Proof. exact (MK_COMB (@lem71745) (@lem71744)). Qed.
Lemma lem71747 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71748 : term28 = term28.
Proof. exact (MK_COMB (@lem71747) (@lem71746)). Qed.
Lemma lem71749 : term30 = term30.
Proof. exact (MK_COMB (@lem71748) (@lem71740)). Qed.
Lemma lem71752 (n : nat) : (term7 n) = (term7 n).
Proof. exact (eq_refl (term7 n)). Qed.
Lemma lem71753 : term9 = term9.
Proof. exact (fun_ext (fun n : nat => @lem71752 n)). Qed.
Lemma lem71754 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem71755 : term11 = term11.
Proof. exact (MK_COMB (@lem71754) (@lem71753)). Qed.
Lemma lem71756 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem71757 : term14 = term14.
Proof. exact (MK_COMB (@lem71756) (@lem71755)). Qed.
Lemma lem71758 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem71759 : term31 = term31.
Proof. exact (MK_COMB (@lem71758) (@lem71757)). Qed.
Lemma lem71760 : term32 = term32.
Proof. exact (MK_COMB (@lem71759) (@lem71749)). Qed.
Lemma lem71805 : term15 = term32.
Proof. exact (TRANS (@lem71708) (@lem71760)). Qed.
Lemma lem71806 : term32 = term15.
Proof. exact (SYM (@lem71805)). Qed.
Lemma lem71807 (h1 : term14) : term14.
Proof. exact (h1). Qed.
Lemma lem71808 (h1 : term43) : term43.
Proof. exact (h1). Qed.
Lemma lem71809 (h1 : term1) : term1.
Proof. exact (h1). Qed.
Lemma lem71810 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem71811 (h1 : term21) : term21.
Proof. exact (h1). Qed.
Lemma lem71814 (n : nat) : (term44 n) = ((term3 n) = (mk_num IND_0)).
Proof. exact (@lem16933 ((term3 n) = (mk_num IND_0))). Qed.
Lemma lem71815 (P : nat -> Prop) : (term45 P) = (term46 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem71816 : term14 = term47.
Proof. exact (@lem71815 term9). Qed.
Lemma lem71817 (n : nat) : (term48 n) = (term7 n).
Proof. exact (eq_refl (term48 n)). Qed.
Lemma lem71818 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem71819 (n : nat) : (term49 n) = (term44 n).
Proof. exact (MK_COMB (@lem71818) (@lem71817 n)). Qed.
Lemma lem71820 (n : nat) : (term49 n) = ((term3 n) = (mk_num IND_0)).
Proof. exact (TRANS (@lem71819 n) (@lem71814 n)). Qed.
Lemma lem71821 : term50 = term51.
Proof. exact (fun_ext (fun n : nat => @lem71820 n)). Qed.
Lemma lem71822 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem71823 : term47 = term52.
Proof. exact (MK_COMB (@lem71822) (@lem71821)). Qed.
Lemma lem71832 : term14 = term52.
Proof. exact (TRANS (@lem71816) (@lem71823)). Qed.
Lemma lem71833 (h1 : term14) : term52.
Proof. exact (EQ_MP (@lem71832) (@lem71807 h1)). Qed.
Lemma lem71834 (x : ind) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem71835 : term42 = term42.
Proof. exact (fun_ext (fun x : ind => @lem71834 x)). Qed.
Lemma lem71836 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71845 : term43 = term43.
Proof. exact (MK_COMB (@lem71836) (@lem71835)). Qed.
Lemma lem71846 (h1 : term43) : term43.
Proof. exact (EQ_MP (@lem71845) (@lem71808 h1)). Qed.
Lemma lem71861 (r : ind) : ((NUM_REP r) = ((term39 r) = r)) = (term53 r).
Proof. exact (@lem17784 (NUM_REP r) ((term39 r) = r)). Qed.
Lemma lem71862 : term40 = term54.
Proof. exact (fun_ext (fun r : ind => @lem71861 r)). Qed.
Lemma lem71863 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71864 : term1 = term55.
Proof. exact (MK_COMB (@lem71863) (@lem71862)). Qed.
Lemma lem71866 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term56 A P Q) = (term57 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem71867 (P : ind -> Prop) (Q : ind -> Prop) : (term58 P Q) = (term59 P Q).
Proof. exact (@lem71866 ind P Q). Qed.
Lemma lem71868 : term60 = term61.
Proof. exact (@lem71867 term62 term63). Qed.
Lemma lem71869 (r : ind) : (term64 r) = (term65 r).
Proof. exact (eq_refl (term64 r)). Qed.
Lemma lem71870 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem71871 (r : ind) : (term66 r) = (term67 r).
Proof. exact (MK_COMB (@lem71870) (@lem71869 r)). Qed.
Lemma lem71872 (r : ind) : (term68 r) = (term69 r).
Proof. exact (eq_refl (term68 r)). Qed.
Lemma lem71873 (r : ind) : (term70 r) = (term53 r).
Proof. exact (MK_COMB (@lem71871 r) (@lem71872 r)). Qed.
Lemma lem71874 : term71 = term54.
Proof. exact (fun_ext (fun r : ind => @lem71873 r)). Qed.
Lemma lem71875 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71876 : term60 = term55.
Proof. exact (MK_COMB (@lem71875) (@lem71874)). Qed.
Lemma lem71877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem71878 : term72 = term73.
Proof. exact (MK_COMB (@lem71877) (@lem71876)). Qed.
Lemma lem71879 (r : ind) : (term64 r) = (term65 r).
Proof. exact (eq_refl (term64 r)). Qed.
Lemma lem71880 : term74 = term62.
Proof. exact (fun_ext (fun r : ind => @lem71879 r)). Qed.
Lemma lem71881 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71882 : term75 = term76.
Proof. exact (MK_COMB (@lem71881) (@lem71880)). Qed.
Lemma lem71883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem71884 : term77 = term78.
Proof. exact (MK_COMB (@lem71883) (@lem71882)). Qed.
Lemma lem71885 (r : ind) : (term68 r) = (term69 r).
Proof. exact (eq_refl (term68 r)). Qed.
Lemma lem71886 : term79 = term63.
Proof. exact (fun_ext (fun r : ind => @lem71885 r)). Qed.
Lemma lem71887 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71888 : term80 = term81.
Proof. exact (MK_COMB (@lem71887) (@lem71886)). Qed.
Lemma lem71889 : term61 = term82.
Proof. exact (MK_COMB (@lem71884) (@lem71888)). Qed.
Lemma lem71890 : (term60 = term61) = (term55 = term82).
Proof. exact (MK_COMB (@lem71878) (@lem71889)). Qed.
Lemma lem71969 : term55 = term82.
Proof. exact (EQ_MP (@lem71890) (@lem71868)). Qed.
Lemma lem71970 : term1 = term82.
Proof. exact (TRANS (@lem71864) (@lem71969)). Qed.
Lemma lem71971 (h1 : term1) : term82.
Proof. exact (EQ_MP (@lem71970) (@lem71809 h1)). Qed.
Lemma lem71972 (a : nat) : ((term37 a) = a) = ((term37 a) = a).
Proof. exact (eq_refl ((term37 a) = a)). Qed.
Lemma lem71973 : term38 = term38.
Proof. exact (fun_ext (fun a : nat => @lem71972 a)). Qed.
Lemma lem71974 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem71983 : term0 = term0.
Proof. exact (MK_COMB (@lem71974) (@lem71973)). Qed.
Lemma lem71984 (h1 : term0) : term0.
Proof. exact (EQ_MP (@lem71983) (@lem71810 h1)). Qed.
Lemma lem71992 (i : ind) : (term33 i) = (term83 i).
Proof. exact (@lem17265 (NUM_REP i) (term84 i)). Qed.
Lemma lem71993 : term34 = term85.
Proof. exact (fun_ext (fun i : ind => @lem71992 i)). Qed.
Lemma lem71994 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem71995 : term35 = term86.
Proof. exact (MK_COMB (@lem71994) (@lem71993)). Qed.
Lemma lem71997 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem72050 : term21 = term87.
Proof. exact (MK_COMB (@lem71997) (@lem71995)). Qed.
Lemma lem72051 (h1 : term21) : term87.
Proof. exact (EQ_MP (@lem72050) (@lem71811 h1)). Qed.
Lemma lem72061 (x : ind) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem72062 : term42 = term42.
Proof. exact (fun_ext (fun x : ind => @lem72061 x)). Qed.
Lemma lem72063 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72064 : term43 = term43.
Proof. exact (MK_COMB (@lem72063) (@lem72062)). Qed.
Lemma lem72065 (h1 : term43) : term43.
Proof. exact (EQ_MP (@lem72064) (@lem71846 h1)). Qed.
Lemma lem72082 (r : ind) : (term69 r) = (term69 r).
Proof. exact (eq_refl (term69 r)). Qed.
Lemma lem72083 : term63 = term63.
Proof. exact (fun_ext (fun r : ind => @lem72082 r)). Qed.
Lemma lem72084 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72085 : term81 = term81.
Proof. exact (MK_COMB (@lem72084) (@lem72083)). Qed.
Lemma lem72102 (r : ind) : (term65 r) = (term65 r).
Proof. exact (eq_refl (term65 r)). Qed.
Lemma lem72103 : term62 = term62.
Proof. exact (fun_ext (fun r : ind => @lem72102 r)). Qed.
Lemma lem72104 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72105 : term76 = term76.
Proof. exact (MK_COMB (@lem72104) (@lem72103)). Qed.
Lemma lem72106 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem72107 : term78 = term78.
Proof. exact (MK_COMB (@lem72106) (@lem72105)). Qed.
Lemma lem72108 : term82 = term82.
Proof. exact (MK_COMB (@lem72107) (@lem72085)). Qed.
Lemma lem72109 (h1 : term1) : term82.
Proof. exact (EQ_MP (@lem72108) (@lem71971 h1)). Qed.
Lemma lem72118 (a : nat) : ((term37 a) = a) = ((term37 a) = a).
Proof. exact (eq_refl ((term37 a) = a)). Qed.
Lemma lem72119 : term38 = term38.
Proof. exact (fun_ext (fun a : nat => @lem72118 a)). Qed.
Lemma lem72120 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem72121 : term0 = term0.
Proof. exact (MK_COMB (@lem72120) (@lem72119)). Qed.
Lemma lem72122 (h1 : term0) : term0.
Proof. exact (EQ_MP (@lem72121) (@lem71984 h1)). Qed.
Lemma lem72135 (i : ind) : (term83 i) = (term83 i).
Proof. exact (eq_refl (term83 i)). Qed.
Lemma lem72136 : term85 = term85.
Proof. exact (fun_ext (fun i : ind => @lem72135 i)). Qed.
Lemma lem72137 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72138 : term86 = term86.
Proof. exact (MK_COMB (@lem72137) (@lem72136)). Qed.
Lemma lem72143 : term36 = term36.
Proof. exact (eq_refl term36). Qed.
Lemma lem72144 : term87 = term87.
Proof. exact (MK_COMB (@lem72143) (@lem72138)). Qed.
Lemma lem72145 (h1 : term21) : term87.
Proof. exact (EQ_MP (@lem72144) (@lem72051 h1)). Qed.
Lemma lem72159 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : (term3 n) = (mk_num IND_0).
Proof. exact (h1). Qed.
Lemma lem72160 (h1 : term21) : term86.
Proof. exact (proj2 (@lem72145 h1)). Qed.
Lemma lem72162 (h1 : term1) : term81.
Proof. exact (proj2 (@lem72109 h1)). Qed.
Lemma lem72163 (h1 : term1) : term76.
Proof. exact (proj1 (@lem72109 h1)). Qed.
Lemma lem72165 (x : ind) : (term41 x) = (term41 x).
Proof. exact (eq_refl (term41 x)). Qed.
Lemma lem72166 : term42 = term42.
Proof. exact (fun_ext (fun x : ind => @lem72165 x)). Qed.
Lemma lem72167 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72169 : term43 = term43.
Proof. exact (MK_COMB (@lem72167) (@lem72166)). Qed.
Lemma lem72170 (h1 : term43) : term43.
Proof. exact (EQ_MP (@lem72169) (@lem72065 h1)). Qed.
Lemma lem72172 (a : nat) : ((term37 a) = a) = ((term37 a) = a).
Proof. exact (eq_refl ((term37 a) = a)). Qed.
Lemma lem72173 : term38 = term38.
Proof. exact (fun_ext (fun a : nat => @lem72172 a)). Qed.
Lemma lem72174 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem72176 : term0 = term0.
Proof. exact (MK_COMB (@lem72174) (@lem72173)). Qed.
Lemma lem72177 (h1 : term0) : term0.
Proof. exact (EQ_MP (@lem72176) (@lem72122 h1)). Qed.
Lemma lem72181 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : (term3 n) = (mk_num IND_0).
Proof. exact (h1). Qed.
Lemma lem72193 (i : ind) : (term83 i) = (term83 i).
Proof. exact (eq_refl (term83 i)). Qed.
Lemma lem72194 : term85 = term85.
Proof. exact (fun_ext (fun i : ind => @lem72193 i)). Qed.
Lemma lem72195 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72197 : term86 = term86.
Proof. exact (MK_COMB (@lem72195) (@lem72194)). Qed.
Lemma lem72198 (h1 : term21) : term86.
Proof. exact (EQ_MP (@lem72197) (@lem72160 h1)). Qed.
Lemma lem72206 (r : ind) : (term65 r) = (term65 r).
Proof. exact (eq_refl (term65 r)). Qed.
Lemma lem72207 : term62 = term62.
Proof. exact (fun_ext (fun r : ind => @lem72206 r)). Qed.
Lemma lem72208 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72210 : term76 = term76.
Proof. exact (MK_COMB (@lem72208) (@lem72207)). Qed.
Lemma lem72211 (h1 : term1) : term76.
Proof. exact (EQ_MP (@lem72210) (@lem72163 h1)). Qed.
Lemma lem72219 (r : ind) : (term69 r) = (term69 r).
Proof. exact (eq_refl (term69 r)). Qed.
Lemma lem72220 : term63 = term63.
Proof. exact (fun_ext (fun r : ind => @lem72219 r)). Qed.
Lemma lem72221 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem72223 : term81 = term81.
Proof. exact (MK_COMB (@lem72221) (@lem72220)). Qed.
Lemma lem72224 (h1 : term1) : term81.
Proof. exact (EQ_MP (@lem72223) (@lem72162 h1)). Qed.
Lemma lem72225 (_2109 : ind) (h1 : term43) : term88 _2109.
Proof. exact (@lem72170 h1 _2109). Qed.
Lemma lem72226 (_2109 : ind) : (term88 _2109) = (term41 _2109).
Proof. exact (eq_refl (term88 _2109)). Qed.
Lemma lem72228 (_2110 : nat) (h1 : term0) : term89 _2110.
Proof. exact (@lem72177 h1 _2110). Qed.
Lemma lem72229 (_2110 : nat) : (term89 _2110) = ((term37 _2110) = _2110).
Proof. exact (eq_refl (term89 _2110)). Qed.
Lemma lem72231 (_2111 : ind) (h1 : term21) : term90 _2111.
Proof. exact (@lem72198 h1 _2111). Qed.
Lemma lem72232 (_2111 : ind) : (term90 _2111) = (term83 _2111).
Proof. exact (eq_refl (term90 _2111)). Qed.
Lemma lem72234 (_2112 : ind) (h1 : term1) : term64 _2112.
Proof. exact (@lem72211 h1 _2112). Qed.
Lemma lem72235 (_2112 : ind) : (term64 _2112) = (term65 _2112).
Proof. exact (eq_refl (term64 _2112)). Qed.
Lemma lem72237 (_2113 : ind) (h1 : term1) : term68 _2113.
Proof. exact (@lem72224 h1 _2113). Qed.
Lemma lem72238 (_2113 : ind) : (term68 _2113) = (term69 _2113).
Proof. exact (eq_refl (term68 _2113)). Qed.
Lemma lem72241 (_2109 : ind) (h1 : term43) : term41 _2109.
Proof. exact (EQ_MP (@lem72226 _2109) (@lem72225 _2109 h1)). Qed.
Lemma lem72245 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : (term3 n) = (mk_num IND_0).
Proof. exact (h1). Qed.
Lemma lem72253 (_2111 : ind) (h1 : term21) : term83 _2111.
Proof. exact (EQ_MP (@lem72232 _2111) (@lem72231 _2111 h1)). Qed.
Lemma lem72259 (_2112 : ind) (h1 : term1) : term65 _2112.
Proof. exact (EQ_MP (@lem72235 _2112) (@lem72234 _2112 h1)). Qed.
Lemma lem72265 (_2113 : ind) (h1 : term1) : term69 _2113.
Proof. exact (EQ_MP (@lem72238 _2113) (@lem72237 _2113 h1)). Qed.
Lemma lem72278 : dest_num = dest_num.
Proof. exact (eq_refl dest_num). Qed.
Lemma lem72279 (_2116 : nat) (_2117 : nat) (h1 : _2116 = _2117) : _2116 = _2117.
Proof. exact (h1). Qed.
Lemma lem72280 (_2116 : nat) (_2117 : nat) (h1 : _2116 = _2117) : (dest_num _2116) = (dest_num _2117).
Proof. exact (MK_COMB (@lem72278) (@lem72279 _2116 _2117 h1)). Qed.
Lemma lem72281 (_2116 : nat) (_2117 : nat) : term91 _2116 _2117.
Proof. exact (fun h0 : _2116 = _2117 => @lem72280 _2116 _2117 h0). Qed.
Lemma lem72283 (a : Prop) (b : Prop) : (a -> b) = (term92 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem72284 (_2116 : nat) (_2117 : nat) : (term91 _2116 _2117) = (term93 _2116 _2117).
Proof. exact (@lem72283 (_2116 = _2117) ((dest_num _2116) = (dest_num _2117))). Qed.
Lemma lem72285 (_2116 : nat) (_2117 : nat) : term93 _2116 _2117.
Proof. exact (EQ_MP (@lem72284 _2116 _2117) (@lem72281 _2116 _2117)). Qed.
Lemma lem72303 (x : ind) (y : ind) (z : ind) : term94 x y z.
Proof. exact (@lem21385 ind x y z). Qed.
Lemma lem72307 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : (term3 n) = (mk_num IND_0).
Proof. exact (h1). Qed.
Lemma lem72308 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : term95 n.
Proof. exact (fun h0 : term7 n => @lem72307 n h1). Qed.
Lemma lem72310 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72311 (n : nat) : (term95 n) = ((term3 n) = (mk_num IND_0)).
Proof. exact (@lem72310 ((term3 n) = (mk_num IND_0))). Qed.
Lemma lem72312 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : (term3 n) = (mk_num IND_0).
Proof. exact (EQ_MP (@lem72311 n) (@lem72308 n h1)). Qed.
Lemma lem72318 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem72319 (_2116 : nat) (_2117 : nat) : (term93 _2116 _2117) = (term97 _2116 _2117).
Proof. exact (@lem72318 ((dest_num _2116) = (dest_num _2117)) (term98 _2116 _2117)). Qed.
Lemma lem72329 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem72330 (_2116 : nat) (_2117 : nat) : (term99 _2116 _2117) = (term100 _2116 _2117).
Proof. exact (MK_COMB (@lem72329) (@lem72319 _2116 _2117)). Qed.
Lemma lem72340 (_2116 : nat) (_2117 : nat) : (term97 _2116 _2117) = (term97 _2116 _2117).
Proof. exact (eq_refl (term97 _2116 _2117)). Qed.
Lemma lem72341 (_2116 : nat) (_2117 : nat) : ((term93 _2116 _2117) = (term97 _2116 _2117)) = ((term97 _2116 _2117) = (term97 _2116 _2117)).
Proof. exact (MK_COMB (@lem72330 _2116 _2117) (@lem72340 _2116 _2117)). Qed.
Lemma lem72343 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem72344 (x : Prop) : (x = x) = True.
Proof. exact (@lem72343 Prop x). Qed.
Lemma lem72345 (_2116 : nat) (_2117 : nat) : ((term97 _2116 _2117) = (term97 _2116 _2117)) = True.
Proof. exact (@lem72344 (term97 _2116 _2117)). Qed.
Lemma lem72346 (_2116 : nat) (_2117 : nat) : ((term93 _2116 _2117) = (term97 _2116 _2117)) = True.
Proof. exact (TRANS (@lem72341 _2116 _2117) (@lem72345 _2116 _2117)). Qed.
Lemma lem72347 (_2116 : nat) (_2117 : nat) : True = ((term93 _2116 _2117) = (term97 _2116 _2117)).
Proof. exact (SYM (@lem72346 _2116 _2117)). Qed.
Lemma lem72348 (_2116 : nat) (_2117 : nat) : (term93 _2116 _2117) = (term97 _2116 _2117).
Proof. exact (EQ_MP (@lem72347 _2116 _2117) (@lem0)). Qed.
Lemma lem72349 (_2116 : nat) (_2117 : nat) : term97 _2116 _2117.
Proof. exact (EQ_MP (@lem72348 _2116 _2117) (@lem72285 _2116 _2117)). Qed.
Lemma lem72351 (b : Prop) (a : Prop) : (a \/ b) = (term101 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem72352 (_2116 : nat) (_2117 : nat) : (term97 _2116 _2117) = (term102 _2116 _2117).
Proof. exact (@lem72351 (term98 _2116 _2117) ((dest_num _2116) = (dest_num _2117))). Qed.
Lemma lem72354 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem72355 (_2116 : nat) (_2117 : nat) : (term104 _2116 _2117) = (_2116 = _2117).
Proof. exact (@lem72354 (_2116 = _2117)). Qed.
Lemma lem72356 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72357 (_2116 : nat) (_2117 : nat) : (term105 _2116 _2117) = (term106 _2116 _2117).
Proof. exact (MK_COMB (@lem72356) (@lem72355 _2116 _2117)). Qed.
Lemma lem72358 (_2116 : nat) (_2117 : nat) : ((dest_num _2116) = (dest_num _2117)) = ((dest_num _2116) = (dest_num _2117)).
Proof. exact (eq_refl ((dest_num _2116) = (dest_num _2117))). Qed.
Lemma lem72359 (_2116 : nat) (_2117 : nat) : (term102 _2116 _2117) = (term91 _2116 _2117).
Proof. exact (MK_COMB (@lem72357 _2116 _2117) (@lem72358 _2116 _2117)). Qed.
Lemma lem72360 (_2116 : nat) (_2117 : nat) : (term97 _2116 _2117) = (term91 _2116 _2117).
Proof. exact (TRANS (@lem72352 _2116 _2117) (@lem72359 _2116 _2117)). Qed.
Lemma lem72363 (_2116 : nat) (_2117 : nat) : term91 _2116 _2117.
Proof. exact (EQ_MP (@lem72360 _2116 _2117) (@lem72349 _2116 _2117)). Qed.
Lemma lem72364 (n : nat) : term107 n.
Proof. exact (@lem72363 (term3 n) (mk_num IND_0)). Qed.
Lemma lem72367 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : (term108 n) = term109.
Proof. exact (@lem72364 n (@lem72312 n h1)). Qed.
Lemma lem72368 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : term110 n.
Proof. exact (fun h0 : term111 n => @lem72367 n h1). Qed.
Lemma lem72370 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72371 (n : nat) : (term110 n) = ((term108 n) = term109).
Proof. exact (@lem72370 ((term108 n) = term109)). Qed.
Lemma lem72372 (n : nat) (h1 : (term3 n) = (mk_num IND_0)) : (term108 n) = term109.
Proof. exact (EQ_MP (@lem72371 n) (@lem72368 n h1)). Qed.
Lemma lem72374 (_2110 : nat) (h1 : term0) : (term37 _2110) = _2110.
Proof. exact (EQ_MP (@lem72229 _2110) (@lem72228 _2110 h1)). Qed.
Lemma lem72375 (n : nat) (h1 : term0) : (term37 n) = n.
Proof. exact (@lem72374 n h1). Qed.
Lemma lem72376 (n : nat) (h1 : term0) : term112 n.
Proof. exact (fun h0 : term113 n => @lem72375 n h1). Qed.
Lemma lem72378 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72379 (n : nat) : (term112 n) = ((term37 n) = n).
Proof. exact (@lem72378 ((term37 n) = n)). Qed.
Lemma lem72380 (n : nat) (h1 : term0) : (term37 n) = n.
Proof. exact (EQ_MP (@lem72379 n) (@lem72376 n h1)). Qed.
Lemma lem72382 (_2116 : nat) (_2117 : nat) : term91 _2116 _2117.
Proof. exact (EQ_MP (@lem72360 _2116 _2117) (@lem72349 _2116 _2117)). Qed.
Lemma lem72383 (n : nat) : term114 n.
Proof. exact (@lem72382 (term37 n) n). Qed.
Lemma lem72386 (n : nat) (h1 : term0) : (term115 n) = (dest_num n).
Proof. exact (@lem72383 n (@lem72380 n h1)). Qed.
Lemma lem72387 (n : nat) (h1 : term0) : term116 n.
Proof. exact (fun h0 : term117 n => @lem72386 n h1). Qed.
Lemma lem72389 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72390 (n : nat) : (term116 n) = ((term115 n) = (dest_num n)).
Proof. exact (@lem72389 ((term115 n) = (dest_num n))). Qed.
Lemma lem72391 (n : nat) (h1 : term0) : (term115 n) = (dest_num n).
Proof. exact (EQ_MP (@lem72390 n) (@lem72387 n h1)). Qed.
Lemma lem72393 (b : Prop) (a : Prop) : (a \/ b) = (term101 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem72394 (_2112 : ind) : (term65 _2112) = (term118 _2112).
Proof. exact (@lem72393 (term119 _2112) (NUM_REP _2112)). Qed.
Lemma lem72396 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem72397 (_2112 : ind) : (term120 _2112) = ((term39 _2112) = _2112).
Proof. exact (@lem72396 ((term39 _2112) = _2112)). Qed.
Lemma lem72398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72399 (_2112 : ind) : (term121 _2112) = (term122 _2112).
Proof. exact (MK_COMB (@lem72398) (@lem72397 _2112)). Qed.
Lemma lem72400 (_2112 : ind) : (NUM_REP _2112) = (NUM_REP _2112).
Proof. exact (eq_refl (NUM_REP _2112)). Qed.
Lemma lem72401 (_2112 : ind) : (term118 _2112) = (term123 _2112).
Proof. exact (MK_COMB (@lem72399 _2112) (@lem72400 _2112)). Qed.
Lemma lem72402 (_2112 : ind) : (term65 _2112) = (term123 _2112).
Proof. exact (TRANS (@lem72394 _2112) (@lem72401 _2112)). Qed.
Lemma lem72405 (_2112 : ind) (h1 : term1) : term123 _2112.
Proof. exact (EQ_MP (@lem72402 _2112) (@lem72259 _2112 h1)). Qed.
Lemma lem72406 (n : nat) (h1 : term1) : term124 n.
Proof. exact (@lem72405 (dest_num n) h1). Qed.
Lemma lem72409 (n : nat) (h1 : term1) (h2 : term0) : term125 n.
Proof. exact (@lem72406 n h1 (@lem72391 n h2)). Qed.
Lemma lem72410 (n : nat) (h1 : term1) (h2 : term0) : term126 n.
Proof. exact (fun h0 : term127 n => @lem72409 n h1 h2). Qed.
Lemma lem72412 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72413 (n : nat) : (term126 n) = (term125 n).
Proof. exact (@lem72412 (term125 n)). Qed.
Lemma lem72414 (n : nat) (h1 : term1) (h2 : term0) : term125 n.
Proof. exact (EQ_MP (@lem72413 n) (@lem72410 n h1 h2)). Qed.
Lemma lem72420 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem72421 (_2111 : ind) : (term83 _2111) = (term128 _2111).
Proof. exact (@lem72420 (term84 _2111) (term129 _2111)). Qed.
Lemma lem72427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem72428 (_2111 : ind) : (term130 _2111) = (term131 _2111).
Proof. exact (MK_COMB (@lem72427) (@lem72421 _2111)). Qed.
Lemma lem72434 (_2111 : ind) : (term128 _2111) = (term128 _2111).
Proof. exact (eq_refl (term128 _2111)). Qed.
Lemma lem72435 (_2111 : ind) : ((term83 _2111) = (term128 _2111)) = ((term128 _2111) = (term128 _2111)).
Proof. exact (MK_COMB (@lem72428 _2111) (@lem72434 _2111)). Qed.
Lemma lem72437 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem72438 (x : Prop) : (x = x) = True.
Proof. exact (@lem72437 Prop x). Qed.
Lemma lem72439 (_2111 : ind) : ((term128 _2111) = (term128 _2111)) = True.
Proof. exact (@lem72438 (term128 _2111)). Qed.
Lemma lem72440 (_2111 : ind) : ((term83 _2111) = (term128 _2111)) = True.
Proof. exact (TRANS (@lem72435 _2111) (@lem72439 _2111)). Qed.
Lemma lem72441 (_2111 : ind) : True = ((term83 _2111) = (term128 _2111)).
Proof. exact (SYM (@lem72440 _2111)). Qed.
Lemma lem72442 (_2111 : ind) : (term83 _2111) = (term128 _2111).
Proof. exact (EQ_MP (@lem72441 _2111) (@lem0)). Qed.
Lemma lem72443 (_2111 : ind) (h1 : term21) : term128 _2111.
Proof. exact (EQ_MP (@lem72442 _2111) (@lem72253 _2111 h1)). Qed.
Lemma lem72445 (b : Prop) (a : Prop) : (a \/ b) = (term101 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem72446 (_2111 : ind) : (term128 _2111) = (term132 _2111).
Proof. exact (@lem72445 (term129 _2111) (term84 _2111)). Qed.
Lemma lem72448 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem72449 (_2111 : ind) : (term133 _2111) = (NUM_REP _2111).
Proof. exact (@lem72448 (NUM_REP _2111)). Qed.
Lemma lem72450 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72451 (_2111 : ind) : (term134 _2111) = (term135 _2111).
Proof. exact (MK_COMB (@lem72450) (@lem72449 _2111)). Qed.
Lemma lem72452 (_2111 : ind) : (term84 _2111) = (term84 _2111).
Proof. exact (eq_refl (term84 _2111)). Qed.
Lemma lem72453 (_2111 : ind) : (term132 _2111) = (term33 _2111).
Proof. exact (MK_COMB (@lem72451 _2111) (@lem72452 _2111)). Qed.
Lemma lem72454 (_2111 : ind) : (term128 _2111) = (term33 _2111).
Proof. exact (TRANS (@lem72446 _2111) (@lem72453 _2111)). Qed.
Lemma lem72457 (_2111 : ind) (h1 : term21) : term33 _2111.
Proof. exact (EQ_MP (@lem72454 _2111) (@lem72443 _2111 h1)). Qed.
Lemma lem72458 (n : nat) (h1 : term21) : term136 n.
Proof. exact (@lem72457 (dest_num n) h1). Qed.
Lemma lem72461 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) : term137 n.
Proof. exact (@lem72458 n h3 (@lem72414 n h1 h2)). Qed.
Lemma lem72462 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) : term138 n.
Proof. exact (fun h0 : term139 n => @lem72461 n h1 h2 h3). Qed.
Lemma lem72464 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72465 (n : nat) : (term138 n) = (term137 n).
Proof. exact (@lem72464 (term137 n)). Qed.
Lemma lem72466 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) : term137 n.
Proof. exact (EQ_MP (@lem72465 n) (@lem72462 n h1 h2 h3)). Qed.
Lemma lem72472 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem72473 (_2113 : ind) : (term69 _2113) = (term140 _2113).
Proof. exact (@lem72472 ((term39 _2113) = _2113) (term129 _2113)). Qed.
Lemma lem72481 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem72482 (_2113 : ind) : (term141 _2113) = (term142 _2113).
Proof. exact (MK_COMB (@lem72481) (@lem72473 _2113)). Qed.
Lemma lem72490 (_2113 : ind) : (term140 _2113) = (term140 _2113).
Proof. exact (eq_refl (term140 _2113)). Qed.
Lemma lem72491 (_2113 : ind) : ((term69 _2113) = (term140 _2113)) = ((term140 _2113) = (term140 _2113)).
Proof. exact (MK_COMB (@lem72482 _2113) (@lem72490 _2113)). Qed.
Lemma lem72493 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem72494 (x : Prop) : (x = x) = True.
Proof. exact (@lem72493 Prop x). Qed.
Lemma lem72495 (_2113 : ind) : ((term140 _2113) = (term140 _2113)) = True.
Proof. exact (@lem72494 (term140 _2113)). Qed.
Lemma lem72496 (_2113 : ind) : ((term69 _2113) = (term140 _2113)) = True.
Proof. exact (TRANS (@lem72491 _2113) (@lem72495 _2113)). Qed.
Lemma lem72497 (_2113 : ind) : True = ((term69 _2113) = (term140 _2113)).
Proof. exact (SYM (@lem72496 _2113)). Qed.
Lemma lem72498 (_2113 : ind) : (term69 _2113) = (term140 _2113).
Proof. exact (EQ_MP (@lem72497 _2113) (@lem0)). Qed.
Lemma lem72499 (_2113 : ind) (h1 : term1) : term140 _2113.
Proof. exact (EQ_MP (@lem72498 _2113) (@lem72265 _2113 h1)). Qed.
Lemma lem72501 (b : Prop) (a : Prop) : (a \/ b) = (term101 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem72502 (_2113 : ind) : (term140 _2113) = (term143 _2113).
Proof. exact (@lem72501 (term129 _2113) ((term39 _2113) = _2113)). Qed.
Lemma lem72504 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem72505 (_2113 : ind) : (term133 _2113) = (NUM_REP _2113).
Proof. exact (@lem72504 (NUM_REP _2113)). Qed.
Lemma lem72506 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72507 (_2113 : ind) : (term134 _2113) = (term135 _2113).
Proof. exact (MK_COMB (@lem72506) (@lem72505 _2113)). Qed.
Lemma lem72508 (_2113 : ind) : ((term39 _2113) = _2113) = ((term39 _2113) = _2113).
Proof. exact (eq_refl ((term39 _2113) = _2113)). Qed.
Lemma lem72509 (_2113 : ind) : (term143 _2113) = (term144 _2113).
Proof. exact (MK_COMB (@lem72507 _2113) (@lem72508 _2113)). Qed.
Lemma lem72510 (_2113 : ind) : (term140 _2113) = (term144 _2113).
Proof. exact (TRANS (@lem72502 _2113) (@lem72509 _2113)). Qed.
Lemma lem72513 (_2113 : ind) (h1 : term1) : term144 _2113.
Proof. exact (EQ_MP (@lem72510 _2113) (@lem72499 _2113 h1)). Qed.
Lemma lem72514 (n : nat) (h1 : term1) : term145 n.
Proof. exact (@lem72513 (term146 n) h1). Qed.
Lemma lem72517 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) : (term108 n) = (term146 n).
Proof. exact (@lem72514 n h1 (@lem72466 n h1 h2 h3)). Qed.
Lemma lem72518 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) : term147 n.
Proof. exact (fun h0 : term148 n => @lem72517 n h1 h2 h3). Qed.
Lemma lem72520 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72521 (n : nat) : (term147 n) = ((term108 n) = (term146 n)).
Proof. exact (@lem72520 ((term108 n) = (term146 n))). Qed.
Lemma lem72522 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) : (term108 n) = (term146 n).
Proof. exact (EQ_MP (@lem72521 n) (@lem72518 n h1 h2 h3)). Qed.
Lemma lem72540 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem72541 (y : ind) (x : ind) (z : ind) : (term149 x y z) = (term150 y x z).
Proof. exact (@lem72540 (y = z) (term151 x z)). Qed.
Lemma lem72551 (x : ind) (y : ind) : (term152 x y) = (term152 x y).
Proof. exact (eq_refl (term152 x y)). Qed.
Lemma lem72552 (y : ind) (x : ind) (z : ind) : (term94 x y z) = (term153 y x z).
Proof. exact (MK_COMB (@lem72551 x y) (@lem72541 y x z)). Qed.
Lemma lem72556 (q : Prop) (p : Prop) (r : Prop) : (term154 p q r) = (term154 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem72557 (y : ind) (x : ind) (z : ind) : (term153 y x z) = (term155 y x z).
Proof. exact (@lem72556 (y = z) (term151 x y) (term151 x z)). Qed.
Lemma lem72579 (y : ind) (x : ind) (z : ind) : (term94 x y z) = (term155 y x z).
Proof. exact (TRANS (@lem72552 y x z) (@lem72557 y x z)). Qed.
Lemma lem72580 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem72581 (y : ind) (x : ind) (z : ind) : (term156 x y z) = (term157 y x z).
Proof. exact (MK_COMB (@lem72580) (@lem72579 y x z)). Qed.
Lemma lem72603 (y : ind) (x : ind) (z : ind) : (term155 y x z) = (term155 y x z).
Proof. exact (eq_refl (term155 y x z)). Qed.
Lemma lem72604 (y : ind) (x : ind) (z : ind) : ((term94 x y z) = (term155 y x z)) = ((term155 y x z) = (term155 y x z)).
Proof. exact (MK_COMB (@lem72581 y x z) (@lem72603 y x z)). Qed.
Lemma lem72606 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem72607 (x : Prop) : (x = x) = True.
Proof. exact (@lem72606 Prop x). Qed.
Lemma lem72608 (y : ind) (x : ind) (z : ind) : ((term155 y x z) = (term155 y x z)) = True.
Proof. exact (@lem72607 (term155 y x z)). Qed.
Lemma lem72609 (y : ind) (x : ind) (z : ind) : ((term94 x y z) = (term155 y x z)) = True.
Proof. exact (TRANS (@lem72604 y x z) (@lem72608 y x z)). Qed.
Lemma lem72610 (y : ind) (x : ind) (z : ind) : True = ((term94 x y z) = (term155 y x z)).
Proof. exact (SYM (@lem72609 y x z)). Qed.
Lemma lem72611 (y : ind) (x : ind) (z : ind) : (term94 x y z) = (term155 y x z).
Proof. exact (EQ_MP (@lem72610 y x z) (@lem0)). Qed.
Lemma lem72612 (y : ind) (x : ind) (z : ind) : term155 y x z.
Proof. exact (EQ_MP (@lem72611 y x z) (@lem72303 x y z)). Qed.
Lemma lem72614 (b : Prop) (a : Prop) : (a \/ b) = (term101 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem72615 (x : ind) (y : ind) (z : ind) : (term155 y x z) = (term158 x y z).
Proof. exact (@lem72614 (term159 y x z) (y = z)). Qed.
Lemma lem72617 (a : Prop) (b : Prop) : (term160 a b) = (term161 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem72618 (y : ind) (x : ind) (z : ind) : (term162 y x z) = (term163 y x z).
Proof. exact (@lem72617 (term151 x y) (term151 x z)). Qed.
Lemma lem72620 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem72621 (x : ind) (y : ind) : (term164 x y) = (x = y).
Proof. exact (@lem72620 (x = y)). Qed.
Lemma lem72622 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem72623 (x : ind) (y : ind) : (term165 x y) = (term166 x y).
Proof. exact (MK_COMB (@lem72622) (@lem72621 x y)). Qed.
Lemma lem72625 (a : Prop) : (term103 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem72626 (x : ind) (z : ind) : (term164 x z) = (x = z).
Proof. exact (@lem72625 (x = z)). Qed.
Lemma lem72627 (y : ind) (x : ind) (z : ind) : (term163 y x z) = (term167 y x z).
Proof. exact (MK_COMB (@lem72623 x y) (@lem72626 x z)). Qed.
Lemma lem72628 (y : ind) (x : ind) (z : ind) : (term162 y x z) = (term167 y x z).
Proof. exact (TRANS (@lem72618 y x z) (@lem72627 y x z)). Qed.
Lemma lem72629 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem72630 (y : ind) (x : ind) (z : ind) : (term168 y x z) = (term169 y x z).
Proof. exact (MK_COMB (@lem72629) (@lem72628 y x z)). Qed.
Lemma lem72631 (y : ind) (z : ind) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem72632 (x : ind) (y : ind) (z : ind) : (term158 x y z) = (term170 x y z).
Proof. exact (MK_COMB (@lem72630 y x z) (@lem72631 y z)). Qed.
Lemma lem72633 (x : ind) (y : ind) (z : ind) : (term155 y x z) = (term170 x y z).
Proof. exact (TRANS (@lem72615 x y z) (@lem72632 x y z)). Qed.
Lemma lem72635 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : term171 n.
Proof. exact (conj (@lem72372 n h4) (@lem72522 n h1 h2 h3)). Qed.
Lemma lem72637 (x : ind) (y : ind) (z : ind) : term170 x y z.
Proof. exact (EQ_MP (@lem72633 x y z) (@lem72612 y x z)). Qed.
Lemma lem72638 (n : nat) : term172 n.
Proof. exact (@lem72637 (term108 n) term109 (term146 n)). Qed.
Lemma lem72641 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : term109 = (term146 n).
Proof. exact (@lem72638 n (@lem72635 n h1 h2 h3 h4)). Qed.
Lemma lem72642 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : term173 n.
Proof. exact (fun h0 : term174 n => @lem72641 n h1 h2 h3 h4). Qed.
Lemma lem72644 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72645 (n : nat) : (term173 n) = (term109 = (term146 n)).
Proof. exact (@lem72644 (term109 = (term146 n))). Qed.
Lemma lem72646 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : term109 = (term146 n).
Proof. exact (EQ_MP (@lem72645 n) (@lem72642 n h1 h2 h3 h4)). Qed.
Lemma lem72648 (h1 : term21) : NUM_REP IND_0.
Proof. exact (proj1 (@lem72145 h1)). Qed.
Lemma lem72649 (h1 : term21) : term175.
Proof. exact (fun h0 : term176 => @lem72648 h1). Qed.
Lemma lem72651 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72652 : term175 = (NUM_REP IND_0).
Proof. exact (@lem72651 (NUM_REP IND_0)). Qed.
Lemma lem72653 (h1 : term21) : NUM_REP IND_0.
Proof. exact (EQ_MP (@lem72652) (@lem72649 h1)). Qed.
Lemma lem72655 (_2113 : ind) (h1 : term1) : term144 _2113.
Proof. exact (EQ_MP (@lem72510 _2113) (@lem72499 _2113 h1)). Qed.
Lemma lem72656 (h1 : term1) : term177.
Proof. exact (@lem72655 IND_0 h1). Qed.
Lemma lem72659 (h1 : term1) (h2 : term21) : term109 = IND_0.
Proof. exact (@lem72656 h1 (@lem72653 h2)). Qed.
Lemma lem72660 (h1 : term1) (h2 : term21) : term178.
Proof. exact (fun h0 : term179 => @lem72659 h1 h2). Qed.
Lemma lem72662 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72663 : term178 = (term109 = IND_0).
Proof. exact (@lem72662 (term109 = IND_0)). Qed.
Lemma lem72664 (h1 : term1) (h2 : term21) : term109 = IND_0.
Proof. exact (EQ_MP (@lem72663) (@lem72660 h1 h2)). Qed.
Lemma lem72665 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : term180 n.
Proof. exact (conj (@lem72646 n h1 h2 h3 h4) (@lem72664 h1 h3)). Qed.
Lemma lem72667 (x : ind) (y : ind) (z : ind) : term170 x y z.
Proof. exact (EQ_MP (@lem72633 x y z) (@lem72612 y x z)). Qed.
Lemma lem72668 (n : nat) : term181 n.
Proof. exact (@lem72667 term109 (term146 n) IND_0). Qed.
Lemma lem72671 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : (term146 n) = IND_0.
Proof. exact (@lem72668 n (@lem72665 n h1 h2 h3 h4)). Qed.
Lemma lem72672 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : term182 n.
Proof. exact (fun h0 : term183 n => @lem72671 n h1 h2 h3 h4). Qed.
Lemma lem72674 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72675 (n : nat) : (term182 n) = ((term146 n) = IND_0).
Proof. exact (@lem72674 ((term146 n) = IND_0)). Qed.
Lemma lem72676 (n : nat) (h1 : term1) (h2 : term0) (h3 : term21) (h4 : (term3 n) = (mk_num IND_0)) : (term146 n) = IND_0.
Proof. exact (EQ_MP (@lem72675 n) (@lem72672 n h1 h2 h3 h4)). Qed.
Lemma lem72679 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem72681 (_2109 : ind) : (term41 _2109) = (term184 _2109).
Proof. exact (@lem72679 ((IND_SUC _2109) = IND_0)). Qed.
Lemma lem72684 (_2109 : ind) (h1 : term43) : term184 _2109.
Proof. exact (EQ_MP (@lem72681 _2109) (@lem72241 _2109 h1)). Qed.
Lemma lem72685 (n : nat) (h1 : term43) : term185 n.
Proof. exact (@lem72684 (dest_num n) h1). Qed.
Lemma lem72688 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (@lem72685 n h1 (@lem72676 n h2 h3 h4 h5)). Qed.
Lemma lem72689 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : term186.
Proof. exact (fun h0 : ~ False => @lem72688 n h1 h2 h3 h4 h5). Qed.
Lemma lem72691 (p : Prop) : (term96 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem72692 : term186 = False.
Proof. exact (@lem72691 False). Qed.
Lemma lem72693 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72692) (@lem72689 n h1 h2 h3 h4 h5)). Qed.
Lemma lem72694 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : ((term3 n) = (mk_num IND_0)) = False.
Proof. exact (prop_ext (fun h6 : (term3 n) = (mk_num IND_0) => @lem72693 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72245 n h5)). Qed.
Lemma lem72695 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72694 n h1 h2 h3 h4 h5) (@lem72245 n h5)). Qed.
Lemma lem72696 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : ((term3 n) = (mk_num IND_0)) = False.
Proof. exact (prop_ext (fun h6 : (term3 n) = (mk_num IND_0) => @lem72695 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72181 n h5)). Qed.
Lemma lem72697 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72696 n h1 h2 h3 h4 h5) (@lem72181 n h5)). Qed.
Lemma lem72698 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : ((term3 n) = (mk_num IND_0)) = False.
Proof. exact (prop_ext (fun h6 : (term3 n) = (mk_num IND_0) => @lem72697 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72181 n h5)). Qed.
Lemma lem72699 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72698 n h1 h2 h3 h4 h5) (@lem72181 n h5)). Qed.
Lemma lem72700 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : term0 = False.
Proof. exact (prop_ext (fun h6 : term0 => @lem72699 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72177 h3)). Qed.
Lemma lem72701 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72700 n h1 h2 h3 h4 h5) (@lem72177 h3)). Qed.
Lemma lem72702 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : term43 = False.
Proof. exact (prop_ext (fun h6 : term43 => @lem72701 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72170 h1)). Qed.
Lemma lem72703 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72702 n h1 h2 h3 h4 h5) (@lem72170 h1)). Qed.
Lemma lem72704 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : ((term3 n) = (mk_num IND_0)) = False.
Proof. exact (prop_ext (fun h6 : (term3 n) = (mk_num IND_0) => @lem72703 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72159 n h5)). Qed.
Lemma lem72705 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72704 n h1 h2 h3 h4 h5) (@lem72159 n h5)). Qed.
Lemma lem72706 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : term0 = False.
Proof. exact (prop_ext (fun h6 : term0 => @lem72705 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72122 h3)). Qed.
Lemma lem72707 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72706 n h1 h2 h3 h4 h5) (@lem72122 h3)). Qed.
Lemma lem72708 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : term43 = False.
Proof. exact (prop_ext (fun h6 : term43 => @lem72707 n h1 h2 h3 h4 h5) (fun h6 : False => @lem72065 h1)). Qed.
Lemma lem72709 (n : nat) (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term21) (h5 : (term3 n) = (mk_num IND_0)) : False.
Proof. exact (EQ_MP (@lem72708 n h1 h2 h3 h4 h5) (@lem72065 h1)). Qed.
Lemma lem72710 (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term14) (h5 : term21) : False.
Proof. exact (ex_elim (@lem71833 h4) (fun n : nat => fun h0 : term51 n => @lem72709 n h1 h2 h3 h5 h0)). Qed.
Lemma lem72711 (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term14) (h5 : term21) : term0 = False.
Proof. exact (prop_ext (fun h6 : term0 => @lem72710 h1 h2 h3 h4 h5) (fun h6 : False => @lem71984 h3)). Qed.
Lemma lem72712 (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term14) (h5 : term21) : False.
Proof. exact (EQ_MP (@lem72711 h1 h2 h3 h4 h5) (@lem71984 h3)). Qed.
Lemma lem72713 (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term14) (h5 : term21) : term43 = False.
Proof. exact (prop_ext (fun h6 : term43 => @lem72712 h1 h2 h3 h4 h5) (fun h6 : False => @lem71846 h1)). Qed.
Lemma lem72714 (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term14) (h5 : term21) : False.
Proof. exact (EQ_MP (@lem72713 h1 h2 h3 h4 h5) (@lem71846 h1)). Qed.
Lemma lem72715 (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term14) : term19.
Proof. exact (fun h0 : term21 => @lem72714 h1 h2 h3 h4 h0). Qed.
Lemma lem72716 : term19 = term20.
Proof. exact (@lem69 term21). Qed.
Lemma lem72717 (h1 : term43) (h2 : term1) (h3 : term0) (h4 : term14) : term20.
Proof. exact (EQ_MP (@lem72716) (@lem72715 h1 h2 h3 h4)). Qed.
Lemma lem72718 (h1 : term43) (h2 : term1) (h3 : term14) : term24.
Proof. exact (fun h0 : term0 => @lem72717 h1 h2 h0 h3). Qed.
Lemma lem72719 (h1 : term43) (h2 : term14) : term27.
Proof. exact (fun h0 : term1 => @lem72718 h1 h0 h2). Qed.
Lemma lem72720 (h1 : term14) : term30.
Proof. exact (fun h0 : term43 => @lem72719 h0 h1). Qed.
Lemma lem72721 : term32.
Proof. exact (fun h0 : term14 => @lem72720 h0). Qed.
Lemma lem72722 : term15.
Proof. exact (EQ_MP (@lem71806) (@lem72721)). Qed.
Lemma lem72724 : term15.
Proof. exact (@lem71653 (@lem72722)). Qed.
Lemma lem72725 (h1 : term14) : term29.
Proof. exact (@lem72724 (@lem71638 h1)). Qed.
Lemma lem72726 (h1 : term14) : term26.
Proof. exact (@lem72725 h1 (@lem70827)). Qed.
Lemma lem72727 (h1 : term14) : term23.
Proof. exact (@lem72726 h1 (@lem71605)). Qed.
Lemma lem72728 (h1 : term14) : term19.
Proof. exact (@lem72727 h1 (@lem71604)). Qed.
Lemma lem72729 (h1 : term14) : False.
Proof. exact (@lem72728 h1 (@lem71256)). Qed.
Lemma lem72730 (h1 : term14) : term14 = False.
Proof. exact (prop_ext (fun h2 : term14 => @lem72729 h1) (fun h2 : False => @lem71638 h1)). Qed.
Lemma lem72731 (h1 : term14) : False.
Proof. exact (EQ_MP (@lem72730 h1) (@lem71638 h1)). Qed.
Lemma lem72732 : term13.
Proof. exact (fun h0 : term14 => @lem72731 h0). Qed.
Lemma lem72733 : term11.
Proof. exact (EQ_MP (@lem71637) (@lem72732)). Qed.
Lemma lem72734 : term10.
Proof. exact (EQ_MP (@lem71633) (@lem72733)). Qed.
