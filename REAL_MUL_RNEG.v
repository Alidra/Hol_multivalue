Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_MUL_RNEG_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_EQ_ADD_RCANCEL_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1338588_spec.
Require Import thm1339188_spec.
Require Import thm16474_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18946_spec.
Require Import thm18947_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
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
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Lemma lem1358674 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1358675 : term1 = term2.
Proof. exact (@lem1358674 term1). Qed.
Lemma lem1358676 : term2 = term1.
Proof. exact (SYM (@lem1358675)). Qed.
Lemma lem1358677 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1358680 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1358681 : term5.
Proof. exact (fun h0 : term4 => @lem1358680 h0). Qed.
Lemma lem1358682 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1358683 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1358684 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1358682 h2 (@lem1358683 h1)). Qed.
Lemma lem1358685 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1358684 h1 h0). Qed.
Lemma lem1358686 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1358687 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1358685 h1 (@lem1358686 h2)). Qed.
Lemma lem1358688 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1358687 h0 h1). Qed.
Lemma lem1358689 : term7.
Proof. exact (fun h0 : term5 => @lem1358688 h0). Qed.
Lemma lem1358692 : term5.
Proof. exact (@lem1358689 (@lem1358681)). Qed.
Lemma lem1358730 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1358731 : term8 = term9.
Proof. exact (@lem1358730 term10). Qed.
Lemma lem1358744 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1358745 : term12 = term13.
Proof. exact (MK_COMB (@lem1358744) (@lem1358731)). Qed.
Lemma lem1358748 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1358749 : term15 = term16.
Proof. exact (MK_COMB (@lem1358748) (@lem1358745)). Qed.
Lemma lem1358752 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1358753 : term18 = term19.
Proof. exact (MK_COMB (@lem1358752) (@lem1358749)). Qed.
Lemma lem1358756 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1358763 : term4 = term21.
Proof. exact (MK_COMB (@lem1358756) (@lem1358753)). Qed.
Lemma lem1358768 (z : real) (x : real) (y : real) : (((real_add x z) = (real_add y z)) = (x = y)) = (((real_add x z) = (real_add y z)) = (x = y)).
Proof. exact (eq_refl (((real_add x z) = (real_add y z)) = (x = y))). Qed.
Lemma lem1358769 (x : real) (y : real) : (term22 x y) = (term22 x y).
Proof. exact (fun_ext (fun z : real => @lem1358768 z x y)). Qed.
Lemma lem1358770 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358771 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1358770) (@lem1358769 x y)). Qed.
Lemma lem1358772 (x : real) : (term24 x) = (term24 x).
Proof. exact (fun_ext (fun y : real => @lem1358771 x y)). Qed.
Lemma lem1358773 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358774 (x : real) : (term25 x) = (term25 x).
Proof. exact (MK_COMB (@lem1358773) (@lem1358772 x)). Qed.
Lemma lem1358775 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1358774 x)). Qed.
Lemma lem1358776 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358777 : term10 = term10.
Proof. exact (MK_COMB (@lem1358776) (@lem1358775)). Qed.
Lemma lem1358778 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1358779 : term9 = term9.
Proof. exact (MK_COMB (@lem1358778) (@lem1358777)). Qed.
Lemma lem1358780 (y : real) (x : real) (z : real) : ((term27 x y z) = (term28 y x z)) = ((term27 x y z) = (term28 y x z)).
Proof. exact (eq_refl ((term27 x y z) = (term28 y x z))). Qed.
Lemma lem1358781 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (fun_ext (fun z : real => @lem1358780 y x z)). Qed.
Lemma lem1358782 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358783 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem1358782) (@lem1358781 y x)). Qed.
Lemma lem1358784 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1358783 y x)). Qed.
Lemma lem1358785 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358786 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1358785) (@lem1358784 x)). Qed.
Lemma lem1358787 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1358786 x)). Qed.
Lemma lem1358788 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358789 : term34 = term34.
Proof. exact (MK_COMB (@lem1358788) (@lem1358787)). Qed.
Lemma lem1358790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1358791 : term11 = term11.
Proof. exact (MK_COMB (@lem1358790) (@lem1358789)). Qed.
Lemma lem1358792 : term13 = term13.
Proof. exact (MK_COMB (@lem1358791) (@lem1358779)). Qed.
Lemma lem1358793 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1358794 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1358793 x)). Qed.
Lemma lem1358795 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358796 : term38 = term38.
Proof. exact (MK_COMB (@lem1358795) (@lem1358794)). Qed.
Lemma lem1358797 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1358798 : term14 = term14.
Proof. exact (MK_COMB (@lem1358797) (@lem1358796)). Qed.
Lemma lem1358799 : term16 = term16.
Proof. exact (MK_COMB (@lem1358798) (@lem1358792)). Qed.
Lemma lem1358800 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1358801 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1358800 x)). Qed.
Lemma lem1358802 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358803 : term41 = term41.
Proof. exact (MK_COMB (@lem1358802) (@lem1358801)). Qed.
Lemma lem1358804 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1358805 : term17 = term17.
Proof. exact (MK_COMB (@lem1358804) (@lem1358803)). Qed.
Lemma lem1358806 : term19 = term19.
Proof. exact (MK_COMB (@lem1358805) (@lem1358799)). Qed.
Lemma lem1358807 (x : real) (y : real) : ((term42 x y) = (term43 x y)) = ((term42 x y) = (term43 x y)).
Proof. exact (eq_refl ((term42 x y) = (term43 x y))). Qed.
Lemma lem1358808 (x : real) : (term44 x) = (term44 x).
Proof. exact (fun_ext (fun y : real => @lem1358807 x y)). Qed.
Lemma lem1358809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358810 (x : real) : (term45 x) = (term45 x).
Proof. exact (MK_COMB (@lem1358809) (@lem1358808 x)). Qed.
Lemma lem1358811 : term46 = term46.
Proof. exact (fun_ext (fun x : real => @lem1358810 x)). Qed.
Lemma lem1358812 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358813 : term1 = term1.
Proof. exact (MK_COMB (@lem1358812) (@lem1358811)). Qed.
Lemma lem1358814 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1358815 : term3 = term3.
Proof. exact (MK_COMB (@lem1358814) (@lem1358813)). Qed.
Lemma lem1358816 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1358817 : term20 = term20.
Proof. exact (MK_COMB (@lem1358816) (@lem1358815)). Qed.
Lemma lem1358818 : term21 = term21.
Proof. exact (MK_COMB (@lem1358817) (@lem1358806)). Qed.
Lemma lem1358889 : term4 = term21.
Proof. exact (TRANS (@lem1358763) (@lem1358818)). Qed.
Lemma lem1358890 : term21 = term4.
Proof. exact (SYM (@lem1358889)). Qed.
Lemma lem1358891 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1358892 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1358893 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1358894 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1358895 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1358897 (P : real -> Prop) : (term47 P) = (term48 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1358898 (x : real) : (term49 x) = (term50 x).
Proof. exact (@lem1358897 (term44 x)). Qed.
Lemma lem1358899 (x : real) (y : real) : (term51 x y) = ((term42 x y) = (term43 x y)).
Proof. exact (eq_refl (term51 x y)). Qed.
Lemma lem1358900 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1358902 (x : real) (y : real) : (term52 x y) = (term53 x y).
Proof. exact (MK_COMB (@lem1358900) (@lem1358899 x y)). Qed.
Lemma lem1358903 (x : real) : (term54 x) = (term55 x).
Proof. exact (fun_ext (fun y : real => @lem1358902 x y)). Qed.
Lemma lem1358904 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1358905 (x : real) : (term50 x) = (term56 x).
Proof. exact (MK_COMB (@lem1358904) (@lem1358903 x)). Qed.
Lemma lem1358906 (x : real) : (term49 x) = (term56 x).
Proof. exact (TRANS (@lem1358898 x) (@lem1358905 x)). Qed.
Lemma lem1358907 (P : real -> Prop) : (term47 P) = (term48 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1358908 : term3 = term57.
Proof. exact (@lem1358907 term46). Qed.
Lemma lem1358909 (x : real) : (term58 x) = (term45 x).
Proof. exact (eq_refl (term58 x)). Qed.
Lemma lem1358910 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1358911 (x : real) : (term59 x) = (term49 x).
Proof. exact (MK_COMB (@lem1358910) (@lem1358909 x)). Qed.
Lemma lem1358912 (x : real) : (term59 x) = (term56 x).
Proof. exact (TRANS (@lem1358911 x) (@lem1358906 x)). Qed.
Lemma lem1358913 : term60 = term61.
Proof. exact (fun_ext (fun x : real => @lem1358912 x)). Qed.
Lemma lem1358914 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1358915 : term57 = term62.
Proof. exact (MK_COMB (@lem1358914) (@lem1358913)). Qed.
Lemma lem1358928 : term3 = term62.
Proof. exact (TRANS (@lem1358908) (@lem1358915)). Qed.
Lemma lem1358929 (h1 : term3) : term62.
Proof. exact (EQ_MP (@lem1358928) (@lem1358891 h1)). Qed.
Lemma lem1358930 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1358931 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1358930 x)). Qed.
Lemma lem1358932 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358941 : term41 = term41.
Proof. exact (MK_COMB (@lem1358932) (@lem1358931)). Qed.
Lemma lem1358942 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1358941) (@lem1358892 h1)). Qed.
Lemma lem1358943 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1358944 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1358943 x)). Qed.
Lemma lem1358945 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358954 : term38 = term38.
Proof. exact (MK_COMB (@lem1358945) (@lem1358944)). Qed.
Lemma lem1358955 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1358954) (@lem1358893 h1)). Qed.
Lemma lem1358956 (y : real) (x : real) (z : real) : ((term27 x y z) = (term28 y x z)) = ((term27 x y z) = (term28 y x z)).
Proof. exact (eq_refl ((term27 x y z) = (term28 y x z))). Qed.
Lemma lem1358957 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (fun_ext (fun z : real => @lem1358956 y x z)). Qed.
Lemma lem1358958 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358959 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem1358958) (@lem1358957 y x)). Qed.
Lemma lem1358960 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1358959 y x)). Qed.
Lemma lem1358961 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358962 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1358961) (@lem1358960 x)). Qed.
Lemma lem1358963 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1358962 x)). Qed.
Lemma lem1358964 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1358981 : term34 = term34.
Proof. exact (MK_COMB (@lem1358964) (@lem1358963)). Qed.
Lemma lem1358982 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1358981) (@lem1358894 h1)). Qed.
Lemma lem1358997 (z : real) (x : real) (y : real) : (((real_add x z) = (real_add y z)) = (x = y)) = (term63 z x y).
Proof. exact (@lem17784 ((real_add x z) = (real_add y z)) (x = y)). Qed.
Lemma lem1358998 (x : real) (y : real) : (term22 x y) = (term64 x y).
Proof. exact (fun_ext (fun z : real => @lem1358997 z x y)). Qed.
Lemma lem1358999 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359000 (x : real) (y : real) : (term23 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1358999) (@lem1358998 x y)). Qed.
Lemma lem1359001 (x : real) : (term24 x) = (term66 x).
Proof. exact (fun_ext (fun y : real => @lem1359000 x y)). Qed.
Lemma lem1359002 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359003 (x : real) : (term25 x) = (term67 x).
Proof. exact (MK_COMB (@lem1359002) (@lem1359001 x)). Qed.
Lemma lem1359004 : term26 = term68.
Proof. exact (fun_ext (fun x : real => @lem1359003 x)). Qed.
Lemma lem1359005 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359006 : term10 = term69.
Proof. exact (MK_COMB (@lem1359005) (@lem1359004)). Qed.
Lemma lem1359016 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1359017 (P : real -> Prop) (Q : real -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem1359016 real P Q). Qed.
Lemma lem1359018 (x : real) (y : real) : (term74 x y) = (term75 x y).
Proof. exact (@lem1359017 (term76 x y) (term77 x y)). Qed.
Lemma lem1359019 (z : real) (x : real) (y : real) : (term78 x y z) = (term79 z x y).
Proof. exact (eq_refl (term78 x y z)). Qed.
Lemma lem1359020 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359021 (z : real) (x : real) (y : real) : (term80 x y z) = (term81 z x y).
Proof. exact (MK_COMB (@lem1359020) (@lem1359019 z x y)). Qed.
Lemma lem1359022 (z : real) (x : real) (y : real) : (term82 x y z) = (term83 z x y).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1359023 (z : real) (x : real) (y : real) : (term84 x y z) = (term63 z x y).
Proof. exact (MK_COMB (@lem1359021 z x y) (@lem1359022 z x y)). Qed.
Lemma lem1359024 (x : real) (y : real) : (term85 x y) = (term64 x y).
Proof. exact (fun_ext (fun z : real => @lem1359023 z x y)). Qed.
Lemma lem1359025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359026 (x : real) (y : real) : (term74 x y) = (term65 x y).
Proof. exact (MK_COMB (@lem1359025) (@lem1359024 x y)). Qed.
Lemma lem1359027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1359028 (x : real) (y : real) : (term86 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem1359027) (@lem1359026 x y)). Qed.
Lemma lem1359029 (z : real) (x : real) (y : real) : (term78 x y z) = (term79 z x y).
Proof. exact (eq_refl (term78 x y z)). Qed.
Lemma lem1359030 (x : real) (y : real) : (term88 x y) = (term76 x y).
Proof. exact (fun_ext (fun z : real => @lem1359029 z x y)). Qed.
Lemma lem1359031 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359032 (x : real) (y : real) : (term89 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1359031) (@lem1359030 x y)). Qed.
Lemma lem1359033 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359034 (x : real) (y : real) : (term91 x y) = (term92 x y).
Proof. exact (MK_COMB (@lem1359033) (@lem1359032 x y)). Qed.
Lemma lem1359035 (z : real) (x : real) (y : real) : (term82 x y z) = (term83 z x y).
Proof. exact (eq_refl (term82 x y z)). Qed.
Lemma lem1359036 (x : real) (y : real) : (term93 x y) = (term77 x y).
Proof. exact (fun_ext (fun z : real => @lem1359035 z x y)). Qed.
Lemma lem1359037 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359038 (x : real) (y : real) : (term94 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1359037) (@lem1359036 x y)). Qed.
Lemma lem1359039 (x : real) (y : real) : (term75 x y) = (term96 x y).
Proof. exact (MK_COMB (@lem1359034 x y) (@lem1359038 x y)). Qed.
Lemma lem1359040 (x : real) (y : real) : ((term74 x y) = (term75 x y)) = ((term65 x y) = (term96 x y)).
Proof. exact (MK_COMB (@lem1359028 x y) (@lem1359039 x y)). Qed.
Lemma lem1359041 (x : real) (y : real) : (term65 x y) = (term96 x y).
Proof. exact (EQ_MP (@lem1359040 x y) (@lem1359018 x y)). Qed.
Lemma lem1359063 {A : Type'} (P : A -> Prop) (Q : Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1359064 (P : real -> Prop) (Q : Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem1359063 real P Q). Qed.
Lemma lem1359065 (x : real) (y : real) : (term101 x y) = (term102 x y).
Proof. exact (@lem1359064 (term103 x y) (term104 x y)). Qed.
Lemma lem1359066 (x : real) (y : real) (z : real) : (term105 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term105 x y z)). Qed.
Lemma lem1359067 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359068 (x : real) (y : real) (z : real) : (term106 x y z) = (term107 x y z).
Proof. exact (MK_COMB (@lem1359067) (@lem1359066 x y z)). Qed.
Lemma lem1359069 (x : real) (y : real) : (term104 x y) = (term104 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1359070 (z : real) (x : real) (y : real) : (term108 z x y) = (term79 z x y).
Proof. exact (MK_COMB (@lem1359068 x y z) (@lem1359069 x y)). Qed.
Lemma lem1359071 (x : real) (y : real) : (term109 x y) = (term76 x y).
Proof. exact (fun_ext (fun z : real => @lem1359070 z x y)). Qed.
Lemma lem1359072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359073 (x : real) (y : real) : (term101 x y) = (term90 x y).
Proof. exact (MK_COMB (@lem1359072) (@lem1359071 x y)). Qed.
Lemma lem1359074 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1359075 (x : real) (y : real) : (term110 x y) = (term111 x y).
Proof. exact (MK_COMB (@lem1359074) (@lem1359073 x y)). Qed.
Lemma lem1359076 (x : real) (y : real) (z : real) : (term105 x y z) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl (term105 x y z)). Qed.
Lemma lem1359077 (x : real) (y : real) : (term112 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1359076 x y z)). Qed.
Lemma lem1359078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359079 (x : real) (y : real) : (term113 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1359078) (@lem1359077 x y)). Qed.
Lemma lem1359080 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359081 (x : real) (y : real) : (term115 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1359080) (@lem1359079 x y)). Qed.
Lemma lem1359082 (x : real) (y : real) : (term104 x y) = (term104 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1359083 (x : real) (y : real) : (term102 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1359081 x y) (@lem1359082 x y)). Qed.
Lemma lem1359084 (x : real) (y : real) : ((term101 x y) = (term102 x y)) = ((term90 x y) = (term117 x y)).
Proof. exact (MK_COMB (@lem1359075 x y) (@lem1359083 x y)). Qed.
Lemma lem1359085 (x : real) (y : real) : (term90 x y) = (term117 x y).
Proof. exact (EQ_MP (@lem1359084 x y) (@lem1359065 x y)). Qed.
Lemma lem1359090 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359091 (x : real) (y : real) : (term92 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1359090) (@lem1359085 x y)). Qed.
Lemma lem1359113 {A : Type'} (P : A -> Prop) (Q : Prop) : (term97 A P Q) = (term98 A P Q).
Proof. exact (EQ_MP (@lem18947 A P Q) (@lem18946 A P Q)). Qed.
Lemma lem1359114 (P : real -> Prop) (Q : Prop) : (term99 P Q) = (term100 P Q).
Proof. exact (@lem1359113 real P Q). Qed.
Lemma lem1359115 (x : real) (y : real) : (term119 x y) = (term120 x y).
Proof. exact (@lem1359114 (term121 x y) (x = y)). Qed.
Lemma lem1359116 (x : real) (y : real) (z : real) : (term122 x y z) = (term123 x y z).
Proof. exact (eq_refl (term122 x y z)). Qed.
Lemma lem1359117 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359118 (x : real) (y : real) (z : real) : (term124 x y z) = (term125 x y z).
Proof. exact (MK_COMB (@lem1359117) (@lem1359116 x y z)). Qed.
Lemma lem1359119 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1359120 (z : real) (x : real) (y : real) : (term126 z x y) = (term83 z x y).
Proof. exact (MK_COMB (@lem1359118 x y z) (@lem1359119 x y)). Qed.
Lemma lem1359121 (x : real) (y : real) : (term127 x y) = (term77 x y).
Proof. exact (fun_ext (fun z : real => @lem1359120 z x y)). Qed.
Lemma lem1359122 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359123 (x : real) (y : real) : (term119 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1359122) (@lem1359121 x y)). Qed.
Lemma lem1359124 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1359125 (x : real) (y : real) : (term128 x y) = (term129 x y).
Proof. exact (MK_COMB (@lem1359124) (@lem1359123 x y)). Qed.
Lemma lem1359126 (x : real) (y : real) (z : real) : (term122 x y z) = (term123 x y z).
Proof. exact (eq_refl (term122 x y z)). Qed.
Lemma lem1359127 (x : real) (y : real) : (term130 x y) = (term121 x y).
Proof. exact (fun_ext (fun z : real => @lem1359126 x y z)). Qed.
Lemma lem1359128 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359129 (x : real) (y : real) : (term131 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1359128) (@lem1359127 x y)). Qed.
Lemma lem1359130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359131 (x : real) (y : real) : (term133 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1359130) (@lem1359129 x y)). Qed.
Lemma lem1359132 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1359133 (x : real) (y : real) : (term120 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1359131 x y) (@lem1359132 x y)). Qed.
Lemma lem1359134 (x : real) (y : real) : ((term119 x y) = (term120 x y)) = ((term95 x y) = (term135 x y)).
Proof. exact (MK_COMB (@lem1359125 x y) (@lem1359133 x y)). Qed.
Lemma lem1359135 (x : real) (y : real) : (term95 x y) = (term135 x y).
Proof. exact (EQ_MP (@lem1359134 x y) (@lem1359115 x y)). Qed.
Lemma lem1359140 (x : real) (y : real) : (term96 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1359091 x y) (@lem1359135 x y)). Qed.
Lemma lem1359141 (x : real) (y : real) : (term65 x y) = (term136 x y).
Proof. exact (TRANS (@lem1359041 x y) (@lem1359140 x y)). Qed.
Lemma lem1359142 (x : real) : (term66 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1359141 x y)). Qed.
Lemma lem1359143 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359144 (x : real) : (term67 x) = (term138 x).
Proof. exact (MK_COMB (@lem1359143) (@lem1359142 x)). Qed.
Lemma lem1359146 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1359147 (P : real -> Prop) (Q : real -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem1359146 real P Q). Qed.
Lemma lem1359148 (x : real) : (term139 x) = (term140 x).
Proof. exact (@lem1359147 (term141 x) (term142 x)). Qed.
Lemma lem1359149 (x : real) (y : real) : (term143 x y) = (term117 x y).
Proof. exact (eq_refl (term143 x y)). Qed.
Lemma lem1359150 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359151 (x : real) (y : real) : (term144 x y) = (term118 x y).
Proof. exact (MK_COMB (@lem1359150) (@lem1359149 x y)). Qed.
Lemma lem1359152 (x : real) (y : real) : (term145 x y) = (term135 x y).
Proof. exact (eq_refl (term145 x y)). Qed.
Lemma lem1359153 (x : real) (y : real) : (term146 x y) = (term136 x y).
Proof. exact (MK_COMB (@lem1359151 x y) (@lem1359152 x y)). Qed.
Lemma lem1359154 (x : real) : (term147 x) = (term137 x).
Proof. exact (fun_ext (fun y : real => @lem1359153 x y)). Qed.
Lemma lem1359155 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359156 (x : real) : (term139 x) = (term138 x).
Proof. exact (MK_COMB (@lem1359155) (@lem1359154 x)). Qed.
Lemma lem1359157 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1359158 (x : real) : (term148 x) = (term149 x).
Proof. exact (MK_COMB (@lem1359157) (@lem1359156 x)). Qed.
Lemma lem1359159 (x : real) (y : real) : (term143 x y) = (term117 x y).
Proof. exact (eq_refl (term143 x y)). Qed.
Lemma lem1359160 (x : real) : (term150 x) = (term141 x).
Proof. exact (fun_ext (fun y : real => @lem1359159 x y)). Qed.
Lemma lem1359161 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359162 (x : real) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem1359161) (@lem1359160 x)). Qed.
Lemma lem1359163 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359164 (x : real) : (term153 x) = (term154 x).
Proof. exact (MK_COMB (@lem1359163) (@lem1359162 x)). Qed.
Lemma lem1359165 (x : real) (y : real) : (term145 x y) = (term135 x y).
Proof. exact (eq_refl (term145 x y)). Qed.
Lemma lem1359166 (x : real) : (term155 x) = (term142 x).
Proof. exact (fun_ext (fun y : real => @lem1359165 x y)). Qed.
Lemma lem1359167 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359168 (x : real) : (term156 x) = (term157 x).
Proof. exact (MK_COMB (@lem1359167) (@lem1359166 x)). Qed.
Lemma lem1359169 (x : real) : (term140 x) = (term158 x).
Proof. exact (MK_COMB (@lem1359164 x) (@lem1359168 x)). Qed.
Lemma lem1359170 (x : real) : ((term139 x) = (term140 x)) = ((term138 x) = (term158 x)).
Proof. exact (MK_COMB (@lem1359158 x) (@lem1359169 x)). Qed.
Lemma lem1359171 (x : real) : (term138 x) = (term158 x).
Proof. exact (EQ_MP (@lem1359170 x) (@lem1359148 x)). Qed.
Lemma lem1359276 (x : real) : (term67 x) = (term158 x).
Proof. exact (TRANS (@lem1359144 x) (@lem1359171 x)). Qed.
Lemma lem1359277 : term68 = term159.
Proof. exact (fun_ext (fun x : real => @lem1359276 x)). Qed.
Lemma lem1359278 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359279 : term69 = term160.
Proof. exact (MK_COMB (@lem1359278) (@lem1359277)). Qed.
Lemma lem1359281 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1359282 (P : real -> Prop) (Q : real -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem1359281 real P Q). Qed.
Lemma lem1359283 : term161 = term162.
Proof. exact (@lem1359282 term163 term164). Qed.
Lemma lem1359284 (x : real) : (term165 x) = (term152 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1359285 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359286 (x : real) : (term166 x) = (term154 x).
Proof. exact (MK_COMB (@lem1359285) (@lem1359284 x)). Qed.
Lemma lem1359287 (x : real) : (term167 x) = (term157 x).
Proof. exact (eq_refl (term167 x)). Qed.
Lemma lem1359288 (x : real) : (term168 x) = (term158 x).
Proof. exact (MK_COMB (@lem1359286 x) (@lem1359287 x)). Qed.
Lemma lem1359289 : term169 = term159.
Proof. exact (fun_ext (fun x : real => @lem1359288 x)). Qed.
Lemma lem1359290 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359291 : term161 = term160.
Proof. exact (MK_COMB (@lem1359290) (@lem1359289)). Qed.
Lemma lem1359292 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1359293 : term170 = term171.
Proof. exact (MK_COMB (@lem1359292) (@lem1359291)). Qed.
Lemma lem1359294 (x : real) : (term165 x) = (term152 x).
Proof. exact (eq_refl (term165 x)). Qed.
Lemma lem1359295 : term172 = term163.
Proof. exact (fun_ext (fun x : real => @lem1359294 x)). Qed.
Lemma lem1359296 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359297 : term173 = term174.
Proof. exact (MK_COMB (@lem1359296) (@lem1359295)). Qed.
Lemma lem1359298 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359299 : term175 = term176.
Proof. exact (MK_COMB (@lem1359298) (@lem1359297)). Qed.
Lemma lem1359300 (x : real) : (term167 x) = (term157 x).
Proof. exact (eq_refl (term167 x)). Qed.
Lemma lem1359301 : term177 = term164.
Proof. exact (fun_ext (fun x : real => @lem1359300 x)). Qed.
Lemma lem1359302 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359303 : term178 = term179.
Proof. exact (MK_COMB (@lem1359302) (@lem1359301)). Qed.
Lemma lem1359304 : term162 = term180.
Proof. exact (MK_COMB (@lem1359299) (@lem1359303)). Qed.
Lemma lem1359305 : (term161 = term162) = (term160 = term180).
Proof. exact (MK_COMB (@lem1359293) (@lem1359304)). Qed.
Lemma lem1359306 : term160 = term180.
Proof. exact (EQ_MP (@lem1359305) (@lem1359283)). Qed.
Lemma lem1359421 : term69 = term180.
Proof. exact (TRANS (@lem1359279) (@lem1359306)). Qed.
Lemma lem1359422 : term10 = term180.
Proof. exact (TRANS (@lem1359006) (@lem1359421)). Qed.
Lemma lem1359423 (h1 : term10) : term180.
Proof. exact (EQ_MP (@lem1359422) (@lem1358895 h1)). Qed.
Lemma lem1359424 (x : real) (h1 : term56 x) : term56 x.
Proof. exact (h1). Qed.
Lemma lem1359442 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1359443 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1359442 x)). Qed.
Lemma lem1359444 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359445 : term41 = term41.
Proof. exact (MK_COMB (@lem1359444) (@lem1359443)). Qed.
Lemma lem1359446 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1359445) (@lem1358942 h1)). Qed.
Lemma lem1359461 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1359462 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1359461 x)). Qed.
Lemma lem1359463 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359464 : term38 = term38.
Proof. exact (MK_COMB (@lem1359463) (@lem1359462)). Qed.
Lemma lem1359465 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1359464) (@lem1358955 h1)). Qed.
Lemma lem1359490 (y : real) (x : real) (z : real) : ((term27 x y z) = (term28 y x z)) = ((term27 x y z) = (term28 y x z)).
Proof. exact (eq_refl ((term27 x y z) = (term28 y x z))). Qed.
Lemma lem1359491 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (fun_ext (fun z : real => @lem1359490 y x z)). Qed.
Lemma lem1359492 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359493 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem1359492) (@lem1359491 y x)). Qed.
Lemma lem1359494 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1359493 y x)). Qed.
Lemma lem1359495 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359496 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1359495) (@lem1359494 x)). Qed.
Lemma lem1359497 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1359496 x)). Qed.
Lemma lem1359498 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359499 : term34 = term34.
Proof. exact (MK_COMB (@lem1359498) (@lem1359497)). Qed.
Lemma lem1359500 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1359499) (@lem1358982 h1)). Qed.
Lemma lem1359505 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1359520 (x : real) (y : real) (z : real) : (term123 x y z) = (term123 x y z).
Proof. exact (eq_refl (term123 x y z)). Qed.
Lemma lem1359521 (x : real) (y : real) : (term121 x y) = (term121 x y).
Proof. exact (fun_ext (fun z : real => @lem1359520 x y z)). Qed.
Lemma lem1359522 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359523 (x : real) (y : real) : (term132 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1359522) (@lem1359521 x y)). Qed.
Lemma lem1359524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359525 (x : real) (y : real) : (term134 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1359524) (@lem1359523 x y)). Qed.
Lemma lem1359526 (x : real) (y : real) : (term135 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1359525 x y) (@lem1359505 x y)). Qed.
Lemma lem1359527 (x : real) : (term142 x) = (term142 x).
Proof. exact (fun_ext (fun y : real => @lem1359526 x y)). Qed.
Lemma lem1359528 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359529 (x : real) : (term157 x) = (term157 x).
Proof. exact (MK_COMB (@lem1359528) (@lem1359527 x)). Qed.
Lemma lem1359530 : term164 = term164.
Proof. exact (fun_ext (fun x : real => @lem1359529 x)). Qed.
Lemma lem1359531 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359532 : term179 = term179.
Proof. exact (MK_COMB (@lem1359531) (@lem1359530)). Qed.
Lemma lem1359539 (x : real) (y : real) : (term104 x y) = (term104 x y).
Proof. exact (eq_refl (term104 x y)). Qed.
Lemma lem1359552 (x : real) (y : real) (z : real) : ((real_add x z) = (real_add y z)) = ((real_add x z) = (real_add y z)).
Proof. exact (eq_refl ((real_add x z) = (real_add y z))). Qed.
Lemma lem1359553 (x : real) (y : real) : (term103 x y) = (term103 x y).
Proof. exact (fun_ext (fun z : real => @lem1359552 x y z)). Qed.
Lemma lem1359554 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359555 (x : real) (y : real) : (term114 x y) = (term114 x y).
Proof. exact (MK_COMB (@lem1359554) (@lem1359553 x y)). Qed.
Lemma lem1359556 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359557 (x : real) (y : real) : (term116 x y) = (term116 x y).
Proof. exact (MK_COMB (@lem1359556) (@lem1359555 x y)). Qed.
Lemma lem1359558 (x : real) (y : real) : (term117 x y) = (term117 x y).
Proof. exact (MK_COMB (@lem1359557 x y) (@lem1359539 x y)). Qed.
Lemma lem1359559 (x : real) : (term141 x) = (term141 x).
Proof. exact (fun_ext (fun y : real => @lem1359558 x y)). Qed.
Lemma lem1359560 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359561 (x : real) : (term152 x) = (term152 x).
Proof. exact (MK_COMB (@lem1359560) (@lem1359559 x)). Qed.
Lemma lem1359562 : term163 = term163.
Proof. exact (fun_ext (fun x : real => @lem1359561 x)). Qed.
Lemma lem1359563 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359564 : term174 = term174.
Proof. exact (MK_COMB (@lem1359563) (@lem1359562)). Qed.
Lemma lem1359565 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359566 : term176 = term176.
Proof. exact (MK_COMB (@lem1359565) (@lem1359564)). Qed.
Lemma lem1359567 : term180 = term180.
Proof. exact (MK_COMB (@lem1359566) (@lem1359532)). Qed.
Lemma lem1359568 (h1 : term10) : term180.
Proof. exact (EQ_MP (@lem1359567) (@lem1359423 h1)). Qed.
Lemma lem1359588 (x : real) (y : real) (h1 : term53 x y) : term53 x y.
Proof. exact (h1). Qed.
Lemma lem1359589 (h1 : term10) : term179.
Proof. exact (proj2 (@lem1359568 h1)). Qed.
Lemma lem1359592 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1359593 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1359592 x)). Qed.
Lemma lem1359594 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359596 : term41 = term41.
Proof. exact (MK_COMB (@lem1359594) (@lem1359593)). Qed.
Lemma lem1359597 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1359596) (@lem1359446 h1)). Qed.
Lemma lem1359599 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1359600 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1359599 x)). Qed.
Lemma lem1359601 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359603 : term38 = term38.
Proof. exact (MK_COMB (@lem1359601) (@lem1359600)). Qed.
Lemma lem1359604 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1359603) (@lem1359465 h1)). Qed.
Lemma lem1359606 (y : real) (x : real) (z : real) : ((term27 x y z) = (term28 y x z)) = ((term27 x y z) = (term28 y x z)).
Proof. exact (eq_refl ((term27 x y z) = (term28 y x z))). Qed.
Lemma lem1359607 (y : real) (x : real) : (term29 y x) = (term29 y x).
Proof. exact (fun_ext (fun z : real => @lem1359606 y x z)). Qed.
Lemma lem1359608 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359609 (y : real) (x : real) : (term30 y x) = (term30 y x).
Proof. exact (MK_COMB (@lem1359608) (@lem1359607 y x)). Qed.
Lemma lem1359610 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1359609 y x)). Qed.
Lemma lem1359611 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359612 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1359611) (@lem1359610 x)). Qed.
Lemma lem1359613 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1359612 x)). Qed.
Lemma lem1359614 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359616 : term34 = term34.
Proof. exact (MK_COMB (@lem1359614) (@lem1359613)). Qed.
Lemma lem1359617 (h1 : term34) : term34.
Proof. exact (EQ_MP (@lem1359616) (@lem1359500 h1)). Qed.
Lemma lem1359621 (x : real) (y : real) (h1 : term53 x y) : term53 x y.
Proof. exact (h1). Qed.
Lemma lem1359671 {A : Type'} (P : A -> Prop) (Q : Prop) : (term98 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem1359672 (P : real -> Prop) (Q : Prop) : (term100 P Q) = (term99 P Q).
Proof. exact (@lem1359671 real P Q). Qed.
Lemma lem1359673 (x : real) (y : real) : (term120 x y) = (term119 x y).
Proof. exact (@lem1359672 (term121 x y) (x = y)). Qed.
Lemma lem1359674 (x : real) (y : real) (z : real) : (term122 x y z) = (term123 x y z).
Proof. exact (eq_refl (term122 x y z)). Qed.
Lemma lem1359675 (x : real) (y : real) : (term130 x y) = (term121 x y).
Proof. exact (fun_ext (fun z : real => @lem1359674 x y z)). Qed.
Lemma lem1359676 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359677 (x : real) (y : real) : (term131 x y) = (term132 x y).
Proof. exact (MK_COMB (@lem1359676) (@lem1359675 x y)). Qed.
Lemma lem1359678 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359679 (x : real) (y : real) : (term133 x y) = (term134 x y).
Proof. exact (MK_COMB (@lem1359678) (@lem1359677 x y)). Qed.
Lemma lem1359680 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1359681 (x : real) (y : real) : (term120 x y) = (term135 x y).
Proof. exact (MK_COMB (@lem1359679 x y) (@lem1359680 x y)). Qed.
Lemma lem1359682 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1359683 (x : real) (y : real) : (term181 x y) = (term182 x y).
Proof. exact (MK_COMB (@lem1359682) (@lem1359681 x y)). Qed.
Lemma lem1359684 (x : real) (y : real) (z : real) : (term122 x y z) = (term123 x y z).
Proof. exact (eq_refl (term122 x y z)). Qed.
Lemma lem1359685 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1359686 (x : real) (y : real) (z : real) : (term124 x y z) = (term125 x y z).
Proof. exact (MK_COMB (@lem1359685) (@lem1359684 x y z)). Qed.
Lemma lem1359687 (x : real) (y : real) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem1359688 (z : real) (x : real) (y : real) : (term126 z x y) = (term83 z x y).
Proof. exact (MK_COMB (@lem1359686 x y z) (@lem1359687 x y)). Qed.
Lemma lem1359689 (x : real) (y : real) : (term127 x y) = (term77 x y).
Proof. exact (fun_ext (fun z : real => @lem1359688 z x y)). Qed.
Lemma lem1359690 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359691 (x : real) (y : real) : (term119 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1359690) (@lem1359689 x y)). Qed.
Lemma lem1359692 (x : real) (y : real) : ((term120 x y) = (term119 x y)) = ((term135 x y) = (term95 x y)).
Proof. exact (MK_COMB (@lem1359683 x y) (@lem1359691 x y)). Qed.
Lemma lem1359693 (x : real) (y : real) : (term135 x y) = (term95 x y).
Proof. exact (EQ_MP (@lem1359692 x y) (@lem1359673 x y)). Qed.
Lemma lem1359694 (x : real) : (term142 x) = (term183 x).
Proof. exact (fun_ext (fun y : real => @lem1359693 x y)). Qed.
Lemma lem1359695 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359696 (x : real) : (term157 x) = (term184 x).
Proof. exact (MK_COMB (@lem1359695) (@lem1359694 x)). Qed.
Lemma lem1359697 : term164 = term185.
Proof. exact (fun_ext (fun x : real => @lem1359696 x)). Qed.
Lemma lem1359698 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359699 : term179 = term186.
Proof. exact (MK_COMB (@lem1359698) (@lem1359697)). Qed.
Lemma lem1359706 (z : real) (x : real) (y : real) : (term83 z x y) = (term83 z x y).
Proof. exact (eq_refl (term83 z x y)). Qed.
Lemma lem1359707 (x : real) (y : real) : (term77 x y) = (term77 x y).
Proof. exact (fun_ext (fun z : real => @lem1359706 z x y)). Qed.
Lemma lem1359708 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359709 (x : real) (y : real) : (term95 x y) = (term95 x y).
Proof. exact (MK_COMB (@lem1359708) (@lem1359707 x y)). Qed.
Lemma lem1359710 (x : real) : (term183 x) = (term183 x).
Proof. exact (fun_ext (fun y : real => @lem1359709 x y)). Qed.
Lemma lem1359711 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359712 (x : real) : (term184 x) = (term184 x).
Proof. exact (MK_COMB (@lem1359711) (@lem1359710 x)). Qed.
Lemma lem1359713 : term185 = term185.
Proof. exact (fun_ext (fun x : real => @lem1359712 x)). Qed.
Lemma lem1359714 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1359715 : term186 = term186.
Proof. exact (MK_COMB (@lem1359714) (@lem1359713)). Qed.
Lemma lem1359716 : term179 = term186.
Proof. exact (TRANS (@lem1359699) (@lem1359715)). Qed.
Lemma lem1359717 (h1 : term10) : term186.
Proof. exact (EQ_MP (@lem1359716) (@lem1359589 h1)). Qed.
Lemma lem1359718 (_24170 : real) (h1 : term41) : term187 _24170.
Proof. exact (@lem1359597 h1 _24170). Qed.
Lemma lem1359719 (_24170 : real) : (term187 _24170) = ((term39 _24170) = term36).
Proof. exact (eq_refl (term187 _24170)). Qed.
Lemma lem1359721 (_24171 : real) (h1 : term38) : term188 _24171.
Proof. exact (@lem1359604 h1 _24171). Qed.
Lemma lem1359722 (_24171 : real) : (term188 _24171) = ((term35 _24171) = term36).
Proof. exact (eq_refl (term188 _24171)). Qed.
Lemma lem1359724 (_24172 : real) (h1 : term34) : term189 _24172.
Proof. exact (@lem1359617 h1 _24172). Qed.
Lemma lem1359725 (_24172 : real) : (term189 _24172) = (term32 _24172).
Proof. exact (eq_refl (term189 _24172)). Qed.
Lemma lem1359726 (_24172 : real) (h1 : term34) : term32 _24172.
Proof. exact (EQ_MP (@lem1359725 _24172) (@lem1359724 _24172 h1)). Qed.
Lemma lem1359727 (_24172 : real) (_24173 : real) (h1 : term34) : term190 _24172 _24173.
Proof. exact (@lem1359726 _24172 h1 _24173). Qed.
Lemma lem1359728 (_24173 : real) (_24172 : real) : (term190 _24172 _24173) = (term30 _24173 _24172).
Proof. exact (eq_refl (term190 _24172 _24173)). Qed.
Lemma lem1359729 (_24173 : real) (_24172 : real) (h1 : term34) : term30 _24173 _24172.
Proof. exact (EQ_MP (@lem1359728 _24173 _24172) (@lem1359727 _24172 _24173 h1)). Qed.
Lemma lem1359730 (_24173 : real) (_24172 : real) (_24174 : real) (h1 : term34) : term191 _24173 _24172 _24174.
Proof. exact (@lem1359729 _24173 _24172 h1 _24174). Qed.
Lemma lem1359731 (_24173 : real) (_24172 : real) (_24174 : real) : (term191 _24173 _24172 _24174) = ((term27 _24172 _24173 _24174) = (term28 _24173 _24172 _24174)).
Proof. exact (eq_refl (term191 _24173 _24172 _24174)). Qed.
Lemma lem1359742 (_24178 : real) (h1 : term10) : term192 _24178.
Proof. exact (@lem1359717 h1 _24178). Qed.
Lemma lem1359743 (_24178 : real) : (term192 _24178) = (term184 _24178).
Proof. exact (eq_refl (term192 _24178)). Qed.
Lemma lem1359744 (_24178 : real) (h1 : term10) : term184 _24178.
Proof. exact (EQ_MP (@lem1359743 _24178) (@lem1359742 _24178 h1)). Qed.
Lemma lem1359745 (_24178 : real) (_24179 : real) (h1 : term10) : term193 _24178 _24179.
Proof. exact (@lem1359744 _24178 h1 _24179). Qed.
Lemma lem1359746 (_24178 : real) (_24179 : real) : (term193 _24178 _24179) = (term95 _24178 _24179).
Proof. exact (eq_refl (term193 _24178 _24179)). Qed.
Lemma lem1359747 (_24178 : real) (_24179 : real) (h1 : term10) : term95 _24178 _24179.
Proof. exact (EQ_MP (@lem1359746 _24178 _24179) (@lem1359745 _24178 _24179 h1)). Qed.
Lemma lem1359748 (_24178 : real) (_24179 : real) (_24180 : real) (h1 : term10) : term82 _24178 _24179 _24180.
Proof. exact (@lem1359747 _24178 _24179 h1 _24180). Qed.
Lemma lem1359749 (_24180 : real) (_24178 : real) (_24179 : real) : (term82 _24178 _24179 _24180) = (term83 _24180 _24178 _24179).
Proof. exact (eq_refl (term82 _24178 _24179 _24180)). Qed.
Lemma lem1359758 (x : real) (y : real) (h1 : term53 x y) : term53 x y.
Proof. exact (h1). Qed.
Lemma lem1359770 (_24180 : real) (_24178 : real) (_24179 : real) (h1 : term10) : term83 _24180 _24178 _24179.
Proof. exact (EQ_MP (@lem1359749 _24180 _24178 _24179) (@lem1359748 _24178 _24179 _24180 h1)). Qed.
Lemma lem1359794 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem1359795 (_24187 : real) (_24189 : real) (h1 : _24187 = _24189) : _24187 = _24189.
Proof. exact (h1). Qed.
Lemma lem1359796 (_24188 : real) (_24190 : real) (h1 : _24188 = _24190) : _24188 = _24190.
Proof. exact (h1). Qed.
Lemma lem1359797 (_24187 : real) (_24189 : real) (h1 : _24187 = _24189) : (real_mul _24187) = (real_mul _24189).
Proof. exact (MK_COMB (@lem1359794) (@lem1359795 _24187 _24189 h1)). Qed.
Lemma lem1359798 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) (h1 : _24187 = _24189) (h2 : _24188 = _24190) : (real_mul _24187 _24188) = (real_mul _24189 _24190).
Proof. exact (MK_COMB (@lem1359797 _24187 _24189 h1) (@lem1359796 _24188 _24190 h2)). Qed.
Lemma lem1359799 (_24188 : real) (_24190 : real) (_24187 : real) (_24189 : real) (h1 : _24187 = _24189) : term194 _24187 _24188 _24189 _24190.
Proof. exact (fun h0 : _24188 = _24190 => @lem1359798 _24187 _24189 _24188 _24190 h1 h0). Qed.
Lemma lem1359801 (a : Prop) (b : Prop) : (a -> b) = (term195 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1359802 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : (term194 _24187 _24188 _24189 _24190) = (term196 _24187 _24188 _24189 _24190).
Proof. exact (@lem1359801 (_24188 = _24190) ((real_mul _24187 _24188) = (real_mul _24189 _24190))). Qed.
Lemma lem1359803 (_24188 : real) (_24190 : real) (_24187 : real) (_24189 : real) (h1 : _24187 = _24189) : term196 _24187 _24188 _24189 _24190.
Proof. exact (EQ_MP (@lem1359802 _24187 _24188 _24189 _24190) (@lem1359799 _24188 _24190 _24187 _24189 h1)). Qed.
Lemma lem1359804 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : term197 _24187 _24188 _24189 _24190.
Proof. exact (fun h0 : _24187 = _24189 => @lem1359803 _24188 _24190 _24187 _24189 h0). Qed.
Lemma lem1359806 (a : Prop) (b : Prop) : (a -> b) = (term195 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1359807 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : (term197 _24187 _24188 _24189 _24190) = (term198 _24187 _24188 _24189 _24190).
Proof. exact (@lem1359806 (_24187 = _24189) (term196 _24187 _24188 _24189 _24190)). Qed.
Lemma lem1359808 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : term198 _24187 _24188 _24189 _24190.
Proof. exact (EQ_MP (@lem1359807 _24187 _24188 _24189 _24190) (@lem1359804 _24187 _24188 _24189 _24190)). Qed.
Lemma lem1359826 (x : real) (y : real) (z : real) : term199 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1359830 (_24170 : real) (h1 : term41) : (term39 _24170) = term36.
Proof. exact (EQ_MP (@lem1359719 _24170) (@lem1359718 _24170 h1)). Qed.
Lemma lem1359831 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (@lem1359830 x h1). Qed.
Lemma lem1359832 (x : real) (h1 : term41) : term200 x.
Proof. exact (fun h0 : term201 x => @lem1359831 x h1). Qed.
Lemma lem1359834 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1359835 (x : real) : (term200 x) = ((term39 x) = term36).
Proof. exact (@lem1359834 ((term39 x) = term36)). Qed.
Lemma lem1359836 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (EQ_MP (@lem1359835 x) (@lem1359832 x h1)). Qed.
Lemma lem1359838 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1359839 (x : real) : term203 x.
Proof. exact (fun h0 : term204 x => @lem1359838 x). Qed.
Lemma lem1359841 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1359842 (x : real) : (term203 x) = (x = x).
Proof. exact (@lem1359841 (x = x)). Qed.
Lemma lem1359843 (x : real) : x = x.
Proof. exact (EQ_MP (@lem1359842 x) (@lem1359839 x)). Qed.
Lemma lem1359845 (_24171 : real) (h1 : term38) : (term35 _24171) = term36.
Proof. exact (EQ_MP (@lem1359722 _24171) (@lem1359721 _24171 h1)). Qed.
Lemma lem1359846 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (@lem1359845 y h1). Qed.
Lemma lem1359847 (y : real) (h1 : term38) : term205 y.
Proof. exact (fun h0 : term206 y => @lem1359846 y h1). Qed.
Lemma lem1359849 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1359850 (y : real) : (term205 y) = ((term35 y) = term36).
Proof. exact (@lem1359849 ((term35 y) = term36)). Qed.
Lemma lem1359851 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (EQ_MP (@lem1359850 y) (@lem1359847 y h1)). Qed.
Lemma lem1359869 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1359870 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term196 _24187 _24188 _24189 _24190) = (term207 _24187 _24189 _24188 _24190).
Proof. exact (@lem1359869 ((real_mul _24187 _24188) = (real_mul _24189 _24190)) (term104 _24188 _24190)). Qed.
Lemma lem1359880 (_24187 : real) (_24189 : real) : (term208 _24187 _24189) = (term208 _24187 _24189).
Proof. exact (eq_refl (term208 _24187 _24189)). Qed.
Lemma lem1359881 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term198 _24187 _24188 _24189 _24190) = (term209 _24187 _24189 _24188 _24190).
Proof. exact (MK_COMB (@lem1359880 _24187 _24189) (@lem1359870 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359885 (q : Prop) (p : Prop) (r : Prop) : (term210 p q r) = (term210 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1359886 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term209 _24187 _24189 _24188 _24190) = (term211 _24187 _24189 _24188 _24190).
Proof. exact (@lem1359885 ((real_mul _24187 _24188) = (real_mul _24189 _24190)) (term104 _24187 _24189) (term104 _24188 _24190)). Qed.
Lemma lem1359908 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term198 _24187 _24188 _24189 _24190) = (term211 _24187 _24189 _24188 _24190).
Proof. exact (TRANS (@lem1359881 _24187 _24189 _24188 _24190) (@lem1359886 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359909 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1359910 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term212 _24187 _24188 _24189 _24190) = (term213 _24187 _24189 _24188 _24190).
Proof. exact (MK_COMB (@lem1359909) (@lem1359908 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359932 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term211 _24187 _24189 _24188 _24190) = (term211 _24187 _24189 _24188 _24190).
Proof. exact (eq_refl (term211 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359933 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : ((term198 _24187 _24188 _24189 _24190) = (term211 _24187 _24189 _24188 _24190)) = ((term211 _24187 _24189 _24188 _24190) = (term211 _24187 _24189 _24188 _24190)).
Proof. exact (MK_COMB (@lem1359910 _24187 _24189 _24188 _24190) (@lem1359932 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359935 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1359936 (x : Prop) : (x = x) = True.
Proof. exact (@lem1359935 Prop x). Qed.
Lemma lem1359937 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : ((term211 _24187 _24189 _24188 _24190) = (term211 _24187 _24189 _24188 _24190)) = True.
Proof. exact (@lem1359936 (term211 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359938 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : ((term198 _24187 _24188 _24189 _24190) = (term211 _24187 _24189 _24188 _24190)) = True.
Proof. exact (TRANS (@lem1359933 _24187 _24189 _24188 _24190) (@lem1359937 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359939 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : True = ((term198 _24187 _24188 _24189 _24190) = (term211 _24187 _24189 _24188 _24190)).
Proof. exact (SYM (@lem1359938 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359940 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term198 _24187 _24188 _24189 _24190) = (term211 _24187 _24189 _24188 _24190).
Proof. exact (EQ_MP (@lem1359939 _24187 _24189 _24188 _24190) (@lem0)). Qed.
Lemma lem1359941 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : term211 _24187 _24189 _24188 _24190.
Proof. exact (EQ_MP (@lem1359940 _24187 _24189 _24188 _24190) (@lem1359808 _24187 _24188 _24189 _24190)). Qed.
Lemma lem1359943 (b : Prop) (a : Prop) : (a \/ b) = (term214 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1359944 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : (term211 _24187 _24189 _24188 _24190) = (term215 _24187 _24188 _24189 _24190).
Proof. exact (@lem1359943 (term216 _24187 _24189 _24188 _24190) ((real_mul _24187 _24188) = (real_mul _24189 _24190))). Qed.
Lemma lem1359946 (a : Prop) (b : Prop) : (term217 a b) = (term218 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1359947 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term219 _24187 _24189 _24188 _24190) = (term220 _24187 _24189 _24188 _24190).
Proof. exact (@lem1359946 (term104 _24187 _24189) (term104 _24188 _24190)). Qed.
Lemma lem1359949 (a : Prop) : (term221 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1359950 (_24187 : real) (_24189 : real) : (term222 _24187 _24189) = (_24187 = _24189).
Proof. exact (@lem1359949 (_24187 = _24189)). Qed.
Lemma lem1359951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1359952 (_24187 : real) (_24189 : real) : (term223 _24187 _24189) = (term224 _24187 _24189).
Proof. exact (MK_COMB (@lem1359951) (@lem1359950 _24187 _24189)). Qed.
Lemma lem1359954 (a : Prop) : (term221 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1359955 (_24188 : real) (_24190 : real) : (term222 _24188 _24190) = (_24188 = _24190).
Proof. exact (@lem1359954 (_24188 = _24190)). Qed.
Lemma lem1359956 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term220 _24187 _24189 _24188 _24190) = (term225 _24187 _24189 _24188 _24190).
Proof. exact (MK_COMB (@lem1359952 _24187 _24189) (@lem1359955 _24188 _24190)). Qed.
Lemma lem1359957 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term219 _24187 _24189 _24188 _24190) = (term225 _24187 _24189 _24188 _24190).
Proof. exact (TRANS (@lem1359947 _24187 _24189 _24188 _24190) (@lem1359956 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359958 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1359959 (_24187 : real) (_24189 : real) (_24188 : real) (_24190 : real) : (term226 _24187 _24189 _24188 _24190) = (term227 _24187 _24189 _24188 _24190).
Proof. exact (MK_COMB (@lem1359958) (@lem1359957 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359960 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : ((real_mul _24187 _24188) = (real_mul _24189 _24190)) = ((real_mul _24187 _24188) = (real_mul _24189 _24190)).
Proof. exact (eq_refl ((real_mul _24187 _24188) = (real_mul _24189 _24190))). Qed.
Lemma lem1359961 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : (term215 _24187 _24188 _24189 _24190) = (term228 _24187 _24188 _24189 _24190).
Proof. exact (MK_COMB (@lem1359959 _24187 _24189 _24188 _24190) (@lem1359960 _24187 _24188 _24189 _24190)). Qed.
Lemma lem1359962 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : (term211 _24187 _24189 _24188 _24190) = (term228 _24187 _24188 _24189 _24190).
Proof. exact (TRANS (@lem1359944 _24187 _24188 _24189 _24190) (@lem1359961 _24187 _24188 _24189 _24190)). Qed.
Lemma lem1359964 (x : real) (y : real) (h1 : term38) : term229 x y.
Proof. exact (conj (@lem1359843 x) (@lem1359851 y h1)). Qed.
Lemma lem1359966 (_24187 : real) (_24188 : real) (_24189 : real) (_24190 : real) : term228 _24187 _24188 _24189 _24190.
Proof. exact (EQ_MP (@lem1359962 _24187 _24188 _24189 _24190) (@lem1359941 _24187 _24189 _24188 _24190)). Qed.
Lemma lem1359967 (y : real) (x : real) : term230 y x.
Proof. exact (@lem1359966 x (term35 y) x term36). Qed.
Lemma lem1359970 (y : real) (x : real) (h1 : term38) : (term231 x y) = (term39 x).
Proof. exact (@lem1359967 y x (@lem1359964 x y h1)). Qed.
Lemma lem1359971 (y : real) (x : real) (h1 : term38) : term232 y x.
Proof. exact (fun h0 : term233 y x => @lem1359970 y x h1). Qed.
Lemma lem1359973 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1359974 (y : real) (x : real) : (term232 y x) = ((term231 x y) = (term39 x)).
Proof. exact (@lem1359973 ((term231 x y) = (term39 x))). Qed.
Lemma lem1359975 (y : real) (x : real) (h1 : term38) : (term231 x y) = (term39 x).
Proof. exact (EQ_MP (@lem1359974 y x) (@lem1359971 y x h1)). Qed.
Lemma lem1359977 (_24173 : real) (_24172 : real) (_24174 : real) (h1 : term34) : (term27 _24172 _24173 _24174) = (term28 _24173 _24172 _24174).
Proof. exact (EQ_MP (@lem1359731 _24173 _24172 _24174) (@lem1359730 _24173 _24172 _24174 h1)). Qed.
Lemma lem1359978 (x : real) (y : real) (h1 : term34) : (term231 x y) = (term234 x y).
Proof. exact (@lem1359977 (real_neg y) x y h1). Qed.
Lemma lem1359979 (x : real) (y : real) (h1 : term34) : term235 x y.
Proof. exact (fun h0 : term236 x y => @lem1359978 x y h1). Qed.
Lemma lem1359981 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1359982 (x : real) (y : real) : (term235 x y) = ((term231 x y) = (term234 x y)).
Proof. exact (@lem1359981 ((term231 x y) = (term234 x y))). Qed.
Lemma lem1359983 (x : real) (y : real) (h1 : term34) : (term231 x y) = (term234 x y).
Proof. exact (EQ_MP (@lem1359982 x y) (@lem1359979 x y h1)). Qed.
Lemma lem1360001 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1360002 (y : real) (x : real) (z : real) : (term237 x y z) = (term238 y x z).
Proof. exact (@lem1360001 (y = z) (term104 x z)). Qed.
Lemma lem1360012 (x : real) (y : real) : (term208 x y) = (term208 x y).
Proof. exact (eq_refl (term208 x y)). Qed.
Lemma lem1360013 (y : real) (x : real) (z : real) : (term199 x y z) = (term239 y x z).
Proof. exact (MK_COMB (@lem1360012 x y) (@lem1360002 y x z)). Qed.
Lemma lem1360017 (q : Prop) (p : Prop) (r : Prop) : (term210 p q r) = (term210 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1360018 (y : real) (x : real) (z : real) : (term239 y x z) = (term240 y x z).
Proof. exact (@lem1360017 (y = z) (term104 x y) (term104 x z)). Qed.
Lemma lem1360040 (y : real) (x : real) (z : real) : (term199 x y z) = (term240 y x z).
Proof. exact (TRANS (@lem1360013 y x z) (@lem1360018 y x z)). Qed.
Lemma lem1360041 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1360042 (y : real) (x : real) (z : real) : (term241 x y z) = (term242 y x z).
Proof. exact (MK_COMB (@lem1360041) (@lem1360040 y x z)). Qed.
Lemma lem1360064 (y : real) (x : real) (z : real) : (term240 y x z) = (term240 y x z).
Proof. exact (eq_refl (term240 y x z)). Qed.
Lemma lem1360065 (y : real) (x : real) (z : real) : ((term199 x y z) = (term240 y x z)) = ((term240 y x z) = (term240 y x z)).
Proof. exact (MK_COMB (@lem1360042 y x z) (@lem1360064 y x z)). Qed.
Lemma lem1360067 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1360068 (x : Prop) : (x = x) = True.
Proof. exact (@lem1360067 Prop x). Qed.
Lemma lem1360069 (y : real) (x : real) (z : real) : ((term240 y x z) = (term240 y x z)) = True.
Proof. exact (@lem1360068 (term240 y x z)). Qed.
Lemma lem1360070 (y : real) (x : real) (z : real) : ((term199 x y z) = (term240 y x z)) = True.
Proof. exact (TRANS (@lem1360065 y x z) (@lem1360069 y x z)). Qed.
Lemma lem1360071 (y : real) (x : real) (z : real) : True = ((term199 x y z) = (term240 y x z)).
Proof. exact (SYM (@lem1360070 y x z)). Qed.
Lemma lem1360072 (y : real) (x : real) (z : real) : (term199 x y z) = (term240 y x z).
Proof. exact (EQ_MP (@lem1360071 y x z) (@lem0)). Qed.
Lemma lem1360073 (y : real) (x : real) (z : real) : term240 y x z.
Proof. exact (EQ_MP (@lem1360072 y x z) (@lem1359826 x y z)). Qed.
Lemma lem1360075 (b : Prop) (a : Prop) : (a \/ b) = (term214 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1360076 (x : real) (y : real) (z : real) : (term240 y x z) = (term243 x y z).
Proof. exact (@lem1360075 (term244 y x z) (y = z)). Qed.
Lemma lem1360078 (a : Prop) (b : Prop) : (term217 a b) = (term218 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1360079 (y : real) (x : real) (z : real) : (term245 y x z) = (term246 y x z).
Proof. exact (@lem1360078 (term104 x y) (term104 x z)). Qed.
Lemma lem1360081 (a : Prop) : (term221 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1360082 (x : real) (y : real) : (term222 x y) = (x = y).
Proof. exact (@lem1360081 (x = y)). Qed.
Lemma lem1360083 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1360084 (x : real) (y : real) : (term223 x y) = (term224 x y).
Proof. exact (MK_COMB (@lem1360083) (@lem1360082 x y)). Qed.
Lemma lem1360086 (a : Prop) : (term221 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1360087 (x : real) (z : real) : (term222 x z) = (x = z).
Proof. exact (@lem1360086 (x = z)). Qed.
Lemma lem1360088 (y : real) (x : real) (z : real) : (term246 y x z) = (term247 y x z).
Proof. exact (MK_COMB (@lem1360084 x y) (@lem1360087 x z)). Qed.
Lemma lem1360089 (y : real) (x : real) (z : real) : (term245 y x z) = (term247 y x z).
Proof. exact (TRANS (@lem1360079 y x z) (@lem1360088 y x z)). Qed.
Lemma lem1360090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1360091 (y : real) (x : real) (z : real) : (term248 y x z) = (term249 y x z).
Proof. exact (MK_COMB (@lem1360090) (@lem1360089 y x z)). Qed.
Lemma lem1360092 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1360093 (x : real) (y : real) (z : real) : (term243 x y z) = (term250 x y z).
Proof. exact (MK_COMB (@lem1360091 y x z) (@lem1360092 y z)). Qed.
Lemma lem1360094 (x : real) (y : real) (z : real) : (term240 y x z) = (term250 x y z).
Proof. exact (TRANS (@lem1360076 x y z) (@lem1360093 x y z)). Qed.
Lemma lem1360096 (x : real) (y : real) (h1 : term34) (h2 : term38) : term251 x y.
Proof. exact (conj (@lem1359975 y x h2) (@lem1359983 x y h1)). Qed.
Lemma lem1360098 (x : real) (y : real) (z : real) : term250 x y z.
Proof. exact (EQ_MP (@lem1360094 x y z) (@lem1360073 y x z)). Qed.
Lemma lem1360099 (x : real) (y : real) : term252 x y.
Proof. exact (@lem1360098 (term231 x y) (term39 x) (term234 x y)). Qed.
Lemma lem1360102 (x : real) (y : real) (h1 : term34) (h2 : term38) : (term39 x) = (term234 x y).
Proof. exact (@lem1360099 x y (@lem1360096 x y h1 h2)). Qed.
Lemma lem1360103 (x : real) (y : real) (h1 : term34) (h2 : term38) : term253 x y.
Proof. exact (fun h0 : term254 x y => @lem1360102 x y h1 h2). Qed.
Lemma lem1360105 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360106 (x : real) (y : real) : (term253 x y) = ((term39 x) = (term234 x y)).
Proof. exact (@lem1360105 ((term39 x) = (term234 x y))). Qed.
Lemma lem1360107 (x : real) (y : real) (h1 : term34) (h2 : term38) : (term39 x) = (term234 x y).
Proof. exact (EQ_MP (@lem1360106 x y) (@lem1360103 x y h1 h2)). Qed.
Lemma lem1360108 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : term255 x y.
Proof. exact (conj (@lem1359836 x h3) (@lem1360107 x y h1 h2)). Qed.
Lemma lem1360110 (x : real) (y : real) (z : real) : term250 x y z.
Proof. exact (EQ_MP (@lem1360094 x y z) (@lem1360073 y x z)). Qed.
Lemma lem1360111 (x : real) (y : real) : term256 x y.
Proof. exact (@lem1360110 (term39 x) term36 (term234 x y)). Qed.
Lemma lem1360114 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : term36 = (term234 x y).
Proof. exact (@lem1360111 x y (@lem1360108 x y h1 h2 h3)). Qed.
Lemma lem1360115 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : term257 x y.
Proof. exact (fun h0 : term258 x y => @lem1360114 x y h1 h2 h3). Qed.
Lemma lem1360117 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360118 (x : real) (y : real) : (term257 x y) = (term36 = (term234 x y)).
Proof. exact (@lem1360117 (term36 = (term234 x y))). Qed.
Lemma lem1360119 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : term36 = (term234 x y).
Proof. exact (EQ_MP (@lem1360118 x y) (@lem1360115 x y h1 h2 h3)). Qed.
Lemma lem1360121 (_24171 : real) (h1 : term38) : (term35 _24171) = term36.
Proof. exact (EQ_MP (@lem1359722 _24171) (@lem1359721 _24171 h1)). Qed.
Lemma lem1360122 (x : real) (y : real) (h1 : term38) : (term259 x y) = term36.
Proof. exact (@lem1360121 (real_mul x y) h1). Qed.
Lemma lem1360123 (x : real) (y : real) (h1 : term38) : term260 x y.
Proof. exact (fun h0 : term261 x y => @lem1360122 x y h1). Qed.
Lemma lem1360125 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360126 (x : real) (y : real) : (term260 x y) = ((term259 x y) = term36).
Proof. exact (@lem1360125 ((term259 x y) = term36)). Qed.
Lemma lem1360127 (x : real) (y : real) (h1 : term38) : (term259 x y) = term36.
Proof. exact (EQ_MP (@lem1360126 x y) (@lem1360123 x y h1)). Qed.
Lemma lem1360129 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1360130 (x : real) (y : real) : (term259 x y) = (term259 x y).
Proof. exact (@lem1360129 (term259 x y)). Qed.
Lemma lem1360131 (x : real) (y : real) : term262 x y.
Proof. exact (fun h0 : term263 x y => @lem1360130 x y). Qed.
Lemma lem1360133 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360134 (x : real) (y : real) : (term262 x y) = ((term259 x y) = (term259 x y)).
Proof. exact (@lem1360133 ((term259 x y) = (term259 x y))). Qed.
Lemma lem1360135 (x : real) (y : real) : (term259 x y) = (term259 x y).
Proof. exact (EQ_MP (@lem1360134 x y) (@lem1360131 x y)). Qed.
Lemma lem1360136 (x : real) (y : real) (h1 : term38) : term264 x y.
Proof. exact (conj (@lem1360127 x y h1) (@lem1360135 x y)). Qed.
Lemma lem1360138 (x : real) (y : real) (z : real) : term250 x y z.
Proof. exact (EQ_MP (@lem1360094 x y z) (@lem1360073 y x z)). Qed.
Lemma lem1360139 (x : real) (y : real) : term265 x y.
Proof. exact (@lem1360138 (term259 x y) term36 (term259 x y)). Qed.
Lemma lem1360142 (x : real) (y : real) (h1 : term38) : term36 = (term259 x y).
Proof. exact (@lem1360139 x y (@lem1360136 x y h1)). Qed.
Lemma lem1360143 (x : real) (y : real) (h1 : term38) : term266 x y.
Proof. exact (fun h0 : term267 x y => @lem1360142 x y h1). Qed.
Lemma lem1360145 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360146 (x : real) (y : real) : (term266 x y) = (term36 = (term259 x y)).
Proof. exact (@lem1360145 (term36 = (term259 x y))). Qed.
Lemma lem1360147 (x : real) (y : real) (h1 : term38) : term36 = (term259 x y).
Proof. exact (EQ_MP (@lem1360146 x y) (@lem1360143 x y h1)). Qed.
Lemma lem1360148 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : term268 x y.
Proof. exact (conj (@lem1360119 x y h1 h2 h3) (@lem1360147 x y h2)). Qed.
Lemma lem1360150 (x : real) (y : real) (z : real) : term250 x y z.
Proof. exact (EQ_MP (@lem1360094 x y z) (@lem1360073 y x z)). Qed.
Lemma lem1360151 (x : real) (y : real) : term269 x y.
Proof. exact (@lem1360150 term36 (term234 x y) (term259 x y)). Qed.
Lemma lem1360154 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : (term234 x y) = (term259 x y).
Proof. exact (@lem1360151 x y (@lem1360148 x y h1 h2 h3)). Qed.
Lemma lem1360155 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : term270 x y.
Proof. exact (fun h0 : term271 x y => @lem1360154 x y h1 h2 h3). Qed.
Lemma lem1360157 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360158 (x : real) (y : real) : (term270 x y) = ((term234 x y) = (term259 x y)).
Proof. exact (@lem1360157 ((term234 x y) = (term259 x y))). Qed.
Lemma lem1360159 (x : real) (y : real) (h1 : term34) (h2 : term38) (h3 : term41) : (term234 x y) = (term259 x y).
Proof. exact (EQ_MP (@lem1360158 x y) (@lem1360155 x y h1 h2 h3)). Qed.
Lemma lem1360165 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1360166 (_24178 : real) (_24179 : real) (_24180 : real) : (term83 _24180 _24178 _24179) = (term272 _24178 _24179 _24180).
Proof. exact (@lem1360165 (_24178 = _24179) (term123 _24178 _24179 _24180)). Qed.
Lemma lem1360176 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1360177 (_24178 : real) (_24179 : real) (_24180 : real) : (term273 _24180 _24178 _24179) = (term274 _24178 _24179 _24180).
Proof. exact (MK_COMB (@lem1360176) (@lem1360166 _24178 _24179 _24180)). Qed.
Lemma lem1360187 (_24178 : real) (_24179 : real) (_24180 : real) : (term272 _24178 _24179 _24180) = (term272 _24178 _24179 _24180).
Proof. exact (eq_refl (term272 _24178 _24179 _24180)). Qed.
Lemma lem1360188 (_24178 : real) (_24179 : real) (_24180 : real) : ((term83 _24180 _24178 _24179) = (term272 _24178 _24179 _24180)) = ((term272 _24178 _24179 _24180) = (term272 _24178 _24179 _24180)).
Proof. exact (MK_COMB (@lem1360177 _24178 _24179 _24180) (@lem1360187 _24178 _24179 _24180)). Qed.
Lemma lem1360190 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1360191 (x : Prop) : (x = x) = True.
Proof. exact (@lem1360190 Prop x). Qed.
Lemma lem1360192 (_24178 : real) (_24179 : real) (_24180 : real) : ((term272 _24178 _24179 _24180) = (term272 _24178 _24179 _24180)) = True.
Proof. exact (@lem1360191 (term272 _24178 _24179 _24180)). Qed.
Lemma lem1360193 (_24178 : real) (_24179 : real) (_24180 : real) : ((term83 _24180 _24178 _24179) = (term272 _24178 _24179 _24180)) = True.
Proof. exact (TRANS (@lem1360188 _24178 _24179 _24180) (@lem1360192 _24178 _24179 _24180)). Qed.
Lemma lem1360194 (_24178 : real) (_24179 : real) (_24180 : real) : True = ((term83 _24180 _24178 _24179) = (term272 _24178 _24179 _24180)).
Proof. exact (SYM (@lem1360193 _24178 _24179 _24180)). Qed.
Lemma lem1360195 (_24178 : real) (_24179 : real) (_24180 : real) : (term83 _24180 _24178 _24179) = (term272 _24178 _24179 _24180).
Proof. exact (EQ_MP (@lem1360194 _24178 _24179 _24180) (@lem0)). Qed.
Lemma lem1360196 (_24178 : real) (_24179 : real) (_24180 : real) (h1 : term10) : term272 _24178 _24179 _24180.
Proof. exact (EQ_MP (@lem1360195 _24178 _24179 _24180) (@lem1359770 _24180 _24178 _24179 h1)). Qed.
Lemma lem1360198 (b : Prop) (a : Prop) : (a \/ b) = (term214 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1360199 (_24180 : real) (_24178 : real) (_24179 : real) : (term272 _24178 _24179 _24180) = (term275 _24180 _24178 _24179).
Proof. exact (@lem1360198 (term123 _24178 _24179 _24180) (_24178 = _24179)). Qed.
Lemma lem1360201 (a : Prop) : (term221 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1360202 (_24178 : real) (_24179 : real) (_24180 : real) : (term276 _24178 _24179 _24180) = ((real_add _24178 _24180) = (real_add _24179 _24180)).
Proof. exact (@lem1360201 ((real_add _24178 _24180) = (real_add _24179 _24180))). Qed.
Lemma lem1360203 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1360204 (_24178 : real) (_24179 : real) (_24180 : real) : (term277 _24178 _24179 _24180) = (term278 _24178 _24179 _24180).
Proof. exact (MK_COMB (@lem1360203) (@lem1360202 _24178 _24179 _24180)). Qed.
Lemma lem1360205 (_24178 : real) (_24179 : real) : (_24178 = _24179) = (_24178 = _24179).
Proof. exact (eq_refl (_24178 = _24179)). Qed.
Lemma lem1360206 (_24180 : real) (_24178 : real) (_24179 : real) : (term275 _24180 _24178 _24179) = (term279 _24180 _24178 _24179).
Proof. exact (MK_COMB (@lem1360204 _24178 _24179 _24180) (@lem1360205 _24178 _24179)). Qed.
Lemma lem1360207 (_24180 : real) (_24178 : real) (_24179 : real) : (term272 _24178 _24179 _24180) = (term279 _24180 _24178 _24179).
Proof. exact (TRANS (@lem1360199 _24180 _24178 _24179) (@lem1360206 _24180 _24178 _24179)). Qed.
Lemma lem1360210 (_24180 : real) (_24178 : real) (_24179 : real) (h1 : term10) : term279 _24180 _24178 _24179.
Proof. exact (EQ_MP (@lem1360207 _24180 _24178 _24179) (@lem1360196 _24178 _24179 _24180 h1)). Qed.
Lemma lem1360211 (x : real) (y : real) (h1 : term10) : term280 x y.
Proof. exact (@lem1360210 (real_mul x y) (term42 x y) (term43 x y) h1). Qed.
Lemma lem1360214 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) : (term42 x y) = (term43 x y).
Proof. exact (@lem1360211 x y h1 (@lem1360159 x y h2 h3 h4)). Qed.
Lemma lem1360215 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) : term281 x y.
Proof. exact (fun h0 : term53 x y => @lem1360214 x y h1 h2 h3 h4). Qed.
Lemma lem1360217 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360218 (x : real) (y : real) : (term281 x y) = ((term42 x y) = (term43 x y)).
Proof. exact (@lem1360217 ((term42 x y) = (term43 x y))). Qed.
Lemma lem1360219 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) : (term42 x y) = (term43 x y).
Proof. exact (EQ_MP (@lem1360218 x y) (@lem1360215 x y h1 h2 h3 h4)). Qed.
Lemma lem1360222 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1360224 (x : real) (y : real) : (term53 x y) = (term282 x y).
Proof. exact (@lem1360222 ((term42 x y) = (term43 x y))). Qed.
Lemma lem1360227 (x : real) (y : real) (h1 : term53 x y) : term282 x y.
Proof. exact (EQ_MP (@lem1360224 x y) (@lem1359758 x y h1)). Qed.
Lemma lem1360230 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (@lem1360227 x y h5 (@lem1360219 x y h1 h2 h3 h4)). Qed.
Lemma lem1360231 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : term283.
Proof. exact (fun h0 : ~ False => @lem1360230 x y h1 h2 h3 h4 h5). Qed.
Lemma lem1360233 (p : Prop) : (term202 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1360234 : term283 = False.
Proof. exact (@lem1360233 False). Qed.
Lemma lem1360235 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360234) (@lem1360231 x y h1 h2 h3 h4 h5)). Qed.
Lemma lem1360236 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : (term53 x y) = False.
Proof. exact (prop_ext (fun h6 : term53 x y => @lem1360235 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359758 x y h5)). Qed.
Lemma lem1360237 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360236 x y h1 h2 h3 h4 h5) (@lem1359758 x y h5)). Qed.
Lemma lem1360238 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : (term53 x y) = False.
Proof. exact (prop_ext (fun h6 : term53 x y => @lem1360237 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359621 x y h5)). Qed.
Lemma lem1360239 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360238 x y h1 h2 h3 h4 h5) (@lem1359621 x y h5)). Qed.
Lemma lem1360240 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : (term53 x y) = False.
Proof. exact (prop_ext (fun h6 : term53 x y => @lem1360239 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359621 x y h5)). Qed.
Lemma lem1360241 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360240 x y h1 h2 h3 h4 h5) (@lem1359621 x y h5)). Qed.
Lemma lem1360242 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : term34 = False.
Proof. exact (prop_ext (fun h6 : term34 => @lem1360241 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359617 h2)). Qed.
Lemma lem1360243 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360242 x y h1 h2 h3 h4 h5) (@lem1359617 h2)). Qed.
Lemma lem1360244 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : term38 = False.
Proof. exact (prop_ext (fun h6 : term38 => @lem1360243 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359604 h3)). Qed.
Lemma lem1360245 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360244 x y h1 h2 h3 h4 h5) (@lem1359604 h3)). Qed.
Lemma lem1360246 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : term41 = False.
Proof. exact (prop_ext (fun h6 : term41 => @lem1360245 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359597 h4)). Qed.
Lemma lem1360247 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360246 x y h1 h2 h3 h4 h5) (@lem1359597 h4)). Qed.
Lemma lem1360248 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : (term53 x y) = False.
Proof. exact (prop_ext (fun h6 : term53 x y => @lem1360247 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359588 x y h5)). Qed.
Lemma lem1360249 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360248 x y h1 h2 h3 h4 h5) (@lem1359588 x y h5)). Qed.
Lemma lem1360250 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : term34 = False.
Proof. exact (prop_ext (fun h6 : term34 => @lem1360249 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359500 h2)). Qed.
Lemma lem1360251 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360250 x y h1 h2 h3 h4 h5) (@lem1359500 h2)). Qed.
Lemma lem1360252 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : term38 = False.
Proof. exact (prop_ext (fun h6 : term38 => @lem1360251 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359465 h3)). Qed.
Lemma lem1360253 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360252 x y h1 h2 h3 h4 h5) (@lem1359465 h3)). Qed.
Lemma lem1360254 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : term41 = False.
Proof. exact (prop_ext (fun h6 : term41 => @lem1360253 x y h1 h2 h3 h4 h5) (fun h6 : False => @lem1359446 h4)). Qed.
Lemma lem1360255 (x : real) (y : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term53 x y) : False.
Proof. exact (EQ_MP (@lem1360254 x y h1 h2 h3 h4 h5) (@lem1359446 h4)). Qed.
Lemma lem1360256 (x : real) (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term56 x) : False.
Proof. exact (ex_elim (@lem1359424 x h5) (fun y : real => fun h0 : term55 x y => @lem1360255 x y h1 h2 h3 h4 h0)). Qed.
Lemma lem1360257 (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term3) : False.
Proof. exact (ex_elim (@lem1358929 h5) (fun x : real => fun h0 : term61 x => @lem1360256 x h1 h2 h3 h4 h0)). Qed.
Lemma lem1360258 (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term3) : term34 = False.
Proof. exact (prop_ext (fun h6 : term34 => @lem1360257 h1 h2 h3 h4 h5) (fun h6 : False => @lem1358982 h2)). Qed.
Lemma lem1360259 (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term3) : False.
Proof. exact (EQ_MP (@lem1360258 h1 h2 h3 h4 h5) (@lem1358982 h2)). Qed.
Lemma lem1360260 (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term3) : term38 = False.
Proof. exact (prop_ext (fun h6 : term38 => @lem1360259 h1 h2 h3 h4 h5) (fun h6 : False => @lem1358955 h3)). Qed.
Lemma lem1360261 (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term3) : False.
Proof. exact (EQ_MP (@lem1360260 h1 h2 h3 h4 h5) (@lem1358955 h3)). Qed.
Lemma lem1360262 (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term3) : term41 = False.
Proof. exact (prop_ext (fun h6 : term41 => @lem1360261 h1 h2 h3 h4 h5) (fun h6 : False => @lem1358942 h4)). Qed.
Lemma lem1360263 (h1 : term10) (h2 : term34) (h3 : term38) (h4 : term41) (h5 : term3) : False.
Proof. exact (EQ_MP (@lem1360262 h1 h2 h3 h4 h5) (@lem1358942 h4)). Qed.
Lemma lem1360264 (h1 : term34) (h2 : term38) (h3 : term41) (h4 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1360263 h0 h1 h2 h3 h4). Qed.
Lemma lem1360265 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1360266 (h1 : term34) (h2 : term38) (h3 : term41) (h4 : term3) : term9.
Proof. exact (EQ_MP (@lem1360265) (@lem1360264 h1 h2 h3 h4)). Qed.
Lemma lem1360267 (h1 : term38) (h2 : term41) (h3 : term3) : term13.
Proof. exact (fun h0 : term34 => @lem1360266 h0 h1 h2 h3). Qed.
Lemma lem1360268 (h1 : term41) (h2 : term3) : term16.
Proof. exact (fun h0 : term38 => @lem1360267 h0 h1 h2). Qed.
Lemma lem1360269 (h1 : term3) : term19.
Proof. exact (fun h0 : term41 => @lem1360268 h0 h1). Qed.
Lemma lem1360270 : term21.
Proof. exact (fun h0 : term3 => @lem1360269 h0). Qed.
Lemma lem1360271 : term4.
Proof. exact (EQ_MP (@lem1358890) (@lem1360270)). Qed.
Lemma lem1360273 : term4.
Proof. exact (@lem1358692 (@lem1360271)). Qed.
Lemma lem1360274 (h1 : term3) : term18.
Proof. exact (@lem1360273 (@lem1358677 h1)). Qed.
Lemma lem1360275 (h1 : term3) : term15.
Proof. exact (@lem1360274 h1 (@lem1356740)). Qed.
Lemma lem1360276 (h1 : term3) : term12.
Proof. exact (@lem1360275 h1 (@lem1338588)). Qed.
Lemma lem1360277 (h1 : term3) : term8.
Proof. exact (@lem1360276 h1 (@lem1339188)). Qed.
Lemma lem1360278 (h1 : term3) : False.
Proof. exact (@lem1360277 h1 (@lem1355147)). Qed.
Lemma lem1360279 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1360278 h1) (fun h2 : False => @lem1358677 h1)). Qed.
Lemma lem1360280 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1360279 h1) (@lem1358677 h1)). Qed.
Lemma lem1360281 : term2.
Proof. exact (fun h0 : term3 => @lem1360280 h0). Qed.
Lemma lem1360282 : term1.
Proof. exact (EQ_MP (@lem1358676) (@lem1360281)). Qed.
