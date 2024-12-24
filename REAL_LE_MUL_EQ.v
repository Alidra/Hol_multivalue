Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LE_MUL_EQ_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LE_LMUL_EQ_spec.
Require Import REAL_LE_RMUL_EQ_spec.
Require Import REAL_MUL_LZERO_spec.
Require Import REAL_MUL_RZERO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18958_spec.
Require Import thm18959_spec.
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
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem1602665 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1602666 : term1 = term2.
Proof. exact (@lem1602665 term1). Qed.
Lemma lem1602667 : term2 = term1.
Proof. exact (SYM (@lem1602666)). Qed.
Lemma lem1602668 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1602671 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1602672 : term5.
Proof. exact (fun h0 : term4 => @lem1602671 h0). Qed.
Lemma lem1602673 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1602674 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1602675 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1602673 h2 (@lem1602674 h1)). Qed.
Lemma lem1602676 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1602675 h1 h0). Qed.
Lemma lem1602677 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1602678 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1602676 h1 (@lem1602677 h2)). Qed.
Lemma lem1602679 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1602678 h0 h1). Qed.
Lemma lem1602680 : term7.
Proof. exact (fun h0 : term5 => @lem1602679 h0). Qed.
Lemma lem1602683 : term5.
Proof. exact (@lem1602680 (@lem1602672)). Qed.
Lemma lem1602737 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1602738 : term8 = term9.
Proof. exact (@lem1602737 term10). Qed.
Lemma lem1602753 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1602754 : term12 = term13.
Proof. exact (MK_COMB (@lem1602753) (@lem1602738)). Qed.
Lemma lem1602757 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1602758 : term15 = term16.
Proof. exact (MK_COMB (@lem1602757) (@lem1602754)). Qed.
Lemma lem1602761 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem1602762 : term18 = term19.
Proof. exact (MK_COMB (@lem1602761) (@lem1602758)). Qed.
Lemma lem1602765 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1602772 : term4 = term21.
Proof. exact (MK_COMB (@lem1602765) (@lem1602762)). Qed.
Lemma lem1602781 (z : real) (x : real) (y : real) : (term22 z x y) = (term22 z x y).
Proof. exact (eq_refl (term22 z x y)). Qed.
Lemma lem1602782 (x : real) (y : real) : (term23 x y) = (term23 x y).
Proof. exact (fun_ext (fun z : real => @lem1602781 z x y)). Qed.
Lemma lem1602783 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602784 (x : real) (y : real) : (term24 x y) = (term24 x y).
Proof. exact (MK_COMB (@lem1602783) (@lem1602782 x y)). Qed.
Lemma lem1602785 (x : real) : (term25 x) = (term25 x).
Proof. exact (fun_ext (fun y : real => @lem1602784 x y)). Qed.
Lemma lem1602786 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602787 (x : real) : (term26 x) = (term26 x).
Proof. exact (MK_COMB (@lem1602786) (@lem1602785 x)). Qed.
Lemma lem1602788 : term27 = term27.
Proof. exact (fun_ext (fun x : real => @lem1602787 x)). Qed.
Lemma lem1602789 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602790 : term10 = term10.
Proof. exact (MK_COMB (@lem1602789) (@lem1602788)). Qed.
Lemma lem1602791 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1602792 : term9 = term9.
Proof. exact (MK_COMB (@lem1602791) (@lem1602790)). Qed.
Lemma lem1602801 (z : real) (x : real) (y : real) : (term28 z x y) = (term28 z x y).
Proof. exact (eq_refl (term28 z x y)). Qed.
Lemma lem1602802 (x : real) (y : real) : (term29 x y) = (term29 x y).
Proof. exact (fun_ext (fun z : real => @lem1602801 z x y)). Qed.
Lemma lem1602803 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602804 (x : real) (y : real) : (term30 x y) = (term30 x y).
Proof. exact (MK_COMB (@lem1602803) (@lem1602802 x y)). Qed.
Lemma lem1602805 (x : real) : (term31 x) = (term31 x).
Proof. exact (fun_ext (fun y : real => @lem1602804 x y)). Qed.
Lemma lem1602806 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602807 (x : real) : (term32 x) = (term32 x).
Proof. exact (MK_COMB (@lem1602806) (@lem1602805 x)). Qed.
Lemma lem1602808 : term33 = term33.
Proof. exact (fun_ext (fun x : real => @lem1602807 x)). Qed.
Lemma lem1602809 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602810 : term34 = term34.
Proof. exact (MK_COMB (@lem1602809) (@lem1602808)). Qed.
Lemma lem1602811 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1602812 : term11 = term11.
Proof. exact (MK_COMB (@lem1602811) (@lem1602810)). Qed.
Lemma lem1602813 : term13 = term13.
Proof. exact (MK_COMB (@lem1602812) (@lem1602792)). Qed.
Lemma lem1602814 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1602815 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1602814 x)). Qed.
Lemma lem1602816 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602817 : term38 = term38.
Proof. exact (MK_COMB (@lem1602816) (@lem1602815)). Qed.
Lemma lem1602818 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1602819 : term14 = term14.
Proof. exact (MK_COMB (@lem1602818) (@lem1602817)). Qed.
Lemma lem1602820 : term16 = term16.
Proof. exact (MK_COMB (@lem1602819) (@lem1602813)). Qed.
Lemma lem1602821 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1602822 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1602821 x)). Qed.
Lemma lem1602823 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602824 : term41 = term41.
Proof. exact (MK_COMB (@lem1602823) (@lem1602822)). Qed.
Lemma lem1602825 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1602826 : term17 = term17.
Proof. exact (MK_COMB (@lem1602825) (@lem1602824)). Qed.
Lemma lem1602827 : term19 = term19.
Proof. exact (MK_COMB (@lem1602826) (@lem1602820)). Qed.
Lemma lem1602836 (y : real) (x : real) : (term42 y x) = (term42 y x).
Proof. exact (eq_refl (term42 y x)). Qed.
Lemma lem1602837 (x : real) : (term43 x) = (term43 x).
Proof. exact (fun_ext (fun y : real => @lem1602836 y x)). Qed.
Lemma lem1602838 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602839 (x : real) : (term44 x) = (term44 x).
Proof. exact (MK_COMB (@lem1602838) (@lem1602837 x)). Qed.
Lemma lem1602840 : term45 = term45.
Proof. exact (fun_ext (fun x : real => @lem1602839 x)). Qed.
Lemma lem1602841 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602842 : term46 = term46.
Proof. exact (MK_COMB (@lem1602841) (@lem1602840)). Qed.
Lemma lem1602851 (x : real) (y : real) : (term47 x y) = (term47 x y).
Proof. exact (eq_refl (term47 x y)). Qed.
Lemma lem1602852 (x : real) : (term48 x) = (term48 x).
Proof. exact (fun_ext (fun y : real => @lem1602851 x y)). Qed.
Lemma lem1602853 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602854 (x : real) : (term49 x) = (term49 x).
Proof. exact (MK_COMB (@lem1602853) (@lem1602852 x)). Qed.
Lemma lem1602855 : term50 = term50.
Proof. exact (fun_ext (fun x : real => @lem1602854 x)). Qed.
Lemma lem1602856 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1602857 : term51 = term51.
Proof. exact (MK_COMB (@lem1602856) (@lem1602855)). Qed.
Lemma lem1602858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1602859 : term52 = term52.
Proof. exact (MK_COMB (@lem1602858) (@lem1602857)). Qed.
Lemma lem1602860 : term1 = term1.
Proof. exact (MK_COMB (@lem1602859) (@lem1602842)). Qed.
Lemma lem1602861 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1602862 : term3 = term3.
Proof. exact (MK_COMB (@lem1602861) (@lem1602860)). Qed.
Lemma lem1602863 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1602864 : term20 = term20.
Proof. exact (MK_COMB (@lem1602863) (@lem1602862)). Qed.
Lemma lem1602865 : term21 = term21.
Proof. exact (MK_COMB (@lem1602864) (@lem1602827)). Qed.
Lemma lem1602958 : term4 = term21.
Proof. exact (TRANS (@lem1602772) (@lem1602865)). Qed.
Lemma lem1602959 : term21 = term4.
Proof. exact (SYM (@lem1602958)). Qed.
Lemma lem1602960 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1602961 (h1 : term41) : term41.
Proof. exact (h1). Qed.
Lemma lem1602962 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1602963 (h1 : term34) : term34.
Proof. exact (h1). Qed.
Lemma lem1602964 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1602980 (x : real) (y : real) : (term53 x y) = (term54 x y).
Proof. exact (@lem17646 (term55 x y) (term56 y)). Qed.
Lemma lem1602982 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1602983 (x : real) (y : real) : (term58 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1602982 x) (@lem1602980 x y)). Qed.
Lemma lem1602984 (x : real) (y : real) : (term60 x y) = (term58 x y).
Proof. exact (@lem17362 (term61 x) ((term55 x y) = (term56 y))). Qed.
Lemma lem1602985 (x : real) (y : real) : (term60 x y) = (term59 x y).
Proof. exact (TRANS (@lem1602984 x y) (@lem1602983 x y)). Qed.
Lemma lem1602986 (P : real -> Prop) : (term62 P) = (term63 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1602987 (x : real) : (term64 x) = (term65 x).
Proof. exact (@lem1602986 (term48 x)). Qed.
Lemma lem1602988 (x : real) (y : real) : (term66 x y) = (term47 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem1602989 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1602990 (x : real) (y : real) : (term67 x y) = (term60 x y).
Proof. exact (MK_COMB (@lem1602989) (@lem1602988 x y)). Qed.
Lemma lem1602991 (x : real) (y : real) : (term67 x y) = (term59 x y).
Proof. exact (TRANS (@lem1602990 x y) (@lem1602985 x y)). Qed.
Lemma lem1602992 (x : real) : (term68 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1602991 x y)). Qed.
Lemma lem1602993 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1602994 (x : real) : (term65 x) = (term70 x).
Proof. exact (MK_COMB (@lem1602993) (@lem1602992 x)). Qed.
Lemma lem1602995 (x : real) : (term64 x) = (term70 x).
Proof. exact (TRANS (@lem1602987 x) (@lem1602994 x)). Qed.
Lemma lem1602996 (P : real -> Prop) : (term62 P) = (term63 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1602997 : term71 = term72.
Proof. exact (@lem1602996 term50). Qed.
Lemma lem1602998 (x : real) : (term73 x) = (term49 x).
Proof. exact (eq_refl (term73 x)). Qed.
Lemma lem1602999 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1603000 (x : real) : (term74 x) = (term64 x).
Proof. exact (MK_COMB (@lem1602999) (@lem1602998 x)). Qed.
Lemma lem1603001 (x : real) : (term74 x) = (term70 x).
Proof. exact (TRANS (@lem1603000 x) (@lem1602995 x)). Qed.
Lemma lem1603002 : term75 = term76.
Proof. exact (fun_ext (fun x : real => @lem1603001 x)). Qed.
Lemma lem1603003 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603004 : term72 = term77.
Proof. exact (MK_COMB (@lem1603003) (@lem1603002)). Qed.
Lemma lem1603005 : term71 = term77.
Proof. exact (TRANS (@lem1602997) (@lem1603004)). Qed.
Lemma lem1603021 (y : real) (x : real) : (term78 y x) = (term79 y x).
Proof. exact (@lem17646 (term55 x y) (term56 x)). Qed.
Lemma lem1603023 (y : real) : (term57 y) = (term57 y).
Proof. exact (eq_refl (term57 y)). Qed.
Lemma lem1603024 (y : real) (x : real) : (term80 y x) = (term81 y x).
Proof. exact (MK_COMB (@lem1603023 y) (@lem1603021 y x)). Qed.
Lemma lem1603025 (y : real) (x : real) : (term82 y x) = (term80 y x).
Proof. exact (@lem17362 (term61 y) ((term55 x y) = (term56 x))). Qed.
Lemma lem1603026 (y : real) (x : real) : (term82 y x) = (term81 y x).
Proof. exact (TRANS (@lem1603025 y x) (@lem1603024 y x)). Qed.
Lemma lem1603027 (P : real -> Prop) : (term62 P) = (term63 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1603028 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1603027 (term43 x)). Qed.
Lemma lem1603029 (y : real) (x : real) : (term85 x y) = (term42 y x).
Proof. exact (eq_refl (term85 x y)). Qed.
Lemma lem1603030 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1603031 (y : real) (x : real) : (term86 x y) = (term82 y x).
Proof. exact (MK_COMB (@lem1603030) (@lem1603029 y x)). Qed.
Lemma lem1603032 (y : real) (x : real) : (term86 x y) = (term81 y x).
Proof. exact (TRANS (@lem1603031 y x) (@lem1603026 y x)). Qed.
Lemma lem1603033 (x : real) : (term87 x) = (term88 x).
Proof. exact (fun_ext (fun y : real => @lem1603032 y x)). Qed.
Lemma lem1603034 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603035 (x : real) : (term84 x) = (term89 x).
Proof. exact (MK_COMB (@lem1603034) (@lem1603033 x)). Qed.
Lemma lem1603036 (x : real) : (term83 x) = (term89 x).
Proof. exact (TRANS (@lem1603028 x) (@lem1603035 x)). Qed.
Lemma lem1603037 (P : real -> Prop) : (term62 P) = (term63 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1603038 : term90 = term91.
Proof. exact (@lem1603037 term45). Qed.
Lemma lem1603039 (x : real) : (term92 x) = (term44 x).
Proof. exact (eq_refl (term92 x)). Qed.
Lemma lem1603040 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1603041 (x : real) : (term93 x) = (term83 x).
Proof. exact (MK_COMB (@lem1603040) (@lem1603039 x)). Qed.
Lemma lem1603042 (x : real) : (term93 x) = (term89 x).
Proof. exact (TRANS (@lem1603041 x) (@lem1603036 x)). Qed.
Lemma lem1603043 : term94 = term95.
Proof. exact (fun_ext (fun x : real => @lem1603042 x)). Qed.
Lemma lem1603044 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603045 : term91 = term96.
Proof. exact (MK_COMB (@lem1603044) (@lem1603043)). Qed.
Lemma lem1603046 : term90 = term96.
Proof. exact (TRANS (@lem1603038) (@lem1603045)). Qed.
Lemma lem1603047 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603048 : term97 = term98.
Proof. exact (MK_COMB (@lem1603047) (@lem1603005)). Qed.
Lemma lem1603049 : term99 = term100.
Proof. exact (MK_COMB (@lem1603048) (@lem1603046)). Qed.
Lemma lem1603050 : term3 = term99.
Proof. exact (@lem17045 term51 term46). Qed.
Lemma lem1603051 : term3 = term100.
Proof. exact (TRANS (@lem1603050) (@lem1603049)). Qed.
Lemma lem1603057 {A : Type'} (P : Prop) (Q : A -> Prop) : (term101 A P Q) = (term102 A P Q).
Proof. exact (EQ_MP (@lem18959 A P Q) (@lem18958 A P Q)). Qed.
Lemma lem1603058 (P : Prop) (Q : real -> Prop) : (term103 P Q) = (term104 P Q).
Proof. exact (@lem1603057 real P Q). Qed.
Lemma lem1603059 (x : real) : (term105 x) = (term106 x).
Proof. exact (@lem1603058 (term61 x) (term107 x)). Qed.
Lemma lem1603060 (x : real) (y : real) : (term108 x y) = (term54 x y).
Proof. exact (eq_refl (term108 x y)). Qed.
Lemma lem1603061 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1603062 (x : real) (y : real) : (term109 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1603061 x) (@lem1603060 x y)). Qed.
Lemma lem1603063 (x : real) : (term110 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1603062 x y)). Qed.
Lemma lem1603064 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603065 (x : real) : (term105 x) = (term70 x).
Proof. exact (MK_COMB (@lem1603064) (@lem1603063 x)). Qed.
Lemma lem1603066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1603067 (x : real) : (term111 x) = (term112 x).
Proof. exact (MK_COMB (@lem1603066) (@lem1603065 x)). Qed.
Lemma lem1603068 (x : real) (y : real) : (term108 x y) = (term54 x y).
Proof. exact (eq_refl (term108 x y)). Qed.
Lemma lem1603069 (x : real) : (term113 x) = (term107 x).
Proof. exact (fun_ext (fun y : real => @lem1603068 x y)). Qed.
Lemma lem1603070 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603071 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1603070) (@lem1603069 x)). Qed.
Lemma lem1603072 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1603073 (x : real) : (term106 x) = (term116 x).
Proof. exact (MK_COMB (@lem1603072 x) (@lem1603071 x)). Qed.
Lemma lem1603074 (x : real) : ((term105 x) = (term106 x)) = ((term70 x) = (term116 x)).
Proof. exact (MK_COMB (@lem1603067 x) (@lem1603073 x)). Qed.
Lemma lem1603075 (x : real) : (term70 x) = (term116 x).
Proof. exact (EQ_MP (@lem1603074 x) (@lem1603059 x)). Qed.
Lemma lem1603077 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term117 A P Q) = (term118 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1603078 (P : real -> Prop) (Q : real -> Prop) : (term119 P Q) = (term120 P Q).
Proof. exact (@lem1603077 real P Q). Qed.
Lemma lem1603079 (x : real) : (term121 x) = (term122 x).
Proof. exact (@lem1603078 (term123 x) (term124 x)). Qed.
Lemma lem1603080 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1603081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603082 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1603081) (@lem1603080 x y)). Qed.
Lemma lem1603083 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1603084 (x : real) (y : real) : (term131 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1603082 x y) (@lem1603083 x y)). Qed.
Lemma lem1603085 (x : real) : (term132 x) = (term107 x).
Proof. exact (fun_ext (fun y : real => @lem1603084 x y)). Qed.
Lemma lem1603086 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603087 (x : real) : (term121 x) = (term115 x).
Proof. exact (MK_COMB (@lem1603086) (@lem1603085 x)). Qed.
Lemma lem1603088 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1603089 (x : real) : (term133 x) = (term134 x).
Proof. exact (MK_COMB (@lem1603088) (@lem1603087 x)). Qed.
Lemma lem1603090 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1603091 (x : real) : (term135 x) = (term123 x).
Proof. exact (fun_ext (fun y : real => @lem1603090 x y)). Qed.
Lemma lem1603092 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603093 (x : real) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1603092) (@lem1603091 x)). Qed.
Lemma lem1603094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603095 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1603094) (@lem1603093 x)). Qed.
Lemma lem1603096 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1603097 (x : real) : (term140 x) = (term124 x).
Proof. exact (fun_ext (fun y : real => @lem1603096 x y)). Qed.
Lemma lem1603098 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603099 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1603098) (@lem1603097 x)). Qed.
Lemma lem1603100 (x : real) : (term122 x) = (term143 x).
Proof. exact (MK_COMB (@lem1603095 x) (@lem1603099 x)). Qed.
Lemma lem1603101 (x : real) : ((term121 x) = (term122 x)) = ((term115 x) = (term143 x)).
Proof. exact (MK_COMB (@lem1603089 x) (@lem1603100 x)). Qed.
Lemma lem1603102 (x : real) : (term115 x) = (term143 x).
Proof. exact (EQ_MP (@lem1603101 x) (@lem1603079 x)). Qed.
Lemma lem1603199 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1603200 (x : real) : (term116 x) = (term144 x).
Proof. exact (MK_COMB (@lem1603199 x) (@lem1603102 x)). Qed.
Lemma lem1603201 (x : real) : (term70 x) = (term144 x).
Proof. exact (TRANS (@lem1603075 x) (@lem1603200 x)). Qed.
Lemma lem1603202 : term76 = term145.
Proof. exact (fun_ext (fun x : real => @lem1603201 x)). Qed.
Lemma lem1603203 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603204 : term77 = term146.
Proof. exact (MK_COMB (@lem1603203) (@lem1603202)). Qed.
Lemma lem1603253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603254 : term98 = term147.
Proof. exact (MK_COMB (@lem1603253) (@lem1603204)). Qed.
Lemma lem1603307 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1603308 : term100 = term148.
Proof. exact (MK_COMB (@lem1603254) (@lem1603307)). Qed.
Lemma lem1603310 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1603311 (P : real -> Prop) (Q : real -> Prop) : (term120 P Q) = (term119 P Q).
Proof. exact (@lem1603310 real P Q). Qed.
Lemma lem1603312 (x : real) : (term122 x) = (term121 x).
Proof. exact (@lem1603311 (term123 x) (term124 x)). Qed.
Lemma lem1603313 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1603314 (x : real) : (term135 x) = (term123 x).
Proof. exact (fun_ext (fun y : real => @lem1603313 x y)). Qed.
Lemma lem1603315 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603316 (x : real) : (term136 x) = (term137 x).
Proof. exact (MK_COMB (@lem1603315) (@lem1603314 x)). Qed.
Lemma lem1603317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603318 (x : real) : (term138 x) = (term139 x).
Proof. exact (MK_COMB (@lem1603317) (@lem1603316 x)). Qed.
Lemma lem1603319 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1603320 (x : real) : (term140 x) = (term124 x).
Proof. exact (fun_ext (fun y : real => @lem1603319 x y)). Qed.
Lemma lem1603321 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603322 (x : real) : (term141 x) = (term142 x).
Proof. exact (MK_COMB (@lem1603321) (@lem1603320 x)). Qed.
Lemma lem1603323 (x : real) : (term122 x) = (term143 x).
Proof. exact (MK_COMB (@lem1603318 x) (@lem1603322 x)). Qed.
Lemma lem1603324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1603325 (x : real) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1603324) (@lem1603323 x)). Qed.
Lemma lem1603326 (x : real) (y : real) : (term125 x y) = (term126 x y).
Proof. exact (eq_refl (term125 x y)). Qed.
Lemma lem1603327 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603328 (x : real) (y : real) : (term127 x y) = (term128 x y).
Proof. exact (MK_COMB (@lem1603327) (@lem1603326 x y)). Qed.
Lemma lem1603329 (x : real) (y : real) : (term129 x y) = (term130 x y).
Proof. exact (eq_refl (term129 x y)). Qed.
Lemma lem1603330 (x : real) (y : real) : (term131 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem1603328 x y) (@lem1603329 x y)). Qed.
Lemma lem1603331 (x : real) : (term132 x) = (term107 x).
Proof. exact (fun_ext (fun y : real => @lem1603330 x y)). Qed.
Lemma lem1603332 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603333 (x : real) : (term121 x) = (term115 x).
Proof. exact (MK_COMB (@lem1603332) (@lem1603331 x)). Qed.
Lemma lem1603334 (x : real) : ((term122 x) = (term121 x)) = ((term143 x) = (term115 x)).
Proof. exact (MK_COMB (@lem1603325 x) (@lem1603333 x)). Qed.
Lemma lem1603335 (x : real) : (term143 x) = (term115 x).
Proof. exact (EQ_MP (@lem1603334 x) (@lem1603312 x)). Qed.
Lemma lem1603336 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1603337 (x : real) : (term144 x) = (term116 x).
Proof. exact (MK_COMB (@lem1603336 x) (@lem1603335 x)). Qed.
Lemma lem1603339 {A : Type'} (P : Prop) (Q : A -> Prop) : (term102 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1603340 (P : Prop) (Q : real -> Prop) : (term104 P Q) = (term103 P Q).
Proof. exact (@lem1603339 real P Q). Qed.
Lemma lem1603341 (x : real) : (term106 x) = (term105 x).
Proof. exact (@lem1603340 (term61 x) (term107 x)). Qed.
Lemma lem1603342 (x : real) (y : real) : (term108 x y) = (term54 x y).
Proof. exact (eq_refl (term108 x y)). Qed.
Lemma lem1603343 (x : real) : (term113 x) = (term107 x).
Proof. exact (fun_ext (fun y : real => @lem1603342 x y)). Qed.
Lemma lem1603344 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603345 (x : real) : (term114 x) = (term115 x).
Proof. exact (MK_COMB (@lem1603344) (@lem1603343 x)). Qed.
Lemma lem1603346 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1603347 (x : real) : (term106 x) = (term116 x).
Proof. exact (MK_COMB (@lem1603346 x) (@lem1603345 x)). Qed.
Lemma lem1603348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1603349 (x : real) : (term151 x) = (term152 x).
Proof. exact (MK_COMB (@lem1603348) (@lem1603347 x)). Qed.
Lemma lem1603350 (x : real) (y : real) : (term108 x y) = (term54 x y).
Proof. exact (eq_refl (term108 x y)). Qed.
Lemma lem1603351 (x : real) : (term57 x) = (term57 x).
Proof. exact (eq_refl (term57 x)). Qed.
Lemma lem1603352 (x : real) (y : real) : (term109 x y) = (term59 x y).
Proof. exact (MK_COMB (@lem1603351 x) (@lem1603350 x y)). Qed.
Lemma lem1603353 (x : real) : (term110 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1603352 x y)). Qed.
Lemma lem1603354 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603355 (x : real) : (term105 x) = (term70 x).
Proof. exact (MK_COMB (@lem1603354) (@lem1603353 x)). Qed.
Lemma lem1603356 (x : real) : ((term106 x) = (term105 x)) = ((term116 x) = (term70 x)).
Proof. exact (MK_COMB (@lem1603349 x) (@lem1603355 x)). Qed.
Lemma lem1603357 (x : real) : (term116 x) = (term70 x).
Proof. exact (EQ_MP (@lem1603356 x) (@lem1603341 x)). Qed.
Lemma lem1603358 (x : real) : (term144 x) = (term70 x).
Proof. exact (TRANS (@lem1603337 x) (@lem1603357 x)). Qed.
Lemma lem1603359 : term145 = term76.
Proof. exact (fun_ext (fun x : real => @lem1603358 x)). Qed.
Lemma lem1603360 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603361 : term146 = term77.
Proof. exact (MK_COMB (@lem1603360) (@lem1603359)). Qed.
Lemma lem1603362 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603363 : term147 = term98.
Proof. exact (MK_COMB (@lem1603362) (@lem1603361)). Qed.
Lemma lem1603364 : term96 = term96.
Proof. exact (eq_refl term96). Qed.
Lemma lem1603365 : term148 = term100.
Proof. exact (MK_COMB (@lem1603363) (@lem1603364)). Qed.
Lemma lem1603367 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1603368 (P : real -> Prop) (Q : real -> Prop) : (term120 P Q) = (term119 P Q).
Proof. exact (@lem1603367 real P Q). Qed.
Lemma lem1603369 : term153 = term154.
Proof. exact (@lem1603368 term76 term95). Qed.
Lemma lem1603370 (x : real) : (term155 x) = (term70 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1603371 : term156 = term76.
Proof. exact (fun_ext (fun x : real => @lem1603370 x)). Qed.
Lemma lem1603372 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603373 : term157 = term77.
Proof. exact (MK_COMB (@lem1603372) (@lem1603371)). Qed.
Lemma lem1603374 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603375 : term158 = term98.
Proof. exact (MK_COMB (@lem1603374) (@lem1603373)). Qed.
Lemma lem1603376 (x : real) : (term159 x) = (term89 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1603377 : term160 = term95.
Proof. exact (fun_ext (fun x : real => @lem1603376 x)). Qed.
Lemma lem1603378 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603379 : term161 = term96.
Proof. exact (MK_COMB (@lem1603378) (@lem1603377)). Qed.
Lemma lem1603380 : term153 = term100.
Proof. exact (MK_COMB (@lem1603375) (@lem1603379)). Qed.
Lemma lem1603381 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1603382 : term162 = term163.
Proof. exact (MK_COMB (@lem1603381) (@lem1603380)). Qed.
Lemma lem1603383 (x : real) : (term155 x) = (term70 x).
Proof. exact (eq_refl (term155 x)). Qed.
Lemma lem1603384 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603385 (x : real) : (term164 x) = (term165 x).
Proof. exact (MK_COMB (@lem1603384) (@lem1603383 x)). Qed.
Lemma lem1603386 (x : real) : (term159 x) = (term89 x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem1603387 (x : real) : (term166 x) = (term167 x).
Proof. exact (MK_COMB (@lem1603385 x) (@lem1603386 x)). Qed.
Lemma lem1603388 : term168 = term169.
Proof. exact (fun_ext (fun x : real => @lem1603387 x)). Qed.
Lemma lem1603389 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603390 : term154 = term170.
Proof. exact (MK_COMB (@lem1603389) (@lem1603388)). Qed.
Lemma lem1603391 : (term153 = term154) = (term100 = term170).
Proof. exact (MK_COMB (@lem1603382) (@lem1603390)). Qed.
Lemma lem1603392 : term100 = term170.
Proof. exact (EQ_MP (@lem1603391) (@lem1603369)). Qed.
Lemma lem1603394 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term118 A P Q) = (term117 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1603395 (P : real -> Prop) (Q : real -> Prop) : (term120 P Q) = (term119 P Q).
Proof. exact (@lem1603394 real P Q). Qed.
Lemma lem1603396 (x : real) : (term171 x) = (term172 x).
Proof. exact (@lem1603395 (term69 x) (term88 x)). Qed.
Lemma lem1603397 (x : real) (y : real) : (term173 x y) = (term59 x y).
Proof. exact (eq_refl (term173 x y)). Qed.
Lemma lem1603398 (x : real) : (term174 x) = (term69 x).
Proof. exact (fun_ext (fun y : real => @lem1603397 x y)). Qed.
Lemma lem1603399 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603400 (x : real) : (term175 x) = (term70 x).
Proof. exact (MK_COMB (@lem1603399) (@lem1603398 x)). Qed.
Lemma lem1603401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603402 (x : real) : (term176 x) = (term165 x).
Proof. exact (MK_COMB (@lem1603401) (@lem1603400 x)). Qed.
Lemma lem1603403 (y : real) (x : real) : (term177 x y) = (term81 y x).
Proof. exact (eq_refl (term177 x y)). Qed.
Lemma lem1603404 (x : real) : (term178 x) = (term88 x).
Proof. exact (fun_ext (fun y : real => @lem1603403 y x)). Qed.
Lemma lem1603405 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603406 (x : real) : (term179 x) = (term89 x).
Proof. exact (MK_COMB (@lem1603405) (@lem1603404 x)). Qed.
Lemma lem1603407 (x : real) : (term171 x) = (term167 x).
Proof. exact (MK_COMB (@lem1603402 x) (@lem1603406 x)). Qed.
Lemma lem1603408 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1603409 (x : real) : (term180 x) = (term181 x).
Proof. exact (MK_COMB (@lem1603408) (@lem1603407 x)). Qed.
Lemma lem1603410 (x : real) (y : real) : (term173 x y) = (term59 x y).
Proof. exact (eq_refl (term173 x y)). Qed.
Lemma lem1603411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1603412 (x : real) (y : real) : (term182 x y) = (term183 x y).
Proof. exact (MK_COMB (@lem1603411) (@lem1603410 x y)). Qed.
Lemma lem1603413 (y : real) (x : real) : (term177 x y) = (term81 y x).
Proof. exact (eq_refl (term177 x y)). Qed.
Lemma lem1603414 (y : real) (x : real) : (term184 x y) = (term185 y x).
Proof. exact (MK_COMB (@lem1603412 x y) (@lem1603413 y x)). Qed.
Lemma lem1603415 (x : real) : (term186 x) = (term187 x).
Proof. exact (fun_ext (fun y : real => @lem1603414 y x)). Qed.
Lemma lem1603416 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603417 (x : real) : (term172 x) = (term188 x).
Proof. exact (MK_COMB (@lem1603416) (@lem1603415 x)). Qed.
Lemma lem1603418 (x : real) : ((term171 x) = (term172 x)) = ((term167 x) = (term188 x)).
Proof. exact (MK_COMB (@lem1603409 x) (@lem1603417 x)). Qed.
Lemma lem1603419 (x : real) : (term167 x) = (term188 x).
Proof. exact (EQ_MP (@lem1603418 x) (@lem1603396 x)). Qed.
Lemma lem1603420 : term169 = term189.
Proof. exact (fun_ext (fun x : real => @lem1603419 x)). Qed.
Lemma lem1603421 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1603422 : term170 = term190.
Proof. exact (MK_COMB (@lem1603421) (@lem1603420)). Qed.
Lemma lem1603423 : term100 = term190.
Proof. exact (TRANS (@lem1603392) (@lem1603422)). Qed.
Lemma lem1603424 : term148 = term190.
Proof. exact (TRANS (@lem1603365) (@lem1603423)). Qed.
Lemma lem1603425 : term100 = term190.
Proof. exact (TRANS (@lem1603308) (@lem1603424)). Qed.
Lemma lem1603426 : term3 = term190.
Proof. exact (TRANS (@lem1603051) (@lem1603425)). Qed.
Lemma lem1603427 (h1 : term3) : term190.
Proof. exact (EQ_MP (@lem1603426) (@lem1602960 h1)). Qed.
Lemma lem1603428 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1603429 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1603428 x)). Qed.
Lemma lem1603430 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603439 : term41 = term41.
Proof. exact (MK_COMB (@lem1603430) (@lem1603429)). Qed.
Lemma lem1603440 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1603439) (@lem1602961 h1)). Qed.
Lemma lem1603441 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1603442 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1603441 x)). Qed.
Lemma lem1603443 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603452 : term38 = term38.
Proof. exact (MK_COMB (@lem1603443) (@lem1603442)). Qed.
Lemma lem1603453 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1603452) (@lem1602962 h1)). Qed.
Lemma lem1603469 (z : real) (x : real) (y : real) : ((term191 x y z) = (real_le x y)) = (term192 z x y).
Proof. exact (@lem17784 (term191 x y z) (real_le x y)). Qed.
Lemma lem1603471 (z : real) : (term193 z) = (term193 z).
Proof. exact (eq_refl (term193 z)). Qed.
Lemma lem1603472 (z : real) (x : real) (y : real) : (term194 z x y) = (term195 z x y).
Proof. exact (MK_COMB (@lem1603471 z) (@lem1603469 z x y)). Qed.
Lemma lem1603473 (z : real) (x : real) (y : real) : (term28 z x y) = (term194 z x y).
Proof. exact (@lem17265 (term61 z) ((term191 x y z) = (real_le x y))). Qed.
Lemma lem1603474 (z : real) (x : real) (y : real) : (term28 z x y) = (term195 z x y).
Proof. exact (TRANS (@lem1603473 z x y) (@lem1603472 z x y)). Qed.
Lemma lem1603475 (x : real) (y : real) : (term29 x y) = (term196 x y).
Proof. exact (fun_ext (fun z : real => @lem1603474 z x y)). Qed.
Lemma lem1603476 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603477 (x : real) (y : real) : (term30 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1603476) (@lem1603475 x y)). Qed.
Lemma lem1603478 (x : real) : (term31 x) = (term198 x).
Proof. exact (fun_ext (fun y : real => @lem1603477 x y)). Qed.
Lemma lem1603479 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603480 (x : real) : (term32 x) = (term199 x).
Proof. exact (MK_COMB (@lem1603479) (@lem1603478 x)). Qed.
Lemma lem1603481 : term33 = term200.
Proof. exact (fun_ext (fun x : real => @lem1603480 x)). Qed.
Lemma lem1603482 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603543 : term34 = term201.
Proof. exact (MK_COMB (@lem1603482) (@lem1603481)). Qed.
Lemma lem1603544 (h1 : term34) : term201.
Proof. exact (EQ_MP (@lem1603543) (@lem1602963 h1)). Qed.
Lemma lem1603560 (z : real) (x : real) (y : real) : ((term202 x z y) = (real_le x y)) = (term203 z x y).
Proof. exact (@lem17784 (term202 x z y) (real_le x y)). Qed.
Lemma lem1603562 (z : real) : (term193 z) = (term193 z).
Proof. exact (eq_refl (term193 z)). Qed.
Lemma lem1603563 (z : real) (x : real) (y : real) : (term204 z x y) = (term205 z x y).
Proof. exact (MK_COMB (@lem1603562 z) (@lem1603560 z x y)). Qed.
Lemma lem1603564 (z : real) (x : real) (y : real) : (term22 z x y) = (term204 z x y).
Proof. exact (@lem17265 (term61 z) ((term202 x z y) = (real_le x y))). Qed.
Lemma lem1603565 (z : real) (x : real) (y : real) : (term22 z x y) = (term205 z x y).
Proof. exact (TRANS (@lem1603564 z x y) (@lem1603563 z x y)). Qed.
Lemma lem1603566 (x : real) (y : real) : (term23 x y) = (term206 x y).
Proof. exact (fun_ext (fun z : real => @lem1603565 z x y)). Qed.
Lemma lem1603567 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603568 (x : real) (y : real) : (term24 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1603567) (@lem1603566 x y)). Qed.
Lemma lem1603569 (x : real) : (term25 x) = (term208 x).
Proof. exact (fun_ext (fun y : real => @lem1603568 x y)). Qed.
Lemma lem1603570 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603571 (x : real) : (term26 x) = (term209 x).
Proof. exact (MK_COMB (@lem1603570) (@lem1603569 x)). Qed.
Lemma lem1603572 : term27 = term210.
Proof. exact (fun_ext (fun x : real => @lem1603571 x)). Qed.
Lemma lem1603573 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603634 : term10 = term211.
Proof. exact (MK_COMB (@lem1603573) (@lem1603572)). Qed.
Lemma lem1603635 (h1 : term10) : term211.
Proof. exact (EQ_MP (@lem1603634) (@lem1602964 h1)). Qed.
Lemma lem1603636 (x : real) (h1 : term188 x) : term188 x.
Proof. exact (h1). Qed.
Lemma lem1603654 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1603655 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1603654 x)). Qed.
Lemma lem1603656 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603657 : term41 = term41.
Proof. exact (MK_COMB (@lem1603656) (@lem1603655)). Qed.
Lemma lem1603658 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1603657) (@lem1603440 h1)). Qed.
Lemma lem1603675 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1603676 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1603675 x)). Qed.
Lemma lem1603677 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603678 : term38 = term38.
Proof. exact (MK_COMB (@lem1603677) (@lem1603676)). Qed.
Lemma lem1603679 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1603678) (@lem1603453 h1)). Qed.
Lemma lem1603742 (z : real) (x : real) (y : real) : (term195 z x y) = (term195 z x y).
Proof. exact (eq_refl (term195 z x y)). Qed.
Lemma lem1603743 (x : real) (y : real) : (term196 x y) = (term196 x y).
Proof. exact (fun_ext (fun z : real => @lem1603742 z x y)). Qed.
Lemma lem1603744 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603745 (x : real) (y : real) : (term197 x y) = (term197 x y).
Proof. exact (MK_COMB (@lem1603744) (@lem1603743 x y)). Qed.
Lemma lem1603746 (x : real) : (term198 x) = (term198 x).
Proof. exact (fun_ext (fun y : real => @lem1603745 x y)). Qed.
Lemma lem1603747 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603748 (x : real) : (term199 x) = (term199 x).
Proof. exact (MK_COMB (@lem1603747) (@lem1603746 x)). Qed.
Lemma lem1603749 : term200 = term200.
Proof. exact (fun_ext (fun x : real => @lem1603748 x)). Qed.
Lemma lem1603750 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603751 : term201 = term201.
Proof. exact (MK_COMB (@lem1603750) (@lem1603749)). Qed.
Lemma lem1603752 (h1 : term34) : term201.
Proof. exact (EQ_MP (@lem1603751) (@lem1603544 h1)). Qed.
Lemma lem1603815 (z : real) (x : real) (y : real) : (term205 z x y) = (term205 z x y).
Proof. exact (eq_refl (term205 z x y)). Qed.
Lemma lem1603816 (x : real) (y : real) : (term206 x y) = (term206 x y).
Proof. exact (fun_ext (fun z : real => @lem1603815 z x y)). Qed.
Lemma lem1603817 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603818 (x : real) (y : real) : (term207 x y) = (term207 x y).
Proof. exact (MK_COMB (@lem1603817) (@lem1603816 x y)). Qed.
Lemma lem1603819 (x : real) : (term208 x) = (term208 x).
Proof. exact (fun_ext (fun y : real => @lem1603818 x y)). Qed.
Lemma lem1603820 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603821 (x : real) : (term209 x) = (term209 x).
Proof. exact (MK_COMB (@lem1603820) (@lem1603819 x)). Qed.
Lemma lem1603822 : term210 = term210.
Proof. exact (fun_ext (fun x : real => @lem1603821 x)). Qed.
Lemma lem1603823 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603824 : term211 = term211.
Proof. exact (MK_COMB (@lem1603823) (@lem1603822)). Qed.
Lemma lem1603825 (h1 : term10) : term211.
Proof. exact (EQ_MP (@lem1603824) (@lem1603635 h1)). Qed.
Lemma lem1603967 (y : real) (x : real) (h1 : term185 y x) : term185 y x.
Proof. exact (h1). Qed.
Lemma lem1603968 (x : real) (y : real) (h1 : term59 x y) : term59 x y.
Proof. exact (h1). Qed.
Lemma lem1603969 (y : real) (x : real) (h1 : term81 y x) : term81 y x.
Proof. exact (h1). Qed.
Lemma lem1603970 (x : real) (y : real) (h1 : term59 x y) : term54 x y.
Proof. exact (proj2 (@lem1603968 x y h1)). Qed.
Lemma lem1603972 (x : real) (y : real) (h1 : term126 x y) : term126 x y.
Proof. exact (h1). Qed.
Lemma lem1603973 (x : real) (y : real) (h1 : term130 x y) : term130 x y.
Proof. exact (h1). Qed.
Lemma lem1603978 (y : real) (x : real) (h1 : term81 y x) : term79 y x.
Proof. exact (proj2 (@lem1603969 y x h1)). Qed.
Lemma lem1603980 (y : real) (x : real) (h1 : term212 y x) : term212 y x.
Proof. exact (h1). Qed.
Lemma lem1603981 (y : real) (x : real) (h1 : term213 y x) : term213 y x.
Proof. exact (h1). Qed.
Lemma lem1603987 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1603988 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1603987 x)). Qed.
Lemma lem1603989 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1603991 : term41 = term41.
Proof. exact (MK_COMB (@lem1603989) (@lem1603988)). Qed.
Lemma lem1603992 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1603991) (@lem1603658 h1)). Qed.
Lemma lem1604070 (z : real) (x : real) (y : real) : (term205 z x y) = (term214 z x y).
Proof. exact (@lem19490 (term215 z x y) (term216 z) (term217 z x y)). Qed.
Lemma lem1604071 (x : real) (y : real) : (term206 x y) = (term218 x y).
Proof. exact (fun_ext (fun z : real => @lem1604070 z x y)). Qed.
Lemma lem1604072 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604073 (x : real) (y : real) : (term207 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1604072) (@lem1604071 x y)). Qed.
Lemma lem1604074 (x : real) : (term208 x) = (term220 x).
Proof. exact (fun_ext (fun y : real => @lem1604073 x y)). Qed.
Lemma lem1604075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604076 (x : real) : (term209 x) = (term221 x).
Proof. exact (MK_COMB (@lem1604075) (@lem1604074 x)). Qed.
Lemma lem1604077 : term210 = term222.
Proof. exact (fun_ext (fun x : real => @lem1604076 x)). Qed.
Lemma lem1604078 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604080 : term211 = term223.
Proof. exact (MK_COMB (@lem1604078) (@lem1604077)). Qed.
Lemma lem1604081 (h1 : term10) : term223.
Proof. exact (EQ_MP (@lem1604080) (@lem1603825 h1)). Qed.
Lemma lem1604095 (x : real) : ((term39 x) = term36) = ((term39 x) = term36).
Proof. exact (eq_refl ((term39 x) = term36)). Qed.
Lemma lem1604096 : term40 = term40.
Proof. exact (fun_ext (fun x : real => @lem1604095 x)). Qed.
Lemma lem1604097 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604099 : term41 = term41.
Proof. exact (MK_COMB (@lem1604097) (@lem1604096)). Qed.
Lemma lem1604100 (h1 : term41) : term41.
Proof. exact (EQ_MP (@lem1604099) (@lem1603658 h1)). Qed.
Lemma lem1604178 (z : real) (x : real) (y : real) : (term205 z x y) = (term214 z x y).
Proof. exact (@lem19490 (term215 z x y) (term216 z) (term217 z x y)). Qed.
Lemma lem1604179 (x : real) (y : real) : (term206 x y) = (term218 x y).
Proof. exact (fun_ext (fun z : real => @lem1604178 z x y)). Qed.
Lemma lem1604180 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604181 (x : real) (y : real) : (term207 x y) = (term219 x y).
Proof. exact (MK_COMB (@lem1604180) (@lem1604179 x y)). Qed.
Lemma lem1604182 (x : real) : (term208 x) = (term220 x).
Proof. exact (fun_ext (fun y : real => @lem1604181 x y)). Qed.
Lemma lem1604183 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604184 (x : real) : (term209 x) = (term221 x).
Proof. exact (MK_COMB (@lem1604183) (@lem1604182 x)). Qed.
Lemma lem1604185 : term210 = term222.
Proof. exact (fun_ext (fun x : real => @lem1604184 x)). Qed.
Lemma lem1604186 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604188 : term211 = term223.
Proof. exact (MK_COMB (@lem1604186) (@lem1604185)). Qed.
Lemma lem1604189 (h1 : term10) : term223.
Proof. exact (EQ_MP (@lem1604188) (@lem1603825 h1)). Qed.
Lemma lem1604210 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1604211 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1604210 x)). Qed.
Lemma lem1604212 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604214 : term38 = term38.
Proof. exact (MK_COMB (@lem1604212) (@lem1604211)). Qed.
Lemma lem1604215 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1604214) (@lem1603679 h1)). Qed.
Lemma lem1604245 (z : real) (x : real) (y : real) : (term195 z x y) = (term224 z x y).
Proof. exact (@lem19490 (term225 z x y) (term216 z) (term226 z x y)). Qed.
Lemma lem1604246 (x : real) (y : real) : (term196 x y) = (term227 x y).
Proof. exact (fun_ext (fun z : real => @lem1604245 z x y)). Qed.
Lemma lem1604247 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604248 (x : real) (y : real) : (term197 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem1604247) (@lem1604246 x y)). Qed.
Lemma lem1604249 (x : real) : (term198 x) = (term229 x).
Proof. exact (fun_ext (fun y : real => @lem1604248 x y)). Qed.
Lemma lem1604250 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604251 (x : real) : (term199 x) = (term230 x).
Proof. exact (MK_COMB (@lem1604250) (@lem1604249 x)). Qed.
Lemma lem1604252 : term200 = term231.
Proof. exact (fun_ext (fun x : real => @lem1604251 x)). Qed.
Lemma lem1604253 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604255 : term201 = term232.
Proof. exact (MK_COMB (@lem1604253) (@lem1604252)). Qed.
Lemma lem1604256 (h1 : term34) : term232.
Proof. exact (EQ_MP (@lem1604255) (@lem1603752 h1)). Qed.
Lemma lem1604318 (x : real) : ((term35 x) = term36) = ((term35 x) = term36).
Proof. exact (eq_refl ((term35 x) = term36)). Qed.
Lemma lem1604319 : term37 = term37.
Proof. exact (fun_ext (fun x : real => @lem1604318 x)). Qed.
Lemma lem1604320 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604322 : term38 = term38.
Proof. exact (MK_COMB (@lem1604320) (@lem1604319)). Qed.
Lemma lem1604323 (h1 : term38) : term38.
Proof. exact (EQ_MP (@lem1604322) (@lem1603679 h1)). Qed.
Lemma lem1604353 (z : real) (x : real) (y : real) : (term195 z x y) = (term224 z x y).
Proof. exact (@lem19490 (term225 z x y) (term216 z) (term226 z x y)). Qed.
Lemma lem1604354 (x : real) (y : real) : (term196 x y) = (term227 x y).
Proof. exact (fun_ext (fun z : real => @lem1604353 z x y)). Qed.
Lemma lem1604355 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604356 (x : real) (y : real) : (term197 x y) = (term228 x y).
Proof. exact (MK_COMB (@lem1604355) (@lem1604354 x y)). Qed.
Lemma lem1604357 (x : real) : (term198 x) = (term229 x).
Proof. exact (fun_ext (fun y : real => @lem1604356 x y)). Qed.
Lemma lem1604358 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604359 (x : real) : (term199 x) = (term230 x).
Proof. exact (MK_COMB (@lem1604358) (@lem1604357 x)). Qed.
Lemma lem1604360 : term200 = term231.
Proof. exact (fun_ext (fun x : real => @lem1604359 x)). Qed.
Lemma lem1604361 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1604363 : term201 = term232.
Proof. exact (MK_COMB (@lem1604361) (@lem1604360)). Qed.
Lemma lem1604364 (h1 : term34) : term232.
Proof. exact (EQ_MP (@lem1604363) (@lem1603752 h1)). Qed.
Lemma lem1604418 (_25293 : real) (h1 : term41) : term233 _25293.
Proof. exact (@lem1603992 h1 _25293). Qed.
Lemma lem1604419 (_25293 : real) : (term233 _25293) = ((term39 _25293) = term36).
Proof. exact (eq_refl (term233 _25293)). Qed.
Lemma lem1604433 (_25298 : real) (h1 : term10) : term234 _25298.
Proof. exact (@lem1604081 h1 _25298). Qed.
Lemma lem1604434 (_25298 : real) : (term234 _25298) = (term221 _25298).
Proof. exact (eq_refl (term234 _25298)). Qed.
Lemma lem1604435 (_25298 : real) (h1 : term10) : term221 _25298.
Proof. exact (EQ_MP (@lem1604434 _25298) (@lem1604433 _25298 h1)). Qed.
Lemma lem1604436 (_25298 : real) (_25299 : real) (h1 : term10) : term235 _25298 _25299.
Proof. exact (@lem1604435 _25298 h1 _25299). Qed.
Lemma lem1604437 (_25298 : real) (_25299 : real) : (term235 _25298 _25299) = (term219 _25298 _25299).
Proof. exact (eq_refl (term235 _25298 _25299)). Qed.
Lemma lem1604438 (_25298 : real) (_25299 : real) (h1 : term10) : term219 _25298 _25299.
Proof. exact (EQ_MP (@lem1604437 _25298 _25299) (@lem1604436 _25298 _25299 h1)). Qed.
Lemma lem1604439 (_25298 : real) (_25299 : real) (_25300 : real) (h1 : term10) : term236 _25298 _25299 _25300.
Proof. exact (@lem1604438 _25298 _25299 h1 _25300). Qed.
Lemma lem1604440 (_25300 : real) (_25298 : real) (_25299 : real) : (term236 _25298 _25299 _25300) = (term214 _25300 _25298 _25299).
Proof. exact (eq_refl (term236 _25298 _25299 _25300)). Qed.
Lemma lem1604441 (_25300 : real) (_25298 : real) (_25299 : real) (h1 : term10) : term214 _25300 _25298 _25299.
Proof. exact (EQ_MP (@lem1604440 _25300 _25298 _25299) (@lem1604439 _25298 _25299 _25300 h1)). Qed.
Lemma lem1604442 (_25301 : real) (h1 : term41) : term233 _25301.
Proof. exact (@lem1604100 h1 _25301). Qed.
Lemma lem1604443 (_25301 : real) : (term233 _25301) = ((term39 _25301) = term36).
Proof. exact (eq_refl (term233 _25301)). Qed.
Lemma lem1604457 (_25306 : real) (h1 : term10) : term234 _25306.
Proof. exact (@lem1604189 h1 _25306). Qed.
Lemma lem1604458 (_25306 : real) : (term234 _25306) = (term221 _25306).
Proof. exact (eq_refl (term234 _25306)). Qed.
Lemma lem1604459 (_25306 : real) (h1 : term10) : term221 _25306.
Proof. exact (EQ_MP (@lem1604458 _25306) (@lem1604457 _25306 h1)). Qed.
Lemma lem1604460 (_25306 : real) (_25307 : real) (h1 : term10) : term235 _25306 _25307.
Proof. exact (@lem1604459 _25306 h1 _25307). Qed.
Lemma lem1604461 (_25306 : real) (_25307 : real) : (term235 _25306 _25307) = (term219 _25306 _25307).
Proof. exact (eq_refl (term235 _25306 _25307)). Qed.
Lemma lem1604462 (_25306 : real) (_25307 : real) (h1 : term10) : term219 _25306 _25307.
Proof. exact (EQ_MP (@lem1604461 _25306 _25307) (@lem1604460 _25306 _25307 h1)). Qed.
Lemma lem1604463 (_25306 : real) (_25307 : real) (_25308 : real) (h1 : term10) : term236 _25306 _25307 _25308.
Proof. exact (@lem1604462 _25306 _25307 h1 _25308). Qed.
Lemma lem1604464 (_25308 : real) (_25306 : real) (_25307 : real) : (term236 _25306 _25307 _25308) = (term214 _25308 _25306 _25307).
Proof. exact (eq_refl (term236 _25306 _25307 _25308)). Qed.
Lemma lem1604465 (_25308 : real) (_25306 : real) (_25307 : real) (h1 : term10) : term214 _25308 _25306 _25307.
Proof. exact (EQ_MP (@lem1604464 _25308 _25306 _25307) (@lem1604463 _25306 _25307 _25308 h1)). Qed.
Lemma lem1604469 (_25310 : real) (h1 : term38) : term237 _25310.
Proof. exact (@lem1604215 h1 _25310). Qed.
Lemma lem1604470 (_25310 : real) : (term237 _25310) = ((term35 _25310) = term36).
Proof. exact (eq_refl (term237 _25310)). Qed.
Lemma lem1604472 (_25311 : real) (h1 : term34) : term238 _25311.
Proof. exact (@lem1604256 h1 _25311). Qed.
Lemma lem1604473 (_25311 : real) : (term238 _25311) = (term230 _25311).
Proof. exact (eq_refl (term238 _25311)). Qed.
Lemma lem1604474 (_25311 : real) (h1 : term34) : term230 _25311.
Proof. exact (EQ_MP (@lem1604473 _25311) (@lem1604472 _25311 h1)). Qed.
Lemma lem1604475 (_25311 : real) (_25312 : real) (h1 : term34) : term239 _25311 _25312.
Proof. exact (@lem1604474 _25311 h1 _25312). Qed.
Lemma lem1604476 (_25311 : real) (_25312 : real) : (term239 _25311 _25312) = (term228 _25311 _25312).
Proof. exact (eq_refl (term239 _25311 _25312)). Qed.
Lemma lem1604477 (_25311 : real) (_25312 : real) (h1 : term34) : term228 _25311 _25312.
Proof. exact (EQ_MP (@lem1604476 _25311 _25312) (@lem1604475 _25311 _25312 h1)). Qed.
Lemma lem1604478 (_25311 : real) (_25312 : real) (_25313 : real) (h1 : term34) : term240 _25311 _25312 _25313.
Proof. exact (@lem1604477 _25311 _25312 h1 _25313). Qed.
Lemma lem1604479 (_25313 : real) (_25311 : real) (_25312 : real) : (term240 _25311 _25312 _25313) = (term224 _25313 _25311 _25312).
Proof. exact (eq_refl (term240 _25311 _25312 _25313)). Qed.
Lemma lem1604480 (_25313 : real) (_25311 : real) (_25312 : real) (h1 : term34) : term224 _25313 _25311 _25312.
Proof. exact (EQ_MP (@lem1604479 _25313 _25311 _25312) (@lem1604478 _25311 _25312 _25313 h1)). Qed.
Lemma lem1604493 (_25318 : real) (h1 : term38) : term237 _25318.
Proof. exact (@lem1604323 h1 _25318). Qed.
Lemma lem1604494 (_25318 : real) : (term237 _25318) = ((term35 _25318) = term36).
Proof. exact (eq_refl (term237 _25318)). Qed.
Lemma lem1604496 (_25319 : real) (h1 : term34) : term238 _25319.
Proof. exact (@lem1604364 h1 _25319). Qed.
Lemma lem1604497 (_25319 : real) : (term238 _25319) = (term230 _25319).
Proof. exact (eq_refl (term238 _25319)). Qed.
Lemma lem1604498 (_25319 : real) (h1 : term34) : term230 _25319.
Proof. exact (EQ_MP (@lem1604497 _25319) (@lem1604496 _25319 h1)). Qed.
Lemma lem1604499 (_25319 : real) (_25320 : real) (h1 : term34) : term239 _25319 _25320.
Proof. exact (@lem1604498 _25319 h1 _25320). Qed.
Lemma lem1604500 (_25319 : real) (_25320 : real) : (term239 _25319 _25320) = (term228 _25319 _25320).
Proof. exact (eq_refl (term239 _25319 _25320)). Qed.
Lemma lem1604501 (_25319 : real) (_25320 : real) (h1 : term34) : term228 _25319 _25320.
Proof. exact (EQ_MP (@lem1604500 _25319 _25320) (@lem1604499 _25319 _25320 h1)). Qed.
Lemma lem1604502 (_25319 : real) (_25320 : real) (_25321 : real) (h1 : term34) : term240 _25319 _25320 _25321.
Proof. exact (@lem1604501 _25319 _25320 h1 _25321). Qed.
Lemma lem1604503 (_25321 : real) (_25319 : real) (_25320 : real) : (term240 _25319 _25320 _25321) = (term224 _25321 _25319 _25320).
Proof. exact (eq_refl (term240 _25319 _25320 _25321)). Qed.
Lemma lem1604504 (_25321 : real) (_25319 : real) (_25320 : real) (h1 : term34) : term224 _25321 _25319 _25320.
Proof. exact (EQ_MP (@lem1604503 _25321 _25319 _25320) (@lem1604502 _25319 _25320 _25321 h1)). Qed.
Lemma lem1604539 (x : real) (y : real) (h1 : term126 x y) : term241 y.
Proof. exact (proj2 (@lem1603972 x y h1)). Qed.
Lemma lem1604559 (_25300 : real) (_25298 : real) (_25299 : real) (h1 : term10) : term242 _25300 _25298 _25299.
Proof. exact (proj2 (@lem1604441 _25300 _25298 _25299 h1)). Qed.
Lemma lem1604587 (x : real) (y : real) (h1 : term130 x y) : term243 x y.
Proof. exact (proj1 (@lem1603973 x y h1)). Qed.
Lemma lem1604599 (_25308 : real) (_25306 : real) (_25307 : real) (h1 : term10) : term244 _25308 _25306 _25307.
Proof. exact (proj1 (@lem1604465 _25308 _25306 _25307 h1)). Qed.
Lemma lem1604639 (y : real) (x : real) (h1 : term212 y x) : term241 x.
Proof. exact (proj2 (@lem1603980 y x h1)). Qed.
Lemma lem1604679 (_25313 : real) (_25311 : real) (_25312 : real) (h1 : term34) : term245 _25313 _25311 _25312.
Proof. exact (proj2 (@lem1604480 _25313 _25311 _25312 h1)). Qed.
Lemma lem1604687 (y : real) (x : real) (h1 : term213 y x) : term243 x y.
Proof. exact (proj1 (@lem1603981 y x h1)). Qed.
Lemma lem1604719 (_25321 : real) (_25319 : real) (_25320 : real) (h1 : term34) : term246 _25321 _25319 _25320.
Proof. exact (proj1 (@lem1604504 _25321 _25319 _25320 h1)). Qed.
Lemma lem1604730 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1604731 (_25325 : real) (_25327 : real) (h1 : _25325 = _25327) : _25325 = _25327.
Proof. exact (h1). Qed.
Lemma lem1604732 (_25326 : real) (_25328 : real) (h1 : _25326 = _25328) : _25326 = _25328.
Proof. exact (h1). Qed.
Lemma lem1604733 (_25325 : real) (_25327 : real) (h1 : _25325 = _25327) : (real_le _25325) = (real_le _25327).
Proof. exact (MK_COMB (@lem1604730) (@lem1604731 _25325 _25327 h1)). Qed.
Lemma lem1604734 (_25325 : real) (_25327 : real) (_25326 : real) (_25328 : real) (h1 : _25325 = _25327) (h2 : _25326 = _25328) : (real_le _25325 _25326) = (real_le _25327 _25328).
Proof. exact (MK_COMB (@lem1604733 _25325 _25327 h1) (@lem1604732 _25326 _25328 h2)). Qed.
Lemma lem1604736 (b : Prop) (a : Prop) : term247 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1604737 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : term248 _25327 _25328 _25325 _25326.
Proof. exact (@lem1604736 (real_le _25327 _25328) (real_le _25325 _25326)). Qed.
Lemma lem1604738 (_25325 : real) (_25327 : real) (_25326 : real) (_25328 : real) (h1 : _25325 = _25327) (h2 : _25326 = _25328) : term249 _25327 _25328 _25325 _25326.
Proof. exact (@lem1604737 _25327 _25328 _25325 _25326 (@lem1604734 _25325 _25327 _25326 _25328 h1 h2)). Qed.
Lemma lem1604739 (_25328 : real) (_25326 : real) (_25325 : real) (_25327 : real) (h1 : _25325 = _25327) : term250 _25327 _25328 _25325 _25326.
Proof. exact (fun h0 : _25326 = _25328 => @lem1604738 _25325 _25327 _25326 _25328 h1 h0). Qed.
Lemma lem1604741 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1604742 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term250 _25327 _25328 _25325 _25326) = (term252 _25327 _25328 _25325 _25326).
Proof. exact (@lem1604741 (_25326 = _25328) (term249 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1604743 (_25328 : real) (_25326 : real) (_25325 : real) (_25327 : real) (h1 : _25325 = _25327) : term252 _25327 _25328 _25325 _25326.
Proof. exact (EQ_MP (@lem1604742 _25327 _25328 _25325 _25326) (@lem1604739 _25328 _25326 _25325 _25327 h1)). Qed.
Lemma lem1604744 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : term253 _25327 _25328 _25325 _25326.
Proof. exact (fun h0 : _25325 = _25327 => @lem1604743 _25328 _25326 _25325 _25327 h0). Qed.
Lemma lem1604746 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1604747 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term253 _25327 _25328 _25325 _25326) = (term254 _25327 _25328 _25325 _25326).
Proof. exact (@lem1604746 (_25325 = _25327) (term252 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1604748 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : term254 _25327 _25328 _25325 _25326.
Proof. exact (EQ_MP (@lem1604747 _25327 _25328 _25325 _25326) (@lem1604744 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1604800 (x : real) (y : real) (z : real) : term255 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1604804 (x : real) (y : real) (h1 : term59 x y) : term61 x.
Proof. exact (proj1 (@lem1603968 x y h1)). Qed.
Lemma lem1604805 (x : real) (y : real) (h1 : term59 x y) : term256 x.
Proof. exact (fun h0 : term216 x => @lem1604804 x y h1). Qed.
Lemma lem1604807 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1604808 (x : real) : (term256 x) = (term61 x).
Proof. exact (@lem1604807 (term61 x)). Qed.
Lemma lem1604809 (x : real) (y : real) (h1 : term59 x y) : term61 x.
Proof. exact (EQ_MP (@lem1604808 x) (@lem1604805 x y h1)). Qed.
Lemma lem1604811 (_25293 : real) (h1 : term41) : (term39 _25293) = term36.
Proof. exact (EQ_MP (@lem1604419 _25293) (@lem1604418 _25293 h1)). Qed.
Lemma lem1604812 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (@lem1604811 x h1). Qed.
Lemma lem1604813 (x : real) (h1 : term41) : term258 x.
Proof. exact (fun h0 : term259 x => @lem1604812 x h1). Qed.
Lemma lem1604815 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1604816 (x : real) : (term258 x) = ((term39 x) = term36).
Proof. exact (@lem1604815 ((term39 x) = term36)). Qed.
Lemma lem1604817 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (EQ_MP (@lem1604816 x) (@lem1604813 x h1)). Qed.
Lemma lem1604819 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1604820 (x : real) : (term39 x) = (term39 x).
Proof. exact (@lem1604819 (term39 x)). Qed.
Lemma lem1604821 (x : real) : term260 x.
Proof. exact (fun h0 : term261 x => @lem1604820 x). Qed.
Lemma lem1604823 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1604824 (x : real) : (term260 x) = ((term39 x) = (term39 x)).
Proof. exact (@lem1604823 ((term39 x) = (term39 x))). Qed.
Lemma lem1604825 (x : real) : (term39 x) = (term39 x).
Proof. exact (EQ_MP (@lem1604824 x) (@lem1604821 x)). Qed.
Lemma lem1604843 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1604844 (y : real) (x : real) (z : real) : (term262 x y z) = (term263 y x z).
Proof. exact (@lem1604843 (y = z) (term264 x z)). Qed.
Lemma lem1604854 (x : real) (y : real) : (term265 x y) = (term265 x y).
Proof. exact (eq_refl (term265 x y)). Qed.
Lemma lem1604855 (y : real) (x : real) (z : real) : (term255 x y z) = (term266 y x z).
Proof. exact (MK_COMB (@lem1604854 x y) (@lem1604844 y x z)). Qed.
Lemma lem1604859 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1604860 (y : real) (x : real) (z : real) : (term266 y x z) = (term268 y x z).
Proof. exact (@lem1604859 (y = z) (term264 x y) (term264 x z)). Qed.
Lemma lem1604882 (y : real) (x : real) (z : real) : (term255 x y z) = (term268 y x z).
Proof. exact (TRANS (@lem1604855 y x z) (@lem1604860 y x z)). Qed.
Lemma lem1604883 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1604884 (y : real) (x : real) (z : real) : (term269 x y z) = (term270 y x z).
Proof. exact (MK_COMB (@lem1604883) (@lem1604882 y x z)). Qed.
Lemma lem1604906 (y : real) (x : real) (z : real) : (term268 y x z) = (term268 y x z).
Proof. exact (eq_refl (term268 y x z)). Qed.
Lemma lem1604907 (y : real) (x : real) (z : real) : ((term255 x y z) = (term268 y x z)) = ((term268 y x z) = (term268 y x z)).
Proof. exact (MK_COMB (@lem1604884 y x z) (@lem1604906 y x z)). Qed.
Lemma lem1604909 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1604910 (x : Prop) : (x = x) = True.
Proof. exact (@lem1604909 Prop x). Qed.
Lemma lem1604911 (y : real) (x : real) (z : real) : ((term268 y x z) = (term268 y x z)) = True.
Proof. exact (@lem1604910 (term268 y x z)). Qed.
Lemma lem1604912 (y : real) (x : real) (z : real) : ((term255 x y z) = (term268 y x z)) = True.
Proof. exact (TRANS (@lem1604907 y x z) (@lem1604911 y x z)). Qed.
Lemma lem1604913 (y : real) (x : real) (z : real) : True = ((term255 x y z) = (term268 y x z)).
Proof. exact (SYM (@lem1604912 y x z)). Qed.
Lemma lem1604914 (y : real) (x : real) (z : real) : (term255 x y z) = (term268 y x z).
Proof. exact (EQ_MP (@lem1604913 y x z) (@lem0)). Qed.
Lemma lem1604915 (y : real) (x : real) (z : real) : term268 y x z.
Proof. exact (EQ_MP (@lem1604914 y x z) (@lem1604800 x y z)). Qed.
Lemma lem1604917 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1604918 (x : real) (y : real) (z : real) : (term268 y x z) = (term272 x y z).
Proof. exact (@lem1604917 (term273 y x z) (y = z)). Qed.
Lemma lem1604920 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1604921 (y : real) (x : real) (z : real) : (term276 y x z) = (term277 y x z).
Proof. exact (@lem1604920 (term264 x y) (term264 x z)). Qed.
Lemma lem1604923 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1604924 (x : real) (y : real) : (term279 x y) = (x = y).
Proof. exact (@lem1604923 (x = y)). Qed.
Lemma lem1604925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1604926 (x : real) (y : real) : (term280 x y) = (term281 x y).
Proof. exact (MK_COMB (@lem1604925) (@lem1604924 x y)). Qed.
Lemma lem1604928 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1604929 (x : real) (z : real) : (term279 x z) = (x = z).
Proof. exact (@lem1604928 (x = z)). Qed.
Lemma lem1604930 (y : real) (x : real) (z : real) : (term277 y x z) = (term282 y x z).
Proof. exact (MK_COMB (@lem1604926 x y) (@lem1604929 x z)). Qed.
Lemma lem1604931 (y : real) (x : real) (z : real) : (term276 y x z) = (term282 y x z).
Proof. exact (TRANS (@lem1604921 y x z) (@lem1604930 y x z)). Qed.
Lemma lem1604932 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1604933 (y : real) (x : real) (z : real) : (term283 y x z) = (term284 y x z).
Proof. exact (MK_COMB (@lem1604932) (@lem1604931 y x z)). Qed.
Lemma lem1604934 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1604935 (x : real) (y : real) (z : real) : (term272 x y z) = (term285 x y z).
Proof. exact (MK_COMB (@lem1604933 y x z) (@lem1604934 y z)). Qed.
Lemma lem1604936 (x : real) (y : real) (z : real) : (term268 y x z) = (term285 x y z).
Proof. exact (TRANS (@lem1604918 x y z) (@lem1604935 x y z)). Qed.
Lemma lem1604938 (x : real) (h1 : term41) : term286 x.
Proof. exact (conj (@lem1604817 x h1) (@lem1604825 x)). Qed.
Lemma lem1604940 (x : real) (y : real) (z : real) : term285 x y z.
Proof. exact (EQ_MP (@lem1604936 x y z) (@lem1604915 y x z)). Qed.
Lemma lem1604941 (x : real) : term287 x.
Proof. exact (@lem1604940 (term39 x) term36 (term39 x)). Qed.
Lemma lem1604944 (x : real) (h1 : term41) : term36 = (term39 x).
Proof. exact (@lem1604941 x (@lem1604938 x h1)). Qed.
Lemma lem1604945 (x : real) (h1 : term41) : term288 x.
Proof. exact (fun h0 : term289 x => @lem1604944 x h1). Qed.
Lemma lem1604947 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1604948 (x : real) : (term288 x) = (term36 = (term39 x)).
Proof. exact (@lem1604947 (term36 = (term39 x))). Qed.
Lemma lem1604949 (x : real) (h1 : term41) : term36 = (term39 x).
Proof. exact (EQ_MP (@lem1604948 x) (@lem1604945 x h1)). Qed.
Lemma lem1604951 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1604952 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1604951 (real_mul x y)). Qed.
Lemma lem1604953 (x : real) (y : real) : term290 x y.
Proof. exact (fun h0 : term291 x y => @lem1604952 x y). Qed.
Lemma lem1604955 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1604956 (x : real) (y : real) : (term290 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1604955 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1604957 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1604956 x y) (@lem1604953 x y)). Qed.
Lemma lem1604959 (x : real) (y : real) (h1 : term126 x y) : term55 x y.
Proof. exact (proj1 (@lem1603972 x y h1)). Qed.
Lemma lem1604960 (x : real) (y : real) (h1 : term126 x y) : term292 x y.
Proof. exact (fun h0 : term243 x y => @lem1604959 x y h1). Qed.
Lemma lem1604962 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1604963 (x : real) (y : real) : (term292 x y) = (term55 x y).
Proof. exact (@lem1604962 (term55 x y)). Qed.
Lemma lem1604964 (x : real) (y : real) (h1 : term126 x y) : term55 x y.
Proof. exact (EQ_MP (@lem1604963 x y) (@lem1604960 x y h1)). Qed.
Lemma lem1604982 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1604983 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term252 _25327 _25328 _25325 _25326) = (term293 _25327 _25328 _25325 _25326).
Proof. exact (@lem1604982 (real_le _25327 _25328) (term264 _25326 _25328) (term294 _25325 _25326)). Qed.
Lemma lem1605001 (_25325 : real) (_25327 : real) : (term265 _25325 _25327) = (term265 _25325 _25327).
Proof. exact (eq_refl (term265 _25325 _25327)). Qed.
Lemma lem1605002 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term254 _25327 _25328 _25325 _25326) = (term295 _25327 _25328 _25325 _25326).
Proof. exact (MK_COMB (@lem1605001 _25325 _25327) (@lem1604983 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605006 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605007 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term295 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326).
Proof. exact (@lem1605006 (real_le _25327 _25328) (term264 _25325 _25327) (term297 _25328 _25325 _25326)). Qed.
Lemma lem1605037 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term254 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326).
Proof. exact (TRANS (@lem1605002 _25327 _25328 _25325 _25326) (@lem1605007 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605038 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1605039 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term298 _25327 _25328 _25325 _25326) = (term299 _25327 _25328 _25325 _25326).
Proof. exact (MK_COMB (@lem1605038) (@lem1605037 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605069 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term296 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326).
Proof. exact (eq_refl (term296 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605070 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : ((term254 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326)) = ((term296 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326)).
Proof. exact (MK_COMB (@lem1605039 _25327 _25328 _25325 _25326) (@lem1605069 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605072 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1605073 (x : Prop) : (x = x) = True.
Proof. exact (@lem1605072 Prop x). Qed.
Lemma lem1605074 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : ((term296 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326)) = True.
Proof. exact (@lem1605073 (term296 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605075 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : ((term254 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326)) = True.
Proof. exact (TRANS (@lem1605070 _25327 _25328 _25325 _25326) (@lem1605074 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605076 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : True = ((term254 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326)).
Proof. exact (SYM (@lem1605075 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605077 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term254 _25327 _25328 _25325 _25326) = (term296 _25327 _25328 _25325 _25326).
Proof. exact (EQ_MP (@lem1605076 _25327 _25328 _25325 _25326) (@lem0)). Qed.
Lemma lem1605078 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : term296 _25327 _25328 _25325 _25326.
Proof. exact (EQ_MP (@lem1605077 _25327 _25328 _25325 _25326) (@lem1604748 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605080 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1605081 (_25325 : real) (_25326 : real) (_25327 : real) (_25328 : real) : (term296 _25327 _25328 _25325 _25326) = (term300 _25325 _25326 _25327 _25328).
Proof. exact (@lem1605080 (term301 _25327 _25328 _25325 _25326) (real_le _25327 _25328)). Qed.
Lemma lem1605083 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1605084 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term302 _25327 _25328 _25325 _25326) = (term303 _25327 _25328 _25325 _25326).
Proof. exact (@lem1605083 (term264 _25325 _25327) (term297 _25328 _25325 _25326)). Qed.
Lemma lem1605086 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605087 (_25325 : real) (_25327 : real) : (term279 _25325 _25327) = (_25325 = _25327).
Proof. exact (@lem1605086 (_25325 = _25327)). Qed.
Lemma lem1605088 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1605089 (_25325 : real) (_25327 : real) : (term280 _25325 _25327) = (term281 _25325 _25327).
Proof. exact (MK_COMB (@lem1605088) (@lem1605087 _25325 _25327)). Qed.
Lemma lem1605091 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1605092 (_25328 : real) (_25325 : real) (_25326 : real) : (term304 _25328 _25325 _25326) = (term305 _25328 _25325 _25326).
Proof. exact (@lem1605091 (term264 _25326 _25328) (term294 _25325 _25326)). Qed.
Lemma lem1605094 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605095 (_25326 : real) (_25328 : real) : (term279 _25326 _25328) = (_25326 = _25328).
Proof. exact (@lem1605094 (_25326 = _25328)). Qed.
Lemma lem1605096 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1605097 (_25326 : real) (_25328 : real) : (term280 _25326 _25328) = (term281 _25326 _25328).
Proof. exact (MK_COMB (@lem1605096) (@lem1605095 _25326 _25328)). Qed.
Lemma lem1605099 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605100 (_25325 : real) (_25326 : real) : (term306 _25325 _25326) = (real_le _25325 _25326).
Proof. exact (@lem1605099 (real_le _25325 _25326)). Qed.
Lemma lem1605101 (_25328 : real) (_25325 : real) (_25326 : real) : (term305 _25328 _25325 _25326) = (term307 _25328 _25325 _25326).
Proof. exact (MK_COMB (@lem1605097 _25326 _25328) (@lem1605100 _25325 _25326)). Qed.
Lemma lem1605102 (_25328 : real) (_25325 : real) (_25326 : real) : (term304 _25328 _25325 _25326) = (term307 _25328 _25325 _25326).
Proof. exact (TRANS (@lem1605092 _25328 _25325 _25326) (@lem1605101 _25328 _25325 _25326)). Qed.
Lemma lem1605103 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term303 _25327 _25328 _25325 _25326) = (term308 _25327 _25328 _25325 _25326).
Proof. exact (MK_COMB (@lem1605089 _25325 _25327) (@lem1605102 _25328 _25325 _25326)). Qed.
Lemma lem1605104 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term302 _25327 _25328 _25325 _25326) = (term308 _25327 _25328 _25325 _25326).
Proof. exact (TRANS (@lem1605084 _25327 _25328 _25325 _25326) (@lem1605103 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605105 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1605106 (_25327 : real) (_25328 : real) (_25325 : real) (_25326 : real) : (term309 _25327 _25328 _25325 _25326) = (term310 _25327 _25328 _25325 _25326).
Proof. exact (MK_COMB (@lem1605105) (@lem1605104 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605107 (_25327 : real) (_25328 : real) : (real_le _25327 _25328) = (real_le _25327 _25328).
Proof. exact (eq_refl (real_le _25327 _25328)). Qed.
Lemma lem1605108 (_25325 : real) (_25326 : real) (_25327 : real) (_25328 : real) : (term300 _25325 _25326 _25327 _25328) = (term311 _25325 _25326 _25327 _25328).
Proof. exact (MK_COMB (@lem1605106 _25327 _25328 _25325 _25326) (@lem1605107 _25327 _25328)). Qed.
Lemma lem1605109 (_25325 : real) (_25326 : real) (_25327 : real) (_25328 : real) : (term296 _25327 _25328 _25325 _25326) = (term311 _25325 _25326 _25327 _25328).
Proof. exact (TRANS (@lem1605081 _25325 _25326 _25327 _25328) (@lem1605108 _25325 _25326 _25327 _25328)). Qed.
Lemma lem1605111 (x : real) (y : real) (h1 : term126 x y) : term312 x y.
Proof. exact (conj (@lem1604957 x y) (@lem1604964 x y h1)). Qed.
Lemma lem1605112 (x : real) (y : real) (h1 : term41) (h2 : term126 x y) : term313 x y.
Proof. exact (conj (@lem1604949 x h1) (@lem1605111 x y h2)). Qed.
Lemma lem1605114 (_25325 : real) (_25326 : real) (_25327 : real) (_25328 : real) : term311 _25325 _25326 _25327 _25328.
Proof. exact (EQ_MP (@lem1605109 _25325 _25326 _25327 _25328) (@lem1605078 _25327 _25328 _25325 _25326)). Qed.
Lemma lem1605115 (x : real) (y : real) : term314 x y.
Proof. exact (@lem1605114 term36 (real_mul x y) (term39 x) (real_mul x y)). Qed.
Lemma lem1605118 (x : real) (y : real) (h1 : term41) (h2 : term126 x y) : term315 x y.
Proof. exact (@lem1605115 x y (@lem1605112 x y h1 h2)). Qed.
Lemma lem1605119 (x : real) (y : real) (h1 : term41) (h2 : term126 x y) : term316 x y.
Proof. exact (fun h0 : term317 x y => @lem1605118 x y h1 h2). Qed.
Lemma lem1605121 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605122 (x : real) (y : real) : (term316 x y) = (term315 x y).
Proof. exact (@lem1605121 (term315 x y)). Qed.
Lemma lem1605123 (x : real) (y : real) (h1 : term41) (h2 : term126 x y) : term315 x y.
Proof. exact (EQ_MP (@lem1605122 x y) (@lem1605119 x y h1 h2)). Qed.
Lemma lem1605129 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605130 (_25300 : real) (_25298 : real) (_25299 : real) : (term242 _25300 _25298 _25299) = (term318 _25300 _25298 _25299).
Proof. exact (@lem1605129 (term319 _25298 _25300 _25299) (term216 _25300) (real_le _25298 _25299)). Qed.
Lemma lem1605144 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1605145 (_25298 : real) (_25299 : real) (_25300 : real) : (term320 _25300 _25298 _25299) = (term321 _25298 _25299 _25300).
Proof. exact (@lem1605144 (real_le _25298 _25299) (term216 _25300)). Qed.
Lemma lem1605151 (_25298 : real) (_25300 : real) (_25299 : real) : (term322 _25298 _25300 _25299) = (term322 _25298 _25300 _25299).
Proof. exact (eq_refl (term322 _25298 _25300 _25299)). Qed.
Lemma lem1605152 (_25298 : real) (_25299 : real) (_25300 : real) : (term318 _25300 _25298 _25299) = (term323 _25298 _25299 _25300).
Proof. exact (MK_COMB (@lem1605151 _25298 _25300 _25299) (@lem1605145 _25298 _25299 _25300)). Qed.
Lemma lem1605156 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605157 (_25298 : real) (_25299 : real) (_25300 : real) : (term323 _25298 _25299 _25300) = (term324 _25298 _25299 _25300).
Proof. exact (@lem1605156 (real_le _25298 _25299) (term319 _25298 _25300 _25299) (term216 _25300)). Qed.
Lemma lem1605173 (_25298 : real) (_25299 : real) (_25300 : real) : (term318 _25300 _25298 _25299) = (term324 _25298 _25299 _25300).
Proof. exact (TRANS (@lem1605152 _25298 _25299 _25300) (@lem1605157 _25298 _25299 _25300)). Qed.
Lemma lem1605174 (_25298 : real) (_25299 : real) (_25300 : real) : (term242 _25300 _25298 _25299) = (term324 _25298 _25299 _25300).
Proof. exact (TRANS (@lem1605130 _25300 _25298 _25299) (@lem1605173 _25298 _25299 _25300)). Qed.
Lemma lem1605175 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1605176 (_25298 : real) (_25299 : real) (_25300 : real) : (term325 _25300 _25298 _25299) = (term326 _25298 _25299 _25300).
Proof. exact (MK_COMB (@lem1605175) (@lem1605174 _25298 _25299 _25300)). Qed.
Lemma lem1605190 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1605191 (_25298 : real) (_25299 : real) (_25300 : real) : (term327 _25298 _25300 _25299) = (term328 _25298 _25299 _25300).
Proof. exact (@lem1605190 (term319 _25298 _25300 _25299) (term216 _25300)). Qed.
Lemma lem1605197 (_25298 : real) (_25299 : real) : (term329 _25298 _25299) = (term329 _25298 _25299).
Proof. exact (eq_refl (term329 _25298 _25299)). Qed.
Lemma lem1605198 (_25298 : real) (_25299 : real) (_25300 : real) : (term330 _25298 _25300 _25299) = (term324 _25298 _25299 _25300).
Proof. exact (MK_COMB (@lem1605197 _25298 _25299) (@lem1605191 _25298 _25299 _25300)). Qed.
Lemma lem1605209 (_25298 : real) (_25299 : real) (_25300 : real) : ((term242 _25300 _25298 _25299) = (term330 _25298 _25300 _25299)) = ((term324 _25298 _25299 _25300) = (term324 _25298 _25299 _25300)).
Proof. exact (MK_COMB (@lem1605176 _25298 _25299 _25300) (@lem1605198 _25298 _25299 _25300)). Qed.
Lemma lem1605211 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1605212 (x : Prop) : (x = x) = True.
Proof. exact (@lem1605211 Prop x). Qed.
Lemma lem1605213 (_25298 : real) (_25299 : real) (_25300 : real) : ((term324 _25298 _25299 _25300) = (term324 _25298 _25299 _25300)) = True.
Proof. exact (@lem1605212 (term324 _25298 _25299 _25300)). Qed.
Lemma lem1605214 (_25298 : real) (_25300 : real) (_25299 : real) : ((term242 _25300 _25298 _25299) = (term330 _25298 _25300 _25299)) = True.
Proof. exact (TRANS (@lem1605209 _25298 _25299 _25300) (@lem1605213 _25298 _25299 _25300)). Qed.
Lemma lem1605215 (_25298 : real) (_25300 : real) (_25299 : real) : True = ((term242 _25300 _25298 _25299) = (term330 _25298 _25300 _25299)).
Proof. exact (SYM (@lem1605214 _25298 _25300 _25299)). Qed.
Lemma lem1605216 (_25298 : real) (_25300 : real) (_25299 : real) : (term242 _25300 _25298 _25299) = (term330 _25298 _25300 _25299).
Proof. exact (EQ_MP (@lem1605215 _25298 _25300 _25299) (@lem0)). Qed.
Lemma lem1605217 (_25298 : real) (_25300 : real) (_25299 : real) (h1 : term10) : term330 _25298 _25300 _25299.
Proof. exact (EQ_MP (@lem1605216 _25298 _25300 _25299) (@lem1604559 _25300 _25298 _25299 h1)). Qed.
Lemma lem1605219 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1605220 (_25300 : real) (_25298 : real) (_25299 : real) : (term330 _25298 _25300 _25299) = (term331 _25300 _25298 _25299).
Proof. exact (@lem1605219 (term327 _25298 _25300 _25299) (real_le _25298 _25299)). Qed.
Lemma lem1605222 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1605223 (_25298 : real) (_25300 : real) (_25299 : real) : (term332 _25298 _25300 _25299) = (term333 _25298 _25300 _25299).
Proof. exact (@lem1605222 (term216 _25300) (term319 _25298 _25300 _25299)). Qed.
Lemma lem1605225 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605226 (_25300 : real) : (term334 _25300) = (term61 _25300).
Proof. exact (@lem1605225 (term61 _25300)). Qed.
Lemma lem1605227 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1605228 (_25300 : real) : (term335 _25300) = (term57 _25300).
Proof. exact (MK_COMB (@lem1605227) (@lem1605226 _25300)). Qed.
Lemma lem1605230 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605231 (_25298 : real) (_25300 : real) (_25299 : real) : (term336 _25298 _25300 _25299) = (term202 _25298 _25300 _25299).
Proof. exact (@lem1605230 (term202 _25298 _25300 _25299)). Qed.
Lemma lem1605232 (_25298 : real) (_25300 : real) (_25299 : real) : (term333 _25298 _25300 _25299) = (term337 _25298 _25300 _25299).
Proof. exact (MK_COMB (@lem1605228 _25300) (@lem1605231 _25298 _25300 _25299)). Qed.
Lemma lem1605233 (_25298 : real) (_25300 : real) (_25299 : real) : (term332 _25298 _25300 _25299) = (term337 _25298 _25300 _25299).
Proof. exact (TRANS (@lem1605223 _25298 _25300 _25299) (@lem1605232 _25298 _25300 _25299)). Qed.
Lemma lem1605234 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1605235 (_25298 : real) (_25300 : real) (_25299 : real) : (term338 _25298 _25300 _25299) = (term339 _25298 _25300 _25299).
Proof. exact (MK_COMB (@lem1605234) (@lem1605233 _25298 _25300 _25299)). Qed.
Lemma lem1605236 (_25298 : real) (_25299 : real) : (real_le _25298 _25299) = (real_le _25298 _25299).
Proof. exact (eq_refl (real_le _25298 _25299)). Qed.
Lemma lem1605237 (_25300 : real) (_25298 : real) (_25299 : real) : (term331 _25300 _25298 _25299) = (term340 _25300 _25298 _25299).
Proof. exact (MK_COMB (@lem1605235 _25298 _25300 _25299) (@lem1605236 _25298 _25299)). Qed.
Lemma lem1605238 (_25300 : real) (_25298 : real) (_25299 : real) : (term330 _25298 _25300 _25299) = (term340 _25300 _25298 _25299).
Proof. exact (TRANS (@lem1605220 _25300 _25298 _25299) (@lem1605237 _25300 _25298 _25299)). Qed.
Lemma lem1605240 (x : real) (y : real) (h1 : term41) (h2 : term126 x y) (h3 : term59 x y) : term341 x y.
Proof. exact (conj (@lem1604809 x y h3) (@lem1605123 x y h1 h2)). Qed.
Lemma lem1605242 (_25300 : real) (_25298 : real) (_25299 : real) (h1 : term10) : term340 _25300 _25298 _25299.
Proof. exact (EQ_MP (@lem1605238 _25300 _25298 _25299) (@lem1605217 _25298 _25300 _25299 h1)). Qed.
Lemma lem1605243 (x : real) (y : real) (h1 : term10) : term342 x y.
Proof. exact (@lem1605242 x term36 y h1). Qed.
Lemma lem1605246 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : term56 y.
Proof. exact (@lem1605243 x y h1 (@lem1605240 x y h2 h3 h4)). Qed.
Lemma lem1605247 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : term343 y.
Proof. exact (fun h0 : term241 y => @lem1605246 x y h1 h2 h3 h4). Qed.
Lemma lem1605249 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605250 (y : real) : (term343 y) = (term56 y).
Proof. exact (@lem1605249 (term56 y)). Qed.
Lemma lem1605251 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : term56 y.
Proof. exact (EQ_MP (@lem1605250 y) (@lem1605247 x y h1 h2 h3 h4)). Qed.
Lemma lem1605254 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1605256 (y : real) : (term241 y) = (term344 y).
Proof. exact (@lem1605254 (term56 y)). Qed.
Lemma lem1605259 (x : real) (y : real) (h1 : term126 x y) : term344 y.
Proof. exact (EQ_MP (@lem1605256 y) (@lem1604539 x y h1)). Qed.
Lemma lem1605262 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : False.
Proof. exact (@lem1605259 x y h3 (@lem1605251 x y h1 h2 h3 h4)). Qed.
Lemma lem1605263 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : term345.
Proof. exact (fun h0 : ~ False => @lem1605262 x y h1 h2 h3 h4). Qed.
Lemma lem1605265 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605266 : term345 = False.
Proof. exact (@lem1605265 False). Qed.
Lemma lem1605267 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : False.
Proof. exact (EQ_MP (@lem1605266) (@lem1605263 x y h1 h2 h3 h4)). Qed.
Lemma lem1605268 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1605269 (_25341 : real) (_25343 : real) (h1 : _25341 = _25343) : _25341 = _25343.
Proof. exact (h1). Qed.
Lemma lem1605270 (_25342 : real) (_25344 : real) (h1 : _25342 = _25344) : _25342 = _25344.
Proof. exact (h1). Qed.
Lemma lem1605271 (_25341 : real) (_25343 : real) (h1 : _25341 = _25343) : (real_le _25341) = (real_le _25343).
Proof. exact (MK_COMB (@lem1605268) (@lem1605269 _25341 _25343 h1)). Qed.
Lemma lem1605272 (_25341 : real) (_25343 : real) (_25342 : real) (_25344 : real) (h1 : _25341 = _25343) (h2 : _25342 = _25344) : (real_le _25341 _25342) = (real_le _25343 _25344).
Proof. exact (MK_COMB (@lem1605271 _25341 _25343 h1) (@lem1605270 _25342 _25344 h2)). Qed.
Lemma lem1605274 (b : Prop) (a : Prop) : term247 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1605275 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : term248 _25343 _25344 _25341 _25342.
Proof. exact (@lem1605274 (real_le _25343 _25344) (real_le _25341 _25342)). Qed.
Lemma lem1605276 (_25341 : real) (_25343 : real) (_25342 : real) (_25344 : real) (h1 : _25341 = _25343) (h2 : _25342 = _25344) : term249 _25343 _25344 _25341 _25342.
Proof. exact (@lem1605275 _25343 _25344 _25341 _25342 (@lem1605272 _25341 _25343 _25342 _25344 h1 h2)). Qed.
Lemma lem1605277 (_25344 : real) (_25342 : real) (_25341 : real) (_25343 : real) (h1 : _25341 = _25343) : term250 _25343 _25344 _25341 _25342.
Proof. exact (fun h0 : _25342 = _25344 => @lem1605276 _25341 _25343 _25342 _25344 h1 h0). Qed.
Lemma lem1605279 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1605280 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term250 _25343 _25344 _25341 _25342) = (term252 _25343 _25344 _25341 _25342).
Proof. exact (@lem1605279 (_25342 = _25344) (term249 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605281 (_25344 : real) (_25342 : real) (_25341 : real) (_25343 : real) (h1 : _25341 = _25343) : term252 _25343 _25344 _25341 _25342.
Proof. exact (EQ_MP (@lem1605280 _25343 _25344 _25341 _25342) (@lem1605277 _25344 _25342 _25341 _25343 h1)). Qed.
Lemma lem1605282 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : term253 _25343 _25344 _25341 _25342.
Proof. exact (fun h0 : _25341 = _25343 => @lem1605281 _25344 _25342 _25341 _25343 h0). Qed.
Lemma lem1605284 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1605285 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term253 _25343 _25344 _25341 _25342) = (term254 _25343 _25344 _25341 _25342).
Proof. exact (@lem1605284 (_25341 = _25343) (term252 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605286 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : term254 _25343 _25344 _25341 _25342.
Proof. exact (EQ_MP (@lem1605285 _25343 _25344 _25341 _25342) (@lem1605282 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605342 (_25301 : real) (h1 : term41) : (term39 _25301) = term36.
Proof. exact (EQ_MP (@lem1604443 _25301) (@lem1604442 _25301 h1)). Qed.
Lemma lem1605343 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (@lem1605342 x h1). Qed.
Lemma lem1605344 (x : real) (h1 : term41) : term258 x.
Proof. exact (fun h0 : term259 x => @lem1605343 x h1). Qed.
Lemma lem1605346 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605347 (x : real) : (term258 x) = ((term39 x) = term36).
Proof. exact (@lem1605346 ((term39 x) = term36)). Qed.
Lemma lem1605348 (x : real) (h1 : term41) : (term39 x) = term36.
Proof. exact (EQ_MP (@lem1605347 x) (@lem1605344 x h1)). Qed.
Lemma lem1605350 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1605351 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1605350 (real_mul x y)). Qed.
Lemma lem1605352 (x : real) (y : real) : term290 x y.
Proof. exact (fun h0 : term291 x y => @lem1605351 x y). Qed.
Lemma lem1605354 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605355 (x : real) (y : real) : (term290 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1605354 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1605356 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1605355 x y) (@lem1605352 x y)). Qed.
Lemma lem1605358 (x : real) (y : real) (h1 : term59 x y) : term61 x.
Proof. exact (proj1 (@lem1603968 x y h1)). Qed.
Lemma lem1605359 (x : real) (y : real) (h1 : term59 x y) : term256 x.
Proof. exact (fun h0 : term216 x => @lem1605358 x y h1). Qed.
Lemma lem1605361 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605362 (x : real) : (term256 x) = (term61 x).
Proof. exact (@lem1605361 (term61 x)). Qed.
Lemma lem1605363 (x : real) (y : real) (h1 : term59 x y) : term61 x.
Proof. exact (EQ_MP (@lem1605362 x) (@lem1605359 x y h1)). Qed.
Lemma lem1605365 (x : real) (y : real) (h1 : term130 x y) : term56 y.
Proof. exact (proj2 (@lem1603973 x y h1)). Qed.
Lemma lem1605366 (x : real) (y : real) (h1 : term130 x y) : term343 y.
Proof. exact (fun h0 : term241 y => @lem1605365 x y h1). Qed.
Lemma lem1605368 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605369 (y : real) : (term343 y) = (term56 y).
Proof. exact (@lem1605368 (term56 y)). Qed.
Lemma lem1605370 (x : real) (y : real) (h1 : term130 x y) : term56 y.
Proof. exact (EQ_MP (@lem1605369 y) (@lem1605366 x y h1)). Qed.
Lemma lem1605376 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605377 (_25308 : real) (_25306 : real) (_25307 : real) : (term244 _25308 _25306 _25307) = (term346 _25308 _25306 _25307).
Proof. exact (@lem1605376 (term202 _25306 _25308 _25307) (term216 _25308) (term294 _25306 _25307)). Qed.
Lemma lem1605391 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1605392 (_25306 : real) (_25307 : real) (_25308 : real) : (term347 _25308 _25306 _25307) = (term348 _25306 _25307 _25308).
Proof. exact (@lem1605391 (term294 _25306 _25307) (term216 _25308)). Qed.
Lemma lem1605398 (_25306 : real) (_25308 : real) (_25307 : real) : (term349 _25306 _25308 _25307) = (term349 _25306 _25308 _25307).
Proof. exact (eq_refl (term349 _25306 _25308 _25307)). Qed.
Lemma lem1605399 (_25306 : real) (_25307 : real) (_25308 : real) : (term346 _25308 _25306 _25307) = (term350 _25306 _25307 _25308).
Proof. exact (MK_COMB (@lem1605398 _25306 _25308 _25307) (@lem1605392 _25306 _25307 _25308)). Qed.
Lemma lem1605410 (_25306 : real) (_25307 : real) (_25308 : real) : (term244 _25308 _25306 _25307) = (term350 _25306 _25307 _25308).
Proof. exact (TRANS (@lem1605377 _25308 _25306 _25307) (@lem1605399 _25306 _25307 _25308)). Qed.
Lemma lem1605411 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1605412 (_25306 : real) (_25307 : real) (_25308 : real) : (term351 _25308 _25306 _25307) = (term352 _25306 _25307 _25308).
Proof. exact (MK_COMB (@lem1605411) (@lem1605410 _25306 _25307 _25308)). Qed.
Lemma lem1605426 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1605427 (_25306 : real) (_25307 : real) (_25308 : real) : (term347 _25308 _25306 _25307) = (term348 _25306 _25307 _25308).
Proof. exact (@lem1605426 (term294 _25306 _25307) (term216 _25308)). Qed.
Lemma lem1605433 (_25306 : real) (_25308 : real) (_25307 : real) : (term349 _25306 _25308 _25307) = (term349 _25306 _25308 _25307).
Proof. exact (eq_refl (term349 _25306 _25308 _25307)). Qed.
Lemma lem1605434 (_25306 : real) (_25307 : real) (_25308 : real) : (term346 _25308 _25306 _25307) = (term350 _25306 _25307 _25308).
Proof. exact (MK_COMB (@lem1605433 _25306 _25308 _25307) (@lem1605427 _25306 _25307 _25308)). Qed.
Lemma lem1605445 (_25306 : real) (_25307 : real) (_25308 : real) : ((term244 _25308 _25306 _25307) = (term346 _25308 _25306 _25307)) = ((term350 _25306 _25307 _25308) = (term350 _25306 _25307 _25308)).
Proof. exact (MK_COMB (@lem1605412 _25306 _25307 _25308) (@lem1605434 _25306 _25307 _25308)). Qed.
Lemma lem1605447 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1605448 (x : Prop) : (x = x) = True.
Proof. exact (@lem1605447 Prop x). Qed.
Lemma lem1605449 (_25306 : real) (_25307 : real) (_25308 : real) : ((term350 _25306 _25307 _25308) = (term350 _25306 _25307 _25308)) = True.
Proof. exact (@lem1605448 (term350 _25306 _25307 _25308)). Qed.
Lemma lem1605450 (_25308 : real) (_25306 : real) (_25307 : real) : ((term244 _25308 _25306 _25307) = (term346 _25308 _25306 _25307)) = True.
Proof. exact (TRANS (@lem1605445 _25306 _25307 _25308) (@lem1605449 _25306 _25307 _25308)). Qed.
Lemma lem1605451 (_25308 : real) (_25306 : real) (_25307 : real) : True = ((term244 _25308 _25306 _25307) = (term346 _25308 _25306 _25307)).
Proof. exact (SYM (@lem1605450 _25308 _25306 _25307)). Qed.
Lemma lem1605452 (_25308 : real) (_25306 : real) (_25307 : real) : (term244 _25308 _25306 _25307) = (term346 _25308 _25306 _25307).
Proof. exact (EQ_MP (@lem1605451 _25308 _25306 _25307) (@lem0)). Qed.
Lemma lem1605453 (_25308 : real) (_25306 : real) (_25307 : real) (h1 : term10) : term346 _25308 _25306 _25307.
Proof. exact (EQ_MP (@lem1605452 _25308 _25306 _25307) (@lem1604599 _25308 _25306 _25307 h1)). Qed.
Lemma lem1605455 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1605456 (_25306 : real) (_25308 : real) (_25307 : real) : (term346 _25308 _25306 _25307) = (term353 _25306 _25308 _25307).
Proof. exact (@lem1605455 (term347 _25308 _25306 _25307) (term202 _25306 _25308 _25307)). Qed.
Lemma lem1605458 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1605459 (_25308 : real) (_25306 : real) (_25307 : real) : (term354 _25308 _25306 _25307) = (term355 _25308 _25306 _25307).
Proof. exact (@lem1605458 (term216 _25308) (term294 _25306 _25307)). Qed.
Lemma lem1605461 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605462 (_25308 : real) : (term334 _25308) = (term61 _25308).
Proof. exact (@lem1605461 (term61 _25308)). Qed.
Lemma lem1605463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1605464 (_25308 : real) : (term335 _25308) = (term57 _25308).
Proof. exact (MK_COMB (@lem1605463) (@lem1605462 _25308)). Qed.
Lemma lem1605466 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605467 (_25306 : real) (_25307 : real) : (term306 _25306 _25307) = (real_le _25306 _25307).
Proof. exact (@lem1605466 (real_le _25306 _25307)). Qed.
Lemma lem1605468 (_25308 : real) (_25306 : real) (_25307 : real) : (term355 _25308 _25306 _25307) = (term356 _25308 _25306 _25307).
Proof. exact (MK_COMB (@lem1605464 _25308) (@lem1605467 _25306 _25307)). Qed.
Lemma lem1605469 (_25308 : real) (_25306 : real) (_25307 : real) : (term354 _25308 _25306 _25307) = (term356 _25308 _25306 _25307).
Proof. exact (TRANS (@lem1605459 _25308 _25306 _25307) (@lem1605468 _25308 _25306 _25307)). Qed.
Lemma lem1605470 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1605471 (_25308 : real) (_25306 : real) (_25307 : real) : (term357 _25308 _25306 _25307) = (term358 _25308 _25306 _25307).
Proof. exact (MK_COMB (@lem1605470) (@lem1605469 _25308 _25306 _25307)). Qed.
Lemma lem1605472 (_25306 : real) (_25308 : real) (_25307 : real) : (term202 _25306 _25308 _25307) = (term202 _25306 _25308 _25307).
Proof. exact (eq_refl (term202 _25306 _25308 _25307)). Qed.
Lemma lem1605473 (_25306 : real) (_25308 : real) (_25307 : real) : (term353 _25306 _25308 _25307) = (term359 _25306 _25308 _25307).
Proof. exact (MK_COMB (@lem1605471 _25308 _25306 _25307) (@lem1605472 _25306 _25308 _25307)). Qed.
Lemma lem1605474 (_25306 : real) (_25308 : real) (_25307 : real) : (term346 _25308 _25306 _25307) = (term359 _25306 _25308 _25307).
Proof. exact (TRANS (@lem1605456 _25306 _25308 _25307) (@lem1605473 _25306 _25308 _25307)). Qed.
Lemma lem1605476 (x : real) (y : real) (h1 : term130 x y) (h2 : term59 x y) : term360 x y.
Proof. exact (conj (@lem1605363 x y h2) (@lem1605370 x y h1)). Qed.
Lemma lem1605478 (_25306 : real) (_25308 : real) (_25307 : real) (h1 : term10) : term359 _25306 _25308 _25307.
Proof. exact (EQ_MP (@lem1605474 _25306 _25308 _25307) (@lem1605453 _25308 _25306 _25307 h1)). Qed.
Lemma lem1605479 (x : real) (y : real) (h1 : term10) : term361 x y.
Proof. exact (@lem1605478 term36 x y h1). Qed.
Lemma lem1605482 (x : real) (y : real) (h1 : term10) (h2 : term130 x y) (h3 : term59 x y) : term315 x y.
Proof. exact (@lem1605479 x y h1 (@lem1605476 x y h2 h3)). Qed.
Lemma lem1605483 (x : real) (y : real) (h1 : term10) (h2 : term130 x y) (h3 : term59 x y) : term316 x y.
Proof. exact (fun h0 : term317 x y => @lem1605482 x y h1 h2 h3). Qed.
Lemma lem1605485 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605486 (x : real) (y : real) : (term316 x y) = (term315 x y).
Proof. exact (@lem1605485 (term315 x y)). Qed.
Lemma lem1605487 (x : real) (y : real) (h1 : term10) (h2 : term130 x y) (h3 : term59 x y) : term315 x y.
Proof. exact (EQ_MP (@lem1605486 x y) (@lem1605483 x y h1 h2 h3)). Qed.
Lemma lem1605505 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605506 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term252 _25343 _25344 _25341 _25342) = (term293 _25343 _25344 _25341 _25342).
Proof. exact (@lem1605505 (real_le _25343 _25344) (term264 _25342 _25344) (term294 _25341 _25342)). Qed.
Lemma lem1605524 (_25341 : real) (_25343 : real) : (term265 _25341 _25343) = (term265 _25341 _25343).
Proof. exact (eq_refl (term265 _25341 _25343)). Qed.
Lemma lem1605525 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term254 _25343 _25344 _25341 _25342) = (term295 _25343 _25344 _25341 _25342).
Proof. exact (MK_COMB (@lem1605524 _25341 _25343) (@lem1605506 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605529 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605530 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term295 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342).
Proof. exact (@lem1605529 (real_le _25343 _25344) (term264 _25341 _25343) (term297 _25344 _25341 _25342)). Qed.
Lemma lem1605560 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term254 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342).
Proof. exact (TRANS (@lem1605525 _25343 _25344 _25341 _25342) (@lem1605530 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605561 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1605562 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term298 _25343 _25344 _25341 _25342) = (term299 _25343 _25344 _25341 _25342).
Proof. exact (MK_COMB (@lem1605561) (@lem1605560 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605592 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term296 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342).
Proof. exact (eq_refl (term296 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605593 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : ((term254 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342)) = ((term296 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342)).
Proof. exact (MK_COMB (@lem1605562 _25343 _25344 _25341 _25342) (@lem1605592 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605595 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1605596 (x : Prop) : (x = x) = True.
Proof. exact (@lem1605595 Prop x). Qed.
Lemma lem1605597 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : ((term296 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342)) = True.
Proof. exact (@lem1605596 (term296 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605598 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : ((term254 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342)) = True.
Proof. exact (TRANS (@lem1605593 _25343 _25344 _25341 _25342) (@lem1605597 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605599 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : True = ((term254 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342)).
Proof. exact (SYM (@lem1605598 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605600 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term254 _25343 _25344 _25341 _25342) = (term296 _25343 _25344 _25341 _25342).
Proof. exact (EQ_MP (@lem1605599 _25343 _25344 _25341 _25342) (@lem0)). Qed.
Lemma lem1605601 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : term296 _25343 _25344 _25341 _25342.
Proof. exact (EQ_MP (@lem1605600 _25343 _25344 _25341 _25342) (@lem1605286 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605603 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1605604 (_25341 : real) (_25342 : real) (_25343 : real) (_25344 : real) : (term296 _25343 _25344 _25341 _25342) = (term300 _25341 _25342 _25343 _25344).
Proof. exact (@lem1605603 (term301 _25343 _25344 _25341 _25342) (real_le _25343 _25344)). Qed.
Lemma lem1605606 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1605607 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term302 _25343 _25344 _25341 _25342) = (term303 _25343 _25344 _25341 _25342).
Proof. exact (@lem1605606 (term264 _25341 _25343) (term297 _25344 _25341 _25342)). Qed.
Lemma lem1605609 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605610 (_25341 : real) (_25343 : real) : (term279 _25341 _25343) = (_25341 = _25343).
Proof. exact (@lem1605609 (_25341 = _25343)). Qed.
Lemma lem1605611 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1605612 (_25341 : real) (_25343 : real) : (term280 _25341 _25343) = (term281 _25341 _25343).
Proof. exact (MK_COMB (@lem1605611) (@lem1605610 _25341 _25343)). Qed.
Lemma lem1605614 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1605615 (_25344 : real) (_25341 : real) (_25342 : real) : (term304 _25344 _25341 _25342) = (term305 _25344 _25341 _25342).
Proof. exact (@lem1605614 (term264 _25342 _25344) (term294 _25341 _25342)). Qed.
Lemma lem1605617 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605618 (_25342 : real) (_25344 : real) : (term279 _25342 _25344) = (_25342 = _25344).
Proof. exact (@lem1605617 (_25342 = _25344)). Qed.
Lemma lem1605619 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1605620 (_25342 : real) (_25344 : real) : (term280 _25342 _25344) = (term281 _25342 _25344).
Proof. exact (MK_COMB (@lem1605619) (@lem1605618 _25342 _25344)). Qed.
Lemma lem1605622 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605623 (_25341 : real) (_25342 : real) : (term306 _25341 _25342) = (real_le _25341 _25342).
Proof. exact (@lem1605622 (real_le _25341 _25342)). Qed.
Lemma lem1605624 (_25344 : real) (_25341 : real) (_25342 : real) : (term305 _25344 _25341 _25342) = (term307 _25344 _25341 _25342).
Proof. exact (MK_COMB (@lem1605620 _25342 _25344) (@lem1605623 _25341 _25342)). Qed.
Lemma lem1605625 (_25344 : real) (_25341 : real) (_25342 : real) : (term304 _25344 _25341 _25342) = (term307 _25344 _25341 _25342).
Proof. exact (TRANS (@lem1605615 _25344 _25341 _25342) (@lem1605624 _25344 _25341 _25342)). Qed.
Lemma lem1605626 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term303 _25343 _25344 _25341 _25342) = (term308 _25343 _25344 _25341 _25342).
Proof. exact (MK_COMB (@lem1605612 _25341 _25343) (@lem1605625 _25344 _25341 _25342)). Qed.
Lemma lem1605627 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term302 _25343 _25344 _25341 _25342) = (term308 _25343 _25344 _25341 _25342).
Proof. exact (TRANS (@lem1605607 _25343 _25344 _25341 _25342) (@lem1605626 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605628 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1605629 (_25343 : real) (_25344 : real) (_25341 : real) (_25342 : real) : (term309 _25343 _25344 _25341 _25342) = (term310 _25343 _25344 _25341 _25342).
Proof. exact (MK_COMB (@lem1605628) (@lem1605627 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605630 (_25343 : real) (_25344 : real) : (real_le _25343 _25344) = (real_le _25343 _25344).
Proof. exact (eq_refl (real_le _25343 _25344)). Qed.
Lemma lem1605631 (_25341 : real) (_25342 : real) (_25343 : real) (_25344 : real) : (term300 _25341 _25342 _25343 _25344) = (term311 _25341 _25342 _25343 _25344).
Proof. exact (MK_COMB (@lem1605629 _25343 _25344 _25341 _25342) (@lem1605630 _25343 _25344)). Qed.
Lemma lem1605632 (_25341 : real) (_25342 : real) (_25343 : real) (_25344 : real) : (term296 _25343 _25344 _25341 _25342) = (term311 _25341 _25342 _25343 _25344).
Proof. exact (TRANS (@lem1605604 _25341 _25342 _25343 _25344) (@lem1605631 _25341 _25342 _25343 _25344)). Qed.
Lemma lem1605634 (x : real) (y : real) (h1 : term10) (h2 : term130 x y) (h3 : term59 x y) : term362 x y.
Proof. exact (conj (@lem1605356 x y) (@lem1605487 x y h1 h2 h3)). Qed.
Lemma lem1605635 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : term363 x y.
Proof. exact (conj (@lem1605348 x h2) (@lem1605634 x y h1 h3 h4)). Qed.
Lemma lem1605637 (_25341 : real) (_25342 : real) (_25343 : real) (_25344 : real) : term311 _25341 _25342 _25343 _25344.
Proof. exact (EQ_MP (@lem1605632 _25341 _25342 _25343 _25344) (@lem1605601 _25343 _25344 _25341 _25342)). Qed.
Lemma lem1605638 (x : real) (y : real) : term364 x y.
Proof. exact (@lem1605637 (term39 x) (real_mul x y) term36 (real_mul x y)). Qed.
Lemma lem1605641 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : term55 x y.
Proof. exact (@lem1605638 x y (@lem1605635 x y h1 h2 h3 h4)). Qed.
Lemma lem1605642 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : term292 x y.
Proof. exact (fun h0 : term243 x y => @lem1605641 x y h1 h2 h3 h4). Qed.
Lemma lem1605644 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605645 (x : real) (y : real) : (term292 x y) = (term55 x y).
Proof. exact (@lem1605644 (term55 x y)). Qed.
Lemma lem1605646 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : term55 x y.
Proof. exact (EQ_MP (@lem1605645 x y) (@lem1605642 x y h1 h2 h3 h4)). Qed.
Lemma lem1605649 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1605651 (x : real) (y : real) : (term243 x y) = (term365 x y).
Proof. exact (@lem1605649 (term55 x y)). Qed.
Lemma lem1605654 (x : real) (y : real) (h1 : term130 x y) : term365 x y.
Proof. exact (EQ_MP (@lem1605651 x y) (@lem1604587 x y h1)). Qed.
Lemma lem1605657 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : False.
Proof. exact (@lem1605654 x y h3 (@lem1605646 x y h1 h2 h3 h4)). Qed.
Lemma lem1605658 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : term345.
Proof. exact (fun h0 : ~ False => @lem1605657 x y h1 h2 h3 h4). Qed.
Lemma lem1605660 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605661 : term345 = False.
Proof. exact (@lem1605660 False). Qed.
Lemma lem1605662 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : False.
Proof. exact (EQ_MP (@lem1605661) (@lem1605658 x y h1 h2 h3 h4)). Qed.
Lemma lem1605663 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1605664 (_25357 : real) (_25359 : real) (h1 : _25357 = _25359) : _25357 = _25359.
Proof. exact (h1). Qed.
Lemma lem1605665 (_25358 : real) (_25360 : real) (h1 : _25358 = _25360) : _25358 = _25360.
Proof. exact (h1). Qed.
Lemma lem1605666 (_25357 : real) (_25359 : real) (h1 : _25357 = _25359) : (real_le _25357) = (real_le _25359).
Proof. exact (MK_COMB (@lem1605663) (@lem1605664 _25357 _25359 h1)). Qed.
Lemma lem1605667 (_25357 : real) (_25359 : real) (_25358 : real) (_25360 : real) (h1 : _25357 = _25359) (h2 : _25358 = _25360) : (real_le _25357 _25358) = (real_le _25359 _25360).
Proof. exact (MK_COMB (@lem1605666 _25357 _25359 h1) (@lem1605665 _25358 _25360 h2)). Qed.
Lemma lem1605669 (b : Prop) (a : Prop) : term247 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1605670 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : term248 _25359 _25360 _25357 _25358.
Proof. exact (@lem1605669 (real_le _25359 _25360) (real_le _25357 _25358)). Qed.
Lemma lem1605671 (_25357 : real) (_25359 : real) (_25358 : real) (_25360 : real) (h1 : _25357 = _25359) (h2 : _25358 = _25360) : term249 _25359 _25360 _25357 _25358.
Proof. exact (@lem1605670 _25359 _25360 _25357 _25358 (@lem1605667 _25357 _25359 _25358 _25360 h1 h2)). Qed.
Lemma lem1605672 (_25360 : real) (_25358 : real) (_25357 : real) (_25359 : real) (h1 : _25357 = _25359) : term250 _25359 _25360 _25357 _25358.
Proof. exact (fun h0 : _25358 = _25360 => @lem1605671 _25357 _25359 _25358 _25360 h1 h0). Qed.
Lemma lem1605674 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1605675 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term250 _25359 _25360 _25357 _25358) = (term252 _25359 _25360 _25357 _25358).
Proof. exact (@lem1605674 (_25358 = _25360) (term249 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1605676 (_25360 : real) (_25358 : real) (_25357 : real) (_25359 : real) (h1 : _25357 = _25359) : term252 _25359 _25360 _25357 _25358.
Proof. exact (EQ_MP (@lem1605675 _25359 _25360 _25357 _25358) (@lem1605672 _25360 _25358 _25357 _25359 h1)). Qed.
Lemma lem1605677 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : term253 _25359 _25360 _25357 _25358.
Proof. exact (fun h0 : _25357 = _25359 => @lem1605676 _25360 _25358 _25357 _25359 h0). Qed.
Lemma lem1605679 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1605680 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term253 _25359 _25360 _25357 _25358) = (term254 _25359 _25360 _25357 _25358).
Proof. exact (@lem1605679 (_25357 = _25359) (term252 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1605681 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : term254 _25359 _25360 _25357 _25358.
Proof. exact (EQ_MP (@lem1605680 _25359 _25360 _25357 _25358) (@lem1605677 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1605733 (x : real) (y : real) (z : real) : term255 x y z.
Proof. exact (@lem21385 real x y z). Qed.
Lemma lem1605737 (y : real) (x : real) (h1 : term81 y x) : term61 y.
Proof. exact (proj1 (@lem1603969 y x h1)). Qed.
Lemma lem1605738 (y : real) (x : real) (h1 : term81 y x) : term256 y.
Proof. exact (fun h0 : term216 y => @lem1605737 y x h1). Qed.
Lemma lem1605740 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605741 (y : real) : (term256 y) = (term61 y).
Proof. exact (@lem1605740 (term61 y)). Qed.
Lemma lem1605742 (y : real) (x : real) (h1 : term81 y x) : term61 y.
Proof. exact (EQ_MP (@lem1605741 y) (@lem1605738 y x h1)). Qed.
Lemma lem1605744 (_25310 : real) (h1 : term38) : (term35 _25310) = term36.
Proof. exact (EQ_MP (@lem1604470 _25310) (@lem1604469 _25310 h1)). Qed.
Lemma lem1605745 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (@lem1605744 y h1). Qed.
Lemma lem1605746 (y : real) (h1 : term38) : term366 y.
Proof. exact (fun h0 : term367 y => @lem1605745 y h1). Qed.
Lemma lem1605748 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605749 (y : real) : (term366 y) = ((term35 y) = term36).
Proof. exact (@lem1605748 ((term35 y) = term36)). Qed.
Lemma lem1605750 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (EQ_MP (@lem1605749 y) (@lem1605746 y h1)). Qed.
Lemma lem1605752 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1605753 (y : real) : (term35 y) = (term35 y).
Proof. exact (@lem1605752 (term35 y)). Qed.
Lemma lem1605754 (y : real) : term368 y.
Proof. exact (fun h0 : term369 y => @lem1605753 y). Qed.
Lemma lem1605756 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605757 (y : real) : (term368 y) = ((term35 y) = (term35 y)).
Proof. exact (@lem1605756 ((term35 y) = (term35 y))). Qed.
Lemma lem1605758 (y : real) : (term35 y) = (term35 y).
Proof. exact (EQ_MP (@lem1605757 y) (@lem1605754 y)). Qed.
Lemma lem1605776 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1605777 (y : real) (x : real) (z : real) : (term262 x y z) = (term263 y x z).
Proof. exact (@lem1605776 (y = z) (term264 x z)). Qed.
Lemma lem1605787 (x : real) (y : real) : (term265 x y) = (term265 x y).
Proof. exact (eq_refl (term265 x y)). Qed.
Lemma lem1605788 (y : real) (x : real) (z : real) : (term255 x y z) = (term266 y x z).
Proof. exact (MK_COMB (@lem1605787 x y) (@lem1605777 y x z)). Qed.
Lemma lem1605792 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605793 (y : real) (x : real) (z : real) : (term266 y x z) = (term268 y x z).
Proof. exact (@lem1605792 (y = z) (term264 x y) (term264 x z)). Qed.
Lemma lem1605815 (y : real) (x : real) (z : real) : (term255 x y z) = (term268 y x z).
Proof. exact (TRANS (@lem1605788 y x z) (@lem1605793 y x z)). Qed.
Lemma lem1605816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1605817 (y : real) (x : real) (z : real) : (term269 x y z) = (term270 y x z).
Proof. exact (MK_COMB (@lem1605816) (@lem1605815 y x z)). Qed.
Lemma lem1605839 (y : real) (x : real) (z : real) : (term268 y x z) = (term268 y x z).
Proof. exact (eq_refl (term268 y x z)). Qed.
Lemma lem1605840 (y : real) (x : real) (z : real) : ((term255 x y z) = (term268 y x z)) = ((term268 y x z) = (term268 y x z)).
Proof. exact (MK_COMB (@lem1605817 y x z) (@lem1605839 y x z)). Qed.
Lemma lem1605842 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1605843 (x : Prop) : (x = x) = True.
Proof. exact (@lem1605842 Prop x). Qed.
Lemma lem1605844 (y : real) (x : real) (z : real) : ((term268 y x z) = (term268 y x z)) = True.
Proof. exact (@lem1605843 (term268 y x z)). Qed.
Lemma lem1605845 (y : real) (x : real) (z : real) : ((term255 x y z) = (term268 y x z)) = True.
Proof. exact (TRANS (@lem1605840 y x z) (@lem1605844 y x z)). Qed.
Lemma lem1605846 (y : real) (x : real) (z : real) : True = ((term255 x y z) = (term268 y x z)).
Proof. exact (SYM (@lem1605845 y x z)). Qed.
Lemma lem1605847 (y : real) (x : real) (z : real) : (term255 x y z) = (term268 y x z).
Proof. exact (EQ_MP (@lem1605846 y x z) (@lem0)). Qed.
Lemma lem1605848 (y : real) (x : real) (z : real) : term268 y x z.
Proof. exact (EQ_MP (@lem1605847 y x z) (@lem1605733 x y z)). Qed.
Lemma lem1605850 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1605851 (x : real) (y : real) (z : real) : (term268 y x z) = (term272 x y z).
Proof. exact (@lem1605850 (term273 y x z) (y = z)). Qed.
Lemma lem1605853 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1605854 (y : real) (x : real) (z : real) : (term276 y x z) = (term277 y x z).
Proof. exact (@lem1605853 (term264 x y) (term264 x z)). Qed.
Lemma lem1605856 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605857 (x : real) (y : real) : (term279 x y) = (x = y).
Proof. exact (@lem1605856 (x = y)). Qed.
Lemma lem1605858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1605859 (x : real) (y : real) : (term280 x y) = (term281 x y).
Proof. exact (MK_COMB (@lem1605858) (@lem1605857 x y)). Qed.
Lemma lem1605861 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1605862 (x : real) (z : real) : (term279 x z) = (x = z).
Proof. exact (@lem1605861 (x = z)). Qed.
Lemma lem1605863 (y : real) (x : real) (z : real) : (term277 y x z) = (term282 y x z).
Proof. exact (MK_COMB (@lem1605859 x y) (@lem1605862 x z)). Qed.
Lemma lem1605864 (y : real) (x : real) (z : real) : (term276 y x z) = (term282 y x z).
Proof. exact (TRANS (@lem1605854 y x z) (@lem1605863 y x z)). Qed.
Lemma lem1605865 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1605866 (y : real) (x : real) (z : real) : (term283 y x z) = (term284 y x z).
Proof. exact (MK_COMB (@lem1605865) (@lem1605864 y x z)). Qed.
Lemma lem1605867 (y : real) (z : real) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem1605868 (x : real) (y : real) (z : real) : (term272 x y z) = (term285 x y z).
Proof. exact (MK_COMB (@lem1605866 y x z) (@lem1605867 y z)). Qed.
Lemma lem1605869 (x : real) (y : real) (z : real) : (term268 y x z) = (term285 x y z).
Proof. exact (TRANS (@lem1605851 x y z) (@lem1605868 x y z)). Qed.
Lemma lem1605871 (y : real) (h1 : term38) : term370 y.
Proof. exact (conj (@lem1605750 y h1) (@lem1605758 y)). Qed.
Lemma lem1605873 (x : real) (y : real) (z : real) : term285 x y z.
Proof. exact (EQ_MP (@lem1605869 x y z) (@lem1605848 y x z)). Qed.
Lemma lem1605874 (y : real) : term371 y.
Proof. exact (@lem1605873 (term35 y) term36 (term35 y)). Qed.
Lemma lem1605877 (y : real) (h1 : term38) : term36 = (term35 y).
Proof. exact (@lem1605874 y (@lem1605871 y h1)). Qed.
Lemma lem1605878 (y : real) (h1 : term38) : term372 y.
Proof. exact (fun h0 : term373 y => @lem1605877 y h1). Qed.
Lemma lem1605880 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605881 (y : real) : (term372 y) = (term36 = (term35 y)).
Proof. exact (@lem1605880 (term36 = (term35 y))). Qed.
Lemma lem1605882 (y : real) (h1 : term38) : term36 = (term35 y).
Proof. exact (EQ_MP (@lem1605881 y) (@lem1605878 y h1)). Qed.
Lemma lem1605884 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1605885 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1605884 (real_mul x y)). Qed.
Lemma lem1605886 (x : real) (y : real) : term290 x y.
Proof. exact (fun h0 : term291 x y => @lem1605885 x y). Qed.
Lemma lem1605888 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605889 (x : real) (y : real) : (term290 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1605888 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1605890 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1605889 x y) (@lem1605886 x y)). Qed.
Lemma lem1605892 (y : real) (x : real) (h1 : term212 y x) : term55 x y.
Proof. exact (proj1 (@lem1603980 y x h1)). Qed.
Lemma lem1605893 (y : real) (x : real) (h1 : term212 y x) : term292 x y.
Proof. exact (fun h0 : term243 x y => @lem1605892 y x h1). Qed.
Lemma lem1605895 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1605896 (x : real) (y : real) : (term292 x y) = (term55 x y).
Proof. exact (@lem1605895 (term55 x y)). Qed.
Lemma lem1605897 (y : real) (x : real) (h1 : term212 y x) : term55 x y.
Proof. exact (EQ_MP (@lem1605896 x y) (@lem1605893 y x h1)). Qed.
Lemma lem1605915 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605916 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term252 _25359 _25360 _25357 _25358) = (term293 _25359 _25360 _25357 _25358).
Proof. exact (@lem1605915 (real_le _25359 _25360) (term264 _25358 _25360) (term294 _25357 _25358)). Qed.
Lemma lem1605934 (_25357 : real) (_25359 : real) : (term265 _25357 _25359) = (term265 _25357 _25359).
Proof. exact (eq_refl (term265 _25357 _25359)). Qed.
Lemma lem1605935 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term254 _25359 _25360 _25357 _25358) = (term295 _25359 _25360 _25357 _25358).
Proof. exact (MK_COMB (@lem1605934 _25357 _25359) (@lem1605916 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1605939 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1605940 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term295 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358).
Proof. exact (@lem1605939 (real_le _25359 _25360) (term264 _25357 _25359) (term297 _25360 _25357 _25358)). Qed.
Lemma lem1605970 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term254 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358).
Proof. exact (TRANS (@lem1605935 _25359 _25360 _25357 _25358) (@lem1605940 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1605971 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1605972 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term298 _25359 _25360 _25357 _25358) = (term299 _25359 _25360 _25357 _25358).
Proof. exact (MK_COMB (@lem1605971) (@lem1605970 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606002 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term296 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358).
Proof. exact (eq_refl (term296 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606003 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : ((term254 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358)) = ((term296 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358)).
Proof. exact (MK_COMB (@lem1605972 _25359 _25360 _25357 _25358) (@lem1606002 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606005 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1606006 (x : Prop) : (x = x) = True.
Proof. exact (@lem1606005 Prop x). Qed.
Lemma lem1606007 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : ((term296 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358)) = True.
Proof. exact (@lem1606006 (term296 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606008 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : ((term254 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358)) = True.
Proof. exact (TRANS (@lem1606003 _25359 _25360 _25357 _25358) (@lem1606007 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606009 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : True = ((term254 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358)).
Proof. exact (SYM (@lem1606008 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606010 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term254 _25359 _25360 _25357 _25358) = (term296 _25359 _25360 _25357 _25358).
Proof. exact (EQ_MP (@lem1606009 _25359 _25360 _25357 _25358) (@lem0)). Qed.
Lemma lem1606011 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : term296 _25359 _25360 _25357 _25358.
Proof. exact (EQ_MP (@lem1606010 _25359 _25360 _25357 _25358) (@lem1605681 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606013 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1606014 (_25357 : real) (_25358 : real) (_25359 : real) (_25360 : real) : (term296 _25359 _25360 _25357 _25358) = (term300 _25357 _25358 _25359 _25360).
Proof. exact (@lem1606013 (term301 _25359 _25360 _25357 _25358) (real_le _25359 _25360)). Qed.
Lemma lem1606016 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1606017 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term302 _25359 _25360 _25357 _25358) = (term303 _25359 _25360 _25357 _25358).
Proof. exact (@lem1606016 (term264 _25357 _25359) (term297 _25360 _25357 _25358)). Qed.
Lemma lem1606019 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606020 (_25357 : real) (_25359 : real) : (term279 _25357 _25359) = (_25357 = _25359).
Proof. exact (@lem1606019 (_25357 = _25359)). Qed.
Lemma lem1606021 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1606022 (_25357 : real) (_25359 : real) : (term280 _25357 _25359) = (term281 _25357 _25359).
Proof. exact (MK_COMB (@lem1606021) (@lem1606020 _25357 _25359)). Qed.
Lemma lem1606024 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1606025 (_25360 : real) (_25357 : real) (_25358 : real) : (term304 _25360 _25357 _25358) = (term305 _25360 _25357 _25358).
Proof. exact (@lem1606024 (term264 _25358 _25360) (term294 _25357 _25358)). Qed.
Lemma lem1606027 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606028 (_25358 : real) (_25360 : real) : (term279 _25358 _25360) = (_25358 = _25360).
Proof. exact (@lem1606027 (_25358 = _25360)). Qed.
Lemma lem1606029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1606030 (_25358 : real) (_25360 : real) : (term280 _25358 _25360) = (term281 _25358 _25360).
Proof. exact (MK_COMB (@lem1606029) (@lem1606028 _25358 _25360)). Qed.
Lemma lem1606032 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606033 (_25357 : real) (_25358 : real) : (term306 _25357 _25358) = (real_le _25357 _25358).
Proof. exact (@lem1606032 (real_le _25357 _25358)). Qed.
Lemma lem1606034 (_25360 : real) (_25357 : real) (_25358 : real) : (term305 _25360 _25357 _25358) = (term307 _25360 _25357 _25358).
Proof. exact (MK_COMB (@lem1606030 _25358 _25360) (@lem1606033 _25357 _25358)). Qed.
Lemma lem1606035 (_25360 : real) (_25357 : real) (_25358 : real) : (term304 _25360 _25357 _25358) = (term307 _25360 _25357 _25358).
Proof. exact (TRANS (@lem1606025 _25360 _25357 _25358) (@lem1606034 _25360 _25357 _25358)). Qed.
Lemma lem1606036 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term303 _25359 _25360 _25357 _25358) = (term308 _25359 _25360 _25357 _25358).
Proof. exact (MK_COMB (@lem1606022 _25357 _25359) (@lem1606035 _25360 _25357 _25358)). Qed.
Lemma lem1606037 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term302 _25359 _25360 _25357 _25358) = (term308 _25359 _25360 _25357 _25358).
Proof. exact (TRANS (@lem1606017 _25359 _25360 _25357 _25358) (@lem1606036 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606038 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606039 (_25359 : real) (_25360 : real) (_25357 : real) (_25358 : real) : (term309 _25359 _25360 _25357 _25358) = (term310 _25359 _25360 _25357 _25358).
Proof. exact (MK_COMB (@lem1606038) (@lem1606037 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606040 (_25359 : real) (_25360 : real) : (real_le _25359 _25360) = (real_le _25359 _25360).
Proof. exact (eq_refl (real_le _25359 _25360)). Qed.
Lemma lem1606041 (_25357 : real) (_25358 : real) (_25359 : real) (_25360 : real) : (term300 _25357 _25358 _25359 _25360) = (term311 _25357 _25358 _25359 _25360).
Proof. exact (MK_COMB (@lem1606039 _25359 _25360 _25357 _25358) (@lem1606040 _25359 _25360)). Qed.
Lemma lem1606042 (_25357 : real) (_25358 : real) (_25359 : real) (_25360 : real) : (term296 _25359 _25360 _25357 _25358) = (term311 _25357 _25358 _25359 _25360).
Proof. exact (TRANS (@lem1606014 _25357 _25358 _25359 _25360) (@lem1606041 _25357 _25358 _25359 _25360)). Qed.
Lemma lem1606044 (y : real) (x : real) (h1 : term212 y x) : term312 x y.
Proof. exact (conj (@lem1605890 x y) (@lem1605897 y x h1)). Qed.
Lemma lem1606045 (y : real) (x : real) (h1 : term38) (h2 : term212 y x) : term374 x y.
Proof. exact (conj (@lem1605882 y h1) (@lem1606044 y x h2)). Qed.
Lemma lem1606047 (_25357 : real) (_25358 : real) (_25359 : real) (_25360 : real) : term311 _25357 _25358 _25359 _25360.
Proof. exact (EQ_MP (@lem1606042 _25357 _25358 _25359 _25360) (@lem1606011 _25359 _25360 _25357 _25358)). Qed.
Lemma lem1606048 (x : real) (y : real) : term375 x y.
Proof. exact (@lem1606047 term36 (real_mul x y) (term35 y) (real_mul x y)). Qed.
Lemma lem1606051 (y : real) (x : real) (h1 : term38) (h2 : term212 y x) : term376 x y.
Proof. exact (@lem1606048 x y (@lem1606045 y x h1 h2)). Qed.
Lemma lem1606052 (y : real) (x : real) (h1 : term38) (h2 : term212 y x) : term377 x y.
Proof. exact (fun h0 : term378 x y => @lem1606051 y x h1 h2). Qed.
Lemma lem1606054 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606055 (x : real) (y : real) : (term377 x y) = (term376 x y).
Proof. exact (@lem1606054 (term376 x y)). Qed.
Lemma lem1606056 (y : real) (x : real) (h1 : term38) (h2 : term212 y x) : term376 x y.
Proof. exact (EQ_MP (@lem1606055 x y) (@lem1606052 y x h1 h2)). Qed.
Lemma lem1606062 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1606063 (_25313 : real) (_25311 : real) (_25312 : real) : (term245 _25313 _25311 _25312) = (term379 _25313 _25311 _25312).
Proof. exact (@lem1606062 (term380 _25311 _25312 _25313) (term216 _25313) (real_le _25311 _25312)). Qed.
Lemma lem1606077 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1606078 (_25311 : real) (_25312 : real) (_25313 : real) : (term320 _25313 _25311 _25312) = (term321 _25311 _25312 _25313).
Proof. exact (@lem1606077 (real_le _25311 _25312) (term216 _25313)). Qed.
Lemma lem1606084 (_25311 : real) (_25312 : real) (_25313 : real) : (term381 _25311 _25312 _25313) = (term381 _25311 _25312 _25313).
Proof. exact (eq_refl (term381 _25311 _25312 _25313)). Qed.
Lemma lem1606085 (_25311 : real) (_25312 : real) (_25313 : real) : (term379 _25313 _25311 _25312) = (term382 _25311 _25312 _25313).
Proof. exact (MK_COMB (@lem1606084 _25311 _25312 _25313) (@lem1606078 _25311 _25312 _25313)). Qed.
Lemma lem1606089 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1606090 (_25311 : real) (_25312 : real) (_25313 : real) : (term382 _25311 _25312 _25313) = (term383 _25311 _25312 _25313).
Proof. exact (@lem1606089 (real_le _25311 _25312) (term380 _25311 _25312 _25313) (term216 _25313)). Qed.
Lemma lem1606106 (_25311 : real) (_25312 : real) (_25313 : real) : (term379 _25313 _25311 _25312) = (term383 _25311 _25312 _25313).
Proof. exact (TRANS (@lem1606085 _25311 _25312 _25313) (@lem1606090 _25311 _25312 _25313)). Qed.
Lemma lem1606107 (_25311 : real) (_25312 : real) (_25313 : real) : (term245 _25313 _25311 _25312) = (term383 _25311 _25312 _25313).
Proof. exact (TRANS (@lem1606063 _25313 _25311 _25312) (@lem1606106 _25311 _25312 _25313)). Qed.
Lemma lem1606108 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1606109 (_25311 : real) (_25312 : real) (_25313 : real) : (term384 _25313 _25311 _25312) = (term385 _25311 _25312 _25313).
Proof. exact (MK_COMB (@lem1606108) (@lem1606107 _25311 _25312 _25313)). Qed.
Lemma lem1606123 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1606124 (_25311 : real) (_25312 : real) (_25313 : real) : (term386 _25311 _25312 _25313) = (term387 _25311 _25312 _25313).
Proof. exact (@lem1606123 (term380 _25311 _25312 _25313) (term216 _25313)). Qed.
Lemma lem1606130 (_25311 : real) (_25312 : real) : (term329 _25311 _25312) = (term329 _25311 _25312).
Proof. exact (eq_refl (term329 _25311 _25312)). Qed.
Lemma lem1606131 (_25311 : real) (_25312 : real) (_25313 : real) : (term388 _25311 _25312 _25313) = (term383 _25311 _25312 _25313).
Proof. exact (MK_COMB (@lem1606130 _25311 _25312) (@lem1606124 _25311 _25312 _25313)). Qed.
Lemma lem1606142 (_25311 : real) (_25312 : real) (_25313 : real) : ((term245 _25313 _25311 _25312) = (term388 _25311 _25312 _25313)) = ((term383 _25311 _25312 _25313) = (term383 _25311 _25312 _25313)).
Proof. exact (MK_COMB (@lem1606109 _25311 _25312 _25313) (@lem1606131 _25311 _25312 _25313)). Qed.
Lemma lem1606144 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1606145 (x : Prop) : (x = x) = True.
Proof. exact (@lem1606144 Prop x). Qed.
Lemma lem1606146 (_25311 : real) (_25312 : real) (_25313 : real) : ((term383 _25311 _25312 _25313) = (term383 _25311 _25312 _25313)) = True.
Proof. exact (@lem1606145 (term383 _25311 _25312 _25313)). Qed.
Lemma lem1606147 (_25311 : real) (_25312 : real) (_25313 : real) : ((term245 _25313 _25311 _25312) = (term388 _25311 _25312 _25313)) = True.
Proof. exact (TRANS (@lem1606142 _25311 _25312 _25313) (@lem1606146 _25311 _25312 _25313)). Qed.
Lemma lem1606148 (_25311 : real) (_25312 : real) (_25313 : real) : True = ((term245 _25313 _25311 _25312) = (term388 _25311 _25312 _25313)).
Proof. exact (SYM (@lem1606147 _25311 _25312 _25313)). Qed.
Lemma lem1606149 (_25311 : real) (_25312 : real) (_25313 : real) : (term245 _25313 _25311 _25312) = (term388 _25311 _25312 _25313).
Proof. exact (EQ_MP (@lem1606148 _25311 _25312 _25313) (@lem0)). Qed.
Lemma lem1606150 (_25311 : real) (_25312 : real) (_25313 : real) (h1 : term34) : term388 _25311 _25312 _25313.
Proof. exact (EQ_MP (@lem1606149 _25311 _25312 _25313) (@lem1604679 _25313 _25311 _25312 h1)). Qed.
Lemma lem1606152 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1606153 (_25313 : real) (_25311 : real) (_25312 : real) : (term388 _25311 _25312 _25313) = (term389 _25313 _25311 _25312).
Proof. exact (@lem1606152 (term386 _25311 _25312 _25313) (real_le _25311 _25312)). Qed.
Lemma lem1606155 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1606156 (_25311 : real) (_25312 : real) (_25313 : real) : (term390 _25311 _25312 _25313) = (term391 _25311 _25312 _25313).
Proof. exact (@lem1606155 (term216 _25313) (term380 _25311 _25312 _25313)). Qed.
Lemma lem1606158 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606159 (_25313 : real) : (term334 _25313) = (term61 _25313).
Proof. exact (@lem1606158 (term61 _25313)). Qed.
Lemma lem1606160 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1606161 (_25313 : real) : (term335 _25313) = (term57 _25313).
Proof. exact (MK_COMB (@lem1606160) (@lem1606159 _25313)). Qed.
Lemma lem1606163 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606164 (_25311 : real) (_25312 : real) (_25313 : real) : (term392 _25311 _25312 _25313) = (term191 _25311 _25312 _25313).
Proof. exact (@lem1606163 (term191 _25311 _25312 _25313)). Qed.
Lemma lem1606165 (_25311 : real) (_25312 : real) (_25313 : real) : (term391 _25311 _25312 _25313) = (term393 _25311 _25312 _25313).
Proof. exact (MK_COMB (@lem1606161 _25313) (@lem1606164 _25311 _25312 _25313)). Qed.
Lemma lem1606166 (_25311 : real) (_25312 : real) (_25313 : real) : (term390 _25311 _25312 _25313) = (term393 _25311 _25312 _25313).
Proof. exact (TRANS (@lem1606156 _25311 _25312 _25313) (@lem1606165 _25311 _25312 _25313)). Qed.
Lemma lem1606167 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606168 (_25311 : real) (_25312 : real) (_25313 : real) : (term394 _25311 _25312 _25313) = (term395 _25311 _25312 _25313).
Proof. exact (MK_COMB (@lem1606167) (@lem1606166 _25311 _25312 _25313)). Qed.
Lemma lem1606169 (_25311 : real) (_25312 : real) : (real_le _25311 _25312) = (real_le _25311 _25312).
Proof. exact (eq_refl (real_le _25311 _25312)). Qed.
Lemma lem1606170 (_25313 : real) (_25311 : real) (_25312 : real) : (term389 _25313 _25311 _25312) = (term396 _25313 _25311 _25312).
Proof. exact (MK_COMB (@lem1606168 _25311 _25312 _25313) (@lem1606169 _25311 _25312)). Qed.
Lemma lem1606171 (_25313 : real) (_25311 : real) (_25312 : real) : (term388 _25311 _25312 _25313) = (term396 _25313 _25311 _25312).
Proof. exact (TRANS (@lem1606153 _25313 _25311 _25312) (@lem1606170 _25313 _25311 _25312)). Qed.
Lemma lem1606173 (y : real) (x : real) (h1 : term38) (h2 : term212 y x) (h3 : term81 y x) : term397 x y.
Proof. exact (conj (@lem1605742 y x h3) (@lem1606056 y x h1 h2)). Qed.
Lemma lem1606175 (_25313 : real) (_25311 : real) (_25312 : real) (h1 : term34) : term396 _25313 _25311 _25312.
Proof. exact (EQ_MP (@lem1606171 _25313 _25311 _25312) (@lem1606150 _25311 _25312 _25313 h1)). Qed.
Lemma lem1606176 (y : real) (x : real) (h1 : term34) : term398 y x.
Proof. exact (@lem1606175 y term36 x h1). Qed.
Lemma lem1606179 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : term56 x.
Proof. exact (@lem1606176 y x h1 (@lem1606173 y x h2 h3 h4)). Qed.
Lemma lem1606180 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : term343 x.
Proof. exact (fun h0 : term241 x => @lem1606179 y x h1 h2 h3 h4). Qed.
Lemma lem1606182 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606183 (x : real) : (term343 x) = (term56 x).
Proof. exact (@lem1606182 (term56 x)). Qed.
Lemma lem1606184 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : term56 x.
Proof. exact (EQ_MP (@lem1606183 x) (@lem1606180 y x h1 h2 h3 h4)). Qed.
Lemma lem1606187 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1606189 (x : real) : (term241 x) = (term344 x).
Proof. exact (@lem1606187 (term56 x)). Qed.
Lemma lem1606192 (y : real) (x : real) (h1 : term212 y x) : term344 x.
Proof. exact (EQ_MP (@lem1606189 x) (@lem1604639 y x h1)). Qed.
Lemma lem1606195 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : False.
Proof. exact (@lem1606192 y x h3 (@lem1606184 y x h1 h2 h3 h4)). Qed.
Lemma lem1606196 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : term345.
Proof. exact (fun h0 : ~ False => @lem1606195 y x h1 h2 h3 h4). Qed.
Lemma lem1606198 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606199 : term345 = False.
Proof. exact (@lem1606198 False). Qed.
Lemma lem1606200 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : False.
Proof. exact (EQ_MP (@lem1606199) (@lem1606196 y x h1 h2 h3 h4)). Qed.
Lemma lem1606201 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1606202 (_25373 : real) (_25375 : real) (h1 : _25373 = _25375) : _25373 = _25375.
Proof. exact (h1). Qed.
Lemma lem1606203 (_25374 : real) (_25376 : real) (h1 : _25374 = _25376) : _25374 = _25376.
Proof. exact (h1). Qed.
Lemma lem1606204 (_25373 : real) (_25375 : real) (h1 : _25373 = _25375) : (real_le _25373) = (real_le _25375).
Proof. exact (MK_COMB (@lem1606201) (@lem1606202 _25373 _25375 h1)). Qed.
Lemma lem1606205 (_25373 : real) (_25375 : real) (_25374 : real) (_25376 : real) (h1 : _25373 = _25375) (h2 : _25374 = _25376) : (real_le _25373 _25374) = (real_le _25375 _25376).
Proof. exact (MK_COMB (@lem1606204 _25373 _25375 h1) (@lem1606203 _25374 _25376 h2)). Qed.
Lemma lem1606207 (b : Prop) (a : Prop) : term247 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem1606208 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : term248 _25375 _25376 _25373 _25374.
Proof. exact (@lem1606207 (real_le _25375 _25376) (real_le _25373 _25374)). Qed.
Lemma lem1606209 (_25373 : real) (_25375 : real) (_25374 : real) (_25376 : real) (h1 : _25373 = _25375) (h2 : _25374 = _25376) : term249 _25375 _25376 _25373 _25374.
Proof. exact (@lem1606208 _25375 _25376 _25373 _25374 (@lem1606205 _25373 _25375 _25374 _25376 h1 h2)). Qed.
Lemma lem1606210 (_25376 : real) (_25374 : real) (_25373 : real) (_25375 : real) (h1 : _25373 = _25375) : term250 _25375 _25376 _25373 _25374.
Proof. exact (fun h0 : _25374 = _25376 => @lem1606209 _25373 _25375 _25374 _25376 h1 h0). Qed.
Lemma lem1606212 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1606213 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term250 _25375 _25376 _25373 _25374) = (term252 _25375 _25376 _25373 _25374).
Proof. exact (@lem1606212 (_25374 = _25376) (term249 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606214 (_25376 : real) (_25374 : real) (_25373 : real) (_25375 : real) (h1 : _25373 = _25375) : term252 _25375 _25376 _25373 _25374.
Proof. exact (EQ_MP (@lem1606213 _25375 _25376 _25373 _25374) (@lem1606210 _25376 _25374 _25373 _25375 h1)). Qed.
Lemma lem1606215 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : term253 _25375 _25376 _25373 _25374.
Proof. exact (fun h0 : _25373 = _25375 => @lem1606214 _25376 _25374 _25373 _25375 h0). Qed.
Lemma lem1606217 (a : Prop) (b : Prop) : (a -> b) = (term251 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem1606218 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term253 _25375 _25376 _25373 _25374) = (term254 _25375 _25376 _25373 _25374).
Proof. exact (@lem1606217 (_25373 = _25375) (term252 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606219 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : term254 _25375 _25376 _25373 _25374.
Proof. exact (EQ_MP (@lem1606218 _25375 _25376 _25373 _25374) (@lem1606215 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606275 (_25318 : real) (h1 : term38) : (term35 _25318) = term36.
Proof. exact (EQ_MP (@lem1604494 _25318) (@lem1604493 _25318 h1)). Qed.
Lemma lem1606276 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (@lem1606275 y h1). Qed.
Lemma lem1606277 (y : real) (h1 : term38) : term366 y.
Proof. exact (fun h0 : term367 y => @lem1606276 y h1). Qed.
Lemma lem1606279 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606280 (y : real) : (term366 y) = ((term35 y) = term36).
Proof. exact (@lem1606279 ((term35 y) = term36)). Qed.
Lemma lem1606281 (y : real) (h1 : term38) : (term35 y) = term36.
Proof. exact (EQ_MP (@lem1606280 y) (@lem1606277 y h1)). Qed.
Lemma lem1606283 (x : real) : x = x.
Proof. exact (@lem21386 real x). Qed.
Lemma lem1606284 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (@lem1606283 (real_mul x y)). Qed.
Lemma lem1606285 (x : real) (y : real) : term290 x y.
Proof. exact (fun h0 : term291 x y => @lem1606284 x y). Qed.
Lemma lem1606287 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606288 (x : real) (y : real) : (term290 x y) = ((real_mul x y) = (real_mul x y)).
Proof. exact (@lem1606287 ((real_mul x y) = (real_mul x y))). Qed.
Lemma lem1606289 (x : real) (y : real) : (real_mul x y) = (real_mul x y).
Proof. exact (EQ_MP (@lem1606288 x y) (@lem1606285 x y)). Qed.
Lemma lem1606291 (y : real) (x : real) (h1 : term81 y x) : term61 y.
Proof. exact (proj1 (@lem1603969 y x h1)). Qed.
Lemma lem1606292 (y : real) (x : real) (h1 : term81 y x) : term256 y.
Proof. exact (fun h0 : term216 y => @lem1606291 y x h1). Qed.
Lemma lem1606294 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606295 (y : real) : (term256 y) = (term61 y).
Proof. exact (@lem1606294 (term61 y)). Qed.
Lemma lem1606296 (y : real) (x : real) (h1 : term81 y x) : term61 y.
Proof. exact (EQ_MP (@lem1606295 y) (@lem1606292 y x h1)). Qed.
Lemma lem1606298 (y : real) (x : real) (h1 : term213 y x) : term56 x.
Proof. exact (proj2 (@lem1603981 y x h1)). Qed.
Lemma lem1606299 (y : real) (x : real) (h1 : term213 y x) : term343 x.
Proof. exact (fun h0 : term241 x => @lem1606298 y x h1). Qed.
Lemma lem1606301 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606302 (x : real) : (term343 x) = (term56 x).
Proof. exact (@lem1606301 (term56 x)). Qed.
Lemma lem1606303 (y : real) (x : real) (h1 : term213 y x) : term56 x.
Proof. exact (EQ_MP (@lem1606302 x) (@lem1606299 y x h1)). Qed.
Lemma lem1606309 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1606310 (_25321 : real) (_25319 : real) (_25320 : real) : (term246 _25321 _25319 _25320) = (term399 _25321 _25319 _25320).
Proof. exact (@lem1606309 (term191 _25319 _25320 _25321) (term216 _25321) (term294 _25319 _25320)). Qed.
Lemma lem1606324 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1606325 (_25319 : real) (_25320 : real) (_25321 : real) : (term347 _25321 _25319 _25320) = (term348 _25319 _25320 _25321).
Proof. exact (@lem1606324 (term294 _25319 _25320) (term216 _25321)). Qed.
Lemma lem1606331 (_25319 : real) (_25320 : real) (_25321 : real) : (term400 _25319 _25320 _25321) = (term400 _25319 _25320 _25321).
Proof. exact (eq_refl (term400 _25319 _25320 _25321)). Qed.
Lemma lem1606332 (_25319 : real) (_25320 : real) (_25321 : real) : (term399 _25321 _25319 _25320) = (term401 _25319 _25320 _25321).
Proof. exact (MK_COMB (@lem1606331 _25319 _25320 _25321) (@lem1606325 _25319 _25320 _25321)). Qed.
Lemma lem1606343 (_25319 : real) (_25320 : real) (_25321 : real) : (term246 _25321 _25319 _25320) = (term401 _25319 _25320 _25321).
Proof. exact (TRANS (@lem1606310 _25321 _25319 _25320) (@lem1606332 _25319 _25320 _25321)). Qed.
Lemma lem1606344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1606345 (_25319 : real) (_25320 : real) (_25321 : real) : (term402 _25321 _25319 _25320) = (term403 _25319 _25320 _25321).
Proof. exact (MK_COMB (@lem1606344) (@lem1606343 _25319 _25320 _25321)). Qed.
Lemma lem1606359 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1606360 (_25319 : real) (_25320 : real) (_25321 : real) : (term347 _25321 _25319 _25320) = (term348 _25319 _25320 _25321).
Proof. exact (@lem1606359 (term294 _25319 _25320) (term216 _25321)). Qed.
Lemma lem1606366 (_25319 : real) (_25320 : real) (_25321 : real) : (term400 _25319 _25320 _25321) = (term400 _25319 _25320 _25321).
Proof. exact (eq_refl (term400 _25319 _25320 _25321)). Qed.
Lemma lem1606367 (_25319 : real) (_25320 : real) (_25321 : real) : (term399 _25321 _25319 _25320) = (term401 _25319 _25320 _25321).
Proof. exact (MK_COMB (@lem1606366 _25319 _25320 _25321) (@lem1606360 _25319 _25320 _25321)). Qed.
Lemma lem1606378 (_25319 : real) (_25320 : real) (_25321 : real) : ((term246 _25321 _25319 _25320) = (term399 _25321 _25319 _25320)) = ((term401 _25319 _25320 _25321) = (term401 _25319 _25320 _25321)).
Proof. exact (MK_COMB (@lem1606345 _25319 _25320 _25321) (@lem1606367 _25319 _25320 _25321)). Qed.
Lemma lem1606380 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1606381 (x : Prop) : (x = x) = True.
Proof. exact (@lem1606380 Prop x). Qed.
Lemma lem1606382 (_25319 : real) (_25320 : real) (_25321 : real) : ((term401 _25319 _25320 _25321) = (term401 _25319 _25320 _25321)) = True.
Proof. exact (@lem1606381 (term401 _25319 _25320 _25321)). Qed.
Lemma lem1606383 (_25321 : real) (_25319 : real) (_25320 : real) : ((term246 _25321 _25319 _25320) = (term399 _25321 _25319 _25320)) = True.
Proof. exact (TRANS (@lem1606378 _25319 _25320 _25321) (@lem1606382 _25319 _25320 _25321)). Qed.
Lemma lem1606384 (_25321 : real) (_25319 : real) (_25320 : real) : True = ((term246 _25321 _25319 _25320) = (term399 _25321 _25319 _25320)).
Proof. exact (SYM (@lem1606383 _25321 _25319 _25320)). Qed.
Lemma lem1606385 (_25321 : real) (_25319 : real) (_25320 : real) : (term246 _25321 _25319 _25320) = (term399 _25321 _25319 _25320).
Proof. exact (EQ_MP (@lem1606384 _25321 _25319 _25320) (@lem0)). Qed.
Lemma lem1606386 (_25321 : real) (_25319 : real) (_25320 : real) (h1 : term34) : term399 _25321 _25319 _25320.
Proof. exact (EQ_MP (@lem1606385 _25321 _25319 _25320) (@lem1604719 _25321 _25319 _25320 h1)). Qed.
Lemma lem1606388 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1606389 (_25319 : real) (_25320 : real) (_25321 : real) : (term399 _25321 _25319 _25320) = (term404 _25319 _25320 _25321).
Proof. exact (@lem1606388 (term347 _25321 _25319 _25320) (term191 _25319 _25320 _25321)). Qed.
Lemma lem1606391 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1606392 (_25321 : real) (_25319 : real) (_25320 : real) : (term354 _25321 _25319 _25320) = (term355 _25321 _25319 _25320).
Proof. exact (@lem1606391 (term216 _25321) (term294 _25319 _25320)). Qed.
Lemma lem1606394 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606395 (_25321 : real) : (term334 _25321) = (term61 _25321).
Proof. exact (@lem1606394 (term61 _25321)). Qed.
Lemma lem1606396 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1606397 (_25321 : real) : (term335 _25321) = (term57 _25321).
Proof. exact (MK_COMB (@lem1606396) (@lem1606395 _25321)). Qed.
Lemma lem1606399 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606400 (_25319 : real) (_25320 : real) : (term306 _25319 _25320) = (real_le _25319 _25320).
Proof. exact (@lem1606399 (real_le _25319 _25320)). Qed.
Lemma lem1606401 (_25321 : real) (_25319 : real) (_25320 : real) : (term355 _25321 _25319 _25320) = (term356 _25321 _25319 _25320).
Proof. exact (MK_COMB (@lem1606397 _25321) (@lem1606400 _25319 _25320)). Qed.
Lemma lem1606402 (_25321 : real) (_25319 : real) (_25320 : real) : (term354 _25321 _25319 _25320) = (term356 _25321 _25319 _25320).
Proof. exact (TRANS (@lem1606392 _25321 _25319 _25320) (@lem1606401 _25321 _25319 _25320)). Qed.
Lemma lem1606403 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606404 (_25321 : real) (_25319 : real) (_25320 : real) : (term357 _25321 _25319 _25320) = (term358 _25321 _25319 _25320).
Proof. exact (MK_COMB (@lem1606403) (@lem1606402 _25321 _25319 _25320)). Qed.
Lemma lem1606405 (_25319 : real) (_25320 : real) (_25321 : real) : (term191 _25319 _25320 _25321) = (term191 _25319 _25320 _25321).
Proof. exact (eq_refl (term191 _25319 _25320 _25321)). Qed.
Lemma lem1606406 (_25319 : real) (_25320 : real) (_25321 : real) : (term404 _25319 _25320 _25321) = (term405 _25319 _25320 _25321).
Proof. exact (MK_COMB (@lem1606404 _25321 _25319 _25320) (@lem1606405 _25319 _25320 _25321)). Qed.
Lemma lem1606407 (_25319 : real) (_25320 : real) (_25321 : real) : (term399 _25321 _25319 _25320) = (term405 _25319 _25320 _25321).
Proof. exact (TRANS (@lem1606389 _25319 _25320 _25321) (@lem1606406 _25319 _25320 _25321)). Qed.
Lemma lem1606409 (y : real) (x : real) (h1 : term213 y x) (h2 : term81 y x) : term360 y x.
Proof. exact (conj (@lem1606296 y x h2) (@lem1606303 y x h1)). Qed.
Lemma lem1606411 (_25319 : real) (_25320 : real) (_25321 : real) (h1 : term34) : term405 _25319 _25320 _25321.
Proof. exact (EQ_MP (@lem1606407 _25319 _25320 _25321) (@lem1606386 _25321 _25319 _25320 h1)). Qed.
Lemma lem1606412 (x : real) (y : real) (h1 : term34) : term406 x y.
Proof. exact (@lem1606411 term36 x y h1). Qed.
Lemma lem1606415 (y : real) (x : real) (h1 : term34) (h2 : term213 y x) (h3 : term81 y x) : term376 x y.
Proof. exact (@lem1606412 x y h1 (@lem1606409 y x h2 h3)). Qed.
Lemma lem1606416 (y : real) (x : real) (h1 : term34) (h2 : term213 y x) (h3 : term81 y x) : term377 x y.
Proof. exact (fun h0 : term378 x y => @lem1606415 y x h1 h2 h3). Qed.
Lemma lem1606418 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606419 (x : real) (y : real) : (term377 x y) = (term376 x y).
Proof. exact (@lem1606418 (term376 x y)). Qed.
Lemma lem1606420 (y : real) (x : real) (h1 : term34) (h2 : term213 y x) (h3 : term81 y x) : term376 x y.
Proof. exact (EQ_MP (@lem1606419 x y) (@lem1606416 y x h1 h2 h3)). Qed.
Lemma lem1606438 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1606439 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term252 _25375 _25376 _25373 _25374) = (term293 _25375 _25376 _25373 _25374).
Proof. exact (@lem1606438 (real_le _25375 _25376) (term264 _25374 _25376) (term294 _25373 _25374)). Qed.
Lemma lem1606457 (_25373 : real) (_25375 : real) : (term265 _25373 _25375) = (term265 _25373 _25375).
Proof. exact (eq_refl (term265 _25373 _25375)). Qed.
Lemma lem1606458 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term254 _25375 _25376 _25373 _25374) = (term295 _25375 _25376 _25373 _25374).
Proof. exact (MK_COMB (@lem1606457 _25373 _25375) (@lem1606439 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606462 (q : Prop) (p : Prop) (r : Prop) : (term267 p q r) = (term267 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1606463 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term295 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374).
Proof. exact (@lem1606462 (real_le _25375 _25376) (term264 _25373 _25375) (term297 _25376 _25373 _25374)). Qed.
Lemma lem1606493 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term254 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374).
Proof. exact (TRANS (@lem1606458 _25375 _25376 _25373 _25374) (@lem1606463 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606494 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1606495 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term298 _25375 _25376 _25373 _25374) = (term299 _25375 _25376 _25373 _25374).
Proof. exact (MK_COMB (@lem1606494) (@lem1606493 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606525 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term296 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374).
Proof. exact (eq_refl (term296 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606526 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : ((term254 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374)) = ((term296 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374)).
Proof. exact (MK_COMB (@lem1606495 _25375 _25376 _25373 _25374) (@lem1606525 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606528 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1606529 (x : Prop) : (x = x) = True.
Proof. exact (@lem1606528 Prop x). Qed.
Lemma lem1606530 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : ((term296 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374)) = True.
Proof. exact (@lem1606529 (term296 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606531 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : ((term254 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374)) = True.
Proof. exact (TRANS (@lem1606526 _25375 _25376 _25373 _25374) (@lem1606530 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606532 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : True = ((term254 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374)).
Proof. exact (SYM (@lem1606531 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606533 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term254 _25375 _25376 _25373 _25374) = (term296 _25375 _25376 _25373 _25374).
Proof. exact (EQ_MP (@lem1606532 _25375 _25376 _25373 _25374) (@lem0)). Qed.
Lemma lem1606534 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : term296 _25375 _25376 _25373 _25374.
Proof. exact (EQ_MP (@lem1606533 _25375 _25376 _25373 _25374) (@lem1606219 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606536 (b : Prop) (a : Prop) : (a \/ b) = (term271 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1606537 (_25373 : real) (_25374 : real) (_25375 : real) (_25376 : real) : (term296 _25375 _25376 _25373 _25374) = (term300 _25373 _25374 _25375 _25376).
Proof. exact (@lem1606536 (term301 _25375 _25376 _25373 _25374) (real_le _25375 _25376)). Qed.
Lemma lem1606539 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1606540 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term302 _25375 _25376 _25373 _25374) = (term303 _25375 _25376 _25373 _25374).
Proof. exact (@lem1606539 (term264 _25373 _25375) (term297 _25376 _25373 _25374)). Qed.
Lemma lem1606542 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606543 (_25373 : real) (_25375 : real) : (term279 _25373 _25375) = (_25373 = _25375).
Proof. exact (@lem1606542 (_25373 = _25375)). Qed.
Lemma lem1606544 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1606545 (_25373 : real) (_25375 : real) : (term280 _25373 _25375) = (term281 _25373 _25375).
Proof. exact (MK_COMB (@lem1606544) (@lem1606543 _25373 _25375)). Qed.
Lemma lem1606547 (a : Prop) (b : Prop) : (term274 a b) = (term275 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1606548 (_25376 : real) (_25373 : real) (_25374 : real) : (term304 _25376 _25373 _25374) = (term305 _25376 _25373 _25374).
Proof. exact (@lem1606547 (term264 _25374 _25376) (term294 _25373 _25374)). Qed.
Lemma lem1606550 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606551 (_25374 : real) (_25376 : real) : (term279 _25374 _25376) = (_25374 = _25376).
Proof. exact (@lem1606550 (_25374 = _25376)). Qed.
Lemma lem1606552 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1606553 (_25374 : real) (_25376 : real) : (term280 _25374 _25376) = (term281 _25374 _25376).
Proof. exact (MK_COMB (@lem1606552) (@lem1606551 _25374 _25376)). Qed.
Lemma lem1606555 (a : Prop) : (term278 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1606556 (_25373 : real) (_25374 : real) : (term306 _25373 _25374) = (real_le _25373 _25374).
Proof. exact (@lem1606555 (real_le _25373 _25374)). Qed.
Lemma lem1606557 (_25376 : real) (_25373 : real) (_25374 : real) : (term305 _25376 _25373 _25374) = (term307 _25376 _25373 _25374).
Proof. exact (MK_COMB (@lem1606553 _25374 _25376) (@lem1606556 _25373 _25374)). Qed.
Lemma lem1606558 (_25376 : real) (_25373 : real) (_25374 : real) : (term304 _25376 _25373 _25374) = (term307 _25376 _25373 _25374).
Proof. exact (TRANS (@lem1606548 _25376 _25373 _25374) (@lem1606557 _25376 _25373 _25374)). Qed.
Lemma lem1606559 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term303 _25375 _25376 _25373 _25374) = (term308 _25375 _25376 _25373 _25374).
Proof. exact (MK_COMB (@lem1606545 _25373 _25375) (@lem1606558 _25376 _25373 _25374)). Qed.
Lemma lem1606560 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term302 _25375 _25376 _25373 _25374) = (term308 _25375 _25376 _25373 _25374).
Proof. exact (TRANS (@lem1606540 _25375 _25376 _25373 _25374) (@lem1606559 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606561 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1606562 (_25375 : real) (_25376 : real) (_25373 : real) (_25374 : real) : (term309 _25375 _25376 _25373 _25374) = (term310 _25375 _25376 _25373 _25374).
Proof. exact (MK_COMB (@lem1606561) (@lem1606560 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606563 (_25375 : real) (_25376 : real) : (real_le _25375 _25376) = (real_le _25375 _25376).
Proof. exact (eq_refl (real_le _25375 _25376)). Qed.
Lemma lem1606564 (_25373 : real) (_25374 : real) (_25375 : real) (_25376 : real) : (term300 _25373 _25374 _25375 _25376) = (term311 _25373 _25374 _25375 _25376).
Proof. exact (MK_COMB (@lem1606562 _25375 _25376 _25373 _25374) (@lem1606563 _25375 _25376)). Qed.
Lemma lem1606565 (_25373 : real) (_25374 : real) (_25375 : real) (_25376 : real) : (term296 _25375 _25376 _25373 _25374) = (term311 _25373 _25374 _25375 _25376).
Proof. exact (TRANS (@lem1606537 _25373 _25374 _25375 _25376) (@lem1606564 _25373 _25374 _25375 _25376)). Qed.
Lemma lem1606567 (y : real) (x : real) (h1 : term34) (h2 : term213 y x) (h3 : term81 y x) : term407 x y.
Proof. exact (conj (@lem1606289 x y) (@lem1606420 y x h1 h2 h3)). Qed.
Lemma lem1606568 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : term408 x y.
Proof. exact (conj (@lem1606281 y h2) (@lem1606567 y x h1 h3 h4)). Qed.
Lemma lem1606570 (_25373 : real) (_25374 : real) (_25375 : real) (_25376 : real) : term311 _25373 _25374 _25375 _25376.
Proof. exact (EQ_MP (@lem1606565 _25373 _25374 _25375 _25376) (@lem1606534 _25375 _25376 _25373 _25374)). Qed.
Lemma lem1606571 (x : real) (y : real) : term409 x y.
Proof. exact (@lem1606570 (term35 y) (real_mul x y) term36 (real_mul x y)). Qed.
Lemma lem1606574 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : term55 x y.
Proof. exact (@lem1606571 x y (@lem1606568 y x h1 h2 h3 h4)). Qed.
Lemma lem1606575 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : term292 x y.
Proof. exact (fun h0 : term243 x y => @lem1606574 y x h1 h2 h3 h4). Qed.
Lemma lem1606577 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606578 (x : real) (y : real) : (term292 x y) = (term55 x y).
Proof. exact (@lem1606577 (term55 x y)). Qed.
Lemma lem1606579 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : term55 x y.
Proof. exact (EQ_MP (@lem1606578 x y) (@lem1606575 y x h1 h2 h3 h4)). Qed.
Lemma lem1606582 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1606584 (x : real) (y : real) : (term243 x y) = (term365 x y).
Proof. exact (@lem1606582 (term55 x y)). Qed.
Lemma lem1606587 (y : real) (x : real) (h1 : term213 y x) : term365 x y.
Proof. exact (EQ_MP (@lem1606584 x y) (@lem1604687 y x h1)). Qed.
Lemma lem1606590 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : False.
Proof. exact (@lem1606587 y x h3 (@lem1606579 y x h1 h2 h3 h4)). Qed.
Lemma lem1606591 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : term345.
Proof. exact (fun h0 : ~ False => @lem1606590 y x h1 h2 h3 h4). Qed.
Lemma lem1606593 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1606594 : term345 = False.
Proof. exact (@lem1606593 False). Qed.
Lemma lem1606595 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : False.
Proof. exact (EQ_MP (@lem1606594) (@lem1606591 y x h1 h2 h3 h4)). Qed.
Lemma lem1606596 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : term38 = False.
Proof. exact (prop_ext (fun h5 : term38 => @lem1606595 y x h1 h2 h3 h4) (fun h5 : False => @lem1604323 h2)). Qed.
Lemma lem1606597 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term213 y x) (h4 : term81 y x) : False.
Proof. exact (EQ_MP (@lem1606596 y x h1 h2 h3 h4) (@lem1604323 h2)). Qed.
Lemma lem1606598 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : term38 = False.
Proof. exact (prop_ext (fun h5 : term38 => @lem1606200 y x h1 h2 h3 h4) (fun h5 : False => @lem1604215 h2)). Qed.
Lemma lem1606599 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term212 y x) (h4 : term81 y x) : False.
Proof. exact (EQ_MP (@lem1606598 y x h1 h2 h3 h4) (@lem1604215 h2)). Qed.
Lemma lem1606600 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : term41 = False.
Proof. exact (prop_ext (fun h5 : term41 => @lem1605662 x y h1 h2 h3 h4) (fun h5 : False => @lem1604100 h2)). Qed.
Lemma lem1606601 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term130 x y) (h4 : term59 x y) : False.
Proof. exact (EQ_MP (@lem1606600 x y h1 h2 h3 h4) (@lem1604100 h2)). Qed.
Lemma lem1606602 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : term41 = False.
Proof. exact (prop_ext (fun h5 : term41 => @lem1605267 x y h1 h2 h3 h4) (fun h5 : False => @lem1603992 h2)). Qed.
Lemma lem1606603 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term126 x y) (h4 : term59 x y) : False.
Proof. exact (EQ_MP (@lem1606602 x y h1 h2 h3 h4) (@lem1603992 h2)). Qed.
Lemma lem1606604 (y : real) (x : real) (h1 : term34) (h2 : term38) (h3 : term81 y x) : False.
Proof. exact (or_elim (@lem1603978 y x h3) (fun h0 : term212 y x => @lem1606599 y x h1 h2 h0 h3) (fun h0 : term213 y x => @lem1606597 y x h1 h2 h0 h3)). Qed.
Lemma lem1606605 (x : real) (y : real) (h1 : term10) (h2 : term41) (h3 : term59 x y) : False.
Proof. exact (or_elim (@lem1603970 x y h3) (fun h0 : term126 x y => @lem1606603 x y h1 h2 h0 h3) (fun h0 : term130 x y => @lem1606601 x y h1 h2 h0 h3)). Qed.
Lemma lem1606606 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term185 y x) : False.
Proof. exact (or_elim (@lem1603967 y x h5) (fun h0 : term59 x y => @lem1606605 x y h1 h3 h0) (fun h0 : term81 y x => @lem1606604 y x h2 h4 h0)). Qed.
Lemma lem1606607 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term185 y x) : (term185 y x) = False.
Proof. exact (prop_ext (fun h6 : term185 y x => @lem1606606 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1603967 y x h5)). Qed.
Lemma lem1606608 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term185 y x) : False.
Proof. exact (EQ_MP (@lem1606607 y x h1 h2 h3 h4 h5) (@lem1603967 y x h5)). Qed.
Lemma lem1606609 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term185 y x) : term38 = False.
Proof. exact (prop_ext (fun h6 : term38 => @lem1606608 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1603679 h4)). Qed.
Lemma lem1606610 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term185 y x) : False.
Proof. exact (EQ_MP (@lem1606609 y x h1 h2 h3 h4 h5) (@lem1603679 h4)). Qed.
Lemma lem1606611 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term185 y x) : term41 = False.
Proof. exact (prop_ext (fun h6 : term41 => @lem1606610 y x h1 h2 h3 h4 h5) (fun h6 : False => @lem1603658 h3)). Qed.
Lemma lem1606612 (y : real) (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term185 y x) : False.
Proof. exact (EQ_MP (@lem1606611 y x h1 h2 h3 h4 h5) (@lem1603658 h3)). Qed.
Lemma lem1606613 (x : real) (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term188 x) : False.
Proof. exact (ex_elim (@lem1603636 x h5) (fun y : real => fun h0 : term187 x y => @lem1606612 y x h1 h2 h3 h4 h0)). Qed.
Lemma lem1606614 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : False.
Proof. exact (ex_elim (@lem1603427 h5) (fun x : real => fun h0 : term189 x => @lem1606613 x h1 h2 h3 h4 h0)). Qed.
Lemma lem1606615 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : term38 = False.
Proof. exact (prop_ext (fun h6 : term38 => @lem1606614 h1 h2 h3 h4 h5) (fun h6 : False => @lem1603453 h4)). Qed.
Lemma lem1606616 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : False.
Proof. exact (EQ_MP (@lem1606615 h1 h2 h3 h4 h5) (@lem1603453 h4)). Qed.
Lemma lem1606617 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : term41 = False.
Proof. exact (prop_ext (fun h6 : term41 => @lem1606616 h1 h2 h3 h4 h5) (fun h6 : False => @lem1603440 h3)). Qed.
Lemma lem1606618 (h1 : term10) (h2 : term34) (h3 : term41) (h4 : term38) (h5 : term3) : False.
Proof. exact (EQ_MP (@lem1606617 h1 h2 h3 h4 h5) (@lem1603440 h3)). Qed.
Lemma lem1606619 (h1 : term34) (h2 : term41) (h3 : term38) (h4 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1606618 h0 h1 h2 h3 h4). Qed.
Lemma lem1606620 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1606621 (h1 : term34) (h2 : term41) (h3 : term38) (h4 : term3) : term9.
Proof. exact (EQ_MP (@lem1606620) (@lem1606619 h1 h2 h3 h4)). Qed.
Lemma lem1606622 (h1 : term41) (h2 : term38) (h3 : term3) : term13.
Proof. exact (fun h0 : term34 => @lem1606621 h0 h1 h2 h3). Qed.
Lemma lem1606623 (h1 : term41) (h2 : term3) : term16.
Proof. exact (fun h0 : term38 => @lem1606622 h1 h0 h2). Qed.
Lemma lem1606624 (h1 : term3) : term19.
Proof. exact (fun h0 : term41 => @lem1606623 h0 h1). Qed.
Lemma lem1606625 : term21.
Proof. exact (fun h0 : term3 => @lem1606624 h0). Qed.
Lemma lem1606626 : term4.
Proof. exact (EQ_MP (@lem1602959) (@lem1606625)). Qed.
Lemma lem1606628 : term4.
Proof. exact (@lem1602683 (@lem1606626)). Qed.
Lemma lem1606629 (h1 : term3) : term18.
Proof. exact (@lem1606628 (@lem1602668 h1)). Qed.
Lemma lem1606630 (h1 : term3) : term15.
Proof. exact (@lem1606629 h1 (@lem1356740)). Qed.
Lemma lem1606631 (h1 : term3) : term12.
Proof. exact (@lem1606630 h1 (@lem1357243)). Qed.
Lemma lem1606632 (h1 : term3) : term8.
Proof. exact (@lem1606631 h1 (@lem1600741)). Qed.
Lemma lem1606633 (h1 : term3) : False.
Proof. exact (@lem1606632 h1 (@lem1602377)). Qed.
Lemma lem1606634 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1606633 h1) (fun h2 : False => @lem1602668 h1)). Qed.
Lemma lem1606635 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1606634 h1) (@lem1602668 h1)). Qed.
Lemma lem1606636 : term2.
Proof. exact (fun h0 : term3 => @lem1606635 h0). Qed.
Lemma lem1606637 : term1.
Proof. exact (EQ_MP (@lem1602667) (@lem1606636)). Qed.
