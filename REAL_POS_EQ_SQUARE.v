Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POS_EQ_SQUARE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import REAL_LE_POW_2_spec.
Require Import SQRT_WORKS_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1943648 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1943649 : term1 = term2.
Proof. exact (@lem1943648 term1). Qed.
Lemma lem1943650 : term2 = term1.
Proof. exact (SYM (@lem1943649)). Qed.
Lemma lem1943651 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1943654 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1943655 : term5.
Proof. exact (fun h0 : term4 => @lem1943654 h0). Qed.
Lemma lem1943656 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1943657 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem1943658 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1943656 h2 (@lem1943657 h1)). Qed.
Lemma lem1943659 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem1943658 h1 h0). Qed.
Lemma lem1943660 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem1943661 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem1943659 h1 (@lem1943660 h2)). Qed.
Lemma lem1943662 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem1943661 h0 h1). Qed.
Lemma lem1943663 : term7.
Proof. exact (fun h0 : term5 => @lem1943662 h0). Qed.
Lemma lem1943666 : term5.
Proof. exact (@lem1943663 (@lem1943655)). Qed.
Lemma lem1943688 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1943689 : term8 = term9.
Proof. exact (@lem1943688 term10). Qed.
Lemma lem1943694 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem1943695 : term12 = term13.
Proof. exact (MK_COMB (@lem1943694) (@lem1943689)). Qed.
Lemma lem1943698 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem1943705 : term4 = term15.
Proof. exact (MK_COMB (@lem1943698) (@lem1943695)). Qed.
Lemma lem1943706 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1943707 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1943706 x)). Qed.
Lemma lem1943708 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1943709 : term10 = term10.
Proof. exact (MK_COMB (@lem1943708) (@lem1943707)). Qed.
Lemma lem1943710 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1943711 : term9 = term9.
Proof. exact (MK_COMB (@lem1943710) (@lem1943709)). Qed.
Lemma lem1943720 (x : real) : (term18 x) = (term18 x).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1943721 : term19 = term19.
Proof. exact (fun_ext (fun x : real => @lem1943720 x)). Qed.
Lemma lem1943722 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1943723 : term20 = term20.
Proof. exact (MK_COMB (@lem1943722) (@lem1943721)). Qed.
Lemma lem1943724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1943725 : term11 = term11.
Proof. exact (MK_COMB (@lem1943724) (@lem1943723)). Qed.
Lemma lem1943726 : term13 = term13.
Proof. exact (MK_COMB (@lem1943725) (@lem1943711)). Qed.
Lemma lem1943727 (y : real) (x : real) : ((term21 y) = x) = ((term21 y) = x).
Proof. exact (eq_refl ((term21 y) = x)). Qed.
Lemma lem1943728 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1943727 y x)). Qed.
Lemma lem1943729 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943730 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1943729) (@lem1943728 x)). Qed.
Lemma lem1943733 (x : real) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1943734 (x : real) : ((term25 x) = (term23 x)) = ((term25 x) = (term23 x)).
Proof. exact (MK_COMB (@lem1943733 x) (@lem1943730 x)). Qed.
Lemma lem1943735 : term26 = term26.
Proof. exact (fun_ext (fun x : real => @lem1943734 x)). Qed.
Lemma lem1943736 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1943737 : term1 = term1.
Proof. exact (MK_COMB (@lem1943736) (@lem1943735)). Qed.
Lemma lem1943738 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1943739 : term3 = term3.
Proof. exact (MK_COMB (@lem1943738) (@lem1943737)). Qed.
Lemma lem1943740 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1943741 : term14 = term14.
Proof. exact (MK_COMB (@lem1943740) (@lem1943739)). Qed.
Lemma lem1943742 : term15 = term15.
Proof. exact (MK_COMB (@lem1943741) (@lem1943726)). Qed.
Lemma lem1943777 : term4 = term15.
Proof. exact (TRANS (@lem1943705) (@lem1943742)). Qed.
Lemma lem1943778 : term15 = term4.
Proof. exact (SYM (@lem1943777)). Qed.
Lemma lem1943779 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem1943780 (h1 : term20) : term20.
Proof. exact (h1). Qed.
Lemma lem1943781 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1943785 (y : real) (x : real) : ((term21 y) = x) = ((term21 y) = x).
Proof. exact (eq_refl ((term21 y) = x)). Qed.
Lemma lem1943786 (P : real -> Prop) : (term27 P) = (term28 P).
Proof. exact (@lem18394 real P). Qed.
Lemma lem1943787 (x : real) : (term29 x) = (term30 x).
Proof. exact (@lem1943786 (term22 x)). Qed.
Lemma lem1943788 (y : real) (x : real) : (term31 x y) = ((term21 y) = x).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1943789 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1943791 (y : real) (x : real) : (term32 x y) = (term33 y x).
Proof. exact (MK_COMB (@lem1943789) (@lem1943788 y x)). Qed.
Lemma lem1943792 (x : real) : (term34 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1943791 y x)). Qed.
Lemma lem1943793 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1943794 (x : real) : (term30 x) = (term36 x).
Proof. exact (MK_COMB (@lem1943793) (@lem1943792 x)). Qed.
Lemma lem1943795 (x : real) : (term29 x) = (term36 x).
Proof. exact (TRANS (@lem1943787 x) (@lem1943794 x)). Qed.
Lemma lem1943796 (x : real) : (term22 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1943785 y x)). Qed.
Lemma lem1943797 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943798 (x : real) : (term23 x) = (term23 x).
Proof. exact (MK_COMB (@lem1943797) (@lem1943796 x)). Qed.
Lemma lem1943800 (x : real) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1943801 (x : real) : (term38 x) = (term38 x).
Proof. exact (MK_COMB (@lem1943800 x) (@lem1943798 x)). Qed.
Lemma lem1943803 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1943804 (x : real) : (term40 x) = (term41 x).
Proof. exact (MK_COMB (@lem1943803 x) (@lem1943795 x)). Qed.
Lemma lem1943805 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1943806 (x : real) : (term42 x) = (term43 x).
Proof. exact (MK_COMB (@lem1943805) (@lem1943804 x)). Qed.
Lemma lem1943807 (x : real) : (term44 x) = (term45 x).
Proof. exact (MK_COMB (@lem1943806 x) (@lem1943801 x)). Qed.
Lemma lem1943808 (x : real) : (term46 x) = (term44 x).
Proof. exact (@lem17646 (term25 x) (term23 x)). Qed.
Lemma lem1943809 (x : real) : (term46 x) = (term45 x).
Proof. exact (TRANS (@lem1943808 x) (@lem1943807 x)). Qed.
Lemma lem1943810 (P : real -> Prop) : (term47 P) = (term48 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1943811 : term3 = term49.
Proof. exact (@lem1943810 term26). Qed.
Lemma lem1943812 (x : real) : (term50 x) = ((term25 x) = (term23 x)).
Proof. exact (eq_refl (term50 x)). Qed.
Lemma lem1943813 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1943814 (x : real) : (term51 x) = (term46 x).
Proof. exact (MK_COMB (@lem1943813) (@lem1943812 x)). Qed.
Lemma lem1943815 (x : real) : (term51 x) = (term45 x).
Proof. exact (TRANS (@lem1943814 x) (@lem1943809 x)). Qed.
Lemma lem1943816 : term52 = term53.
Proof. exact (fun_ext (fun x : real => @lem1943815 x)). Qed.
Lemma lem1943817 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943818 : term49 = term54.
Proof. exact (MK_COMB (@lem1943817) (@lem1943816)). Qed.
Lemma lem1943819 : term3 = term54.
Proof. exact (TRANS (@lem1943811) (@lem1943818)). Qed.
Lemma lem1943821 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term55 A P Q) = (term56 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem1943822 (P : real -> Prop) (Q : real -> Prop) : (term57 P Q) = (term58 P Q).
Proof. exact (@lem1943821 real P Q). Qed.
Lemma lem1943823 : term59 = term60.
Proof. exact (@lem1943822 term61 term62). Qed.
Lemma lem1943824 (x : real) : (term63 x) = (term41 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1943825 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1943826 (x : real) : (term64 x) = (term43 x).
Proof. exact (MK_COMB (@lem1943825) (@lem1943824 x)). Qed.
Lemma lem1943827 (x : real) : (term65 x) = (term38 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1943828 (x : real) : (term66 x) = (term45 x).
Proof. exact (MK_COMB (@lem1943826 x) (@lem1943827 x)). Qed.
Lemma lem1943829 : term67 = term53.
Proof. exact (fun_ext (fun x : real => @lem1943828 x)). Qed.
Lemma lem1943830 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943831 : term59 = term54.
Proof. exact (MK_COMB (@lem1943830) (@lem1943829)). Qed.
Lemma lem1943832 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1943833 : term68 = term69.
Proof. exact (MK_COMB (@lem1943832) (@lem1943831)). Qed.
Lemma lem1943834 (x : real) : (term63 x) = (term41 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1943835 : term70 = term61.
Proof. exact (fun_ext (fun x : real => @lem1943834 x)). Qed.
Lemma lem1943836 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943837 : term71 = term72.
Proof. exact (MK_COMB (@lem1943836) (@lem1943835)). Qed.
Lemma lem1943838 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1943839 : term73 = term74.
Proof. exact (MK_COMB (@lem1943838) (@lem1943837)). Qed.
Lemma lem1943840 (x : real) : (term65 x) = (term38 x).
Proof. exact (eq_refl (term65 x)). Qed.
Lemma lem1943841 : term75 = term62.
Proof. exact (fun_ext (fun x : real => @lem1943840 x)). Qed.
Lemma lem1943842 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943843 : term76 = term77.
Proof. exact (MK_COMB (@lem1943842) (@lem1943841)). Qed.
Lemma lem1943844 : term60 = term78.
Proof. exact (MK_COMB (@lem1943839) (@lem1943843)). Qed.
Lemma lem1943845 : (term59 = term60) = (term54 = term78).
Proof. exact (MK_COMB (@lem1943833) (@lem1943844)). Qed.
Lemma lem1943846 : term54 = term78.
Proof. exact (EQ_MP (@lem1943845) (@lem1943823)). Qed.
Lemma lem1943952 {A : Type'} (P : Prop) (Q : A -> Prop) : (term79 A P Q) = (term80 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1943953 (P : Prop) (Q : real -> Prop) : (term81 P Q) = (term82 P Q).
Proof. exact (@lem1943952 real P Q). Qed.
Lemma lem1943954 (x : real) : (term83 x) = (term84 x).
Proof. exact (@lem1943953 (term85 x) (term22 x)). Qed.
Lemma lem1943955 (y : real) (x : real) : (term31 x y) = ((term21 y) = x).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1943956 (x : real) : (term86 x) = (term22 x).
Proof. exact (fun_ext (fun y : real => @lem1943955 y x)). Qed.
Lemma lem1943957 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943958 (x : real) : (term87 x) = (term23 x).
Proof. exact (MK_COMB (@lem1943957) (@lem1943956 x)). Qed.
Lemma lem1943959 (x : real) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1943960 (x : real) : (term83 x) = (term38 x).
Proof. exact (MK_COMB (@lem1943959 x) (@lem1943958 x)). Qed.
Lemma lem1943961 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1943962 (x : real) : (term88 x) = (term89 x).
Proof. exact (MK_COMB (@lem1943961) (@lem1943960 x)). Qed.
Lemma lem1943963 (y : real) (x : real) : (term31 x y) = ((term21 y) = x).
Proof. exact (eq_refl (term31 x y)). Qed.
Lemma lem1943964 (x : real) : (term37 x) = (term37 x).
Proof. exact (eq_refl (term37 x)). Qed.
Lemma lem1943965 (y : real) (x : real) : (term90 x y) = (term91 y x).
Proof. exact (MK_COMB (@lem1943964 x) (@lem1943963 y x)). Qed.
Lemma lem1943966 (x : real) : (term92 x) = (term93 x).
Proof. exact (fun_ext (fun y : real => @lem1943965 y x)). Qed.
Lemma lem1943967 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943968 (x : real) : (term84 x) = (term94 x).
Proof. exact (MK_COMB (@lem1943967) (@lem1943966 x)). Qed.
Lemma lem1943969 (x : real) : ((term83 x) = (term84 x)) = ((term38 x) = (term94 x)).
Proof. exact (MK_COMB (@lem1943962 x) (@lem1943968 x)). Qed.
Lemma lem1943970 (x : real) : (term38 x) = (term94 x).
Proof. exact (EQ_MP (@lem1943969 x) (@lem1943954 x)). Qed.
Lemma lem1943971 : term62 = term95.
Proof. exact (fun_ext (fun x : real => @lem1943970 x)). Qed.
Lemma lem1943972 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943973 : term77 = term96.
Proof. exact (MK_COMB (@lem1943972) (@lem1943971)). Qed.
Lemma lem1943974 : term74 = term74.
Proof. exact (eq_refl term74). Qed.
Lemma lem1943975 : term78 = term97.
Proof. exact (MK_COMB (@lem1943974) (@lem1943973)). Qed.
Lemma lem1943977 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term56 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem1943978 (P : real -> Prop) (Q : real -> Prop) : (term58 P Q) = (term57 P Q).
Proof. exact (@lem1943977 real P Q). Qed.
Lemma lem1943979 : term98 = term99.
Proof. exact (@lem1943978 term61 term95). Qed.
Lemma lem1943980 (x : real) : (term63 x) = (term41 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1943981 : term70 = term61.
Proof. exact (fun_ext (fun x : real => @lem1943980 x)). Qed.
Lemma lem1943982 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943983 : term71 = term72.
Proof. exact (MK_COMB (@lem1943982) (@lem1943981)). Qed.
Lemma lem1943984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1943985 : term73 = term74.
Proof. exact (MK_COMB (@lem1943984) (@lem1943983)). Qed.
Lemma lem1943986 (x : real) : (term100 x) = (term94 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1943987 : term101 = term95.
Proof. exact (fun_ext (fun x : real => @lem1943986 x)). Qed.
Lemma lem1943988 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1943989 : term102 = term96.
Proof. exact (MK_COMB (@lem1943988) (@lem1943987)). Qed.
Lemma lem1943990 : term98 = term97.
Proof. exact (MK_COMB (@lem1943985) (@lem1943989)). Qed.
Lemma lem1943991 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1943992 : term103 = term104.
Proof. exact (MK_COMB (@lem1943991) (@lem1943990)). Qed.
Lemma lem1943993 (x : real) : (term63 x) = (term41 x).
Proof. exact (eq_refl (term63 x)). Qed.
Lemma lem1943994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1943995 (x : real) : (term64 x) = (term43 x).
Proof. exact (MK_COMB (@lem1943994) (@lem1943993 x)). Qed.
Lemma lem1943996 (x : real) : (term100 x) = (term94 x).
Proof. exact (eq_refl (term100 x)). Qed.
Lemma lem1943997 (x : real) : (term105 x) = (term106 x).
Proof. exact (MK_COMB (@lem1943995 x) (@lem1943996 x)). Qed.
Lemma lem1943998 : term107 = term108.
Proof. exact (fun_ext (fun x : real => @lem1943997 x)). Qed.
Lemma lem1943999 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1944000 : term99 = term109.
Proof. exact (MK_COMB (@lem1943999) (@lem1943998)). Qed.
Lemma lem1944001 : (term98 = term99) = (term97 = term109).
Proof. exact (MK_COMB (@lem1943992) (@lem1944000)). Qed.
Lemma lem1944002 : term97 = term109.
Proof. exact (EQ_MP (@lem1944001) (@lem1943979)). Qed.
Lemma lem1944004 {A : Type'} (P : Prop) (Q : A -> Prop) : (term110 A P Q) = (term111 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1944005 (P : Prop) (Q : real -> Prop) : (term112 P Q) = (term113 P Q).
Proof. exact (@lem1944004 real P Q). Qed.
Lemma lem1944006 (x : real) : (term114 x) = (term115 x).
Proof. exact (@lem1944005 (term41 x) (term93 x)). Qed.
Lemma lem1944007 (y : real) (x : real) : (term116 x y) = (term91 y x).
Proof. exact (eq_refl (term116 x y)). Qed.
Lemma lem1944008 (x : real) : (term117 x) = (term93 x).
Proof. exact (fun_ext (fun y : real => @lem1944007 y x)). Qed.
Lemma lem1944009 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1944010 (x : real) : (term118 x) = (term94 x).
Proof. exact (MK_COMB (@lem1944009) (@lem1944008 x)). Qed.
Lemma lem1944011 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1944012 (x : real) : (term114 x) = (term106 x).
Proof. exact (MK_COMB (@lem1944011 x) (@lem1944010 x)). Qed.
Lemma lem1944013 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1944014 (x : real) : (term119 x) = (term120 x).
Proof. exact (MK_COMB (@lem1944013) (@lem1944012 x)). Qed.
Lemma lem1944015 (y : real) (x : real) : (term116 x y) = (term91 y x).
Proof. exact (eq_refl (term116 x y)). Qed.
Lemma lem1944016 (x : real) : (term43 x) = (term43 x).
Proof. exact (eq_refl (term43 x)). Qed.
Lemma lem1944017 (y : real) (x : real) : (term121 x y) = (term122 y x).
Proof. exact (MK_COMB (@lem1944016 x) (@lem1944015 y x)). Qed.
Lemma lem1944018 (x : real) : (term123 x) = (term124 x).
Proof. exact (fun_ext (fun y : real => @lem1944017 y x)). Qed.
Lemma lem1944019 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1944020 (x : real) : (term115 x) = (term125 x).
Proof. exact (MK_COMB (@lem1944019) (@lem1944018 x)). Qed.
Lemma lem1944021 (x : real) : ((term114 x) = (term115 x)) = ((term106 x) = (term125 x)).
Proof. exact (MK_COMB (@lem1944014 x) (@lem1944020 x)). Qed.
Lemma lem1944022 (x : real) : (term106 x) = (term125 x).
Proof. exact (EQ_MP (@lem1944021 x) (@lem1944006 x)). Qed.
Lemma lem1944023 : term108 = term126.
Proof. exact (fun_ext (fun x : real => @lem1944022 x)). Qed.
Lemma lem1944024 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1944025 : term109 = term127.
Proof. exact (MK_COMB (@lem1944024) (@lem1944023)). Qed.
Lemma lem1944026 : term97 = term127.
Proof. exact (TRANS (@lem1944002) (@lem1944025)). Qed.
Lemma lem1944027 : term78 = term127.
Proof. exact (TRANS (@lem1943975) (@lem1944026)). Qed.
Lemma lem1944028 : term54 = term127.
Proof. exact (TRANS (@lem1943846) (@lem1944027)). Qed.
Lemma lem1944029 : term3 = term127.
Proof. exact (TRANS (@lem1943819) (@lem1944028)). Qed.
Lemma lem1944030 (h1 : term3) : term127.
Proof. exact (EQ_MP (@lem1944029) (@lem1943779 h1)). Qed.
Lemma lem1944041 (x : real) : (term18 x) = (term128 x).
Proof. exact (@lem17265 (term25 x) (term129 x)). Qed.
Lemma lem1944042 : term19 = term130.
Proof. exact (fun_ext (fun x : real => @lem1944041 x)). Qed.
Lemma lem1944043 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944096 : term20 = term131.
Proof. exact (MK_COMB (@lem1944043) (@lem1944042)). Qed.
Lemma lem1944097 (h1 : term20) : term131.
Proof. exact (EQ_MP (@lem1944096) (@lem1943780 h1)). Qed.
Lemma lem1944098 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1944099 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1944098 x)). Qed.
Lemma lem1944100 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944109 : term10 = term10.
Proof. exact (MK_COMB (@lem1944100) (@lem1944099)). Qed.
Lemma lem1944110 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1944109) (@lem1943781 h1)). Qed.
Lemma lem1944111 (x : real) (h1 : term125 x) : term125 x.
Proof. exact (h1). Qed.
Lemma lem1944112 (y : real) (x : real) (h1 : term122 y x) : term122 y x.
Proof. exact (h1). Qed.
Lemma lem1944157 (x : real) : (term128 x) = (term128 x).
Proof. exact (eq_refl (term128 x)). Qed.
Lemma lem1944158 : term130 = term130.
Proof. exact (fun_ext (fun x : real => @lem1944157 x)). Qed.
Lemma lem1944159 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944160 : term131 = term131.
Proof. exact (MK_COMB (@lem1944159) (@lem1944158)). Qed.
Lemma lem1944161 (h1 : term20) : term131.
Proof. exact (EQ_MP (@lem1944160) (@lem1944097 h1)). Qed.
Lemma lem1944180 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1944181 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1944180 x)). Qed.
Lemma lem1944182 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944183 : term10 = term10.
Proof. exact (MK_COMB (@lem1944182) (@lem1944181)). Qed.
Lemma lem1944184 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1944183) (@lem1944110 h1)). Qed.
Lemma lem1944213 (y : real) (x : real) : (term91 y x) = (term91 y x).
Proof. exact (eq_refl (term91 y x)). Qed.
Lemma lem1944230 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (eq_refl (term33 y x)). Qed.
Lemma lem1944231 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1944230 y x)). Qed.
Lemma lem1944232 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944233 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1944232) (@lem1944231 x)). Qed.
Lemma lem1944244 (x : real) : (term39 x) = (term39 x).
Proof. exact (eq_refl (term39 x)). Qed.
Lemma lem1944245 (x : real) : (term41 x) = (term41 x).
Proof. exact (MK_COMB (@lem1944244 x) (@lem1944233 x)). Qed.
Lemma lem1944246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1944247 (x : real) : (term43 x) = (term43 x).
Proof. exact (MK_COMB (@lem1944246) (@lem1944245 x)). Qed.
Lemma lem1944248 (y : real) (x : real) : (term122 y x) = (term122 y x).
Proof. exact (MK_COMB (@lem1944247 x) (@lem1944213 y x)). Qed.
Lemma lem1944249 (y : real) (x : real) (h1 : term122 y x) : term122 y x.
Proof. exact (EQ_MP (@lem1944248 y x) (@lem1944112 y x h1)). Qed.
Lemma lem1944250 (x : real) (h1 : term41 x) : term41 x.
Proof. exact (h1). Qed.
Lemma lem1944251 (y : real) (x : real) (h1 : term91 y x) : term91 y x.
Proof. exact (h1). Qed.
Lemma lem1944252 (x : real) (h1 : term41 x) : term36 x.
Proof. exact (proj2 (@lem1944250 x h1)). Qed.
Lemma lem1944273 (x : real) : (term128 x) = (term132 x).
Proof. exact (@lem19490 (term133 x) (term85 x) ((term134 x) = x)). Qed.
Lemma lem1944274 : term130 = term135.
Proof. exact (fun_ext (fun x : real => @lem1944273 x)). Qed.
Lemma lem1944275 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944277 : term131 = term136.
Proof. exact (MK_COMB (@lem1944275) (@lem1944274)). Qed.
Lemma lem1944278 (h1 : term20) : term136.
Proof. exact (EQ_MP (@lem1944277) (@lem1944161 h1)). Qed.
Lemma lem1944291 (y : real) (x : real) : (term33 y x) = (term33 y x).
Proof. exact (eq_refl (term33 y x)). Qed.
Lemma lem1944292 (x : real) : (term35 x) = (term35 x).
Proof. exact (fun_ext (fun y : real => @lem1944291 y x)). Qed.
Lemma lem1944293 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944295 (x : real) : (term36 x) = (term36 x).
Proof. exact (MK_COMB (@lem1944293) (@lem1944292 x)). Qed.
Lemma lem1944296 (x : real) (h1 : term41 x) : term36 x.
Proof. exact (EQ_MP (@lem1944295 x) (@lem1944252 x h1)). Qed.
Lemma lem1944321 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1944322 : term17 = term17.
Proof. exact (fun_ext (fun x : real => @lem1944321 x)). Qed.
Lemma lem1944323 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1944325 : term10 = term10.
Proof. exact (MK_COMB (@lem1944323) (@lem1944322)). Qed.
Lemma lem1944326 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1944325) (@lem1944184 h1)). Qed.
Lemma lem1944335 (_27231 : real) (h1 : term20) : term137 _27231.
Proof. exact (@lem1944278 h1 _27231). Qed.
Lemma lem1944336 (_27231 : real) : (term137 _27231) = (term132 _27231).
Proof. exact (eq_refl (term137 _27231)). Qed.
Lemma lem1944337 (_27231 : real) (h1 : term20) : term132 _27231.
Proof. exact (EQ_MP (@lem1944336 _27231) (@lem1944335 _27231 h1)). Qed.
Lemma lem1944341 (_27233 : real) (x : real) (h1 : term41 x) : term138 x _27233.
Proof. exact (@lem1944296 x h1 _27233). Qed.
Lemma lem1944342 (_27233 : real) (x : real) : (term138 x _27233) = (term33 _27233 x).
Proof. exact (eq_refl (term138 x _27233)). Qed.
Lemma lem1944347 (_27235 : real) (h1 : term10) : term139 _27235.
Proof. exact (@lem1944326 h1 _27235). Qed.
Lemma lem1944348 (_27235 : real) : (term139 _27235) = (term16 _27235).
Proof. exact (eq_refl (term139 _27235)). Qed.
Lemma lem1944359 (_27233 : real) (x : real) (h1 : term41 x) : term33 _27233 x.
Proof. exact (EQ_MP (@lem1944342 _27233 x) (@lem1944341 _27233 x h1)). Qed.
Lemma lem1944371 (_27231 : real) (h1 : term20) : term140 _27231.
Proof. exact (proj2 (@lem1944337 _27231 h1)). Qed.
Lemma lem1944375 (y : real) (x : real) (h1 : term91 y x) : term85 x.
Proof. exact (proj1 (@lem1944251 y x h1)). Qed.
Lemma lem1944377 (y : real) (x : real) (h1 : term91 y x) : (term21 y) = x.
Proof. exact (proj2 (@lem1944251 y x h1)). Qed.
Lemma lem1944390 (y : real) (x : real) (h1 : term91 y x) : x = (term21 y).
Proof. exact (SYM (@lem1944377 y x h1)). Qed.
Lemma lem1944419 : term141 = term141.
Proof. exact (eq_refl term141). Qed.
Lemma lem1944420 (y : real) (x : real) (h1 : term91 y x) : (term142 x) = (term143 y).
Proof. exact (MK_COMB (@lem1944419) (@lem1944390 y x h1)). Qed.
Lemma lem1944421 (y : real) : (term143 y) = (term144 y).
Proof. exact (eq_refl (term143 y)). Qed.
Lemma lem1944422 (x : real) : (term145 x) = (term145 x).
Proof. exact (eq_refl (term145 x)). Qed.
Lemma lem1944423 (x : real) (y : real) : ((term142 x) = (term143 y)) = ((term142 x) = (term144 y)).
Proof. exact (MK_COMB (@lem1944422 x) (@lem1944421 y)). Qed.
Lemma lem1944424 (x : real) : (term142 x) = (term85 x).
Proof. exact (eq_refl (term142 x)). Qed.
Lemma lem1944425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1944426 (x : real) : (term145 x) = (term146 x).
Proof. exact (MK_COMB (@lem1944425) (@lem1944424 x)). Qed.
Lemma lem1944427 (y : real) : (term144 y) = (term144 y).
Proof. exact (eq_refl (term144 y)). Qed.
Lemma lem1944428 (x : real) (y : real) : ((term142 x) = (term144 y)) = ((term85 x) = (term144 y)).
Proof. exact (MK_COMB (@lem1944426 x) (@lem1944427 y)). Qed.
Lemma lem1944429 (x : real) (y : real) : ((term142 x) = (term143 y)) = ((term85 x) = (term144 y)).
Proof. exact (TRANS (@lem1944423 x y) (@lem1944428 x y)). Qed.
Lemma lem1944430 (y : real) (x : real) (h1 : term91 y x) : (term85 x) = (term144 y).
Proof. exact (EQ_MP (@lem1944429 x y) (@lem1944420 y x h1)). Qed.
Lemma lem1944431 (y : real) (x : real) (h1 : term91 y x) : term144 y.
Proof. exact (EQ_MP (@lem1944430 y x h1) (@lem1944375 y x h1)). Qed.
Lemma lem1944539 (x : real) (h1 : term41 x) : term25 x.
Proof. exact (proj1 (@lem1944250 x h1)). Qed.
Lemma lem1944540 (x : real) (h1 : term41 x) : term147 x.
Proof. exact (fun h0 : term85 x => @lem1944539 x h1). Qed.
Lemma lem1944542 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1944543 (x : real) : (term147 x) = (term25 x).
Proof. exact (@lem1944542 (term25 x)). Qed.
Lemma lem1944544 (x : real) (h1 : term41 x) : term25 x.
Proof. exact (EQ_MP (@lem1944543 x) (@lem1944540 x h1)). Qed.
Lemma lem1944550 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1944551 (_27231 : real) : (term140 _27231) = (term149 _27231).
Proof. exact (@lem1944550 ((term134 _27231) = _27231) (term85 _27231)). Qed.
Lemma lem1944559 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1944560 (_27231 : real) : (term150 _27231) = (term151 _27231).
Proof. exact (MK_COMB (@lem1944559) (@lem1944551 _27231)). Qed.
Lemma lem1944568 (_27231 : real) : (term149 _27231) = (term149 _27231).
Proof. exact (eq_refl (term149 _27231)). Qed.
Lemma lem1944569 (_27231 : real) : ((term140 _27231) = (term149 _27231)) = ((term149 _27231) = (term149 _27231)).
Proof. exact (MK_COMB (@lem1944560 _27231) (@lem1944568 _27231)). Qed.
Lemma lem1944571 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1944572 (x : Prop) : (x = x) = True.
Proof. exact (@lem1944571 Prop x). Qed.
Lemma lem1944573 (_27231 : real) : ((term149 _27231) = (term149 _27231)) = True.
Proof. exact (@lem1944572 (term149 _27231)). Qed.
Lemma lem1944574 (_27231 : real) : ((term140 _27231) = (term149 _27231)) = True.
Proof. exact (TRANS (@lem1944569 _27231) (@lem1944573 _27231)). Qed.
Lemma lem1944575 (_27231 : real) : True = ((term140 _27231) = (term149 _27231)).
Proof. exact (SYM (@lem1944574 _27231)). Qed.
Lemma lem1944576 (_27231 : real) : (term140 _27231) = (term149 _27231).
Proof. exact (EQ_MP (@lem1944575 _27231) (@lem0)). Qed.
Lemma lem1944577 (_27231 : real) (h1 : term20) : term149 _27231.
Proof. exact (EQ_MP (@lem1944576 _27231) (@lem1944371 _27231 h1)). Qed.
Lemma lem1944579 (b : Prop) (a : Prop) : (a \/ b) = (term152 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1944580 (_27231 : real) : (term149 _27231) = (term153 _27231).
Proof. exact (@lem1944579 (term85 _27231) ((term134 _27231) = _27231)). Qed.
Lemma lem1944582 (a : Prop) : (term154 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1944583 (_27231 : real) : (term155 _27231) = (term25 _27231).
Proof. exact (@lem1944582 (term25 _27231)). Qed.
Lemma lem1944584 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1944585 (_27231 : real) : (term156 _27231) = (term157 _27231).
Proof. exact (MK_COMB (@lem1944584) (@lem1944583 _27231)). Qed.
Lemma lem1944586 (_27231 : real) : ((term134 _27231) = _27231) = ((term134 _27231) = _27231).
Proof. exact (eq_refl ((term134 _27231) = _27231)). Qed.
Lemma lem1944587 (_27231 : real) : (term153 _27231) = (term158 _27231).
Proof. exact (MK_COMB (@lem1944585 _27231) (@lem1944586 _27231)). Qed.
Lemma lem1944588 (_27231 : real) : (term149 _27231) = (term158 _27231).
Proof. exact (TRANS (@lem1944580 _27231) (@lem1944587 _27231)). Qed.
Lemma lem1944591 (_27231 : real) (h1 : term20) : term158 _27231.
Proof. exact (EQ_MP (@lem1944588 _27231) (@lem1944577 _27231 h1)). Qed.
Lemma lem1944592 (x : real) (h1 : term20) : term158 x.
Proof. exact (@lem1944591 x h1). Qed.
Lemma lem1944595 (x : real) (h1 : term20) (h2 : term41 x) : (term134 x) = x.
Proof. exact (@lem1944592 x h1 (@lem1944544 x h2)). Qed.
Lemma lem1944596 (x : real) (h1 : term20) (h2 : term41 x) : term159 x.
Proof. exact (fun h0 : term160 x => @lem1944595 x h1 h2). Qed.
Lemma lem1944598 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1944599 (x : real) : (term159 x) = ((term134 x) = x).
Proof. exact (@lem1944598 ((term134 x) = x)). Qed.
Lemma lem1944600 (x : real) (h1 : term20) (h2 : term41 x) : (term134 x) = x.
Proof. exact (EQ_MP (@lem1944599 x) (@lem1944596 x h1 h2)). Qed.
Lemma lem1944603 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1944605 (_27233 : real) (x : real) : (term33 _27233 x) = (term161 _27233 x).
Proof. exact (@lem1944603 ((term21 _27233) = x)). Qed.
Lemma lem1944608 (_27233 : real) (x : real) (h1 : term41 x) : term161 _27233 x.
Proof. exact (EQ_MP (@lem1944605 _27233 x) (@lem1944359 _27233 x h1)). Qed.
Lemma lem1944609 (x : real) (h1 : term41 x) : term162 x.
Proof. exact (@lem1944608 (sqrt x) x h1). Qed.
Lemma lem1944612 (x : real) (h1 : term20) (h2 : term41 x) : False.
Proof. exact (@lem1944609 x h2 (@lem1944600 x h1 h2)). Qed.
Lemma lem1944613 (x : real) (h1 : term20) (h2 : term41 x) : term163.
Proof. exact (fun h0 : ~ False => @lem1944612 x h1 h2). Qed.
Lemma lem1944615 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1944616 : term163 = False.
Proof. exact (@lem1944615 False). Qed.
Lemma lem1944617 (x : real) (h1 : term20) (h2 : term41 x) : False.
Proof. exact (EQ_MP (@lem1944616) (@lem1944613 x h1 h2)). Qed.
Lemma lem1944697 (_27235 : real) (h1 : term10) : term16 _27235.
Proof. exact (EQ_MP (@lem1944348 _27235) (@lem1944347 _27235 h1)). Qed.
Lemma lem1944698 (y : real) (h1 : term10) : term16 y.
Proof. exact (@lem1944697 y h1). Qed.
Lemma lem1944699 (y : real) (h1 : term10) : term164 y.
Proof. exact (fun h0 : term144 y => @lem1944698 y h1). Qed.
Lemma lem1944701 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1944702 (y : real) : (term164 y) = (term16 y).
Proof. exact (@lem1944701 (term16 y)). Qed.
Lemma lem1944703 (y : real) (h1 : term10) : term16 y.
Proof. exact (EQ_MP (@lem1944702 y) (@lem1944699 y h1)). Qed.
Lemma lem1944706 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1944708 (y : real) : (term144 y) = (term165 y).
Proof. exact (@lem1944706 (term16 y)). Qed.
Lemma lem1944711 (y : real) (x : real) (h1 : term91 y x) : term165 y.
Proof. exact (EQ_MP (@lem1944708 y) (@lem1944431 y x h1)). Qed.
Lemma lem1944714 (y : real) (x : real) (h1 : term10) (h2 : term91 y x) : False.
Proof. exact (@lem1944711 y x h2 (@lem1944703 y h1)). Qed.
Lemma lem1944715 (y : real) (x : real) (h1 : term10) (h2 : term91 y x) : term163.
Proof. exact (fun h0 : ~ False => @lem1944714 y x h1 h2). Qed.
Lemma lem1944717 (p : Prop) : (term148 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1944718 : term163 = False.
Proof. exact (@lem1944717 False). Qed.
Lemma lem1944720 (y : real) (x : real) (h1 : term10) (h2 : term91 y x) : False.
Proof. exact (EQ_MP (@lem1944718) (@lem1944715 y x h1 h2)). Qed.
Lemma lem1944721 (y : real) (x : real) (h1 : term10) (h2 : term91 y x) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1944720 y x h1 h2) (fun h3 : False => @lem1944326 h1)). Qed.
Lemma lem1944722 (y : real) (x : real) (h1 : term10) (h2 : term91 y x) : False.
Proof. exact (EQ_MP (@lem1944721 y x h1 h2) (@lem1944326 h1)). Qed.
Lemma lem1944723 (y : real) (x : real) (h1 : term20) (h2 : term10) (h3 : term122 y x) : False.
Proof. exact (or_elim (@lem1944249 y x h3) (fun h0 : term41 x => @lem1944617 x h1 h0) (fun h0 : term91 y x => @lem1944722 y x h2 h0)). Qed.
Lemma lem1944724 (y : real) (x : real) (h1 : term20) (h2 : term10) (h3 : term122 y x) : (term122 y x) = False.
Proof. exact (prop_ext (fun h4 : term122 y x => @lem1944723 y x h1 h2 h3) (fun h4 : False => @lem1944249 y x h3)). Qed.
Lemma lem1944725 (y : real) (x : real) (h1 : term20) (h2 : term10) (h3 : term122 y x) : False.
Proof. exact (EQ_MP (@lem1944724 y x h1 h2 h3) (@lem1944249 y x h3)). Qed.
Lemma lem1944726 (y : real) (x : real) (h1 : term20) (h2 : term10) (h3 : term122 y x) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1944725 y x h1 h2 h3) (fun h4 : False => @lem1944184 h2)). Qed.
Lemma lem1944727 (y : real) (x : real) (h1 : term20) (h2 : term10) (h3 : term122 y x) : False.
Proof. exact (EQ_MP (@lem1944726 y x h1 h2 h3) (@lem1944184 h2)). Qed.
Lemma lem1944728 (x : real) (h1 : term20) (h2 : term10) (h3 : term125 x) : False.
Proof. exact (ex_elim (@lem1944111 x h3) (fun y : real => fun h0 : term124 x y => @lem1944727 y x h1 h2 h0)). Qed.
Lemma lem1944729 (h1 : term20) (h2 : term10) (h3 : term3) : False.
Proof. exact (ex_elim (@lem1944030 h3) (fun x : real => fun h0 : term126 x => @lem1944728 x h1 h2 h0)). Qed.
Lemma lem1944730 (h1 : term20) (h2 : term10) (h3 : term3) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem1944729 h1 h2 h3) (fun h4 : False => @lem1944110 h2)). Qed.
Lemma lem1944731 (h1 : term20) (h2 : term10) (h3 : term3) : False.
Proof. exact (EQ_MP (@lem1944730 h1 h2 h3) (@lem1944110 h2)). Qed.
Lemma lem1944732 (h1 : term20) (h2 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem1944731 h1 h0 h2). Qed.
Lemma lem1944733 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1944734 (h1 : term20) (h2 : term3) : term9.
Proof. exact (EQ_MP (@lem1944733) (@lem1944732 h1 h2)). Qed.
Lemma lem1944735 (h1 : term3) : term13.
Proof. exact (fun h0 : term20 => @lem1944734 h0 h1). Qed.
Lemma lem1944736 : term15.
Proof. exact (fun h0 : term3 => @lem1944735 h0). Qed.
Lemma lem1944737 : term4.
Proof. exact (EQ_MP (@lem1943778) (@lem1944736)). Qed.
Lemma lem1944739 : term4.
Proof. exact (@lem1943666 (@lem1944737)). Qed.
Lemma lem1944740 (h1 : term3) : term12.
Proof. exact (@lem1944739 (@lem1943651 h1)). Qed.
Lemma lem1944741 (h1 : term3) : term8.
Proof. exact (@lem1944740 h1 (@lem1943636)). Qed.
Lemma lem1944742 (h1 : term3) : False.
Proof. exact (@lem1944741 h1 (@lem1646060)). Qed.
Lemma lem1944743 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem1944742 h1) (fun h2 : False => @lem1943651 h1)). Qed.
Lemma lem1944744 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem1944743 h1) (@lem1943651 h1)). Qed.
Lemma lem1944745 : term2.
Proof. exact (fun h0 : term3 => @lem1944744 h0). Qed.
Lemma lem1944746 : term1.
Proof. exact (EQ_MP (@lem1943650) (@lem1944745)). Qed.
