Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_WLOG_LE_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1339697_spec.
Require Import thm16474_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm69_spec.
Lemma lem1863613 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1863614 (P : type1626) : (term1 P) = (term2 P).
Proof. exact (@lem1863613 (term1 P)). Qed.
Lemma lem1863615 (P : type1626) : (term2 P) = (term1 P).
Proof. exact (SYM (@lem1863614 P)). Qed.
Lemma lem1863616 (P : type1626) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem1863619 (P : type1626) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem1863620 (P : type1626) : term5 P.
Proof. exact (fun h0 : term4 P => @lem1863619 P h0). Qed.
Lemma lem1863621 (P : type1626) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem1863622 (P : type1626) (h1 : term4 P) : term4 P.
Proof. exact (h1). Qed.
Lemma lem1863623 (P : type1626) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem1863621 P h2 (@lem1863622 P h1)). Qed.
Lemma lem1863624 (P : type1626) (h1 : term4 P) : term6 P.
Proof. exact (fun h0 : term5 P => @lem1863623 P h1 h0). Qed.
Lemma lem1863625 (P : type1626) (h1 : term5 P) : term5 P.
Proof. exact (h1). Qed.
Lemma lem1863626 (P : type1626) (h1 : term4 P) (h2 : term5 P) : term4 P.
Proof. exact (@lem1863624 P h1 (@lem1863625 P h2)). Qed.
Lemma lem1863627 (P : type1626) (h1 : term5 P) : term5 P.
Proof. exact (fun h0 : term4 P => @lem1863626 P h0 h1). Qed.
Lemma lem1863628 (P : type1626) : term7 P.
Proof. exact (fun h0 : term5 P => @lem1863627 P h0). Qed.
Lemma lem1863631 (P : type1626) : term5 P.
Proof. exact (@lem1863628 P (@lem1863620 P)). Qed.
Lemma lem1863669 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1863670 : term8 = term9.
Proof. exact (@lem1863669 term10). Qed.
Lemma lem1863725 (P : type1626) : (term11 P) = (term11 P).
Proof. exact (eq_refl (term11 P)). Qed.
Lemma lem1863726 (P : type1626) : (term4 P) = (term12 P).
Proof. exact (MK_COMB (@lem1863725 P) (@lem1863670)). Qed.
Lemma lem1863729 : term13 = term14.
Proof. exact (fun_ext (fun P : type1626 => @lem1863726 P)). Qed.
Lemma lem1863730 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem1863739 : term15 = term16.
Proof. exact (MK_COMB (@lem1863730) (@lem1863729)). Qed.
Lemma lem1863744 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1863745 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1863744 y x)). Qed.
Lemma lem1863746 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863747 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1863746) (@lem1863745 x)). Qed.
Lemma lem1863748 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1863747 x)). Qed.
Lemma lem1863749 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863750 : term10 = term10.
Proof. exact (MK_COMB (@lem1863749) (@lem1863748)). Qed.
Lemma lem1863751 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1863752 : term9 = term9.
Proof. exact (MK_COMB (@lem1863751) (@lem1863750)). Qed.
Lemma lem1863753 (P : type1626) (x : real) (y : real) : (P x y) = (P x y).
Proof. exact (eq_refl (P x y)). Qed.
Lemma lem1863754 (P : type1626) (x : real) : (term21 P x) = (term21 P x).
Proof. exact (fun_ext (fun y : real => @lem1863753 P x y)). Qed.
Lemma lem1863755 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863756 (P : type1626) (x : real) : (term22 P x) = (term22 P x).
Proof. exact (MK_COMB (@lem1863755) (@lem1863754 P x)). Qed.
Lemma lem1863757 (P : type1626) : (term23 P) = (term23 P).
Proof. exact (fun_ext (fun x : real => @lem1863756 P x)). Qed.
Lemma lem1863758 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863759 (P : type1626) : (term24 P) = (term24 P).
Proof. exact (MK_COMB (@lem1863758) (@lem1863757 P)). Qed.
Lemma lem1863764 (P : type1626) (x : real) (y : real) : (term25 P x y) = (term25 P x y).
Proof. exact (eq_refl (term25 P x y)). Qed.
Lemma lem1863765 (P : type1626) (x : real) : (term26 P x) = (term26 P x).
Proof. exact (fun_ext (fun y : real => @lem1863764 P x y)). Qed.
Lemma lem1863766 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863767 (P : type1626) (x : real) : (term27 P x) = (term27 P x).
Proof. exact (MK_COMB (@lem1863766) (@lem1863765 P x)). Qed.
Lemma lem1863768 (P : type1626) : (term28 P) = (term28 P).
Proof. exact (fun_ext (fun x : real => @lem1863767 P x)). Qed.
Lemma lem1863769 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863770 (P : type1626) : (term29 P) = (term29 P).
Proof. exact (MK_COMB (@lem1863769) (@lem1863768 P)). Qed.
Lemma lem1863775 (P : type1626) (y : real) (x : real) : ((P x y) = (P y x)) = ((P x y) = (P y x)).
Proof. exact (eq_refl ((P x y) = (P y x))). Qed.
Lemma lem1863776 (P : type1626) (x : real) : (term30 P x) = (term30 P x).
Proof. exact (fun_ext (fun y : real => @lem1863775 P y x)). Qed.
Lemma lem1863777 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863778 (P : type1626) (x : real) : (term31 P x) = (term31 P x).
Proof. exact (MK_COMB (@lem1863777) (@lem1863776 P x)). Qed.
Lemma lem1863779 (P : type1626) : (term32 P) = (term32 P).
Proof. exact (fun_ext (fun x : real => @lem1863778 P x)). Qed.
Lemma lem1863780 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863781 (P : type1626) : (term33 P) = (term33 P).
Proof. exact (MK_COMB (@lem1863780) (@lem1863779 P)). Qed.
Lemma lem1863782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1863783 (P : type1626) : (term34 P) = (term34 P).
Proof. exact (MK_COMB (@lem1863782) (@lem1863781 P)). Qed.
Lemma lem1863784 (P : type1626) : (term35 P) = (term35 P).
Proof. exact (MK_COMB (@lem1863783 P) (@lem1863770 P)). Qed.
Lemma lem1863785 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1863786 (P : type1626) : (term36 P) = (term36 P).
Proof. exact (MK_COMB (@lem1863785) (@lem1863784 P)). Qed.
Lemma lem1863787 (P : type1626) : (term1 P) = (term1 P).
Proof. exact (MK_COMB (@lem1863786 P) (@lem1863759 P)). Qed.
Lemma lem1863788 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1863789 (P : type1626) : (term3 P) = (term3 P).
Proof. exact (MK_COMB (@lem1863788) (@lem1863787 P)). Qed.
Lemma lem1863790 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1863791 (P : type1626) : (term11 P) = (term11 P).
Proof. exact (MK_COMB (@lem1863790) (@lem1863789 P)). Qed.
Lemma lem1863792 (P : type1626) : (term12 P) = (term12 P).
Proof. exact (MK_COMB (@lem1863791 P) (@lem1863752)). Qed.
Lemma lem1863793 : term14 = term14.
Proof. exact (fun_ext (fun P : type1626 => @lem1863792 P)). Qed.
Lemma lem1863794 : (@all (real -> real -> Prop)) = (@all (real -> real -> Prop)).
Proof. exact (eq_refl (@all (real -> real -> Prop))). Qed.
Lemma lem1863795 : term16 = term16.
Proof. exact (MK_COMB (@lem1863794) (@lem1863793)). Qed.
Lemma lem1863862 : term15 = term16.
Proof. exact (TRANS (@lem1863739) (@lem1863795)). Qed.
Lemma lem1863863 : term16 = term15.
Proof. exact (SYM (@lem1863862)). Qed.
Lemma lem1863864 (P : type1626) (h1 : term3 P) : term3 P.
Proof. exact (h1). Qed.
Lemma lem1863865 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem1863880 (P : type1626) (y : real) (x : real) : ((P x y) = (P y x)) = (term37 P y x).
Proof. exact (@lem17784 (P x y) (P y x)). Qed.
Lemma lem1863881 (P : type1626) (x : real) : (term30 P x) = (term38 P x).
Proof. exact (fun_ext (fun y : real => @lem1863880 P y x)). Qed.
Lemma lem1863882 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863883 (P : type1626) (x : real) : (term31 P x) = (term39 P x).
Proof. exact (MK_COMB (@lem1863882) (@lem1863881 P x)). Qed.
Lemma lem1863884 (P : type1626) : (term32 P) = (term40 P).
Proof. exact (fun_ext (fun x : real => @lem1863883 P x)). Qed.
Lemma lem1863885 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863886 (P : type1626) : (term33 P) = (term41 P).
Proof. exact (MK_COMB (@lem1863885) (@lem1863884 P)). Qed.
Lemma lem1863893 (P : type1626) (x : real) (y : real) : (term25 P x y) = (term42 P x y).
Proof. exact (@lem17265 (real_le x y) (P x y)). Qed.
Lemma lem1863894 (P : type1626) (x : real) : (term26 P x) = (term43 P x).
Proof. exact (fun_ext (fun y : real => @lem1863893 P x y)). Qed.
Lemma lem1863895 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863896 (P : type1626) (x : real) : (term27 P x) = (term44 P x).
Proof. exact (MK_COMB (@lem1863895) (@lem1863894 P x)). Qed.
Lemma lem1863897 (P : type1626) : (term28 P) = (term45 P).
Proof. exact (fun_ext (fun x : real => @lem1863896 P x)). Qed.
Lemma lem1863898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863899 (P : type1626) : (term29 P) = (term46 P).
Proof. exact (MK_COMB (@lem1863898) (@lem1863897 P)). Qed.
Lemma lem1863900 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1863901 (P : type1626) : (term34 P) = (term47 P).
Proof. exact (MK_COMB (@lem1863900) (@lem1863886 P)). Qed.
Lemma lem1863902 (P : type1626) : (term35 P) = (term48 P).
Proof. exact (MK_COMB (@lem1863901 P) (@lem1863899 P)). Qed.
Lemma lem1863904 (P : real -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1863905 (P : type1626) (x : real) : (term51 P x) = (term52 P x).
Proof. exact (@lem1863904 (term21 P x)). Qed.
Lemma lem1863906 (P : type1626) (x : real) (y : real) : (term53 P x y) = (P x y).
Proof. exact (eq_refl (term53 P x y)). Qed.
Lemma lem1863907 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1863909 (P : type1626) (x : real) (y : real) : (term54 P x y) = (term55 P x y).
Proof. exact (MK_COMB (@lem1863907) (@lem1863906 P x y)). Qed.
Lemma lem1863910 (P : type1626) (x : real) : (term56 P x) = (term57 P x).
Proof. exact (fun_ext (fun y : real => @lem1863909 P x y)). Qed.
Lemma lem1863911 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1863912 (P : type1626) (x : real) : (term52 P x) = (term58 P x).
Proof. exact (MK_COMB (@lem1863911) (@lem1863910 P x)). Qed.
Lemma lem1863913 (P : type1626) (x : real) : (term51 P x) = (term58 P x).
Proof. exact (TRANS (@lem1863905 P x) (@lem1863912 P x)). Qed.
Lemma lem1863914 (P : real -> Prop) : (term49 P) = (term50 P).
Proof. exact (@lem18392 real P). Qed.
Lemma lem1863915 (P : type1626) : (term59 P) = (term60 P).
Proof. exact (@lem1863914 (term23 P)). Qed.
Lemma lem1863916 (P : type1626) (x : real) : (term61 P x) = (term22 P x).
Proof. exact (eq_refl (term61 P x)). Qed.
Lemma lem1863917 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1863918 (P : type1626) (x : real) : (term62 P x) = (term51 P x).
Proof. exact (MK_COMB (@lem1863917) (@lem1863916 P x)). Qed.
Lemma lem1863919 (P : type1626) (x : real) : (term62 P x) = (term58 P x).
Proof. exact (TRANS (@lem1863918 P x) (@lem1863913 P x)). Qed.
Lemma lem1863920 (P : type1626) : (term63 P) = (term64 P).
Proof. exact (fun_ext (fun x : real => @lem1863919 P x)). Qed.
Lemma lem1863921 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1863922 (P : type1626) : (term60 P) = (term65 P).
Proof. exact (MK_COMB (@lem1863921) (@lem1863920 P)). Qed.
Lemma lem1863923 (P : type1626) : (term59 P) = (term65 P).
Proof. exact (TRANS (@lem1863915 P) (@lem1863922 P)). Qed.
Lemma lem1863924 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1863925 (P : type1626) : (term66 P) = (term67 P).
Proof. exact (MK_COMB (@lem1863924) (@lem1863902 P)). Qed.
Lemma lem1863926 (P : type1626) : (term68 P) = (term69 P).
Proof. exact (MK_COMB (@lem1863925 P) (@lem1863923 P)). Qed.
Lemma lem1863927 (P : type1626) : (term3 P) = (term68 P).
Proof. exact (@lem17362 (term35 P) (term24 P)). Qed.
Lemma lem1863928 (P : type1626) : (term3 P) = (term69 P).
Proof. exact (TRANS (@lem1863927 P) (@lem1863926 P)). Qed.
Lemma lem1863934 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1863935 (P : real -> Prop) (Q : real -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem1863934 real P Q). Qed.
Lemma lem1863936 (P : type1626) (x : real) : (term74 P x) = (term75 P x).
Proof. exact (@lem1863935 (term76 P x) (term77 P x)). Qed.
Lemma lem1863937 (P : type1626) (y : real) (x : real) : (term78 P x y) = (term79 P y x).
Proof. exact (eq_refl (term78 P x y)). Qed.
Lemma lem1863938 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1863939 (P : type1626) (y : real) (x : real) : (term80 P x y) = (term81 P y x).
Proof. exact (MK_COMB (@lem1863938) (@lem1863937 P y x)). Qed.
Lemma lem1863940 (P : type1626) (y : real) (x : real) : (term82 P x y) = (term83 P y x).
Proof. exact (eq_refl (term82 P x y)). Qed.
Lemma lem1863941 (P : type1626) (y : real) (x : real) : (term84 P x y) = (term37 P y x).
Proof. exact (MK_COMB (@lem1863939 P y x) (@lem1863940 P y x)). Qed.
Lemma lem1863942 (P : type1626) (x : real) : (term85 P x) = (term38 P x).
Proof. exact (fun_ext (fun y : real => @lem1863941 P y x)). Qed.
Lemma lem1863943 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863944 (P : type1626) (x : real) : (term74 P x) = (term39 P x).
Proof. exact (MK_COMB (@lem1863943) (@lem1863942 P x)). Qed.
Lemma lem1863945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1863946 (P : type1626) (x : real) : (term86 P x) = (term87 P x).
Proof. exact (MK_COMB (@lem1863945) (@lem1863944 P x)). Qed.
Lemma lem1863947 (P : type1626) (y : real) (x : real) : (term78 P x y) = (term79 P y x).
Proof. exact (eq_refl (term78 P x y)). Qed.
Lemma lem1863948 (P : type1626) (x : real) : (term88 P x) = (term76 P x).
Proof. exact (fun_ext (fun y : real => @lem1863947 P y x)). Qed.
Lemma lem1863949 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863950 (P : type1626) (x : real) : (term89 P x) = (term90 P x).
Proof. exact (MK_COMB (@lem1863949) (@lem1863948 P x)). Qed.
Lemma lem1863951 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1863952 (P : type1626) (x : real) : (term91 P x) = (term92 P x).
Proof. exact (MK_COMB (@lem1863951) (@lem1863950 P x)). Qed.
Lemma lem1863953 (P : type1626) (y : real) (x : real) : (term82 P x y) = (term83 P y x).
Proof. exact (eq_refl (term82 P x y)). Qed.
Lemma lem1863954 (P : type1626) (x : real) : (term93 P x) = (term77 P x).
Proof. exact (fun_ext (fun y : real => @lem1863953 P y x)). Qed.
Lemma lem1863955 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1863956 (P : type1626) (x : real) : (term94 P x) = (term95 P x).
Proof. exact (MK_COMB (@lem1863955) (@lem1863954 P x)). Qed.
Lemma lem1863957 (P : type1626) (x : real) : (term75 P x) = (term96 P x).
Proof. exact (MK_COMB (@lem1863952 P x) (@lem1863956 P x)). Qed.
Lemma lem1863958 (P : type1626) (x : real) : ((term74 P x) = (term75 P x)) = ((term39 P x) = (term96 P x)).
Proof. exact (MK_COMB (@lem1863946 P x) (@lem1863957 P x)). Qed.
Lemma lem1863959 (P : type1626) (x : real) : (term39 P x) = (term96 P x).
Proof. exact (EQ_MP (@lem1863958 P x) (@lem1863936 P x)). Qed.
Lemma lem1864056 (P : type1626) : (term40 P) = (term97 P).
Proof. exact (fun_ext (fun x : real => @lem1863959 P x)). Qed.
Lemma lem1864057 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864058 (P : type1626) : (term41 P) = (term98 P).
Proof. exact (MK_COMB (@lem1864057) (@lem1864056 P)). Qed.
Lemma lem1864060 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term70 A P Q) = (term71 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem1864061 (P : real -> Prop) (Q : real -> Prop) : (term72 P Q) = (term73 P Q).
Proof. exact (@lem1864060 real P Q). Qed.
Lemma lem1864062 (P : type1626) : (term99 P) = (term100 P).
Proof. exact (@lem1864061 (term101 P) (term102 P)). Qed.
Lemma lem1864063 (P : type1626) (x : real) : (term103 P x) = (term90 P x).
Proof. exact (eq_refl (term103 P x)). Qed.
Lemma lem1864064 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1864065 (P : type1626) (x : real) : (term104 P x) = (term92 P x).
Proof. exact (MK_COMB (@lem1864064) (@lem1864063 P x)). Qed.
Lemma lem1864066 (P : type1626) (x : real) : (term105 P x) = (term95 P x).
Proof. exact (eq_refl (term105 P x)). Qed.
Lemma lem1864067 (P : type1626) (x : real) : (term106 P x) = (term96 P x).
Proof. exact (MK_COMB (@lem1864065 P x) (@lem1864066 P x)). Qed.
Lemma lem1864068 (P : type1626) : (term107 P) = (term97 P).
Proof. exact (fun_ext (fun x : real => @lem1864067 P x)). Qed.
Lemma lem1864069 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864070 (P : type1626) : (term99 P) = (term98 P).
Proof. exact (MK_COMB (@lem1864069) (@lem1864068 P)). Qed.
Lemma lem1864071 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1864072 (P : type1626) : (term108 P) = (term109 P).
Proof. exact (MK_COMB (@lem1864071) (@lem1864070 P)). Qed.
Lemma lem1864073 (P : type1626) (x : real) : (term103 P x) = (term90 P x).
Proof. exact (eq_refl (term103 P x)). Qed.
Lemma lem1864074 (P : type1626) : (term110 P) = (term101 P).
Proof. exact (fun_ext (fun x : real => @lem1864073 P x)). Qed.
Lemma lem1864075 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864076 (P : type1626) : (term111 P) = (term112 P).
Proof. exact (MK_COMB (@lem1864075) (@lem1864074 P)). Qed.
Lemma lem1864077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1864078 (P : type1626) : (term113 P) = (term114 P).
Proof. exact (MK_COMB (@lem1864077) (@lem1864076 P)). Qed.
Lemma lem1864079 (P : type1626) (x : real) : (term105 P x) = (term95 P x).
Proof. exact (eq_refl (term105 P x)). Qed.
Lemma lem1864080 (P : type1626) : (term115 P) = (term102 P).
Proof. exact (fun_ext (fun x : real => @lem1864079 P x)). Qed.
Lemma lem1864081 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864082 (P : type1626) : (term116 P) = (term117 P).
Proof. exact (MK_COMB (@lem1864081) (@lem1864080 P)). Qed.
Lemma lem1864083 (P : type1626) : (term100 P) = (term118 P).
Proof. exact (MK_COMB (@lem1864078 P) (@lem1864082 P)). Qed.
Lemma lem1864084 (P : type1626) : ((term99 P) = (term100 P)) = ((term98 P) = (term118 P)).
Proof. exact (MK_COMB (@lem1864072 P) (@lem1864083 P)). Qed.
Lemma lem1864085 (P : type1626) : (term98 P) = (term118 P).
Proof. exact (EQ_MP (@lem1864084 P) (@lem1864062 P)). Qed.
Lemma lem1864190 (P : type1626) : (term41 P) = (term118 P).
Proof. exact (TRANS (@lem1864058 P) (@lem1864085 P)). Qed.
Lemma lem1864191 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1864192 (P : type1626) : (term47 P) = (term119 P).
Proof. exact (MK_COMB (@lem1864191) (@lem1864190 P)). Qed.
Lemma lem1864245 (P : type1626) : (term46 P) = (term46 P).
Proof. exact (eq_refl (term46 P)). Qed.
Lemma lem1864246 (P : type1626) : (term48 P) = (term120 P).
Proof. exact (MK_COMB (@lem1864192 P) (@lem1864245 P)). Qed.
Lemma lem1864247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1864248 (P : type1626) : (term67 P) = (term121 P).
Proof. exact (MK_COMB (@lem1864247) (@lem1864246 P)). Qed.
Lemma lem1864257 (P : type1626) : (term65 P) = (term65 P).
Proof. exact (eq_refl (term65 P)). Qed.
Lemma lem1864258 (P : type1626) : (term69 P) = (term122 P).
Proof. exact (MK_COMB (@lem1864248 P) (@lem1864257 P)). Qed.
Lemma lem1864260 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1864261 (P : Prop) (Q : real -> Prop) : (term125 P Q) = (term126 P Q).
Proof. exact (@lem1864260 real P Q). Qed.
Lemma lem1864262 (P : type1626) : (term127 P) = (term128 P).
Proof. exact (@lem1864261 (term120 P) (term64 P)). Qed.
Lemma lem1864263 (P : type1626) (x : real) : (term129 P x) = (term58 P x).
Proof. exact (eq_refl (term129 P x)). Qed.
Lemma lem1864264 (P : type1626) : (term130 P) = (term64 P).
Proof. exact (fun_ext (fun x : real => @lem1864263 P x)). Qed.
Lemma lem1864265 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1864266 (P : type1626) : (term131 P) = (term65 P).
Proof. exact (MK_COMB (@lem1864265) (@lem1864264 P)). Qed.
Lemma lem1864267 (P : type1626) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1864268 (P : type1626) : (term127 P) = (term122 P).
Proof. exact (MK_COMB (@lem1864267 P) (@lem1864266 P)). Qed.
Lemma lem1864269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1864270 (P : type1626) : (term132 P) = (term133 P).
Proof. exact (MK_COMB (@lem1864269) (@lem1864268 P)). Qed.
Lemma lem1864271 (P : type1626) (x : real) : (term129 P x) = (term58 P x).
Proof. exact (eq_refl (term129 P x)). Qed.
Lemma lem1864272 (P : type1626) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1864273 (P : type1626) (x : real) : (term134 P x) = (term135 P x).
Proof. exact (MK_COMB (@lem1864272 P) (@lem1864271 P x)). Qed.
Lemma lem1864274 (P : type1626) : (term136 P) = (term137 P).
Proof. exact (fun_ext (fun x : real => @lem1864273 P x)). Qed.
Lemma lem1864275 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1864276 (P : type1626) : (term128 P) = (term138 P).
Proof. exact (MK_COMB (@lem1864275) (@lem1864274 P)). Qed.
Lemma lem1864277 (P : type1626) : ((term127 P) = (term128 P)) = ((term122 P) = (term138 P)).
Proof. exact (MK_COMB (@lem1864270 P) (@lem1864276 P)). Qed.
Lemma lem1864278 (P : type1626) : (term122 P) = (term138 P).
Proof. exact (EQ_MP (@lem1864277 P) (@lem1864262 P)). Qed.
Lemma lem1864280 {A : Type'} (P : Prop) (Q : A -> Prop) : (term123 A P Q) = (term124 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem1864281 (P : Prop) (Q : real -> Prop) : (term125 P Q) = (term126 P Q).
Proof. exact (@lem1864280 real P Q). Qed.
Lemma lem1864282 (P : type1626) (x : real) : (term139 P x) = (term140 P x).
Proof. exact (@lem1864281 (term120 P) (term57 P x)). Qed.
Lemma lem1864283 (P : type1626) (x : real) (y : real) : (term141 P x y) = (term55 P x y).
Proof. exact (eq_refl (term141 P x y)). Qed.
Lemma lem1864284 (P : type1626) (x : real) : (term142 P x) = (term57 P x).
Proof. exact (fun_ext (fun y : real => @lem1864283 P x y)). Qed.
Lemma lem1864285 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1864286 (P : type1626) (x : real) : (term143 P x) = (term58 P x).
Proof. exact (MK_COMB (@lem1864285) (@lem1864284 P x)). Qed.
Lemma lem1864287 (P : type1626) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1864288 (P : type1626) (x : real) : (term139 P x) = (term135 P x).
Proof. exact (MK_COMB (@lem1864287 P) (@lem1864286 P x)). Qed.
Lemma lem1864289 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1864290 (P : type1626) (x : real) : (term144 P x) = (term145 P x).
Proof. exact (MK_COMB (@lem1864289) (@lem1864288 P x)). Qed.
Lemma lem1864291 (P : type1626) (x : real) (y : real) : (term141 P x y) = (term55 P x y).
Proof. exact (eq_refl (term141 P x y)). Qed.
Lemma lem1864292 (P : type1626) : (term121 P) = (term121 P).
Proof. exact (eq_refl (term121 P)). Qed.
Lemma lem1864293 (P : type1626) (x : real) (y : real) : (term146 P x y) = (term147 P x y).
Proof. exact (MK_COMB (@lem1864292 P) (@lem1864291 P x y)). Qed.
Lemma lem1864294 (P : type1626) (x : real) : (term148 P x) = (term149 P x).
Proof. exact (fun_ext (fun y : real => @lem1864293 P x y)). Qed.
Lemma lem1864295 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1864296 (P : type1626) (x : real) : (term140 P x) = (term150 P x).
Proof. exact (MK_COMB (@lem1864295) (@lem1864294 P x)). Qed.
Lemma lem1864297 (P : type1626) (x : real) : ((term139 P x) = (term140 P x)) = ((term135 P x) = (term150 P x)).
Proof. exact (MK_COMB (@lem1864290 P x) (@lem1864296 P x)). Qed.
Lemma lem1864298 (P : type1626) (x : real) : (term135 P x) = (term150 P x).
Proof. exact (EQ_MP (@lem1864297 P x) (@lem1864282 P x)). Qed.
Lemma lem1864299 (P : type1626) : (term137 P) = (term151 P).
Proof. exact (fun_ext (fun x : real => @lem1864298 P x)). Qed.
Lemma lem1864300 : (@ex real) = (@ex real).
Proof. exact (eq_refl (@ex real)). Qed.
Lemma lem1864301 (P : type1626) : (term138 P) = (term152 P).
Proof. exact (MK_COMB (@lem1864300) (@lem1864299 P)). Qed.
Lemma lem1864302 (P : type1626) : (term122 P) = (term152 P).
Proof. exact (TRANS (@lem1864278 P) (@lem1864301 P)). Qed.
Lemma lem1864303 (P : type1626) : (term69 P) = (term152 P).
Proof. exact (TRANS (@lem1864258 P) (@lem1864302 P)). Qed.
Lemma lem1864304 (P : type1626) : (term3 P) = (term152 P).
Proof. exact (TRANS (@lem1863928 P) (@lem1864303 P)). Qed.
Lemma lem1864305 (P : type1626) (h1 : term3 P) : term152 P.
Proof. exact (EQ_MP (@lem1864304 P) (@lem1863864 P h1)). Qed.
Lemma lem1864310 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1864311 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1864310 y x)). Qed.
Lemma lem1864312 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864313 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1864312) (@lem1864311 x)). Qed.
Lemma lem1864314 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1864313 x)). Qed.
Lemma lem1864315 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864372 : term10 = term10.
Proof. exact (MK_COMB (@lem1864315) (@lem1864314)). Qed.
Lemma lem1864373 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1864372) (@lem1863865 h1)). Qed.
Lemma lem1864374 (P : type1626) (x : real) (h1 : term150 P x) : term150 P x.
Proof. exact (h1). Qed.
Lemma lem1864375 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term147 P x y.
Proof. exact (h1). Qed.
Lemma lem1864388 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1864389 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1864388 y x)). Qed.
Lemma lem1864390 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864391 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1864390) (@lem1864389 x)). Qed.
Lemma lem1864392 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1864391 x)). Qed.
Lemma lem1864393 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864394 : term10 = term10.
Proof. exact (MK_COMB (@lem1864393) (@lem1864392)). Qed.
Lemma lem1864395 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1864394) (@lem1864373 h1)). Qed.
Lemma lem1864402 (P : type1626) (x : real) (y : real) : (term55 P x y) = (term55 P x y).
Proof. exact (eq_refl (term55 P x y)). Qed.
Lemma lem1864417 (P : type1626) (x : real) (y : real) : (term42 P x y) = (term42 P x y).
Proof. exact (eq_refl (term42 P x y)). Qed.
Lemma lem1864418 (P : type1626) (x : real) : (term43 P x) = (term43 P x).
Proof. exact (fun_ext (fun y : real => @lem1864417 P x y)). Qed.
Lemma lem1864419 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864420 (P : type1626) (x : real) : (term44 P x) = (term44 P x).
Proof. exact (MK_COMB (@lem1864419) (@lem1864418 P x)). Qed.
Lemma lem1864421 (P : type1626) : (term45 P) = (term45 P).
Proof. exact (fun_ext (fun x : real => @lem1864420 P x)). Qed.
Lemma lem1864422 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864423 (P : type1626) : (term46 P) = (term46 P).
Proof. exact (MK_COMB (@lem1864422) (@lem1864421 P)). Qed.
Lemma lem1864438 (P : type1626) (y : real) (x : real) : (term83 P y x) = (term83 P y x).
Proof. exact (eq_refl (term83 P y x)). Qed.
Lemma lem1864439 (P : type1626) (x : real) : (term77 P x) = (term77 P x).
Proof. exact (fun_ext (fun y : real => @lem1864438 P y x)). Qed.
Lemma lem1864440 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864441 (P : type1626) (x : real) : (term95 P x) = (term95 P x).
Proof. exact (MK_COMB (@lem1864440) (@lem1864439 P x)). Qed.
Lemma lem1864442 (P : type1626) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun x : real => @lem1864441 P x)). Qed.
Lemma lem1864443 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864444 (P : type1626) : (term117 P) = (term117 P).
Proof. exact (MK_COMB (@lem1864443) (@lem1864442 P)). Qed.
Lemma lem1864459 (P : type1626) (y : real) (x : real) : (term79 P y x) = (term79 P y x).
Proof. exact (eq_refl (term79 P y x)). Qed.
Lemma lem1864460 (P : type1626) (x : real) : (term76 P x) = (term76 P x).
Proof. exact (fun_ext (fun y : real => @lem1864459 P y x)). Qed.
Lemma lem1864461 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864462 (P : type1626) (x : real) : (term90 P x) = (term90 P x).
Proof. exact (MK_COMB (@lem1864461) (@lem1864460 P x)). Qed.
Lemma lem1864463 (P : type1626) : (term101 P) = (term101 P).
Proof. exact (fun_ext (fun x : real => @lem1864462 P x)). Qed.
Lemma lem1864464 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864465 (P : type1626) : (term112 P) = (term112 P).
Proof. exact (MK_COMB (@lem1864464) (@lem1864463 P)). Qed.
Lemma lem1864466 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1864467 (P : type1626) : (term114 P) = (term114 P).
Proof. exact (MK_COMB (@lem1864466) (@lem1864465 P)). Qed.
Lemma lem1864468 (P : type1626) : (term118 P) = (term118 P).
Proof. exact (MK_COMB (@lem1864467 P) (@lem1864444 P)). Qed.
Lemma lem1864469 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1864470 (P : type1626) : (term119 P) = (term119 P).
Proof. exact (MK_COMB (@lem1864469) (@lem1864468 P)). Qed.
Lemma lem1864471 (P : type1626) : (term120 P) = (term120 P).
Proof. exact (MK_COMB (@lem1864470 P) (@lem1864423 P)). Qed.
Lemma lem1864472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1864473 (P : type1626) : (term121 P) = (term121 P).
Proof. exact (MK_COMB (@lem1864472) (@lem1864471 P)). Qed.
Lemma lem1864474 (P : type1626) (x : real) (y : real) : (term147 P x y) = (term147 P x y).
Proof. exact (MK_COMB (@lem1864473 P) (@lem1864402 P x y)). Qed.
Lemma lem1864475 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term147 P x y.
Proof. exact (EQ_MP (@lem1864474 P x y) (@lem1864375 P x y h1)). Qed.
Lemma lem1864477 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term120 P.
Proof. exact (proj1 (@lem1864475 P x y h1)). Qed.
Lemma lem1864478 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term46 P.
Proof. exact (proj2 (@lem1864477 P x y h1)). Qed.
Lemma lem1864479 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term118 P.
Proof. exact (proj1 (@lem1864477 P x y h1)). Qed.
Lemma lem1864480 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term117 P.
Proof. exact (proj2 (@lem1864479 P x y h1)). Qed.
Lemma lem1864489 (y : real) (x : real) : (term17 y x) = (term17 y x).
Proof. exact (eq_refl (term17 y x)). Qed.
Lemma lem1864490 (x : real) : (term18 x) = (term18 x).
Proof. exact (fun_ext (fun y : real => @lem1864489 y x)). Qed.
Lemma lem1864491 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864492 (x : real) : (term19 x) = (term19 x).
Proof. exact (MK_COMB (@lem1864491) (@lem1864490 x)). Qed.
Lemma lem1864493 : term20 = term20.
Proof. exact (fun_ext (fun x : real => @lem1864492 x)). Qed.
Lemma lem1864494 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864496 : term10 = term10.
Proof. exact (MK_COMB (@lem1864494) (@lem1864493)). Qed.
Lemma lem1864497 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem1864496) (@lem1864395 h1)). Qed.
Lemma lem1864509 (P : type1626) (x : real) (y : real) : (term42 P x y) = (term42 P x y).
Proof. exact (eq_refl (term42 P x y)). Qed.
Lemma lem1864510 (P : type1626) (x : real) : (term43 P x) = (term43 P x).
Proof. exact (fun_ext (fun y : real => @lem1864509 P x y)). Qed.
Lemma lem1864511 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864512 (P : type1626) (x : real) : (term44 P x) = (term44 P x).
Proof. exact (MK_COMB (@lem1864511) (@lem1864510 P x)). Qed.
Lemma lem1864513 (P : type1626) : (term45 P) = (term45 P).
Proof. exact (fun_ext (fun x : real => @lem1864512 P x)). Qed.
Lemma lem1864514 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864516 (P : type1626) : (term46 P) = (term46 P).
Proof. exact (MK_COMB (@lem1864514) (@lem1864513 P)). Qed.
Lemma lem1864517 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term46 P.
Proof. exact (EQ_MP (@lem1864516 P) (@lem1864478 P x y h1)). Qed.
Lemma lem1864541 (P : type1626) (y : real) (x : real) : (term83 P y x) = (term83 P y x).
Proof. exact (eq_refl (term83 P y x)). Qed.
Lemma lem1864542 (P : type1626) (x : real) : (term77 P x) = (term77 P x).
Proof. exact (fun_ext (fun y : real => @lem1864541 P y x)). Qed.
Lemma lem1864543 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864544 (P : type1626) (x : real) : (term95 P x) = (term95 P x).
Proof. exact (MK_COMB (@lem1864543) (@lem1864542 P x)). Qed.
Lemma lem1864545 (P : type1626) : (term102 P) = (term102 P).
Proof. exact (fun_ext (fun x : real => @lem1864544 P x)). Qed.
Lemma lem1864546 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1864548 (P : type1626) : (term117 P) = (term117 P).
Proof. exact (MK_COMB (@lem1864546) (@lem1864545 P)). Qed.
Lemma lem1864549 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term117 P.
Proof. exact (EQ_MP (@lem1864548 P) (@lem1864480 P x y h1)). Qed.
Lemma lem1864550 (_26989 : real) (h1 : term10) : term153 _26989.
Proof. exact (@lem1864497 h1 _26989). Qed.
Lemma lem1864551 (_26989 : real) : (term153 _26989) = (term19 _26989).
Proof. exact (eq_refl (term153 _26989)). Qed.
Lemma lem1864552 (_26989 : real) (h1 : term10) : term19 _26989.
Proof. exact (EQ_MP (@lem1864551 _26989) (@lem1864550 _26989 h1)). Qed.
Lemma lem1864553 (_26989 : real) (_26990 : real) (h1 : term10) : term154 _26989 _26990.
Proof. exact (@lem1864552 _26989 h1 _26990). Qed.
Lemma lem1864554 (_26990 : real) (_26989 : real) : (term154 _26989 _26990) = (term17 _26990 _26989).
Proof. exact (eq_refl (term154 _26989 _26990)). Qed.
Lemma lem1864556 (_26991 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term155 P _26991.
Proof. exact (@lem1864517 P x y h1 _26991). Qed.
Lemma lem1864557 (P : type1626) (_26991 : real) : (term155 P _26991) = (term44 P _26991).
Proof. exact (eq_refl (term155 P _26991)). Qed.
Lemma lem1864558 (_26991 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term44 P _26991.
Proof. exact (EQ_MP (@lem1864557 P _26991) (@lem1864556 _26991 P x y h1)). Qed.
Lemma lem1864559 (_26991 : real) (_26992 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term156 P _26991 _26992.
Proof. exact (@lem1864558 _26991 P x y h1 _26992). Qed.
Lemma lem1864560 (P : type1626) (_26991 : real) (_26992 : real) : (term156 P _26991 _26992) = (term42 P _26991 _26992).
Proof. exact (eq_refl (term156 P _26991 _26992)). Qed.
Lemma lem1864568 (_26995 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term105 P _26995.
Proof. exact (@lem1864549 P x y h1 _26995). Qed.
Lemma lem1864569 (P : type1626) (_26995 : real) : (term105 P _26995) = (term95 P _26995).
Proof. exact (eq_refl (term105 P _26995)). Qed.
Lemma lem1864570 (_26995 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term95 P _26995.
Proof. exact (EQ_MP (@lem1864569 P _26995) (@lem1864568 _26995 P x y h1)). Qed.
Lemma lem1864571 (_26995 : real) (_26996 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term82 P _26995 _26996.
Proof. exact (@lem1864570 _26995 P x y h1 _26996). Qed.
Lemma lem1864572 (P : type1626) (_26996 : real) (_26995 : real) : (term82 P _26995 _26996) = (term83 P _26996 _26995).
Proof. exact (eq_refl (term82 P _26995 _26996)). Qed.
Lemma lem1864579 (_26990 : real) (_26989 : real) (h1 : term10) : term17 _26990 _26989.
Proof. exact (EQ_MP (@lem1864554 _26990 _26989) (@lem1864553 _26989 _26990 h1)). Qed.
Lemma lem1864581 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term55 P x y.
Proof. exact (proj2 (@lem1864475 P x y h1)). Qed.
Lemma lem1864587 (_26991 : real) (_26992 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term42 P _26991 _26992.
Proof. exact (EQ_MP (@lem1864560 P _26991 _26992) (@lem1864559 _26991 _26992 P x y h1)). Qed.
Lemma lem1864599 (_26996 : real) (_26995 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term83 P _26996 _26995.
Proof. exact (EQ_MP (@lem1864572 P _26996 _26995) (@lem1864571 _26995 _26996 P x y h1)). Qed.
Lemma lem1864602 (P : type1626) (x : real) (y : real) (h1 : term55 P x y) : term55 P x y.
Proof. exact (h1). Qed.
Lemma lem1864603 (P : type1626) (x : real) (y : real) (h1 : term55 P x y) : term157 P x y.
Proof. exact (fun h0 : P x y => @lem1864602 P x y h1). Qed.
Lemma lem1864605 (p : Prop) : (term158 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1864606 (P : type1626) (x : real) (y : real) : (term157 P x y) = (term55 P x y).
Proof. exact (@lem1864605 (P x y)). Qed.
Lemma lem1864607 (P : type1626) (x : real) (y : real) (h1 : term55 P x y) : term55 P x y.
Proof. exact (EQ_MP (@lem1864606 P x y) (@lem1864603 P x y h1)). Qed.
Lemma lem1864609 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1864612 (P : type1626) (_26991 : real) (_26992 : real) : (term42 P _26991 _26992) = (term160 P _26991 _26992).
Proof. exact (@lem1864609 (P _26991 _26992) (term161 _26991 _26992)). Qed.
Lemma lem1864615 (_26991 : real) (_26992 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term160 P _26991 _26992.
Proof. exact (EQ_MP (@lem1864612 P _26991 _26992) (@lem1864587 _26991 _26992 P x y h1)). Qed.
Lemma lem1864616 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term160 P x y.
Proof. exact (@lem1864615 x y P x y h1). Qed.
Lemma lem1864619 (P : type1626) (x : real) (y : real) (h1 : term55 P x y) (h2 : term147 P x y) : term161 x y.
Proof. exact (@lem1864616 P x y h2 (@lem1864607 P x y h1)). Qed.
Lemma lem1864620 (P : type1626) (x : real) (y : real) (h1 : term55 P x y) (h2 : term147 P x y) : term162 x y.
Proof. exact (fun h0 : real_le x y => @lem1864619 P x y h1 h2). Qed.
Lemma lem1864622 (p : Prop) : (term158 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem1864623 (x : real) (y : real) : (term162 x y) = (term161 x y).
Proof. exact (@lem1864622 (real_le x y)). Qed.
Lemma lem1864624 (P : type1626) (x : real) (y : real) (h1 : term55 P x y) (h2 : term147 P x y) : term161 x y.
Proof. exact (EQ_MP (@lem1864623 x y) (@lem1864620 P x y h1 h2)). Qed.
Lemma lem1864635 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1864636 (_26990 : real) (_26989 : real) : (term17 _26989 _26990) = (term17 _26990 _26989).
Proof. exact (@lem1864635 (real_le _26989 _26990) (real_le _26990 _26989)). Qed.
Lemma lem1864642 (_26990 : real) (_26989 : real) : (term163 _26990 _26989) = (term163 _26990 _26989).
Proof. exact (eq_refl (term163 _26990 _26989)). Qed.
Lemma lem1864643 (_26990 : real) (_26989 : real) : ((term17 _26990 _26989) = (term17 _26989 _26990)) = ((term17 _26990 _26989) = (term17 _26990 _26989)).
Proof. exact (MK_COMB (@lem1864642 _26990 _26989) (@lem1864636 _26990 _26989)). Qed.
Lemma lem1864645 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1864646 (x : Prop) : (x = x) = True.
Proof. exact (@lem1864645 Prop x). Qed.
Lemma lem1864647 (_26990 : real) (_26989 : real) : ((term17 _26990 _26989) = (term17 _26990 _26989)) = True.
Proof. exact (@lem1864646 (term17 _26990 _26989)). Qed.
Lemma lem1864648 (_26989 : real) (_26990 : real) : ((term17 _26990 _26989) = (term17 _26989 _26990)) = True.
Proof. exact (TRANS (@lem1864643 _26990 _26989) (@lem1864647 _26990 _26989)). Qed.
Lemma lem1864649 (_26989 : real) (_26990 : real) : True = ((term17 _26990 _26989) = (term17 _26989 _26990)).
Proof. exact (SYM (@lem1864648 _26989 _26990)). Qed.
Lemma lem1864650 (_26989 : real) (_26990 : real) : (term17 _26990 _26989) = (term17 _26989 _26990).
Proof. exact (EQ_MP (@lem1864649 _26989 _26990) (@lem0)). Qed.
Lemma lem1864651 (_26989 : real) (_26990 : real) (h1 : term10) : term17 _26989 _26990.
Proof. exact (EQ_MP (@lem1864650 _26989 _26990) (@lem1864579 _26990 _26989 h1)). Qed.
Lemma lem1864653 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1864656 (_26990 : real) (_26989 : real) : (term17 _26989 _26990) = (term164 _26990 _26989).
Proof. exact (@lem1864653 (real_le _26989 _26990) (real_le _26990 _26989)). Qed.
Lemma lem1864659 (_26990 : real) (_26989 : real) (h1 : term10) : term164 _26990 _26989.
Proof. exact (EQ_MP (@lem1864656 _26990 _26989) (@lem1864651 _26989 _26990 h1)). Qed.
Lemma lem1864660 (y : real) (x : real) (h1 : term10) : term164 y x.
Proof. exact (@lem1864659 y x h1). Qed.
Lemma lem1864663 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term55 P x y) (h3 : term147 P x y) : real_le y x.
Proof. exact (@lem1864660 y x h1 (@lem1864624 P x y h2 h3)). Qed.
Lemma lem1864664 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term55 P x y) (h3 : term147 P x y) : term165 y x.
Proof. exact (fun h0 : term161 y x => @lem1864663 P x y h1 h2 h3). Qed.
Lemma lem1864666 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1864667 (y : real) (x : real) : (term165 y x) = (real_le y x).
Proof. exact (@lem1864666 (real_le y x)). Qed.
Lemma lem1864668 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term55 P x y) (h3 : term147 P x y) : real_le y x.
Proof. exact (EQ_MP (@lem1864667 y x) (@lem1864664 P x y h1 h2 h3)). Qed.
Lemma lem1864674 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1864675 (P : type1626) (_26991 : real) (_26992 : real) : (term42 P _26991 _26992) = (term167 P _26991 _26992).
Proof. exact (@lem1864674 (P _26991 _26992) (term161 _26991 _26992)). Qed.
Lemma lem1864681 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1864682 (P : type1626) (_26991 : real) (_26992 : real) : (term168 P _26991 _26992) = (term169 P _26991 _26992).
Proof. exact (MK_COMB (@lem1864681) (@lem1864675 P _26991 _26992)). Qed.
Lemma lem1864688 (P : type1626) (_26991 : real) (_26992 : real) : (term167 P _26991 _26992) = (term167 P _26991 _26992).
Proof. exact (eq_refl (term167 P _26991 _26992)). Qed.
Lemma lem1864689 (P : type1626) (_26991 : real) (_26992 : real) : ((term42 P _26991 _26992) = (term167 P _26991 _26992)) = ((term167 P _26991 _26992) = (term167 P _26991 _26992)).
Proof. exact (MK_COMB (@lem1864682 P _26991 _26992) (@lem1864688 P _26991 _26992)). Qed.
Lemma lem1864691 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1864692 (x : Prop) : (x = x) = True.
Proof. exact (@lem1864691 Prop x). Qed.
Lemma lem1864693 (P : type1626) (_26991 : real) (_26992 : real) : ((term167 P _26991 _26992) = (term167 P _26991 _26992)) = True.
Proof. exact (@lem1864692 (term167 P _26991 _26992)). Qed.
Lemma lem1864694 (P : type1626) (_26991 : real) (_26992 : real) : ((term42 P _26991 _26992) = (term167 P _26991 _26992)) = True.
Proof. exact (TRANS (@lem1864689 P _26991 _26992) (@lem1864693 P _26991 _26992)). Qed.
Lemma lem1864695 (P : type1626) (_26991 : real) (_26992 : real) : True = ((term42 P _26991 _26992) = (term167 P _26991 _26992)).
Proof. exact (SYM (@lem1864694 P _26991 _26992)). Qed.
Lemma lem1864696 (P : type1626) (_26991 : real) (_26992 : real) : (term42 P _26991 _26992) = (term167 P _26991 _26992).
Proof. exact (EQ_MP (@lem1864695 P _26991 _26992) (@lem0)). Qed.
Lemma lem1864697 (_26991 : real) (_26992 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term167 P _26991 _26992.
Proof. exact (EQ_MP (@lem1864696 P _26991 _26992) (@lem1864587 _26991 _26992 P x y h1)). Qed.
Lemma lem1864699 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1864700 (P : type1626) (_26991 : real) (_26992 : real) : (term167 P _26991 _26992) = (term170 P _26991 _26992).
Proof. exact (@lem1864699 (term161 _26991 _26992) (P _26991 _26992)). Qed.
Lemma lem1864702 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1864703 (_26991 : real) (_26992 : real) : (term172 _26991 _26992) = (real_le _26991 _26992).
Proof. exact (@lem1864702 (real_le _26991 _26992)). Qed.
Lemma lem1864704 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1864705 (_26991 : real) (_26992 : real) : (term173 _26991 _26992) = (term174 _26991 _26992).
Proof. exact (MK_COMB (@lem1864704) (@lem1864703 _26991 _26992)). Qed.
Lemma lem1864706 (P : type1626) (_26991 : real) (_26992 : real) : (P _26991 _26992) = (P _26991 _26992).
Proof. exact (eq_refl (P _26991 _26992)). Qed.
Lemma lem1864707 (P : type1626) (_26991 : real) (_26992 : real) : (term170 P _26991 _26992) = (term25 P _26991 _26992).
Proof. exact (MK_COMB (@lem1864705 _26991 _26992) (@lem1864706 P _26991 _26992)). Qed.
Lemma lem1864708 (P : type1626) (_26991 : real) (_26992 : real) : (term167 P _26991 _26992) = (term25 P _26991 _26992).
Proof. exact (TRANS (@lem1864700 P _26991 _26992) (@lem1864707 P _26991 _26992)). Qed.
Lemma lem1864711 (_26991 : real) (_26992 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term25 P _26991 _26992.
Proof. exact (EQ_MP (@lem1864708 P _26991 _26992) (@lem1864697 _26991 _26992 P x y h1)). Qed.
Lemma lem1864712 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term25 P y x.
Proof. exact (@lem1864711 y x P x y h1). Qed.
Lemma lem1864715 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term55 P x y) (h3 : term147 P x y) : P y x.
Proof. exact (@lem1864712 P x y h3 (@lem1864668 P x y h1 h2 h3)). Qed.
Lemma lem1864716 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term55 P x y) (h3 : term147 P x y) : term175 P y x.
Proof. exact (fun h0 : term55 P y x => @lem1864715 P x y h1 h2 h3). Qed.
Lemma lem1864718 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1864719 (P : type1626) (y : real) (x : real) : (term175 P y x) = (P y x).
Proof. exact (@lem1864718 (P y x)). Qed.
Lemma lem1864720 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term55 P x y) (h3 : term147 P x y) : P y x.
Proof. exact (EQ_MP (@lem1864719 P y x) (@lem1864716 P x y h1 h2 h3)). Qed.
Lemma lem1864726 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1864727 (P : type1626) (_26995 : real) (_26996 : real) : (term83 P _26996 _26995) = (term79 P _26995 _26996).
Proof. exact (@lem1864726 (P _26996 _26995) (term55 P _26995 _26996)). Qed.
Lemma lem1864733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1864734 (P : type1626) (_26995 : real) (_26996 : real) : (term176 P _26996 _26995) = (term177 P _26995 _26996).
Proof. exact (MK_COMB (@lem1864733) (@lem1864727 P _26995 _26996)). Qed.
Lemma lem1864740 (P : type1626) (_26995 : real) (_26996 : real) : (term79 P _26995 _26996) = (term79 P _26995 _26996).
Proof. exact (eq_refl (term79 P _26995 _26996)). Qed.
Lemma lem1864741 (P : type1626) (_26995 : real) (_26996 : real) : ((term83 P _26996 _26995) = (term79 P _26995 _26996)) = ((term79 P _26995 _26996) = (term79 P _26995 _26996)).
Proof. exact (MK_COMB (@lem1864734 P _26995 _26996) (@lem1864740 P _26995 _26996)). Qed.
Lemma lem1864743 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1864744 (x : Prop) : (x = x) = True.
Proof. exact (@lem1864743 Prop x). Qed.
Lemma lem1864745 (P : type1626) (_26995 : real) (_26996 : real) : ((term79 P _26995 _26996) = (term79 P _26995 _26996)) = True.
Proof. exact (@lem1864744 (term79 P _26995 _26996)). Qed.
Lemma lem1864746 (P : type1626) (_26995 : real) (_26996 : real) : ((term83 P _26996 _26995) = (term79 P _26995 _26996)) = True.
Proof. exact (TRANS (@lem1864741 P _26995 _26996) (@lem1864745 P _26995 _26996)). Qed.
Lemma lem1864747 (P : type1626) (_26995 : real) (_26996 : real) : True = ((term83 P _26996 _26995) = (term79 P _26995 _26996)).
Proof. exact (SYM (@lem1864746 P _26995 _26996)). Qed.
Lemma lem1864748 (P : type1626) (_26995 : real) (_26996 : real) : (term83 P _26996 _26995) = (term79 P _26995 _26996).
Proof. exact (EQ_MP (@lem1864747 P _26995 _26996) (@lem0)). Qed.
Lemma lem1864749 (_26995 : real) (_26996 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term79 P _26995 _26996.
Proof. exact (EQ_MP (@lem1864748 P _26995 _26996) (@lem1864599 _26996 _26995 P x y h1)). Qed.
Lemma lem1864751 (b : Prop) (a : Prop) : (a \/ b) = (term159 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1864752 (P : type1626) (_26996 : real) (_26995 : real) : (term79 P _26995 _26996) = (term178 P _26996 _26995).
Proof. exact (@lem1864751 (term55 P _26995 _26996) (P _26996 _26995)). Qed.
Lemma lem1864754 (a : Prop) : (term171 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1864755 (P : type1626) (_26995 : real) (_26996 : real) : (term179 P _26995 _26996) = (P _26995 _26996).
Proof. exact (@lem1864754 (P _26995 _26996)). Qed.
Lemma lem1864756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1864757 (P : type1626) (_26995 : real) (_26996 : real) : (term180 P _26995 _26996) = (term181 P _26995 _26996).
Proof. exact (MK_COMB (@lem1864756) (@lem1864755 P _26995 _26996)). Qed.
Lemma lem1864758 (P : type1626) (_26996 : real) (_26995 : real) : (P _26996 _26995) = (P _26996 _26995).
Proof. exact (eq_refl (P _26996 _26995)). Qed.
Lemma lem1864759 (P : type1626) (_26996 : real) (_26995 : real) : (term178 P _26996 _26995) = (term182 P _26996 _26995).
Proof. exact (MK_COMB (@lem1864757 P _26995 _26996) (@lem1864758 P _26996 _26995)). Qed.
Lemma lem1864760 (P : type1626) (_26996 : real) (_26995 : real) : (term79 P _26995 _26996) = (term182 P _26996 _26995).
Proof. exact (TRANS (@lem1864752 P _26996 _26995) (@lem1864759 P _26996 _26995)). Qed.
Lemma lem1864763 (_26996 : real) (_26995 : real) (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term182 P _26996 _26995.
Proof. exact (EQ_MP (@lem1864760 P _26996 _26995) (@lem1864749 _26995 _26996 P x y h1)). Qed.
Lemma lem1864764 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term182 P x y.
Proof. exact (@lem1864763 x y P x y h1). Qed.
Lemma lem1864767 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term55 P x y) (h3 : term147 P x y) : P x y.
Proof. exact (@lem1864764 P x y h3 (@lem1864720 P x y h1 h2 h3)). Qed.
Lemma lem1864768 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : term175 P x y.
Proof. exact (fun h0 : term55 P x y => @lem1864767 P x y h1 h0 h2). Qed.
Lemma lem1864770 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1864771 (P : type1626) (x : real) (y : real) : (term175 P x y) = (P x y).
Proof. exact (@lem1864770 (P x y)). Qed.
Lemma lem1864772 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : P x y.
Proof. exact (EQ_MP (@lem1864771 P x y) (@lem1864768 P x y h1 h2)). Qed.
Lemma lem1864775 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1864777 (P : type1626) (x : real) (y : real) : (term55 P x y) = (term183 P x y).
Proof. exact (@lem1864775 (P x y)). Qed.
Lemma lem1864780 (P : type1626) (x : real) (y : real) (h1 : term147 P x y) : term183 P x y.
Proof. exact (EQ_MP (@lem1864777 P x y) (@lem1864581 P x y h1)). Qed.
Lemma lem1864783 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : False.
Proof. exact (@lem1864780 P x y h2 (@lem1864772 P x y h1 h2)). Qed.
Lemma lem1864784 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : term184.
Proof. exact (fun h0 : ~ False => @lem1864783 P x y h1 h2). Qed.
Lemma lem1864786 (p : Prop) : (term166 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1864787 : term184 = False.
Proof. exact (@lem1864786 False). Qed.
Lemma lem1864788 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : False.
Proof. exact (EQ_MP (@lem1864787) (@lem1864784 P x y h1 h2)). Qed.
Lemma lem1864789 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1864788 P x y h1 h2) (fun h3 : False => @lem1864497 h1)). Qed.
Lemma lem1864790 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : False.
Proof. exact (EQ_MP (@lem1864789 P x y h1 h2) (@lem1864497 h1)). Qed.
Lemma lem1864791 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : (term147 P x y) = False.
Proof. exact (prop_ext (fun h3 : term147 P x y => @lem1864790 P x y h1 h2) (fun h3 : False => @lem1864475 P x y h2)). Qed.
Lemma lem1864792 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : False.
Proof. exact (EQ_MP (@lem1864791 P x y h1 h2) (@lem1864475 P x y h2)). Qed.
Lemma lem1864793 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1864792 P x y h1 h2) (fun h3 : False => @lem1864395 h1)). Qed.
Lemma lem1864794 (P : type1626) (x : real) (y : real) (h1 : term10) (h2 : term147 P x y) : False.
Proof. exact (EQ_MP (@lem1864793 P x y h1 h2) (@lem1864395 h1)). Qed.
Lemma lem1864795 (P : type1626) (x : real) (h1 : term10) (h2 : term150 P x) : False.
Proof. exact (ex_elim (@lem1864374 P x h2) (fun y : real => fun h0 : term149 P x y => @lem1864794 P x y h1 h0)). Qed.
Lemma lem1864796 (P : type1626) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (ex_elim (@lem1864305 P h2) (fun x : real => fun h0 : term151 P x => @lem1864795 P x h1 h0)). Qed.
Lemma lem1864797 (P : type1626) (h1 : term10) (h2 : term3 P) : term10 = False.
Proof. exact (prop_ext (fun h3 : term10 => @lem1864796 P h1 h2) (fun h3 : False => @lem1864373 h1)). Qed.
Lemma lem1864798 (P : type1626) (h1 : term10) (h2 : term3 P) : False.
Proof. exact (EQ_MP (@lem1864797 P h1 h2) (@lem1864373 h1)). Qed.
Lemma lem1864799 (P : type1626) (h1 : term3 P) : term8.
Proof. exact (fun h0 : term10 => @lem1864798 P h0 h1). Qed.
Lemma lem1864800 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem1864801 (P : type1626) (h1 : term3 P) : term9.
Proof. exact (EQ_MP (@lem1864800) (@lem1864799 P h1)). Qed.
Lemma lem1864802 (P : type1626) : term12 P.
Proof. exact (fun h0 : term3 P => @lem1864801 P h0). Qed.
Lemma lem1864807 : term16.
Proof. exact (fun P : type1626 => @lem1864802 P). Qed.
Lemma lem1864808 : term15.
Proof. exact (EQ_MP (@lem1863863) (@lem1864807)). Qed.
Lemma lem1864809 (P : type1626) : term185 P.
Proof. exact (@lem1864808 P). Qed.
Lemma lem1864810 (P : type1626) : (term185 P) = (term4 P).
Proof. exact (eq_refl (term185 P)). Qed.
Lemma lem1864811 (P : type1626) : term4 P.
Proof. exact (EQ_MP (@lem1864810 P) (@lem1864809 P)). Qed.
Lemma lem1864813 (P : type1626) : term4 P.
Proof. exact (@lem1863631 P (@lem1864811 P)). Qed.
Lemma lem1864814 (P : type1626) (h1 : term3 P) : term8.
Proof. exact (@lem1864813 P (@lem1863616 P h1)). Qed.
Lemma lem1864815 (P : type1626) (h1 : term3 P) : False.
Proof. exact (@lem1864814 P h1 (@lem1339697)). Qed.
Lemma lem1864816 (P : type1626) (h1 : term3 P) : (term3 P) = False.
Proof. exact (prop_ext (fun h2 : term3 P => @lem1864815 P h1) (fun h2 : False => @lem1863616 P h1)). Qed.
Lemma lem1864817 (P : type1626) (h1 : term3 P) : False.
Proof. exact (EQ_MP (@lem1864816 P h1) (@lem1863616 P h1)). Qed.
Lemma lem1864818 (P : type1626) : term2 P.
Proof. exact (fun h0 : term3 P => @lem1864817 P h0). Qed.
Lemma lem1864819 (P : type1626) : term1 P.
Proof. exact (EQ_MP (@lem1863615 P) (@lem1864818 P)). Qed.
