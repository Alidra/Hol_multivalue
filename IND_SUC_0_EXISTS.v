Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IND_SUC_0_EXISTS_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import INFINITY_AX_spec.
Require Import ONE_ONE_spec.
Require Import ONTO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16433_spec.
Require Import thm16434_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
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
Lemma lem68764 {A B : Type'} (f : A -> B) : term0 A B f.
Proof. exact (@lem68752 A B f). Qed.
Lemma lem68765 {A B : Type'} (f : A -> B) : (term0 A B f) = ((@ONTO A B f) = (term1 A B f)).
Proof. exact (eq_refl (term0 A B f)). Qed.
Lemma lem68767 {A B : Type'} (f : A -> B) : term2 A B f.
Proof. exact (@lem68585 A B f). Qed.
Lemma lem68768 {A B : Type'} (f : A -> B) : (term2 A B f) = ((@ONE_ONE A B f) = (term3 A B f)).
Proof. exact (eq_refl (term2 A B f)). Qed.
Lemma lem68770 (f : ind -> ind) (h1 : term4 f) : term4 f.
Proof. exact (h1). Qed.
Lemma lem68776 {A B : Type'} (f : A -> B) : (@ONE_ONE A B f) = (term3 A B f).
Proof. exact (EQ_MP (@lem68768 A B f) (@lem68767 A B f)). Qed.
Lemma lem68777 (f : ind -> ind) : (@ONE_ONE ind ind f) = (term5 f).
Proof. exact (@lem68776 ind ind f). Qed.
Lemma lem68794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem68795 (f : ind -> ind) : (term6 f) = (term7 f).
Proof. exact (MK_COMB (@lem68794) (@lem68777 f)). Qed.
Lemma lem68797 {A B : Type'} (f : A -> B) : (@ONTO A B f) = (term1 A B f).
Proof. exact (EQ_MP (@lem68765 A B f) (@lem68764 A B f)). Qed.
Lemma lem68798 (f : ind -> ind) : (@ONTO ind ind f) = (term8 f).
Proof. exact (@lem68797 ind ind f). Qed.
Lemma lem68809 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem68810 (f : ind -> ind) : (term9 f) = (term10 f).
Proof. exact (MK_COMB (@lem68809) (@lem68798 f)). Qed.
Lemma lem68811 (f : ind -> ind) : (term4 f) = (term11 f).
Proof. exact (MK_COMB (@lem68795 f) (@lem68810 f)). Qed.
Lemma lem68814 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem68815 (f : ind -> ind) : (term12 f) = (term13 f).
Proof. exact (MK_COMB (@lem68814) (@lem68811 f)). Qed.
Lemma lem68842 (f : ind -> ind) : (term14 f) = (term14 f).
Proof. exact (eq_refl (term14 f)). Qed.
Lemma lem68843 (f : ind -> ind) : (term15 f) = (term16 f).
Proof. exact (MK_COMB (@lem68815 f) (@lem68842 f)). Qed.
Lemma lem68846 (f : ind -> ind) : (term16 f) = (term15 f).
Proof. exact (SYM (@lem68843 f)). Qed.
Lemma lem68848 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem68849 (f : ind -> ind) : (term16 f) = (term18 f).
Proof. exact (@lem68848 (term16 f)). Qed.
Lemma lem68850 (f : ind -> ind) : (term18 f) = (term16 f).
Proof. exact (SYM (@lem68849 f)). Qed.
Lemma lem68851 (f : ind -> ind) (h1 : term19 f) : term19 f.
Proof. exact (h1). Qed.
Lemma lem68854 (f : ind -> ind) (h1 : term18 f) : term18 f.
Proof. exact (h1). Qed.
Lemma lem68855 (f : ind -> ind) : term20 f.
Proof. exact (fun h0 : term18 f => @lem68854 f h0). Qed.
Lemma lem68856 (f : ind -> ind) (h1 : term20 f) : term20 f.
Proof. exact (h1). Qed.
Lemma lem68857 (f : ind -> ind) (h1 : term18 f) : term18 f.
Proof. exact (h1). Qed.
Lemma lem68858 (f : ind -> ind) (h1 : term18 f) (h2 : term20 f) : term18 f.
Proof. exact (@lem68856 f h2 (@lem68857 f h1)). Qed.
Lemma lem68859 (f : ind -> ind) (h1 : term18 f) : term21 f.
Proof. exact (fun h0 : term20 f => @lem68858 f h1 h0). Qed.
Lemma lem68860 (f : ind -> ind) (h1 : term20 f) : term20 f.
Proof. exact (h1). Qed.
Lemma lem68861 (f : ind -> ind) (h1 : term18 f) (h2 : term20 f) : term18 f.
Proof. exact (@lem68859 f h1 (@lem68860 f h2)). Qed.
Lemma lem68862 (f : ind -> ind) (h1 : term20 f) : term20 f.
Proof. exact (fun h0 : term18 f => @lem68861 f h0 h1). Qed.
Lemma lem68863 (f : ind -> ind) : term22 f.
Proof. exact (fun h0 : term20 f => @lem68862 f h0). Qed.
Lemma lem68866 (f : ind -> ind) : term20 f.
Proof. exact (@lem68863 f (@lem68855 f)). Qed.
Lemma lem68872 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem68873 (f : ind -> ind) : (term18 f) = (term23 f).
Proof. exact (@lem68872 (term19 f)). Qed.
Lemma lem68875 (t : Prop) : (term24 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem68876 (f : ind -> ind) : (term23 f) = (term16 f).
Proof. exact (@lem68875 (term16 f)). Qed.
Lemma lem68879 (f : ind -> ind) : (term18 f) = (term16 f).
Proof. exact (TRANS (@lem68873 f) (@lem68876 f)). Qed.
Lemma lem68901 {A : Type'} (P : Prop) (Q : A -> Prop) : (term25 A P Q) = (term26 A P Q).
Proof. exact (EQ_MP (@lem16434 A P Q) (@lem16433 A P Q)). Qed.
Lemma lem68902 (P : Prop) (Q : ind -> Prop) : (term27 P Q) = (term28 P Q).
Proof. exact (@lem68901 ind P Q). Qed.
Lemma lem68903 (f : ind -> ind) : (term29 f) = (term30 f).
Proof. exact (@lem68902 (term31 f) (term32 f)). Qed.
Lemma lem68904 (f : ind -> ind) (z : ind) : (term33 f z) = (term34 f z).
Proof. exact (eq_refl (term33 f z)). Qed.
Lemma lem68905 (f : ind -> ind) : (term35 f) = (term35 f).
Proof. exact (eq_refl (term35 f)). Qed.
Lemma lem68906 (f : ind -> ind) (z : ind) : (term36 f z) = (term37 f z).
Proof. exact (MK_COMB (@lem68905 f) (@lem68904 f z)). Qed.
Lemma lem68907 (f : ind -> ind) : (term38 f) = (term39 f).
Proof. exact (fun_ext (fun z : ind => @lem68906 f z)). Qed.
Lemma lem68908 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem68909 (f : ind -> ind) : (term29 f) = (term14 f).
Proof. exact (MK_COMB (@lem68908) (@lem68907 f)). Qed.
Lemma lem68910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem68911 (f : ind -> ind) : (term40 f) = (term41 f).
Proof. exact (MK_COMB (@lem68910) (@lem68909 f)). Qed.
Lemma lem68912 (f : ind -> ind) (z : ind) : (term33 f z) = (term34 f z).
Proof. exact (eq_refl (term33 f z)). Qed.
Lemma lem68913 (f : ind -> ind) : (term42 f) = (term32 f).
Proof. exact (fun_ext (fun z : ind => @lem68912 f z)). Qed.
Lemma lem68914 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem68915 (f : ind -> ind) : (term43 f) = (term44 f).
Proof. exact (MK_COMB (@lem68914) (@lem68913 f)). Qed.
Lemma lem68916 (f : ind -> ind) : (term35 f) = (term35 f).
Proof. exact (eq_refl (term35 f)). Qed.
Lemma lem68917 (f : ind -> ind) : (term30 f) = (term45 f).
Proof. exact (MK_COMB (@lem68916 f) (@lem68915 f)). Qed.
Lemma lem68918 (f : ind -> ind) : ((term29 f) = (term30 f)) = ((term14 f) = (term45 f)).
Proof. exact (MK_COMB (@lem68911 f) (@lem68917 f)). Qed.
Lemma lem68919 (f : ind -> ind) : (term14 f) = (term45 f).
Proof. exact (EQ_MP (@lem68918 f) (@lem68903 f)). Qed.
Lemma lem68938 (f : ind -> ind) : (term13 f) = (term13 f).
Proof. exact (eq_refl (term13 f)). Qed.
Lemma lem68939 (f : ind -> ind) : (term16 f) = (term46 f).
Proof. exact (MK_COMB (@lem68938 f) (@lem68919 f)). Qed.
Lemma lem68942 (f : ind -> ind) : (term18 f) = (term46 f).
Proof. exact (TRANS (@lem68879 f) (@lem68939 f)). Qed.
Lemma lem68943 : term47 = term48.
Proof. exact (fun_ext (fun f : ind -> ind => @lem68942 f)). Qed.
Lemma lem68944 : (@all (ind -> ind)) = (@all (ind -> ind)).
Proof. exact (eq_refl (@all (ind -> ind))). Qed.
Lemma lem68953 : term49 = term50.
Proof. exact (MK_COMB (@lem68944) (@lem68943)). Qed.
Lemma lem68956 (f : ind -> ind) (x : ind) (z : ind) : (term51 f x z) = (term51 f x z).
Proof. exact (eq_refl (term51 f x z)). Qed.
Lemma lem68957 (f : ind -> ind) (z : ind) : (term52 f z) = (term52 f z).
Proof. exact (fun_ext (fun x : ind => @lem68956 f x z)). Qed.
Lemma lem68958 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem68959 (f : ind -> ind) (z : ind) : (term34 f z) = (term34 f z).
Proof. exact (MK_COMB (@lem68958) (@lem68957 f z)). Qed.
Lemma lem68960 (f : ind -> ind) : (term32 f) = (term32 f).
Proof. exact (fun_ext (fun z : ind => @lem68959 f z)). Qed.
Lemma lem68961 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem68962 (f : ind -> ind) : (term44 f) = (term44 f).
Proof. exact (MK_COMB (@lem68961) (@lem68960 f)). Qed.
Lemma lem68967 (f : ind -> ind) (x1 : ind) (x2 : ind) : (((f x1) = (f x2)) = (x1 = x2)) = (((f x1) = (f x2)) = (x1 = x2)).
Proof. exact (eq_refl (((f x1) = (f x2)) = (x1 = x2))). Qed.
Lemma lem68968 (f : ind -> ind) (x1 : ind) : (term53 f x1) = (term53 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem68967 f x1 x2)). Qed.
Lemma lem68969 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem68970 (f : ind -> ind) (x1 : ind) : (term54 f x1) = (term54 f x1).
Proof. exact (MK_COMB (@lem68969) (@lem68968 f x1)). Qed.
Lemma lem68971 (f : ind -> ind) : (term55 f) = (term55 f).
Proof. exact (fun_ext (fun x1 : ind => @lem68970 f x1)). Qed.
Lemma lem68972 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem68973 (f : ind -> ind) : (term31 f) = (term31 f).
Proof. exact (MK_COMB (@lem68972) (@lem68971 f)). Qed.
Lemma lem68974 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem68975 (f : ind -> ind) : (term35 f) = (term35 f).
Proof. exact (MK_COMB (@lem68974) (@lem68973 f)). Qed.
Lemma lem68976 (f : ind -> ind) : (term45 f) = (term45 f).
Proof. exact (MK_COMB (@lem68975 f) (@lem68962 f)). Qed.
Lemma lem68977 (y : ind) (f : ind -> ind) (x : ind) : (y = (f x)) = (y = (f x)).
Proof. exact (eq_refl (y = (f x))). Qed.
Lemma lem68978 (y : ind) (f : ind -> ind) : (term56 y f) = (term56 y f).
Proof. exact (fun_ext (fun x : ind => @lem68977 y f x)). Qed.
Lemma lem68979 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem68980 (y : ind) (f : ind -> ind) : (term57 y f) = (term57 y f).
Proof. exact (MK_COMB (@lem68979) (@lem68978 y f)). Qed.
Lemma lem68981 (f : ind -> ind) : (term58 f) = (term58 f).
Proof. exact (fun_ext (fun y : ind => @lem68980 y f)). Qed.
Lemma lem68982 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem68983 (f : ind -> ind) : (term8 f) = (term8 f).
Proof. exact (MK_COMB (@lem68982) (@lem68981 f)). Qed.
Lemma lem68984 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem68985 (f : ind -> ind) : (term10 f) = (term10 f).
Proof. exact (MK_COMB (@lem68984) (@lem68983 f)). Qed.
Lemma lem68990 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term59 f x1 x2) = (term59 f x1 x2).
Proof. exact (eq_refl (term59 f x1 x2)). Qed.
Lemma lem68991 (f : ind -> ind) (x1 : ind) : (term60 f x1) = (term60 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem68990 f x1 x2)). Qed.
Lemma lem68992 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem68993 (f : ind -> ind) (x1 : ind) : (term61 f x1) = (term61 f x1).
Proof. exact (MK_COMB (@lem68992) (@lem68991 f x1)). Qed.
Lemma lem68994 (f : ind -> ind) : (term62 f) = (term62 f).
Proof. exact (fun_ext (fun x1 : ind => @lem68993 f x1)). Qed.
Lemma lem68995 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem68996 (f : ind -> ind) : (term5 f) = (term5 f).
Proof. exact (MK_COMB (@lem68995) (@lem68994 f)). Qed.
Lemma lem68997 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem68998 (f : ind -> ind) : (term7 f) = (term7 f).
Proof. exact (MK_COMB (@lem68997) (@lem68996 f)). Qed.
Lemma lem68999 (f : ind -> ind) : (term11 f) = (term11 f).
Proof. exact (MK_COMB (@lem68998 f) (@lem68985 f)). Qed.
Lemma lem69000 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem69001 (f : ind -> ind) : (term13 f) = (term13 f).
Proof. exact (MK_COMB (@lem69000) (@lem68999 f)). Qed.
Lemma lem69002 (f : ind -> ind) : (term46 f) = (term46 f).
Proof. exact (MK_COMB (@lem69001 f) (@lem68976 f)). Qed.
Lemma lem69003 : term48 = term48.
Proof. exact (fun_ext (fun f : ind -> ind => @lem69002 f)). Qed.
Lemma lem69004 : (@all (ind -> ind)) = (@all (ind -> ind)).
Proof. exact (eq_refl (@all (ind -> ind))). Qed.
Lemma lem69005 : term50 = term50.
Proof. exact (MK_COMB (@lem69004) (@lem69003)). Qed.
Lemma lem69070 : term49 = term50.
Proof. exact (TRANS (@lem68953) (@lem69005)). Qed.
Lemma lem69071 : term50 = term49.
Proof. exact (SYM (@lem69070)). Qed.
Lemma lem69072 (f : ind -> ind) (h1 : term11 f) : term11 f.
Proof. exact (h1). Qed.
Lemma lem69074 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem69075 (f : ind -> ind) : (term45 f) = (term63 f).
Proof. exact (@lem69074 (term45 f)). Qed.
Lemma lem69076 (f : ind -> ind) : (term63 f) = (term45 f).
Proof. exact (SYM (@lem69075 f)). Qed.
Lemma lem69077 (f : ind -> ind) (h1 : term64 f) : term64 f.
Proof. exact (h1). Qed.
Lemma lem69084 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term59 f x1 x2) = (term65 f x1 x2).
Proof. exact (@lem17265 ((f x1) = (f x2)) (x1 = x2)). Qed.
Lemma lem69085 (f : ind -> ind) (x1 : ind) : (term60 f x1) = (term66 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69084 f x1 x2)). Qed.
Lemma lem69086 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69087 (f : ind -> ind) (x1 : ind) : (term61 f x1) = (term67 f x1).
Proof. exact (MK_COMB (@lem69086) (@lem69085 f x1)). Qed.
Lemma lem69088 (f : ind -> ind) : (term62 f) = (term68 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69087 f x1)). Qed.
Lemma lem69089 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69090 (f : ind -> ind) : (term5 f) = (term69 f).
Proof. exact (MK_COMB (@lem69089) (@lem69088 f)). Qed.
Lemma lem69092 (P : ind -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18394 ind P). Qed.
Lemma lem69093 (y : ind) (f : ind -> ind) : (term72 y f) = (term73 y f).
Proof. exact (@lem69092 (term56 y f)). Qed.
Lemma lem69094 (y : ind) (f : ind -> ind) (x : ind) : (term74 y f x) = (y = (f x)).
Proof. exact (eq_refl (term74 y f x)). Qed.
Lemma lem69095 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem69097 (y : ind) (f : ind -> ind) (x : ind) : (term75 y f x) = (term76 y f x).
Proof. exact (MK_COMB (@lem69095) (@lem69094 y f x)). Qed.
Lemma lem69098 (y : ind) (f : ind -> ind) : (term77 y f) = (term78 y f).
Proof. exact (fun_ext (fun x : ind => @lem69097 y f x)). Qed.
Lemma lem69099 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69100 (y : ind) (f : ind -> ind) : (term73 y f) = (term79 y f).
Proof. exact (MK_COMB (@lem69099) (@lem69098 y f)). Qed.
Lemma lem69101 (y : ind) (f : ind -> ind) : (term72 y f) = (term79 y f).
Proof. exact (TRANS (@lem69093 y f) (@lem69100 y f)). Qed.
Lemma lem69102 (P : ind -> Prop) : (term80 P) = (term81 P).
Proof. exact (@lem18392 ind P). Qed.
Lemma lem69103 (f : ind -> ind) : (term10 f) = (term82 f).
Proof. exact (@lem69102 (term58 f)). Qed.
Lemma lem69104 (y : ind) (f : ind -> ind) : (term83 f y) = (term57 y f).
Proof. exact (eq_refl (term83 f y)). Qed.
Lemma lem69105 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem69106 (y : ind) (f : ind -> ind) : (term84 f y) = (term72 y f).
Proof. exact (MK_COMB (@lem69105) (@lem69104 y f)). Qed.
Lemma lem69107 (y : ind) (f : ind -> ind) : (term84 f y) = (term79 y f).
Proof. exact (TRANS (@lem69106 y f) (@lem69101 y f)). Qed.
Lemma lem69108 (f : ind -> ind) : (term85 f) = (term86 f).
Proof. exact (fun_ext (fun y : ind => @lem69107 y f)). Qed.
Lemma lem69109 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69110 (f : ind -> ind) : (term82 f) = (term87 f).
Proof. exact (MK_COMB (@lem69109) (@lem69108 f)). Qed.
Lemma lem69111 (f : ind -> ind) : (term10 f) = (term87 f).
Proof. exact (TRANS (@lem69103 f) (@lem69110 f)). Qed.
Lemma lem69112 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem69113 (f : ind -> ind) : (term7 f) = (term88 f).
Proof. exact (MK_COMB (@lem69112) (@lem69090 f)). Qed.
Lemma lem69114 (f : ind -> ind) : (term11 f) = (term89 f).
Proof. exact (MK_COMB (@lem69113 f) (@lem69111 f)). Qed.
Lemma lem69177 {A : Type'} (P : Prop) (Q : A -> Prop) : (term26 A P Q) = (term25 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem69178 (P : Prop) (Q : ind -> Prop) : (term28 P Q) = (term27 P Q).
Proof. exact (@lem69177 ind P Q). Qed.
Lemma lem69179 (f : ind -> ind) : (term90 f) = (term91 f).
Proof. exact (@lem69178 (term69 f) (term86 f)). Qed.
Lemma lem69180 (y : ind) (f : ind -> ind) : (term92 f y) = (term79 y f).
Proof. exact (eq_refl (term92 f y)). Qed.
Lemma lem69181 (f : ind -> ind) : (term93 f) = (term86 f).
Proof. exact (fun_ext (fun y : ind => @lem69180 y f)). Qed.
Lemma lem69182 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69183 (f : ind -> ind) : (term94 f) = (term87 f).
Proof. exact (MK_COMB (@lem69182) (@lem69181 f)). Qed.
Lemma lem69184 (f : ind -> ind) : (term88 f) = (term88 f).
Proof. exact (eq_refl (term88 f)). Qed.
Lemma lem69185 (f : ind -> ind) : (term90 f) = (term89 f).
Proof. exact (MK_COMB (@lem69184 f) (@lem69183 f)). Qed.
Lemma lem69186 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69187 (f : ind -> ind) : (term95 f) = (term96 f).
Proof. exact (MK_COMB (@lem69186) (@lem69185 f)). Qed.
Lemma lem69188 (y : ind) (f : ind -> ind) : (term92 f y) = (term79 y f).
Proof. exact (eq_refl (term92 f y)). Qed.
Lemma lem69189 (f : ind -> ind) : (term88 f) = (term88 f).
Proof. exact (eq_refl (term88 f)). Qed.
Lemma lem69190 (y : ind) (f : ind -> ind) : (term97 f y) = (term98 y f).
Proof. exact (MK_COMB (@lem69189 f) (@lem69188 y f)). Qed.
Lemma lem69191 (f : ind -> ind) : (term99 f) = (term100 f).
Proof. exact (fun_ext (fun y : ind => @lem69190 y f)). Qed.
Lemma lem69192 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69193 (f : ind -> ind) : (term91 f) = (term101 f).
Proof. exact (MK_COMB (@lem69192) (@lem69191 f)). Qed.
Lemma lem69194 (f : ind -> ind) : ((term90 f) = (term91 f)) = ((term89 f) = (term101 f)).
Proof. exact (MK_COMB (@lem69187 f) (@lem69193 f)). Qed.
Lemma lem69196 (f : ind -> ind) : (term89 f) = (term101 f).
Proof. exact (EQ_MP (@lem69194 f) (@lem69179 f)). Qed.
Lemma lem69197 (f : ind -> ind) : (term11 f) = (term101 f).
Proof. exact (TRANS (@lem69114 f) (@lem69196 f)). Qed.
Lemma lem69198 (f : ind -> ind) (h1 : term11 f) : term101 f.
Proof. exact (EQ_MP (@lem69197 f) (@lem69072 f h1)). Qed.
Lemma lem69213 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term102 f x1 x2) = (term103 f x1 x2).
Proof. exact (@lem17646 ((f x1) = (f x2)) (x1 = x2)). Qed.
Lemma lem69214 (P : ind -> Prop) : (term80 P) = (term81 P).
Proof. exact (@lem18392 ind P). Qed.
Lemma lem69215 (f : ind -> ind) (x1 : ind) : (term104 f x1) = (term105 f x1).
Proof. exact (@lem69214 (term53 f x1)). Qed.
Lemma lem69216 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term106 f x1 x2) = (((f x1) = (f x2)) = (x1 = x2)).
Proof. exact (eq_refl (term106 f x1 x2)). Qed.
Lemma lem69217 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem69218 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term107 f x1 x2) = (term102 f x1 x2).
Proof. exact (MK_COMB (@lem69217) (@lem69216 f x1 x2)). Qed.
Lemma lem69219 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term107 f x1 x2) = (term103 f x1 x2).
Proof. exact (TRANS (@lem69218 f x1 x2) (@lem69213 f x1 x2)). Qed.
Lemma lem69220 (f : ind -> ind) (x1 : ind) : (term108 f x1) = (term109 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69219 f x1 x2)). Qed.
Lemma lem69221 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69222 (f : ind -> ind) (x1 : ind) : (term105 f x1) = (term110 f x1).
Proof. exact (MK_COMB (@lem69221) (@lem69220 f x1)). Qed.
Lemma lem69223 (f : ind -> ind) (x1 : ind) : (term104 f x1) = (term110 f x1).
Proof. exact (TRANS (@lem69215 f x1) (@lem69222 f x1)). Qed.
Lemma lem69224 (P : ind -> Prop) : (term80 P) = (term81 P).
Proof. exact (@lem18392 ind P). Qed.
Lemma lem69225 (f : ind -> ind) : (term111 f) = (term112 f).
Proof. exact (@lem69224 (term55 f)). Qed.
Lemma lem69226 (f : ind -> ind) (x1 : ind) : (term113 f x1) = (term54 f x1).
Proof. exact (eq_refl (term113 f x1)). Qed.
Lemma lem69227 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem69228 (f : ind -> ind) (x1 : ind) : (term114 f x1) = (term104 f x1).
Proof. exact (MK_COMB (@lem69227) (@lem69226 f x1)). Qed.
Lemma lem69229 (f : ind -> ind) (x1 : ind) : (term114 f x1) = (term110 f x1).
Proof. exact (TRANS (@lem69228 f x1) (@lem69223 f x1)). Qed.
Lemma lem69230 (f : ind -> ind) : (term115 f) = (term116 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69229 f x1)). Qed.
Lemma lem69231 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69232 (f : ind -> ind) : (term112 f) = (term117 f).
Proof. exact (MK_COMB (@lem69231) (@lem69230 f)). Qed.
Lemma lem69233 (f : ind -> ind) : (term111 f) = (term117 f).
Proof. exact (TRANS (@lem69225 f) (@lem69232 f)). Qed.
Lemma lem69236 (f : ind -> ind) (x : ind) (z : ind) : (term118 f x z) = ((f x) = z).
Proof. exact (@lem16933 ((f x) = z)). Qed.
Lemma lem69237 (P : ind -> Prop) : (term80 P) = (term81 P).
Proof. exact (@lem18392 ind P). Qed.
Lemma lem69238 (f : ind -> ind) (z : ind) : (term119 f z) = (term120 f z).
Proof. exact (@lem69237 (term52 f z)). Qed.
Lemma lem69239 (f : ind -> ind) (x : ind) (z : ind) : (term121 f z x) = (term51 f x z).
Proof. exact (eq_refl (term121 f z x)). Qed.
Lemma lem69240 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem69241 (f : ind -> ind) (x : ind) (z : ind) : (term122 f z x) = (term118 f x z).
Proof. exact (MK_COMB (@lem69240) (@lem69239 f x z)). Qed.
Lemma lem69242 (f : ind -> ind) (x : ind) (z : ind) : (term122 f z x) = ((f x) = z).
Proof. exact (TRANS (@lem69241 f x z) (@lem69236 f x z)). Qed.
Lemma lem69243 (f : ind -> ind) (z : ind) : (term123 f z) = (term124 f z).
Proof. exact (fun_ext (fun x : ind => @lem69242 f x z)). Qed.
Lemma lem69244 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69245 (f : ind -> ind) (z : ind) : (term120 f z) = (term125 f z).
Proof. exact (MK_COMB (@lem69244) (@lem69243 f z)). Qed.
Lemma lem69246 (f : ind -> ind) (z : ind) : (term119 f z) = (term125 f z).
Proof. exact (TRANS (@lem69238 f z) (@lem69245 f z)). Qed.
Lemma lem69247 (P : ind -> Prop) : (term70 P) = (term71 P).
Proof. exact (@lem18394 ind P). Qed.
Lemma lem69248 (f : ind -> ind) : (term126 f) = (term127 f).
Proof. exact (@lem69247 (term32 f)). Qed.
Lemma lem69249 (f : ind -> ind) (z : ind) : (term33 f z) = (term34 f z).
Proof. exact (eq_refl (term33 f z)). Qed.
Lemma lem69250 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem69251 (f : ind -> ind) (z : ind) : (term128 f z) = (term119 f z).
Proof. exact (MK_COMB (@lem69250) (@lem69249 f z)). Qed.
Lemma lem69252 (f : ind -> ind) (z : ind) : (term128 f z) = (term125 f z).
Proof. exact (TRANS (@lem69251 f z) (@lem69246 f z)). Qed.
Lemma lem69253 (f : ind -> ind) : (term129 f) = (term130 f).
Proof. exact (fun_ext (fun z : ind => @lem69252 f z)). Qed.
Lemma lem69254 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69255 (f : ind -> ind) : (term127 f) = (term131 f).
Proof. exact (MK_COMB (@lem69254) (@lem69253 f)). Qed.
Lemma lem69256 (f : ind -> ind) : (term126 f) = (term131 f).
Proof. exact (TRANS (@lem69248 f) (@lem69255 f)). Qed.
Lemma lem69257 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69258 (f : ind -> ind) : (term132 f) = (term133 f).
Proof. exact (MK_COMB (@lem69257) (@lem69233 f)). Qed.
Lemma lem69259 (f : ind -> ind) : (term134 f) = (term135 f).
Proof. exact (MK_COMB (@lem69258 f) (@lem69256 f)). Qed.
Lemma lem69260 (f : ind -> ind) : (term64 f) = (term134 f).
Proof. exact (@lem17045 (term31 f) (term44 f)). Qed.
Lemma lem69261 (f : ind -> ind) : (term64 f) = (term135 f).
Proof. exact (TRANS (@lem69260 f) (@lem69259 f)). Qed.
Lemma lem69267 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem69268 (P : ind -> Prop) (Q : ind -> Prop) : (term138 P Q) = (term139 P Q).
Proof. exact (@lem69267 ind P Q). Qed.
Lemma lem69269 (f : ind -> ind) (x1 : ind) : (term140 f x1) = (term141 f x1).
Proof. exact (@lem69268 (term142 f x1) (term143 f x1)). Qed.
Lemma lem69270 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term144 f x1 x2) = (term145 f x1 x2).
Proof. exact (eq_refl (term144 f x1 x2)). Qed.
Lemma lem69271 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69272 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term146 f x1 x2) = (term147 f x1 x2).
Proof. exact (MK_COMB (@lem69271) (@lem69270 f x1 x2)). Qed.
Lemma lem69273 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term148 f x1 x2) = (term149 f x1 x2).
Proof. exact (eq_refl (term148 f x1 x2)). Qed.
Lemma lem69274 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term150 f x1 x2) = (term103 f x1 x2).
Proof. exact (MK_COMB (@lem69272 f x1 x2) (@lem69273 f x1 x2)). Qed.
Lemma lem69275 (f : ind -> ind) (x1 : ind) : (term151 f x1) = (term109 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69274 f x1 x2)). Qed.
Lemma lem69276 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69277 (f : ind -> ind) (x1 : ind) : (term140 f x1) = (term110 f x1).
Proof. exact (MK_COMB (@lem69276) (@lem69275 f x1)). Qed.
Lemma lem69278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69279 (f : ind -> ind) (x1 : ind) : (term152 f x1) = (term153 f x1).
Proof. exact (MK_COMB (@lem69278) (@lem69277 f x1)). Qed.
Lemma lem69280 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term144 f x1 x2) = (term145 f x1 x2).
Proof. exact (eq_refl (term144 f x1 x2)). Qed.
Lemma lem69281 (f : ind -> ind) (x1 : ind) : (term154 f x1) = (term142 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69280 f x1 x2)). Qed.
Lemma lem69282 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69283 (f : ind -> ind) (x1 : ind) : (term155 f x1) = (term156 f x1).
Proof. exact (MK_COMB (@lem69282) (@lem69281 f x1)). Qed.
Lemma lem69284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69285 (f : ind -> ind) (x1 : ind) : (term157 f x1) = (term158 f x1).
Proof. exact (MK_COMB (@lem69284) (@lem69283 f x1)). Qed.
Lemma lem69286 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term148 f x1 x2) = (term149 f x1 x2).
Proof. exact (eq_refl (term148 f x1 x2)). Qed.
Lemma lem69287 (f : ind -> ind) (x1 : ind) : (term159 f x1) = (term143 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69286 f x1 x2)). Qed.
Lemma lem69288 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69289 (f : ind -> ind) (x1 : ind) : (term160 f x1) = (term161 f x1).
Proof. exact (MK_COMB (@lem69288) (@lem69287 f x1)). Qed.
Lemma lem69290 (f : ind -> ind) (x1 : ind) : (term141 f x1) = (term162 f x1).
Proof. exact (MK_COMB (@lem69285 f x1) (@lem69289 f x1)). Qed.
Lemma lem69291 (f : ind -> ind) (x1 : ind) : ((term140 f x1) = (term141 f x1)) = ((term110 f x1) = (term162 f x1)).
Proof. exact (MK_COMB (@lem69279 f x1) (@lem69290 f x1)). Qed.
Lemma lem69292 (f : ind -> ind) (x1 : ind) : (term110 f x1) = (term162 f x1).
Proof. exact (EQ_MP (@lem69291 f x1) (@lem69269 f x1)). Qed.
Lemma lem69389 (f : ind -> ind) : (term116 f) = (term163 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69292 f x1)). Qed.
Lemma lem69390 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69391 (f : ind -> ind) : (term117 f) = (term164 f).
Proof. exact (MK_COMB (@lem69390) (@lem69389 f)). Qed.
Lemma lem69393 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term136 A P Q) = (term137 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem69394 (P : ind -> Prop) (Q : ind -> Prop) : (term138 P Q) = (term139 P Q).
Proof. exact (@lem69393 ind P Q). Qed.
Lemma lem69395 (f : ind -> ind) : (term165 f) = (term166 f).
Proof. exact (@lem69394 (term167 f) (term168 f)). Qed.
Lemma lem69396 (f : ind -> ind) (x1 : ind) : (term169 f x1) = (term156 f x1).
Proof. exact (eq_refl (term169 f x1)). Qed.
Lemma lem69397 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69398 (f : ind -> ind) (x1 : ind) : (term170 f x1) = (term158 f x1).
Proof. exact (MK_COMB (@lem69397) (@lem69396 f x1)). Qed.
Lemma lem69399 (f : ind -> ind) (x1 : ind) : (term171 f x1) = (term161 f x1).
Proof. exact (eq_refl (term171 f x1)). Qed.
Lemma lem69400 (f : ind -> ind) (x1 : ind) : (term172 f x1) = (term162 f x1).
Proof. exact (MK_COMB (@lem69398 f x1) (@lem69399 f x1)). Qed.
Lemma lem69401 (f : ind -> ind) : (term173 f) = (term163 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69400 f x1)). Qed.
Lemma lem69402 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69403 (f : ind -> ind) : (term165 f) = (term164 f).
Proof. exact (MK_COMB (@lem69402) (@lem69401 f)). Qed.
Lemma lem69404 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69405 (f : ind -> ind) : (term174 f) = (term175 f).
Proof. exact (MK_COMB (@lem69404) (@lem69403 f)). Qed.
Lemma lem69406 (f : ind -> ind) (x1 : ind) : (term169 f x1) = (term156 f x1).
Proof. exact (eq_refl (term169 f x1)). Qed.
Lemma lem69407 (f : ind -> ind) : (term176 f) = (term167 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69406 f x1)). Qed.
Lemma lem69408 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69409 (f : ind -> ind) : (term177 f) = (term178 f).
Proof. exact (MK_COMB (@lem69408) (@lem69407 f)). Qed.
Lemma lem69410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69411 (f : ind -> ind) : (term179 f) = (term180 f).
Proof. exact (MK_COMB (@lem69410) (@lem69409 f)). Qed.
Lemma lem69412 (f : ind -> ind) (x1 : ind) : (term171 f x1) = (term161 f x1).
Proof. exact (eq_refl (term171 f x1)). Qed.
Lemma lem69413 (f : ind -> ind) : (term181 f) = (term168 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69412 f x1)). Qed.
Lemma lem69414 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69415 (f : ind -> ind) : (term182 f) = (term183 f).
Proof. exact (MK_COMB (@lem69414) (@lem69413 f)). Qed.
Lemma lem69416 (f : ind -> ind) : (term166 f) = (term184 f).
Proof. exact (MK_COMB (@lem69411 f) (@lem69415 f)). Qed.
Lemma lem69417 (f : ind -> ind) : ((term165 f) = (term166 f)) = ((term164 f) = (term184 f)).
Proof. exact (MK_COMB (@lem69405 f) (@lem69416 f)). Qed.
Lemma lem69418 (f : ind -> ind) : (term164 f) = (term184 f).
Proof. exact (EQ_MP (@lem69417 f) (@lem69395 f)). Qed.
Lemma lem69523 (f : ind -> ind) : (term117 f) = (term184 f).
Proof. exact (TRANS (@lem69391 f) (@lem69418 f)). Qed.
Lemma lem69524 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69525 (f : ind -> ind) : (term133 f) = (term185 f).
Proof. exact (MK_COMB (@lem69524) (@lem69523 f)). Qed.
Lemma lem69534 (f : ind -> ind) : (term131 f) = (term131 f).
Proof. exact (eq_refl (term131 f)). Qed.
Lemma lem69535 (f : ind -> ind) : (term135 f) = (term186 f).
Proof. exact (MK_COMB (@lem69525 f) (@lem69534 f)). Qed.
Lemma lem69537 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem69538 (P : ind -> Prop) (Q : ind -> Prop) : (term139 P Q) = (term138 P Q).
Proof. exact (@lem69537 ind P Q). Qed.
Lemma lem69539 (f : ind -> ind) : (term166 f) = (term165 f).
Proof. exact (@lem69538 (term167 f) (term168 f)). Qed.
Lemma lem69540 (f : ind -> ind) (x1 : ind) : (term169 f x1) = (term156 f x1).
Proof. exact (eq_refl (term169 f x1)). Qed.
Lemma lem69541 (f : ind -> ind) : (term176 f) = (term167 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69540 f x1)). Qed.
Lemma lem69542 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69543 (f : ind -> ind) : (term177 f) = (term178 f).
Proof. exact (MK_COMB (@lem69542) (@lem69541 f)). Qed.
Lemma lem69544 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69545 (f : ind -> ind) : (term179 f) = (term180 f).
Proof. exact (MK_COMB (@lem69544) (@lem69543 f)). Qed.
Lemma lem69546 (f : ind -> ind) (x1 : ind) : (term171 f x1) = (term161 f x1).
Proof. exact (eq_refl (term171 f x1)). Qed.
Lemma lem69547 (f : ind -> ind) : (term181 f) = (term168 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69546 f x1)). Qed.
Lemma lem69548 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69549 (f : ind -> ind) : (term182 f) = (term183 f).
Proof. exact (MK_COMB (@lem69548) (@lem69547 f)). Qed.
Lemma lem69550 (f : ind -> ind) : (term166 f) = (term184 f).
Proof. exact (MK_COMB (@lem69545 f) (@lem69549 f)). Qed.
Lemma lem69551 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69552 (f : ind -> ind) : (term187 f) = (term188 f).
Proof. exact (MK_COMB (@lem69551) (@lem69550 f)). Qed.
Lemma lem69553 (f : ind -> ind) (x1 : ind) : (term169 f x1) = (term156 f x1).
Proof. exact (eq_refl (term169 f x1)). Qed.
Lemma lem69554 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69555 (f : ind -> ind) (x1 : ind) : (term170 f x1) = (term158 f x1).
Proof. exact (MK_COMB (@lem69554) (@lem69553 f x1)). Qed.
Lemma lem69556 (f : ind -> ind) (x1 : ind) : (term171 f x1) = (term161 f x1).
Proof. exact (eq_refl (term171 f x1)). Qed.
Lemma lem69557 (f : ind -> ind) (x1 : ind) : (term172 f x1) = (term162 f x1).
Proof. exact (MK_COMB (@lem69555 f x1) (@lem69556 f x1)). Qed.
Lemma lem69558 (f : ind -> ind) : (term173 f) = (term163 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69557 f x1)). Qed.
Lemma lem69559 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69560 (f : ind -> ind) : (term165 f) = (term164 f).
Proof. exact (MK_COMB (@lem69559) (@lem69558 f)). Qed.
Lemma lem69561 (f : ind -> ind) : ((term166 f) = (term165 f)) = ((term184 f) = (term164 f)).
Proof. exact (MK_COMB (@lem69552 f) (@lem69560 f)). Qed.
Lemma lem69562 (f : ind -> ind) : (term184 f) = (term164 f).
Proof. exact (EQ_MP (@lem69561 f) (@lem69539 f)). Qed.
Lemma lem69564 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term137 A P Q) = (term136 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem69565 (P : ind -> Prop) (Q : ind -> Prop) : (term139 P Q) = (term138 P Q).
Proof. exact (@lem69564 ind P Q). Qed.
Lemma lem69566 (f : ind -> ind) (x1 : ind) : (term141 f x1) = (term140 f x1).
Proof. exact (@lem69565 (term142 f x1) (term143 f x1)). Qed.
Lemma lem69567 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term144 f x1 x2) = (term145 f x1 x2).
Proof. exact (eq_refl (term144 f x1 x2)). Qed.
Lemma lem69568 (f : ind -> ind) (x1 : ind) : (term154 f x1) = (term142 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69567 f x1 x2)). Qed.
Lemma lem69569 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69570 (f : ind -> ind) (x1 : ind) : (term155 f x1) = (term156 f x1).
Proof. exact (MK_COMB (@lem69569) (@lem69568 f x1)). Qed.
Lemma lem69571 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69572 (f : ind -> ind) (x1 : ind) : (term157 f x1) = (term158 f x1).
Proof. exact (MK_COMB (@lem69571) (@lem69570 f x1)). Qed.
Lemma lem69573 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term148 f x1 x2) = (term149 f x1 x2).
Proof. exact (eq_refl (term148 f x1 x2)). Qed.
Lemma lem69574 (f : ind -> ind) (x1 : ind) : (term159 f x1) = (term143 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69573 f x1 x2)). Qed.
Lemma lem69575 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69576 (f : ind -> ind) (x1 : ind) : (term160 f x1) = (term161 f x1).
Proof. exact (MK_COMB (@lem69575) (@lem69574 f x1)). Qed.
Lemma lem69577 (f : ind -> ind) (x1 : ind) : (term141 f x1) = (term162 f x1).
Proof. exact (MK_COMB (@lem69572 f x1) (@lem69576 f x1)). Qed.
Lemma lem69578 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69579 (f : ind -> ind) (x1 : ind) : (term189 f x1) = (term190 f x1).
Proof. exact (MK_COMB (@lem69578) (@lem69577 f x1)). Qed.
Lemma lem69580 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term144 f x1 x2) = (term145 f x1 x2).
Proof. exact (eq_refl (term144 f x1 x2)). Qed.
Lemma lem69581 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69582 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term146 f x1 x2) = (term147 f x1 x2).
Proof. exact (MK_COMB (@lem69581) (@lem69580 f x1 x2)). Qed.
Lemma lem69583 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term148 f x1 x2) = (term149 f x1 x2).
Proof. exact (eq_refl (term148 f x1 x2)). Qed.
Lemma lem69584 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term150 f x1 x2) = (term103 f x1 x2).
Proof. exact (MK_COMB (@lem69582 f x1 x2) (@lem69583 f x1 x2)). Qed.
Lemma lem69585 (f : ind -> ind) (x1 : ind) : (term151 f x1) = (term109 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69584 f x1 x2)). Qed.
Lemma lem69586 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69587 (f : ind -> ind) (x1 : ind) : (term140 f x1) = (term110 f x1).
Proof. exact (MK_COMB (@lem69586) (@lem69585 f x1)). Qed.
Lemma lem69588 (f : ind -> ind) (x1 : ind) : ((term141 f x1) = (term140 f x1)) = ((term162 f x1) = (term110 f x1)).
Proof. exact (MK_COMB (@lem69579 f x1) (@lem69587 f x1)). Qed.
Lemma lem69589 (f : ind -> ind) (x1 : ind) : (term162 f x1) = (term110 f x1).
Proof. exact (EQ_MP (@lem69588 f x1) (@lem69566 f x1)). Qed.
Lemma lem69590 (f : ind -> ind) : (term163 f) = (term116 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69589 f x1)). Qed.
Lemma lem69591 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69592 (f : ind -> ind) : (term164 f) = (term117 f).
Proof. exact (MK_COMB (@lem69591) (@lem69590 f)). Qed.
Lemma lem69593 (f : ind -> ind) : (term184 f) = (term117 f).
Proof. exact (TRANS (@lem69562 f) (@lem69592 f)). Qed.
Lemma lem69594 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69595 (f : ind -> ind) : (term185 f) = (term133 f).
Proof. exact (MK_COMB (@lem69594) (@lem69593 f)). Qed.
Lemma lem69597 {A B : Type'} (P : type1413 A B) : (term191 A B P) = (term192 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem69598 (P : type1547) : (term193 P) = (term194 P).
Proof. exact (@lem69597 ind ind P). Qed.
Lemma lem69599 (f : ind -> ind) : (term195 f) = (term196 f).
Proof. exact (@lem69598 (term197 f)). Qed.
Lemma lem69600 (f : ind -> ind) (z : ind) : (term198 f z) = (term124 f z).
Proof. exact (eq_refl (term198 f z)). Qed.
Lemma lem69601 (x : ind) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem69602 (f : ind -> ind) (z : ind) (x : ind) : (term199 f z x) = (term200 f z x).
Proof. exact (MK_COMB (@lem69600 f z) (@lem69601 x)). Qed.
Lemma lem69603 (f : ind -> ind) (x : ind) (z : ind) : (term200 f z x) = ((f x) = z).
Proof. exact (eq_refl (term200 f z x)). Qed.
Lemma lem69604 (f : ind -> ind) (x : ind) (z : ind) : (term199 f z x) = ((f x) = z).
Proof. exact (TRANS (@lem69602 f z x) (@lem69603 f x z)). Qed.
Lemma lem69605 (f : ind -> ind) (z : ind) : (term201 f z) = (term124 f z).
Proof. exact (fun_ext (fun x : ind => @lem69604 f x z)). Qed.
Lemma lem69606 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69607 (f : ind -> ind) (z : ind) : (term202 f z) = (term125 f z).
Proof. exact (MK_COMB (@lem69606) (@lem69605 f z)). Qed.
Lemma lem69608 (f : ind -> ind) : (term203 f) = (term130 f).
Proof. exact (fun_ext (fun z : ind => @lem69607 f z)). Qed.
Lemma lem69609 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69610 (f : ind -> ind) : (term195 f) = (term131 f).
Proof. exact (MK_COMB (@lem69609) (@lem69608 f)). Qed.
Lemma lem69611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69612 (f : ind -> ind) : (term204 f) = (term205 f).
Proof. exact (MK_COMB (@lem69611) (@lem69610 f)). Qed.
Lemma lem69613 (f : ind -> ind) (z : ind) : (term198 f z) = (term124 f z).
Proof. exact (eq_refl (term198 f z)). Qed.
Lemma lem69614 (x : ind -> ind) (z : ind) : (x z) = (x z).
Proof. exact (eq_refl (x z)). Qed.
Lemma lem69615 (f : ind -> ind) (x : ind -> ind) (z : ind) : (term206 f x z) = (term207 f x z).
Proof. exact (MK_COMB (@lem69613 f z) (@lem69614 x z)). Qed.
Lemma lem69616 (f : ind -> ind) (x : ind -> ind) (z : ind) : (term207 f x z) = ((term208 f x z) = z).
Proof. exact (eq_refl (term207 f x z)). Qed.
Lemma lem69617 (f : ind -> ind) (x : ind -> ind) (z : ind) : (term206 f x z) = ((term208 f x z) = z).
Proof. exact (TRANS (@lem69615 f x z) (@lem69616 f x z)). Qed.
Lemma lem69618 (f : ind -> ind) (x : ind -> ind) : (term209 f x) = (term210 f x).
Proof. exact (fun_ext (fun z : ind => @lem69617 f x z)). Qed.
Lemma lem69619 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69620 (f : ind -> ind) (x : ind -> ind) : (term211 f x) = (term212 f x).
Proof. exact (MK_COMB (@lem69619) (@lem69618 f x)). Qed.
Lemma lem69621 (f : ind -> ind) : (term213 f) = (term214 f).
Proof. exact (fun_ext (fun x : ind -> ind => @lem69620 f x)). Qed.
Lemma lem69622 : (@ex (ind -> ind)) = (@ex (ind -> ind)).
Proof. exact (eq_refl (@ex (ind -> ind))). Qed.
Lemma lem69623 (f : ind -> ind) : (term196 f) = (term215 f).
Proof. exact (MK_COMB (@lem69622) (@lem69621 f)). Qed.
Lemma lem69624 (f : ind -> ind) : ((term195 f) = (term196 f)) = ((term131 f) = (term215 f)).
Proof. exact (MK_COMB (@lem69612 f) (@lem69623 f)). Qed.
Lemma lem69625 (f : ind -> ind) : (term131 f) = (term215 f).
Proof. exact (EQ_MP (@lem69624 f) (@lem69599 f)). Qed.
Lemma lem69626 (f : ind -> ind) : (term186 f) = (term216 f).
Proof. exact (MK_COMB (@lem69595 f) (@lem69625 f)). Qed.
Lemma lem69630 {A : Type'} (P : A -> Prop) (Q : Prop) : (term217 A P Q) = (term218 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem69631 (P : ind -> Prop) (Q : Prop) : (term219 P Q) = (term220 P Q).
Proof. exact (@lem69630 ind P Q). Qed.
Lemma lem69632 (f : ind -> ind) : (term221 f) = (term222 f).
Proof. exact (@lem69631 (term116 f) (term215 f)). Qed.
Lemma lem69633 (f : ind -> ind) (x1 : ind) : (term223 f x1) = (term110 f x1).
Proof. exact (eq_refl (term223 f x1)). Qed.
Lemma lem69634 (f : ind -> ind) : (term224 f) = (term116 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69633 f x1)). Qed.
Lemma lem69635 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69636 (f : ind -> ind) : (term225 f) = (term117 f).
Proof. exact (MK_COMB (@lem69635) (@lem69634 f)). Qed.
Lemma lem69637 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69638 (f : ind -> ind) : (term226 f) = (term133 f).
Proof. exact (MK_COMB (@lem69637) (@lem69636 f)). Qed.
Lemma lem69639 (f : ind -> ind) : (term215 f) = (term215 f).
Proof. exact (eq_refl (term215 f)). Qed.
Lemma lem69640 (f : ind -> ind) : (term221 f) = (term216 f).
Proof. exact (MK_COMB (@lem69638 f) (@lem69639 f)). Qed.
Lemma lem69641 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69642 (f : ind -> ind) : (term227 f) = (term228 f).
Proof. exact (MK_COMB (@lem69641) (@lem69640 f)). Qed.
Lemma lem69643 (f : ind -> ind) (x1 : ind) : (term223 f x1) = (term110 f x1).
Proof. exact (eq_refl (term223 f x1)). Qed.
Lemma lem69644 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69645 (f : ind -> ind) (x1 : ind) : (term229 f x1) = (term230 f x1).
Proof. exact (MK_COMB (@lem69644) (@lem69643 f x1)). Qed.
Lemma lem69646 (f : ind -> ind) : (term215 f) = (term215 f).
Proof. exact (eq_refl (term215 f)). Qed.
Lemma lem69647 (x1 : ind) (f : ind -> ind) : (term231 x1 f) = (term232 x1 f).
Proof. exact (MK_COMB (@lem69645 f x1) (@lem69646 f)). Qed.
Lemma lem69648 (f : ind -> ind) : (term233 f) = (term234 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69647 x1 f)). Qed.
Lemma lem69649 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69650 (f : ind -> ind) : (term222 f) = (term235 f).
Proof. exact (MK_COMB (@lem69649) (@lem69648 f)). Qed.
Lemma lem69651 (f : ind -> ind) : ((term221 f) = (term222 f)) = ((term216 f) = (term235 f)).
Proof. exact (MK_COMB (@lem69642 f) (@lem69650 f)). Qed.
Lemma lem69652 (f : ind -> ind) : (term216 f) = (term235 f).
Proof. exact (EQ_MP (@lem69651 f) (@lem69632 f)). Qed.
Lemma lem69656 {A : Type'} (P : A -> Prop) (Q : Prop) : (term217 A P Q) = (term218 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem69657 (P : ind -> Prop) (Q : Prop) : (term219 P Q) = (term220 P Q).
Proof. exact (@lem69656 ind P Q). Qed.
Lemma lem69658 (x1 : ind) (f : ind -> ind) : (term236 x1 f) = (term237 x1 f).
Proof. exact (@lem69657 (term109 f x1) (term215 f)). Qed.
Lemma lem69659 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term238 f x1 x2) = (term103 f x1 x2).
Proof. exact (eq_refl (term238 f x1 x2)). Qed.
Lemma lem69660 (f : ind -> ind) (x1 : ind) : (term239 f x1) = (term109 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69659 f x1 x2)). Qed.
Lemma lem69661 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69662 (f : ind -> ind) (x1 : ind) : (term240 f x1) = (term110 f x1).
Proof. exact (MK_COMB (@lem69661) (@lem69660 f x1)). Qed.
Lemma lem69663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69664 (f : ind -> ind) (x1 : ind) : (term241 f x1) = (term230 f x1).
Proof. exact (MK_COMB (@lem69663) (@lem69662 f x1)). Qed.
Lemma lem69665 (f : ind -> ind) : (term215 f) = (term215 f).
Proof. exact (eq_refl (term215 f)). Qed.
Lemma lem69666 (x1 : ind) (f : ind -> ind) : (term236 x1 f) = (term232 x1 f).
Proof. exact (MK_COMB (@lem69664 f x1) (@lem69665 f)). Qed.
Lemma lem69667 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69668 (x1 : ind) (f : ind -> ind) : (term242 x1 f) = (term243 x1 f).
Proof. exact (MK_COMB (@lem69667) (@lem69666 x1 f)). Qed.
Lemma lem69669 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term238 f x1 x2) = (term103 f x1 x2).
Proof. exact (eq_refl (term238 f x1 x2)). Qed.
Lemma lem69670 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem69671 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term244 f x1 x2) = (term245 f x1 x2).
Proof. exact (MK_COMB (@lem69670) (@lem69669 f x1 x2)). Qed.
Lemma lem69672 (f : ind -> ind) : (term215 f) = (term215 f).
Proof. exact (eq_refl (term215 f)). Qed.
Lemma lem69673 (x1 : ind) (x2 : ind) (f : ind -> ind) : (term246 x1 x2 f) = (term247 x1 x2 f).
Proof. exact (MK_COMB (@lem69671 f x1 x2) (@lem69672 f)). Qed.
Lemma lem69674 (x1 : ind) (f : ind -> ind) : (term248 x1 f) = (term249 x1 f).
Proof. exact (fun_ext (fun x2 : ind => @lem69673 x1 x2 f)). Qed.
Lemma lem69675 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69676 (x1 : ind) (f : ind -> ind) : (term237 x1 f) = (term250 x1 f).
Proof. exact (MK_COMB (@lem69675) (@lem69674 x1 f)). Qed.
Lemma lem69677 (x1 : ind) (f : ind -> ind) : ((term236 x1 f) = (term237 x1 f)) = ((term232 x1 f) = (term250 x1 f)).
Proof. exact (MK_COMB (@lem69668 x1 f) (@lem69676 x1 f)). Qed.
Lemma lem69678 (x1 : ind) (f : ind -> ind) : (term232 x1 f) = (term250 x1 f).
Proof. exact (EQ_MP (@lem69677 x1 f) (@lem69658 x1 f)). Qed.
Lemma lem69680 {A : Type'} (P : Prop) (Q : A -> Prop) : (term251 A P Q) = (term252 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem69681 (P : Prop) (Q : type922) : (term253 P Q) = (term254 P Q).
Proof. exact (@lem69680 (ind -> ind) P Q). Qed.
Lemma lem69682 (x1 : ind) (x2 : ind) (f : ind -> ind) : (term255 x1 x2 f) = (term256 x1 x2 f).
Proof. exact (@lem69681 (term103 f x1 x2) (term214 f)). Qed.
Lemma lem69683 (f : ind -> ind) (x : ind -> ind) : (term257 f x) = (term212 f x).
Proof. exact (eq_refl (term257 f x)). Qed.
Lemma lem69684 (f : ind -> ind) : (term258 f) = (term214 f).
Proof. exact (fun_ext (fun x : ind -> ind => @lem69683 f x)). Qed.
Lemma lem69685 : (@ex (ind -> ind)) = (@ex (ind -> ind)).
Proof. exact (eq_refl (@ex (ind -> ind))). Qed.
Lemma lem69686 (f : ind -> ind) : (term259 f) = (term215 f).
Proof. exact (MK_COMB (@lem69685) (@lem69684 f)). Qed.
Lemma lem69687 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term245 f x1 x2) = (term245 f x1 x2).
Proof. exact (eq_refl (term245 f x1 x2)). Qed.
Lemma lem69688 (x1 : ind) (x2 : ind) (f : ind -> ind) : (term255 x1 x2 f) = (term247 x1 x2 f).
Proof. exact (MK_COMB (@lem69687 f x1 x2) (@lem69686 f)). Qed.
Lemma lem69689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem69690 (x1 : ind) (x2 : ind) (f : ind -> ind) : (term260 x1 x2 f) = (term261 x1 x2 f).
Proof. exact (MK_COMB (@lem69689) (@lem69688 x1 x2 f)). Qed.
Lemma lem69691 (f : ind -> ind) (x : ind -> ind) : (term257 f x) = (term212 f x).
Proof. exact (eq_refl (term257 f x)). Qed.
Lemma lem69692 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term245 f x1 x2) = (term245 f x1 x2).
Proof. exact (eq_refl (term245 f x1 x2)). Qed.
Lemma lem69693 (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) : (term262 x1 x2 f x) = (term263 x1 x2 f x).
Proof. exact (MK_COMB (@lem69692 f x1 x2) (@lem69691 f x)). Qed.
Lemma lem69694 (x1 : ind) (x2 : ind) (f : ind -> ind) : (term264 x1 x2 f) = (term265 x1 x2 f).
Proof. exact (fun_ext (fun x : ind -> ind => @lem69693 x1 x2 f x)). Qed.
Lemma lem69695 : (@ex (ind -> ind)) = (@ex (ind -> ind)).
Proof. exact (eq_refl (@ex (ind -> ind))). Qed.
Lemma lem69696 (x1 : ind) (x2 : ind) (f : ind -> ind) : (term256 x1 x2 f) = (term266 x1 x2 f).
Proof. exact (MK_COMB (@lem69695) (@lem69694 x1 x2 f)). Qed.
Lemma lem69697 (x1 : ind) (x2 : ind) (f : ind -> ind) : ((term255 x1 x2 f) = (term256 x1 x2 f)) = ((term247 x1 x2 f) = (term266 x1 x2 f)).
Proof. exact (MK_COMB (@lem69690 x1 x2 f) (@lem69696 x1 x2 f)). Qed.
Lemma lem69698 (x1 : ind) (x2 : ind) (f : ind -> ind) : (term247 x1 x2 f) = (term266 x1 x2 f).
Proof. exact (EQ_MP (@lem69697 x1 x2 f) (@lem69682 x1 x2 f)). Qed.
Lemma lem69699 (x1 : ind) (f : ind -> ind) : (term249 x1 f) = (term267 x1 f).
Proof. exact (fun_ext (fun x2 : ind => @lem69698 x1 x2 f)). Qed.
Lemma lem69700 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69701 (x1 : ind) (f : ind -> ind) : (term250 x1 f) = (term268 x1 f).
Proof. exact (MK_COMB (@lem69700) (@lem69699 x1 f)). Qed.
Lemma lem69702 (x1 : ind) (f : ind -> ind) : (term232 x1 f) = (term268 x1 f).
Proof. exact (TRANS (@lem69678 x1 f) (@lem69701 x1 f)). Qed.
Lemma lem69703 (f : ind -> ind) : (term234 f) = (term269 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69702 x1 f)). Qed.
Lemma lem69704 : (@ex ind) = (@ex ind).
Proof. exact (eq_refl (@ex ind)). Qed.
Lemma lem69705 (f : ind -> ind) : (term235 f) = (term270 f).
Proof. exact (MK_COMB (@lem69704) (@lem69703 f)). Qed.
Lemma lem69706 (f : ind -> ind) : (term216 f) = (term270 f).
Proof. exact (TRANS (@lem69652 f) (@lem69705 f)). Qed.
Lemma lem69707 (f : ind -> ind) : (term186 f) = (term270 f).
Proof. exact (TRANS (@lem69626 f) (@lem69706 f)). Qed.
Lemma lem69708 (f : ind -> ind) : (term135 f) = (term270 f).
Proof. exact (TRANS (@lem69535 f) (@lem69707 f)). Qed.
Lemma lem69709 (f : ind -> ind) : (term64 f) = (term270 f).
Proof. exact (TRANS (@lem69261 f) (@lem69708 f)). Qed.
Lemma lem69710 (f : ind -> ind) (h1 : term64 f) : term270 f.
Proof. exact (EQ_MP (@lem69709 f) (@lem69077 f h1)). Qed.
Lemma lem69711 (x1 : ind) (f : ind -> ind) (h1 : term268 x1 f) : term268 x1 f.
Proof. exact (h1). Qed.
Lemma lem69712 (x1 : ind) (x2 : ind) (f : ind -> ind) (h1 : term266 x1 x2 f) : term266 x1 x2 f.
Proof. exact (h1). Qed.
Lemma lem69713 (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term263 x1 x2 f x) : term263 x1 x2 f x.
Proof. exact (h1). Qed.
Lemma lem69714 (y : ind) (f : ind -> ind) (h1 : term98 y f) : term98 y f.
Proof. exact (h1). Qed.
Lemma lem69723 (f : ind -> ind) (x : ind -> ind) (z : ind) : ((term208 f x z) = z) = ((term208 f x z) = z).
Proof. exact (eq_refl ((term208 f x z) = z)). Qed.
Lemma lem69724 (f : ind -> ind) (x : ind -> ind) : (term210 f x) = (term210 f x).
Proof. exact (fun_ext (fun z : ind => @lem69723 f x z)). Qed.
Lemma lem69725 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69726 (f : ind -> ind) (x : ind -> ind) : (term212 f x) = (term212 f x).
Proof. exact (MK_COMB (@lem69725) (@lem69724 f x)). Qed.
Lemma lem69769 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term245 f x1 x2) = (term245 f x1 x2).
Proof. exact (eq_refl (term245 f x1 x2)). Qed.
Lemma lem69770 (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) : (term263 x1 x2 f x) = (term263 x1 x2 f x).
Proof. exact (MK_COMB (@lem69769 f x1 x2) (@lem69726 f x)). Qed.
Lemma lem69771 (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term263 x1 x2 f x) : term263 x1 x2 f x.
Proof. exact (EQ_MP (@lem69770 x1 x2 f x) (@lem69713 x1 x2 f x h1)). Qed.
Lemma lem69780 (y : ind) (f : ind -> ind) (x : ind) : (term76 y f x) = (term76 y f x).
Proof. exact (eq_refl (term76 y f x)). Qed.
Lemma lem69781 (y : ind) (f : ind -> ind) : (term78 y f) = (term78 y f).
Proof. exact (fun_ext (fun x : ind => @lem69780 y f x)). Qed.
Lemma lem69782 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69783 (y : ind) (f : ind -> ind) : (term79 y f) = (term79 y f).
Proof. exact (MK_COMB (@lem69782) (@lem69781 y f)). Qed.
Lemma lem69802 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term65 f x1 x2) = (term65 f x1 x2).
Proof. exact (eq_refl (term65 f x1 x2)). Qed.
Lemma lem69803 (f : ind -> ind) (x1 : ind) : (term66 f x1) = (term66 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69802 f x1 x2)). Qed.
Lemma lem69804 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69805 (f : ind -> ind) (x1 : ind) : (term67 f x1) = (term67 f x1).
Proof. exact (MK_COMB (@lem69804) (@lem69803 f x1)). Qed.
Lemma lem69806 (f : ind -> ind) : (term68 f) = (term68 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69805 f x1)). Qed.
Lemma lem69807 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69808 (f : ind -> ind) : (term69 f) = (term69 f).
Proof. exact (MK_COMB (@lem69807) (@lem69806 f)). Qed.
Lemma lem69809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem69810 (f : ind -> ind) : (term88 f) = (term88 f).
Proof. exact (MK_COMB (@lem69809) (@lem69808 f)). Qed.
Lemma lem69811 (y : ind) (f : ind -> ind) : (term98 y f) = (term98 y f).
Proof. exact (MK_COMB (@lem69810 f) (@lem69783 y f)). Qed.
Lemma lem69812 (y : ind) (f : ind -> ind) (h1 : term98 y f) : term98 y f.
Proof. exact (EQ_MP (@lem69811 y f) (@lem69714 y f h1)). Qed.
Lemma lem69813 (y : ind) (f : ind -> ind) (h1 : term98 y f) : term79 y f.
Proof. exact (proj2 (@lem69812 y f h1)). Qed.
Lemma lem69814 (y : ind) (f : ind -> ind) (h1 : term98 y f) : term69 f.
Proof. exact (proj1 (@lem69812 y f h1)). Qed.
Lemma lem69815 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term103 f x1 x2) : term103 f x1 x2.
Proof. exact (h1). Qed.
Lemma lem69816 (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : term212 f x.
Proof. exact (h1). Qed.
Lemma lem69817 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term145 f x1 x2) : term145 f x1 x2.
Proof. exact (h1). Qed.
Lemma lem69818 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : term149 f x1 x2.
Proof. exact (h1). Qed.
Lemma lem69830 (f : ind -> ind) (x1 : ind) (x2 : ind) : (term65 f x1 x2) = (term65 f x1 x2).
Proof. exact (eq_refl (term65 f x1 x2)). Qed.
Lemma lem69831 (f : ind -> ind) (x1 : ind) : (term66 f x1) = (term66 f x1).
Proof. exact (fun_ext (fun x2 : ind => @lem69830 f x1 x2)). Qed.
Lemma lem69832 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69833 (f : ind -> ind) (x1 : ind) : (term67 f x1) = (term67 f x1).
Proof. exact (MK_COMB (@lem69832) (@lem69831 f x1)). Qed.
Lemma lem69834 (f : ind -> ind) : (term68 f) = (term68 f).
Proof. exact (fun_ext (fun x1 : ind => @lem69833 f x1)). Qed.
Lemma lem69835 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69837 (f : ind -> ind) : (term69 f) = (term69 f).
Proof. exact (MK_COMB (@lem69835) (@lem69834 f)). Qed.
Lemma lem69838 (y : ind) (f : ind -> ind) (h1 : term98 y f) : term69 f.
Proof. exact (EQ_MP (@lem69837 f) (@lem69814 y f h1)). Qed.
Lemma lem69902 (y : ind) (f : ind -> ind) (x : ind) : (term76 y f x) = (term76 y f x).
Proof. exact (eq_refl (term76 y f x)). Qed.
Lemma lem69903 (y : ind) (f : ind -> ind) : (term78 y f) = (term78 y f).
Proof. exact (fun_ext (fun x : ind => @lem69902 y f x)). Qed.
Lemma lem69904 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69906 (y : ind) (f : ind -> ind) : (term79 y f) = (term79 y f).
Proof. exact (MK_COMB (@lem69904) (@lem69903 y f)). Qed.
Lemma lem69907 (y : ind) (f : ind -> ind) (h1 : term98 y f) : term79 y f.
Proof. exact (EQ_MP (@lem69906 y f) (@lem69813 y f h1)). Qed.
Lemma lem69909 (f : ind -> ind) (x : ind -> ind) (z : ind) : ((term208 f x z) = z) = ((term208 f x z) = z).
Proof. exact (eq_refl ((term208 f x z) = z)). Qed.
Lemma lem69910 (f : ind -> ind) (x : ind -> ind) : (term210 f x) = (term210 f x).
Proof. exact (fun_ext (fun z : ind => @lem69909 f x z)). Qed.
Lemma lem69911 : (@all ind) = (@all ind).
Proof. exact (eq_refl (@all ind)). Qed.
Lemma lem69913 (f : ind -> ind) (x : ind -> ind) : (term212 f x) = (term212 f x).
Proof. exact (MK_COMB (@lem69911) (@lem69910 f x)). Qed.
Lemma lem69914 (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : term212 f x.
Proof. exact (EQ_MP (@lem69913 f x) (@lem69816 f x h1)). Qed.
Lemma lem69915 (_2074 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term271 f _2074.
Proof. exact (@lem69838 y f h1 _2074). Qed.
Lemma lem69916 (f : ind -> ind) (_2074 : ind) : (term271 f _2074) = (term67 f _2074).
Proof. exact (eq_refl (term271 f _2074)). Qed.
Lemma lem69917 (_2074 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term67 f _2074.
Proof. exact (EQ_MP (@lem69916 f _2074) (@lem69915 _2074 y f h1)). Qed.
Lemma lem69918 (_2074 : ind) (_2075 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term272 f _2074 _2075.
Proof. exact (@lem69917 _2074 y f h1 _2075). Qed.
Lemma lem69919 (f : ind -> ind) (_2074 : ind) (_2075 : ind) : (term272 f _2074 _2075) = (term65 f _2074 _2075).
Proof. exact (eq_refl (term272 f _2074 _2075)). Qed.
Lemma lem69939 (_2082 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term273 y f _2082.
Proof. exact (@lem69907 y f h1 _2082). Qed.
Lemma lem69940 (y : ind) (f : ind -> ind) (_2082 : ind) : (term273 y f _2082) = (term76 y f _2082).
Proof. exact (eq_refl (term273 y f _2082)). Qed.
Lemma lem69942 (_2083 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : term274 f x _2083.
Proof. exact (@lem69914 f x h1 _2083). Qed.
Lemma lem69943 (f : ind -> ind) (x : ind -> ind) (_2083 : ind) : (term274 f x _2083) = ((term208 f x _2083) = _2083).
Proof. exact (eq_refl (term274 f x _2083)). Qed.
Lemma lem69950 (_2074 : ind) (_2075 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term65 f _2074 _2075.
Proof. exact (EQ_MP (@lem69919 f _2074 _2075) (@lem69918 _2074 _2075 y f h1)). Qed.
Lemma lem69956 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term145 f x1 x2) : term275 x1 x2.
Proof. exact (proj2 (@lem69817 f x1 x2 h1)). Qed.
Lemma lem69966 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : term276 x1 f x2.
Proof. exact (proj1 (@lem69818 f x1 x2 h1)). Qed.
Lemma lem69968 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : x1 = x2.
Proof. exact (proj2 (@lem69818 f x1 x2 h1)). Qed.
Lemma lem69976 (_2082 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term76 y f _2082.
Proof. exact (EQ_MP (@lem69940 y f _2082) (@lem69939 _2082 y f h1)). Qed.
Lemma lem70021 (f : ind -> ind) (x2 : ind) : (term277 f x2) = (term277 f x2).
Proof. exact (eq_refl (term277 f x2)). Qed.
Lemma lem70022 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : (term278 f x2 x1) = (term279 f x2).
Proof. exact (MK_COMB (@lem70021 f x2) (@lem69968 f x1 x2 h1)). Qed.
Lemma lem70023 (f : ind -> ind) (x2 : ind) : (term279 f x2) = (term280 f x2).
Proof. exact (eq_refl (term279 f x2)). Qed.
Lemma lem70024 (f : ind -> ind) (x2 : ind) (x1 : ind) : (term281 f x2 x1) = (term281 f x2 x1).
Proof. exact (eq_refl (term281 f x2 x1)). Qed.
Lemma lem70025 (x1 : ind) (f : ind -> ind) (x2 : ind) : ((term278 f x2 x1) = (term279 f x2)) = ((term278 f x2 x1) = (term280 f x2)).
Proof. exact (MK_COMB (@lem70024 f x2 x1) (@lem70023 f x2)). Qed.
Lemma lem70026 (x1 : ind) (f : ind -> ind) (x2 : ind) : (term278 f x2 x1) = (term276 x1 f x2).
Proof. exact (eq_refl (term278 f x2 x1)). Qed.
Lemma lem70027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem70028 (x1 : ind) (f : ind -> ind) (x2 : ind) : (term281 f x2 x1) = (term282 x1 f x2).
Proof. exact (MK_COMB (@lem70027) (@lem70026 x1 f x2)). Qed.
Lemma lem70029 (f : ind -> ind) (x2 : ind) : (term280 f x2) = (term280 f x2).
Proof. exact (eq_refl (term280 f x2)). Qed.
Lemma lem70030 (x1 : ind) (f : ind -> ind) (x2 : ind) : ((term278 f x2 x1) = (term280 f x2)) = ((term276 x1 f x2) = (term280 f x2)).
Proof. exact (MK_COMB (@lem70028 x1 f x2) (@lem70029 f x2)). Qed.
Lemma lem70031 (x1 : ind) (f : ind -> ind) (x2 : ind) : ((term278 f x2 x1) = (term279 f x2)) = ((term276 x1 f x2) = (term280 f x2)).
Proof. exact (TRANS (@lem70025 x1 f x2) (@lem70030 x1 f x2)). Qed.
Lemma lem70032 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : (term276 x1 f x2) = (term280 f x2).
Proof. exact (EQ_MP (@lem70031 x1 f x2) (@lem70022 f x1 x2 h1)). Qed.
Lemma lem70033 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : term280 f x2.
Proof. exact (EQ_MP (@lem70032 f x1 x2 h1) (@lem69966 f x1 x2 h1)). Qed.
Lemma lem70045 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term145 f x1 x2) : (f x1) = (f x2).
Proof. exact (proj1 (@lem69817 f x1 x2 h1)). Qed.
Lemma lem70046 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term145 f x1 x2) : term283 x1 f x2.
Proof. exact (fun h0 : term276 x1 f x2 => @lem70045 f x1 x2 h1). Qed.
Lemma lem70048 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70049 (x1 : ind) (f : ind -> ind) (x2 : ind) : (term283 x1 f x2) = ((f x1) = (f x2)).
Proof. exact (@lem70048 ((f x1) = (f x2))). Qed.
Lemma lem70050 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term145 f x1 x2) : (f x1) = (f x2).
Proof. exact (EQ_MP (@lem70049 x1 f x2) (@lem70046 f x1 x2 h1)). Qed.
Lemma lem70056 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem70057 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : (term65 f _2074 _2075) = (term285 _2074 f _2075).
Proof. exact (@lem70056 (_2074 = _2075) (term276 _2074 f _2075)). Qed.
Lemma lem70067 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem70068 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : (term286 f _2074 _2075) = (term287 _2074 f _2075).
Proof. exact (MK_COMB (@lem70067) (@lem70057 _2074 f _2075)). Qed.
Lemma lem70078 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : (term285 _2074 f _2075) = (term285 _2074 f _2075).
Proof. exact (eq_refl (term285 _2074 f _2075)). Qed.
Lemma lem70079 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : ((term65 f _2074 _2075) = (term285 _2074 f _2075)) = ((term285 _2074 f _2075) = (term285 _2074 f _2075)).
Proof. exact (MK_COMB (@lem70068 _2074 f _2075) (@lem70078 _2074 f _2075)). Qed.
Lemma lem70081 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem70082 (x : Prop) : (x = x) = True.
Proof. exact (@lem70081 Prop x). Qed.
Lemma lem70083 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : ((term285 _2074 f _2075) = (term285 _2074 f _2075)) = True.
Proof. exact (@lem70082 (term285 _2074 f _2075)). Qed.
Lemma lem70084 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : ((term65 f _2074 _2075) = (term285 _2074 f _2075)) = True.
Proof. exact (TRANS (@lem70079 _2074 f _2075) (@lem70083 _2074 f _2075)). Qed.
Lemma lem70085 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : True = ((term65 f _2074 _2075) = (term285 _2074 f _2075)).
Proof. exact (SYM (@lem70084 _2074 f _2075)). Qed.
Lemma lem70086 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : (term65 f _2074 _2075) = (term285 _2074 f _2075).
Proof. exact (EQ_MP (@lem70085 _2074 f _2075) (@lem0)). Qed.
Lemma lem70087 (_2074 : ind) (_2075 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term285 _2074 f _2075.
Proof. exact (EQ_MP (@lem70086 _2074 f _2075) (@lem69950 _2074 _2075 y f h1)). Qed.
Lemma lem70089 (b : Prop) (a : Prop) : (a \/ b) = (term288 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem70090 (f : ind -> ind) (_2074 : ind) (_2075 : ind) : (term285 _2074 f _2075) = (term289 f _2074 _2075).
Proof. exact (@lem70089 (term276 _2074 f _2075) (_2074 = _2075)). Qed.
Lemma lem70092 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem70093 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : (term290 _2074 f _2075) = ((f _2074) = (f _2075)).
Proof. exact (@lem70092 ((f _2074) = (f _2075))). Qed.
Lemma lem70094 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem70095 (_2074 : ind) (f : ind -> ind) (_2075 : ind) : (term291 _2074 f _2075) = (term292 _2074 f _2075).
Proof. exact (MK_COMB (@lem70094) (@lem70093 _2074 f _2075)). Qed.
Lemma lem70096 (_2074 : ind) (_2075 : ind) : (_2074 = _2075) = (_2074 = _2075).
Proof. exact (eq_refl (_2074 = _2075)). Qed.
Lemma lem70097 (f : ind -> ind) (_2074 : ind) (_2075 : ind) : (term289 f _2074 _2075) = (term59 f _2074 _2075).
Proof. exact (MK_COMB (@lem70095 _2074 f _2075) (@lem70096 _2074 _2075)). Qed.
Lemma lem70098 (f : ind -> ind) (_2074 : ind) (_2075 : ind) : (term285 _2074 f _2075) = (term59 f _2074 _2075).
Proof. exact (TRANS (@lem70090 f _2074 _2075) (@lem70097 f _2074 _2075)). Qed.
Lemma lem70101 (_2074 : ind) (_2075 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term59 f _2074 _2075.
Proof. exact (EQ_MP (@lem70098 f _2074 _2075) (@lem70087 _2074 _2075 y f h1)). Qed.
Lemma lem70102 (x1 : ind) (x2 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term59 f x1 x2.
Proof. exact (@lem70101 x1 x2 y f h1). Qed.
Lemma lem70105 (y : ind) (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term98 y f) (h2 : term145 f x1 x2) : x1 = x2.
Proof. exact (@lem70102 x1 x2 y f h1 (@lem70050 f x1 x2 h2)). Qed.
Lemma lem70106 (y : ind) (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term98 y f) (h2 : term145 f x1 x2) : term293 x1 x2.
Proof. exact (fun h0 : term275 x1 x2 => @lem70105 y f x1 x2 h1 h2). Qed.
Lemma lem70108 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70109 (x1 : ind) (x2 : ind) : (term293 x1 x2) = (x1 = x2).
Proof. exact (@lem70108 (x1 = x2)). Qed.
Lemma lem70110 (y : ind) (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term98 y f) (h2 : term145 f x1 x2) : x1 = x2.
Proof. exact (EQ_MP (@lem70109 x1 x2) (@lem70106 y f x1 x2 h1 h2)). Qed.
Lemma lem70113 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem70115 (x1 : ind) (x2 : ind) : (term275 x1 x2) = (term294 x1 x2).
Proof. exact (@lem70113 (x1 = x2)). Qed.
Lemma lem70118 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term145 f x1 x2) : term294 x1 x2.
Proof. exact (EQ_MP (@lem70115 x1 x2) (@lem69956 f x1 x2 h1)). Qed.
Lemma lem70121 (y : ind) (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term98 y f) (h2 : term145 f x1 x2) : False.
Proof. exact (@lem70118 f x1 x2 h2 (@lem70110 y f x1 x2 h1 h2)). Qed.
Lemma lem70122 (y : ind) (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term98 y f) (h2 : term145 f x1 x2) : term295.
Proof. exact (fun h0 : ~ False => @lem70121 y f x1 x2 h1 h2). Qed.
Lemma lem70124 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70125 : term295 = False.
Proof. exact (@lem70124 False). Qed.
Lemma lem70126 (y : ind) (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term98 y f) (h2 : term145 f x1 x2) : False.
Proof. exact (EQ_MP (@lem70125) (@lem70122 y f x1 x2 h1 h2)). Qed.
Lemma lem70138 (x : ind) : x = x.
Proof. exact (@lem21386 ind x). Qed.
Lemma lem70139 (f : ind -> ind) (x2 : ind) : (f x2) = (f x2).
Proof. exact (@lem70138 (f x2)). Qed.
Lemma lem70140 (f : ind -> ind) (x2 : ind) : term296 f x2.
Proof. exact (fun h0 : term280 f x2 => @lem70139 f x2). Qed.
Lemma lem70142 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70143 (f : ind -> ind) (x2 : ind) : (term296 f x2) = ((f x2) = (f x2)).
Proof. exact (@lem70142 ((f x2) = (f x2))). Qed.
Lemma lem70144 (f : ind -> ind) (x2 : ind) : (f x2) = (f x2).
Proof. exact (EQ_MP (@lem70143 f x2) (@lem70140 f x2)). Qed.
Lemma lem70147 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem70149 (f : ind -> ind) (x2 : ind) : (term280 f x2) = (term297 f x2).
Proof. exact (@lem70147 ((f x2) = (f x2))). Qed.
Lemma lem70152 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : term297 f x2.
Proof. exact (EQ_MP (@lem70149 f x2) (@lem70033 f x1 x2 h1)). Qed.
Lemma lem70155 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : False.
Proof. exact (@lem70152 f x1 x2 h1 (@lem70144 f x2)). Qed.
Lemma lem70156 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : term295.
Proof. exact (fun h0 : ~ False => @lem70155 f x1 x2 h1). Qed.
Lemma lem70158 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70159 : term295 = False.
Proof. exact (@lem70158 False). Qed.
Lemma lem70178 (x : ind) (y : ind) (z : ind) : term298 x y z.
Proof. exact (@lem21385 ind x y z). Qed.
Lemma lem70180 (_2083 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : (term208 f x _2083) = _2083.
Proof. exact (EQ_MP (@lem69943 f x _2083) (@lem69942 _2083 f x h1)). Qed.
Lemma lem70181 (y : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : (term208 f x y) = y.
Proof. exact (@lem70180 y f x h1). Qed.
Lemma lem70182 (y : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : term299 f x y.
Proof. exact (fun h0 : term300 f x y => @lem70181 y f x h1). Qed.
Lemma lem70184 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70185 (f : ind -> ind) (x : ind -> ind) (y : ind) : (term299 f x y) = ((term208 f x y) = y).
Proof. exact (@lem70184 ((term208 f x y) = y)). Qed.
Lemma lem70186 (y : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : (term208 f x y) = y.
Proof. exact (EQ_MP (@lem70185 f x y) (@lem70182 y f x h1)). Qed.
Lemma lem70188 (x : ind) : x = x.
Proof. exact (@lem21386 ind x). Qed.
Lemma lem70189 (f : ind -> ind) (x : ind -> ind) (y : ind) : (term208 f x y) = (term208 f x y).
Proof. exact (@lem70188 (term208 f x y)). Qed.
Lemma lem70190 (f : ind -> ind) (x : ind -> ind) (y : ind) : term301 f x y.
Proof. exact (fun h0 : term302 f x y => @lem70189 f x y). Qed.
Lemma lem70192 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70193 (f : ind -> ind) (x : ind -> ind) (y : ind) : (term301 f x y) = ((term208 f x y) = (term208 f x y)).
Proof. exact (@lem70192 ((term208 f x y) = (term208 f x y))). Qed.
Lemma lem70194 (f : ind -> ind) (x : ind -> ind) (y : ind) : (term208 f x y) = (term208 f x y).
Proof. exact (EQ_MP (@lem70193 f x y) (@lem70190 f x y)). Qed.
Lemma lem70212 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem70213 (y : ind) (x : ind) (z : ind) : (term303 x y z) = (term304 y x z).
Proof. exact (@lem70212 (y = z) (term275 x z)). Qed.
Lemma lem70223 (x : ind) (y : ind) : (term305 x y) = (term305 x y).
Proof. exact (eq_refl (term305 x y)). Qed.
Lemma lem70224 (y : ind) (x : ind) (z : ind) : (term298 x y z) = (term306 y x z).
Proof. exact (MK_COMB (@lem70223 x y) (@lem70213 y x z)). Qed.
Lemma lem70228 (q : Prop) (p : Prop) (r : Prop) : (term307 p q r) = (term307 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem70229 (y : ind) (x : ind) (z : ind) : (term306 y x z) = (term308 y x z).
Proof. exact (@lem70228 (y = z) (term275 x y) (term275 x z)). Qed.
Lemma lem70251 (y : ind) (x : ind) (z : ind) : (term298 x y z) = (term308 y x z).
Proof. exact (TRANS (@lem70224 y x z) (@lem70229 y x z)). Qed.
Lemma lem70252 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem70253 (y : ind) (x : ind) (z : ind) : (term309 x y z) = (term310 y x z).
Proof. exact (MK_COMB (@lem70252) (@lem70251 y x z)). Qed.
Lemma lem70275 (y : ind) (x : ind) (z : ind) : (term308 y x z) = (term308 y x z).
Proof. exact (eq_refl (term308 y x z)). Qed.
Lemma lem70276 (y : ind) (x : ind) (z : ind) : ((term298 x y z) = (term308 y x z)) = ((term308 y x z) = (term308 y x z)).
Proof. exact (MK_COMB (@lem70253 y x z) (@lem70275 y x z)). Qed.
Lemma lem70278 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem70279 (x : Prop) : (x = x) = True.
Proof. exact (@lem70278 Prop x). Qed.
Lemma lem70280 (y : ind) (x : ind) (z : ind) : ((term308 y x z) = (term308 y x z)) = True.
Proof. exact (@lem70279 (term308 y x z)). Qed.
Lemma lem70281 (y : ind) (x : ind) (z : ind) : ((term298 x y z) = (term308 y x z)) = True.
Proof. exact (TRANS (@lem70276 y x z) (@lem70280 y x z)). Qed.
Lemma lem70282 (y : ind) (x : ind) (z : ind) : True = ((term298 x y z) = (term308 y x z)).
Proof. exact (SYM (@lem70281 y x z)). Qed.
Lemma lem70283 (y : ind) (x : ind) (z : ind) : (term298 x y z) = (term308 y x z).
Proof. exact (EQ_MP (@lem70282 y x z) (@lem0)). Qed.
Lemma lem70284 (y : ind) (x : ind) (z : ind) : term308 y x z.
Proof. exact (EQ_MP (@lem70283 y x z) (@lem70178 x y z)). Qed.
Lemma lem70286 (b : Prop) (a : Prop) : (a \/ b) = (term288 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem70287 (x : ind) (y : ind) (z : ind) : (term308 y x z) = (term311 x y z).
Proof. exact (@lem70286 (term312 y x z) (y = z)). Qed.
Lemma lem70289 (a : Prop) (b : Prop) : (term313 a b) = (term314 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem70290 (y : ind) (x : ind) (z : ind) : (term315 y x z) = (term316 y x z).
Proof. exact (@lem70289 (term275 x y) (term275 x z)). Qed.
Lemma lem70292 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem70293 (x : ind) (y : ind) : (term317 x y) = (x = y).
Proof. exact (@lem70292 (x = y)). Qed.
Lemma lem70294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem70295 (x : ind) (y : ind) : (term318 x y) = (term319 x y).
Proof. exact (MK_COMB (@lem70294) (@lem70293 x y)). Qed.
Lemma lem70297 (a : Prop) : (term24 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem70298 (x : ind) (z : ind) : (term317 x z) = (x = z).
Proof. exact (@lem70297 (x = z)). Qed.
Lemma lem70299 (y : ind) (x : ind) (z : ind) : (term316 y x z) = (term320 y x z).
Proof. exact (MK_COMB (@lem70295 x y) (@lem70298 x z)). Qed.
Lemma lem70300 (y : ind) (x : ind) (z : ind) : (term315 y x z) = (term320 y x z).
Proof. exact (TRANS (@lem70290 y x z) (@lem70299 y x z)). Qed.
Lemma lem70301 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem70302 (y : ind) (x : ind) (z : ind) : (term321 y x z) = (term322 y x z).
Proof. exact (MK_COMB (@lem70301) (@lem70300 y x z)). Qed.
Lemma lem70303 (y : ind) (z : ind) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem70304 (x : ind) (y : ind) (z : ind) : (term311 x y z) = (term323 x y z).
Proof. exact (MK_COMB (@lem70302 y x z) (@lem70303 y z)). Qed.
Lemma lem70305 (x : ind) (y : ind) (z : ind) : (term308 y x z) = (term323 x y z).
Proof. exact (TRANS (@lem70287 x y z) (@lem70304 x y z)). Qed.
Lemma lem70307 (y : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : term324 f x y.
Proof. exact (conj (@lem70186 y f x h1) (@lem70194 f x y)). Qed.
Lemma lem70309 (x : ind) (y : ind) (z : ind) : term323 x y z.
Proof. exact (EQ_MP (@lem70305 x y z) (@lem70284 y x z)). Qed.
Lemma lem70310 (f : ind -> ind) (x : ind -> ind) (y : ind) : term325 f x y.
Proof. exact (@lem70309 (term208 f x y) y (term208 f x y)). Qed.
Lemma lem70313 (y : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : y = (term208 f x y).
Proof. exact (@lem70310 f x y (@lem70307 y f x h1)). Qed.
Lemma lem70314 (y : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : term326 f x y.
Proof. exact (fun h0 : term327 f x y => @lem70313 y f x h1). Qed.
Lemma lem70316 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70317 (f : ind -> ind) (x : ind -> ind) (y : ind) : (term326 f x y) = (y = (term208 f x y)).
Proof. exact (@lem70316 (y = (term208 f x y))). Qed.
Lemma lem70318 (y : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term212 f x) : y = (term208 f x y).
Proof. exact (EQ_MP (@lem70317 f x y) (@lem70314 y f x h1)). Qed.
Lemma lem70321 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem70323 (y : ind) (f : ind -> ind) (_2082 : ind) : (term76 y f _2082) = (term328 y f _2082).
Proof. exact (@lem70321 (y = (f _2082))). Qed.
Lemma lem70326 (_2082 : ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term328 y f _2082.
Proof. exact (EQ_MP (@lem70323 y f _2082) (@lem69976 _2082 y f h1)). Qed.
Lemma lem70327 (x : ind -> ind) (y : ind) (f : ind -> ind) (h1 : term98 y f) : term329 f x y.
Proof. exact (@lem70326 (x y) y f h1). Qed.
Lemma lem70330 (x : ind -> ind) (y : ind) (f : ind -> ind) (h1 : term212 f x) (h2 : term98 y f) : False.
Proof. exact (@lem70327 x y f h2 (@lem70318 y f x h1)). Qed.
Lemma lem70331 (x : ind -> ind) (y : ind) (f : ind -> ind) (h1 : term212 f x) (h2 : term98 y f) : term295.
Proof. exact (fun h0 : ~ False => @lem70330 x y f h1 h2). Qed.
Lemma lem70333 (p : Prop) : (term284 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem70334 : term295 = False.
Proof. exact (@lem70333 False). Qed.
Lemma lem70335 (x : ind -> ind) (y : ind) (f : ind -> ind) (h1 : term212 f x) (h2 : term98 y f) : False.
Proof. exact (EQ_MP (@lem70334) (@lem70331 x y f h1 h2)). Qed.
Lemma lem70336 (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term149 f x1 x2) : False.
Proof. exact (EQ_MP (@lem70159) (@lem70156 f x1 x2 h1)). Qed.
Lemma lem70337 (x : ind -> ind) (y : ind) (f : ind -> ind) (h1 : term212 f x) (h2 : term98 y f) : (term212 f x) = False.
Proof. exact (prop_ext (fun h3 : term212 f x => @lem70335 x y f h1 h2) (fun h3 : False => @lem69914 f x h1)). Qed.
Lemma lem70338 (x : ind -> ind) (y : ind) (f : ind -> ind) (h1 : term212 f x) (h2 : term98 y f) : False.
Proof. exact (EQ_MP (@lem70337 x y f h1 h2) (@lem69914 f x h1)). Qed.
Lemma lem70339 (y : ind) (f : ind -> ind) (x1 : ind) (x2 : ind) (h1 : term98 y f) (h2 : term103 f x1 x2) : False.
Proof. exact (or_elim (@lem69815 f x1 x2 h2) (fun h0 : term145 f x1 x2 => @lem70126 y f x1 x2 h1 h0) (fun h0 : term149 f x1 x2 => @lem70336 f x1 x2 h0)). Qed.
Lemma lem70340 (y : ind) (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term98 y f) (h2 : term263 x1 x2 f x) : False.
Proof. exact (or_elim (@lem69771 x1 x2 f x h2) (fun h0 : term103 f x1 x2 => @lem70339 y f x1 x2 h1 h0) (fun h0 : term212 f x => @lem70338 x y f h0 h1)). Qed.
Lemma lem70341 (y : ind) (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term98 y f) (h2 : term263 x1 x2 f x) : (term98 y f) = False.
Proof. exact (prop_ext (fun h3 : term98 y f => @lem70340 y x1 x2 f x h1 h2) (fun h3 : False => @lem69812 y f h1)). Qed.
Lemma lem70342 (y : ind) (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term98 y f) (h2 : term263 x1 x2 f x) : False.
Proof. exact (EQ_MP (@lem70341 y x1 x2 f x h1 h2) (@lem69812 y f h1)). Qed.
Lemma lem70343 (y : ind) (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term98 y f) (h2 : term263 x1 x2 f x) : (term263 x1 x2 f x) = False.
Proof. exact (prop_ext (fun h3 : term263 x1 x2 f x => @lem70342 y x1 x2 f x h1 h2) (fun h3 : False => @lem69771 x1 x2 f x h2)). Qed.
Lemma lem70344 (y : ind) (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term98 y f) (h2 : term263 x1 x2 f x) : False.
Proof. exact (EQ_MP (@lem70343 y x1 x2 f x h1 h2) (@lem69771 x1 x2 f x h2)). Qed.
Lemma lem70345 (x1 : ind) (x2 : ind) (f : ind -> ind) (x : ind -> ind) (h1 : term11 f) (h2 : term263 x1 x2 f x) : False.
Proof. exact (ex_elim (@lem69198 f h1) (fun y : ind => fun h0 : term100 f y => @lem70344 y x1 x2 f x h0 h2)). Qed.
Lemma lem70346 (x1 : ind) (x2 : ind) (f : ind -> ind) (h1 : term266 x1 x2 f) (h2 : term11 f) : False.
Proof. exact (ex_elim (@lem69712 x1 x2 f h1) (fun x : ind -> ind => fun h0 : term265 x1 x2 f x => @lem70345 x1 x2 f x h2 h0)). Qed.
Lemma lem70347 (x1 : ind) (f : ind -> ind) (h1 : term268 x1 f) (h2 : term11 f) : False.
Proof. exact (ex_elim (@lem69711 x1 f h1) (fun x2 : ind => fun h0 : term267 x1 f x2 => @lem70346 x1 x2 f h0 h2)). Qed.
Lemma lem70348 (f : ind -> ind) (h1 : term64 f) (h2 : term11 f) : False.
Proof. exact (ex_elim (@lem69710 f h1) (fun x1 : ind => fun h0 : term269 f x1 => @lem70347 x1 f h0 h2)). Qed.
Lemma lem70349 (f : ind -> ind) (h1 : term64 f) (h2 : term11 f) : (term64 f) = False.
Proof. exact (prop_ext (fun h3 : term64 f => @lem70348 f h1 h2) (fun h3 : False => @lem69077 f h1)). Qed.
Lemma lem70350 (f : ind -> ind) (h1 : term64 f) (h2 : term11 f) : False.
Proof. exact (EQ_MP (@lem70349 f h1 h2) (@lem69077 f h1)). Qed.
Lemma lem70351 (f : ind -> ind) (h1 : term11 f) : term63 f.
Proof. exact (fun h0 : term64 f => @lem70350 f h0 h1). Qed.
Lemma lem70352 (f : ind -> ind) (h1 : term11 f) : term45 f.
Proof. exact (EQ_MP (@lem69076 f) (@lem70351 f h1)). Qed.
Lemma lem70353 (f : ind -> ind) : term46 f.
Proof. exact (fun h0 : term11 f => @lem70352 f h0). Qed.
Lemma lem70358 : term50.
Proof. exact (fun f : ind -> ind => @lem70353 f). Qed.
Lemma lem70359 : term49.
Proof. exact (EQ_MP (@lem69071) (@lem70358)). Qed.
Lemma lem70360 (f : ind -> ind) : term330 f.
Proof. exact (@lem70359 f). Qed.
Lemma lem70361 (f : ind -> ind) : (term330 f) = (term18 f).
Proof. exact (eq_refl (term330 f)). Qed.
Lemma lem70362 (f : ind -> ind) : term18 f.
Proof. exact (EQ_MP (@lem70361 f) (@lem70360 f)). Qed.
Lemma lem70364 (f : ind -> ind) : term18 f.
Proof. exact (@lem68866 f (@lem70362 f)). Qed.
Lemma lem70365 (f : ind -> ind) (h1 : term19 f) : False.
Proof. exact (@lem70364 f (@lem68851 f h1)). Qed.
Lemma lem70366 (f : ind -> ind) (h1 : term19 f) : (term19 f) = False.
Proof. exact (prop_ext (fun h2 : term19 f => @lem70365 f h1) (fun h2 : False => @lem68851 f h1)). Qed.
Lemma lem70367 (f : ind -> ind) (h1 : term19 f) : False.
Proof. exact (EQ_MP (@lem70366 f h1) (@lem68851 f h1)). Qed.
Lemma lem70368 (f : ind -> ind) : term18 f.
Proof. exact (fun h0 : term19 f => @lem70367 f h0). Qed.
Lemma lem70369 (f : ind -> ind) : term16 f.
Proof. exact (EQ_MP (@lem68850 f) (@lem70368 f)). Qed.
Lemma lem70370 (f : ind -> ind) : term15 f.
Proof. exact (EQ_MP (@lem68846 f) (@lem70369 f)). Qed.
Lemma lem70371 (f : ind -> ind) (h1 : term4 f) : term14 f.
Proof. exact (@lem70370 f (@lem68770 f h1)). Qed.
Lemma lem70372 (f : ind -> ind) (h1 : term4 f) : term331.
Proof. exact (ex_intro term332 f (@lem70371 f h1)). Qed.
Lemma lem70373 : term331.
Proof. exact (ex_elim (@lem68753) (fun f : ind -> ind => fun h0 : term333 f => @lem70372 f h0)). Qed.
