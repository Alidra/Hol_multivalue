Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SUM_POS_LT_ALL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import REAL_LT_IMP_LE_spec.
Require Import SUM_POS_LT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17784_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
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
Lemma lem7078806 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7078807 {A : Type'} (f : A -> real) (h1 : term0 A) : term1 A f.
Proof. exact (@lem7078806 A h1 f). Qed.
Lemma lem7078808 {A : Type'} (f : A -> real) : (term1 A f) = (term2 A f).
Proof. exact (eq_refl (term1 A f)). Qed.
Lemma lem7078809 {A : Type'} (f : A -> real) (h1 : term0 A) : term2 A f.
Proof. exact (EQ_MP (@lem7078808 A f) (@lem7078807 A f h1)). Qed.
Lemma lem7078810 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term0 A) : term3 A f s.
Proof. exact (@lem7078809 A f h1 s). Qed.
Lemma lem7078811 {A : Type'} (s : A -> Prop) (f : A -> real) : (term3 A f s) = (term4 A s f).
Proof. exact (eq_refl (term3 A f s)). Qed.
Lemma lem7078812 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A) : term4 A s f.
Proof. exact (EQ_MP (@lem7078811 A s f) (@lem7078810 A f s h1)). Qed.
Lemma lem7078813 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term5 A s f) : term5 A s f.
Proof. exact (h1). Qed.
Lemma lem7078814 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A) (h2 : term5 A s f) : term6 A s f.
Proof. exact (@lem7078812 A s f h1 (@lem7078813 A s f h2)). Qed.
Lemma lem7078815 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term5 A s f) : term7 A s f.
Proof. exact (fun h0 : term0 A => @lem7078814 A s f h0 h1). Qed.
Lemma lem7078816 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem7078817 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A) (h2 : term5 A s f) : term6 A s f.
Proof. exact (@lem7078815 A s f h2 (@lem7078816 A h1)). Qed.
Lemma lem7078818 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term0 A) : term4 A s f.
Proof. exact (fun h0 : term5 A s f => @lem7078817 A s f h1 h0). Qed.
Lemma lem7078819 {A : Type'} (s : A -> Prop) (h1 : term0 A) : term8 A s.
Proof. exact (fun f : A -> real => @lem7078818 A s f h1). Qed.
Lemma lem7078820 {A : Type'} (h1 : term0 A) : term9 A.
Proof. exact (fun s : A -> Prop => @lem7078819 A s h1). Qed.
Lemma lem7078821 {A : Type'} : term10 A.
Proof. exact (fun h0 : term0 A => @lem7078820 A h0). Qed.
Lemma lem7078822 {A : Type'} : term9 A.
Proof. exact (@lem7078821 A (@lem7078795 A)). Qed.
Lemma lem7078823 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (@lem7078822 A s). Qed.
Lemma lem7078824 {A : Type'} (s : A -> Prop) : (term11 A s) = (term8 A s).
Proof. exact (eq_refl (term11 A s)). Qed.
Lemma lem7078825 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem7078824 A s) (@lem7078823 A s)). Qed.
Lemma lem7078826 {A : Type'} (s : A -> Prop) (f : A -> real) : term12 A s f.
Proof. exact (@lem7078825 A s f). Qed.
Lemma lem7078827 {A : Type'} (s : A -> Prop) (f : A -> real) : (term12 A s f) = (term4 A s f).
Proof. exact (eq_refl (term12 A s f)). Qed.
Lemma lem7078829 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term13 A s f) : term13 A s f.
Proof. exact (h1). Qed.
Lemma lem7078830 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term14 A s f) : term14 A s f.
Proof. exact (h1). Qed.
Lemma lem7078831 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7078832 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term15 A s f.
Proof. exact (h1). Qed.
Lemma lem7078833 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem7078835 {A : Type'} (s : A -> Prop) (f : A -> real) : term4 A s f.
Proof. exact (EQ_MP (@lem7078827 A s f) (@lem7078826 A s f)). Qed.
Lemma lem7078836 {A : Type'} (s : A -> Prop) (f : A -> real) : term4 A s f.
Proof. exact (@lem7078835 A s f). Qed.
Lemma lem7078838 (p : Prop) : p = (term17 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem7078839 {A : Type'} (s : A -> Prop) (f : A -> real) : (term5 A s f) = (term18 A s f).
Proof. exact (@lem7078838 (term5 A s f)). Qed.
Lemma lem7078840 {A : Type'} (s : A -> Prop) (f : A -> real) : (term18 A s f) = (term5 A s f).
Proof. exact (SYM (@lem7078839 A s f)). Qed.
Lemma lem7078841 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term19 A s f) : term19 A s f.
Proof. exact (h1). Qed.
Lemma lem7078842 {A : Type'} : term20 A.
Proof. exact (@lem3216368 A). Qed.
Lemma lem7078847 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term21 A s f.
Proof. exact (h1). Qed.
Lemma lem7078848 {A : Type'} (s : A -> Prop) (f : A -> real) : term22 A s f.
Proof. exact (fun h0 : term21 A s f => @lem7078847 A s f h0). Qed.
Lemma lem7078849 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term22 A s f) : term22 A s f.
Proof. exact (h1). Qed.
Lemma lem7078850 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term21 A s f.
Proof. exact (h1). Qed.
Lemma lem7078851 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) (h2 : term22 A s f) : term21 A s f.
Proof. exact (@lem7078849 A s f h2 (@lem7078850 A s f h1)). Qed.
Lemma lem7078852 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) : term23 A s f.
Proof. exact (fun h0 : term22 A s f => @lem7078851 A s f h1 h0). Qed.
Lemma lem7078853 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term22 A s f) : term22 A s f.
Proof. exact (h1). Qed.
Lemma lem7078854 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term21 A s f) (h2 : term22 A s f) : term21 A s f.
Proof. exact (@lem7078852 A s f h1 (@lem7078853 A s f h2)). Qed.
Lemma lem7078855 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term22 A s f) : term22 A s f.
Proof. exact (fun h0 : term21 A s f => @lem7078854 A s f h0 h1). Qed.
Lemma lem7078856 {A : Type'} (s : A -> Prop) (f : A -> real) : term24 A s f.
Proof. exact (fun h0 : term22 A s f => @lem7078855 A s f h0). Qed.
Lemma lem7078859 {A : Type'} (s : A -> Prop) (f : A -> real) : term22 A s f.
Proof. exact (@lem7078856 A s f (@lem7078848 A s f)). Qed.
Lemma lem7078860 {A : Type'} (s : A -> Prop) (f : A -> real) : term22 A s f.
Proof. exact (@lem7078859 A s f). Qed.
Lemma lem7078956 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem7078957 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem7078956 (term20 A)). Qed.
Lemma lem7078966 : term27 = term27.
Proof. exact (eq_refl term27). Qed.
Lemma lem7078967 {A : Type'} : (term28 A) = (term29 A).
Proof. exact (MK_COMB (@lem7078966) (@lem7078957 A)). Qed.
Lemma lem7078970 {A : Type'} (s : A -> Prop) (f : A -> real) : (term30 A s f) = (term30 A s f).
Proof. exact (eq_refl (term30 A s f)). Qed.
Lemma lem7078971 {A : Type'} (s : A -> Prop) (f : A -> real) : (term31 A s f) = (term32 A s f).
Proof. exact (MK_COMB (@lem7078970 A s f) (@lem7078967 A)). Qed.
Lemma lem7078974 {A : Type'} (s : A -> Prop) (f : A -> real) : (term33 A s f) = (term33 A s f).
Proof. exact (eq_refl (term33 A s f)). Qed.
Lemma lem7078975 {A : Type'} (s : A -> Prop) (f : A -> real) : (term34 A s f) = (term35 A s f).
Proof. exact (MK_COMB (@lem7078974 A s f) (@lem7078971 A s f)). Qed.
Lemma lem7078978 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (eq_refl (term36 A s)). Qed.
Lemma lem7078979 {A : Type'} (s : A -> Prop) (f : A -> real) : (term37 A s f) = (term38 A s f).
Proof. exact (MK_COMB (@lem7078978 A s) (@lem7078975 A s f)). Qed.
Lemma lem7078982 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem7078983 {A : Type'} (s : A -> Prop) (f : A -> real) : (term21 A s f) = (term40 A s f).
Proof. exact (MK_COMB (@lem7078982 A s) (@lem7078979 A s f)). Qed.
Lemma lem7078986 {A : Type'} (f : A -> real) : (term41 A f) = (term42 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7078983 A s f)). Qed.
Lemma lem7078987 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7078988 {A : Type'} (f : A -> real) : (term43 A f) = (term44 A f).
Proof. exact (MK_COMB (@lem7078987 A) (@lem7078986 A f)). Qed.
Lemma lem7078993 {A : Type'} : (term45 A) = (term46 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7078988 A f)). Qed.
Lemma lem7078994 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7079003 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (MK_COMB (@lem7078994 A) (@lem7078993 A)). Qed.
Lemma lem7079006 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem7079007 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7079008 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun x : A => @lem7079007 A x s)). Qed.
Lemma lem7079009 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079010 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem7079009 A) (@lem7079008 A s)). Qed.
Lemma lem7079011 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7079012 {A : Type'} (s : A -> Prop) : (term51 A s) = (term51 A s).
Proof. exact (MK_COMB (@lem7079011) (@lem7079010 A s)). Qed.
Lemma lem7079013 {A : Type'} (s : A -> Prop) : ((term50 A s) = (term16 A s)) = ((term50 A s) = (term16 A s)).
Proof. exact (MK_COMB (@lem7079012 A s) (@lem7079006 A s)). Qed.
Lemma lem7079014 {A : Type'} : (term52 A) = (term52 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079013 A s)). Qed.
Lemma lem7079015 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079016 {A : Type'} : (term20 A) = (term20 A).
Proof. exact (MK_COMB (@lem7079015 A) (@lem7079014 A)). Qed.
Lemma lem7079017 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7079018 {A : Type'} : (term26 A) = (term26 A).
Proof. exact (MK_COMB (@lem7079017) (@lem7079016 A)). Qed.
Lemma lem7079023 (x : real) (y : real) : (term53 x y) = (term53 x y).
Proof. exact (eq_refl (term53 x y)). Qed.
Lemma lem7079024 (x : real) : (term54 x) = (term54 x).
Proof. exact (fun_ext (fun y : real => @lem7079023 x y)). Qed.
Lemma lem7079025 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7079026 (x : real) : (term55 x) = (term55 x).
Proof. exact (MK_COMB (@lem7079025) (@lem7079024 x)). Qed.
Lemma lem7079027 : term56 = term56.
Proof. exact (fun_ext (fun x : real => @lem7079026 x)). Qed.
Lemma lem7079028 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7079029 : term57 = term57.
Proof. exact (MK_COMB (@lem7079028) (@lem7079027)). Qed.
Lemma lem7079030 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7079031 : term27 = term27.
Proof. exact (MK_COMB (@lem7079030) (@lem7079029)). Qed.
Lemma lem7079032 {A : Type'} : (term29 A) = (term29 A).
Proof. exact (MK_COMB (@lem7079031) (@lem7079018 A)). Qed.
Lemma lem7079037 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term58 A s f x) = (term58 A s f x).
Proof. exact (eq_refl (term58 A s f x)). Qed.
Lemma lem7079038 {A : Type'} (s : A -> Prop) (f : A -> real) : (term59 A s f) = (term59 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079037 A s f x)). Qed.
Lemma lem7079039 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079040 {A : Type'} (s : A -> Prop) (f : A -> real) : (term60 A s f) = (term60 A s f).
Proof. exact (MK_COMB (@lem7079039 A) (@lem7079038 A s f)). Qed.
Lemma lem7079045 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term61 A s f x) = (term61 A s f x).
Proof. exact (eq_refl (term61 A s f x)). Qed.
Lemma lem7079046 {A : Type'} (s : A -> Prop) (f : A -> real) : (term62 A s f) = (term62 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079045 A s f x)). Qed.
Lemma lem7079047 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079048 {A : Type'} (s : A -> Prop) (f : A -> real) : (term63 A s f) = (term63 A s f).
Proof. exact (MK_COMB (@lem7079047 A) (@lem7079046 A s f)). Qed.
Lemma lem7079049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079050 {A : Type'} (s : A -> Prop) (f : A -> real) : (term64 A s f) = (term64 A s f).
Proof. exact (MK_COMB (@lem7079049) (@lem7079048 A s f)). Qed.
Lemma lem7079051 {A : Type'} (s : A -> Prop) (f : A -> real) : (term65 A s f) = (term65 A s f).
Proof. exact (MK_COMB (@lem7079050 A s f) (@lem7079040 A s f)). Qed.
Lemma lem7079054 {A : Type'} (s : A -> Prop) : (term66 A s) = (term66 A s).
Proof. exact (eq_refl (term66 A s)). Qed.
Lemma lem7079055 {A : Type'} (s : A -> Prop) (f : A -> real) : (term5 A s f) = (term5 A s f).
Proof. exact (MK_COMB (@lem7079054 A s) (@lem7079051 A s f)). Qed.
Lemma lem7079056 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7079057 {A : Type'} (s : A -> Prop) (f : A -> real) : (term19 A s f) = (term19 A s f).
Proof. exact (MK_COMB (@lem7079056) (@lem7079055 A s f)). Qed.
Lemma lem7079058 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7079059 {A : Type'} (s : A -> Prop) (f : A -> real) : (term30 A s f) = (term30 A s f).
Proof. exact (MK_COMB (@lem7079058) (@lem7079057 A s f)). Qed.
Lemma lem7079060 {A : Type'} (s : A -> Prop) (f : A -> real) : (term32 A s f) = (term32 A s f).
Proof. exact (MK_COMB (@lem7079059 A s f) (@lem7079032 A)). Qed.
Lemma lem7079065 {A : Type'} (s : A -> Prop) (f : A -> real) (i : A) : (term67 A s f i) = (term67 A s f i).
Proof. exact (eq_refl (term67 A s f i)). Qed.
Lemma lem7079066 {A : Type'} (s : A -> Prop) (f : A -> real) : (term68 A s f) = (term68 A s f).
Proof. exact (fun_ext (fun i : A => @lem7079065 A s f i)). Qed.
Lemma lem7079067 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079068 {A : Type'} (s : A -> Prop) (f : A -> real) : (term15 A s f) = (term15 A s f).
Proof. exact (MK_COMB (@lem7079067 A) (@lem7079066 A s f)). Qed.
Lemma lem7079069 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7079070 {A : Type'} (s : A -> Prop) (f : A -> real) : (term33 A s f) = (term33 A s f).
Proof. exact (MK_COMB (@lem7079069) (@lem7079068 A s f)). Qed.
Lemma lem7079071 {A : Type'} (s : A -> Prop) (f : A -> real) : (term35 A s f) = (term35 A s f).
Proof. exact (MK_COMB (@lem7079070 A s f) (@lem7079060 A s f)). Qed.
Lemma lem7079076 {A : Type'} (s : A -> Prop) : (term36 A s) = (term36 A s).
Proof. exact (eq_refl (term36 A s)). Qed.
Lemma lem7079077 {A : Type'} (s : A -> Prop) (f : A -> real) : (term38 A s f) = (term38 A s f).
Proof. exact (MK_COMB (@lem7079076 A s) (@lem7079071 A s f)). Qed.
Lemma lem7079080 {A : Type'} (s : A -> Prop) : (term39 A s) = (term39 A s).
Proof. exact (eq_refl (term39 A s)). Qed.
Lemma lem7079081 {A : Type'} (s : A -> Prop) (f : A -> real) : (term40 A s f) = (term40 A s f).
Proof. exact (MK_COMB (@lem7079080 A s) (@lem7079077 A s f)). Qed.
Lemma lem7079082 {A : Type'} (f : A -> real) : (term42 A f) = (term42 A f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079081 A s f)). Qed.
Lemma lem7079083 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079084 {A : Type'} (f : A -> real) : (term44 A f) = (term44 A f).
Proof. exact (MK_COMB (@lem7079083 A) (@lem7079082 A f)). Qed.
Lemma lem7079085 {A : Type'} : (term46 A) = (term46 A).
Proof. exact (fun_ext (fun f : A -> real => @lem7079084 A f)). Qed.
Lemma lem7079086 {A : Type'} : (@all (A -> real)) = (@all (A -> real)).
Proof. exact (eq_refl (@all (A -> real))). Qed.
Lemma lem7079087 {A : Type'} : (term48 A) = (term48 A).
Proof. exact (MK_COMB (@lem7079086 A) (@lem7079085 A)). Qed.
Lemma lem7079166 {A : Type'} : (term47 A) = (term48 A).
Proof. exact (TRANS (@lem7079003 A) (@lem7079087 A)). Qed.
Lemma lem7079167 {A : Type'} : (term48 A) = (term47 A).
Proof. exact (SYM (@lem7079166 A)). Qed.
Lemma lem7079170 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term15 A s f.
Proof. exact (h1). Qed.
Lemma lem7079171 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term19 A s f) : term19 A s f.
Proof. exact (h1). Qed.
Lemma lem7079172 (h1 : term57) : term57.
Proof. exact (h1). Qed.
Lemma lem7079173 {A : Type'} (h1 : term20 A) : term20 A.
Proof. exact (h1). Qed.
Lemma lem7079179 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7079185 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem7079192 {A : Type'} (s : A -> Prop) (f : A -> real) (i : A) : (term67 A s f i) = (term69 A s f i).
Proof. exact (@lem17265 (@IN A i s) (term70 A f i)). Qed.
Lemma lem7079193 {A : Type'} (s : A -> Prop) (f : A -> real) : (term68 A s f) = (term71 A s f).
Proof. exact (fun_ext (fun i : A => @lem7079192 A s f i)). Qed.
Lemma lem7079194 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079247 {A : Type'} (s : A -> Prop) (f : A -> real) : (term15 A s f) = (term72 A s f).
Proof. exact (MK_COMB (@lem7079194 A) (@lem7079193 A s f)). Qed.
Lemma lem7079248 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term72 A s f.
Proof. exact (EQ_MP (@lem7079247 A s f) (@lem7079170 A s f h1)). Qed.
Lemma lem7079256 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term73 A s f x) = (term74 A s f x).
Proof. exact (@lem17362 (@IN A x s) (term75 A f x)). Qed.
Lemma lem7079257 {A : Type'} (P : A -> Prop) : (term76 A P) = (term77 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem7079258 {A : Type'} (s : A -> Prop) (f : A -> real) : (term78 A s f) = (term79 A s f).
Proof. exact (@lem7079257 A (term62 A s f)). Qed.
Lemma lem7079259 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term80 A s f x) = (term61 A s f x).
Proof. exact (eq_refl (term80 A s f x)). Qed.
Lemma lem7079260 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7079261 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term81 A s f x) = (term73 A s f x).
Proof. exact (MK_COMB (@lem7079260) (@lem7079259 A s f x)). Qed.
Lemma lem7079262 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term81 A s f x) = (term74 A s f x).
Proof. exact (TRANS (@lem7079261 A s f x) (@lem7079256 A s f x)). Qed.
Lemma lem7079263 {A : Type'} (s : A -> Prop) (f : A -> real) : (term82 A s f) = (term83 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079262 A s f x)). Qed.
Lemma lem7079264 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079265 {A : Type'} (s : A -> Prop) (f : A -> real) : (term79 A s f) = (term84 A s f).
Proof. exact (MK_COMB (@lem7079264 A) (@lem7079263 A s f)). Qed.
Lemma lem7079266 {A : Type'} (s : A -> Prop) (f : A -> real) : (term78 A s f) = (term84 A s f).
Proof. exact (TRANS (@lem7079258 A s f) (@lem7079265 A s f)). Qed.
Lemma lem7079273 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term85 A s f x) = (term86 A s f x).
Proof. exact (@lem17045 (@IN A x s) (term70 A f x)). Qed.
Lemma lem7079274 {A : Type'} (P : A -> Prop) : (term87 A P) = (term88 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7079275 {A : Type'} (s : A -> Prop) (f : A -> real) : (term89 A s f) = (term90 A s f).
Proof. exact (@lem7079274 A (term59 A s f)). Qed.
Lemma lem7079276 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term91 A s f x) = (term58 A s f x).
Proof. exact (eq_refl (term91 A s f x)). Qed.
Lemma lem7079277 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7079278 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term92 A s f x) = (term85 A s f x).
Proof. exact (MK_COMB (@lem7079277) (@lem7079276 A s f x)). Qed.
Lemma lem7079279 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term92 A s f x) = (term86 A s f x).
Proof. exact (TRANS (@lem7079278 A s f x) (@lem7079273 A s f x)). Qed.
Lemma lem7079280 {A : Type'} (s : A -> Prop) (f : A -> real) : (term93 A s f) = (term94 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079279 A s f x)). Qed.
Lemma lem7079281 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079282 {A : Type'} (s : A -> Prop) (f : A -> real) : (term90 A s f) = (term95 A s f).
Proof. exact (MK_COMB (@lem7079281 A) (@lem7079280 A s f)). Qed.
Lemma lem7079283 {A : Type'} (s : A -> Prop) (f : A -> real) : (term89 A s f) = (term95 A s f).
Proof. exact (TRANS (@lem7079275 A s f) (@lem7079282 A s f)). Qed.
Lemma lem7079284 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079285 {A : Type'} (s : A -> Prop) (f : A -> real) : (term96 A s f) = (term97 A s f).
Proof. exact (MK_COMB (@lem7079284) (@lem7079266 A s f)). Qed.
Lemma lem7079286 {A : Type'} (s : A -> Prop) (f : A -> real) : (term98 A s f) = (term99 A s f).
Proof. exact (MK_COMB (@lem7079285 A s f) (@lem7079283 A s f)). Qed.
Lemma lem7079287 {A : Type'} (s : A -> Prop) (f : A -> real) : (term100 A s f) = (term98 A s f).
Proof. exact (@lem17045 (term63 A s f) (term60 A s f)). Qed.
Lemma lem7079288 {A : Type'} (s : A -> Prop) (f : A -> real) : (term100 A s f) = (term99 A s f).
Proof. exact (TRANS (@lem7079287 A s f) (@lem7079286 A s f)). Qed.
Lemma lem7079290 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (eq_refl (term101 A s)). Qed.
Lemma lem7079291 {A : Type'} (s : A -> Prop) (f : A -> real) : (term102 A s f) = (term103 A s f).
Proof. exact (MK_COMB (@lem7079290 A s) (@lem7079288 A s f)). Qed.
Lemma lem7079292 {A : Type'} (s : A -> Prop) (f : A -> real) : (term19 A s f) = (term102 A s f).
Proof. exact (@lem17045 (@FINITE A s) (term65 A s f)). Qed.
Lemma lem7079293 {A : Type'} (s : A -> Prop) (f : A -> real) : (term19 A s f) = (term103 A s f).
Proof. exact (TRANS (@lem7079292 A s f) (@lem7079291 A s f)). Qed.
Lemma lem7079392 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7079393 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (@lem7079392 A P Q). Qed.
Lemma lem7079394 {A : Type'} (s : A -> Prop) (f : A -> real) : (term106 A s f) = (term107 A s f).
Proof. exact (@lem7079393 A (term83 A s f) (term95 A s f)). Qed.
Lemma lem7079395 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term108 A s f x) = (term74 A s f x).
Proof. exact (eq_refl (term108 A s f x)). Qed.
Lemma lem7079396 {A : Type'} (s : A -> Prop) (f : A -> real) : (term109 A s f) = (term83 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079395 A s f x)). Qed.
Lemma lem7079397 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079398 {A : Type'} (s : A -> Prop) (f : A -> real) : (term110 A s f) = (term84 A s f).
Proof. exact (MK_COMB (@lem7079397 A) (@lem7079396 A s f)). Qed.
Lemma lem7079399 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079400 {A : Type'} (s : A -> Prop) (f : A -> real) : (term111 A s f) = (term97 A s f).
Proof. exact (MK_COMB (@lem7079399) (@lem7079398 A s f)). Qed.
Lemma lem7079401 {A : Type'} (s : A -> Prop) (f : A -> real) : (term95 A s f) = (term95 A s f).
Proof. exact (eq_refl (term95 A s f)). Qed.
Lemma lem7079402 {A : Type'} (s : A -> Prop) (f : A -> real) : (term106 A s f) = (term99 A s f).
Proof. exact (MK_COMB (@lem7079400 A s f) (@lem7079401 A s f)). Qed.
Lemma lem7079403 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7079404 {A : Type'} (s : A -> Prop) (f : A -> real) : (term112 A s f) = (term113 A s f).
Proof. exact (MK_COMB (@lem7079403) (@lem7079402 A s f)). Qed.
Lemma lem7079405 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term108 A s f x) = (term74 A s f x).
Proof. exact (eq_refl (term108 A s f x)). Qed.
Lemma lem7079406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079407 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term114 A s f x) = (term115 A s f x).
Proof. exact (MK_COMB (@lem7079406) (@lem7079405 A s f x)). Qed.
Lemma lem7079408 {A : Type'} (s : A -> Prop) (f : A -> real) : (term95 A s f) = (term95 A s f).
Proof. exact (eq_refl (term95 A s f)). Qed.
Lemma lem7079409 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term116 A x s f) = (term117 A x s f).
Proof. exact (MK_COMB (@lem7079407 A s f x) (@lem7079408 A s f)). Qed.
Lemma lem7079410 {A : Type'} (s : A -> Prop) (f : A -> real) : (term118 A s f) = (term119 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079409 A x s f)). Qed.
Lemma lem7079411 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079412 {A : Type'} (s : A -> Prop) (f : A -> real) : (term107 A s f) = (term120 A s f).
Proof. exact (MK_COMB (@lem7079411 A) (@lem7079410 A s f)). Qed.
Lemma lem7079413 {A : Type'} (s : A -> Prop) (f : A -> real) : ((term106 A s f) = (term107 A s f)) = ((term99 A s f) = (term120 A s f)).
Proof. exact (MK_COMB (@lem7079404 A s f) (@lem7079412 A s f)). Qed.
Lemma lem7079414 {A : Type'} (s : A -> Prop) (f : A -> real) : (term99 A s f) = (term120 A s f).
Proof. exact (EQ_MP (@lem7079413 A s f) (@lem7079394 A s f)). Qed.
Lemma lem7079415 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (eq_refl (term101 A s)). Qed.
Lemma lem7079416 {A : Type'} (s : A -> Prop) (f : A -> real) : (term103 A s f) = (term121 A s f).
Proof. exact (MK_COMB (@lem7079415 A s) (@lem7079414 A s f)). Qed.
Lemma lem7079418 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem7079419 {A : Type'} (P : Prop) (Q : A -> Prop) : (term122 A P Q) = (term123 A P Q).
Proof. exact (@lem7079418 A P Q). Qed.
Lemma lem7079420 {A : Type'} (s : A -> Prop) (f : A -> real) : (term124 A s f) = (term125 A s f).
Proof. exact (@lem7079419 A (term126 A s) (term119 A s f)). Qed.
Lemma lem7079421 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term127 A s f x) = (term117 A x s f).
Proof. exact (eq_refl (term127 A s f x)). Qed.
Lemma lem7079422 {A : Type'} (s : A -> Prop) (f : A -> real) : (term128 A s f) = (term119 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079421 A x s f)). Qed.
Lemma lem7079423 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079424 {A : Type'} (s : A -> Prop) (f : A -> real) : (term129 A s f) = (term120 A s f).
Proof. exact (MK_COMB (@lem7079423 A) (@lem7079422 A s f)). Qed.
Lemma lem7079425 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (eq_refl (term101 A s)). Qed.
Lemma lem7079426 {A : Type'} (s : A -> Prop) (f : A -> real) : (term124 A s f) = (term121 A s f).
Proof. exact (MK_COMB (@lem7079425 A s) (@lem7079424 A s f)). Qed.
Lemma lem7079427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7079428 {A : Type'} (s : A -> Prop) (f : A -> real) : (term130 A s f) = (term131 A s f).
Proof. exact (MK_COMB (@lem7079427) (@lem7079426 A s f)). Qed.
Lemma lem7079429 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term127 A s f x) = (term117 A x s f).
Proof. exact (eq_refl (term127 A s f x)). Qed.
Lemma lem7079430 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (eq_refl (term101 A s)). Qed.
Lemma lem7079431 {A : Type'} (x : A) (s : A -> Prop) (f : A -> real) : (term132 A s f x) = (term133 A x s f).
Proof. exact (MK_COMB (@lem7079430 A s) (@lem7079429 A x s f)). Qed.
Lemma lem7079432 {A : Type'} (s : A -> Prop) (f : A -> real) : (term134 A s f) = (term135 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079431 A x s f)). Qed.
Lemma lem7079433 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079434 {A : Type'} (s : A -> Prop) (f : A -> real) : (term125 A s f) = (term136 A s f).
Proof. exact (MK_COMB (@lem7079433 A) (@lem7079432 A s f)). Qed.
Lemma lem7079435 {A : Type'} (s : A -> Prop) (f : A -> real) : ((term124 A s f) = (term125 A s f)) = ((term121 A s f) = (term136 A s f)).
Proof. exact (MK_COMB (@lem7079428 A s f) (@lem7079434 A s f)). Qed.
Lemma lem7079436 {A : Type'} (s : A -> Prop) (f : A -> real) : (term121 A s f) = (term136 A s f).
Proof. exact (EQ_MP (@lem7079435 A s f) (@lem7079420 A s f)). Qed.
Lemma lem7079438 {A : Type'} (s : A -> Prop) (f : A -> real) : (term103 A s f) = (term136 A s f).
Proof. exact (TRANS (@lem7079416 A s f) (@lem7079436 A s f)). Qed.
Lemma lem7079439 {A : Type'} (s : A -> Prop) (f : A -> real) : (term19 A s f) = (term136 A s f).
Proof. exact (TRANS (@lem7079293 A s f) (@lem7079438 A s f)). Qed.
Lemma lem7079440 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term19 A s f) : term136 A s f.
Proof. exact (EQ_MP (@lem7079439 A s f) (@lem7079171 A s f h1)). Qed.
Lemma lem7079447 (x : real) (y : real) : (term53 x y) = (term137 x y).
Proof. exact (@lem17265 (real_lt x y) (real_le x y)). Qed.
Lemma lem7079448 (x : real) : (term54 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem7079447 x y)). Qed.
Lemma lem7079449 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7079450 (x : real) : (term55 x) = (term139 x).
Proof. exact (MK_COMB (@lem7079449) (@lem7079448 x)). Qed.
Lemma lem7079451 : term56 = term140.
Proof. exact (fun_ext (fun x : real => @lem7079450 x)). Qed.
Lemma lem7079452 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7079509 : term57 = term141.
Proof. exact (MK_COMB (@lem7079452) (@lem7079451)). Qed.
Lemma lem7079510 (h1 : term57) : term141.
Proof. exact (EQ_MP (@lem7079509) (@lem7079172 h1)). Qed.
Lemma lem7079512 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem7079513 {A : Type'} (P : A -> Prop) : (term87 A P) = (term88 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem7079514 {A : Type'} (s : A -> Prop) : (term142 A s) = (term143 A s).
Proof. exact (@lem7079513 A (term49 A s)). Qed.
Lemma lem7079515 {A : Type'} (x : A) (s : A -> Prop) : (term144 A s x) = (@IN A x s).
Proof. exact (eq_refl (term144 A s x)). Qed.
Lemma lem7079516 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem7079518 {A : Type'} (x : A) (s : A -> Prop) : (term145 A s x) = (term146 A x s).
Proof. exact (MK_COMB (@lem7079516) (@lem7079515 A x s)). Qed.
Lemma lem7079519 {A : Type'} (s : A -> Prop) : (term147 A s) = (term148 A s).
Proof. exact (fun_ext (fun x : A => @lem7079518 A x s)). Qed.
Lemma lem7079520 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079521 {A : Type'} (s : A -> Prop) : (term143 A s) = (term149 A s).
Proof. exact (MK_COMB (@lem7079520 A) (@lem7079519 A s)). Qed.
Lemma lem7079522 {A : Type'} (s : A -> Prop) : (term142 A s) = (term149 A s).
Proof. exact (TRANS (@lem7079514 A s) (@lem7079521 A s)). Qed.
Lemma lem7079523 {A : Type'} (s : A -> Prop) : (term49 A s) = (term49 A s).
Proof. exact (fun_ext (fun x : A => @lem7079512 A x s)). Qed.
Lemma lem7079524 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079525 {A : Type'} (s : A -> Prop) : (term50 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem7079524 A) (@lem7079523 A s)). Qed.
Lemma lem7079526 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem7079529 {A : Type'} (s : A -> Prop) : (term150 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem7079530 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079531 {A : Type'} (s : A -> Prop) : (term151 A s) = (term152 A s).
Proof. exact (MK_COMB (@lem7079530) (@lem7079522 A s)). Qed.
Lemma lem7079532 {A : Type'} (s : A -> Prop) : (term153 A s) = (term154 A s).
Proof. exact (MK_COMB (@lem7079531 A s) (@lem7079526 A s)). Qed.
Lemma lem7079533 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079534 {A : Type'} (s : A -> Prop) : (term155 A s) = (term155 A s).
Proof. exact (MK_COMB (@lem7079533) (@lem7079525 A s)). Qed.
Lemma lem7079535 {A : Type'} (s : A -> Prop) : (term156 A s) = (term157 A s).
Proof. exact (MK_COMB (@lem7079534 A s) (@lem7079529 A s)). Qed.
Lemma lem7079536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079537 {A : Type'} (s : A -> Prop) : (term158 A s) = (term159 A s).
Proof. exact (MK_COMB (@lem7079536) (@lem7079535 A s)). Qed.
Lemma lem7079538 {A : Type'} (s : A -> Prop) : (term160 A s) = (term161 A s).
Proof. exact (MK_COMB (@lem7079537 A s) (@lem7079532 A s)). Qed.
Lemma lem7079539 {A : Type'} (s : A -> Prop) : ((term50 A s) = (term16 A s)) = (term160 A s).
Proof. exact (@lem17784 (term50 A s) (term16 A s)). Qed.
Lemma lem7079540 {A : Type'} (s : A -> Prop) : ((term50 A s) = (term16 A s)) = (term161 A s).
Proof. exact (TRANS (@lem7079539 A s) (@lem7079538 A s)). Qed.
Lemma lem7079541 {A : Type'} : (term52 A) = (term162 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079540 A s)). Qed.
Lemma lem7079542 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079543 {A : Type'} : (term20 A) = (term163 A).
Proof. exact (MK_COMB (@lem7079542 A) (@lem7079541 A)). Qed.
Lemma lem7079545 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term164 A P Q) = (term165 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem7079546 {A : Type'} (P : type686 A) (Q : type686 A) : (term166 A P Q) = (term167 A P Q).
Proof. exact (@lem7079545 (A -> Prop) P Q). Qed.
Lemma lem7079547 {A : Type'} : (term168 A) = (term169 A).
Proof. exact (@lem7079546 A (term170 A) (term171 A)). Qed.
Lemma lem7079548 {A : Type'} (s : A -> Prop) : (term172 A s) = (term157 A s).
Proof. exact (eq_refl (term172 A s)). Qed.
Lemma lem7079549 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079550 {A : Type'} (s : A -> Prop) : (term173 A s) = (term159 A s).
Proof. exact (MK_COMB (@lem7079549) (@lem7079548 A s)). Qed.
Lemma lem7079551 {A : Type'} (s : A -> Prop) : (term174 A s) = (term154 A s).
Proof. exact (eq_refl (term174 A s)). Qed.
Lemma lem7079552 {A : Type'} (s : A -> Prop) : (term175 A s) = (term161 A s).
Proof. exact (MK_COMB (@lem7079550 A s) (@lem7079551 A s)). Qed.
Lemma lem7079553 {A : Type'} : (term176 A) = (term162 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079552 A s)). Qed.
Lemma lem7079554 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079555 {A : Type'} : (term168 A) = (term163 A).
Proof. exact (MK_COMB (@lem7079554 A) (@lem7079553 A)). Qed.
Lemma lem7079556 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7079557 {A : Type'} : (term177 A) = (term178 A).
Proof. exact (MK_COMB (@lem7079556) (@lem7079555 A)). Qed.
Lemma lem7079558 {A : Type'} (s : A -> Prop) : (term172 A s) = (term157 A s).
Proof. exact (eq_refl (term172 A s)). Qed.
Lemma lem7079559 {A : Type'} : (term179 A) = (term170 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079558 A s)). Qed.
Lemma lem7079560 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079561 {A : Type'} : (term180 A) = (term181 A).
Proof. exact (MK_COMB (@lem7079560 A) (@lem7079559 A)). Qed.
Lemma lem7079562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079563 {A : Type'} : (term182 A) = (term183 A).
Proof. exact (MK_COMB (@lem7079562) (@lem7079561 A)). Qed.
Lemma lem7079564 {A : Type'} (s : A -> Prop) : (term174 A s) = (term154 A s).
Proof. exact (eq_refl (term174 A s)). Qed.
Lemma lem7079565 {A : Type'} : (term184 A) = (term171 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079564 A s)). Qed.
Lemma lem7079566 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079567 {A : Type'} : (term185 A) = (term186 A).
Proof. exact (MK_COMB (@lem7079566 A) (@lem7079565 A)). Qed.
Lemma lem7079568 {A : Type'} : (term169 A) = (term187 A).
Proof. exact (MK_COMB (@lem7079563 A) (@lem7079567 A)). Qed.
Lemma lem7079569 {A : Type'} : ((term168 A) = (term169 A)) = ((term163 A) = (term187 A)).
Proof. exact (MK_COMB (@lem7079557 A) (@lem7079568 A)). Qed.
Lemma lem7079570 {A : Type'} : (term163 A) = (term187 A).
Proof. exact (EQ_MP (@lem7079569 A) (@lem7079547 A)). Qed.
Lemma lem7079676 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem7079677 {A : Type'} (P : A -> Prop) (Q : Prop) : (term104 A P Q) = (term105 A P Q).
Proof. exact (@lem7079676 A P Q). Qed.
Lemma lem7079678 {A : Type'} (s : A -> Prop) : (term188 A s) = (term189 A s).
Proof. exact (@lem7079677 A (term49 A s) (s = (@EMPTY A))). Qed.
Lemma lem7079679 {A : Type'} (x : A) (s : A -> Prop) : (term144 A s x) = (@IN A x s).
Proof. exact (eq_refl (term144 A s x)). Qed.
Lemma lem7079680 {A : Type'} (s : A -> Prop) : (term190 A s) = (term49 A s).
Proof. exact (fun_ext (fun x : A => @lem7079679 A x s)). Qed.
Lemma lem7079681 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079682 {A : Type'} (s : A -> Prop) : (term191 A s) = (term50 A s).
Proof. exact (MK_COMB (@lem7079681 A) (@lem7079680 A s)). Qed.
Lemma lem7079683 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079684 {A : Type'} (s : A -> Prop) : (term192 A s) = (term155 A s).
Proof. exact (MK_COMB (@lem7079683) (@lem7079682 A s)). Qed.
Lemma lem7079685 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem7079686 {A : Type'} (s : A -> Prop) : (term188 A s) = (term157 A s).
Proof. exact (MK_COMB (@lem7079684 A s) (@lem7079685 A s)). Qed.
Lemma lem7079687 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7079688 {A : Type'} (s : A -> Prop) : (term193 A s) = (term194 A s).
Proof. exact (MK_COMB (@lem7079687) (@lem7079686 A s)). Qed.
Lemma lem7079689 {A : Type'} (x : A) (s : A -> Prop) : (term144 A s x) = (@IN A x s).
Proof. exact (eq_refl (term144 A s x)). Qed.
Lemma lem7079690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079691 {A : Type'} (x : A) (s : A -> Prop) : (term195 A s x) = (term196 A x s).
Proof. exact (MK_COMB (@lem7079690) (@lem7079689 A x s)). Qed.
Lemma lem7079692 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem7079693 {A : Type'} (x : A) (s : A -> Prop) : (term197 A x s) = (term198 A x s).
Proof. exact (MK_COMB (@lem7079691 A x s) (@lem7079692 A s)). Qed.
Lemma lem7079694 {A : Type'} (s : A -> Prop) : (term199 A s) = (term200 A s).
Proof. exact (fun_ext (fun x : A => @lem7079693 A x s)). Qed.
Lemma lem7079695 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079696 {A : Type'} (s : A -> Prop) : (term189 A s) = (term201 A s).
Proof. exact (MK_COMB (@lem7079695 A) (@lem7079694 A s)). Qed.
Lemma lem7079697 {A : Type'} (s : A -> Prop) : ((term188 A s) = (term189 A s)) = ((term157 A s) = (term201 A s)).
Proof. exact (MK_COMB (@lem7079688 A s) (@lem7079696 A s)). Qed.
Lemma lem7079698 {A : Type'} (s : A -> Prop) : (term157 A s) = (term201 A s).
Proof. exact (EQ_MP (@lem7079697 A s) (@lem7079678 A s)). Qed.
Lemma lem7079699 {A : Type'} : (term170 A) = (term202 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079698 A s)). Qed.
Lemma lem7079700 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079701 {A : Type'} : (term181 A) = (term203 A).
Proof. exact (MK_COMB (@lem7079700 A) (@lem7079699 A)). Qed.
Lemma lem7079703 {A B : Type'} (P : type1413 A B) : (term204 A B P) = (term205 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem7079704 {A : Type'} (P : type672 A) : (term206 A P) = (term207 A P).
Proof. exact (@lem7079703 (A -> Prop) A P). Qed.
Lemma lem7079705 {A : Type'} : (term208 A) = (term209 A).
Proof. exact (@lem7079704 A (term210 A)). Qed.
Lemma lem7079706 {A : Type'} (s : A -> Prop) : (term211 A s) = (term200 A s).
Proof. exact (eq_refl (term211 A s)). Qed.
Lemma lem7079707 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem7079708 {A : Type'} (s : A -> Prop) (x : A) : (term212 A s x) = (term213 A s x).
Proof. exact (MK_COMB (@lem7079706 A s) (@lem7079707 A x)). Qed.
Lemma lem7079709 {A : Type'} (x : A) (s : A -> Prop) : (term213 A s x) = (term198 A x s).
Proof. exact (eq_refl (term213 A s x)). Qed.
Lemma lem7079710 {A : Type'} (x : A) (s : A -> Prop) : (term212 A s x) = (term198 A x s).
Proof. exact (TRANS (@lem7079708 A s x) (@lem7079709 A x s)). Qed.
Lemma lem7079711 {A : Type'} (s : A -> Prop) : (term214 A s) = (term200 A s).
Proof. exact (fun_ext (fun x : A => @lem7079710 A x s)). Qed.
Lemma lem7079712 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem7079713 {A : Type'} (s : A -> Prop) : (term215 A s) = (term201 A s).
Proof. exact (MK_COMB (@lem7079712 A) (@lem7079711 A s)). Qed.
Lemma lem7079714 {A : Type'} : (term216 A) = (term202 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079713 A s)). Qed.
Lemma lem7079715 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079716 {A : Type'} : (term208 A) = (term203 A).
Proof. exact (MK_COMB (@lem7079715 A) (@lem7079714 A)). Qed.
Lemma lem7079717 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7079718 {A : Type'} : (term217 A) = (term218 A).
Proof. exact (MK_COMB (@lem7079717) (@lem7079716 A)). Qed.
Lemma lem7079719 {A : Type'} (s : A -> Prop) : (term211 A s) = (term200 A s).
Proof. exact (eq_refl (term211 A s)). Qed.
Lemma lem7079720 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem7079721 {A : Type'} (x : type684 A) (s : A -> Prop) : (term219 A x s) = (term220 A x s).
Proof. exact (MK_COMB (@lem7079719 A s) (@lem7079720 A x s)). Qed.
Lemma lem7079722 {A : Type'} (x : type684 A) (s : A -> Prop) : (term220 A x s) = (term221 A x s).
Proof. exact (eq_refl (term220 A x s)). Qed.
Lemma lem7079723 {A : Type'} (x : type684 A) (s : A -> Prop) : (term219 A x s) = (term221 A x s).
Proof. exact (TRANS (@lem7079721 A x s) (@lem7079722 A x s)). Qed.
Lemma lem7079724 {A : Type'} (x : type684 A) : (term222 A x) = (term223 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079723 A x s)). Qed.
Lemma lem7079725 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079726 {A : Type'} (x : type684 A) : (term224 A x) = (term225 A x).
Proof. exact (MK_COMB (@lem7079725 A) (@lem7079724 A x)). Qed.
Lemma lem7079727 {A : Type'} : (term226 A) = (term227 A).
Proof. exact (fun_ext (fun x : type684 A => @lem7079726 A x)). Qed.
Lemma lem7079728 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7079729 {A : Type'} : (term209 A) = (term228 A).
Proof. exact (MK_COMB (@lem7079728 A) (@lem7079727 A)). Qed.
Lemma lem7079730 {A : Type'} : ((term208 A) = (term209 A)) = ((term203 A) = (term228 A)).
Proof. exact (MK_COMB (@lem7079718 A) (@lem7079729 A)). Qed.
Lemma lem7079731 {A : Type'} : (term203 A) = (term228 A).
Proof. exact (EQ_MP (@lem7079730 A) (@lem7079705 A)). Qed.
Lemma lem7079732 {A : Type'} : (term181 A) = (term228 A).
Proof. exact (TRANS (@lem7079701 A) (@lem7079731 A)). Qed.
Lemma lem7079733 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079734 {A : Type'} : (term183 A) = (term229 A).
Proof. exact (MK_COMB (@lem7079733) (@lem7079732 A)). Qed.
Lemma lem7079735 {A : Type'} : (term186 A) = (term186 A).
Proof. exact (eq_refl (term186 A)). Qed.
Lemma lem7079736 {A : Type'} : (term187 A) = (term230 A).
Proof. exact (MK_COMB (@lem7079734 A) (@lem7079735 A)). Qed.
Lemma lem7079738 {A : Type'} (P : A -> Prop) (Q : Prop) : (term231 A P Q) = (term232 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem7079739 {A : Type'} (P : type162 A) (Q : Prop) : (term233 A P Q) = (term234 A P Q).
Proof. exact (@lem7079738 (type684 A) P Q). Qed.
Lemma lem7079740 {A : Type'} : (term235 A) = (term236 A).
Proof. exact (@lem7079739 A (term227 A) (term186 A)). Qed.
Lemma lem7079741 {A : Type'} (x : type684 A) : (term237 A x) = (term225 A x).
Proof. exact (eq_refl (term237 A x)). Qed.
Lemma lem7079742 {A : Type'} : (term238 A) = (term227 A).
Proof. exact (fun_ext (fun x : type684 A => @lem7079741 A x)). Qed.
Lemma lem7079743 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7079744 {A : Type'} : (term239 A) = (term228 A).
Proof. exact (MK_COMB (@lem7079743 A) (@lem7079742 A)). Qed.
Lemma lem7079745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079746 {A : Type'} : (term240 A) = (term229 A).
Proof. exact (MK_COMB (@lem7079745) (@lem7079744 A)). Qed.
Lemma lem7079747 {A : Type'} : (term186 A) = (term186 A).
Proof. exact (eq_refl (term186 A)). Qed.
Lemma lem7079748 {A : Type'} : (term235 A) = (term230 A).
Proof. exact (MK_COMB (@lem7079746 A) (@lem7079747 A)). Qed.
Lemma lem7079749 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7079750 {A : Type'} : (term241 A) = (term242 A).
Proof. exact (MK_COMB (@lem7079749) (@lem7079748 A)). Qed.
Lemma lem7079751 {A : Type'} (x : type684 A) : (term237 A x) = (term225 A x).
Proof. exact (eq_refl (term237 A x)). Qed.
Lemma lem7079752 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079753 {A : Type'} (x : type684 A) : (term243 A x) = (term244 A x).
Proof. exact (MK_COMB (@lem7079752) (@lem7079751 A x)). Qed.
Lemma lem7079754 {A : Type'} : (term186 A) = (term186 A).
Proof. exact (eq_refl (term186 A)). Qed.
Lemma lem7079755 {A : Type'} (x : type684 A) : (term245 A x) = (term246 A x).
Proof. exact (MK_COMB (@lem7079753 A x) (@lem7079754 A)). Qed.
Lemma lem7079756 {A : Type'} : (term247 A) = (term248 A).
Proof. exact (fun_ext (fun x : type684 A => @lem7079755 A x)). Qed.
Lemma lem7079757 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem7079758 {A : Type'} : (term236 A) = (term249 A).
Proof. exact (MK_COMB (@lem7079757 A) (@lem7079756 A)). Qed.
Lemma lem7079759 {A : Type'} : ((term235 A) = (term236 A)) = ((term230 A) = (term249 A)).
Proof. exact (MK_COMB (@lem7079750 A) (@lem7079758 A)). Qed.
Lemma lem7079760 {A : Type'} : (term230 A) = (term249 A).
Proof. exact (EQ_MP (@lem7079759 A) (@lem7079740 A)). Qed.
Lemma lem7079761 {A : Type'} : (term187 A) = (term249 A).
Proof. exact (TRANS (@lem7079736 A) (@lem7079760 A)). Qed.
Lemma lem7079762 {A : Type'} : (term163 A) = (term249 A).
Proof. exact (TRANS (@lem7079570 A) (@lem7079761 A)). Qed.
Lemma lem7079763 {A : Type'} : (term20 A) = (term249 A).
Proof. exact (TRANS (@lem7079543 A) (@lem7079762 A)). Qed.
Lemma lem7079764 {A : Type'} (h1 : term20 A) : term249 A.
Proof. exact (EQ_MP (@lem7079763 A) (@lem7079173 A h1)). Qed.
Lemma lem7079765 {A : Type'} (x : type684 A) (h1 : term246 A x) : term246 A x.
Proof. exact (h1). Qed.
Lemma lem7079766 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term133 A x' s f) : term133 A x' s f.
Proof. exact (h1). Qed.
Lemma lem7079770 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7079778 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem7079799 {A : Type'} (s : A -> Prop) (f : A -> real) (i : A) : (term69 A s f i) = (term69 A s f i).
Proof. exact (eq_refl (term69 A s f i)). Qed.
Lemma lem7079800 {A : Type'} (s : A -> Prop) (f : A -> real) : (term71 A s f) = (term71 A s f).
Proof. exact (fun_ext (fun i : A => @lem7079799 A s f i)). Qed.
Lemma lem7079801 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079802 {A : Type'} (s : A -> Prop) (f : A -> real) : (term72 A s f) = (term72 A s f).
Proof. exact (MK_COMB (@lem7079801 A) (@lem7079800 A s f)). Qed.
Lemma lem7079803 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term72 A s f.
Proof. exact (EQ_MP (@lem7079802 A s f) (@lem7079248 A s f h1)). Qed.
Lemma lem7079818 (x : real) (y : real) : (term137 x y) = (term137 x y).
Proof. exact (eq_refl (term137 x y)). Qed.
Lemma lem7079819 (x : real) : (term138 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem7079818 x y)). Qed.
Lemma lem7079820 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7079821 (x : real) : (term139 x) = (term139 x).
Proof. exact (MK_COMB (@lem7079820) (@lem7079819 x)). Qed.
Lemma lem7079822 : term140 = term140.
Proof. exact (fun_ext (fun x : real => @lem7079821 x)). Qed.
Lemma lem7079823 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7079824 : term141 = term141.
Proof. exact (MK_COMB (@lem7079823) (@lem7079822)). Qed.
Lemma lem7079825 (h1 : term57) : term141.
Proof. exact (EQ_MP (@lem7079824) (@lem7079510 h1)). Qed.
Lemma lem7079832 {A : Type'} (s : A -> Prop) : (term16 A s) = (term16 A s).
Proof. exact (eq_refl (term16 A s)). Qed.
Lemma lem7079839 {A : Type'} (x : A) (s : A -> Prop) : (term146 A x s) = (term146 A x s).
Proof. exact (eq_refl (term146 A x s)). Qed.
Lemma lem7079840 {A : Type'} (s : A -> Prop) : (term148 A s) = (term148 A s).
Proof. exact (fun_ext (fun x : A => @lem7079839 A x s)). Qed.
Lemma lem7079841 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079842 {A : Type'} (s : A -> Prop) : (term149 A s) = (term149 A s).
Proof. exact (MK_COMB (@lem7079841 A) (@lem7079840 A s)). Qed.
Lemma lem7079843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem7079844 {A : Type'} (s : A -> Prop) : (term152 A s) = (term152 A s).
Proof. exact (MK_COMB (@lem7079843) (@lem7079842 A s)). Qed.
Lemma lem7079845 {A : Type'} (s : A -> Prop) : (term154 A s) = (term154 A s).
Proof. exact (MK_COMB (@lem7079844 A s) (@lem7079832 A s)). Qed.
Lemma lem7079846 {A : Type'} : (term171 A) = (term171 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079845 A s)). Qed.
Lemma lem7079847 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079848 {A : Type'} : (term186 A) = (term186 A).
Proof. exact (MK_COMB (@lem7079847 A) (@lem7079846 A)). Qed.
Lemma lem7079863 {A : Type'} (x : type684 A) (s : A -> Prop) : (term221 A x s) = (term221 A x s).
Proof. exact (eq_refl (term221 A x s)). Qed.
Lemma lem7079864 {A : Type'} (x : type684 A) : (term223 A x) = (term223 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7079863 A x s)). Qed.
Lemma lem7079865 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7079866 {A : Type'} (x : type684 A) : (term225 A x) = (term225 A x).
Proof. exact (MK_COMB (@lem7079865 A) (@lem7079864 A x)). Qed.
Lemma lem7079867 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7079868 {A : Type'} (x : type684 A) : (term244 A x) = (term244 A x).
Proof. exact (MK_COMB (@lem7079867) (@lem7079866 A x)). Qed.
Lemma lem7079869 {A : Type'} (x : type684 A) : (term246 A x) = (term246 A x).
Proof. exact (MK_COMB (@lem7079868 A x) (@lem7079848 A)). Qed.
Lemma lem7079870 {A : Type'} (x : type684 A) (h1 : term246 A x) : term246 A x.
Proof. exact (EQ_MP (@lem7079869 A x) (@lem7079765 A x h1)). Qed.
Lemma lem7079893 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term86 A s f x) = (term86 A s f x).
Proof. exact (eq_refl (term86 A s f x)). Qed.
Lemma lem7079894 {A : Type'} (s : A -> Prop) (f : A -> real) : (term94 A s f) = (term94 A s f).
Proof. exact (fun_ext (fun x : A => @lem7079893 A s f x)). Qed.
Lemma lem7079895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7079896 {A : Type'} (s : A -> Prop) (f : A -> real) : (term95 A s f) = (term95 A s f).
Proof. exact (MK_COMB (@lem7079895 A) (@lem7079894 A s f)). Qed.
Lemma lem7079919 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) : (term115 A s f x') = (term115 A s f x').
Proof. exact (eq_refl (term115 A s f x')). Qed.
Lemma lem7079920 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term117 A x' s f) = (term117 A x' s f).
Proof. exact (MK_COMB (@lem7079919 A s f x') (@lem7079896 A s f)). Qed.
Lemma lem7079927 {A : Type'} (s : A -> Prop) : (term101 A s) = (term101 A s).
Proof. exact (eq_refl (term101 A s)). Qed.
Lemma lem7079928 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) : (term133 A x' s f) = (term133 A x' s f).
Proof. exact (MK_COMB (@lem7079927 A s) (@lem7079920 A x' s f)). Qed.
Lemma lem7079929 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term133 A x' s f) : term133 A x' s f.
Proof. exact (EQ_MP (@lem7079928 A x' s f) (@lem7079766 A x' s f h1)). Qed.
Lemma lem7079931 {A : Type'} (x : type684 A) (h1 : term246 A x) : term225 A x.
Proof. exact (proj1 (@lem7079870 A x h1)). Qed.
Lemma lem7079933 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term117 A x' s f) : term117 A x' s f.
Proof. exact (h1). Qed.
Lemma lem7079934 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term74 A s f x') : term74 A s f x'.
Proof. exact (h1). Qed.
Lemma lem7079935 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term95 A s f) : term95 A s f.
Proof. exact (h1). Qed.
Lemma lem7079941 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7080033 {A : Type'} (s : A -> Prop) (h1 : term126 A s) : term126 A s.
Proof. exact (h1). Qed.
Lemma lem7080049 {A : Type'} (s : A -> Prop) (f : A -> real) (i : A) : (term69 A s f i) = (term69 A s f i).
Proof. exact (eq_refl (term69 A s f i)). Qed.
Lemma lem7080050 {A : Type'} (s : A -> Prop) (f : A -> real) : (term71 A s f) = (term71 A s f).
Proof. exact (fun_ext (fun i : A => @lem7080049 A s f i)). Qed.
Lemma lem7080051 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7080053 {A : Type'} (s : A -> Prop) (f : A -> real) : (term72 A s f) = (term72 A s f).
Proof. exact (MK_COMB (@lem7080051 A) (@lem7080050 A s f)). Qed.
Lemma lem7080054 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term72 A s f.
Proof. exact (EQ_MP (@lem7080053 A s f) (@lem7079803 A s f h1)). Qed.
Lemma lem7080062 (x : real) (y : real) : (term137 x y) = (term137 x y).
Proof. exact (eq_refl (term137 x y)). Qed.
Lemma lem7080063 (x : real) : (term138 x) = (term138 x).
Proof. exact (fun_ext (fun y : real => @lem7080062 x y)). Qed.
Lemma lem7080064 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7080065 (x : real) : (term139 x) = (term139 x).
Proof. exact (MK_COMB (@lem7080064) (@lem7080063 x)). Qed.
Lemma lem7080066 : term140 = term140.
Proof. exact (fun_ext (fun x : real => @lem7080065 x)). Qed.
Lemma lem7080067 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem7080069 : term141 = term141.
Proof. exact (MK_COMB (@lem7080067) (@lem7080066)). Qed.
Lemma lem7080070 (h1 : term57) : term141.
Proof. exact (EQ_MP (@lem7080069) (@lem7079825 h1)). Qed.
Lemma lem7080141 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem7080149 {A : Type'} (s : A -> Prop) (f : A -> real) (i : A) : (term69 A s f i) = (term69 A s f i).
Proof. exact (eq_refl (term69 A s f i)). Qed.
Lemma lem7080150 {A : Type'} (s : A -> Prop) (f : A -> real) : (term71 A s f) = (term71 A s f).
Proof. exact (fun_ext (fun i : A => @lem7080149 A s f i)). Qed.
Lemma lem7080151 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7080153 {A : Type'} (s : A -> Prop) (f : A -> real) : (term72 A s f) = (term72 A s f).
Proof. exact (MK_COMB (@lem7080151 A) (@lem7080150 A s f)). Qed.
Lemma lem7080154 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term72 A s f.
Proof. exact (EQ_MP (@lem7080153 A s f) (@lem7079803 A s f h1)). Qed.
Lemma lem7080178 {A : Type'} (x : type684 A) (s : A -> Prop) : (term221 A x s) = (term221 A x s).
Proof. exact (eq_refl (term221 A x s)). Qed.
Lemma lem7080179 {A : Type'} (x : type684 A) : (term223 A x) = (term223 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem7080178 A x s)). Qed.
Lemma lem7080180 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem7080182 {A : Type'} (x : type684 A) : (term225 A x) = (term225 A x).
Proof. exact (MK_COMB (@lem7080180 A) (@lem7080179 A x)). Qed.
Lemma lem7080183 {A : Type'} (x : type684 A) (h1 : term246 A x) : term225 A x.
Proof. exact (EQ_MP (@lem7080182 A x) (@lem7079931 A x h1)). Qed.
Lemma lem7080233 {A : Type'} (s : A -> Prop) (f : A -> real) (x : A) : (term86 A s f x) = (term86 A s f x).
Proof. exact (eq_refl (term86 A s f x)). Qed.
Lemma lem7080234 {A : Type'} (s : A -> Prop) (f : A -> real) : (term94 A s f) = (term94 A s f).
Proof. exact (fun_ext (fun x : A => @lem7080233 A s f x)). Qed.
Lemma lem7080235 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem7080237 {A : Type'} (s : A -> Prop) (f : A -> real) : (term95 A s f) = (term95 A s f).
Proof. exact (MK_COMB (@lem7080235 A) (@lem7080234 A s f)). Qed.
Lemma lem7080238 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term95 A s f) : term95 A s f.
Proof. exact (EQ_MP (@lem7080237 A s f) (@lem7079935 A s f h1)). Qed.
Lemma lem7080257 {A : Type'} (_94465 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term250 A s f _94465.
Proof. exact (@lem7080054 A s f h1 _94465). Qed.
Lemma lem7080258 {A : Type'} (s : A -> Prop) (f : A -> real) (_94465 : A) : (term250 A s f _94465) = (term69 A s f _94465).
Proof. exact (eq_refl (term250 A s f _94465)). Qed.
Lemma lem7080260 (_94466 : real) (h1 : term57) : term251 _94466.
Proof. exact (@lem7080070 h1 _94466). Qed.
Lemma lem7080261 (_94466 : real) : (term251 _94466) = (term139 _94466).
Proof. exact (eq_refl (term251 _94466)). Qed.
Lemma lem7080262 (_94466 : real) (h1 : term57) : term139 _94466.
Proof. exact (EQ_MP (@lem7080261 _94466) (@lem7080260 _94466 h1)). Qed.
Lemma lem7080263 (_94466 : real) (_94467 : real) (h1 : term57) : term252 _94466 _94467.
Proof. exact (@lem7080262 _94466 h1 _94467). Qed.
Lemma lem7080264 (_94466 : real) (_94467 : real) : (term252 _94466 _94467) = (term137 _94466 _94467).
Proof. exact (eq_refl (term252 _94466 _94467)). Qed.
Lemma lem7080275 {A : Type'} (_94471 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term250 A s f _94471.
Proof. exact (@lem7080154 A s f h1 _94471). Qed.
Lemma lem7080276 {A : Type'} (s : A -> Prop) (f : A -> real) (_94471 : A) : (term250 A s f _94471) = (term69 A s f _94471).
Proof. exact (eq_refl (term250 A s f _94471)). Qed.
Lemma lem7080284 {A : Type'} (_94474 : A -> Prop) (x : type684 A) (h1 : term246 A x) : term253 A x _94474.
Proof. exact (@lem7080183 A x h1 _94474). Qed.
Lemma lem7080285 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : (term253 A x _94474) = (term221 A x _94474).
Proof. exact (eq_refl (term253 A x _94474)). Qed.
Lemma lem7080293 {A : Type'} (_94477 : A) (s : A -> Prop) (f : A -> real) (h1 : term95 A s f) : term254 A s f _94477.
Proof. exact (@lem7080238 A s f h1 _94477). Qed.
Lemma lem7080294 {A : Type'} (s : A -> Prop) (f : A -> real) (_94477 : A) : (term254 A s f _94477) = (term86 A s f _94477).
Proof. exact (eq_refl (term254 A s f _94477)). Qed.
Lemma lem7080297 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7080325 {A : Type'} (s : A -> Prop) (h1 : term126 A s) : term126 A s.
Proof. exact (h1). Qed.
Lemma lem7080335 {A : Type'} (_94465 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term69 A s f _94465.
Proof. exact (EQ_MP (@lem7080258 A s f _94465) (@lem7080257 A _94465 s f h1)). Qed.
Lemma lem7080341 (_94466 : real) (_94467 : real) (h1 : term57) : term137 _94466 _94467.
Proof. exact (EQ_MP (@lem7080264 _94466 _94467) (@lem7080263 _94466 _94467 h1)). Qed.
Lemma lem7080357 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term74 A s f x') : term255 A f x'.
Proof. exact (proj2 (@lem7079934 A s f x' h1)). Qed.
Lemma lem7080361 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem7080367 {A : Type'} (_94471 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term69 A s f _94471.
Proof. exact (EQ_MP (@lem7080276 A s f _94471) (@lem7080275 A _94471 s f h1)). Qed.
Lemma lem7080379 {A : Type'} (_94474 : A -> Prop) (x : type684 A) (h1 : term246 A x) : term221 A x _94474.
Proof. exact (EQ_MP (@lem7080285 A x _94474) (@lem7080284 A _94474 x h1)). Qed.
Lemma lem7080391 {A : Type'} (_94477 : A) (s : A -> Prop) (f : A -> real) (h1 : term95 A s f) : term86 A s f _94477.
Proof. exact (EQ_MP (@lem7080294 A s f _94477) (@lem7080293 A _94477 s f h1)). Qed.
Lemma lem7080502 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem7080503 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term256 A s.
Proof. exact (fun h0 : term126 A s => @lem7080502 A s h1). Qed.
Lemma lem7080505 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080506 {A : Type'} (s : A -> Prop) : (term256 A s) = (@FINITE A s).
Proof. exact (@lem7080505 (@FINITE A s)). Qed.
Lemma lem7080507 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (EQ_MP (@lem7080506 A s) (@lem7080503 A s h1)). Qed.
Lemma lem7080510 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7080512 {A : Type'} (s : A -> Prop) : (term126 A s) = (term258 A s).
Proof. exact (@lem7080510 (@FINITE A s)). Qed.
Lemma lem7080515 {A : Type'} (s : A -> Prop) (h1 : term126 A s) : term258 A s.
Proof. exact (EQ_MP (@lem7080512 A s) (@lem7080325 A s h1)). Qed.
Lemma lem7080518 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (@lem7080515 A s h2 (@lem7080507 A s h1)). Qed.
Lemma lem7080519 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : term259.
Proof. exact (fun h0 : ~ False => @lem7080518 A s h1 h2). Qed.
Lemma lem7080521 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080522 : term259 = False.
Proof. exact (@lem7080521 False). Qed.
Lemma lem7080523 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (EQ_MP (@lem7080522) (@lem7080519 A s h1 h2)). Qed.
Lemma lem7080634 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term74 A s f x') : @IN A x' s.
Proof. exact (proj1 (@lem7079934 A s f x' h1)). Qed.
Lemma lem7080635 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term74 A s f x') : term260 A x' s.
Proof. exact (fun h0 : term146 A x' s => @lem7080634 A s f x' h1). Qed.
Lemma lem7080637 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080638 {A : Type'} (x' : A) (s : A -> Prop) : (term260 A x' s) = (@IN A x' s).
Proof. exact (@lem7080637 (@IN A x' s)). Qed.
Lemma lem7080639 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term74 A s f x') : @IN A x' s.
Proof. exact (EQ_MP (@lem7080638 A x' s) (@lem7080635 A s f x' h1)). Qed.
Lemma lem7080645 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7080646 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : (term69 A s f _94465) = (term261 A f _94465 s).
Proof. exact (@lem7080645 (term70 A f _94465) (term146 A _94465 s)). Qed.
Lemma lem7080652 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7080653 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : (term262 A s f _94465) = (term263 A f _94465 s).
Proof. exact (MK_COMB (@lem7080652) (@lem7080646 A f _94465 s)). Qed.
Lemma lem7080659 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : (term261 A f _94465 s) = (term261 A f _94465 s).
Proof. exact (eq_refl (term261 A f _94465 s)). Qed.
Lemma lem7080660 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : ((term69 A s f _94465) = (term261 A f _94465 s)) = ((term261 A f _94465 s) = (term261 A f _94465 s)).
Proof. exact (MK_COMB (@lem7080653 A f _94465 s) (@lem7080659 A f _94465 s)). Qed.
Lemma lem7080662 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7080663 (x : Prop) : (x = x) = True.
Proof. exact (@lem7080662 Prop x). Qed.
Lemma lem7080664 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : ((term261 A f _94465 s) = (term261 A f _94465 s)) = True.
Proof. exact (@lem7080663 (term261 A f _94465 s)). Qed.
Lemma lem7080665 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : ((term69 A s f _94465) = (term261 A f _94465 s)) = True.
Proof. exact (TRANS (@lem7080660 A f _94465 s) (@lem7080664 A f _94465 s)). Qed.
Lemma lem7080666 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : True = ((term69 A s f _94465) = (term261 A f _94465 s)).
Proof. exact (SYM (@lem7080665 A f _94465 s)). Qed.
Lemma lem7080667 {A : Type'} (f : A -> real) (_94465 : A) (s : A -> Prop) : (term69 A s f _94465) = (term261 A f _94465 s).
Proof. exact (EQ_MP (@lem7080666 A f _94465 s) (@lem0)). Qed.
Lemma lem7080668 {A : Type'} (_94465 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term261 A f _94465 s.
Proof. exact (EQ_MP (@lem7080667 A f _94465 s) (@lem7080335 A _94465 s f h1)). Qed.
Lemma lem7080670 (b : Prop) (a : Prop) : (a \/ b) = (term264 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7080671 {A : Type'} (s : A -> Prop) (f : A -> real) (_94465 : A) : (term261 A f _94465 s) = (term265 A s f _94465).
Proof. exact (@lem7080670 (term146 A _94465 s) (term70 A f _94465)). Qed.
Lemma lem7080673 (a : Prop) : (term266 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7080674 {A : Type'} (_94465 : A) (s : A -> Prop) : (term267 A _94465 s) = (@IN A _94465 s).
Proof. exact (@lem7080673 (@IN A _94465 s)). Qed.
Lemma lem7080675 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7080676 {A : Type'} (_94465 : A) (s : A -> Prop) : (term268 A _94465 s) = (term269 A _94465 s).
Proof. exact (MK_COMB (@lem7080675) (@lem7080674 A _94465 s)). Qed.
Lemma lem7080677 {A : Type'} (f : A -> real) (_94465 : A) : (term70 A f _94465) = (term70 A f _94465).
Proof. exact (eq_refl (term70 A f _94465)). Qed.
Lemma lem7080678 {A : Type'} (s : A -> Prop) (f : A -> real) (_94465 : A) : (term265 A s f _94465) = (term67 A s f _94465).
Proof. exact (MK_COMB (@lem7080676 A _94465 s) (@lem7080677 A f _94465)). Qed.
Lemma lem7080679 {A : Type'} (s : A -> Prop) (f : A -> real) (_94465 : A) : (term261 A f _94465 s) = (term67 A s f _94465).
Proof. exact (TRANS (@lem7080671 A s f _94465) (@lem7080678 A s f _94465)). Qed.
Lemma lem7080682 {A : Type'} (_94465 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term67 A s f _94465.
Proof. exact (EQ_MP (@lem7080679 A s f _94465) (@lem7080668 A _94465 s f h1)). Qed.
Lemma lem7080683 {A : Type'} (_94465 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term67 A s f _94465.
Proof. exact (@lem7080682 A _94465 s f h1). Qed.
Lemma lem7080684 {A : Type'} (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term67 A s f x'.
Proof. exact (@lem7080683 A x' s f h1). Qed.
Lemma lem7080687 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term74 A s f x') : term70 A f x'.
Proof. exact (@lem7080684 A x' s f h1 (@lem7080639 A s f x' h2)). Qed.
Lemma lem7080688 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term74 A s f x') : term270 A f x'.
Proof. exact (fun h0 : term271 A f x' => @lem7080687 A s f x' h1 h2). Qed.
Lemma lem7080690 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080691 {A : Type'} (f : A -> real) (x' : A) : (term270 A f x') = (term70 A f x').
Proof. exact (@lem7080690 (term70 A f x')). Qed.
Lemma lem7080692 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term74 A s f x') : term70 A f x'.
Proof. exact (EQ_MP (@lem7080691 A f x') (@lem7080688 A s f x' h1 h2)). Qed.
Lemma lem7080698 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7080699 (_94466 : real) (_94467 : real) : (term137 _94466 _94467) = (term272 _94466 _94467).
Proof. exact (@lem7080698 (real_le _94466 _94467) (term273 _94466 _94467)). Qed.
Lemma lem7080705 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7080706 (_94466 : real) (_94467 : real) : (term274 _94466 _94467) = (term275 _94466 _94467).
Proof. exact (MK_COMB (@lem7080705) (@lem7080699 _94466 _94467)). Qed.
Lemma lem7080712 (_94466 : real) (_94467 : real) : (term272 _94466 _94467) = (term272 _94466 _94467).
Proof. exact (eq_refl (term272 _94466 _94467)). Qed.
Lemma lem7080713 (_94466 : real) (_94467 : real) : ((term137 _94466 _94467) = (term272 _94466 _94467)) = ((term272 _94466 _94467) = (term272 _94466 _94467)).
Proof. exact (MK_COMB (@lem7080706 _94466 _94467) (@lem7080712 _94466 _94467)). Qed.
Lemma lem7080715 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7080716 (x : Prop) : (x = x) = True.
Proof. exact (@lem7080715 Prop x). Qed.
Lemma lem7080717 (_94466 : real) (_94467 : real) : ((term272 _94466 _94467) = (term272 _94466 _94467)) = True.
Proof. exact (@lem7080716 (term272 _94466 _94467)). Qed.
Lemma lem7080718 (_94466 : real) (_94467 : real) : ((term137 _94466 _94467) = (term272 _94466 _94467)) = True.
Proof. exact (TRANS (@lem7080713 _94466 _94467) (@lem7080717 _94466 _94467)). Qed.
Lemma lem7080719 (_94466 : real) (_94467 : real) : True = ((term137 _94466 _94467) = (term272 _94466 _94467)).
Proof. exact (SYM (@lem7080718 _94466 _94467)). Qed.
Lemma lem7080720 (_94466 : real) (_94467 : real) : (term137 _94466 _94467) = (term272 _94466 _94467).
Proof. exact (EQ_MP (@lem7080719 _94466 _94467) (@lem0)). Qed.
Lemma lem7080721 (_94466 : real) (_94467 : real) (h1 : term57) : term272 _94466 _94467.
Proof. exact (EQ_MP (@lem7080720 _94466 _94467) (@lem7080341 _94466 _94467 h1)). Qed.
Lemma lem7080723 (b : Prop) (a : Prop) : (a \/ b) = (term264 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7080724 (_94466 : real) (_94467 : real) : (term272 _94466 _94467) = (term276 _94466 _94467).
Proof. exact (@lem7080723 (term273 _94466 _94467) (real_le _94466 _94467)). Qed.
Lemma lem7080726 (a : Prop) : (term266 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7080727 (_94466 : real) (_94467 : real) : (term277 _94466 _94467) = (real_lt _94466 _94467).
Proof. exact (@lem7080726 (real_lt _94466 _94467)). Qed.
Lemma lem7080728 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7080729 (_94466 : real) (_94467 : real) : (term278 _94466 _94467) = (term279 _94466 _94467).
Proof. exact (MK_COMB (@lem7080728) (@lem7080727 _94466 _94467)). Qed.
Lemma lem7080730 (_94466 : real) (_94467 : real) : (real_le _94466 _94467) = (real_le _94466 _94467).
Proof. exact (eq_refl (real_le _94466 _94467)). Qed.
Lemma lem7080731 (_94466 : real) (_94467 : real) : (term276 _94466 _94467) = (term53 _94466 _94467).
Proof. exact (MK_COMB (@lem7080729 _94466 _94467) (@lem7080730 _94466 _94467)). Qed.
Lemma lem7080732 (_94466 : real) (_94467 : real) : (term272 _94466 _94467) = (term53 _94466 _94467).
Proof. exact (TRANS (@lem7080724 _94466 _94467) (@lem7080731 _94466 _94467)). Qed.
Lemma lem7080735 (_94466 : real) (_94467 : real) (h1 : term57) : term53 _94466 _94467.
Proof. exact (EQ_MP (@lem7080732 _94466 _94467) (@lem7080721 _94466 _94467 h1)). Qed.
Lemma lem7080736 {A : Type'} (f : A -> real) (x' : A) (h1 : term57) : term280 A f x'.
Proof. exact (@lem7080735 term281 (f x') h1). Qed.
Lemma lem7080739 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term57) (h3 : term74 A s f x') : term75 A f x'.
Proof. exact (@lem7080736 A f x' h2 (@lem7080692 A s f x' h1 h3)). Qed.
Lemma lem7080740 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term57) (h3 : term74 A s f x') : term282 A f x'.
Proof. exact (fun h0 : term255 A f x' => @lem7080739 A s f x' h1 h2 h3). Qed.
Lemma lem7080742 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080743 {A : Type'} (f : A -> real) (x' : A) : (term282 A f x') = (term75 A f x').
Proof. exact (@lem7080742 (term75 A f x')). Qed.
Lemma lem7080744 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term57) (h3 : term74 A s f x') : term75 A f x'.
Proof. exact (EQ_MP (@lem7080743 A f x') (@lem7080740 A s f x' h1 h2 h3)). Qed.
Lemma lem7080747 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7080749 {A : Type'} (f : A -> real) (x' : A) : (term255 A f x') = (term283 A f x').
Proof. exact (@lem7080747 (term75 A f x')). Qed.
Lemma lem7080752 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term74 A s f x') : term283 A f x'.
Proof. exact (EQ_MP (@lem7080749 A f x') (@lem7080357 A s f x' h1)). Qed.
Lemma lem7080755 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term57) (h3 : term74 A s f x') : False.
Proof. exact (@lem7080752 A s f x' h3 (@lem7080744 A s f x' h1 h2 h3)). Qed.
Lemma lem7080756 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term57) (h3 : term74 A s f x') : term259.
Proof. exact (fun h0 : ~ False => @lem7080755 A s f x' h1 h2 h3). Qed.
Lemma lem7080758 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080759 : term259 = False.
Proof. exact (@lem7080758 False). Qed.
Lemma lem7080760 {A : Type'} (s : A -> Prop) (f : A -> real) (x' : A) (h1 : term15 A s f) (h2 : term57) (h3 : term74 A s f x') : False.
Proof. exact (EQ_MP (@lem7080759) (@lem7080756 A s f x' h1 h2 h3)). Qed.
Lemma lem7080872 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (h1). Qed.
Lemma lem7080873 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term284 A s.
Proof. exact (fun h0 : s = (@EMPTY A) => @lem7080872 A s h1). Qed.
Lemma lem7080875 (p : Prop) : (term285 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7080876 {A : Type'} (s : A -> Prop) : (term284 A s) = (term16 A s).
Proof. exact (@lem7080875 (s = (@EMPTY A))). Qed.
Lemma lem7080877 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term16 A s.
Proof. exact (EQ_MP (@lem7080876 A s) (@lem7080873 A s h1)). Qed.
Lemma lem7080879 (b : Prop) (a : Prop) : (a \/ b) = (term264 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7080882 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : (term221 A x _94474) = (term286 A x _94474).
Proof. exact (@lem7080879 (_94474 = (@EMPTY A)) (term287 A x _94474)). Qed.
Lemma lem7080885 {A : Type'} (_94474 : A -> Prop) (x : type684 A) (h1 : term246 A x) : term286 A x _94474.
Proof. exact (EQ_MP (@lem7080882 A x _94474) (@lem7080379 A _94474 x h1)). Qed.
Lemma lem7080886 {A : Type'} (_94474 : A -> Prop) (x : type684 A) (h1 : term246 A x) : term286 A x _94474.
Proof. exact (@lem7080885 A _94474 x h1). Qed.
Lemma lem7080887 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term246 A x) : term286 A x s.
Proof. exact (@lem7080886 A s x h1). Qed.
Lemma lem7080890 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term16 A s) (h2 : term246 A x) : term287 A x s.
Proof. exact (@lem7080887 A s x h2 (@lem7080877 A s h1)). Qed.
Lemma lem7080891 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term16 A s) (h2 : term246 A x) : term288 A x s.
Proof. exact (fun h0 : term289 A x s => @lem7080890 A s x h1 h2). Qed.
Lemma lem7080893 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080894 {A : Type'} (x : type684 A) (s : A -> Prop) : (term288 A x s) = (term287 A x s).
Proof. exact (@lem7080893 (term287 A x s)). Qed.
Lemma lem7080895 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term16 A s) (h2 : term246 A x) : term287 A x s.
Proof. exact (EQ_MP (@lem7080894 A x s) (@lem7080891 A s x h1 h2)). Qed.
Lemma lem7080901 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7080902 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : (term69 A s f _94471) = (term261 A f _94471 s).
Proof. exact (@lem7080901 (term70 A f _94471) (term146 A _94471 s)). Qed.
Lemma lem7080908 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7080909 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : (term262 A s f _94471) = (term263 A f _94471 s).
Proof. exact (MK_COMB (@lem7080908) (@lem7080902 A f _94471 s)). Qed.
Lemma lem7080915 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : (term261 A f _94471 s) = (term261 A f _94471 s).
Proof. exact (eq_refl (term261 A f _94471 s)). Qed.
Lemma lem7080916 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : ((term69 A s f _94471) = (term261 A f _94471 s)) = ((term261 A f _94471 s) = (term261 A f _94471 s)).
Proof. exact (MK_COMB (@lem7080909 A f _94471 s) (@lem7080915 A f _94471 s)). Qed.
Lemma lem7080918 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7080919 (x : Prop) : (x = x) = True.
Proof. exact (@lem7080918 Prop x). Qed.
Lemma lem7080920 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : ((term261 A f _94471 s) = (term261 A f _94471 s)) = True.
Proof. exact (@lem7080919 (term261 A f _94471 s)). Qed.
Lemma lem7080921 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : ((term69 A s f _94471) = (term261 A f _94471 s)) = True.
Proof. exact (TRANS (@lem7080916 A f _94471 s) (@lem7080920 A f _94471 s)). Qed.
Lemma lem7080922 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : True = ((term69 A s f _94471) = (term261 A f _94471 s)).
Proof. exact (SYM (@lem7080921 A f _94471 s)). Qed.
Lemma lem7080923 {A : Type'} (f : A -> real) (_94471 : A) (s : A -> Prop) : (term69 A s f _94471) = (term261 A f _94471 s).
Proof. exact (EQ_MP (@lem7080922 A f _94471 s) (@lem0)). Qed.
Lemma lem7080924 {A : Type'} (_94471 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term261 A f _94471 s.
Proof. exact (EQ_MP (@lem7080923 A f _94471 s) (@lem7080367 A _94471 s f h1)). Qed.
Lemma lem7080926 (b : Prop) (a : Prop) : (a \/ b) = (term264 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7080927 {A : Type'} (s : A -> Prop) (f : A -> real) (_94471 : A) : (term261 A f _94471 s) = (term265 A s f _94471).
Proof. exact (@lem7080926 (term146 A _94471 s) (term70 A f _94471)). Qed.
Lemma lem7080929 (a : Prop) : (term266 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7080930 {A : Type'} (_94471 : A) (s : A -> Prop) : (term267 A _94471 s) = (@IN A _94471 s).
Proof. exact (@lem7080929 (@IN A _94471 s)). Qed.
Lemma lem7080931 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7080932 {A : Type'} (_94471 : A) (s : A -> Prop) : (term268 A _94471 s) = (term269 A _94471 s).
Proof. exact (MK_COMB (@lem7080931) (@lem7080930 A _94471 s)). Qed.
Lemma lem7080933 {A : Type'} (f : A -> real) (_94471 : A) : (term70 A f _94471) = (term70 A f _94471).
Proof. exact (eq_refl (term70 A f _94471)). Qed.
Lemma lem7080934 {A : Type'} (s : A -> Prop) (f : A -> real) (_94471 : A) : (term265 A s f _94471) = (term67 A s f _94471).
Proof. exact (MK_COMB (@lem7080932 A _94471 s) (@lem7080933 A f _94471)). Qed.
Lemma lem7080935 {A : Type'} (s : A -> Prop) (f : A -> real) (_94471 : A) : (term261 A f _94471 s) = (term67 A s f _94471).
Proof. exact (TRANS (@lem7080927 A s f _94471) (@lem7080934 A s f _94471)). Qed.
Lemma lem7080938 {A : Type'} (_94471 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term67 A s f _94471.
Proof. exact (EQ_MP (@lem7080935 A s f _94471) (@lem7080924 A _94471 s f h1)). Qed.
Lemma lem7080939 {A : Type'} (_94471 : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term67 A s f _94471.
Proof. exact (@lem7080938 A _94471 s f h1). Qed.
Lemma lem7080940 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) : term290 A f x s.
Proof. exact (@lem7080939 A (x s) s f h1). Qed.
Lemma lem7080943 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term16 A s) (h3 : term246 A x) : term291 A f x s.
Proof. exact (@lem7080940 A x s f h1 (@lem7080895 A s x h2 h3)). Qed.
Lemma lem7080944 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term16 A s) (h3 : term246 A x) : term292 A f x s.
Proof. exact (fun h0 : term293 A f x s => @lem7080943 A f s x h1 h2 h3). Qed.
Lemma lem7080946 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7080947 {A : Type'} (f : A -> real) (x : type684 A) (s : A -> Prop) : (term292 A f x s) = (term291 A f x s).
Proof. exact (@lem7080946 (term291 A f x s)). Qed.
Lemma lem7080948 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term16 A s) (h3 : term246 A x) : term291 A f x s.
Proof. exact (EQ_MP (@lem7080947 A f x s) (@lem7080944 A f s x h1 h2 h3)). Qed.
Lemma lem7080950 (b : Prop) (a : Prop) : (a \/ b) = (term264 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7080951 {A : Type'} (f : A -> real) (_94477 : A) (s : A -> Prop) : (term86 A s f _94477) = (term294 A f _94477 s).
Proof. exact (@lem7080950 (term271 A f _94477) (term146 A _94477 s)). Qed.
Lemma lem7080953 (a : Prop) : (term266 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem7080954 {A : Type'} (f : A -> real) (_94477 : A) : (term295 A f _94477) = (term70 A f _94477).
Proof. exact (@lem7080953 (term70 A f _94477)). Qed.
Lemma lem7080955 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem7080956 {A : Type'} (f : A -> real) (_94477 : A) : (term296 A f _94477) = (term297 A f _94477).
Proof. exact (MK_COMB (@lem7080955) (@lem7080954 A f _94477)). Qed.
Lemma lem7080957 {A : Type'} (_94477 : A) (s : A -> Prop) : (term146 A _94477 s) = (term146 A _94477 s).
Proof. exact (eq_refl (term146 A _94477 s)). Qed.
Lemma lem7080958 {A : Type'} (f : A -> real) (_94477 : A) (s : A -> Prop) : (term294 A f _94477 s) = (term298 A f _94477 s).
Proof. exact (MK_COMB (@lem7080956 A f _94477) (@lem7080957 A _94477 s)). Qed.
Lemma lem7080959 {A : Type'} (f : A -> real) (_94477 : A) (s : A -> Prop) : (term86 A s f _94477) = (term298 A f _94477 s).
Proof. exact (TRANS (@lem7080951 A f _94477 s) (@lem7080958 A f _94477 s)). Qed.
Lemma lem7080962 {A : Type'} (_94477 : A) (s : A -> Prop) (f : A -> real) (h1 : term95 A s f) : term298 A f _94477 s.
Proof. exact (EQ_MP (@lem7080959 A f _94477 s) (@lem7080391 A _94477 s f h1)). Qed.
Lemma lem7080963 {A : Type'} (_94477 : A) (s : A -> Prop) (f : A -> real) (h1 : term95 A s f) : term298 A f _94477 s.
Proof. exact (@lem7080962 A _94477 s f h1). Qed.
Lemma lem7080964 {A : Type'} (x : type684 A) (s : A -> Prop) (f : A -> real) (h1 : term95 A s f) : term299 A f x s.
Proof. exact (@lem7080963 A (x s) s f h1). Qed.
Lemma lem7080967 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : term289 A x s.
Proof. exact (@lem7080964 A x s f h2 (@lem7080948 A f s x h1 h3 h4)). Qed.
Lemma lem7080968 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : term300 A x s.
Proof. exact (fun h0 : term287 A x s => @lem7080967 A f s x h1 h2 h3 h4). Qed.
Lemma lem7080970 (p : Prop) : (term285 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem7080971 {A : Type'} (x : type684 A) (s : A -> Prop) : (term300 A x s) = (term289 A x s).
Proof. exact (@lem7080970 (term287 A x s)). Qed.
Lemma lem7080972 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : term289 A x s.
Proof. exact (EQ_MP (@lem7080971 A x s) (@lem7080968 A f s x h1 h2 h3 h4)). Qed.
Lemma lem7080978 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem7080979 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : (term221 A x _94474) = (term301 A x _94474).
Proof. exact (@lem7080978 (_94474 = (@EMPTY A)) (term287 A x _94474)). Qed.
Lemma lem7080987 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem7080988 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : (term302 A x _94474) = (term303 A x _94474).
Proof. exact (MK_COMB (@lem7080987) (@lem7080979 A x _94474)). Qed.
Lemma lem7080996 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : (term301 A x _94474) = (term301 A x _94474).
Proof. exact (eq_refl (term301 A x _94474)). Qed.
Lemma lem7080997 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : ((term221 A x _94474) = (term301 A x _94474)) = ((term301 A x _94474) = (term301 A x _94474)).
Proof. exact (MK_COMB (@lem7080988 A x _94474) (@lem7080996 A x _94474)). Qed.
Lemma lem7080999 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem7081000 (x : Prop) : (x = x) = True.
Proof. exact (@lem7080999 Prop x). Qed.
Lemma lem7081001 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : ((term301 A x _94474) = (term301 A x _94474)) = True.
Proof. exact (@lem7081000 (term301 A x _94474)). Qed.
Lemma lem7081002 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : ((term221 A x _94474) = (term301 A x _94474)) = True.
Proof. exact (TRANS (@lem7080997 A x _94474) (@lem7081001 A x _94474)). Qed.
Lemma lem7081003 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : True = ((term221 A x _94474) = (term301 A x _94474)).
Proof. exact (SYM (@lem7081002 A x _94474)). Qed.
Lemma lem7081004 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : (term221 A x _94474) = (term301 A x _94474).
Proof. exact (EQ_MP (@lem7081003 A x _94474) (@lem0)). Qed.
Lemma lem7081005 {A : Type'} (_94474 : A -> Prop) (x : type684 A) (h1 : term246 A x) : term301 A x _94474.
Proof. exact (EQ_MP (@lem7081004 A x _94474) (@lem7080379 A _94474 x h1)). Qed.
Lemma lem7081007 (b : Prop) (a : Prop) : (a \/ b) = (term264 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem7081010 {A : Type'} (x : type684 A) (_94474 : A -> Prop) : (term301 A x _94474) = (term304 A x _94474).
Proof. exact (@lem7081007 (term287 A x _94474) (_94474 = (@EMPTY A))). Qed.
Lemma lem7081013 {A : Type'} (_94474 : A -> Prop) (x : type684 A) (h1 : term246 A x) : term304 A x _94474.
Proof. exact (EQ_MP (@lem7081010 A x _94474) (@lem7081005 A _94474 x h1)). Qed.
Lemma lem7081014 {A : Type'} (_94474 : A -> Prop) (x : type684 A) (h1 : term246 A x) : term304 A x _94474.
Proof. exact (@lem7081013 A _94474 x h1). Qed.
Lemma lem7081015 {A : Type'} (s : A -> Prop) (x : type684 A) (h1 : term246 A x) : term304 A x s.
Proof. exact (@lem7081014 A s x h1). Qed.
Lemma lem7081018 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : s = (@EMPTY A).
Proof. exact (@lem7081015 A s x h4 (@lem7080972 A f s x h1 h2 h3 h4)). Qed.
Lemma lem7081019 {A : Type'} (s : A -> Prop) (f : A -> real) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term246 A x) : term305 A s.
Proof. exact (fun h0 : term16 A s => @lem7081018 A f s x h1 h2 h0 h3). Qed.
Lemma lem7081021 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7081022 {A : Type'} (s : A -> Prop) : (term305 A s) = (s = (@EMPTY A)).
Proof. exact (@lem7081021 (s = (@EMPTY A))). Qed.
Lemma lem7081023 {A : Type'} (s : A -> Prop) (f : A -> real) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term246 A x) : s = (@EMPTY A).
Proof. exact (EQ_MP (@lem7081022 A s) (@lem7081019 A s f x h1 h2 h3)). Qed.
Lemma lem7081026 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem7081028 {A : Type'} (s : A -> Prop) : (term16 A s) = (term306 A s).
Proof. exact (@lem7081026 (s = (@EMPTY A))). Qed.
Lemma lem7081031 {A : Type'} (s : A -> Prop) (h1 : term16 A s) : term306 A s.
Proof. exact (EQ_MP (@lem7081028 A s) (@lem7080361 A s h1)). Qed.
Lemma lem7081034 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : False.
Proof. exact (@lem7081031 A s h3 (@lem7081023 A s f x h1 h2 h4)). Qed.
Lemma lem7081035 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : term259.
Proof. exact (fun h0 : ~ False => @lem7081034 A f s x h1 h2 h3 h4). Qed.
Lemma lem7081037 (p : Prop) : (term257 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem7081038 : term259 = False.
Proof. exact (@lem7081037 False). Qed.
Lemma lem7081039 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : False.
Proof. exact (EQ_MP (@lem7081038) (@lem7081035 A f s x h1 h2 h3 h4)). Qed.
Lemma lem7081040 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : (term16 A s) = False.
Proof. exact (prop_ext (fun h5 : term16 A s => @lem7081039 A f s x h1 h2 h3 h4) (fun h5 : False => @lem7080361 A s h3)). Qed.
Lemma lem7081041 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : False.
Proof. exact (EQ_MP (@lem7081040 A f s x h1 h2 h3 h4) (@lem7080361 A s h3)). Qed.
Lemma lem7081042 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : (term126 A s) = False.
Proof. exact (prop_ext (fun h3 : term126 A s => @lem7080523 A s h1 h2) (fun h3 : False => @lem7080325 A s h2)). Qed.
Lemma lem7081043 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (EQ_MP (@lem7081042 A s h1 h2) (@lem7080325 A s h2)). Qed.
Lemma lem7081044 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7081043 A s h1 h2) (fun h3 : False => @lem7080297 A s h1)). Qed.
Lemma lem7081045 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (EQ_MP (@lem7081044 A s h1 h2) (@lem7080297 A s h1)). Qed.
Lemma lem7081046 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : (term16 A s) = False.
Proof. exact (prop_ext (fun h5 : term16 A s => @lem7081041 A f s x h1 h2 h3 h4) (fun h5 : False => @lem7080141 A s h3)). Qed.
Lemma lem7081047 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : False.
Proof. exact (EQ_MP (@lem7081046 A f s x h1 h2 h3 h4) (@lem7080141 A s h3)). Qed.
Lemma lem7081048 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : (term126 A s) = False.
Proof. exact (prop_ext (fun h3 : term126 A s => @lem7081045 A s h1 h2) (fun h3 : False => @lem7080033 A s h2)). Qed.
Lemma lem7081049 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (EQ_MP (@lem7081048 A s h1 h2) (@lem7080033 A s h2)). Qed.
Lemma lem7081050 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7081049 A s h1 h2) (fun h3 : False => @lem7079941 A s h1)). Qed.
Lemma lem7081051 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (EQ_MP (@lem7081050 A s h1 h2) (@lem7079941 A s h1)). Qed.
Lemma lem7081052 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : (term95 A s f) = False.
Proof. exact (prop_ext (fun h5 : term95 A s f => @lem7081047 A f s x h1 h2 h3 h4) (fun h5 : False => @lem7080238 A s f h2)). Qed.
Lemma lem7081053 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : False.
Proof. exact (EQ_MP (@lem7081052 A f s x h1 h2 h3 h4) (@lem7080238 A s f h2)). Qed.
Lemma lem7081054 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : (term16 A s) = False.
Proof. exact (prop_ext (fun h5 : term16 A s => @lem7081053 A f s x h1 h2 h3 h4) (fun h5 : False => @lem7080141 A s h3)). Qed.
Lemma lem7081055 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term95 A s f) (h3 : term16 A s) (h4 : term246 A x) : False.
Proof. exact (EQ_MP (@lem7081054 A f s x h1 h2 h3 h4) (@lem7080141 A s h3)). Qed.
Lemma lem7081056 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : (term126 A s) = False.
Proof. exact (prop_ext (fun h3 : term126 A s => @lem7081051 A s h1 h2) (fun h3 : False => @lem7080033 A s h2)). Qed.
Lemma lem7081057 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (EQ_MP (@lem7081056 A s h1 h2) (@lem7080033 A s h2)). Qed.
Lemma lem7081058 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7081057 A s h1 h2) (fun h3 : False => @lem7079941 A s h1)). Qed.
Lemma lem7081059 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) (h2 : term126 A s) : False.
Proof. exact (EQ_MP (@lem7081058 A s h1 h2) (@lem7079941 A s h1)). Qed.
Lemma lem7081060 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : term16 A s) (h4 : term246 A x) (h5 : term117 A x' s f) : False.
Proof. exact (or_elim (@lem7079933 A x' s f h5) (fun h0 : term74 A s f x' => @lem7080760 A s f x' h1 h2 h0) (fun h0 : term95 A s f => @lem7081055 A f s x h1 h0 h3 h4)). Qed.
Lemma lem7081061 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : False.
Proof. exact (or_elim (@lem7079929 A x' s f h6) (fun h0 : term126 A s => @lem7081059 A s h3 h0) (fun h0 : term117 A x' s f => @lem7081060 A x x' s f h1 h2 h4 h5 h0)). Qed.
Lemma lem7081062 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : (term133 A x' s f) = False.
Proof. exact (prop_ext (fun h7 : term133 A x' s f => @lem7081061 A x x' s f h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7079929 A x' s f h6)). Qed.
Lemma lem7081063 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : False.
Proof. exact (EQ_MP (@lem7081062 A x x' s f h1 h2 h3 h4 h5 h6) (@lem7079929 A x' s f h6)). Qed.
Lemma lem7081064 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : (term246 A x) = False.
Proof. exact (prop_ext (fun h7 : term246 A x => @lem7081063 A x x' s f h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7079870 A x h5)). Qed.
Lemma lem7081065 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : False.
Proof. exact (EQ_MP (@lem7081064 A x x' s f h1 h2 h3 h4 h5 h6) (@lem7079870 A x h5)). Qed.
Lemma lem7081066 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : (term16 A s) = False.
Proof. exact (prop_ext (fun h7 : term16 A s => @lem7081065 A x x' s f h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7079778 A s h4)). Qed.
Lemma lem7081067 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : False.
Proof. exact (EQ_MP (@lem7081066 A x x' s f h1 h2 h3 h4 h5 h6) (@lem7079778 A s h4)). Qed.
Lemma lem7081068 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE A s => @lem7081067 A x x' s f h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7079770 A s h3)). Qed.
Lemma lem7081069 {A : Type'} (x : type684 A) (x' : A) (s : A -> Prop) (f : A -> real) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term16 A s) (h5 : term246 A x) (h6 : term133 A x' s f) : False.
Proof. exact (EQ_MP (@lem7081068 A x x' s f h1 h2 h3 h4 h5 h6) (@lem7079770 A s h3)). Qed.
Lemma lem7081070 {A : Type'} (f : A -> real) (s : A -> Prop) (x : type684 A) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) (h6 : term246 A x) : False.
Proof. exact (ex_elim (@lem7079440 A s f h4) (fun x' : A => fun h0 : term135 A s f x' => @lem7081069 A x x' s f h1 h2 h3 h5 h6 h0)). Qed.
Lemma lem7081071 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : term57) (h4 : @FINITE A s) (h5 : term19 A s f) (h6 : term16 A s) : False.
Proof. exact (ex_elim (@lem7079764 A h2) (fun x : type684 A => fun h0 : term248 A x => @lem7081070 A f s x h1 h3 h4 h5 h6 h0)). Qed.
Lemma lem7081072 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : term57) (h4 : @FINITE A s) (h5 : term19 A s f) (h6 : term16 A s) : (term16 A s) = False.
Proof. exact (prop_ext (fun h7 : term16 A s => @lem7081071 A f s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7079185 A s h6)). Qed.
Lemma lem7081073 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : term57) (h4 : @FINITE A s) (h5 : term19 A s f) (h6 : term16 A s) : False.
Proof. exact (EQ_MP (@lem7081072 A f s h1 h2 h3 h4 h5 h6) (@lem7079185 A s h6)). Qed.
Lemma lem7081074 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : term57) (h4 : @FINITE A s) (h5 : term19 A s f) (h6 : term16 A s) : (@FINITE A s) = False.
Proof. exact (prop_ext (fun h7 : @FINITE A s => @lem7081073 A f s h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem7079179 A s h4)). Qed.
Lemma lem7081075 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : term20 A) (h3 : term57) (h4 : @FINITE A s) (h5 : term19 A s f) (h6 : term16 A s) : False.
Proof. exact (EQ_MP (@lem7081074 A f s h1 h2 h3 h4 h5 h6) (@lem7079179 A s h4)). Qed.
Lemma lem7081076 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) : term25 A.
Proof. exact (fun h0 : term20 A => @lem7081075 A f s h1 h0 h2 h3 h4 h5). Qed.
Lemma lem7081077 {A : Type'} : (term25 A) = (term26 A).
Proof. exact (@lem69 (term20 A)). Qed.
Lemma lem7081078 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : term57) (h3 : @FINITE A s) (h4 : term19 A s f) (h5 : term16 A s) : term26 A.
Proof. exact (EQ_MP (@lem7081077 A) (@lem7081076 A f s h1 h2 h3 h4 h5)). Qed.
Lemma lem7081079 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term29 A.
Proof. exact (fun h0 : term57 => @lem7081078 A f s h1 h0 h2 h3 h4). Qed.
Lemma lem7081080 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term32 A s f.
Proof. exact (fun h0 : term19 A s f => @lem7081079 A f s h1 h2 h0 h3). Qed.
Lemma lem7081081 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term16 A s) : term35 A s f.
Proof. exact (fun h0 : term15 A s f => @lem7081080 A f s h0 h1 h2). Qed.
Lemma lem7081082 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : term38 A s f.
Proof. exact (fun h0 : term16 A s => @lem7081081 A f s h1 h0). Qed.
Lemma lem7081083 {A : Type'} (s : A -> Prop) (f : A -> real) : term40 A s f.
Proof. exact (fun h0 : @FINITE A s => @lem7081082 A f s h0). Qed.
Lemma lem7081088 {A : Type'} (f : A -> real) : term44 A f.
Proof. exact (fun s : A -> Prop => @lem7081083 A s f). Qed.
Lemma lem7081093 {A : Type'} : term48 A.
Proof. exact (fun f : A -> real => @lem7081088 A f). Qed.
Lemma lem7081094 {A : Type'} : term47 A.
Proof. exact (EQ_MP (@lem7079167 A) (@lem7081093 A)). Qed.
Lemma lem7081095 {A : Type'} (f : A -> real) : term307 A f.
Proof. exact (@lem7081094 A f). Qed.
Lemma lem7081096 {A : Type'} (f : A -> real) : (term307 A f) = (term43 A f).
Proof. exact (eq_refl (term307 A f)). Qed.
Lemma lem7081097 {A : Type'} (f : A -> real) : term43 A f.
Proof. exact (EQ_MP (@lem7081096 A f) (@lem7081095 A f)). Qed.
Lemma lem7081098 {A : Type'} (f : A -> real) (s : A -> Prop) : term308 A f s.
Proof. exact (@lem7081097 A f s). Qed.
Lemma lem7081099 {A : Type'} (s : A -> Prop) (f : A -> real) : (term308 A f s) = (term21 A s f).
Proof. exact (eq_refl (term308 A f s)). Qed.
Lemma lem7081100 {A : Type'} (s : A -> Prop) (f : A -> real) : term21 A s f.
Proof. exact (EQ_MP (@lem7081099 A s f) (@lem7081098 A f s)). Qed.
Lemma lem7081102 {A : Type'} (s : A -> Prop) (f : A -> real) : term21 A s f.
Proof. exact (@lem7078860 A s f (@lem7081100 A s f)). Qed.
Lemma lem7081103 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) : term37 A s f.
Proof. exact (@lem7081102 A s f (@lem7078831 A s h1)). Qed.
Lemma lem7081104 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term16 A s) : term34 A s f.
Proof. exact (@lem7081103 A f s h1 (@lem7078833 A s h2)). Qed.
Lemma lem7081105 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term31 A s f.
Proof. exact (@lem7081104 A f s h2 h3 (@lem7078832 A s f h1)). Qed.
Lemma lem7081106 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term28 A.
Proof. exact (@lem7081105 A f s h1 h2 h4 (@lem7078841 A s f h3)). Qed.
Lemma lem7081107 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : term25 A.
Proof. exact (@lem7081106 A f s h1 h2 h3 h4 (@lem1369133)). Qed.
Lemma lem7081108 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : False.
Proof. exact (@lem7081107 A f s h1 h2 h3 h4 (@lem7078842 A)). Qed.
Lemma lem7081109 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : (term19 A s f) = False.
Proof. exact (prop_ext (fun h5 : term19 A s f => @lem7081108 A f s h1 h2 h3 h4) (fun h5 : False => @lem7078841 A s f h3)). Qed.
Lemma lem7081110 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term19 A s f) (h4 : term16 A s) : False.
Proof. exact (EQ_MP (@lem7081109 A f s h1 h2 h3 h4) (@lem7078841 A s f h3)). Qed.
Lemma lem7081111 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term18 A s f.
Proof. exact (fun h0 : term19 A s f => @lem7081110 A f s h1 h2 h0 h3). Qed.
Lemma lem7081112 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term5 A s f.
Proof. exact (EQ_MP (@lem7078840 A s f) (@lem7081111 A f s h1 h2 h3)). Qed.
Lemma lem7081113 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term6 A s f.
Proof. exact (@lem7078836 A s f (@lem7081112 A f s h1 h2 h3)). Qed.
Lemma lem7081114 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term13 A s f) : term14 A s f.
Proof. exact (proj2 (@lem7078829 A s f h1)). Qed.
Lemma lem7081115 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term13 A s f) : @FINITE A s.
Proof. exact (proj1 (@lem7078829 A s f h1)). Qed.
Lemma lem7081116 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term14 A s f) : term15 A s f.
Proof. exact (proj2 (@lem7078830 A s f h1)). Qed.
Lemma lem7081117 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term14 A s f) : term16 A s.
Proof. exact (proj1 (@lem7078830 A s f h1)). Qed.
Lemma lem7081118 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : (term15 A s f) = (term6 A s f).
Proof. exact (prop_ext (fun h4 : term15 A s f => @lem7081113 A f s h1 h2 h3) (fun h4 : term6 A s f => @lem7078832 A s f h1)). Qed.
Lemma lem7081119 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term6 A s f.
Proof. exact (EQ_MP (@lem7081118 A f s h1 h2 h3) (@lem7078832 A s f h1)). Qed.
Lemma lem7081120 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : (term16 A s) = (term6 A s f).
Proof. exact (prop_ext (fun h4 : term16 A s => @lem7081119 A f s h1 h2 h3) (fun h4 : term6 A s f => @lem7078833 A s h3)). Qed.
Lemma lem7081121 {A : Type'} (f : A -> real) (s : A -> Prop) (h1 : term15 A s f) (h2 : @FINITE A s) (h3 : term16 A s) : term6 A s f.
Proof. exact (EQ_MP (@lem7081120 A f s h1 h2 h3) (@lem7078833 A s h3)). Qed.
Lemma lem7081122 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term16 A s) (h3 : term14 A s f) : (term15 A s f) = (term6 A s f).
Proof. exact (prop_ext (fun h4 : term15 A s f => @lem7081121 A f s h4 h1 h2) (fun h4 : term6 A s f => @lem7081116 A s f h3)). Qed.
Lemma lem7081123 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term16 A s) (h3 : term14 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem7081122 A s f h1 h2 h3) (@lem7081116 A s f h3)). Qed.
Lemma lem7081124 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term14 A s f) : (term16 A s) = (term6 A s f).
Proof. exact (prop_ext (fun h3 : term16 A s => @lem7081123 A s f h1 h3 h2) (fun h3 : term6 A s f => @lem7081117 A s f h2)). Qed.
Lemma lem7081125 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term14 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem7081124 A s f h1 h2) (@lem7081117 A s f h2)). Qed.
Lemma lem7081126 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term14 A s f) : (@FINITE A s) = (term6 A s f).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem7081125 A s f h1 h2) (fun h3 : term6 A s f => @lem7078831 A s h1)). Qed.
Lemma lem7081127 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term14 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem7081126 A s f h1 h2) (@lem7078831 A s h1)). Qed.
Lemma lem7081128 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term13 A s f) : (term14 A s f) = (term6 A s f).
Proof. exact (prop_ext (fun h3 : term14 A s f => @lem7081127 A s f h1 h3) (fun h3 : term6 A s f => @lem7081114 A s f h2)). Qed.
Lemma lem7081129 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : @FINITE A s) (h2 : term13 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem7081128 A s f h1 h2) (@lem7081114 A s f h2)). Qed.
Lemma lem7081130 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term13 A s f) : (@FINITE A s) = (term6 A s f).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem7081129 A s f h2 h1) (fun h2 : term6 A s f => @lem7081115 A s f h1)). Qed.
Lemma lem7081131 {A : Type'} (s : A -> Prop) (f : A -> real) (h1 : term13 A s f) : term6 A s f.
Proof. exact (EQ_MP (@lem7081130 A s f h1) (@lem7081115 A s f h1)). Qed.
Lemma lem7081132 {A : Type'} (s : A -> Prop) (f : A -> real) : term309 A s f.
Proof. exact (fun h0 : term13 A s f => @lem7081131 A s f h0). Qed.
Lemma lem7081137 {A : Type'} (s : A -> Prop) : term310 A s.
Proof. exact (fun f : A -> real => @lem7081132 A s f). Qed.
Lemma lem7081142 {A : Type'} : term311 A.
Proof. exact (fun s : A -> Prop => @lem7081137 A s). Qed.
