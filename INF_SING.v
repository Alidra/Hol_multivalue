Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INF_SING_term_abbrevs.
Require Import FINITE_EMPTY_spec.
Require Import INF_INSERT_FINITE_spec.
Require Import thm0_spec.
Require Import thm15249_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem5256774 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = ((@FINITE _92140 (@EMPTY _92140)) = True).
Proof. exact (@lem7 (@FINITE _92140 (@EMPTY _92140))). Qed.
Lemma lem5256776 (x : real) : term0 x.
Proof. exact (@lem5256773 x). Qed.
Lemma lem5256777 (x : real) : (term0 x) = (term1 x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem5256778 (x : real) : term1 x.
Proof. exact (EQ_MP (@lem5256777 x) (@lem5256776 x)). Qed.
Lemma lem5256779 (x : real) (s : real -> Prop) : term2 x s.
Proof. exact (@lem5256778 x s). Qed.
Lemma lem5256780 (x : real) (s : real -> Prop) : (term2 x s) = (term3 x s).
Proof. exact (eq_refl (term2 x s)). Qed.
Lemma lem5256781 (x : real) (s : real -> Prop) : term3 x s.
Proof. exact (EQ_MP (@lem5256780 x s) (@lem5256779 x s)). Qed.
Lemma lem5256782 (s : real -> Prop) (h1 : @FINITE real s) : @FINITE real s.
Proof. exact (h1). Qed.
Lemma lem5256783 (x : real) (s : real -> Prop) (h1 : @FINITE real s) : (term4 x s) = (term5 x s).
Proof. exact (@lem5256781 x s (@lem5256782 s h1)). Qed.
Lemma lem5256796 (x : real) (s : real -> Prop) : term3 x s.
Proof. exact (fun h0 : @FINITE real s => @lem5256783 x s h0). Qed.
Lemma lem5256797 (a : real) : term6 a.
Proof. exact (@lem5256796 a (@EMPTY real)). Qed.
Lemma lem5256799 {_92140 : Type'} : (@FINITE _92140 (@EMPTY _92140)) = True.
Proof. exact (EQ_MP (@lem5256774 _92140) (@lem3596285 _92140)). Qed.
Lemma lem5256800 : (@FINITE real (@EMPTY real)) = True.
Proof. exact (@lem5256799 real). Qed.
Lemma lem5256801 : True = (@FINITE real (@EMPTY real)).
Proof. exact (SYM (@lem5256800)). Qed.
Lemma lem5256802 : @FINITE real (@EMPTY real).
Proof. exact (EQ_MP (@lem5256801) (@lem0)). Qed.
Lemma lem5256803 (a : real) : (term7 a) = (term8 a).
Proof. exact (@lem5256797 a (@lem5256802)). Qed.
Lemma lem5256805 {_2975 _2982 : Type'} (x : _2982) (z : _2975) (y : _2975) : (term9 _2975 _2982 x y z) = y.
Proof. exact (EQ_MP (@lem15249 _2975 _2982 x z y) (@lem0)). Qed.
Lemma lem5256806 (x : real -> Prop) (z : real) (y : real) : (term10 x y z) = y.
Proof. exact (@lem5256805 real (real -> Prop) x z y). Qed.
Lemma lem5256807 (a : real) : (term8 a) = a.
Proof. exact (@lem5256806 (@EMPTY real) (term11 a) a). Qed.
Lemma lem5256808 (a : real) : (term7 a) = a.
Proof. exact (TRANS (@lem5256803 a) (@lem5256807 a)). Qed.
Lemma lem5256809 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem5256810 (a : real) : (term12 a) = (@eq real a).
Proof. exact (MK_COMB (@lem5256809) (@lem5256808 a)). Qed.
Lemma lem5256811 (a : real) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem5256812 (a : real) : ((term7 a) = a) = (a = a).
Proof. exact (MK_COMB (@lem5256810 a) (@lem5256811 a)). Qed.
Lemma lem5256814 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5256815 (x : real) : (x = x) = True.
Proof. exact (@lem5256814 real x). Qed.
Lemma lem5256816 (a : real) : (a = a) = True.
Proof. exact (@lem5256815 a). Qed.
Lemma lem5256817 (a : real) : ((term7 a) = a) = True.
Proof. exact (TRANS (@lem5256812 a) (@lem5256816 a)). Qed.
Lemma lem5256818 : term13 = term14.
Proof. exact (fun_ext (fun a : real => @lem5256817 a)). Qed.
Lemma lem5256819 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem5256820 : term15 = term16.
Proof. exact (MK_COMB (@lem5256819) (@lem5256818)). Qed.
Lemma lem5256822 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem5256823 (t : Prop) : (term18 t) = t.
Proof. exact (@lem5256822 real t). Qed.
Lemma lem5256824 : term16 = True.
Proof. exact (@lem5256823 True). Qed.
Lemma lem5256825 : term15 = True.
Proof. exact (TRANS (@lem5256820) (@lem5256824)). Qed.
Lemma lem5256826 : True = term15.
Proof. exact (SYM (@lem5256825)). Qed.
Lemma lem5256827 : term15.
Proof. exact (EQ_MP (@lem5256826) (@lem0)). Qed.
