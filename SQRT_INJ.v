Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SQRT_INJ_term_abbrevs.
Require Import SQRT_MONO_LE_EQ_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1954892 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (term0 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1954893 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (x = y) = (term0 y x).
Proof. exact (SYM (@lem1954892 x y h1)). Qed.
Lemma lem1954894 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (x = y) = (term0 y x).
Proof. exact (h1). Qed.
Lemma lem1954895 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (term0 y x) = (x = y).
Proof. exact (SYM (@lem1954894 y x h1)). Qed.
Lemma lem1954896 (y : real) (x : real) : ((term0 y x) = (x = y)) = ((x = y) = (term0 y x)).
Proof. exact (prop_ext (fun h1 : (term0 y x) = (x = y) => @lem1954893 x y h1) (fun h1 : (x = y) = (term0 y x) => @lem1954895 y x h1)). Qed.
Lemma lem1954897 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1954896 y x)). Qed.
Lemma lem1954898 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954899 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1954898) (@lem1954897 x)). Qed.
Lemma lem1954900 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1954899 x)). Qed.
Lemma lem1954901 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954902 : term7 = term8.
Proof. exact (MK_COMB (@lem1954901) (@lem1954900)). Qed.
Lemma lem1954903 : term8.
Proof. exact (EQ_MP (@lem1954902) (@lem1339379)). Qed.
Lemma lem1954904 (x : real) : term9 x.
Proof. exact (@lem1954889 x). Qed.
Lemma lem1954905 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1954906 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1954905 x) (@lem1954904 x)). Qed.
Lemma lem1954907 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1954906 x y). Qed.
Lemma lem1954908 (x : real) (y : real) : (term11 x y) = ((term12 x y) = (real_le x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1954910 (x : real) : term13 x.
Proof. exact (@lem1954903 x). Qed.
Lemma lem1954911 (x : real) : (term13 x) = (term4 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem1954912 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1954911 x) (@lem1954910 x)). Qed.
Lemma lem1954913 (x : real) (y : real) : term14 x y.
Proof. exact (@lem1954912 x y). Qed.
Lemma lem1954914 (y : real) (x : real) : (term14 x y) = ((x = y) = (term0 y x)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem1954931 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem1954914 y x) (@lem1954913 x y)). Qed.
Lemma lem1954932 (y : real) (x : real) : ((sqrt x) = (sqrt y)) = (term15 y x).
Proof. exact (@lem1954931 (sqrt y) (sqrt x)). Qed.
Lemma lem1954936 (x : real) (y : real) : (term12 x y) = (real_le x y).
Proof. exact (EQ_MP (@lem1954908 x y) (@lem1954907 x y)). Qed.
Lemma lem1954937 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1954938 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1954937) (@lem1954936 x y)). Qed.
Lemma lem1954940 (x : real) (y : real) : (term12 x y) = (real_le x y).
Proof. exact (EQ_MP (@lem1954908 x y) (@lem1954907 x y)). Qed.
Lemma lem1954941 (y : real) (x : real) : (term12 y x) = (real_le y x).
Proof. exact (@lem1954940 y x). Qed.
Lemma lem1954942 (y : real) (x : real) : (term15 y x) = (term0 y x).
Proof. exact (MK_COMB (@lem1954938 x y) (@lem1954941 y x)). Qed.
Lemma lem1954945 (y : real) (x : real) : ((sqrt x) = (sqrt y)) = (term0 y x).
Proof. exact (TRANS (@lem1954932 y x) (@lem1954942 y x)). Qed.
Lemma lem1954946 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1954947 (y : real) (x : real) : (term18 x y) = (term19 y x).
Proof. exact (MK_COMB (@lem1954946) (@lem1954945 y x)). Qed.
Lemma lem1954953 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem1954914 y x) (@lem1954913 x y)). Qed.
Lemma lem1954956 (y : real) (x : real) : (((sqrt x) = (sqrt y)) = (x = y)) = ((term0 y x) = (term0 y x)).
Proof. exact (MK_COMB (@lem1954947 y x) (@lem1954953 y x)). Qed.
Lemma lem1954958 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1954959 (x : Prop) : (x = x) = True.
Proof. exact (@lem1954958 Prop x). Qed.
Lemma lem1954960 (y : real) (x : real) : ((term0 y x) = (term0 y x)) = True.
Proof. exact (@lem1954959 (term0 y x)). Qed.
Lemma lem1954961 (x : real) (y : real) : (((sqrt x) = (sqrt y)) = (x = y)) = True.
Proof. exact (TRANS (@lem1954956 y x) (@lem1954960 y x)). Qed.
Lemma lem1954962 (x : real) : (term20 x) = term21.
Proof. exact (fun_ext (fun y : real => @lem1954961 x y)). Qed.
Lemma lem1954963 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954964 (x : real) : (term22 x) = term23.
Proof. exact (MK_COMB (@lem1954963) (@lem1954962 x)). Qed.
Lemma lem1954966 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1954967 (t : Prop) : (term25 t) = t.
Proof. exact (@lem1954966 real t). Qed.
Lemma lem1954968 : term23 = True.
Proof. exact (@lem1954967 True). Qed.
Lemma lem1954969 (x : real) : (term22 x) = True.
Proof. exact (TRANS (@lem1954964 x) (@lem1954968)). Qed.
Lemma lem1954970 : term26 = term21.
Proof. exact (fun_ext (fun x : real => @lem1954969 x)). Qed.
Lemma lem1954971 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1954972 : term27 = term23.
Proof. exact (MK_COMB (@lem1954971) (@lem1954970)). Qed.
Lemma lem1954974 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1954975 (t : Prop) : (term25 t) = t.
Proof. exact (@lem1954974 real t). Qed.
Lemma lem1954976 : term23 = True.
Proof. exact (@lem1954975 True). Qed.
Lemma lem1954977 : term27 = True.
Proof. exact (TRANS (@lem1954972) (@lem1954976)). Qed.
Lemma lem1954978 : True = term27.
Proof. exact (SYM (@lem1954977)). Qed.
Lemma lem1954979 : term27.
Proof. exact (EQ_MP (@lem1954978) (@lem0)). Qed.
