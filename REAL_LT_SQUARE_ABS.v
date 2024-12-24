Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_LT_SQUARE_ABS_term_abbrevs.
Require Import REAL_LE_SQUARE_ABS_spec.
Require Import REAL_NOT_LE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1645871 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (term0 x y) = (real_lt y x).
Proof. exact (h1). Qed.
Lemma lem1645872 (y : real) (x : real) (h1 : (term0 x y) = (real_lt y x)) : (real_lt y x) = (term0 x y).
Proof. exact (SYM (@lem1645871 y x h1)). Qed.
Lemma lem1645873 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (real_lt y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1645874 (x : real) (y : real) (h1 : (real_lt y x) = (term0 x y)) : (term0 x y) = (real_lt y x).
Proof. exact (SYM (@lem1645873 x y h1)). Qed.
Lemma lem1645875 (x : real) (y : real) : ((term0 x y) = (real_lt y x)) = ((real_lt y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_lt y x) => @lem1645872 y x h1) (fun h1 : (real_lt y x) = (term0 x y) => @lem1645874 x y h1)). Qed.
Lemma lem1645876 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1645875 x y)). Qed.
Lemma lem1645877 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1645878 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1645877) (@lem1645876 x)). Qed.
Lemma lem1645879 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1645878 x)). Qed.
Lemma lem1645880 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1645881 : term7 = term8.
Proof. exact (MK_COMB (@lem1645880) (@lem1645879)). Qed.
Lemma lem1645882 : term8.
Proof. exact (EQ_MP (@lem1645881) (@lem1495933)). Qed.
Lemma lem1645883 (x : real) : term9 x.
Proof. exact (@lem1645868 x). Qed.
Lemma lem1645884 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1645885 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1645884 x) (@lem1645883 x)). Qed.
Lemma lem1645886 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1645885 x y). Qed.
Lemma lem1645887 (x : real) (y : real) : (term11 x y) = ((term12 x y) = (term13 x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1645889 (x : real) : term14 x.
Proof. exact (@lem1645882 x). Qed.
Lemma lem1645890 (x : real) : (term14 x) = (term4 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1645891 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1645890 x) (@lem1645889 x)). Qed.
Lemma lem1645892 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1645891 x y). Qed.
Lemma lem1645893 (x : real) (y : real) : (term15 x y) = ((real_lt y x) = (term0 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1645906 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1645893 x y) (@lem1645892 x y)). Qed.
Lemma lem1645907 (y : real) (x : real) : (term16 x y) = (term17 y x).
Proof. exact (@lem1645906 (real_abs y) (real_abs x)). Qed.
Lemma lem1645909 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1645887 x y) (@lem1645886 x y)). Qed.
Lemma lem1645910 (y : real) (x : real) : (term12 y x) = (term13 y x).
Proof. exact (@lem1645909 y x). Qed.
Lemma lem1645911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1645912 (y : real) (x : real) : (term17 y x) = (term18 y x).
Proof. exact (MK_COMB (@lem1645911) (@lem1645910 y x)). Qed.
Lemma lem1645913 (y : real) (x : real) : (term16 x y) = (term18 y x).
Proof. exact (TRANS (@lem1645907 y x) (@lem1645912 y x)). Qed.
Lemma lem1645914 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1645915 (y : real) (x : real) : (term19 x y) = (term20 y x).
Proof. exact (MK_COMB (@lem1645914) (@lem1645913 y x)). Qed.
Lemma lem1645917 (x : real) (y : real) : (real_lt y x) = (term0 x y).
Proof. exact (EQ_MP (@lem1645893 x y) (@lem1645892 x y)). Qed.
Lemma lem1645918 (y : real) (x : real) : (term21 x y) = (term18 y x).
Proof. exact (@lem1645917 (term22 y) (term22 x)). Qed.
Lemma lem1645919 (y : real) (x : real) : ((term16 x y) = (term21 x y)) = ((term18 y x) = (term18 y x)).
Proof. exact (MK_COMB (@lem1645915 y x) (@lem1645918 y x)). Qed.
Lemma lem1645921 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1645922 (x : Prop) : (x = x) = True.
Proof. exact (@lem1645921 Prop x). Qed.
Lemma lem1645923 (y : real) (x : real) : ((term18 y x) = (term18 y x)) = True.
Proof. exact (@lem1645922 (term18 y x)). Qed.
Lemma lem1645924 (x : real) (y : real) : ((term16 x y) = (term21 x y)) = True.
Proof. exact (TRANS (@lem1645919 y x) (@lem1645923 y x)). Qed.
Lemma lem1645925 (x : real) : (term23 x) = term24.
Proof. exact (fun_ext (fun y : real => @lem1645924 x y)). Qed.
Lemma lem1645926 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1645927 (x : real) : (term25 x) = term26.
Proof. exact (MK_COMB (@lem1645926) (@lem1645925 x)). Qed.
Lemma lem1645929 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1645930 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1645929 real t). Qed.
Lemma lem1645931 : term26 = True.
Proof. exact (@lem1645930 True). Qed.
Lemma lem1645932 (x : real) : (term25 x) = True.
Proof. exact (TRANS (@lem1645927 x) (@lem1645931)). Qed.
Lemma lem1645933 : term29 = term24.
Proof. exact (fun_ext (fun x : real => @lem1645932 x)). Qed.
Lemma lem1645934 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1645935 : term30 = term26.
Proof. exact (MK_COMB (@lem1645934) (@lem1645933)). Qed.
Lemma lem1645937 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1645938 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1645937 real t). Qed.
Lemma lem1645939 : term26 = True.
Proof. exact (@lem1645938 True). Qed.
Lemma lem1645940 : term30 = True.
Proof. exact (TRANS (@lem1645935) (@lem1645939)). Qed.
Lemma lem1645941 : True = term30.
Proof. exact (SYM (@lem1645940)). Qed.
Lemma lem1645942 : term30.
Proof. exact (EQ_MP (@lem1645941) (@lem0)). Qed.
