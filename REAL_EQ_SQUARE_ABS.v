Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_EQ_SQUARE_ABS_term_abbrevs.
Require Import REAL_LE_SQUARE_ABS_spec.
Require Import thm0_spec.
Require Import thm1339379_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1645945 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (term0 y x) = (x = y).
Proof. exact (h1). Qed.
Lemma lem1645946 (x : real) (y : real) (h1 : (term0 y x) = (x = y)) : (x = y) = (term0 y x).
Proof. exact (SYM (@lem1645945 x y h1)). Qed.
Lemma lem1645947 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (x = y) = (term0 y x).
Proof. exact (h1). Qed.
Lemma lem1645948 (y : real) (x : real) (h1 : (x = y) = (term0 y x)) : (term0 y x) = (x = y).
Proof. exact (SYM (@lem1645947 y x h1)). Qed.
Lemma lem1645949 (y : real) (x : real) : ((term0 y x) = (x = y)) = ((x = y) = (term0 y x)).
Proof. exact (prop_ext (fun h1 : (term0 y x) = (x = y) => @lem1645946 x y h1) (fun h1 : (x = y) = (term0 y x) => @lem1645948 y x h1)). Qed.
Lemma lem1645950 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem1645949 y x)). Qed.
Lemma lem1645951 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1645952 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem1645951) (@lem1645950 x)). Qed.
Lemma lem1645953 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem1645952 x)). Qed.
Lemma lem1645954 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1645955 : term7 = term8.
Proof. exact (MK_COMB (@lem1645954) (@lem1645953)). Qed.
Lemma lem1645956 : term8.
Proof. exact (EQ_MP (@lem1645955) (@lem1339379)). Qed.
Lemma lem1645957 (x : real) : term9 x.
Proof. exact (@lem1645868 x). Qed.
Lemma lem1645958 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1645959 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem1645958 x) (@lem1645957 x)). Qed.
Lemma lem1645960 (x : real) (y : real) : term11 x y.
Proof. exact (@lem1645959 x y). Qed.
Lemma lem1645961 (x : real) (y : real) : (term11 x y) = ((term12 x y) = (term13 x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem1645963 (x : real) : term14 x.
Proof. exact (@lem1645956 x). Qed.
Lemma lem1645964 (x : real) : (term14 x) = (term4 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1645965 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem1645964 x) (@lem1645963 x)). Qed.
Lemma lem1645966 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1645965 x y). Qed.
Lemma lem1645967 (y : real) (x : real) : (term15 x y) = ((x = y) = (term0 y x)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1645984 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem1645967 y x) (@lem1645966 x y)). Qed.
Lemma lem1645985 (y : real) (x : real) : ((real_abs x) = (real_abs y)) = (term16 y x).
Proof. exact (@lem1645984 (real_abs y) (real_abs x)). Qed.
Lemma lem1645989 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1645961 x y) (@lem1645960 x y)). Qed.
Lemma lem1645990 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1645991 (x : real) (y : real) : (term17 x y) = (term18 x y).
Proof. exact (MK_COMB (@lem1645990) (@lem1645989 x y)). Qed.
Lemma lem1645993 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (EQ_MP (@lem1645961 x y) (@lem1645960 x y)). Qed.
Lemma lem1645994 (y : real) (x : real) : (term12 y x) = (term13 y x).
Proof. exact (@lem1645993 y x). Qed.
Lemma lem1645995 (y : real) (x : real) : (term16 y x) = (term19 y x).
Proof. exact (MK_COMB (@lem1645991 x y) (@lem1645994 y x)). Qed.
Lemma lem1645998 (y : real) (x : real) : ((real_abs x) = (real_abs y)) = (term19 y x).
Proof. exact (TRANS (@lem1645985 y x) (@lem1645995 y x)). Qed.
Lemma lem1645999 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1646000 (y : real) (x : real) : (term20 x y) = (term21 y x).
Proof. exact (MK_COMB (@lem1645999) (@lem1645998 y x)). Qed.
Lemma lem1646004 (y : real) (x : real) : (x = y) = (term0 y x).
Proof. exact (EQ_MP (@lem1645967 y x) (@lem1645966 x y)). Qed.
Lemma lem1646005 (y : real) (x : real) : ((term22 x) = (term22 y)) = (term19 y x).
Proof. exact (@lem1646004 (term22 y) (term22 x)). Qed.
Lemma lem1646008 (y : real) (x : real) : (((real_abs x) = (real_abs y)) = ((term22 x) = (term22 y))) = ((term19 y x) = (term19 y x)).
Proof. exact (MK_COMB (@lem1646000 y x) (@lem1646005 y x)). Qed.
Lemma lem1646010 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1646011 (x : Prop) : (x = x) = True.
Proof. exact (@lem1646010 Prop x). Qed.
Lemma lem1646012 (y : real) (x : real) : ((term19 y x) = (term19 y x)) = True.
Proof. exact (@lem1646011 (term19 y x)). Qed.
Lemma lem1646013 (x : real) (y : real) : (((real_abs x) = (real_abs y)) = ((term22 x) = (term22 y))) = True.
Proof. exact (TRANS (@lem1646008 y x) (@lem1646012 y x)). Qed.
Lemma lem1646014 (x : real) : (term23 x) = term24.
Proof. exact (fun_ext (fun y : real => @lem1646013 x y)). Qed.
Lemma lem1646015 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1646016 (x : real) : (term25 x) = term26.
Proof. exact (MK_COMB (@lem1646015) (@lem1646014 x)). Qed.
Lemma lem1646018 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1646019 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1646018 real t). Qed.
Lemma lem1646020 : term26 = True.
Proof. exact (@lem1646019 True). Qed.
Lemma lem1646021 (x : real) : (term25 x) = True.
Proof. exact (TRANS (@lem1646016 x) (@lem1646020)). Qed.
Lemma lem1646022 : term29 = term24.
Proof. exact (fun_ext (fun x : real => @lem1646021 x)). Qed.
Lemma lem1646023 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1646024 : term30 = term26.
Proof. exact (MK_COMB (@lem1646023) (@lem1646022)). Qed.
Lemma lem1646026 {A : Type'} (t : Prop) : (term27 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1646027 (t : Prop) : (term28 t) = t.
Proof. exact (@lem1646026 real t). Qed.
Lemma lem1646028 : term26 = True.
Proof. exact (@lem1646027 True). Qed.
Lemma lem1646029 : term30 = True.
Proof. exact (TRANS (@lem1646024) (@lem1646028)). Qed.
Lemma lem1646030 : True = term30.
Proof. exact (SYM (@lem1646029)). Qed.
Lemma lem1646031 : term30.
Proof. exact (EQ_MP (@lem1646030) (@lem0)). Qed.
