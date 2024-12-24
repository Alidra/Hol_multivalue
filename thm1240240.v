Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm1240240_term_abbrevs.
Require Import thm0_spec.
Require Import thm32_spec.
Require Import thm37_spec.
Require Import thm51_spec.
Require Import thm9103_spec.
Require Import thm9104_spec.
Require Import thm9120_spec.
Lemma lem1239856 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (h1). Qed.
Lemma lem1239857 (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term0 char' _22730'.
Proof. exact (h1). Qed.
Lemma lem1239858 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term1 char' _22730' a0.
Proof. exact (@lem1239857 char' _22730' h1 a0). Qed.
Lemma lem1239859 (char' : type1335) (_22730' : type1539) (a0 : Prop) : (term1 char' _22730' a0) = (term2 char' _22730' a0).
Proof. exact (eq_refl (term1 char' _22730' a0)). Qed.
Lemma lem1239860 (a0 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term2 char' _22730' a0.
Proof. exact (EQ_MP (@lem1239859 char' _22730' a0) (@lem1239858 a0 char' _22730' h1)). Qed.
Lemma lem1239861 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term3 char' _22730' a0 a1.
Proof. exact (@lem1239860 a0 char' _22730' h1 a1). Qed.
Lemma lem1239862 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) : (term3 char' _22730' a0 a1) = (term4 char' _22730' a0 a1).
Proof. exact (eq_refl (term3 char' _22730' a0 a1)). Qed.
Lemma lem1239863 (a0 : Prop) (a1 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term4 char' _22730' a0 a1.
Proof. exact (EQ_MP (@lem1239862 char' _22730' a0 a1) (@lem1239861 a0 a1 char' _22730' h1)). Qed.
Lemma lem1239864 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term5 char' _22730' a0 a1 a2.
Proof. exact (@lem1239863 a0 a1 char' _22730' h1 a2). Qed.
Lemma lem1239865 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) : (term5 char' _22730' a0 a1 a2) = (term6 char' _22730' a0 a1 a2).
Proof. exact (eq_refl (term5 char' _22730' a0 a1 a2)). Qed.
Lemma lem1239866 (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term6 char' _22730' a0 a1 a2.
Proof. exact (EQ_MP (@lem1239865 char' _22730' a0 a1 a2) (@lem1239864 a0 a1 a2 char' _22730' h1)). Qed.
Lemma lem1239867 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term7 char' _22730' a0 a1 a2 a3.
Proof. exact (@lem1239866 a0 a1 a2 char' _22730' h1 a3). Qed.
Lemma lem1239868 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) : (term7 char' _22730' a0 a1 a2 a3) = (term8 char' _22730' a0 a1 a2 a3).
Proof. exact (eq_refl (term7 char' _22730' a0 a1 a2 a3)). Qed.
Lemma lem1239869 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term8 char' _22730' a0 a1 a2 a3.
Proof. exact (EQ_MP (@lem1239868 char' _22730' a0 a1 a2 a3) (@lem1239867 a0 a1 a2 a3 char' _22730' h1)). Qed.
Lemma lem1239870 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term9 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (@lem1239869 a0 a1 a2 a3 char' _22730' h1 a4). Qed.
Lemma lem1239871 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) : (term9 char' _22730' a0 a1 a2 a3 a4) = (term10 char' _22730' a0 a1 a2 a3 a4).
Proof. exact (eq_refl (term9 char' _22730' a0 a1 a2 a3 a4)). Qed.
Lemma lem1239872 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term10 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (EQ_MP (@lem1239871 char' _22730' a0 a1 a2 a3 a4) (@lem1239870 a0 a1 a2 a3 a4 char' _22730' h1)). Qed.
Lemma lem1239873 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term11 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (@lem1239872 a0 a1 a2 a3 a4 char' _22730' h1 a5). Qed.
Lemma lem1239874 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) : (term11 char' _22730' a0 a1 a2 a3 a4 a5) = (term12 char' _22730' a0 a1 a2 a3 a4 a5).
Proof. exact (eq_refl (term11 char' _22730' a0 a1 a2 a3 a4 a5)). Qed.
Lemma lem1239875 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term12 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (EQ_MP (@lem1239874 char' _22730' a0 a1 a2 a3 a4 a5) (@lem1239873 a0 a1 a2 a3 a4 a5 char' _22730' h1)). Qed.
Lemma lem1239876 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term13 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (@lem1239875 a0 a1 a2 a3 a4 a5 char' _22730' h1 a6). Qed.
Lemma lem1239877 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) : (term13 char' _22730' a0 a1 a2 a3 a4 a5 a6) = (term14 char' _22730' a0 a1 a2 a3 a4 a5 a6).
Proof. exact (eq_refl (term13 char' _22730' a0 a1 a2 a3 a4 a5 a6)). Qed.
Lemma lem1239878 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term14 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (EQ_MP (@lem1239877 char' _22730' a0 a1 a2 a3 a4 a5 a6) (@lem1239876 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1)). Qed.
Lemma lem1239879 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term15 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1239878 a0 a1 a2 a3 a4 a5 a6 char' _22730' h1 a7). Qed.
Lemma lem1239880 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term15 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term16 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term15 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1239881 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term16 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239880 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239879 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1)). Qed.
Lemma lem1239882 (char' : type1335) : char' = char'.
Proof. exact (eq_refl char'). Qed.
Lemma lem1239883 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : (char' a) = (term16 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (MK_COMB (@lem1239882 char') (@lem1239856 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239884 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : (term16 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (char' a).
Proof. exact (SYM (@lem1239883 char' a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239885 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : term0 char' _22730') (h2 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : char' a.
Proof. exact (EQ_MP (@lem1239884 char' a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h2) (@lem1239881 a0 a1 a2 a3 a4 a5 a6 a7 char' _22730' h1)). Qed.
Lemma lem1239886 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term17 _22730' a0 a1 a2 a3 a4 a5 a6 a7 char' a.
Proof. exact (fun h0 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7) => @lem1239885 char' a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1 h0). Qed.
Lemma lem1239887 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (h1). Qed.
Lemma lem1239888 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : term0 char' _22730') (h2 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : char' a.
Proof. exact (@lem1239886 a0 a1 a2 a3 a4 a5 a6 a7 a char' _22730' h1 (@lem1239887 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h2)). Qed.
Lemma lem1239889 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term17 _22730' a0 a1 a2 a3 a4 a5 a6 a7 char' a.
Proof. exact (fun h0 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7) => @lem1239888 char' a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1 h0). Qed.
Lemma lem1239890 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term18 _22730' a0 a1 a2 a3 a4 a5 a6 char' a.
Proof. exact (fun a7 : Prop => @lem1239889 a0 a1 a2 a3 a4 a5 a6 a7 a char' _22730' h1). Qed.
Lemma lem1239891 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term19 _22730' a0 a1 a2 a3 a4 a5 char' a.
Proof. exact (fun a6 : Prop => @lem1239890 a0 a1 a2 a3 a4 a5 a6 a char' _22730' h1). Qed.
Lemma lem1239892 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term20 _22730' a0 a1 a2 a3 a4 char' a.
Proof. exact (fun a5 : Prop => @lem1239891 a0 a1 a2 a3 a4 a5 a char' _22730' h1). Qed.
Lemma lem1239893 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term21 _22730' a0 a1 a2 a3 char' a.
Proof. exact (fun a4 : Prop => @lem1239892 a0 a1 a2 a3 a4 a char' _22730' h1). Qed.
Lemma lem1239894 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term22 _22730' a0 a1 a2 char' a.
Proof. exact (fun a3 : Prop => @lem1239893 a0 a1 a2 a3 a char' _22730' h1). Qed.
Lemma lem1239895 (a0 : Prop) (a1 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term23 _22730' a0 a1 char' a.
Proof. exact (fun a2 : Prop => @lem1239894 a0 a1 a2 a char' _22730' h1). Qed.
Lemma lem1239896 (a0 : Prop) (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term24 _22730' a0 char' a.
Proof. exact (fun a1 : Prop => @lem1239895 a0 a1 a char' _22730' h1). Qed.
Lemma lem1239897 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term25 _22730' char' a.
Proof. exact (fun a0 : Prop => @lem1239896 a0 a char' _22730' h1). Qed.
Lemma lem1239898 (char' : type1335) (_22730' : type1539) (h1 : term0 char' _22730') : term26 _22730' char'.
Proof. exact (fun a : type1678 => @lem1239897 a char' _22730' h1). Qed.
Lemma lem1239899 (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term26 _22730' char'.
Proof. exact (h1). Qed.
Lemma lem1239900 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term27 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1239899 _22730' char' h1 (_22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1239901 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term27 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term28 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term27 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1239902 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term28 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239901 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239900 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1)). Qed.
Lemma lem1239903 (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a0 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term29 char' _22730' a1 a2 a3 a4 a5 a6 a7 a0.
Proof. exact (@lem1239902 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a0). Qed.
Lemma lem1239904 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term29 char' _22730' a1 a2 a3 a4 a5 a6 a7 a0) = (term30 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term29 char' _22730' a1 a2 a3 a4 a5 a6 a7 a0)). Qed.
Lemma lem1239905 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term30 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239904 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239903 a1 a2 a3 a4 a5 a6 a7 a0 _22730' char' h1)). Qed.
Lemma lem1239906 (a0 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a1 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term31 char' _22730' a0 a2 a3 a4 a5 a6 a7 a1.
Proof. exact (@lem1239905 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a1). Qed.
Lemma lem1239907 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term31 char' _22730' a0 a2 a3 a4 a5 a6 a7 a1) = (term32 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term31 char' _22730' a0 a2 a3 a4 a5 a6 a7 a1)). Qed.
Lemma lem1239908 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term32 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239907 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239906 a0 a2 a3 a4 a5 a6 a7 a1 _22730' char' h1)). Qed.
Lemma lem1239909 (a0 : Prop) (a1 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a2 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term33 char' _22730' a0 a1 a3 a4 a5 a6 a7 a2.
Proof. exact (@lem1239908 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a2). Qed.
Lemma lem1239910 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term33 char' _22730' a0 a1 a3 a4 a5 a6 a7 a2) = (term34 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term33 char' _22730' a0 a1 a3 a4 a5 a6 a7 a2)). Qed.
Lemma lem1239911 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term34 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239910 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239909 a0 a1 a3 a4 a5 a6 a7 a2 _22730' char' h1)). Qed.
Lemma lem1239912 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a3 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term35 char' _22730' a0 a1 a2 a4 a5 a6 a7 a3.
Proof. exact (@lem1239911 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a3). Qed.
Lemma lem1239913 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term35 char' _22730' a0 a1 a2 a4 a5 a6 a7 a3) = (term36 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term35 char' _22730' a0 a1 a2 a4 a5 a6 a7 a3)). Qed.
Lemma lem1239914 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term36 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239913 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239912 a0 a1 a2 a4 a5 a6 a7 a3 _22730' char' h1)). Qed.
Lemma lem1239915 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (a4 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term37 char' _22730' a0 a1 a2 a3 a5 a6 a7 a4.
Proof. exact (@lem1239914 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a4). Qed.
Lemma lem1239916 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term37 char' _22730' a0 a1 a2 a3 a5 a6 a7 a4) = (term38 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term37 char' _22730' a0 a1 a2 a3 a5 a6 a7 a4)). Qed.
Lemma lem1239917 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term38 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239916 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239915 a0 a1 a2 a3 a5 a6 a7 a4 _22730' char' h1)). Qed.
Lemma lem1239918 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a6 : Prop) (a7 : Prop) (a5 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term39 char' _22730' a0 a1 a2 a3 a4 a6 a7 a5.
Proof. exact (@lem1239917 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a5). Qed.
Lemma lem1239919 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term39 char' _22730' a0 a1 a2 a3 a4 a6 a7 a5) = (term40 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term39 char' _22730' a0 a1 a2 a3 a4 a6 a7 a5)). Qed.
Lemma lem1239920 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term40 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239919 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239918 a0 a1 a2 a3 a4 a6 a7 a5 _22730' char' h1)). Qed.
Lemma lem1239921 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a7 : Prop) (a6 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term41 char' _22730' a0 a1 a2 a3 a4 a5 a7 a6.
Proof. exact (@lem1239920 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a6). Qed.
Lemma lem1239922 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term41 char' _22730' a0 a1 a2 a3 a4 a5 a7 a6) = (term42 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term41 char' _22730' a0 a1 a2 a3 a4 a5 a7 a6)). Qed.
Lemma lem1239923 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term42 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239922 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239921 a0 a1 a2 a3 a4 a5 a7 a6 _22730' char' h1)). Qed.
Lemma lem1239924 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term43 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1239923 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 a7). Qed.
Lemma lem1239925 (char' : type1335) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (term43 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) = (term44 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (term43 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1239926 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term44 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (EQ_MP (@lem1239925 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7) (@lem1239924 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1)). Qed.
Lemma lem1239927 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) : (_22730' a0 a1 a2 a3 a4 a5 a6 a7) = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (eq_refl (_22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1239928 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term16 char' _22730' a0 a1 a2 a3 a4 a5 a6 a7.
Proof. exact (@lem1239926 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1 (@lem1239927 _22730' a0 a1 a2 a3 a4 a5 a6 a7)). Qed.
Lemma lem1239929 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term14 char' _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (fun a7 : Prop => @lem1239928 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' h1). Qed.
Lemma lem1239930 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term12 char' _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (fun a6 : Prop => @lem1239929 a0 a1 a2 a3 a4 a5 a6 _22730' char' h1). Qed.
Lemma lem1239931 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term10 char' _22730' a0 a1 a2 a3 a4.
Proof. exact (fun a5 : Prop => @lem1239930 a0 a1 a2 a3 a4 a5 _22730' char' h1). Qed.
Lemma lem1239932 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term8 char' _22730' a0 a1 a2 a3.
Proof. exact (fun a4 : Prop => @lem1239931 a0 a1 a2 a3 a4 _22730' char' h1). Qed.
Lemma lem1239933 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term6 char' _22730' a0 a1 a2.
Proof. exact (fun a3 : Prop => @lem1239932 a0 a1 a2 a3 _22730' char' h1). Qed.
Lemma lem1239934 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term4 char' _22730' a0 a1.
Proof. exact (fun a2 : Prop => @lem1239933 a0 a1 a2 _22730' char' h1). Qed.
Lemma lem1239935 (a0 : Prop) (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term2 char' _22730' a0.
Proof. exact (fun a1 : Prop => @lem1239934 a0 a1 _22730' char' h1). Qed.
Lemma lem1239936 (_22730' : type1539) (char' : type1335) (h1 : term26 _22730' char') : term0 char' _22730'.
Proof. exact (fun a0 : Prop => @lem1239935 a0 _22730' char' h1). Qed.
Lemma lem1239937 (char' : type1335) (_22730' : type1539) : term45 char' _22730'.
Proof. exact (fun h0 : term26 _22730' char' => @lem1239936 _22730' char' h0). Qed.
Lemma lem1239938 (_22730' : type1539) (char' : type1335) : term46 _22730' char'.
Proof. exact (fun h0 : term0 char' _22730' => @lem1239898 char' _22730' h0). Qed.
Lemma lem1239939 (char' : type1335) (_22730' : type1539) : term47 char' _22730'.
Proof. exact (conj (@lem1239938 _22730' char') (@lem1239937 char' _22730')). Qed.
Lemma lem1239940 (_22730' : type1539) (char' : type1335) : (term47 char' _22730') = ((term0 char' _22730') = (term26 _22730' char')).
Proof. exact (@lem32 (term0 char' _22730') (term26 _22730' char')). Qed.
Lemma lem1239941 (_22730' : type1539) (char' : type1335) : (term0 char' _22730') = (term26 _22730' char').
Proof. exact (EQ_MP (@lem1239940 _22730' char') (@lem1239939 char' _22730')). Qed.
Lemma lem1239942 (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term25 _22730' char' a.
Proof. exact (h1). Qed.
Lemma lem1239943 (a0 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term48 _22730' char' a a0.
Proof. exact (@lem1239942 _22730' char' a h1 a0). Qed.
Lemma lem1239944 (_22730' : type1539) (a0 : Prop) (char' : type1335) (a : type1678) : (term48 _22730' char' a a0) = (term24 _22730' a0 char' a).
Proof. exact (eq_refl (term48 _22730' char' a a0)). Qed.
Lemma lem1239945 (a0 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term24 _22730' a0 char' a.
Proof. exact (EQ_MP (@lem1239944 _22730' a0 char' a) (@lem1239943 a0 _22730' char' a h1)). Qed.
Lemma lem1239946 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term49 _22730' a0 char' a a1.
Proof. exact (@lem1239945 a0 _22730' char' a h1 a1). Qed.
Lemma lem1239947 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (char' : type1335) (a : type1678) : (term49 _22730' a0 char' a a1) = (term23 _22730' a0 a1 char' a).
Proof. exact (eq_refl (term49 _22730' a0 char' a a1)). Qed.
Lemma lem1239948 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term23 _22730' a0 a1 char' a.
Proof. exact (EQ_MP (@lem1239947 _22730' a0 a1 char' a) (@lem1239946 a0 a1 _22730' char' a h1)). Qed.
Lemma lem1239949 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term50 _22730' a0 a1 char' a a2.
Proof. exact (@lem1239948 a0 a1 _22730' char' a h1 a2). Qed.
Lemma lem1239950 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (char' : type1335) (a : type1678) : (term50 _22730' a0 a1 char' a a2) = (term22 _22730' a0 a1 a2 char' a).
Proof. exact (eq_refl (term50 _22730' a0 a1 char' a a2)). Qed.
Lemma lem1239951 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term22 _22730' a0 a1 a2 char' a.
Proof. exact (EQ_MP (@lem1239950 _22730' a0 a1 a2 char' a) (@lem1239949 a0 a1 a2 _22730' char' a h1)). Qed.
Lemma lem1239952 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term51 _22730' a0 a1 a2 char' a a3.
Proof. exact (@lem1239951 a0 a1 a2 _22730' char' a h1 a3). Qed.
Lemma lem1239953 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (char' : type1335) (a : type1678) : (term51 _22730' a0 a1 a2 char' a a3) = (term21 _22730' a0 a1 a2 a3 char' a).
Proof. exact (eq_refl (term51 _22730' a0 a1 a2 char' a a3)). Qed.
Lemma lem1239954 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term21 _22730' a0 a1 a2 a3 char' a.
Proof. exact (EQ_MP (@lem1239953 _22730' a0 a1 a2 a3 char' a) (@lem1239952 a0 a1 a2 a3 _22730' char' a h1)). Qed.
Lemma lem1239955 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term52 _22730' a0 a1 a2 a3 char' a a4.
Proof. exact (@lem1239954 a0 a1 a2 a3 _22730' char' a h1 a4). Qed.
Lemma lem1239956 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (char' : type1335) (a : type1678) : (term52 _22730' a0 a1 a2 a3 char' a a4) = (term20 _22730' a0 a1 a2 a3 a4 char' a).
Proof. exact (eq_refl (term52 _22730' a0 a1 a2 a3 char' a a4)). Qed.
Lemma lem1239957 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term20 _22730' a0 a1 a2 a3 a4 char' a.
Proof. exact (EQ_MP (@lem1239956 _22730' a0 a1 a2 a3 a4 char' a) (@lem1239955 a0 a1 a2 a3 a4 _22730' char' a h1)). Qed.
Lemma lem1239958 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term53 _22730' a0 a1 a2 a3 a4 char' a a5.
Proof. exact (@lem1239957 a0 a1 a2 a3 a4 _22730' char' a h1 a5). Qed.
Lemma lem1239959 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (char' : type1335) (a : type1678) : (term53 _22730' a0 a1 a2 a3 a4 char' a a5) = (term19 _22730' a0 a1 a2 a3 a4 a5 char' a).
Proof. exact (eq_refl (term53 _22730' a0 a1 a2 a3 a4 char' a a5)). Qed.
Lemma lem1239960 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term19 _22730' a0 a1 a2 a3 a4 a5 char' a.
Proof. exact (EQ_MP (@lem1239959 _22730' a0 a1 a2 a3 a4 a5 char' a) (@lem1239958 a0 a1 a2 a3 a4 a5 _22730' char' a h1)). Qed.
Lemma lem1239961 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term54 _22730' a0 a1 a2 a3 a4 a5 char' a a6.
Proof. exact (@lem1239960 a0 a1 a2 a3 a4 a5 _22730' char' a h1 a6). Qed.
Lemma lem1239962 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (char' : type1335) (a : type1678) : (term54 _22730' a0 a1 a2 a3 a4 a5 char' a a6) = (term18 _22730' a0 a1 a2 a3 a4 a5 a6 char' a).
Proof. exact (eq_refl (term54 _22730' a0 a1 a2 a3 a4 a5 char' a a6)). Qed.
Lemma lem1239963 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term18 _22730' a0 a1 a2 a3 a4 a5 a6 char' a.
Proof. exact (EQ_MP (@lem1239962 _22730' a0 a1 a2 a3 a4 a5 a6 char' a) (@lem1239961 a0 a1 a2 a3 a4 a5 a6 _22730' char' a h1)). Qed.
Lemma lem1239964 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term55 _22730' a0 a1 a2 a3 a4 a5 a6 char' a a7.
Proof. exact (@lem1239963 a0 a1 a2 a3 a4 a5 a6 _22730' char' a h1 a7). Qed.
Lemma lem1239965 (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (char' : type1335) (a : type1678) : (term55 _22730' a0 a1 a2 a3 a4 a5 a6 char' a a7) = (term17 _22730' a0 a1 a2 a3 a4 a5 a6 a7 char' a).
Proof. exact (eq_refl (term55 _22730' a0 a1 a2 a3 a4 a5 a6 char' a a7)). Qed.
Lemma lem1239966 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term17 _22730' a0 a1 a2 a3 a4 a5 a6 a7 char' a.
Proof. exact (EQ_MP (@lem1239965 _22730' a0 a1 a2 a3 a4 a5 a6 a7 char' a) (@lem1239964 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' a h1)). Qed.
Lemma lem1239967 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (h1). Qed.
Lemma lem1239968 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : term25 _22730' char' a) (h2 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : char' a.
Proof. exact (@lem1239966 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' a h1 (@lem1239967 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h2)). Qed.
Lemma lem1239969 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term56 _22730' char' a.
Proof. exact (fun h0 : term25 _22730' char' a => @lem1239968 char' a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h0 h1). Qed.
Lemma lem1239970 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (h1 : term57 a _22730' a0 a1 a2 a3 a4 a5 a6) : term57 a _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (h1). Qed.
Lemma lem1239971 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (h1 : term57 a _22730' a0 a1 a2 a3 a4 a5 a6) : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239970 a _22730' a0 a1 a2 a3 a4 a5 a6 h1) (fun a7 : Prop => fun h0 : term58 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 => @lem1239969 char' a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h0)). Qed.
Lemma lem1239972 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (h1 : term59 a _22730' a0 a1 a2 a3 a4 a5) : term59 a _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (h1). Qed.
Lemma lem1239973 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (h1 : term59 a _22730' a0 a1 a2 a3 a4 a5) : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239972 a _22730' a0 a1 a2 a3 a4 a5 h1) (fun a6 : Prop => fun h0 : term60 a _22730' a0 a1 a2 a3 a4 a5 a6 => @lem1239971 char' a _22730' a0 a1 a2 a3 a4 a5 a6 h0)). Qed.
Lemma lem1239974 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h1 : term61 a _22730' a0 a1 a2 a3 a4) : term61 a _22730' a0 a1 a2 a3 a4.
Proof. exact (h1). Qed.
Lemma lem1239975 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (h1 : term61 a _22730' a0 a1 a2 a3 a4) : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239974 a _22730' a0 a1 a2 a3 a4 h1) (fun a5 : Prop => fun h0 : term62 a _22730' a0 a1 a2 a3 a4 a5 => @lem1239973 char' a _22730' a0 a1 a2 a3 a4 a5 h0)). Qed.
Lemma lem1239976 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h1 : term63 a _22730' a0 a1 a2 a3) : term63 a _22730' a0 a1 a2 a3.
Proof. exact (h1). Qed.
Lemma lem1239977 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (h1 : term63 a _22730' a0 a1 a2 a3) : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239976 a _22730' a0 a1 a2 a3 h1) (fun a4 : Prop => fun h0 : term64 a _22730' a0 a1 a2 a3 a4 => @lem1239975 char' a _22730' a0 a1 a2 a3 a4 h0)). Qed.
Lemma lem1239978 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (h1 : term65 a _22730' a0 a1 a2) : term65 a _22730' a0 a1 a2.
Proof. exact (h1). Qed.
Lemma lem1239979 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (h1 : term65 a _22730' a0 a1 a2) : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239978 a _22730' a0 a1 a2 h1) (fun a3 : Prop => fun h0 : term66 a _22730' a0 a1 a2 a3 => @lem1239977 char' a _22730' a0 a1 a2 a3 h0)). Qed.
Lemma lem1239980 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (h1 : term67 a _22730' a0 a1) : term67 a _22730' a0 a1.
Proof. exact (h1). Qed.
Lemma lem1239981 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (h1 : term67 a _22730' a0 a1) : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239980 a _22730' a0 a1 h1) (fun a2 : Prop => fun h0 : term68 a _22730' a0 a1 a2 => @lem1239979 char' a _22730' a0 a1 a2 h0)). Qed.
Lemma lem1239982 (a : type1678) (_22730' : type1539) (a0 : Prop) (h1 : term69 a _22730' a0) : term69 a _22730' a0.
Proof. exact (h1). Qed.
Lemma lem1239983 (char' : type1335) (a : type1678) (_22730' : type1539) (a0 : Prop) (h1 : term69 a _22730' a0) : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239982 a _22730' a0 h1) (fun a1 : Prop => fun h0 : term70 a _22730' a0 a1 => @lem1239981 char' a _22730' a0 a1 h0)). Qed.
Lemma lem1239984 (a : type1678) (_22730' : type1539) (h1 : term71 a _22730') : term71 a _22730'.
Proof. exact (h1). Qed.
Lemma lem1239985 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term71 a _22730') : term56 _22730' char' a.
Proof. exact (ex_elim (@lem1239984 a _22730' h1) (fun a0 : Prop => fun h0 : term72 a _22730' a0 => @lem1239983 char' a _22730' a0 h0)). Qed.
Lemma lem1239986 (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term25 _22730' char' a.
Proof. exact (h1). Qed.
Lemma lem1239987 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term25 _22730' char' a) (h2 : term71 a _22730') : char' a.
Proof. exact (@lem1239985 char' a _22730' h2 (@lem1239986 _22730' char' a h1)). Qed.
Lemma lem1239988 (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term25 _22730' char' a) : term73 _22730' char' a.
Proof. exact (fun h0 : term71 a _22730' => @lem1239987 char' a _22730' h1 h0). Qed.
Lemma lem1239989 (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term73 _22730' char' a.
Proof. exact (h1). Qed.
Lemma lem1239990 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7).
Proof. exact (h1). Qed.
Lemma lem1239991 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term57 a _22730' a0 a1 a2 a3 a4 a5 a6.
Proof. exact (ex_intro (term58 a _22730' a0 a1 a2 a3 a4 a5 a6) a7 (@lem1239990 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239992 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term59 a _22730' a0 a1 a2 a3 a4 a5.
Proof. exact (ex_intro (term60 a _22730' a0 a1 a2 a3 a4 a5) a6 (@lem1239991 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239993 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term61 a _22730' a0 a1 a2 a3 a4.
Proof. exact (ex_intro (term62 a _22730' a0 a1 a2 a3 a4) a5 (@lem1239992 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239994 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term63 a _22730' a0 a1 a2 a3.
Proof. exact (ex_intro (term64 a _22730' a0 a1 a2 a3) a4 (@lem1239993 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239995 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term65 a _22730' a0 a1 a2.
Proof. exact (ex_intro (term66 a _22730' a0 a1 a2) a3 (@lem1239994 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239996 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term67 a _22730' a0 a1.
Proof. exact (ex_intro (term68 a _22730' a0 a1) a2 (@lem1239995 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239997 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term69 a _22730' a0.
Proof. exact (ex_intro (term70 a _22730' a0) a1 (@lem1239996 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239998 (a : type1678) (_22730' : type1539) (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) : term71 a _22730'.
Proof. exact (ex_intro (term72 a _22730') a0 (@lem1239997 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1239999 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7)) (h2 : term73 _22730' char' a) : char' a.
Proof. exact (@lem1239989 _22730' char' a h2 (@lem1239998 a _22730' a0 a1 a2 a3 a4 a5 a6 a7 h1)). Qed.
Lemma lem1240000 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (a7 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term17 _22730' a0 a1 a2 a3 a4 a5 a6 a7 char' a.
Proof. exact (fun h0 : a = (_22730' a0 a1 a2 a3 a4 a5 a6 a7) => @lem1239999 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' a h0 h1). Qed.
Lemma lem1240001 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (a6 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term18 _22730' a0 a1 a2 a3 a4 a5 a6 char' a.
Proof. exact (fun a7 : Prop => @lem1240000 a0 a1 a2 a3 a4 a5 a6 a7 _22730' char' a h1). Qed.
Lemma lem1240002 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (a5 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term19 _22730' a0 a1 a2 a3 a4 a5 char' a.
Proof. exact (fun a6 : Prop => @lem1240001 a0 a1 a2 a3 a4 a5 a6 _22730' char' a h1). Qed.
Lemma lem1240003 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (a4 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term20 _22730' a0 a1 a2 a3 a4 char' a.
Proof. exact (fun a5 : Prop => @lem1240002 a0 a1 a2 a3 a4 a5 _22730' char' a h1). Qed.
Lemma lem1240004 (a0 : Prop) (a1 : Prop) (a2 : Prop) (a3 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term21 _22730' a0 a1 a2 a3 char' a.
Proof. exact (fun a4 : Prop => @lem1240003 a0 a1 a2 a3 a4 _22730' char' a h1). Qed.
Lemma lem1240005 (a0 : Prop) (a1 : Prop) (a2 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term22 _22730' a0 a1 a2 char' a.
Proof. exact (fun a3 : Prop => @lem1240004 a0 a1 a2 a3 _22730' char' a h1). Qed.
Lemma lem1240006 (a0 : Prop) (a1 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term23 _22730' a0 a1 char' a.
Proof. exact (fun a2 : Prop => @lem1240005 a0 a1 a2 _22730' char' a h1). Qed.
Lemma lem1240007 (a0 : Prop) (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term24 _22730' a0 char' a.
Proof. exact (fun a1 : Prop => @lem1240006 a0 a1 _22730' char' a h1). Qed.
Lemma lem1240008 (_22730' : type1539) (char' : type1335) (a : type1678) (h1 : term73 _22730' char' a) : term25 _22730' char' a.
Proof. exact (fun a0 : Prop => @lem1240007 a0 _22730' char' a h1). Qed.
Lemma lem1240009 (_22730' : type1539) (char' : type1335) (a : type1678) : term74 _22730' char' a.
Proof. exact (fun h0 : term73 _22730' char' a => @lem1240008 _22730' char' a h0). Qed.
Lemma lem1240010 (_22730' : type1539) (char' : type1335) (a : type1678) : term75 _22730' char' a.
Proof. exact (fun h0 : term25 _22730' char' a => @lem1239988 _22730' char' a h0). Qed.
Lemma lem1240011 (_22730' : type1539) (char' : type1335) (a : type1678) : term76 _22730' char' a.
Proof. exact (conj (@lem1240010 _22730' char' a) (@lem1240009 _22730' char' a)). Qed.
Lemma lem1240012 (_22730' : type1539) (char' : type1335) (a : type1678) : (term76 _22730' char' a) = ((term25 _22730' char' a) = (term73 _22730' char' a)).
Proof. exact (@lem32 (term25 _22730' char' a) (term73 _22730' char' a)). Qed.
Lemma lem1240013 (_22730' : type1539) (char' : type1335) (a : type1678) : (term25 _22730' char' a) = (term73 _22730' char' a).
Proof. exact (EQ_MP (@lem1240012 _22730' char' a) (@lem1240011 _22730' char' a)). Qed.
Lemma lem1240014 (_22730' : type1539) (char' : type1335) : (term77 _22730' char') = (term78 _22730' char').
Proof. exact (fun_ext (fun a : type1678 => @lem1240013 _22730' char' a)). Qed.
Lemma lem1240015 : (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) = (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))).
Proof. exact (eq_refl (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))))). Qed.
Lemma lem1240016 (_22730' : type1539) (char' : type1335) : (term26 _22730' char') = (term79 _22730' char').
Proof. exact (MK_COMB (@lem1240015) (@lem1240014 _22730' char')). Qed.
Lemma lem1240017 (_22730' : type1539) (char' : type1335) : (term0 char' _22730') = (term79 _22730' char').
Proof. exact (TRANS (@lem1239941 _22730' char') (@lem1240016 _22730' char')). Qed.
Lemma lem1240019 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem9104 A x) (@lem9103 A x)). Qed.
Lemma lem1240020 (x : Prop) : (x = x) = True.
Proof. exact (@lem1240019 Prop x). Qed.
Lemma lem1240021 (_22730' : type1539) (char' : type1335) : ((term79 _22730' char') = (term79 _22730' char')) = True.
Proof. exact (@lem1240020 (term79 _22730' char')). Qed.
Lemma lem1240022 (_22730' : type1539) (char' : type1335) : True = ((term79 _22730' char') = (term79 _22730' char')).
Proof. exact (SYM (@lem1240021 _22730' char')). Qed.
Lemma lem1240023 (_22730' : type1539) (char' : type1335) : (term79 _22730' char') = (term79 _22730' char').
Proof. exact (EQ_MP (@lem1240022 _22730' char') (@lem0)). Qed.
Lemma lem1240024 (_22730' : type1539) (char' : type1335) : (term0 char' _22730') = (term79 _22730' char').
Proof. exact (TRANS (@lem1240017 _22730' char') (@lem1240023 _22730' char')). Qed.
Lemma lem1240025 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (h1). Qed.
Lemma lem1240026 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term80 _22730' char' a.
Proof. exact (@lem1240025 _22730' char' h1 a). Qed.
Lemma lem1240027 (_22730' : type1539) (char' : type1335) (a : type1678) : (term80 _22730' char' a) = (term73 _22730' char' a).
Proof. exact (eq_refl (term80 _22730' char' a)). Qed.
Lemma lem1240028 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term73 _22730' char' a.
Proof. exact (EQ_MP (@lem1240027 _22730' char' a) (@lem1240026 a _22730' char' h1)). Qed.
Lemma lem1240029 (a : type1678) (_22730' : type1539) (h1 : term71 a _22730') : term71 a _22730'.
Proof. exact (h1). Qed.
Lemma lem1240030 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : term71 a _22730') : char' a.
Proof. exact (@lem1240028 a _22730' char' h1 (@lem1240029 a _22730' h2)). Qed.
Lemma lem1240031 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term71 a _22730') : term81 _22730' char' a.
Proof. exact (fun h0 : term79 _22730' char' => @lem1240030 char' a _22730' h0 h1). Qed.
Lemma lem1240032 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (h1). Qed.
Lemma lem1240033 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : term71 a _22730') : char' a.
Proof. exact (@lem1240031 char' a _22730' h2 (@lem1240032 _22730' char' h1)). Qed.
Lemma lem1240034 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term73 _22730' char' a.
Proof. exact (fun h0 : term71 a _22730' => @lem1240033 char' a _22730' h1 h0). Qed.
Lemma lem1240035 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (fun a : type1678 => @lem1240034 a _22730' char' h1). Qed.
Lemma lem1240036 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (h1). Qed.
Lemma lem1240037 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term80 _22730' char' a.
Proof. exact (@lem1240036 _22730' char' h1 a). Qed.
Lemma lem1240038 (_22730' : type1539) (char' : type1335) (a : type1678) : (term80 _22730' char' a) = (term73 _22730' char' a).
Proof. exact (eq_refl (term80 _22730' char' a)). Qed.
Lemma lem1240039 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term73 _22730' char' a.
Proof. exact (EQ_MP (@lem1240038 _22730' char' a) (@lem1240037 a _22730' char' h1)). Qed.
Lemma lem1240040 (a : type1678) (_22730' : type1539) (h1 : term71 a _22730') : term71 a _22730'.
Proof. exact (h1). Qed.
Lemma lem1240041 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : term71 a _22730') : char' a.
Proof. exact (@lem1240039 a _22730' char' h1 (@lem1240040 a _22730' h2)). Qed.
Lemma lem1240042 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term71 a _22730') : term81 _22730' char' a.
Proof. exact (fun h0 : term79 _22730' char' => @lem1240041 char' a _22730' h0 h1). Qed.
Lemma lem1240043 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (h1). Qed.
Lemma lem1240044 (char' : type1335) (a : type1678) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : term71 a _22730') : char' a.
Proof. exact (@lem1240042 char' a _22730' h2 (@lem1240043 _22730' char' h1)). Qed.
Lemma lem1240045 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term73 _22730' char' a.
Proof. exact (fun h0 : term71 a _22730' => @lem1240044 char' a _22730' h1 h0). Qed.
Lemma lem1240046 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (fun a : type1678 => @lem1240045 a _22730' char' h1). Qed.
Lemma lem1240047 (_22730' : type1539) (char' : type1335) : term82 _22730' char'.
Proof. exact (fun h0 : term79 _22730' char' => @lem1240046 _22730' char' h0). Qed.
Lemma lem1240048 (_22730' : type1539) (char' : type1335) : term82 _22730' char'.
Proof. exact (fun h0 : term79 _22730' char' => @lem1240035 _22730' char' h0). Qed.
Lemma lem1240049 (_22730' : type1539) (char' : type1335) : term83 _22730' char'.
Proof. exact (conj (@lem1240048 _22730' char') (@lem1240047 _22730' char')). Qed.
Lemma lem1240050 (_22730' : type1539) (char' : type1335) : (term83 _22730' char') = ((term79 _22730' char') = (term79 _22730' char')).
Proof. exact (@lem32 (term79 _22730' char') (term79 _22730' char')). Qed.
Lemma lem1240051 (_22730' : type1539) (char' : type1335) : (term79 _22730' char') = (term79 _22730' char').
Proof. exact (EQ_MP (@lem1240050 _22730' char') (@lem1240049 _22730' char')). Qed.
Lemma lem1240052 (_22730' : type1539) (char' : type1335) : (term0 char' _22730') = (term79 _22730' char').
Proof. exact (TRANS (@lem1240024 _22730' char') (@lem1240051 _22730' char')). Qed.
Lemma lem1240053 (char' : type1335) (_22730' : type1539) : (term79 _22730' char') = (term0 char' _22730').
Proof. exact (SYM (@lem1240052 _22730' char')). Qed.
Lemma lem1240054 (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : char' = (term84 _22730').
Proof. exact (h1). Qed.
Lemma lem1240055 (a : type1678) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem1240056 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : (char' a) = (term85 _22730' a).
Proof. exact (MK_COMB (@lem1240054 char' _22730' h1) (@lem1240055 a)). Qed.
Lemma lem1240057 (_22730' : type1539) (a : type1678) : (term85 _22730' a) = (term86 _22730' a).
Proof. exact (eq_refl (term85 _22730' a)). Qed.
Lemma lem1240058 (char' : type1335) (a : type1678) : (term87 char' a) = (term87 char' a).
Proof. exact (eq_refl (term87 char' a)). Qed.
Lemma lem1240059 (char' : type1335) (_22730' : type1539) (a : type1678) : ((char' a) = (term85 _22730' a)) = ((char' a) = (term86 _22730' a)).
Proof. exact (MK_COMB (@lem1240058 char' a) (@lem1240057 _22730' a)). Qed.
Lemma lem1240060 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : (char' a) = (term86 _22730' a).
Proof. exact (EQ_MP (@lem1240059 char' _22730' a) (@lem1240056 a char' _22730' h1)). Qed.
Lemma lem1240061 (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term88 char' _22730'.
Proof. exact (fun a : type1678 => @lem1240060 a char' _22730' h1). Qed.
Lemma lem1240062 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term89 char' _22730' a.
Proof. exact (@lem1240061 char' _22730' h1 a). Qed.
Lemma lem1240063 (char' : type1335) (_22730' : type1539) (a : type1678) : (term89 char' _22730' a) = ((char' a) = (term86 _22730' a)).
Proof. exact (eq_refl (term89 char' _22730' a)). Qed.
Lemma lem1240064 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : (char' a) = (term86 _22730' a).
Proof. exact (EQ_MP (@lem1240063 char' _22730' a) (@lem1240062 a char' _22730' h1)). Qed.
Lemma lem1240067 (char' : type1335) (_22730' : type1539) (a : type1678) : term90 char' _22730' a.
Proof. exact (@lem37 (char' a) (term86 _22730' a)). Qed.
Lemma lem1240068 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term91 char' _22730' a.
Proof. exact (@lem1240067 char' _22730' a (@lem1240064 a char' _22730' h1)). Qed.
Lemma lem1240069 (char' : type1335) (a : type1678) (h1 : char' a) : char' a.
Proof. exact (h1). Qed.
Lemma lem1240070 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' a) (h2 : char' = (term84 _22730')) : term86 _22730' a.
Proof. exact (@lem1240068 a char' _22730' h2 (@lem1240069 char' a h1)). Qed.
Lemma lem1240071 (char' : type1335) (a : type1678) (char'' : type1335) (_22730' : type1539) (h1 : char'' a) (h2 : char'' = (term84 _22730')) : term92 _22730' a char'.
Proof. exact (@lem1240070 a char'' _22730' h1 h2 char'). Qed.
Lemma lem1240072 (_22730' : type1539) (char' : type1335) (a : type1678) : (term92 _22730' a char') = (term81 _22730' char' a).
Proof. exact (eq_refl (term92 _22730' a char')). Qed.
Lemma lem1240073 (char' : type1335) (a : type1678) (char'' : type1335) (_22730' : type1539) (h1 : char'' a) (h2 : char'' = (term84 _22730')) : term81 _22730' char' a.
Proof. exact (EQ_MP (@lem1240072 _22730' char' a) (@lem1240071 char' a char'' _22730' h1 h2)). Qed.
Lemma lem1240074 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (h1). Qed.
Lemma lem1240075 (char' : type1335) (a : type1678) (char'' : type1335) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : char'' a) (h3 : char'' = (term84 _22730')) : char' a.
Proof. exact (@lem1240073 char' a char'' _22730' h2 h3 (@lem1240074 _22730' char' h1)). Qed.
Lemma lem1240076 (a : type1678) (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : char'' = (term84 _22730')) : term93 char'' char' a.
Proof. exact (fun h0 : char'' a => @lem1240075 char' a char'' _22730' h1 h0 h2). Qed.
Lemma lem1240077 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : char'' = (term84 _22730')) : term94 char'' char'.
Proof. exact (fun a : type1678 => @lem1240076 a char' char'' _22730' h1 h2). Qed.
Lemma lem1240078 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : char'' = (term84 _22730')) : term95 _22730' char'' char'.
Proof. exact (fun h0 : term79 _22730' char' => @lem1240077 char' char'' _22730' h0 h1). Qed.
Lemma lem1240079 (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term96 _22730' char'.
Proof. exact (fun char'' : type1335 => @lem1240078 char'' char' _22730' h1). Qed.
Lemma lem1240080 (_22730' : type1539) (h1 : term97 _22730') : term97 _22730'.
Proof. exact (h1). Qed.
Lemma lem1240081 (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term79 _22730' char'.
Proof. exact (h1). Qed.
Lemma lem1240082 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : char'' = (term84 _22730')) : term98 _22730' char'' char'.
Proof. exact (@lem1240079 char'' _22730' h1 char'). Qed.
Lemma lem1240083 (_22730' : type1539) (char' : type1335) (char'' : type1335) : (term98 _22730' char' char'') = (term95 _22730' char' char'').
Proof. exact (eq_refl (term98 _22730' char' char'')). Qed.
Lemma lem1240084 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : char'' = (term84 _22730')) : term95 _22730' char'' char'.
Proof. exact (EQ_MP (@lem1240083 _22730' char'' char') (@lem1240082 char' char'' _22730' h1)). Qed.
Lemma lem1240085 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term79 _22730' char') (h2 : char'' = (term84 _22730')) : term94 char'' char'.
Proof. exact (@lem1240084 char' char'' _22730' h2 (@lem1240081 _22730' char' h1)). Qed.
Lemma lem1240086 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') : term99 _22730' char'.
Proof. exact (@lem1240080 _22730' h1 char'). Qed.
Lemma lem1240087 (char' : type1335) (_22730' : type1539) : (term99 _22730' char') = (term100 char' _22730').
Proof. exact (eq_refl (term99 _22730' char')). Qed.
Lemma lem1240088 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') : term100 char' _22730'.
Proof. exact (EQ_MP (@lem1240087 char' _22730') (@lem1240086 char' _22730' h1)). Qed.
Lemma lem1240089 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') : term101 char' _22730' char''.
Proof. exact (@lem1240088 char' _22730' h1 char''). Qed.
Lemma lem1240090 (char' : type1335) (char'' : type1335) (_22730' : type1539) : (term101 char' _22730' char'') = (term102 char' char'' _22730').
Proof. exact (eq_refl (term101 char' _22730' char'')). Qed.
Lemma lem1240091 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') : term102 char' char'' _22730'.
Proof. exact (EQ_MP (@lem1240090 char' char'' _22730') (@lem1240089 char' char'' _22730' h1)). Qed.
Lemma lem1240092 (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term79 _22730' char') (h3 : char'' = (term84 _22730')) : term103 _22730'.
Proof. exact (@lem1240091 char'' char' _22730' h1 (@lem1240085 char' char'' _22730' h2 h3)). Qed.
Lemma lem1240093 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term80 _22730' char' a.
Proof. exact (@lem1240081 _22730' char' h1 a). Qed.
Lemma lem1240094 (_22730' : type1539) (char' : type1335) (a : type1678) : (term80 _22730' char' a) = (term73 _22730' char' a).
Proof. exact (eq_refl (term80 _22730' char' a)). Qed.
Lemma lem1240095 (a : type1678) (_22730' : type1539) (char' : type1335) (h1 : term79 _22730' char') : term73 _22730' char' a.
Proof. exact (EQ_MP (@lem1240094 _22730' char' a) (@lem1240093 a _22730' char' h1)). Qed.
Lemma lem1240096 (a : type1678) (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term79 _22730' char') (h3 : char'' = (term84 _22730')) : term104 _22730' a.
Proof. exact (@lem1240092 char' char'' _22730' h1 h2 h3 a). Qed.
Lemma lem1240097 (a : type1678) (_22730' : type1539) : (term104 _22730' a) = (term105 a _22730').
Proof. exact (eq_refl (term104 _22730' a)). Qed.
Lemma lem1240098 (a : type1678) (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term79 _22730' char') (h3 : char'' = (term84 _22730')) : term105 a _22730'.
Proof. exact (EQ_MP (@lem1240097 a _22730') (@lem1240096 a char' char'' _22730' h1 h2 h3)). Qed.
Lemma lem1240099 (_22730' : type1539) (char' : type1335) (a : type1678) : term106 _22730' char' a.
Proof. exact (@lem51 (term71 a _22730') (term71 a _22730') (char' a)). Qed.
Lemma lem1240100 (a : type1678) (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term79 _22730' char') (h3 : char'' = (term84 _22730')) : term107 _22730' char' a.
Proof. exact (@lem1240099 _22730' char' a (@lem1240098 a char' char'' _22730' h1 h2 h3)). Qed.
Lemma lem1240101 (a : type1678) (char' : type1335) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term79 _22730' char') (h3 : char'' = (term84 _22730')) : term73 _22730' char' a.
Proof. exact (@lem1240100 a char' char'' _22730' h1 h2 h3 (@lem1240095 a _22730' char' h2)). Qed.
Lemma lem1240102 (a : type1678) (_22730' : type1539) (h1 : term71 a _22730') : term71 a _22730'.
Proof. exact (h1). Qed.
Lemma lem1240103 (char' : type1335) (a : type1678) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term79 _22730' char') (h3 : term71 a _22730') (h4 : char'' = (term84 _22730')) : char' a.
Proof. exact (@lem1240101 a char' char'' _22730' h1 h2 h4 (@lem1240102 a _22730' h3)). Qed.
Lemma lem1240104 (char' : type1335) (a : type1678) (char'' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term71 a _22730') (h3 : char'' = (term84 _22730')) : term81 _22730' char' a.
Proof. exact (fun h0 : term79 _22730' char' => @lem1240103 char' a char'' _22730' h1 h0 h2 h3). Qed.
Lemma lem1240105 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term71 a _22730') (h3 : char' = (term84 _22730')) : term86 _22730' a.
Proof. exact (fun char'' : type1335 => @lem1240104 char'' a char' _22730' h1 h2 h3). Qed.
Lemma lem1240106 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term89 char' _22730' a.
Proof. exact (@lem1240061 char' _22730' h1 a). Qed.
Lemma lem1240107 (char' : type1335) (_22730' : type1539) (a : type1678) : (term89 char' _22730' a) = ((char' a) = (term86 _22730' a)).
Proof. exact (eq_refl (term89 char' _22730' a)). Qed.
Lemma lem1240108 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : (char' a) = (term86 _22730' a).
Proof. exact (EQ_MP (@lem1240107 char' _22730' a) (@lem1240106 a char' _22730' h1)). Qed.
Lemma lem1240109 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : (term86 _22730' a) = (char' a).
Proof. exact (SYM (@lem1240108 a char' _22730' h1)). Qed.
Lemma lem1240110 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : term71 a _22730') (h3 : char' = (term84 _22730')) : char' a.
Proof. exact (EQ_MP (@lem1240109 a char' _22730' h3) (@lem1240105 a char' _22730' h1 h2 h3)). Qed.
Lemma lem1240111 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term73 _22730' char' a.
Proof. exact (fun h0 : term71 a _22730' => @lem1240110 a char' _22730' h1 h0 h2). Qed.
Lemma lem1240112 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term79 _22730' char'.
Proof. exact (fun a : type1678 => @lem1240111 a char' _22730' h1 h2). Qed.
Lemma lem1240115 (_22730' : type1539) (a : type1678) : (term108 _22730' a) = (term108 _22730' a).
Proof. exact (eq_refl (term108 _22730' a)). Qed.
Lemma lem1240116 (a : type1678) (_22730' : type1539) : (term108 _22730' a) = (term71 a _22730').
Proof. exact (eq_refl (term108 _22730' a)). Qed.
Lemma lem1240117 (_22730' : type1539) (a : type1678) : (term109 _22730' a) = (term109 _22730' a).
Proof. exact (eq_refl (term109 _22730' a)). Qed.
Lemma lem1240118 (a : type1678) (_22730' : type1539) : ((term108 _22730' a) = (term108 _22730' a)) = ((term108 _22730' a) = (term71 a _22730')).
Proof. exact (MK_COMB (@lem1240117 _22730' a) (@lem1240116 a _22730')). Qed.
Lemma lem1240119 (a : type1678) (_22730' : type1539) : (term108 _22730' a) = (term71 a _22730').
Proof. exact (EQ_MP (@lem1240118 a _22730') (@lem1240115 _22730' a)). Qed.
Lemma lem1240120 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1240121 (a : type1678) (_22730' : type1539) : (term110 _22730' a) = (term111 a _22730').
Proof. exact (MK_COMB (@lem1240120) (@lem1240119 a _22730')). Qed.
Lemma lem1240122 (char' : type1335) (a : type1678) : (char' a) = (char' a).
Proof. exact (eq_refl (char' a)). Qed.
Lemma lem1240123 (_22730' : type1539) (char' : type1335) (a : type1678) : (term112 _22730' char' a) = (term73 _22730' char' a).
Proof. exact (MK_COMB (@lem1240121 a _22730') (@lem1240122 char' a)). Qed.
Lemma lem1240124 (a : type1678) (_22730' : type1539) : (term111 a _22730') = (term111 a _22730').
Proof. exact (eq_refl (term111 a _22730')). Qed.
Lemma lem1240125 (a : type1678) (_22730' : type1539) : (term113 _22730' a) = (term105 a _22730').
Proof. exact (MK_COMB (@lem1240124 a _22730') (@lem1240119 a _22730')). Qed.
Lemma lem1240126 (char' : type1335) (a : type1678) : (term114 char' a) = (term114 char' a).
Proof. exact (eq_refl (term114 char' a)). Qed.
Lemma lem1240127 (char' : type1335) (a : type1678) (_22730' : type1539) : (term115 char' _22730' a) = (term116 char' a _22730').
Proof. exact (MK_COMB (@lem1240126 char' a) (@lem1240119 a _22730')). Qed.
Lemma lem1240128 (char' : type1335) (_22730' : type1539) : (term117 char' _22730') = (term118 char' _22730').
Proof. exact (fun_ext (fun a : type1678 => @lem1240127 char' a _22730')). Qed.
Lemma lem1240129 : (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) = (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))).
Proof. exact (eq_refl (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))))). Qed.
Lemma lem1240130 (char' : type1335) (_22730' : type1539) : (term119 char' _22730') = (term120 char' _22730').
Proof. exact (MK_COMB (@lem1240129) (@lem1240128 char' _22730')). Qed.
Lemma lem1240131 (_22730' : type1539) : (term121 _22730') = (term122 _22730').
Proof. exact (fun_ext (fun a : type1678 => @lem1240125 a _22730')). Qed.
Lemma lem1240132 : (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) = (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))).
Proof. exact (eq_refl (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))))). Qed.
Lemma lem1240133 (_22730' : type1539) : (term123 _22730') = (term103 _22730').
Proof. exact (MK_COMB (@lem1240132) (@lem1240131 _22730')). Qed.
Lemma lem1240134 (_22730' : type1539) (char' : type1335) : (term124 _22730' char') = (term78 _22730' char').
Proof. exact (fun_ext (fun a : type1678 => @lem1240123 _22730' char' a)). Qed.
Lemma lem1240135 : (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))) = (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop))))))))).
Proof. exact (eq_refl (@all (recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))))). Qed.
Lemma lem1240136 (_22730' : type1539) (char' : type1335) : (term125 _22730' char') = (term79 _22730' char').
Proof. exact (MK_COMB (@lem1240135) (@lem1240134 _22730' char')). Qed.
Lemma lem1240137 (_22730' : type1539) (char' : type1335) : (term79 _22730' char') = (term125 _22730' char').
Proof. exact (SYM (@lem1240136 _22730' char')). Qed.
Lemma lem1240138 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term125 _22730' char'.
Proof. exact (EQ_MP (@lem1240137 _22730' char') (@lem1240112 char' _22730' h1 h2)). Qed.
Lemma lem1240139 (_22730' : type1539) (h1 : term97 _22730') : term126 _22730'.
Proof. exact (@lem1240080 _22730' h1 (term127 _22730')). Qed.
Lemma lem1240140 (_22730' : type1539) : (term126 _22730') = (term128 _22730').
Proof. exact (eq_refl (term126 _22730')). Qed.
Lemma lem1240141 (_22730' : type1539) (h1 : term97 _22730') : term128 _22730'.
Proof. exact (EQ_MP (@lem1240140 _22730') (@lem1240139 _22730' h1)). Qed.
Lemma lem1240142 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') : term129 _22730' char'.
Proof. exact (@lem1240141 _22730' h1 char'). Qed.
Lemma lem1240143 (char' : type1335) (_22730' : type1539) : (term129 _22730' char') = (term130 char' _22730').
Proof. exact (eq_refl (term129 _22730' char')). Qed.
Lemma lem1240144 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') : term130 char' _22730'.
Proof. exact (EQ_MP (@lem1240143 char' _22730') (@lem1240142 char' _22730' h1)). Qed.
Lemma lem1240145 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term103 _22730'.
Proof. exact (@lem1240144 char' _22730' h1 (@lem1240138 char' _22730' h1 h2)). Qed.
Lemma lem1240146 (_22730' : type1539) : (term103 _22730') = (term123 _22730').
Proof. exact (SYM (@lem1240133 _22730')). Qed.
Lemma lem1240147 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term123 _22730'.
Proof. exact (EQ_MP (@lem1240146 _22730') (@lem1240145 char' _22730' h1 h2)). Qed.
Lemma lem1240148 (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term131 char' _22730'.
Proof. exact (@lem1240079 char' _22730' h1 (term127 _22730')). Qed.
Lemma lem1240149 (char' : type1335) (_22730' : type1539) : (term131 char' _22730') = (term132 char' _22730').
Proof. exact (eq_refl (term131 char' _22730')). Qed.
Lemma lem1240150 (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term132 char' _22730'.
Proof. exact (EQ_MP (@lem1240149 char' _22730') (@lem1240148 char' _22730' h1)). Qed.
Lemma lem1240151 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term119 char' _22730'.
Proof. exact (@lem1240150 char' _22730' h2 (@lem1240147 char' _22730' h1 h2)). Qed.
Lemma lem1240152 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term120 char' _22730'.
Proof. exact (EQ_MP (@lem1240130 char' _22730') (@lem1240151 char' _22730' h1 h2)). Qed.
Lemma lem1240153 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term80 _22730' char' a.
Proof. exact (@lem1240112 char' _22730' h1 h2 a). Qed.
Lemma lem1240154 (_22730' : type1539) (char' : type1335) (a : type1678) : (term80 _22730' char' a) = (term73 _22730' char' a).
Proof. exact (eq_refl (term80 _22730' char' a)). Qed.
Lemma lem1240155 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term73 _22730' char' a.
Proof. exact (EQ_MP (@lem1240154 _22730' char' a) (@lem1240153 a char' _22730' h1 h2)). Qed.
Lemma lem1240156 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term133 char' _22730' a.
Proof. exact (@lem1240152 char' _22730' h1 h2 a). Qed.
Lemma lem1240157 (char' : type1335) (a : type1678) (_22730' : type1539) : (term133 char' _22730' a) = (term116 char' a _22730').
Proof. exact (eq_refl (term133 char' _22730' a)). Qed.
Lemma lem1240158 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term116 char' a _22730'.
Proof. exact (EQ_MP (@lem1240157 char' a _22730') (@lem1240156 a char' _22730' h1 h2)). Qed.
Lemma lem1240159 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term134 _22730' char' a.
Proof. exact (conj (@lem1240158 a char' _22730' h1 h2) (@lem1240155 a char' _22730' h1 h2)). Qed.
Lemma lem1240160 (char' : type1335) (a : type1678) (_22730' : type1539) : (term134 _22730' char' a) = ((char' a) = (term71 a _22730')).
Proof. exact (@lem32 (char' a) (term71 a _22730')). Qed.
Lemma lem1240161 (a : type1678) (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : (char' a) = (term71 a _22730').
Proof. exact (EQ_MP (@lem1240160 char' a _22730') (@lem1240159 a char' _22730' h1 h2)). Qed.
Lemma lem1240166 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term79 _22730' char'.
Proof. exact (fun a : type1678 => @lem1240111 a char' _22730' h1 h2). Qed.
Lemma lem1240167 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term135 char' _22730'.
Proof. exact (fun a : type1678 => @lem1240161 a char' _22730' h1 h2). Qed.
Lemma lem1240168 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term96 _22730' char'.
Proof. exact (fun char'' : type1335 => @lem1240078 char'' char' _22730' h2). Qed.
Lemma lem1240169 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term0 char' _22730'.
Proof. exact (EQ_MP (@lem1240053 char' _22730') (@lem1240166 char' _22730' h1 h2)). Qed.
Lemma lem1240183 (char' : type1335) (_22730' : type1539) : (term79 _22730' char') = (term0 char' _22730').
Proof. exact (SYM (@lem1240052 _22730' char')). Qed.
Lemma lem1240184 (char' : type1335) (_22730' : type1539) : (term79 _22730' char') = (term0 char' _22730').
Proof. exact (@lem1240183 char' _22730'). Qed.
Lemma lem1240185 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1240186 (char' : type1335) (_22730' : type1539) : (term136 _22730' char') = (term137 char' _22730').
Proof. exact (MK_COMB (@lem1240185) (@lem1240184 char' _22730')). Qed.
Lemma lem1240211 (char' : type1335) (char'' : type1335) : (term94 char' char'') = (term94 char' char'').
Proof. exact (eq_refl (term94 char' char'')). Qed.
Lemma lem1240212 (_22730' : type1539) (char' : type1335) (char'' : type1335) : (term95 _22730' char' char'') = (term138 _22730' char' char'').
Proof. exact (MK_COMB (@lem1240186 char'' _22730') (@lem1240211 char' char'')). Qed.
Lemma lem1240213 (_22730' : type1539) (char' : type1335) : (term139 _22730' char') = (term140 _22730' char').
Proof. exact (fun_ext (fun char'' : type1335 => @lem1240212 _22730' char' char'')). Qed.
Lemma lem1240214 : (@all ((recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop)) = (@all ((recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop)).
Proof. exact (eq_refl (@all ((recspace (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop (prod Prop Prop)))))))) -> Prop))). Qed.
Lemma lem1240215 (_22730' : type1539) (char' : type1335) : (term96 _22730' char') = (term141 _22730' char').
Proof. exact (MK_COMB (@lem1240214) (@lem1240213 _22730' char')). Qed.
Lemma lem1240216 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term141 _22730' char'.
Proof. exact (EQ_MP (@lem1240215 _22730' char') (@lem1240168 char' _22730' h1 h2)). Qed.
Lemma lem1240217 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term142 char' _22730'.
Proof. exact (conj (@lem1240216 char' _22730' h1 h2) (@lem1240167 char' _22730' h1 h2)). Qed.
Lemma lem1240218 (char' : type1335) (_22730' : type1539) (h1 : term97 _22730') (h2 : char' = (term84 _22730')) : term143 char' _22730'.
Proof. exact (conj (@lem1240169 char' _22730' h1 h2) (@lem1240217 char' _22730' h1 h2)). Qed.
Lemma lem1240220 (a : type1678) (_22730' : type1539) : term144 a _22730'.
Proof. exact (@lem9120 (term71 a _22730')). Qed.
Lemma lem1240221 (a : type1678) (_22730' : type1539) : (term144 a _22730') = (term105 a _22730').
Proof. exact (eq_refl (term144 a _22730')). Qed.
Lemma lem1240222 (a : type1678) (_22730' : type1539) : term105 a _22730'.
Proof. exact (EQ_MP (@lem1240221 a _22730') (@lem1240220 a _22730')). Qed.
Lemma lem1240227 (_22730' : type1539) : term103 _22730'.
Proof. exact (fun a : type1678 => @lem1240222 a _22730'). Qed.
Lemma lem1240228 (char' : type1335) (char'' : type1335) (_22730' : type1539) : term102 char' char'' _22730'.
Proof. exact (fun h0 : term94 char' char'' => @lem1240227 _22730'). Qed.
Lemma lem1240233 (char' : type1335) (_22730' : type1539) : term100 char' _22730'.
Proof. exact (fun char'' : type1335 => @lem1240228 char' char'' _22730'). Qed.
Lemma lem1240238 (_22730' : type1539) : term97 _22730'.
Proof. exact (fun char' : type1335 => @lem1240233 char' _22730'). Qed.
Lemma lem1240239 (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : (term97 _22730') = (term143 char' _22730').
Proof. exact (prop_ext (fun h2 : term97 _22730' => @lem1240218 char' _22730' h2 h1) (fun h2 : term143 char' _22730' => @lem1240238 _22730')). Qed.
Lemma lem1240240 (char' : type1335) (_22730' : type1539) (h1 : char' = (term84 _22730')) : term143 char' _22730'.
Proof. exact (EQ_MP (@lem1240239 char' _22730' h1) (@lem1240238 _22730')). Qed.
