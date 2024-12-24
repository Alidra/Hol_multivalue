Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_LE_1_term_abbrevs.
Require Import REAL_INV_1_spec.
Require Import REAL_LE_INV2_spec.
Require Import REAL_LT_01_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1632889 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1632890 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1632889 h1 x). Qed.
Lemma lem1632891 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1632892 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1632891 x) (@lem1632890 x h1)). Qed.
Lemma lem1632893 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1632892 x h1 y). Qed.
Lemma lem1632894 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1632895 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1632894 y x) (@lem1632893 x y h1)). Qed.
Lemma lem1632896 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1632897 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1632895 y x h1 (@lem1632896 x y h2)). Qed.
Lemma lem1632898 (x : real) (y : real) (h1 : term5 x y) : term7 y x.
Proof. exact (fun h0 : term0 => @lem1632897 x y h0 h1). Qed.
Lemma lem1632899 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1632900 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1632898 x y h2 (@lem1632899 h1)). Qed.
Lemma lem1632901 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (fun h0 : term5 x y => @lem1632900 x y h1 h0). Qed.
Lemma lem1632902 (y : real) (h1 : term0) : term8 y.
Proof. exact (fun x : real => @lem1632901 y x h1). Qed.
Lemma lem1632903 (h1 : term0) : term9.
Proof. exact (fun y : real => @lem1632902 y h1). Qed.
Lemma lem1632904 : term10.
Proof. exact (fun h0 : term0 => @lem1632903 h0). Qed.
Lemma lem1632905 : term9.
Proof. exact (@lem1632904 (@lem1632440)). Qed.
Lemma lem1632906 (y : real) : term11 y.
Proof. exact (@lem1632905 y). Qed.
Lemma lem1632907 (y : real) : (term11 y) = (term8 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1632908 (y : real) : term8 y.
Proof. exact (EQ_MP (@lem1632907 y) (@lem1632906 y)). Qed.
Lemma lem1632909 (y : real) (x : real) : term12 y x.
Proof. exact (@lem1632908 y x). Qed.
Lemma lem1632910 (y : real) (x : real) : (term12 y x) = (term4 y x).
Proof. exact (eq_refl (term12 y x)). Qed.
Lemma lem1632912 (h1 : term13 = term14) : term13 = term14.
Proof. exact (h1). Qed.
Lemma lem1632913 (h1 : term13 = term14) : term14 = term13.
Proof. exact (SYM (@lem1632912 h1)). Qed.
Lemma lem1632914 (h1 : term14 = term13) : term14 = term13.
Proof. exact (h1). Qed.
Lemma lem1632915 (h1 : term14 = term13) : term13 = term14.
Proof. exact (SYM (@lem1632914 h1)). Qed.
Lemma lem1632916 : (term13 = term14) = (term14 = term13).
Proof. exact (prop_ext (fun h1 : term13 = term14 => @lem1632913 h1) (fun h1 : term14 = term13 => @lem1632915 h1)). Qed.
Lemma lem1632918 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1632920 : term14 = term13.
Proof. exact (EQ_MP (@lem1632916) (@lem1592031)). Qed.
Lemma lem1632921 (x : real) : (term16 x) = (term16 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1632922 (x : real) : (term17 x) = (term18 x).
Proof. exact (MK_COMB (@lem1632921 x) (@lem1632920)). Qed.
Lemma lem1632923 (x : real) : (term18 x) = (term17 x).
Proof. exact (SYM (@lem1632922 x)). Qed.
Lemma lem1632925 (y : real) (x : real) : term4 y x.
Proof. exact (EQ_MP (@lem1632910 y x) (@lem1632909 y x)). Qed.
Lemma lem1632926 (x : real) : term19 x.
Proof. exact (@lem1632925 x term14). Qed.
Lemma lem1632927 : term20 = (term20 = True).
Proof. exact (@lem7 term20). Qed.
Lemma lem1632929 (x : real) : (term15 x) = ((term15 x) = True).
Proof. exact (@lem7 (term15 x)). Qed.
Lemma lem1632934 : term20 = True.
Proof. exact (EQ_MP (@lem1632927) (@lem1499399)). Qed.
Lemma lem1632935 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1632936 : term21 = (and True).
Proof. exact (MK_COMB (@lem1632935) (@lem1632934)). Qed.
Lemma lem1632938 (x : real) (h1 : term15 x) : (term15 x) = True.
Proof. exact (EQ_MP (@lem1632929 x) (@lem1632918 x h1)). Qed.
Lemma lem1632939 (x : real) (h1 : term15 x) : (term22 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1632936) (@lem1632938 x h1)). Qed.
Lemma lem1632941 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1632942 : (True /\ True) = True.
Proof. exact (@lem1632941 True). Qed.
Lemma lem1632943 (x : real) (h1 : term15 x) : (term22 x) = True.
Proof. exact (TRANS (@lem1632939 x h1) (@lem1632942)). Qed.
Lemma lem1632944 (x : real) (h1 : term15 x) : True = (term22 x).
Proof. exact (SYM (@lem1632943 x h1)). Qed.
Lemma lem1632945 (x : real) (h1 : term15 x) : term22 x.
Proof. exact (EQ_MP (@lem1632944 x h1) (@lem0)). Qed.
Lemma lem1632946 (x : real) (h1 : term15 x) : term18 x.
Proof. exact (@lem1632926 x (@lem1632945 x h1)). Qed.
Lemma lem1632947 (x : real) (h1 : term15 x) : term17 x.
Proof. exact (EQ_MP (@lem1632923 x) (@lem1632946 x h1)). Qed.
Lemma lem1632948 (x : real) (h1 : term15 x) : (term15 x) = (term17 x).
Proof. exact (prop_ext (fun h2 : term15 x => @lem1632947 x h1) (fun h2 : term17 x => @lem1632918 x h1)). Qed.
Lemma lem1632949 (x : real) (h1 : term15 x) : term17 x.
Proof. exact (EQ_MP (@lem1632948 x h1) (@lem1632918 x h1)). Qed.
Lemma lem1632950 (x : real) : term23 x.
Proof. exact (fun h0 : term15 x => @lem1632949 x h0). Qed.
Lemma lem1632955 : term24.
Proof. exact (fun x : real => @lem1632950 x). Qed.
