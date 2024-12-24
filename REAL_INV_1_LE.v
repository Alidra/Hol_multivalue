Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_1_LE_term_abbrevs.
Require Import REAL_INV_1_spec.
Require Import REAL_LE_INV2_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1632956 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1632957 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1632956 h1 x). Qed.
Lemma lem1632958 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1632959 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1632958 x) (@lem1632957 x h1)). Qed.
Lemma lem1632960 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1632959 x h1 y). Qed.
Lemma lem1632961 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1632962 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1632961 y x) (@lem1632960 x y h1)). Qed.
Lemma lem1632963 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1632964 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1632962 y x h1 (@lem1632963 x y h2)). Qed.
Lemma lem1632965 (x : real) (y : real) (h1 : term5 x y) : term7 y x.
Proof. exact (fun h0 : term0 => @lem1632964 x y h0 h1). Qed.
Lemma lem1632966 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1632967 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1632965 x y h2 (@lem1632966 h1)). Qed.
Lemma lem1632968 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (fun h0 : term5 x y => @lem1632967 x y h1 h0). Qed.
Lemma lem1632969 (y : real) (h1 : term0) : term8 y.
Proof. exact (fun x : real => @lem1632968 y x h1). Qed.
Lemma lem1632970 (h1 : term0) : term9.
Proof. exact (fun y : real => @lem1632969 y h1). Qed.
Lemma lem1632971 : term10.
Proof. exact (fun h0 : term0 => @lem1632970 h0). Qed.
Lemma lem1632972 : term9.
Proof. exact (@lem1632971 (@lem1632440)). Qed.
Lemma lem1632973 (y : real) : term11 y.
Proof. exact (@lem1632972 y). Qed.
Lemma lem1632974 (y : real) : (term11 y) = (term8 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1632975 (y : real) : term8 y.
Proof. exact (EQ_MP (@lem1632974 y) (@lem1632973 y)). Qed.
Lemma lem1632976 (y : real) (x : real) : term12 y x.
Proof. exact (@lem1632975 y x). Qed.
Lemma lem1632977 (y : real) (x : real) : (term12 y x) = (term4 y x).
Proof. exact (eq_refl (term12 y x)). Qed.
Lemma lem1632979 (h1 : term13 = term14) : term13 = term14.
Proof. exact (h1). Qed.
Lemma lem1632980 (h1 : term13 = term14) : term14 = term13.
Proof. exact (SYM (@lem1632979 h1)). Qed.
Lemma lem1632981 (h1 : term14 = term13) : term14 = term13.
Proof. exact (h1). Qed.
Lemma lem1632982 (h1 : term14 = term13) : term13 = term14.
Proof. exact (SYM (@lem1632981 h1)). Qed.
Lemma lem1632983 : (term13 = term14) = (term14 = term13).
Proof. exact (prop_ext (fun h1 : term13 = term14 => @lem1632980 h1) (fun h1 : term14 = term13 => @lem1632982 h1)). Qed.
Lemma lem1632985 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1632986 (x : real) (h1 : term16 x) : term16 x.
Proof. exact (h1). Qed.
Lemma lem1632987 (x : real) (h1 : term17 x) : term17 x.
Proof. exact (h1). Qed.
Lemma lem1632989 : term14 = term13.
Proof. exact (EQ_MP (@lem1632983) (@lem1592031)). Qed.
Lemma lem1632990 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem1632991 : term18 = term19.
Proof. exact (MK_COMB (@lem1632990) (@lem1632989)). Qed.
Lemma lem1632992 (x : real) : (real_inv x) = (real_inv x).
Proof. exact (eq_refl (real_inv x)). Qed.
Lemma lem1632993 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1632991) (@lem1632992 x)). Qed.
Lemma lem1632994 (x : real) : (term21 x) = (term20 x).
Proof. exact (SYM (@lem1632993 x)). Qed.
Lemma lem1632996 (y : real) (x : real) : term4 y x.
Proof. exact (EQ_MP (@lem1632977 y x) (@lem1632976 y x)). Qed.
Lemma lem1632997 (x : real) : term22 x.
Proof. exact (@lem1632996 term14 x). Qed.
Lemma lem1633000 (x : real) : (term17 x) = ((term17 x) = True).
Proof. exact (@lem7 (term17 x)). Qed.
Lemma lem1633002 (x : real) : (term16 x) = ((term16 x) = True).
Proof. exact (@lem7 (term16 x)). Qed.
Lemma lem1633007 (x : real) (h1 : term17 x) : (term17 x) = True.
Proof. exact (EQ_MP (@lem1633000 x) (@lem1632987 x h1)). Qed.
Lemma lem1633008 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1633009 (x : real) (h1 : term17 x) : (term23 x) = (and True).
Proof. exact (MK_COMB (@lem1633008) (@lem1633007 x h1)). Qed.
Lemma lem1633011 (x : real) (h1 : term16 x) : (term16 x) = True.
Proof. exact (EQ_MP (@lem1633002 x) (@lem1632986 x h1)). Qed.
Lemma lem1633012 (x : real) (h1 : term16 x) (h2 : term17 x) : (term15 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1633009 x h2) (@lem1633011 x h1)). Qed.
Lemma lem1633014 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1633015 : (True /\ True) = True.
Proof. exact (@lem1633014 True). Qed.
Lemma lem1633016 (x : real) (h1 : term16 x) (h2 : term17 x) : (term15 x) = True.
Proof. exact (TRANS (@lem1633012 x h1 h2) (@lem1633015)). Qed.
Lemma lem1633017 (x : real) (h1 : term16 x) (h2 : term17 x) : True = (term15 x).
Proof. exact (SYM (@lem1633016 x h1 h2)). Qed.
Lemma lem1633018 (x : real) (h1 : term16 x) (h2 : term17 x) : term15 x.
Proof. exact (EQ_MP (@lem1633017 x h1 h2) (@lem0)). Qed.
Lemma lem1633019 (x : real) (h1 : term16 x) (h2 : term17 x) : term21 x.
Proof. exact (@lem1632997 x (@lem1633018 x h1 h2)). Qed.
Lemma lem1633020 (x : real) (h1 : term16 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1632994 x) (@lem1633019 x h1 h2)). Qed.
Lemma lem1633021 (x : real) (h1 : term15 x) : term16 x.
Proof. exact (proj2 (@lem1632985 x h1)). Qed.
Lemma lem1633022 (x : real) (h1 : term15 x) : term17 x.
Proof. exact (proj1 (@lem1632985 x h1)). Qed.
Lemma lem1633023 (x : real) (h1 : term16 x) (h2 : term17 x) : (term16 x) = (term20 x).
Proof. exact (prop_ext (fun h3 : term16 x => @lem1633020 x h1 h2) (fun h3 : term20 x => @lem1632986 x h1)). Qed.
Lemma lem1633024 (x : real) (h1 : term16 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1633023 x h1 h2) (@lem1632986 x h1)). Qed.
Lemma lem1633025 (x : real) (h1 : term16 x) (h2 : term17 x) : (term17 x) = (term20 x).
Proof. exact (prop_ext (fun h3 : term17 x => @lem1633024 x h1 h2) (fun h3 : term20 x => @lem1632987 x h2)). Qed.
Lemma lem1633026 (x : real) (h1 : term16 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1633025 x h1 h2) (@lem1632987 x h2)). Qed.
Lemma lem1633027 (x : real) (h1 : term15 x) (h2 : term17 x) : (term16 x) = (term20 x).
Proof. exact (prop_ext (fun h3 : term16 x => @lem1633026 x h3 h2) (fun h3 : term20 x => @lem1633021 x h1)). Qed.
Lemma lem1633028 (x : real) (h1 : term15 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1633027 x h1 h2) (@lem1633021 x h1)). Qed.
Lemma lem1633029 (x : real) (h1 : term15 x) : (term17 x) = (term20 x).
Proof. exact (prop_ext (fun h2 : term17 x => @lem1633028 x h1 h2) (fun h2 : term20 x => @lem1633022 x h1)). Qed.
Lemma lem1633030 (x : real) (h1 : term15 x) : term20 x.
Proof. exact (EQ_MP (@lem1633029 x h1) (@lem1633022 x h1)). Qed.
Lemma lem1633031 (x : real) : term24 x.
Proof. exact (fun h0 : term15 x => @lem1633030 x h0). Qed.
Lemma lem1633036 : term25.
Proof. exact (fun x : real => @lem1633031 x). Qed.
