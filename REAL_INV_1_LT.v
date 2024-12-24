Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_INV_1_LT_term_abbrevs.
Require Import REAL_INV_1_spec.
Require Import REAL_LT_INV2_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem1633104 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1633105 (x : real) (h1 : term0) : term1 x.
Proof. exact (@lem1633104 h1 x). Qed.
Lemma lem1633106 (x : real) : (term1 x) = (term2 x).
Proof. exact (eq_refl (term1 x)). Qed.
Lemma lem1633107 (x : real) (h1 : term0) : term2 x.
Proof. exact (EQ_MP (@lem1633106 x) (@lem1633105 x h1)). Qed.
Lemma lem1633108 (x : real) (y : real) (h1 : term0) : term3 x y.
Proof. exact (@lem1633107 x h1 y). Qed.
Lemma lem1633109 (y : real) (x : real) : (term3 x y) = (term4 y x).
Proof. exact (eq_refl (term3 x y)). Qed.
Lemma lem1633110 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (EQ_MP (@lem1633109 y x) (@lem1633108 x y h1)). Qed.
Lemma lem1633111 (x : real) (y : real) (h1 : term5 x y) : term5 x y.
Proof. exact (h1). Qed.
Lemma lem1633112 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1633110 y x h1 (@lem1633111 x y h2)). Qed.
Lemma lem1633113 (x : real) (y : real) (h1 : term5 x y) : term7 y x.
Proof. exact (fun h0 : term0 => @lem1633112 x y h0 h1). Qed.
Lemma lem1633114 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem1633115 (x : real) (y : real) (h1 : term0) (h2 : term5 x y) : term6 y x.
Proof. exact (@lem1633113 x y h2 (@lem1633114 h1)). Qed.
Lemma lem1633116 (y : real) (x : real) (h1 : term0) : term4 y x.
Proof. exact (fun h0 : term5 x y => @lem1633115 x y h1 h0). Qed.
Lemma lem1633117 (y : real) (h1 : term0) : term8 y.
Proof. exact (fun x : real => @lem1633116 y x h1). Qed.
Lemma lem1633118 (h1 : term0) : term9.
Proof. exact (fun y : real => @lem1633117 y h1). Qed.
Lemma lem1633119 : term10.
Proof. exact (fun h0 : term0 => @lem1633118 h0). Qed.
Lemma lem1633120 : term9.
Proof. exact (@lem1633119 (@lem1632194)). Qed.
Lemma lem1633121 (y : real) : term11 y.
Proof. exact (@lem1633120 y). Qed.
Lemma lem1633122 (y : real) : (term11 y) = (term8 y).
Proof. exact (eq_refl (term11 y)). Qed.
Lemma lem1633123 (y : real) : term8 y.
Proof. exact (EQ_MP (@lem1633122 y) (@lem1633121 y)). Qed.
Lemma lem1633124 (y : real) (x : real) : term12 y x.
Proof. exact (@lem1633123 y x). Qed.
Lemma lem1633125 (y : real) (x : real) : (term12 y x) = (term4 y x).
Proof. exact (eq_refl (term12 y x)). Qed.
Lemma lem1633127 (h1 : term13 = term14) : term13 = term14.
Proof. exact (h1). Qed.
Lemma lem1633128 (h1 : term13 = term14) : term14 = term13.
Proof. exact (SYM (@lem1633127 h1)). Qed.
Lemma lem1633129 (h1 : term14 = term13) : term14 = term13.
Proof. exact (h1). Qed.
Lemma lem1633130 (h1 : term14 = term13) : term13 = term14.
Proof. exact (SYM (@lem1633129 h1)). Qed.
Lemma lem1633131 : (term13 = term14) = (term14 = term13).
Proof. exact (prop_ext (fun h1 : term13 = term14 => @lem1633128 h1) (fun h1 : term14 = term13 => @lem1633130 h1)). Qed.
Lemma lem1633133 (x : real) (h1 : term15 x) : term15 x.
Proof. exact (h1). Qed.
Lemma lem1633134 (x : real) (h1 : term16 x) : term16 x.
Proof. exact (h1). Qed.
Lemma lem1633135 (x : real) (h1 : term17 x) : term17 x.
Proof. exact (h1). Qed.
Lemma lem1633137 : term14 = term13.
Proof. exact (EQ_MP (@lem1633131) (@lem1592031)). Qed.
Lemma lem1633138 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem1633139 : term18 = term19.
Proof. exact (MK_COMB (@lem1633138) (@lem1633137)). Qed.
Lemma lem1633140 (x : real) : (real_inv x) = (real_inv x).
Proof. exact (eq_refl (real_inv x)). Qed.
Lemma lem1633141 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1633139) (@lem1633140 x)). Qed.
Lemma lem1633142 (x : real) : (term21 x) = (term20 x).
Proof. exact (SYM (@lem1633141 x)). Qed.
Lemma lem1633144 (y : real) (x : real) : term4 y x.
Proof. exact (EQ_MP (@lem1633125 y x) (@lem1633124 y x)). Qed.
Lemma lem1633145 (x : real) : term22 x.
Proof. exact (@lem1633144 term14 x). Qed.
Lemma lem1633148 (x : real) : (term17 x) = ((term17 x) = True).
Proof. exact (@lem7 (term17 x)). Qed.
Lemma lem1633150 (x : real) : (term16 x) = ((term16 x) = True).
Proof. exact (@lem7 (term16 x)). Qed.
Lemma lem1633155 (x : real) (h1 : term17 x) : (term17 x) = True.
Proof. exact (EQ_MP (@lem1633148 x) (@lem1633135 x h1)). Qed.
Lemma lem1633156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1633157 (x : real) (h1 : term17 x) : (term23 x) = (and True).
Proof. exact (MK_COMB (@lem1633156) (@lem1633155 x h1)). Qed.
Lemma lem1633159 (x : real) (h1 : term16 x) : (term16 x) = True.
Proof. exact (EQ_MP (@lem1633150 x) (@lem1633134 x h1)). Qed.
Lemma lem1633160 (x : real) (h1 : term16 x) (h2 : term17 x) : (term15 x) = (True /\ True).
Proof. exact (MK_COMB (@lem1633157 x h2) (@lem1633159 x h1)). Qed.
Lemma lem1633162 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1633163 : (True /\ True) = True.
Proof. exact (@lem1633162 True). Qed.
Lemma lem1633164 (x : real) (h1 : term16 x) (h2 : term17 x) : (term15 x) = True.
Proof. exact (TRANS (@lem1633160 x h1 h2) (@lem1633163)). Qed.
Lemma lem1633165 (x : real) (h1 : term16 x) (h2 : term17 x) : True = (term15 x).
Proof. exact (SYM (@lem1633164 x h1 h2)). Qed.
Lemma lem1633166 (x : real) (h1 : term16 x) (h2 : term17 x) : term15 x.
Proof. exact (EQ_MP (@lem1633165 x h1 h2) (@lem0)). Qed.
Lemma lem1633167 (x : real) (h1 : term16 x) (h2 : term17 x) : term21 x.
Proof. exact (@lem1633145 x (@lem1633166 x h1 h2)). Qed.
Lemma lem1633168 (x : real) (h1 : term16 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1633142 x) (@lem1633167 x h1 h2)). Qed.
Lemma lem1633169 (x : real) (h1 : term15 x) : term16 x.
Proof. exact (proj2 (@lem1633133 x h1)). Qed.
Lemma lem1633170 (x : real) (h1 : term15 x) : term17 x.
Proof. exact (proj1 (@lem1633133 x h1)). Qed.
Lemma lem1633171 (x : real) (h1 : term16 x) (h2 : term17 x) : (term16 x) = (term20 x).
Proof. exact (prop_ext (fun h3 : term16 x => @lem1633168 x h1 h2) (fun h3 : term20 x => @lem1633134 x h1)). Qed.
Lemma lem1633172 (x : real) (h1 : term16 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1633171 x h1 h2) (@lem1633134 x h1)). Qed.
Lemma lem1633173 (x : real) (h1 : term16 x) (h2 : term17 x) : (term17 x) = (term20 x).
Proof. exact (prop_ext (fun h3 : term17 x => @lem1633172 x h1 h2) (fun h3 : term20 x => @lem1633135 x h2)). Qed.
Lemma lem1633174 (x : real) (h1 : term16 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1633173 x h1 h2) (@lem1633135 x h2)). Qed.
Lemma lem1633175 (x : real) (h1 : term15 x) (h2 : term17 x) : (term16 x) = (term20 x).
Proof. exact (prop_ext (fun h3 : term16 x => @lem1633174 x h3 h2) (fun h3 : term20 x => @lem1633169 x h1)). Qed.
Lemma lem1633176 (x : real) (h1 : term15 x) (h2 : term17 x) : term20 x.
Proof. exact (EQ_MP (@lem1633175 x h1 h2) (@lem1633169 x h1)). Qed.
Lemma lem1633177 (x : real) (h1 : term15 x) : (term17 x) = (term20 x).
Proof. exact (prop_ext (fun h2 : term17 x => @lem1633176 x h1 h2) (fun h2 : term20 x => @lem1633170 x h1)). Qed.
Lemma lem1633178 (x : real) (h1 : term15 x) : term20 x.
Proof. exact (EQ_MP (@lem1633177 x h1) (@lem1633170 x h1)). Qed.
Lemma lem1633179 (x : real) : term24 x.
Proof. exact (fun h0 : term15 x => @lem1633178 x h0). Qed.
Lemma lem1633184 : term25.
Proof. exact (fun x : real => @lem1633179 x). Qed.
