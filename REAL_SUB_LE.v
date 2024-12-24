Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SUB_LE_term_abbrevs.
Require Import REAL_LE_LNEG_spec.
Require Import REAL_LE_NEG2_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1374147 (x : real) (y : real) (h1 : (term0 x y) = (term1 x y)) : (term0 x y) = (term1 x y).
Proof. exact (h1). Qed.
Lemma lem1374148 (x : real) (y : real) (h1 : (term0 x y) = (term1 x y)) : (term1 x y) = (term0 x y).
Proof. exact (SYM (@lem1374147 x y h1)). Qed.
Lemma lem1374149 (x : real) (y : real) (h1 : (term1 x y) = (term0 x y)) : (term1 x y) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem1374150 (x : real) (y : real) (h1 : (term1 x y) = (term0 x y)) : (term0 x y) = (term1 x y).
Proof. exact (SYM (@lem1374149 x y h1)). Qed.
Lemma lem1374151 (x : real) (y : real) : ((term0 x y) = (term1 x y)) = ((term1 x y) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (term1 x y) => @lem1374148 x y h1) (fun h1 : (term1 x y) = (term0 x y) => @lem1374150 x y h1)). Qed.
Lemma lem1374152 (x : real) : (term2 x) = (term3 x).
Proof. exact (fun_ext (fun y : real => @lem1374151 x y)). Qed.
Lemma lem1374153 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374154 (x : real) : (term4 x) = (term5 x).
Proof. exact (MK_COMB (@lem1374153) (@lem1374152 x)). Qed.
Lemma lem1374155 : term6 = term7.
Proof. exact (fun_ext (fun x : real => @lem1374154 x)). Qed.
Lemma lem1374156 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374157 : term8 = term9.
Proof. exact (MK_COMB (@lem1374156) (@lem1374155)). Qed.
Lemma lem1374158 : term9.
Proof. exact (EQ_MP (@lem1374157) (@lem1362225)). Qed.
Lemma lem1374159 (x : real) : term10 x.
Proof. exact (@lem1362291 x). Qed.
Lemma lem1374160 (x : real) : (term10 x) = (term11 x).
Proof. exact (eq_refl (term10 x)). Qed.
Lemma lem1374161 (x : real) : term11 x.
Proof. exact (EQ_MP (@lem1374160 x) (@lem1374159 x)). Qed.
Lemma lem1374162 (x : real) (y : real) : term12 x y.
Proof. exact (@lem1374161 x y). Qed.
Lemma lem1374163 (y : real) (x : real) : (term12 x y) = ((term13 x y) = (real_le y x)).
Proof. exact (eq_refl (term12 x y)). Qed.
Lemma lem1374165 (x : real) : term14 x.
Proof. exact (@lem1374158 x). Qed.
Lemma lem1374166 (x : real) : (term14 x) = (term5 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1374167 (x : real) : term5 x.
Proof. exact (EQ_MP (@lem1374166 x) (@lem1374165 x)). Qed.
Lemma lem1374168 (x : real) (y : real) : term15 x y.
Proof. exact (@lem1374167 x y). Qed.
Lemma lem1374169 (x : real) (y : real) : (term15 x y) = ((term1 x y) = (term0 x y)).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem1374171 (x : real) : term16 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1374172 (x : real) : (term16 x) = (term17 x).
Proof. exact (eq_refl (term16 x)). Qed.
Lemma lem1374173 (x : real) : term17 x.
Proof. exact (EQ_MP (@lem1374172 x) (@lem1374171 x)). Qed.
Lemma lem1374174 (x : real) (y : real) : term18 x y.
Proof. exact (@lem1374173 x y). Qed.
Lemma lem1374175 (x : real) (y : real) : (term18 x y) = ((real_sub x y) = (term19 x y)).
Proof. exact (eq_refl (term18 x y)). Qed.
Lemma lem1374188 (x : real) (y : real) : (real_sub x y) = (term19 x y).
Proof. exact (EQ_MP (@lem1374175 x y) (@lem1374174 x y)). Qed.
Lemma lem1374189 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem1374190 (x : real) (y : real) : (term21 x y) = (term22 x y).
Proof. exact (MK_COMB (@lem1374189) (@lem1374188 x y)). Qed.
Lemma lem1374192 (x : real) (y : real) : (term1 x y) = (term0 x y).
Proof. exact (EQ_MP (@lem1374169 x y) (@lem1374168 x y)). Qed.
Lemma lem1374193 (x : real) (y : real) : (term22 x y) = (term13 x y).
Proof. exact (@lem1374192 x (real_neg y)). Qed.
Lemma lem1374195 (y : real) (x : real) : (term13 x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1374163 y x) (@lem1374162 x y)). Qed.
Lemma lem1374196 (y : real) (x : real) : (term22 x y) = (real_le y x).
Proof. exact (TRANS (@lem1374193 x y) (@lem1374195 y x)). Qed.
Lemma lem1374197 (y : real) (x : real) : (term21 x y) = (real_le y x).
Proof. exact (TRANS (@lem1374190 x y) (@lem1374196 y x)). Qed.
Lemma lem1374198 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1374199 (y : real) (x : real) : (term23 x y) = (term24 y x).
Proof. exact (MK_COMB (@lem1374198) (@lem1374197 y x)). Qed.
Lemma lem1374200 (y : real) (x : real) : (real_le y x) = (real_le y x).
Proof. exact (eq_refl (real_le y x)). Qed.
Lemma lem1374201 (y : real) (x : real) : ((term21 x y) = (real_le y x)) = ((real_le y x) = (real_le y x)).
Proof. exact (MK_COMB (@lem1374199 y x) (@lem1374200 y x)). Qed.
Lemma lem1374203 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1374204 (x : Prop) : (x = x) = True.
Proof. exact (@lem1374203 Prop x). Qed.
Lemma lem1374205 (y : real) (x : real) : ((real_le y x) = (real_le y x)) = True.
Proof. exact (@lem1374204 (real_le y x)). Qed.
Lemma lem1374206 (y : real) (x : real) : ((term21 x y) = (real_le y x)) = True.
Proof. exact (TRANS (@lem1374201 y x) (@lem1374205 y x)). Qed.
Lemma lem1374207 (x : real) : (term25 x) = term26.
Proof. exact (fun_ext (fun y : real => @lem1374206 y x)). Qed.
Lemma lem1374208 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374209 (x : real) : (term27 x) = term28.
Proof. exact (MK_COMB (@lem1374208) (@lem1374207 x)). Qed.
Lemma lem1374211 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1374212 (t : Prop) : (term30 t) = t.
Proof. exact (@lem1374211 real t). Qed.
Lemma lem1374213 : term28 = True.
Proof. exact (@lem1374212 True). Qed.
Lemma lem1374214 (x : real) : (term27 x) = True.
Proof. exact (TRANS (@lem1374209 x) (@lem1374213)). Qed.
Lemma lem1374215 : term31 = term26.
Proof. exact (fun_ext (fun x : real => @lem1374214 x)). Qed.
Lemma lem1374216 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374217 : term32 = term28.
Proof. exact (MK_COMB (@lem1374216) (@lem1374215)). Qed.
Lemma lem1374219 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1374220 (t : Prop) : (term30 t) = t.
Proof. exact (@lem1374219 real t). Qed.
Lemma lem1374221 : term28 = True.
Proof. exact (@lem1374220 True). Qed.
Lemma lem1374222 : term32 = True.
Proof. exact (TRANS (@lem1374217) (@lem1374221)). Qed.
Lemma lem1374223 : True = term32.
Proof. exact (SYM (@lem1374222)). Qed.
Lemma lem1374224 : term32.
Proof. exact (EQ_MP (@lem1374223) (@lem0)). Qed.
