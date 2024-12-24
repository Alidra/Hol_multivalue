Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_SHRINK_LE_term_abbrevs.
Require Import REAL_NOT_LT_spec.
Require Import REAL_SHRINK_LT_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2227225 (y : real) (x : real) (h1 : (term0 x y) = (real_le y x)) : (term0 x y) = (real_le y x).
Proof. exact (h1). Qed.
Lemma lem2227226 (y : real) (x : real) (h1 : (term0 x y) = (real_le y x)) : (real_le y x) = (term0 x y).
Proof. exact (SYM (@lem2227225 y x h1)). Qed.
Lemma lem2227227 (x : real) (y : real) (h1 : (real_le y x) = (term0 x y)) : (real_le y x) = (term0 x y).
Proof. exact (h1). Qed.
Lemma lem2227228 (x : real) (y : real) (h1 : (real_le y x) = (term0 x y)) : (term0 x y) = (real_le y x).
Proof. exact (SYM (@lem2227227 x y h1)). Qed.
Lemma lem2227229 (x : real) (y : real) : ((term0 x y) = (real_le y x)) = ((real_le y x) = (term0 x y)).
Proof. exact (prop_ext (fun h1 : (term0 x y) = (real_le y x) => @lem2227226 y x h1) (fun h1 : (real_le y x) = (term0 x y) => @lem2227228 x y h1)). Qed.
Lemma lem2227230 (x : real) : (term1 x) = (term2 x).
Proof. exact (fun_ext (fun y : real => @lem2227229 x y)). Qed.
Lemma lem2227231 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227232 (x : real) : (term3 x) = (term4 x).
Proof. exact (MK_COMB (@lem2227231) (@lem2227230 x)). Qed.
Lemma lem2227233 : term5 = term6.
Proof. exact (fun_ext (fun x : real => @lem2227232 x)). Qed.
Lemma lem2227234 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227235 : term7 = term8.
Proof. exact (MK_COMB (@lem2227234) (@lem2227233)). Qed.
Lemma lem2227236 : term8.
Proof. exact (EQ_MP (@lem2227235) (@lem1376537)). Qed.
Lemma lem2227237 (x : real) : term9 x.
Proof. exact (@lem2227222 x). Qed.
Lemma lem2227238 (x : real) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2227239 (x : real) : term10 x.
Proof. exact (EQ_MP (@lem2227238 x) (@lem2227237 x)). Qed.
Lemma lem2227240 (x : real) (y : real) : term11 x y.
Proof. exact (@lem2227239 x y). Qed.
Lemma lem2227241 (x : real) (y : real) : (term11 x y) = ((term12 x y) = (real_lt x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem2227243 (x : real) : term13 x.
Proof. exact (@lem2227236 x). Qed.
Lemma lem2227244 (x : real) : (term13 x) = (term4 x).
Proof. exact (eq_refl (term13 x)). Qed.
Lemma lem2227245 (x : real) : term4 x.
Proof. exact (EQ_MP (@lem2227244 x) (@lem2227243 x)). Qed.
Lemma lem2227246 (x : real) (y : real) : term14 x y.
Proof. exact (@lem2227245 x y). Qed.
Lemma lem2227247 (x : real) (y : real) : (term14 x y) = ((real_le y x) = (term0 x y)).
Proof. exact (eq_refl (term14 x y)). Qed.
Lemma lem2227260 (x : real) (y : real) : (real_le y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2227247 x y) (@lem2227246 x y)). Qed.
Lemma lem2227261 (y : real) (x : real) : (term15 x y) = (term16 y x).
Proof. exact (@lem2227260 (term17 y) (term17 x)). Qed.
Lemma lem2227263 (x : real) (y : real) : (term12 x y) = (real_lt x y).
Proof. exact (EQ_MP (@lem2227241 x y) (@lem2227240 x y)). Qed.
Lemma lem2227264 (y : real) (x : real) : (term12 y x) = (real_lt y x).
Proof. exact (@lem2227263 y x). Qed.
Lemma lem2227265 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2227266 (y : real) (x : real) : (term16 y x) = (term0 y x).
Proof. exact (MK_COMB (@lem2227265) (@lem2227264 y x)). Qed.
Lemma lem2227267 (y : real) (x : real) : (term15 x y) = (term0 y x).
Proof. exact (TRANS (@lem2227261 y x) (@lem2227266 y x)). Qed.
Lemma lem2227268 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2227269 (y : real) (x : real) : (term18 x y) = (term19 y x).
Proof. exact (MK_COMB (@lem2227268) (@lem2227267 y x)). Qed.
Lemma lem2227271 (x : real) (y : real) : (real_le y x) = (term0 x y).
Proof. exact (EQ_MP (@lem2227247 x y) (@lem2227246 x y)). Qed.
Lemma lem2227272 (y : real) (x : real) : (real_le x y) = (term0 y x).
Proof. exact (@lem2227271 y x). Qed.
Lemma lem2227273 (y : real) (x : real) : ((term15 x y) = (real_le x y)) = ((term0 y x) = (term0 y x)).
Proof. exact (MK_COMB (@lem2227269 y x) (@lem2227272 y x)). Qed.
Lemma lem2227275 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2227276 (x : Prop) : (x = x) = True.
Proof. exact (@lem2227275 Prop x). Qed.
Lemma lem2227277 (y : real) (x : real) : ((term0 y x) = (term0 y x)) = True.
Proof. exact (@lem2227276 (term0 y x)). Qed.
Lemma lem2227278 (x : real) (y : real) : ((term15 x y) = (real_le x y)) = True.
Proof. exact (TRANS (@lem2227273 y x) (@lem2227277 y x)). Qed.
Lemma lem2227279 (x : real) : (term20 x) = term21.
Proof. exact (fun_ext (fun y : real => @lem2227278 x y)). Qed.
Lemma lem2227280 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227281 (x : real) : (term22 x) = term23.
Proof. exact (MK_COMB (@lem2227280) (@lem2227279 x)). Qed.
Lemma lem2227283 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2227284 (t : Prop) : (term25 t) = t.
Proof. exact (@lem2227283 real t). Qed.
Lemma lem2227285 : term23 = True.
Proof. exact (@lem2227284 True). Qed.
Lemma lem2227286 (x : real) : (term22 x) = True.
Proof. exact (TRANS (@lem2227281 x) (@lem2227285)). Qed.
Lemma lem2227287 : term26 = term21.
Proof. exact (fun_ext (fun x : real => @lem2227286 x)). Qed.
Lemma lem2227288 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem2227289 : term27 = term23.
Proof. exact (MK_COMB (@lem2227288) (@lem2227287)). Qed.
Lemma lem2227291 {A : Type'} (t : Prop) : (term24 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2227292 (t : Prop) : (term25 t) = t.
Proof. exact (@lem2227291 real t). Qed.
Lemma lem2227293 : term23 = True.
Proof. exact (@lem2227292 True). Qed.
Lemma lem2227294 : term27 = True.
Proof. exact (TRANS (@lem2227289) (@lem2227293)). Qed.
Lemma lem2227295 : True = term27.
Proof. exact (SYM (@lem2227294)). Qed.
Lemma lem2227296 : term27.
Proof. exact (EQ_MP (@lem2227295) (@lem0)). Qed.
