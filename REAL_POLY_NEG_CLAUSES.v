Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POLY_NEG_CLAUSES_term_abbrevs.
Require Import REAL_MUL_LNEG_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1338986_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1384211 (x : real) : term0 x.
Proof. exact (@lem1338986 x). Qed.
Lemma lem1384212 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1384214 (x : real) : term2 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1384215 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1384216 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1384215 x) (@lem1384214 x)). Qed.
Lemma lem1384217 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1384216 x y). Qed.
Lemma lem1384218 (x : real) (y : real) : (term4 x y) = ((real_sub x y) = (term5 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1384220 (x : real) : term6 x.
Proof. exact (@lem1360913 x). Qed.
Lemma lem1384221 (x : real) : (term6 x) = (term7 x).
Proof. exact (eq_refl (term6 x)). Qed.
Lemma lem1384222 (x : real) : term7 x.
Proof. exact (EQ_MP (@lem1384221 x) (@lem1384220 x)). Qed.
Lemma lem1384223 (x : real) (y : real) : term8 x y.
Proof. exact (@lem1384222 x y). Qed.
Lemma lem1384224 (x : real) (y : real) : (term8 x y) = ((term9 x y) = (term10 x y)).
Proof. exact (eq_refl (term8 x y)). Qed.
Lemma lem1384235 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1384224 x y) (@lem1384223 x y)). Qed.
Lemma lem1384236 (x : real) : (term11 x) = (term12 x).
Proof. exact (@lem1384235 term13 x). Qed.
Lemma lem1384238 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1384212 x) (@lem1384211 x)). Qed.
Lemma lem1384239 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1384240 (x : real) : (term12 x) = (real_neg x).
Proof. exact (MK_COMB (@lem1384239) (@lem1384238 x)). Qed.
Lemma lem1384241 (x : real) : (term11 x) = (real_neg x).
Proof. exact (TRANS (@lem1384236 x) (@lem1384240 x)). Qed.
Lemma lem1384242 (x : real) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1384243 (x : real) : ((real_neg x) = (term11 x)) = ((real_neg x) = (real_neg x)).
Proof. exact (MK_COMB (@lem1384242 x) (@lem1384241 x)). Qed.
Lemma lem1384245 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384246 (x : real) : (x = x) = True.
Proof. exact (@lem1384245 real x). Qed.
Lemma lem1384247 (x : real) : ((real_neg x) = (real_neg x)) = True.
Proof. exact (@lem1384246 (real_neg x)). Qed.
Lemma lem1384248 (x : real) : ((real_neg x) = (term11 x)) = True.
Proof. exact (TRANS (@lem1384243 x) (@lem1384247 x)). Qed.
Lemma lem1384249 : term15 = term16.
Proof. exact (fun_ext (fun x : real => @lem1384248 x)). Qed.
Lemma lem1384250 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384251 : term17 = term18.
Proof. exact (MK_COMB (@lem1384250) (@lem1384249)). Qed.
Lemma lem1384253 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384254 (t : Prop) : (term20 t) = t.
Proof. exact (@lem1384253 real t). Qed.
Lemma lem1384255 : term18 = True.
Proof. exact (@lem1384254 True). Qed.
Lemma lem1384256 : term17 = True.
Proof. exact (TRANS (@lem1384251) (@lem1384255)). Qed.
Lemma lem1384257 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1384258 : term21 = (and True).
Proof. exact (MK_COMB (@lem1384257) (@lem1384256)). Qed.
Lemma lem1384270 (x : real) (y : real) : (real_sub x y) = (term5 x y).
Proof. exact (EQ_MP (@lem1384218 x y) (@lem1384217 x y)). Qed.
Lemma lem1384271 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1384272 (x : real) (y : real) : (term22 x y) = (term23 x y).
Proof. exact (MK_COMB (@lem1384271) (@lem1384270 x y)). Qed.
Lemma lem1384274 (x : real) (y : real) : (term9 x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1384224 x y) (@lem1384223 x y)). Qed.
Lemma lem1384275 (y : real) : (term11 y) = (term12 y).
Proof. exact (@lem1384274 term13 y). Qed.
Lemma lem1384277 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1384212 x) (@lem1384211 x)). Qed.
Lemma lem1384278 (y : real) : (term1 y) = y.
Proof. exact (@lem1384277 y). Qed.
Lemma lem1384279 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1384280 (y : real) : (term12 y) = (real_neg y).
Proof. exact (MK_COMB (@lem1384279) (@lem1384278 y)). Qed.
Lemma lem1384281 (y : real) : (term11 y) = (real_neg y).
Proof. exact (TRANS (@lem1384275 y) (@lem1384280 y)). Qed.
Lemma lem1384282 (x : real) : (real_add x) = (real_add x).
Proof. exact (eq_refl (real_add x)). Qed.
Lemma lem1384283 (x : real) (y : real) : (term24 x y) = (term5 x y).
Proof. exact (MK_COMB (@lem1384282 x) (@lem1384281 y)). Qed.
Lemma lem1384284 (x : real) (y : real) : ((real_sub x y) = (term24 x y)) = ((term5 x y) = (term5 x y)).
Proof. exact (MK_COMB (@lem1384272 x y) (@lem1384283 x y)). Qed.
Lemma lem1384286 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1384287 (x : real) : (x = x) = True.
Proof. exact (@lem1384286 real x). Qed.
Lemma lem1384288 (x : real) (y : real) : ((term5 x y) = (term5 x y)) = True.
Proof. exact (@lem1384287 (term5 x y)). Qed.
Lemma lem1384289 (x : real) (y : real) : ((real_sub x y) = (term24 x y)) = True.
Proof. exact (TRANS (@lem1384284 x y) (@lem1384288 x y)). Qed.
Lemma lem1384290 (x : real) : (term25 x) = term16.
Proof. exact (fun_ext (fun y : real => @lem1384289 x y)). Qed.
Lemma lem1384291 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384292 (x : real) : (term26 x) = term18.
Proof. exact (MK_COMB (@lem1384291) (@lem1384290 x)). Qed.
Lemma lem1384294 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384295 (t : Prop) : (term20 t) = t.
Proof. exact (@lem1384294 real t). Qed.
Lemma lem1384296 : term18 = True.
Proof. exact (@lem1384295 True). Qed.
Lemma lem1384297 (x : real) : (term26 x) = True.
Proof. exact (TRANS (@lem1384292 x) (@lem1384296)). Qed.
Lemma lem1384298 : term27 = term16.
Proof. exact (fun_ext (fun x : real => @lem1384297 x)). Qed.
Lemma lem1384299 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1384300 : term28 = term18.
Proof. exact (MK_COMB (@lem1384299) (@lem1384298)). Qed.
Lemma lem1384302 {A : Type'} (t : Prop) : (term19 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1384303 (t : Prop) : (term20 t) = t.
Proof. exact (@lem1384302 real t). Qed.
Lemma lem1384304 : term18 = True.
Proof. exact (@lem1384303 True). Qed.
Lemma lem1384305 : term28 = True.
Proof. exact (TRANS (@lem1384300) (@lem1384304)). Qed.
Lemma lem1384306 : term29 = (True /\ True).
Proof. exact (MK_COMB (@lem1384258) (@lem1384305)). Qed.
Lemma lem1384308 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1384309 : (True /\ True) = True.
Proof. exact (@lem1384308 True). Qed.
Lemma lem1384310 : term29 = True.
Proof. exact (TRANS (@lem1384306) (@lem1384309)). Qed.
Lemma lem1384311 : True = term29.
Proof. exact (SYM (@lem1384310)). Qed.
Lemma lem1384312 : term29.
Proof. exact (EQ_MP (@lem1384311) (@lem0)). Qed.
