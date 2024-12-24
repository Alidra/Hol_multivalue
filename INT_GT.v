Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_GT_term_abbrevs.
Require Import int_gt_spec.
Require Import int_lt_spec.
Require Import real_gt_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem2318244 (y : real) : term0 y.
Proof. exact (@lem1342768 y). Qed.
Lemma lem2318245 (y : real) : (term0 y) = (term1 y).
Proof. exact (eq_refl (term0 y)). Qed.
Lemma lem2318246 (y : real) : term1 y.
Proof. exact (EQ_MP (@lem2318245 y) (@lem2318244 y)). Qed.
Lemma lem2318247 (y : real) (x : real) : term2 y x.
Proof. exact (@lem2318246 y x). Qed.
Lemma lem2318248 (y : real) (x : real) : (term2 y x) = ((real_gt x y) = (real_lt y x)).
Proof. exact (eq_refl (term2 y x)). Qed.
Lemma lem2318250 (x : int) : term3 x.
Proof. exact (@lem2269769 x). Qed.
Lemma lem2318251 (x : int) : (term3 x) = (term4 x).
Proof. exact (eq_refl (term3 x)). Qed.
Lemma lem2318252 (x : int) : term4 x.
Proof. exact (EQ_MP (@lem2318251 x) (@lem2318250 x)). Qed.
Lemma lem2318253 (x : int) (y : int) : term5 x y.
Proof. exact (@lem2318252 x y). Qed.
Lemma lem2318254 (x : int) (y : int) : (term5 x y) = ((int_lt x y) = (term6 x y)).
Proof. exact (eq_refl (term5 x y)). Qed.
Lemma lem2318256 (x : int) : term7 x.
Proof. exact (@lem2271143 x). Qed.
Lemma lem2318257 (x : int) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem2318258 (x : int) : term8 x.
Proof. exact (EQ_MP (@lem2318257 x) (@lem2318256 x)). Qed.
Lemma lem2318259 (x : int) (y : int) : term9 x y.
Proof. exact (@lem2318258 x y). Qed.
Lemma lem2318260 (x : int) (y : int) : (term9 x y) = ((int_gt x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem2318273 (x : int) (y : int) : (int_gt x y) = (term10 x y).
Proof. exact (EQ_MP (@lem2318260 x y) (@lem2318259 x y)). Qed.
Lemma lem2318275 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem2318248 y x) (@lem2318247 y x)). Qed.
Lemma lem2318276 (y : int) (x : int) : (term10 x y) = (term6 y x).
Proof. exact (@lem2318275 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2318277 (y : int) (x : int) : (int_gt x y) = (term6 y x).
Proof. exact (TRANS (@lem2318273 x y) (@lem2318276 y x)). Qed.
Lemma lem2318278 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2318279 (y : int) (x : int) : (term11 x y) = (term12 y x).
Proof. exact (MK_COMB (@lem2318278) (@lem2318277 y x)). Qed.
Lemma lem2318281 (x : int) (y : int) : (int_lt x y) = (term6 x y).
Proof. exact (EQ_MP (@lem2318254 x y) (@lem2318253 x y)). Qed.
Lemma lem2318282 (y : int) (x : int) : (int_lt y x) = (term6 y x).
Proof. exact (@lem2318281 y x). Qed.
Lemma lem2318283 (y : int) (x : int) : ((int_gt x y) = (int_lt y x)) = ((term6 y x) = (term6 y x)).
Proof. exact (MK_COMB (@lem2318279 y x) (@lem2318282 y x)). Qed.
Lemma lem2318285 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2318286 (x : Prop) : (x = x) = True.
Proof. exact (@lem2318285 Prop x). Qed.
Lemma lem2318287 (y : int) (x : int) : ((term6 y x) = (term6 y x)) = True.
Proof. exact (@lem2318286 (term6 y x)). Qed.
Lemma lem2318288 (y : int) (x : int) : ((int_gt x y) = (int_lt y x)) = True.
Proof. exact (TRANS (@lem2318283 y x) (@lem2318287 y x)). Qed.
Lemma lem2318289 (x : int) : (term13 x) = term14.
Proof. exact (fun_ext (fun y : int => @lem2318288 y x)). Qed.
Lemma lem2318290 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2318291 (x : int) : (term15 x) = term16.
Proof. exact (MK_COMB (@lem2318290) (@lem2318289 x)). Qed.
Lemma lem2318293 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2318294 (t : Prop) : (term18 t) = t.
Proof. exact (@lem2318293 int t). Qed.
Lemma lem2318295 : term16 = True.
Proof. exact (@lem2318294 True). Qed.
Lemma lem2318296 (x : int) : (term15 x) = True.
Proof. exact (TRANS (@lem2318291 x) (@lem2318295)). Qed.
Lemma lem2318297 : term19 = term14.
Proof. exact (fun_ext (fun x : int => @lem2318296 x)). Qed.
Lemma lem2318298 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2318299 : term20 = term16.
Proof. exact (MK_COMB (@lem2318298) (@lem2318297)). Qed.
Lemma lem2318301 {A : Type'} (t : Prop) : (term17 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2318302 (t : Prop) : (term18 t) = t.
Proof. exact (@lem2318301 int t). Qed.
Lemma lem2318303 : term16 = True.
Proof. exact (@lem2318302 True). Qed.
Lemma lem2318304 : term20 = True.
Proof. exact (TRANS (@lem2318299) (@lem2318303)). Qed.
Lemma lem2318305 : True = term20.
Proof. exact (SYM (@lem2318304)). Qed.
Lemma lem2318306 : term20.
Proof. exact (EQ_MP (@lem2318305) (@lem0)). Qed.
