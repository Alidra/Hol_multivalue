Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_NEG_SUB_term_abbrevs.
Require Import REAL_ADD_AC_spec.
Require Import REAL_NEG_ADD_spec.
Require Import REAL_NEG_NEG_spec.
Require Import real_sub_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1374229 (x : real) : term0 x.
Proof. exact (@lem1358662 x). Qed.
Lemma lem1374230 (x : real) : (term0 x) = ((term1 x) = x).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1374232 (x : real) : term2 x.
Proof. exact (@lem1361095 x). Qed.
Lemma lem1374233 (x : real) : (term2 x) = (term3 x).
Proof. exact (eq_refl (term2 x)). Qed.
Lemma lem1374234 (x : real) : term3 x.
Proof. exact (EQ_MP (@lem1374233 x) (@lem1374232 x)). Qed.
Lemma lem1374235 (x : real) (y : real) : term4 x y.
Proof. exact (@lem1374234 x y). Qed.
Lemma lem1374236 (x : real) (y : real) : (term4 x y) = ((term5 x y) = (term6 x y)).
Proof. exact (eq_refl (term4 x y)). Qed.
Lemma lem1374238 (x : real) : term7 x.
Proof. exact (@lem1340977 x). Qed.
Lemma lem1374239 (x : real) : (term7 x) = (term8 x).
Proof. exact (eq_refl (term7 x)). Qed.
Lemma lem1374240 (x : real) : term8 x.
Proof. exact (EQ_MP (@lem1374239 x) (@lem1374238 x)). Qed.
Lemma lem1374241 (x : real) (y : real) : term9 x y.
Proof. exact (@lem1374240 x y). Qed.
Lemma lem1374242 (x : real) (y : real) : (term9 x y) = ((real_sub x y) = (term10 x y)).
Proof. exact (eq_refl (term9 x y)). Qed.
Lemma lem1374255 (x : real) (y : real) : (real_sub x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1374242 x y) (@lem1374241 x y)). Qed.
Lemma lem1374256 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem1374257 (x : real) (y : real) : (term11 x y) = (term12 x y).
Proof. exact (MK_COMB (@lem1374256) (@lem1374255 x y)). Qed.
Lemma lem1374259 (x : real) (y : real) : (term5 x y) = (term6 x y).
Proof. exact (EQ_MP (@lem1374236 x y) (@lem1374235 x y)). Qed.
Lemma lem1374260 (x : real) (y : real) : (term12 x y) = (term13 x y).
Proof. exact (@lem1374259 x (real_neg y)). Qed.
Lemma lem1374262 (x : real) : (term1 x) = x.
Proof. exact (EQ_MP (@lem1374230 x) (@lem1374229 x)). Qed.
Lemma lem1374263 (y : real) : (term1 y) = y.
Proof. exact (@lem1374262 y). Qed.
Lemma lem1374264 (x : real) : (term14 x) = (term14 x).
Proof. exact (eq_refl (term14 x)). Qed.
Lemma lem1374265 (x : real) (y : real) : (term13 x y) = (term15 x y).
Proof. exact (MK_COMB (@lem1374264 x) (@lem1374263 y)). Qed.
Lemma lem1374266 (x : real) (y : real) : (term12 x y) = (term15 x y).
Proof. exact (TRANS (@lem1374260 x y) (@lem1374265 x y)). Qed.
Lemma lem1374267 (x : real) (y : real) : (term11 x y) = (term15 x y).
Proof. exact (TRANS (@lem1374257 x y) (@lem1374266 x y)). Qed.
Lemma lem1374268 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1374269 (x : real) (y : real) : (term16 x y) = (term17 x y).
Proof. exact (MK_COMB (@lem1374268) (@lem1374267 x y)). Qed.
Lemma lem1374271 (x : real) (y : real) : (real_sub x y) = (term10 x y).
Proof. exact (EQ_MP (@lem1374242 x y) (@lem1374241 x y)). Qed.
Lemma lem1374272 (y : real) (x : real) : (real_sub y x) = (term10 y x).
Proof. exact (@lem1374271 y x). Qed.
Lemma lem1374273 (y : real) (x : real) : ((term11 x y) = (real_sub y x)) = ((term15 x y) = (term10 y x)).
Proof. exact (MK_COMB (@lem1374269 x y) (@lem1374272 y x)). Qed.
Lemma lem1374276 (x : real) : (term18 x) = (term19 x).
Proof. exact (fun_ext (fun y : real => @lem1374273 y x)). Qed.
Lemma lem1374277 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374278 (x : real) : (term20 x) = (term21 x).
Proof. exact (MK_COMB (@lem1374277) (@lem1374276 x)). Qed.
Lemma lem1374283 : term22 = term23.
Proof. exact (fun_ext (fun x : real => @lem1374278 x)). Qed.
Lemma lem1374284 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374285 : term24 = term25.
Proof. exact (MK_COMB (@lem1374284) (@lem1374283)). Qed.
Lemma lem1374290 : term25 = term24.
Proof. exact (SYM (@lem1374285)). Qed.
Lemma lem1374302 (n : real) (m : real) : (real_add m n) = (real_add n m).
Proof. exact (proj1 (@lem1352530 n m (@el real))). Qed.
Lemma lem1374303 (y : real) (x : real) : (term15 x y) = (term10 y x).
Proof. exact (@lem1374302 y (real_neg x)). Qed.
Lemma lem1374307 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1374308 (y : real) (x : real) : (term17 x y) = (term26 y x).
Proof. exact (MK_COMB (@lem1374307) (@lem1374303 y x)). Qed.
Lemma lem1374312 (y : real) (x : real) : (term10 y x) = (term10 y x).
Proof. exact (eq_refl (term10 y x)). Qed.
Lemma lem1374313 (y : real) (x : real) : ((term15 x y) = (term10 y x)) = ((term10 y x) = (term10 y x)).
Proof. exact (MK_COMB (@lem1374308 y x) (@lem1374312 y x)). Qed.
Lemma lem1374315 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1374316 (x : real) : (x = x) = True.
Proof. exact (@lem1374315 real x). Qed.
Lemma lem1374317 (y : real) (x : real) : ((term10 y x) = (term10 y x)) = True.
Proof. exact (@lem1374316 (term10 y x)). Qed.
Lemma lem1374318 (y : real) (x : real) : ((term15 x y) = (term10 y x)) = True.
Proof. exact (TRANS (@lem1374313 y x) (@lem1374317 y x)). Qed.
Lemma lem1374319 (x : real) : (term19 x) = term27.
Proof. exact (fun_ext (fun y : real => @lem1374318 y x)). Qed.
Lemma lem1374320 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374321 (x : real) : (term21 x) = term28.
Proof. exact (MK_COMB (@lem1374320) (@lem1374319 x)). Qed.
Lemma lem1374323 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1374324 (t : Prop) : (term30 t) = t.
Proof. exact (@lem1374323 real t). Qed.
Lemma lem1374325 : term28 = True.
Proof. exact (@lem1374324 True). Qed.
Lemma lem1374326 (x : real) : (term21 x) = True.
Proof. exact (TRANS (@lem1374321 x) (@lem1374325)). Qed.
Lemma lem1374327 : term23 = term27.
Proof. exact (fun_ext (fun x : real => @lem1374326 x)). Qed.
Lemma lem1374328 : (@all real) = (@all real).
Proof. exact (eq_refl (@all real)). Qed.
Lemma lem1374329 : term25 = term28.
Proof. exact (MK_COMB (@lem1374328) (@lem1374327)). Qed.
Lemma lem1374331 {A : Type'} (t : Prop) : (term29 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1374332 (t : Prop) : (term30 t) = t.
Proof. exact (@lem1374331 real t). Qed.
Lemma lem1374333 : term28 = True.
Proof. exact (@lem1374332 True). Qed.
Lemma lem1374334 : term25 = True.
Proof. exact (TRANS (@lem1374329) (@lem1374333)). Qed.
Lemma lem1374335 : True = term25.
Proof. exact (SYM (@lem1374334)). Qed.
Lemma lem1374336 : term25.
Proof. exact (EQ_MP (@lem1374335) (@lem0)). Qed.
Lemma lem1374337 : term24.
Proof. exact (EQ_MP (@lem1374290) (@lem1374336)). Qed.
