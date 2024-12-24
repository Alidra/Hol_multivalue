Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import BIJECTIONS_HAS_SIZE_EQ_term_abbrevs.
Require Import BIJECTIONS_HAS_SIZE_spec.
Require Import BOOL_CASES_AX_spec.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm32_spec.
Lemma lem5096207 (a : Prop) : term0 a.
Proof. exact (@lem9851 a). Qed.
Lemma lem5096208 (a : Prop) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem5096209 (a : Prop) : term1 a.
Proof. exact (EQ_MP (@lem5096208 a) (@lem5096207 a)). Qed.
Lemma lem5096210 (a : Prop) (h1 : a = True) : a = True.
Proof. exact (h1). Qed.
Lemma lem5096211 (a : Prop) (h1 : a = False) : a = False.
Proof. exact (h1). Qed.
Lemma lem5096228 (b : Prop) (c : Prop) (d : Prop) : (term2 b c d) = (term2 b c d).
Proof. exact (eq_refl (term2 b c d)). Qed.
Lemma lem5096229 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : (term3 b c d a) = (term4 b c d).
Proof. exact (MK_COMB (@lem5096228 b c d) (@lem5096210 a h1)). Qed.
Lemma lem5096230 (b : Prop) (c : Prop) (d : Prop) : (term4 b c d) = ((term5 b c d) = (term6 b c d)).
Proof. exact (eq_refl (term4 b c d)). Qed.
Lemma lem5096231 (b : Prop) (c : Prop) (d : Prop) (a : Prop) : (term7 b c d a) = (term7 b c d a).
Proof. exact (eq_refl (term7 b c d a)). Qed.
Lemma lem5096232 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term3 b c d a) = (term4 b c d)) = ((term3 b c d a) = ((term5 b c d) = (term6 b c d))).
Proof. exact (MK_COMB (@lem5096231 b c d a) (@lem5096230 b c d)). Qed.
Lemma lem5096233 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term3 b c d a) = ((term8 a b c d) = (term9 a b c d)).
Proof. exact (eq_refl (term3 b c d a)). Qed.
Lemma lem5096234 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096235 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term7 b c d a) = (term10 a b c d).
Proof. exact (MK_COMB (@lem5096234) (@lem5096233 a b c d)). Qed.
Lemma lem5096236 (b : Prop) (c : Prop) (d : Prop) : ((term5 b c d) = (term6 b c d)) = ((term5 b c d) = (term6 b c d)).
Proof. exact (eq_refl ((term5 b c d) = (term6 b c d))). Qed.
Lemma lem5096237 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term3 b c d a) = ((term5 b c d) = (term6 b c d))) = (((term8 a b c d) = (term9 a b c d)) = ((term5 b c d) = (term6 b c d))).
Proof. exact (MK_COMB (@lem5096235 a b c d) (@lem5096236 b c d)). Qed.
Lemma lem5096238 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term3 b c d a) = (term4 b c d)) = (((term8 a b c d) = (term9 a b c d)) = ((term5 b c d) = (term6 b c d))).
Proof. exact (TRANS (@lem5096232 a b c d) (@lem5096237 a b c d)). Qed.
Lemma lem5096239 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : ((term8 a b c d) = (term9 a b c d)) = ((term5 b c d) = (term6 b c d)).
Proof. exact (EQ_MP (@lem5096238 a b c d) (@lem5096229 b c d a h1)). Qed.
Lemma lem5096240 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : ((term5 b c d) = (term6 b c d)) = ((term8 a b c d) = (term9 a b c d)).
Proof. exact (SYM (@lem5096239 b c d a h1)). Qed.
Lemma lem5096241 (b : Prop) (c : Prop) (d : Prop) : (term2 b c d) = (term2 b c d).
Proof. exact (eq_refl (term2 b c d)). Qed.
Lemma lem5096242 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : (term3 b c d a) = (term11 b c d).
Proof. exact (MK_COMB (@lem5096241 b c d) (@lem5096211 a h1)). Qed.
Lemma lem5096243 (b : Prop) (c : Prop) (d : Prop) : (term11 b c d) = ((term12 b c d) = (term13 b c d)).
Proof. exact (eq_refl (term11 b c d)). Qed.
Lemma lem5096244 (b : Prop) (c : Prop) (d : Prop) (a : Prop) : (term7 b c d a) = (term7 b c d a).
Proof. exact (eq_refl (term7 b c d a)). Qed.
Lemma lem5096245 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term3 b c d a) = (term11 b c d)) = ((term3 b c d a) = ((term12 b c d) = (term13 b c d))).
Proof. exact (MK_COMB (@lem5096244 b c d a) (@lem5096243 b c d)). Qed.
Lemma lem5096246 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term3 b c d a) = ((term8 a b c d) = (term9 a b c d)).
Proof. exact (eq_refl (term3 b c d a)). Qed.
Lemma lem5096247 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096248 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term7 b c d a) = (term10 a b c d).
Proof. exact (MK_COMB (@lem5096247) (@lem5096246 a b c d)). Qed.
Lemma lem5096249 (b : Prop) (c : Prop) (d : Prop) : ((term12 b c d) = (term13 b c d)) = ((term12 b c d) = (term13 b c d)).
Proof. exact (eq_refl ((term12 b c d) = (term13 b c d))). Qed.
Lemma lem5096250 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term3 b c d a) = ((term12 b c d) = (term13 b c d))) = (((term8 a b c d) = (term9 a b c d)) = ((term12 b c d) = (term13 b c d))).
Proof. exact (MK_COMB (@lem5096248 a b c d) (@lem5096249 b c d)). Qed.
Lemma lem5096251 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : ((term3 b c d a) = (term11 b c d)) = (((term8 a b c d) = (term9 a b c d)) = ((term12 b c d) = (term13 b c d))).
Proof. exact (TRANS (@lem5096245 a b c d) (@lem5096250 a b c d)). Qed.
Lemma lem5096252 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : ((term8 a b c d) = (term9 a b c d)) = ((term12 b c d) = (term13 b c d)).
Proof. exact (EQ_MP (@lem5096251 a b c d) (@lem5096242 b c d a h1)). Qed.
Lemma lem5096253 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : ((term12 b c d) = (term13 b c d)) = ((term8 a b c d) = (term9 a b c d)).
Proof. exact (SYM (@lem5096252 b c d a h1)). Qed.
Lemma lem5096259 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5096260 (b : Prop) (c : Prop) : (term14 b c) = (b /\ c).
Proof. exact (@lem5096259 (b /\ c)). Qed.
Lemma lem5096263 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096264 (b : Prop) (c : Prop) : (term15 b c) = (term16 b c).
Proof. exact (MK_COMB (@lem5096263) (@lem5096260 b c)). Qed.
Lemma lem5096265 (d : Prop) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem5096266 (b : Prop) (c : Prop) (d : Prop) : (term5 b c d) = (term17 b c d).
Proof. exact (MK_COMB (@lem5096264 b c) (@lem5096265 d)). Qed.
Lemma lem5096269 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096270 (b : Prop) (c : Prop) (d : Prop) : (term18 b c d) = (term19 b c d).
Proof. exact (MK_COMB (@lem5096269) (@lem5096266 b c d)). Qed.
Lemma lem5096274 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5096275 (b : Prop) : (True /\ b) = b.
Proof. exact (@lem5096274 b). Qed.
Lemma lem5096276 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096277 (b : Prop) : (term20 b) = (imp b).
Proof. exact (MK_COMB (@lem5096276) (@lem5096275 b)). Qed.
Lemma lem5096280 (c : Prop) (d : Prop) : (c -> d) = (c -> d).
Proof. exact (eq_refl (c -> d)). Qed.
Lemma lem5096281 (b : Prop) (c : Prop) (d : Prop) : (term6 b c d) = (term21 b c d).
Proof. exact (MK_COMB (@lem5096277 b) (@lem5096280 c d)). Qed.
Lemma lem5096284 (b : Prop) (c : Prop) (d : Prop) : ((term5 b c d) = (term6 b c d)) = ((term17 b c d) = (term21 b c d)).
Proof. exact (MK_COMB (@lem5096270 b c d) (@lem5096281 b c d)). Qed.
Lemma lem5096287 (b : Prop) (c : Prop) (d : Prop) : ((term17 b c d) = (term21 b c d)) = ((term5 b c d) = (term6 b c d)).
Proof. exact (SYM (@lem5096284 b c d)). Qed.
Lemma lem5096288 (b : Prop) : term0 b.
Proof. exact (@lem9851 b). Qed.
Lemma lem5096289 (b : Prop) : (term0 b) = (term1 b).
Proof. exact (eq_refl (term0 b)). Qed.
Lemma lem5096290 (b : Prop) : term1 b.
Proof. exact (EQ_MP (@lem5096289 b) (@lem5096288 b)). Qed.
Lemma lem5096291 (b : Prop) (h1 : b = True) : b = True.
Proof. exact (h1). Qed.
Lemma lem5096292 (b : Prop) (h1 : b = False) : b = False.
Proof. exact (h1). Qed.
Lemma lem5096305 (c : Prop) (d : Prop) : (term22 c d) = (term22 c d).
Proof. exact (eq_refl (term22 c d)). Qed.
Lemma lem5096306 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : (term23 c d b) = (term24 c d).
Proof. exact (MK_COMB (@lem5096305 c d) (@lem5096291 b h1)). Qed.
Lemma lem5096307 (c : Prop) (d : Prop) : (term24 c d) = ((term25 c d) = (term26 c d)).
Proof. exact (eq_refl (term24 c d)). Qed.
Lemma lem5096308 (c : Prop) (d : Prop) (b : Prop) : (term27 c d b) = (term27 c d b).
Proof. exact (eq_refl (term27 c d b)). Qed.
Lemma lem5096309 (b : Prop) (c : Prop) (d : Prop) : ((term23 c d b) = (term24 c d)) = ((term23 c d b) = ((term25 c d) = (term26 c d))).
Proof. exact (MK_COMB (@lem5096308 c d b) (@lem5096307 c d)). Qed.
Lemma lem5096310 (b : Prop) (c : Prop) (d : Prop) : (term23 c d b) = ((term17 b c d) = (term21 b c d)).
Proof. exact (eq_refl (term23 c d b)). Qed.
Lemma lem5096311 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096312 (b : Prop) (c : Prop) (d : Prop) : (term27 c d b) = (term28 b c d).
Proof. exact (MK_COMB (@lem5096311) (@lem5096310 b c d)). Qed.
Lemma lem5096313 (c : Prop) (d : Prop) : ((term25 c d) = (term26 c d)) = ((term25 c d) = (term26 c d)).
Proof. exact (eq_refl ((term25 c d) = (term26 c d))). Qed.
Lemma lem5096314 (b : Prop) (c : Prop) (d : Prop) : ((term23 c d b) = ((term25 c d) = (term26 c d))) = (((term17 b c d) = (term21 b c d)) = ((term25 c d) = (term26 c d))).
Proof. exact (MK_COMB (@lem5096312 b c d) (@lem5096313 c d)). Qed.
Lemma lem5096315 (b : Prop) (c : Prop) (d : Prop) : ((term23 c d b) = (term24 c d)) = (((term17 b c d) = (term21 b c d)) = ((term25 c d) = (term26 c d))).
Proof. exact (TRANS (@lem5096309 b c d) (@lem5096314 b c d)). Qed.
Lemma lem5096316 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : ((term17 b c d) = (term21 b c d)) = ((term25 c d) = (term26 c d)).
Proof. exact (EQ_MP (@lem5096315 b c d) (@lem5096306 c d b h1)). Qed.
Lemma lem5096317 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : ((term25 c d) = (term26 c d)) = ((term17 b c d) = (term21 b c d)).
Proof. exact (SYM (@lem5096316 c d b h1)). Qed.
Lemma lem5096318 (c : Prop) (d : Prop) : (term22 c d) = (term22 c d).
Proof. exact (eq_refl (term22 c d)). Qed.
Lemma lem5096319 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : (term23 c d b) = (term29 c d).
Proof. exact (MK_COMB (@lem5096318 c d) (@lem5096292 b h1)). Qed.
Lemma lem5096320 (c : Prop) (d : Prop) : (term29 c d) = ((term30 c d) = (term31 c d)).
Proof. exact (eq_refl (term29 c d)). Qed.
Lemma lem5096321 (c : Prop) (d : Prop) (b : Prop) : (term27 c d b) = (term27 c d b).
Proof. exact (eq_refl (term27 c d b)). Qed.
Lemma lem5096322 (b : Prop) (c : Prop) (d : Prop) : ((term23 c d b) = (term29 c d)) = ((term23 c d b) = ((term30 c d) = (term31 c d))).
Proof. exact (MK_COMB (@lem5096321 c d b) (@lem5096320 c d)). Qed.
Lemma lem5096323 (b : Prop) (c : Prop) (d : Prop) : (term23 c d b) = ((term17 b c d) = (term21 b c d)).
Proof. exact (eq_refl (term23 c d b)). Qed.
Lemma lem5096324 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096325 (b : Prop) (c : Prop) (d : Prop) : (term27 c d b) = (term28 b c d).
Proof. exact (MK_COMB (@lem5096324) (@lem5096323 b c d)). Qed.
Lemma lem5096326 (c : Prop) (d : Prop) : ((term30 c d) = (term31 c d)) = ((term30 c d) = (term31 c d)).
Proof. exact (eq_refl ((term30 c d) = (term31 c d))). Qed.
Lemma lem5096327 (b : Prop) (c : Prop) (d : Prop) : ((term23 c d b) = ((term30 c d) = (term31 c d))) = (((term17 b c d) = (term21 b c d)) = ((term30 c d) = (term31 c d))).
Proof. exact (MK_COMB (@lem5096325 b c d) (@lem5096326 c d)). Qed.
Lemma lem5096328 (b : Prop) (c : Prop) (d : Prop) : ((term23 c d b) = (term29 c d)) = (((term17 b c d) = (term21 b c d)) = ((term30 c d) = (term31 c d))).
Proof. exact (TRANS (@lem5096322 b c d) (@lem5096327 b c d)). Qed.
Lemma lem5096329 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : ((term17 b c d) = (term21 b c d)) = ((term30 c d) = (term31 c d)).
Proof. exact (EQ_MP (@lem5096328 b c d) (@lem5096319 c d b h1)). Qed.
Lemma lem5096330 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : ((term30 c d) = (term31 c d)) = ((term17 b c d) = (term21 b c d)).
Proof. exact (SYM (@lem5096329 c d b h1)). Qed.
Lemma lem5096336 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5096337 (c : Prop) : (True /\ c) = c.
Proof. exact (@lem5096336 c). Qed.
Lemma lem5096338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096339 (c : Prop) : (term20 c) = (imp c).
Proof. exact (MK_COMB (@lem5096338) (@lem5096337 c)). Qed.
Lemma lem5096340 (d : Prop) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem5096341 (c : Prop) (d : Prop) : (term25 c d) = (c -> d).
Proof. exact (MK_COMB (@lem5096339 c) (@lem5096340 d)). Qed.
Lemma lem5096344 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096345 (c : Prop) (d : Prop) : (term32 c d) = (term33 c d).
Proof. exact (MK_COMB (@lem5096344) (@lem5096341 c d)). Qed.
Lemma lem5096347 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem5096348 (c : Prop) (d : Prop) : (term26 c d) = (c -> d).
Proof. exact (@lem5096347 (c -> d)). Qed.
Lemma lem5096351 (c : Prop) (d : Prop) : ((term25 c d) = (term26 c d)) = ((c -> d) = (c -> d)).
Proof. exact (MK_COMB (@lem5096345 c d) (@lem5096348 c d)). Qed.
Lemma lem5096353 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem5096354 (x : Prop) : (x = x) = True.
Proof. exact (@lem5096353 Prop x). Qed.
Lemma lem5096355 (c : Prop) (d : Prop) : ((c -> d) = (c -> d)) = True.
Proof. exact (@lem5096354 (c -> d)). Qed.
Lemma lem5096356 (c : Prop) (d : Prop) : ((term25 c d) = (term26 c d)) = True.
Proof. exact (TRANS (@lem5096351 c d) (@lem5096355 c d)). Qed.
Lemma lem5096357 (c : Prop) (d : Prop) : True = ((term25 c d) = (term26 c d)).
Proof. exact (SYM (@lem5096356 c d)). Qed.
Lemma lem5096358 (c : Prop) (d : Prop) : (term25 c d) = (term26 c d).
Proof. exact (EQ_MP (@lem5096357 c d) (@lem0)). Qed.
Lemma lem5096364 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5096365 (c : Prop) : (False /\ c) = False.
Proof. exact (@lem5096364 c). Qed.
Lemma lem5096366 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096367 (c : Prop) : (term34 c) = (imp False).
Proof. exact (MK_COMB (@lem5096366) (@lem5096365 c)). Qed.
Lemma lem5096368 (d : Prop) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem5096369 (c : Prop) (d : Prop) : (term30 c d) = (False -> d).
Proof. exact (MK_COMB (@lem5096367 c) (@lem5096368 d)). Qed.
Lemma lem5096371 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5096372 (d : Prop) : (False -> d) = True.
Proof. exact (@lem5096371 d). Qed.
Lemma lem5096373 (c : Prop) (d : Prop) : (term30 c d) = True.
Proof. exact (TRANS (@lem5096369 c d) (@lem5096372 d)). Qed.
Lemma lem5096374 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096375 (c : Prop) (d : Prop) : (term35 c d) = (@eq Prop True).
Proof. exact (MK_COMB (@lem5096374) (@lem5096373 c d)). Qed.
Lemma lem5096377 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5096378 (c : Prop) (d : Prop) : (term31 c d) = True.
Proof. exact (@lem5096377 (c -> d)). Qed.
Lemma lem5096379 (c : Prop) (d : Prop) : ((term30 c d) = (term31 c d)) = (True = True).
Proof. exact (MK_COMB (@lem5096375 c d) (@lem5096378 c d)). Qed.
Lemma lem5096381 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem5096382 : (True = True) = True.
Proof. exact (@lem5096381 True). Qed.
Lemma lem5096383 (c : Prop) (d : Prop) : ((term30 c d) = (term31 c d)) = True.
Proof. exact (TRANS (@lem5096379 c d) (@lem5096382)). Qed.
Lemma lem5096384 (c : Prop) (d : Prop) : True = ((term30 c d) = (term31 c d)).
Proof. exact (SYM (@lem5096383 c d)). Qed.
Lemma lem5096385 (c : Prop) (d : Prop) : (term30 c d) = (term31 c d).
Proof. exact (EQ_MP (@lem5096384 c d) (@lem0)). Qed.
Lemma lem5096386 (c : Prop) (d : Prop) (b : Prop) (h1 : b = False) : (term17 b c d) = (term21 b c d).
Proof. exact (EQ_MP (@lem5096330 c d b h1) (@lem5096385 c d)). Qed.
Lemma lem5096387 (c : Prop) (d : Prop) (b : Prop) (h1 : b = True) : (term17 b c d) = (term21 b c d).
Proof. exact (EQ_MP (@lem5096317 c d b h1) (@lem5096358 c d)). Qed.
Lemma lem5096389 (b : Prop) (c : Prop) (d : Prop) : (term17 b c d) = (term21 b c d).
Proof. exact (or_elim (@lem5096290 b) (fun h0 : b = True => @lem5096387 c d b h0) (fun h0 : b = False => @lem5096386 c d b h0)). Qed.
Lemma lem5096390 (b : Prop) (c : Prop) (d : Prop) : (term5 b c d) = (term6 b c d).
Proof. exact (EQ_MP (@lem5096287 b c d) (@lem5096389 b c d)). Qed.
Lemma lem5096396 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5096397 (b : Prop) (c : Prop) : (term36 b c) = False.
Proof. exact (@lem5096396 (b /\ c)). Qed.
Lemma lem5096398 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096399 (b : Prop) (c : Prop) : (term37 b c) = (imp False).
Proof. exact (MK_COMB (@lem5096398) (@lem5096397 b c)). Qed.
Lemma lem5096400 (d : Prop) : d = d.
Proof. exact (eq_refl d). Qed.
Lemma lem5096401 (b : Prop) (c : Prop) (d : Prop) : (term12 b c d) = (False -> d).
Proof. exact (MK_COMB (@lem5096399 b c) (@lem5096400 d)). Qed.
Lemma lem5096403 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5096404 (d : Prop) : (False -> d) = True.
Proof. exact (@lem5096403 d). Qed.
Lemma lem5096405 (b : Prop) (c : Prop) (d : Prop) : (term12 b c d) = True.
Proof. exact (TRANS (@lem5096401 b c d) (@lem5096404 d)). Qed.
Lemma lem5096406 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5096407 (b : Prop) (c : Prop) (d : Prop) : (term38 b c d) = (@eq Prop True).
Proof. exact (MK_COMB (@lem5096406) (@lem5096405 b c d)). Qed.
Lemma lem5096411 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem5096412 (b : Prop) : (False /\ b) = False.
Proof. exact (@lem5096411 b). Qed.
Lemma lem5096413 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096414 (b : Prop) : (term34 b) = (imp False).
Proof. exact (MK_COMB (@lem5096413) (@lem5096412 b)). Qed.
Lemma lem5096417 (c : Prop) (d : Prop) : (c -> d) = (c -> d).
Proof. exact (eq_refl (c -> d)). Qed.
Lemma lem5096418 (b : Prop) (c : Prop) (d : Prop) : (term13 b c d) = (term31 c d).
Proof. exact (MK_COMB (@lem5096414 b) (@lem5096417 c d)). Qed.
Lemma lem5096420 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem5096421 (c : Prop) (d : Prop) : (term31 c d) = True.
Proof. exact (@lem5096420 (c -> d)). Qed.
Lemma lem5096422 (b : Prop) (c : Prop) (d : Prop) : (term13 b c d) = True.
Proof. exact (TRANS (@lem5096418 b c d) (@lem5096421 c d)). Qed.
Lemma lem5096423 (b : Prop) (c : Prop) (d : Prop) : ((term12 b c d) = (term13 b c d)) = (True = True).
Proof. exact (MK_COMB (@lem5096407 b c d) (@lem5096422 b c d)). Qed.
Lemma lem5096425 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem5096426 : (True = True) = True.
Proof. exact (@lem5096425 True). Qed.
Lemma lem5096427 (b : Prop) (c : Prop) (d : Prop) : ((term12 b c d) = (term13 b c d)) = True.
Proof. exact (TRANS (@lem5096423 b c d) (@lem5096426)). Qed.
Lemma lem5096428 (b : Prop) (c : Prop) (d : Prop) : True = ((term12 b c d) = (term13 b c d)).
Proof. exact (SYM (@lem5096427 b c d)). Qed.
Lemma lem5096429 (b : Prop) (c : Prop) (d : Prop) : (term12 b c d) = (term13 b c d).
Proof. exact (EQ_MP (@lem5096428 b c d) (@lem0)). Qed.
Lemma lem5096430 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = False) : (term8 a b c d) = (term9 a b c d).
Proof. exact (EQ_MP (@lem5096253 b c d a h1) (@lem5096429 b c d)). Qed.
Lemma lem5096431 (b : Prop) (c : Prop) (d : Prop) (a : Prop) (h1 : a = True) : (term8 a b c d) = (term9 a b c d).
Proof. exact (EQ_MP (@lem5096240 b c d a h1) (@lem5096390 b c d)). Qed.
Lemma lem5096452 (a : Prop) (b : Prop) (c : Prop) (d : Prop) : (term8 a b c d) = (term9 a b c d).
Proof. exact (or_elim (@lem5096209 a) (fun h0 : a = True => @lem5096431 b c d a h0) (fun h0 : a = False => @lem5096430 b c d a h0)). Qed.
Lemma lem5096453 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (n : nat) : (term39 A B f g s t n) = (term40 A B f g s t n).
Proof. exact (@lem5096452 (term41 A B s t g f) (term42 A B t s f g) (@HAS_SIZE A s n) (@HAS_SIZE B t n)). Qed.
Lemma lem5096454 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (n : nat) : (term43 A B f s t n) = (term44 A B f s t n).
Proof. exact (fun_ext (fun g : B -> A => @lem5096453 A B f g s t n)). Qed.
Lemma lem5096455 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5096456 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (n : nat) : (term45 A B f s t n) = (term46 A B f s t n).
Proof. exact (MK_COMB (@lem5096455 A B) (@lem5096454 A B f s t n)). Qed.
Lemma lem5096457 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term47 A B s t n) = (term48 A B s t n).
Proof. exact (fun_ext (fun f : A -> B => @lem5096456 A B f s t n)). Qed.
Lemma lem5096458 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5096459 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term49 A B s t n) = (term50 A B s t n).
Proof. exact (MK_COMB (@lem5096458 A B) (@lem5096457 A B s t n)). Qed.
Lemma lem5096460 {A B : Type'} (s : A -> Prop) (n : nat) : (term51 A B s n) = (term52 A B s n).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5096459 A B s t n)). Qed.
Lemma lem5096461 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5096462 {A B : Type'} (s : A -> Prop) (n : nat) : (term53 A B s n) = (term54 A B s n).
Proof. exact (MK_COMB (@lem5096461 B) (@lem5096460 A B s n)). Qed.
Lemma lem5096463 {A B : Type'} (n : nat) : (term55 A B n) = (term56 A B n).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5096462 A B s n)). Qed.
Lemma lem5096464 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5096465 {A B : Type'} (n : nat) : (term57 A B n) = (term58 A B n).
Proof. exact (MK_COMB (@lem5096464 A) (@lem5096463 A B n)). Qed.
Lemma lem5096466 {A B : Type'} (n : nat) : term58 A B n.
Proof. exact (EQ_MP (@lem5096465 A B n) (@lem5096180 A B n)). Qed.
Lemma lem5096467 {A B : Type'} (n : nat) (h1 : term58 A B n) : term58 A B n.
Proof. exact (h1). Qed.
Lemma lem5096468 {A B : Type'} (s : A -> Prop) (n : nat) (h1 : term58 A B n) : term59 A B n s.
Proof. exact (@lem5096467 A B n h1 s). Qed.
Lemma lem5096469 {A B : Type'} (s : A -> Prop) (n : nat) : (term59 A B n s) = (term54 A B s n).
Proof. exact (eq_refl (term59 A B n s)). Qed.
Lemma lem5096470 {A B : Type'} (s : A -> Prop) (n : nat) (h1 : term58 A B n) : term54 A B s n.
Proof. exact (EQ_MP (@lem5096469 A B s n) (@lem5096468 A B s n h1)). Qed.
Lemma lem5096471 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) (h1 : term58 A B n) : term60 A B s n t.
Proof. exact (@lem5096470 A B s n h1 t). Qed.
Lemma lem5096472 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term60 A B s n t) = (term50 A B s t n).
Proof. exact (eq_refl (term60 A B s n t)). Qed.
Lemma lem5096473 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) (h1 : term58 A B n) : term50 A B s t n.
Proof. exact (EQ_MP (@lem5096472 A B s t n) (@lem5096471 A B s t n h1)). Qed.
Lemma lem5096474 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (n : nat) (h1 : term58 A B n) : term61 A B s t n f.
Proof. exact (@lem5096473 A B s t n h1 f). Qed.
Lemma lem5096475 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (n : nat) : (term61 A B s t n f) = (term46 A B f s t n).
Proof. exact (eq_refl (term61 A B s t n f)). Qed.
Lemma lem5096476 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (n : nat) (h1 : term58 A B n) : term46 A B f s t n.
Proof. exact (EQ_MP (@lem5096475 A B f s t n) (@lem5096474 A B s t f n h1)). Qed.
Lemma lem5096477 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (n : nat) (h1 : term58 A B n) : term62 A B f s t n g.
Proof. exact (@lem5096476 A B f s t n h1 g). Qed.
Lemma lem5096478 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (n : nat) : (term62 A B f s t n g) = (term40 A B f g s t n).
Proof. exact (eq_refl (term62 A B f s t n g)). Qed.
Lemma lem5096479 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) (n : nat) (h1 : term58 A B n) : term40 A B f g s t n.
Proof. exact (EQ_MP (@lem5096478 A B f g s t n) (@lem5096477 A B f s t g n h1)). Qed.
Lemma lem5096480 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term63 A B t s f g) : term63 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096481 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term58 A B n) (h2 : term63 A B t s f g) : term64 A B s t n.
Proof. exact (@lem5096479 A B f g s t n h1 (@lem5096480 A B t s f g h2)). Qed.
Lemma lem5096482 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term63 A B t s f g) : term65 A B s t n.
Proof. exact (fun h0 : term58 A B n => @lem5096481 A B n t s f g h0 h1). Qed.
Lemma lem5096483 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term66 A B t s f) : term66 A B t s f.
Proof. exact (h1). Qed.
Lemma lem5096484 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (h1 : term66 A B t s f) : term65 A B s t n.
Proof. exact (ex_elim (@lem5096483 A B t s f h1) (fun g : B -> A => fun h0 : term67 A B t s f g => @lem5096482 A B n t s f g h0)). Qed.
Lemma lem5096485 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (h1 : term68 A B t s) : term68 A B t s.
Proof. exact (h1). Qed.
Lemma lem5096486 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (h1 : term68 A B t s) : term65 A B s t n.
Proof. exact (ex_elim (@lem5096485 A B t s h1) (fun f : A -> B => fun h0 : term69 A B t s f => @lem5096484 A B n t s f h0)). Qed.
Lemma lem5096487 {A B : Type'} (n : nat) (h1 : term58 A B n) : term58 A B n.
Proof. exact (h1). Qed.
Lemma lem5096488 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (h1 : term58 A B n) (h2 : term68 A B t s) : term64 A B s t n.
Proof. exact (@lem5096486 A B n t s h2 (@lem5096487 A B n h1)). Qed.
Lemma lem5096489 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) (h1 : term58 A B n) : term70 A B s t n.
Proof. exact (fun h0 : term68 A B t s => @lem5096488 A B n t s h1 h0). Qed.
Lemma lem5096490 {A B : Type'} (s : A -> Prop) (n : nat) (h1 : term58 A B n) : term71 A B s n.
Proof. exact (fun t : B -> Prop => @lem5096489 A B s t n h1). Qed.
Lemma lem5096491 {A B : Type'} (n : nat) (h1 : term58 A B n) : term72 A B n.
Proof. exact (fun s : A -> Prop => @lem5096490 A B s n h1). Qed.
Lemma lem5096492 {A B : Type'} (n : nat) : term73 A B n.
Proof. exact (fun h0 : term58 A B n => @lem5096491 A B n h0). Qed.
Lemma lem5096493 {A B : Type'} (n : nat) : term72 A B n.
Proof. exact (@lem5096492 A B n (@lem5096466 A B n)). Qed.
Lemma lem5096494 {A B : Type'} (n : nat) (s : A -> Prop) : term74 A B n s.
Proof. exact (@lem5096493 A B n s). Qed.
Lemma lem5096495 {A B : Type'} (s : A -> Prop) (n : nat) : (term74 A B n s) = (term71 A B s n).
Proof. exact (eq_refl (term74 A B n s)). Qed.
Lemma lem5096496 {A B : Type'} (s : A -> Prop) (n : nat) : term71 A B s n.
Proof. exact (EQ_MP (@lem5096495 A B s n) (@lem5096494 A B n s)). Qed.
Lemma lem5096497 {A B : Type'} (s : A -> Prop) (n : nat) (t : B -> Prop) : term75 A B s n t.
Proof. exact (@lem5096496 A B s n t). Qed.
Lemma lem5096498 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term75 A B s n t) = (term70 A B s t n).
Proof. exact (eq_refl (term75 A B s n t)). Qed.
Lemma lem5096500 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term63 A B t s f g) : term63 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096501 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term42 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096502 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term41 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5096504 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : term70 A B s t n.
Proof. exact (EQ_MP (@lem5096498 A B s t n) (@lem5096497 A B s n t)). Qed.
Lemma lem5096505 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : term70 A B s t n.
Proof. exact (@lem5096504 A B s t n). Qed.
Lemma lem5096507 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : term70 A B s t n.
Proof. exact (EQ_MP (@lem5096498 A B s t n) (@lem5096497 A B s n t)). Qed.
Lemma lem5096508 {A B : Type'} (s : B -> Prop) (t : A -> Prop) (n : nat) : term76 A B s t n.
Proof. exact (@lem5096507 B A s t n). Qed.
Lemma lem5096509 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (n : nat) : term76 A B t s n.
Proof. exact (@lem5096508 A B t s n). Qed.
Lemma lem5096511 (p : Prop) : p = (term77 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5096512 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term63 A B t s f g) = (term78 A B t s f g).
Proof. exact (@lem5096511 (term63 A B t s f g)). Qed.
Lemma lem5096513 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term78 A B t s f g) = (term63 A B t s f g).
Proof. exact (SYM (@lem5096512 A B t s f g)). Qed.
Lemma lem5096514 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term79 A B t s f g) : term79 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096517 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term80 A B t s f g) : term80 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096518 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term81 A B t s f g.
Proof. exact (fun h0 : term80 A B t s f g => @lem5096517 A B t s f g h0). Qed.
Lemma lem5096519 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term81 A B t s f g) : term81 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096520 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term80 A B t s f g) : term80 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096521 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term80 A B t s f g) (h2 : term81 A B t s f g) : term80 A B t s f g.
Proof. exact (@lem5096519 A B t s f g h2 (@lem5096520 A B t s f g h1)). Qed.
Lemma lem5096522 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term80 A B t s f g) : term82 A B t s f g.
Proof. exact (fun h0 : term81 A B t s f g => @lem5096521 A B t s f g h1 h0). Qed.
Lemma lem5096523 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term81 A B t s f g) : term81 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096524 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term80 A B t s f g) (h2 : term81 A B t s f g) : term80 A B t s f g.
Proof. exact (@lem5096522 A B t s f g h1 (@lem5096523 A B t s f g h2)). Qed.
Lemma lem5096525 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term81 A B t s f g) : term81 A B t s f g.
Proof. exact (fun h0 : term80 A B t s f g => @lem5096524 A B t s f g h0 h1). Qed.
Lemma lem5096526 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term83 A B t s f g.
Proof. exact (fun h0 : term81 A B t s f g => @lem5096525 A B t s f g h0). Qed.
Lemma lem5096529 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term81 A B t s f g.
Proof. exact (@lem5096526 A B t s f g (@lem5096518 A B t s f g)). Qed.
Lemma lem5096530 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term81 A B t s f g.
Proof. exact (@lem5096529 A B t s f g). Qed.
Lemma lem5096568 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5096569 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term78 A B t s f g) = (term84 A B t s f g).
Proof. exact (@lem5096568 (term79 A B t s f g)). Qed.
Lemma lem5096571 (t : Prop) : (term85 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5096572 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term84 A B t s f g) = (term63 A B t s f g).
Proof. exact (@lem5096571 (term63 A B t s f g)). Qed.
Lemma lem5096575 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term78 A B t s f g) = (term63 A B t s f g).
Proof. exact (TRANS (@lem5096569 A B t s f g) (@lem5096572 A B t s f g)). Qed.
Lemma lem5096592 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term86 A B t s f g) = (term86 A B t s f g).
Proof. exact (eq_refl (term86 A B t s f g)). Qed.
Lemma lem5096593 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term87 A B t s f g) = (term88 A B t s f g).
Proof. exact (MK_COMB (@lem5096592 A B t s f g) (@lem5096575 A B t s f g)). Qed.
Lemma lem5096596 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term89 A B s t g f) = (term89 A B s t g f).
Proof. exact (eq_refl (term89 A B s t g f)). Qed.
Lemma lem5096597 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term80 A B t s f g) = (term90 A B t s f g).
Proof. exact (MK_COMB (@lem5096596 A B s t g f) (@lem5096593 A B t s f g)). Qed.
Lemma lem5096600 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term91 A B s f g) = (term92 A B s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5096597 A B t s f g)). Qed.
Lemma lem5096601 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5096602 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term93 A B s f g) = (term94 A B s f g).
Proof. exact (MK_COMB (@lem5096601 B) (@lem5096600 A B s f g)). Qed.
Lemma lem5096607 {A B : Type'} (f : A -> B) (g : B -> A) : (term95 A B f g) = (term96 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5096602 A B s f g)). Qed.
Lemma lem5096608 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5096609 {A B : Type'} (f : A -> B) (g : B -> A) : (term97 A B f g) = (term98 A B f g).
Proof. exact (MK_COMB (@lem5096608 A) (@lem5096607 A B f g)). Qed.
Lemma lem5096614 {A B : Type'} (g : B -> A) : (term99 A B g) = (term100 A B g).
Proof. exact (fun_ext (fun f : A -> B => @lem5096609 A B f g)). Qed.
Lemma lem5096615 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5096616 {A B : Type'} (g : B -> A) : (term101 A B g) = (term102 A B g).
Proof. exact (MK_COMB (@lem5096615 A B) (@lem5096614 A B g)). Qed.
Lemma lem5096621 {A B : Type'} : (term103 A B) = (term104 A B).
Proof. exact (fun_ext (fun g : B -> A => @lem5096616 A B g)). Qed.
Lemma lem5096622 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5096631 {A B : Type'} : (term105 A B) = (term106 A B).
Proof. exact (MK_COMB (@lem5096622 A B) (@lem5096621 A B)). Qed.
Lemma lem5096640 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term107 A B t s f g y) = (term107 A B t s f g y).
Proof. exact (eq_refl (term107 A B t s f g y)). Qed.
Lemma lem5096641 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term108 A B t s f g) = (term108 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5096640 A B t s f g y)). Qed.
Lemma lem5096642 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5096643 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term42 A B t s f g) = (term42 A B t s f g).
Proof. exact (MK_COMB (@lem5096642 B) (@lem5096641 A B t s f g)). Qed.
Lemma lem5096652 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term109 A B s t g f x) = (term109 A B s t g f x).
Proof. exact (eq_refl (term109 A B s t g f x)). Qed.
Lemma lem5096653 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term110 A B s t g f) = (term110 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5096652 A B s t g f x)). Qed.
Lemma lem5096654 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5096655 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term41 A B s t g f) = (term41 A B s t g f).
Proof. exact (MK_COMB (@lem5096654 A) (@lem5096653 A B s t g f)). Qed.
Lemma lem5096656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5096657 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term111 A B s t g f) = (term111 A B s t g f).
Proof. exact (MK_COMB (@lem5096656) (@lem5096655 A B s t g f)). Qed.
Lemma lem5096658 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term63 A B t s f g) = (term63 A B t s f g).
Proof. exact (MK_COMB (@lem5096657 A B s t g f) (@lem5096643 A B t s f g)). Qed.
Lemma lem5096667 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term107 A B t s f g y) = (term107 A B t s f g y).
Proof. exact (eq_refl (term107 A B t s f g y)). Qed.
Lemma lem5096668 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term108 A B t s f g) = (term108 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5096667 A B t s f g y)). Qed.
Lemma lem5096669 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5096670 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term42 A B t s f g) = (term42 A B t s f g).
Proof. exact (MK_COMB (@lem5096669 B) (@lem5096668 A B t s f g)). Qed.
Lemma lem5096671 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096672 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term86 A B t s f g) = (term86 A B t s f g).
Proof. exact (MK_COMB (@lem5096671) (@lem5096670 A B t s f g)). Qed.
Lemma lem5096673 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term88 A B t s f g) = (term88 A B t s f g).
Proof. exact (MK_COMB (@lem5096672 A B t s f g) (@lem5096658 A B t s f g)). Qed.
Lemma lem5096682 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term109 A B s t g f x) = (term109 A B s t g f x).
Proof. exact (eq_refl (term109 A B s t g f x)). Qed.
Lemma lem5096683 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term110 A B s t g f) = (term110 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5096682 A B s t g f x)). Qed.
Lemma lem5096684 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5096685 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term41 A B s t g f) = (term41 A B s t g f).
Proof. exact (MK_COMB (@lem5096684 A) (@lem5096683 A B s t g f)). Qed.
Lemma lem5096686 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5096687 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term89 A B s t g f) = (term89 A B s t g f).
Proof. exact (MK_COMB (@lem5096686) (@lem5096685 A B s t g f)). Qed.
Lemma lem5096688 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term90 A B t s f g) = (term90 A B t s f g).
Proof. exact (MK_COMB (@lem5096687 A B s t g f) (@lem5096673 A B t s f g)). Qed.
Lemma lem5096689 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term92 A B s f g) = (term92 A B s f g).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5096688 A B t s f g)). Qed.
Lemma lem5096690 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5096691 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term94 A B s f g) = (term94 A B s f g).
Proof. exact (MK_COMB (@lem5096690 B) (@lem5096689 A B s f g)). Qed.
Lemma lem5096692 {A B : Type'} (f : A -> B) (g : B -> A) : (term96 A B f g) = (term96 A B f g).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5096691 A B s f g)). Qed.
Lemma lem5096693 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5096694 {A B : Type'} (f : A -> B) (g : B -> A) : (term98 A B f g) = (term98 A B f g).
Proof. exact (MK_COMB (@lem5096693 A) (@lem5096692 A B f g)). Qed.
Lemma lem5096695 {A B : Type'} (g : B -> A) : (term100 A B g) = (term100 A B g).
Proof. exact (fun_ext (fun f : A -> B => @lem5096694 A B f g)). Qed.
Lemma lem5096696 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5096697 {A B : Type'} (g : B -> A) : (term102 A B g) = (term102 A B g).
Proof. exact (MK_COMB (@lem5096696 A B) (@lem5096695 A B g)). Qed.
Lemma lem5096698 {A B : Type'} : (term104 A B) = (term104 A B).
Proof. exact (fun_ext (fun g : B -> A => @lem5096697 A B g)). Qed.
Lemma lem5096699 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5096700 {A B : Type'} : (term106 A B) = (term106 A B).
Proof. exact (MK_COMB (@lem5096699 A B) (@lem5096698 A B)). Qed.
Lemma lem5096773 {A B : Type'} : (term105 A B) = (term106 A B).
Proof. exact (TRANS (@lem5096631 A B) (@lem5096700 A B)). Qed.
Lemma lem5096774 {A B : Type'} : (term106 A B) = (term105 A B).
Proof. exact (SYM (@lem5096773 A B)). Qed.
Lemma lem5096775 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term41 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5096776 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term42 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096778 (p : Prop) : p = (term77 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5096779 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term63 A B t s f g) = (term78 A B t s f g).
Proof. exact (@lem5096778 (term63 A B t s f g)). Qed.
Lemma lem5096780 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term78 A B t s f g) = (term63 A B t s f g).
Proof. exact (SYM (@lem5096779 A B t s f g)). Qed.
Lemma lem5096781 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term79 A B t s f g) : term79 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5096792 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term109 A B s t g f x) = (term112 A B s t g f x).
Proof. exact (@lem17265 (@IN A x s) (term113 A B t g f x)). Qed.
Lemma lem5096793 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term110 A B s t g f) = (term114 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5096792 A B s t g f x)). Qed.
Lemma lem5096794 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5096847 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term41 A B s t g f) = (term115 A B s t g f).
Proof. exact (MK_COMB (@lem5096794 A) (@lem5096793 A B s t g f)). Qed.
Lemma lem5096848 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term115 A B s t g f.
Proof. exact (EQ_MP (@lem5096847 A B s t g f) (@lem5096775 A B s t g f h1)). Qed.
Lemma lem5096859 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term107 A B t s f g y) = (term116 A B t s f g y).
Proof. exact (@lem17265 (@IN B y t) (term117 A B s f g y)). Qed.
Lemma lem5096860 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term108 A B t s f g) = (term118 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5096859 A B t s f g y)). Qed.
Lemma lem5096861 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5096914 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term42 A B t s f g) = (term119 A B t s f g).
Proof. exact (MK_COMB (@lem5096861 B) (@lem5096860 A B t s f g)). Qed.
Lemma lem5096915 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term119 A B t s f g.
Proof. exact (EQ_MP (@lem5096914 A B t s f g) (@lem5096776 A B t s f g h1)). Qed.
Lemma lem5096923 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term120 A B t g f x) = (term121 A B t g f x).
Proof. exact (@lem17045 (term122 A B f x t) ((term123 A B g f x) = x)). Qed.
Lemma lem5096925 {A : Type'} (x : A) (s : A -> Prop) : (term124 A x s) = (term124 A x s).
Proof. exact (eq_refl (term124 A x s)). Qed.
Lemma lem5096926 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term125 A B s t g f x) = (term126 A B s t g f x).
Proof. exact (MK_COMB (@lem5096925 A x s) (@lem5096923 A B t g f x)). Qed.
Lemma lem5096927 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term127 A B s t g f x) = (term125 A B s t g f x).
Proof. exact (@lem17362 (@IN A x s) (term113 A B t g f x)). Qed.
Lemma lem5096928 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term127 A B s t g f x) = (term126 A B s t g f x).
Proof. exact (TRANS (@lem5096927 A B s t g f x) (@lem5096926 A B s t g f x)). Qed.
Lemma lem5096929 {A : Type'} (P : A -> Prop) : (term128 A P) = (term129 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5096930 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term130 A B s t g f) = (term131 A B s t g f).
Proof. exact (@lem5096929 A (term110 A B s t g f)). Qed.
Lemma lem5096931 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term132 A B s t g f x) = (term109 A B s t g f x).
Proof. exact (eq_refl (term132 A B s t g f x)). Qed.
Lemma lem5096932 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5096933 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term133 A B s t g f x) = (term127 A B s t g f x).
Proof. exact (MK_COMB (@lem5096932) (@lem5096931 A B s t g f x)). Qed.
Lemma lem5096934 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term133 A B s t g f x) = (term126 A B s t g f x).
Proof. exact (TRANS (@lem5096933 A B s t g f x) (@lem5096928 A B s t g f x)). Qed.
Lemma lem5096935 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term134 A B s t g f) = (term135 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5096934 A B s t g f x)). Qed.
Lemma lem5096936 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5096937 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term131 A B s t g f) = (term136 A B s t g f).
Proof. exact (MK_COMB (@lem5096936 A) (@lem5096935 A B s t g f)). Qed.
Lemma lem5096938 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term130 A B s t g f) = (term136 A B s t g f).
Proof. exact (TRANS (@lem5096930 A B s t g f) (@lem5096937 A B s t g f)). Qed.
Lemma lem5096946 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term137 A B s f g y) = (term138 A B s f g y).
Proof. exact (@lem17045 (term139 A B g y s) ((term140 A B f g y) = y)). Qed.
Lemma lem5096948 {B : Type'} (y : B) (t : B -> Prop) : (term124 B y t) = (term124 B y t).
Proof. exact (eq_refl (term124 B y t)). Qed.
Lemma lem5096949 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term141 A B t s f g y) = (term142 A B t s f g y).
Proof. exact (MK_COMB (@lem5096948 B y t) (@lem5096946 A B s f g y)). Qed.
Lemma lem5096950 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term143 A B t s f g y) = (term141 A B t s f g y).
Proof. exact (@lem17362 (@IN B y t) (term117 A B s f g y)). Qed.
Lemma lem5096951 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term143 A B t s f g y) = (term142 A B t s f g y).
Proof. exact (TRANS (@lem5096950 A B t s f g y) (@lem5096949 A B t s f g y)). Qed.
Lemma lem5096952 {B : Type'} (P : B -> Prop) : (term128 B P) = (term129 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5096953 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term144 A B t s f g) = (term145 A B t s f g).
Proof. exact (@lem5096952 B (term108 A B t s f g)). Qed.
Lemma lem5096954 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term146 A B t s f g y) = (term107 A B t s f g y).
Proof. exact (eq_refl (term146 A B t s f g y)). Qed.
Lemma lem5096955 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5096956 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term147 A B t s f g y) = (term143 A B t s f g y).
Proof. exact (MK_COMB (@lem5096955) (@lem5096954 A B t s f g y)). Qed.
Lemma lem5096957 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term147 A B t s f g y) = (term142 A B t s f g y).
Proof. exact (TRANS (@lem5096956 A B t s f g y) (@lem5096951 A B t s f g y)). Qed.
Lemma lem5096958 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term148 A B t s f g) = (term149 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5096957 A B t s f g y)). Qed.
Lemma lem5096959 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5096960 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term145 A B t s f g) = (term150 A B t s f g).
Proof. exact (MK_COMB (@lem5096959 B) (@lem5096958 A B t s f g)). Qed.
Lemma lem5096961 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term144 A B t s f g) = (term150 A B t s f g).
Proof. exact (TRANS (@lem5096953 A B t s f g) (@lem5096960 A B t s f g)). Qed.
Lemma lem5096962 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5096963 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term151 A B s t g f) = (term152 A B s t g f).
Proof. exact (MK_COMB (@lem5096962) (@lem5096938 A B s t g f)). Qed.
Lemma lem5096964 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term153 A B t s f g) = (term154 A B t s f g).
Proof. exact (MK_COMB (@lem5096963 A B s t g f) (@lem5096961 A B t s f g)). Qed.
Lemma lem5096965 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term79 A B t s f g) = (term153 A B t s f g).
Proof. exact (@lem17045 (term41 A B s t g f) (term42 A B t s f g)). Qed.
Lemma lem5096966 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term79 A B t s f g) = (term154 A B t s f g).
Proof. exact (TRANS (@lem5096965 A B t s f g) (@lem5096964 A B t s f g)). Qed.
Lemma lem5097067 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5097068 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (@lem5097067 A P Q). Qed.
Lemma lem5097069 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term157 A B t s f g) = (term158 A B t s f g).
Proof. exact (@lem5097068 A (term135 A B s t g f) (term150 A B t s f g)). Qed.
Lemma lem5097070 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term159 A B s t g f x) = (term126 A B s t g f x).
Proof. exact (eq_refl (term159 A B s t g f x)). Qed.
Lemma lem5097071 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term160 A B s t g f) = (term135 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5097070 A B s t g f x)). Qed.
Lemma lem5097072 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5097073 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term161 A B s t g f) = (term136 A B s t g f).
Proof. exact (MK_COMB (@lem5097072 A) (@lem5097071 A B s t g f)). Qed.
Lemma lem5097074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5097075 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term162 A B s t g f) = (term152 A B s t g f).
Proof. exact (MK_COMB (@lem5097074) (@lem5097073 A B s t g f)). Qed.
Lemma lem5097076 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term150 A B t s f g) = (term150 A B t s f g).
Proof. exact (eq_refl (term150 A B t s f g)). Qed.
Lemma lem5097077 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term157 A B t s f g) = (term154 A B t s f g).
Proof. exact (MK_COMB (@lem5097075 A B s t g f) (@lem5097076 A B t s f g)). Qed.
Lemma lem5097078 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5097079 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term163 A B t s f g) = (term164 A B t s f g).
Proof. exact (MK_COMB (@lem5097078) (@lem5097077 A B t s f g)). Qed.
Lemma lem5097080 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term159 A B s t g f x) = (term126 A B s t g f x).
Proof. exact (eq_refl (term159 A B s t g f x)). Qed.
Lemma lem5097081 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5097082 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term165 A B s t g f x) = (term166 A B s t g f x).
Proof. exact (MK_COMB (@lem5097081) (@lem5097080 A B s t g f x)). Qed.
Lemma lem5097083 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term150 A B t s f g) = (term150 A B t s f g).
Proof. exact (eq_refl (term150 A B t s f g)). Qed.
Lemma lem5097084 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term167 A B x t s f g) = (term168 A B x t s f g).
Proof. exact (MK_COMB (@lem5097082 A B s t g f x) (@lem5097083 A B t s f g)). Qed.
Lemma lem5097085 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term169 A B t s f g) = (term170 A B t s f g).
Proof. exact (fun_ext (fun x : A => @lem5097084 A B x t s f g)). Qed.
Lemma lem5097086 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5097087 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term158 A B t s f g) = (term171 A B t s f g).
Proof. exact (MK_COMB (@lem5097086 A) (@lem5097085 A B t s f g)). Qed.
Lemma lem5097088 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term157 A B t s f g) = (term158 A B t s f g)) = ((term154 A B t s f g) = (term171 A B t s f g)).
Proof. exact (MK_COMB (@lem5097079 A B t s f g) (@lem5097087 A B t s f g)). Qed.
Lemma lem5097089 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term154 A B t s f g) = (term171 A B t s f g).
Proof. exact (EQ_MP (@lem5097088 A B t s f g) (@lem5097069 A B t s f g)). Qed.
Lemma lem5097091 {A : Type'} (P : Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5097092 {B : Type'} (P : Prop) (Q : B -> Prop) : (term172 B P Q) = (term173 B P Q).
Proof. exact (@lem5097091 B P Q). Qed.
Lemma lem5097093 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term174 A B x t s f g) = (term175 A B x t s f g).
Proof. exact (@lem5097092 B (term126 A B s t g f x) (term149 A B t s f g)). Qed.
Lemma lem5097094 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term176 A B t s f g y) = (term142 A B t s f g y).
Proof. exact (eq_refl (term176 A B t s f g y)). Qed.
Lemma lem5097095 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term177 A B t s f g) = (term149 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5097094 A B t s f g y)). Qed.
Lemma lem5097096 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5097097 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term178 A B t s f g) = (term150 A B t s f g).
Proof. exact (MK_COMB (@lem5097096 B) (@lem5097095 A B t s f g)). Qed.
Lemma lem5097098 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term166 A B s t g f x) = (term166 A B s t g f x).
Proof. exact (eq_refl (term166 A B s t g f x)). Qed.
Lemma lem5097099 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term174 A B x t s f g) = (term168 A B x t s f g).
Proof. exact (MK_COMB (@lem5097098 A B s t g f x) (@lem5097097 A B t s f g)). Qed.
Lemma lem5097100 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5097101 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term179 A B x t s f g) = (term180 A B x t s f g).
Proof. exact (MK_COMB (@lem5097100) (@lem5097099 A B x t s f g)). Qed.
Lemma lem5097102 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term176 A B t s f g y) = (term142 A B t s f g y).
Proof. exact (eq_refl (term176 A B t s f g y)). Qed.
Lemma lem5097103 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term166 A B s t g f x) = (term166 A B s t g f x).
Proof. exact (eq_refl (term166 A B s t g f x)). Qed.
Lemma lem5097104 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term181 A B x t s f g y) = (term182 A B x t s f g y).
Proof. exact (MK_COMB (@lem5097103 A B s t g f x) (@lem5097102 A B t s f g y)). Qed.
Lemma lem5097105 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term183 A B x t s f g) = (term184 A B x t s f g).
Proof. exact (fun_ext (fun y : B => @lem5097104 A B x t s f g y)). Qed.
Lemma lem5097106 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5097107 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term175 A B x t s f g) = (term185 A B x t s f g).
Proof. exact (MK_COMB (@lem5097106 B) (@lem5097105 A B x t s f g)). Qed.
Lemma lem5097108 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : ((term174 A B x t s f g) = (term175 A B x t s f g)) = ((term168 A B x t s f g) = (term185 A B x t s f g)).
Proof. exact (MK_COMB (@lem5097101 A B x t s f g) (@lem5097107 A B x t s f g)). Qed.
Lemma lem5097109 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term168 A B x t s f g) = (term185 A B x t s f g).
Proof. exact (EQ_MP (@lem5097108 A B x t s f g) (@lem5097093 A B x t s f g)). Qed.
Lemma lem5097110 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term170 A B t s f g) = (term186 A B t s f g).
Proof. exact (fun_ext (fun x : A => @lem5097109 A B x t s f g)). Qed.
Lemma lem5097111 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5097112 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term171 A B t s f g) = (term187 A B t s f g).
Proof. exact (MK_COMB (@lem5097111 A) (@lem5097110 A B t s f g)). Qed.
Lemma lem5097114 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term154 A B t s f g) = (term187 A B t s f g).
Proof. exact (TRANS (@lem5097089 A B t s f g) (@lem5097112 A B t s f g)). Qed.
Lemma lem5097115 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term79 A B t s f g) = (term187 A B t s f g).
Proof. exact (TRANS (@lem5096966 A B t s f g) (@lem5097114 A B t s f g)). Qed.
Lemma lem5097116 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term79 A B t s f g) : term187 A B t s f g.
Proof. exact (EQ_MP (@lem5097115 A B t s f g) (@lem5096781 A B t s f g h1)). Qed.
Lemma lem5097117 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term185 A B x t s f g) : term185 A B x t s f g.
Proof. exact (h1). Qed.
Lemma lem5097147 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term112 A B s t g f x) = (term112 A B s t g f x).
Proof. exact (eq_refl (term112 A B s t g f x)). Qed.
Lemma lem5097148 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term114 A B s t g f) = (term114 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5097147 A B s t g f x)). Qed.
Lemma lem5097149 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5097150 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term115 A B s t g f) = (term115 A B s t g f).
Proof. exact (MK_COMB (@lem5097149 A) (@lem5097148 A B s t g f)). Qed.
Lemma lem5097151 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term115 A B s t g f.
Proof. exact (EQ_MP (@lem5097150 A B s t g f) (@lem5096848 A B s t g f h1)). Qed.
Lemma lem5097180 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term116 A B t s f g y) = (term116 A B t s f g y).
Proof. exact (eq_refl (term116 A B t s f g y)). Qed.
Lemma lem5097181 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term118 A B t s f g) = (term118 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5097180 A B t s f g y)). Qed.
Lemma lem5097182 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5097183 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term119 A B t s f g) = (term119 A B t s f g).
Proof. exact (MK_COMB (@lem5097182 B) (@lem5097181 A B t s f g)). Qed.
Lemma lem5097184 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term119 A B t s f g.
Proof. exact (EQ_MP (@lem5097183 A B t s f g) (@lem5096915 A B t s f g h1)). Qed.
Lemma lem5097250 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term182 A B x t s f g y) : term182 A B x t s f g y.
Proof. exact (h1). Qed.
Lemma lem5097251 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : term126 A B s t g f x.
Proof. exact (h1). Qed.
Lemma lem5097252 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : term142 A B t s f g y.
Proof. exact (h1). Qed.
Lemma lem5097253 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : term121 A B t g f x.
Proof. exact (proj2 (@lem5097251 A B s t g f x h1)). Qed.
Lemma lem5097257 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : term138 A B s f g y.
Proof. exact (proj2 (@lem5097252 A B t s f g y h1)). Qed.
Lemma lem5097278 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term112 A B s t g f x) = (term188 A B t s g f x).
Proof. exact (@lem19490 (term122 A B f x t) (term189 A x s) ((term123 A B g f x) = x)). Qed.
Lemma lem5097279 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term114 A B s t g f) = (term190 A B t s g f).
Proof. exact (fun_ext (fun x : A => @lem5097278 A B t s g f x)). Qed.
Lemma lem5097280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5097282 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term115 A B s t g f) = (term191 A B t s g f).
Proof. exact (MK_COMB (@lem5097280 A) (@lem5097279 A B t s g f)). Qed.
Lemma lem5097283 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term191 A B t s g f.
Proof. exact (EQ_MP (@lem5097282 A B t s g f) (@lem5097151 A B s t g f h1)). Qed.
Lemma lem5097314 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term192 A B f x t) : term192 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5097332 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term112 A B s t g f x) = (term188 A B t s g f x).
Proof. exact (@lem19490 (term122 A B f x t) (term189 A x s) ((term123 A B g f x) = x)). Qed.
Lemma lem5097333 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term114 A B s t g f) = (term190 A B t s g f).
Proof. exact (fun_ext (fun x : A => @lem5097332 A B t s g f x)). Qed.
Lemma lem5097334 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5097336 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term115 A B s t g f) = (term191 A B t s g f).
Proof. exact (MK_COMB (@lem5097334 A) (@lem5097333 A B t s g f)). Qed.
Lemma lem5097337 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term191 A B t s g f.
Proof. exact (EQ_MP (@lem5097336 A B t s g f) (@lem5097151 A B s t g f h1)). Qed.
Lemma lem5097368 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term193 A B g f x) : term193 A B g f x.
Proof. exact (h1). Qed.
Lemma lem5097409 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term116 A B t s f g y) = (term194 A B s t f g y).
Proof. exact (@lem19490 (term139 A B g y s) (term189 B y t) ((term140 A B f g y) = y)). Qed.
Lemma lem5097410 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term118 A B t s f g) = (term195 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5097409 A B s t f g y)). Qed.
Lemma lem5097411 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5097413 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term119 A B t s f g) = (term196 A B s t f g).
Proof. exact (MK_COMB (@lem5097411 B) (@lem5097410 A B s t f g)). Qed.
Lemma lem5097414 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term196 A B s t f g.
Proof. exact (EQ_MP (@lem5097413 A B s t f g) (@lem5097184 A B t s f g h1)). Qed.
Lemma lem5097422 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term197 A B g y s) : term197 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5097463 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term116 A B t s f g y) = (term194 A B s t f g y).
Proof. exact (@lem19490 (term139 A B g y s) (term189 B y t) ((term140 A B f g y) = y)). Qed.
Lemma lem5097464 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term118 A B t s f g) = (term195 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5097463 A B s t f g y)). Qed.
Lemma lem5097465 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5097467 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term119 A B t s f g) = (term196 A B s t f g).
Proof. exact (MK_COMB (@lem5097465 B) (@lem5097464 A B s t f g)). Qed.
Lemma lem5097468 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term196 A B s t f g.
Proof. exact (EQ_MP (@lem5097467 A B s t f g) (@lem5097184 A B t s f g h1)). Qed.
Lemma lem5097476 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term198 A B f g y) : term198 A B f g y.
Proof. exact (h1). Qed.
Lemma lem5097477 {A B : Type'} (_66345 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term199 A B t s g f _66345.
Proof. exact (@lem5097283 A B s t g f h1 _66345). Qed.
Lemma lem5097478 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (_66345 : A) : (term199 A B t s g f _66345) = (term188 A B t s g f _66345).
Proof. exact (eq_refl (term199 A B t s g f _66345)). Qed.
Lemma lem5097479 {A B : Type'} (_66345 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term188 A B t s g f _66345.
Proof. exact (EQ_MP (@lem5097478 A B t s g f _66345) (@lem5097477 A B _66345 s t g f h1)). Qed.
Lemma lem5097483 {A B : Type'} (_66347 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term199 A B t s g f _66347.
Proof. exact (@lem5097337 A B s t g f h1 _66347). Qed.
Lemma lem5097484 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (_66347 : A) : (term199 A B t s g f _66347) = (term188 A B t s g f _66347).
Proof. exact (eq_refl (term199 A B t s g f _66347)). Qed.
Lemma lem5097485 {A B : Type'} (_66347 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term188 A B t s g f _66347.
Proof. exact (EQ_MP (@lem5097484 A B t s g f _66347) (@lem5097483 A B _66347 s t g f h1)). Qed.
Lemma lem5097492 {A B : Type'} (_66350 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term200 A B s t f g _66350.
Proof. exact (@lem5097414 A B t s f g h1 _66350). Qed.
Lemma lem5097493 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_66350 : B) : (term200 A B s t f g _66350) = (term194 A B s t f g _66350).
Proof. exact (eq_refl (term200 A B s t f g _66350)). Qed.
Lemma lem5097494 {A B : Type'} (_66350 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term194 A B s t f g _66350.
Proof. exact (EQ_MP (@lem5097493 A B s t f g _66350) (@lem5097492 A B _66350 t s f g h1)). Qed.
Lemma lem5097498 {A B : Type'} (_66352 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term200 A B s t f g _66352.
Proof. exact (@lem5097468 A B t s f g h1 _66352). Qed.
Lemma lem5097499 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_66352 : B) : (term200 A B s t f g _66352) = (term194 A B s t f g _66352).
Proof. exact (eq_refl (term200 A B s t f g _66352)). Qed.
Lemma lem5097500 {A B : Type'} (_66352 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term194 A B s t f g _66352.
Proof. exact (EQ_MP (@lem5097499 A B s t f g _66352) (@lem5097498 A B _66352 t s f g h1)). Qed.
Lemma lem5097520 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term192 A B f x t) : term192 A B f x t.
Proof. exact (h1). Qed.
Lemma lem5097538 {A B : Type'} (_66345 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term201 A B s f _66345 t.
Proof. exact (proj1 (@lem5097479 A B _66345 s t g f h1)). Qed.
Lemma lem5097548 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term193 A B g f x) : term193 A B g f x.
Proof. exact (h1). Qed.
Lemma lem5097572 {A B : Type'} (_66347 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term202 A B s g f _66347.
Proof. exact (proj2 (@lem5097485 A B _66347 s t g f h1)). Qed.
Lemma lem5097576 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term197 A B g y s) : term197 A B g y s.
Proof. exact (h1). Qed.
Lemma lem5097582 {A B : Type'} (_66350 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term203 A B t g _66350 s.
Proof. exact (proj1 (@lem5097494 A B _66350 t s f g h1)). Qed.
Lemma lem5097604 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term198 A B f g y) : term198 A B f g y.
Proof. exact (h1). Qed.
Lemma lem5097616 {A B : Type'} (_66352 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term204 A B t f g _66352.
Proof. exact (proj2 (@lem5097500 A B _66352 t s f g h1)). Qed.
Lemma lem5097692 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5097251 A B s t g f x h1)). Qed.
Lemma lem5097693 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : term205 A x s.
Proof. exact (fun h0 : term189 A x s => @lem5097692 A B s t g f x h1). Qed.
Lemma lem5097695 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5097696 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (@IN A x s).
Proof. exact (@lem5097695 (@IN A x s)). Qed.
Lemma lem5097697 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5097696 A x s) (@lem5097693 A B s t g f x h1)). Qed.
Lemma lem5097703 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5097704 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : (term201 A B s f _66345 t) = (term207 A B f t _66345 s).
Proof. exact (@lem5097703 (term122 A B f _66345 t) (term189 A _66345 s)). Qed.
Lemma lem5097710 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5097711 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : (term208 A B s f _66345 t) = (term209 A B f t _66345 s).
Proof. exact (MK_COMB (@lem5097710) (@lem5097704 A B f t _66345 s)). Qed.
Lemma lem5097717 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : (term207 A B f t _66345 s) = (term207 A B f t _66345 s).
Proof. exact (eq_refl (term207 A B f t _66345 s)). Qed.
Lemma lem5097718 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : ((term201 A B s f _66345 t) = (term207 A B f t _66345 s)) = ((term207 A B f t _66345 s) = (term207 A B f t _66345 s)).
Proof. exact (MK_COMB (@lem5097711 A B f t _66345 s) (@lem5097717 A B f t _66345 s)). Qed.
Lemma lem5097720 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5097721 (x : Prop) : (x = x) = True.
Proof. exact (@lem5097720 Prop x). Qed.
Lemma lem5097722 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : ((term207 A B f t _66345 s) = (term207 A B f t _66345 s)) = True.
Proof. exact (@lem5097721 (term207 A B f t _66345 s)). Qed.
Lemma lem5097723 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : ((term201 A B s f _66345 t) = (term207 A B f t _66345 s)) = True.
Proof. exact (TRANS (@lem5097718 A B f t _66345 s) (@lem5097722 A B f t _66345 s)). Qed.
Lemma lem5097724 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : True = ((term201 A B s f _66345 t) = (term207 A B f t _66345 s)).
Proof. exact (SYM (@lem5097723 A B f t _66345 s)). Qed.
Lemma lem5097725 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66345 : A) (s : A -> Prop) : (term201 A B s f _66345 t) = (term207 A B f t _66345 s).
Proof. exact (EQ_MP (@lem5097724 A B f t _66345 s) (@lem0)). Qed.
Lemma lem5097726 {A B : Type'} (_66345 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term207 A B f t _66345 s.
Proof. exact (EQ_MP (@lem5097725 A B f t _66345 s) (@lem5097538 A B _66345 s t g f h1)). Qed.
Lemma lem5097728 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5097729 {A B : Type'} (s : A -> Prop) (f : A -> B) (_66345 : A) (t : B -> Prop) : (term207 A B f t _66345 s) = (term211 A B s f _66345 t).
Proof. exact (@lem5097728 (term189 A _66345 s) (term122 A B f _66345 t)). Qed.
Lemma lem5097731 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5097732 {A : Type'} (_66345 : A) (s : A -> Prop) : (term212 A _66345 s) = (@IN A _66345 s).
Proof. exact (@lem5097731 (@IN A _66345 s)). Qed.
Lemma lem5097733 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5097734 {A : Type'} (_66345 : A) (s : A -> Prop) : (term213 A _66345 s) = (term214 A _66345 s).
Proof. exact (MK_COMB (@lem5097733) (@lem5097732 A _66345 s)). Qed.
Lemma lem5097735 {A B : Type'} (f : A -> B) (_66345 : A) (t : B -> Prop) : (term122 A B f _66345 t) = (term122 A B f _66345 t).
Proof. exact (eq_refl (term122 A B f _66345 t)). Qed.
Lemma lem5097736 {A B : Type'} (s : A -> Prop) (f : A -> B) (_66345 : A) (t : B -> Prop) : (term211 A B s f _66345 t) = (term215 A B s f _66345 t).
Proof. exact (MK_COMB (@lem5097734 A _66345 s) (@lem5097735 A B f _66345 t)). Qed.
Lemma lem5097737 {A B : Type'} (s : A -> Prop) (f : A -> B) (_66345 : A) (t : B -> Prop) : (term207 A B f t _66345 s) = (term215 A B s f _66345 t).
Proof. exact (TRANS (@lem5097729 A B s f _66345 t) (@lem5097736 A B s f _66345 t)). Qed.
Lemma lem5097740 {A B : Type'} (_66345 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term215 A B s f _66345 t.
Proof. exact (EQ_MP (@lem5097737 A B s f _66345 t) (@lem5097726 A B _66345 s t g f h1)). Qed.
Lemma lem5097741 {A B : Type'} (_66345 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term215 A B s f _66345 t.
Proof. exact (@lem5097740 A B _66345 s t g f h1). Qed.
Lemma lem5097742 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term215 A B s f x t.
Proof. exact (@lem5097741 A B x s t g f h1). Qed.
Lemma lem5097745 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f x) : term122 A B f x t.
Proof. exact (@lem5097742 A B x s t g f h1 (@lem5097697 A B s t g f x h2)). Qed.
Lemma lem5097746 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f x) : term216 A B f x t.
Proof. exact (fun h0 : term192 A B f x t => @lem5097745 A B s t g f x h1 h2). Qed.
Lemma lem5097748 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5097749 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term216 A B f x t) = (term122 A B f x t).
Proof. exact (@lem5097748 (term122 A B f x t)). Qed.
Lemma lem5097750 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f x) : term122 A B f x t.
Proof. exact (EQ_MP (@lem5097749 A B f x t) (@lem5097746 A B s t g f x h1 h2)). Qed.
Lemma lem5097753 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5097755 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) : (term192 A B f x t) = (term217 A B f x t).
Proof. exact (@lem5097753 (term122 A B f x t)). Qed.
Lemma lem5097758 {A B : Type'} (f : A -> B) (x : A) (t : B -> Prop) (h1 : term192 A B f x t) : term217 A B f x t.
Proof. exact (EQ_MP (@lem5097755 A B f x t) (@lem5097520 A B f x t h1)). Qed.
Lemma lem5097761 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : False.
Proof. exact (@lem5097758 A B f x t h2 (@lem5097750 A B s t g f x h1 h3)). Qed.
Lemma lem5097762 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : term218.
Proof. exact (fun h0 : ~ False => @lem5097761 A B s t g f x h1 h2 h3). Qed.
Lemma lem5097764 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5097765 : term218 = False.
Proof. exact (@lem5097764 False). Qed.
Lemma lem5097766 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5097765) (@lem5097762 A B s t g f x h1 h2 h3)). Qed.
Lemma lem5097830 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : @IN A x s.
Proof. exact (proj1 (@lem5097251 A B s t g f x h1)). Qed.
Lemma lem5097831 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : term205 A x s.
Proof. exact (fun h0 : term189 A x s => @lem5097830 A B s t g f x h1). Qed.
Lemma lem5097833 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5097834 {A : Type'} (x : A) (s : A -> Prop) : (term205 A x s) = (@IN A x s).
Proof. exact (@lem5097833 (@IN A x s)). Qed.
Lemma lem5097835 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term126 A B s t g f x) : @IN A x s.
Proof. exact (EQ_MP (@lem5097834 A x s) (@lem5097831 A B s t g f x h1)). Qed.
Lemma lem5097841 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5097842 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : (term202 A B s g f _66347) = (term219 A B g f _66347 s).
Proof. exact (@lem5097841 ((term123 A B g f _66347) = _66347) (term189 A _66347 s)). Qed.
Lemma lem5097850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5097851 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : (term220 A B s g f _66347) = (term221 A B g f _66347 s).
Proof. exact (MK_COMB (@lem5097850) (@lem5097842 A B g f _66347 s)). Qed.
Lemma lem5097859 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : (term219 A B g f _66347 s) = (term219 A B g f _66347 s).
Proof. exact (eq_refl (term219 A B g f _66347 s)). Qed.
Lemma lem5097860 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : ((term202 A B s g f _66347) = (term219 A B g f _66347 s)) = ((term219 A B g f _66347 s) = (term219 A B g f _66347 s)).
Proof. exact (MK_COMB (@lem5097851 A B g f _66347 s) (@lem5097859 A B g f _66347 s)). Qed.
Lemma lem5097862 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5097863 (x : Prop) : (x = x) = True.
Proof. exact (@lem5097862 Prop x). Qed.
Lemma lem5097864 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : ((term219 A B g f _66347 s) = (term219 A B g f _66347 s)) = True.
Proof. exact (@lem5097863 (term219 A B g f _66347 s)). Qed.
Lemma lem5097865 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : ((term202 A B s g f _66347) = (term219 A B g f _66347 s)) = True.
Proof. exact (TRANS (@lem5097860 A B g f _66347 s) (@lem5097864 A B g f _66347 s)). Qed.
Lemma lem5097866 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : True = ((term202 A B s g f _66347) = (term219 A B g f _66347 s)).
Proof. exact (SYM (@lem5097865 A B g f _66347 s)). Qed.
Lemma lem5097867 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) (s : A -> Prop) : (term202 A B s g f _66347) = (term219 A B g f _66347 s).
Proof. exact (EQ_MP (@lem5097866 A B g f _66347 s) (@lem0)). Qed.
Lemma lem5097868 {A B : Type'} (_66347 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term219 A B g f _66347 s.
Proof. exact (EQ_MP (@lem5097867 A B g f _66347 s) (@lem5097572 A B _66347 s t g f h1)). Qed.
Lemma lem5097870 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5097871 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66347 : A) : (term219 A B g f _66347 s) = (term222 A B s g f _66347).
Proof. exact (@lem5097870 (term189 A _66347 s) ((term123 A B g f _66347) = _66347)). Qed.
Lemma lem5097873 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5097874 {A : Type'} (_66347 : A) (s : A -> Prop) : (term212 A _66347 s) = (@IN A _66347 s).
Proof. exact (@lem5097873 (@IN A _66347 s)). Qed.
Lemma lem5097875 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5097876 {A : Type'} (_66347 : A) (s : A -> Prop) : (term213 A _66347 s) = (term214 A _66347 s).
Proof. exact (MK_COMB (@lem5097875) (@lem5097874 A _66347 s)). Qed.
Lemma lem5097877 {A B : Type'} (g : B -> A) (f : A -> B) (_66347 : A) : ((term123 A B g f _66347) = _66347) = ((term123 A B g f _66347) = _66347).
Proof. exact (eq_refl ((term123 A B g f _66347) = _66347)). Qed.
Lemma lem5097878 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66347 : A) : (term222 A B s g f _66347) = (term223 A B s g f _66347).
Proof. exact (MK_COMB (@lem5097876 A _66347 s) (@lem5097877 A B g f _66347)). Qed.
Lemma lem5097879 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66347 : A) : (term219 A B g f _66347 s) = (term223 A B s g f _66347).
Proof. exact (TRANS (@lem5097871 A B s g f _66347) (@lem5097878 A B s g f _66347)). Qed.
Lemma lem5097882 {A B : Type'} (_66347 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term223 A B s g f _66347.
Proof. exact (EQ_MP (@lem5097879 A B s g f _66347) (@lem5097868 A B _66347 s t g f h1)). Qed.
Lemma lem5097883 {A B : Type'} (_66347 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term223 A B s g f _66347.
Proof. exact (@lem5097882 A B _66347 s t g f h1). Qed.
Lemma lem5097884 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term223 A B s g f x.
Proof. exact (@lem5097883 A B x s t g f h1). Qed.
Lemma lem5097887 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f x) : (term123 A B g f x) = x.
Proof. exact (@lem5097884 A B x s t g f h1 (@lem5097835 A B s t g f x h2)). Qed.
Lemma lem5097888 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f x) : term224 A B g f x.
Proof. exact (fun h0 : term193 A B g f x => @lem5097887 A B s t g f x h1 h2). Qed.
Lemma lem5097890 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5097891 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term224 A B g f x) = ((term123 A B g f x) = x).
Proof. exact (@lem5097890 ((term123 A B g f x) = x)). Qed.
Lemma lem5097892 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f x) : (term123 A B g f x) = x.
Proof. exact (EQ_MP (@lem5097891 A B g f x) (@lem5097888 A B s t g f x h1 h2)). Qed.
Lemma lem5097895 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5097897 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) : (term193 A B g f x) = (term225 A B g f x).
Proof. exact (@lem5097895 ((term123 A B g f x) = x)). Qed.
Lemma lem5097900 {A B : Type'} (g : B -> A) (f : A -> B) (x : A) (h1 : term193 A B g f x) : term225 A B g f x.
Proof. exact (EQ_MP (@lem5097897 A B g f x) (@lem5097548 A B g f x h1)). Qed.
Lemma lem5097903 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : False.
Proof. exact (@lem5097900 A B g f x h2 (@lem5097892 A B s t g f x h1 h3)). Qed.
Lemma lem5097904 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : term218.
Proof. exact (fun h0 : ~ False => @lem5097903 A B s t g f x h1 h2 h3). Qed.
Lemma lem5097906 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5097907 : term218 = False.
Proof. exact (@lem5097906 False). Qed.
Lemma lem5097908 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5097907) (@lem5097904 A B s t g f x h1 h2 h3)). Qed.
Lemma lem5097972 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : @IN B y t.
Proof. exact (proj1 (@lem5097252 A B t s f g y h1)). Qed.
Lemma lem5097973 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : term205 B y t.
Proof. exact (fun h0 : term189 B y t => @lem5097972 A B t s f g y h1). Qed.
Lemma lem5097975 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5097976 {B : Type'} (y : B) (t : B -> Prop) : (term205 B y t) = (@IN B y t).
Proof. exact (@lem5097975 (@IN B y t)). Qed.
Lemma lem5097977 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : @IN B y t.
Proof. exact (EQ_MP (@lem5097976 B y t) (@lem5097973 A B t s f g y h1)). Qed.
Lemma lem5097983 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5097984 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : (term203 A B t g _66350 s) = (term226 A B g s _66350 t).
Proof. exact (@lem5097983 (term139 A B g _66350 s) (term189 B _66350 t)). Qed.
Lemma lem5097990 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5097991 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : (term227 A B t g _66350 s) = (term228 A B g s _66350 t).
Proof. exact (MK_COMB (@lem5097990) (@lem5097984 A B g s _66350 t)). Qed.
Lemma lem5097997 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : (term226 A B g s _66350 t) = (term226 A B g s _66350 t).
Proof. exact (eq_refl (term226 A B g s _66350 t)). Qed.
Lemma lem5097998 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : ((term203 A B t g _66350 s) = (term226 A B g s _66350 t)) = ((term226 A B g s _66350 t) = (term226 A B g s _66350 t)).
Proof. exact (MK_COMB (@lem5097991 A B g s _66350 t) (@lem5097997 A B g s _66350 t)). Qed.
Lemma lem5098000 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5098001 (x : Prop) : (x = x) = True.
Proof. exact (@lem5098000 Prop x). Qed.
Lemma lem5098002 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : ((term226 A B g s _66350 t) = (term226 A B g s _66350 t)) = True.
Proof. exact (@lem5098001 (term226 A B g s _66350 t)). Qed.
Lemma lem5098003 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : ((term203 A B t g _66350 s) = (term226 A B g s _66350 t)) = True.
Proof. exact (TRANS (@lem5097998 A B g s _66350 t) (@lem5098002 A B g s _66350 t)). Qed.
Lemma lem5098004 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : True = ((term203 A B t g _66350 s) = (term226 A B g s _66350 t)).
Proof. exact (SYM (@lem5098003 A B g s _66350 t)). Qed.
Lemma lem5098005 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66350 : B) (t : B -> Prop) : (term203 A B t g _66350 s) = (term226 A B g s _66350 t).
Proof. exact (EQ_MP (@lem5098004 A B g s _66350 t) (@lem0)). Qed.
Lemma lem5098006 {A B : Type'} (_66350 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term226 A B g s _66350 t.
Proof. exact (EQ_MP (@lem5098005 A B g s _66350 t) (@lem5097582 A B _66350 t s f g h1)). Qed.
Lemma lem5098008 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5098009 {A B : Type'} (t : B -> Prop) (g : B -> A) (_66350 : B) (s : A -> Prop) : (term226 A B g s _66350 t) = (term229 A B t g _66350 s).
Proof. exact (@lem5098008 (term189 B _66350 t) (term139 A B g _66350 s)). Qed.
Lemma lem5098011 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5098012 {B : Type'} (_66350 : B) (t : B -> Prop) : (term212 B _66350 t) = (@IN B _66350 t).
Proof. exact (@lem5098011 (@IN B _66350 t)). Qed.
Lemma lem5098013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5098014 {B : Type'} (_66350 : B) (t : B -> Prop) : (term213 B _66350 t) = (term214 B _66350 t).
Proof. exact (MK_COMB (@lem5098013) (@lem5098012 B _66350 t)). Qed.
Lemma lem5098015 {A B : Type'} (g : B -> A) (_66350 : B) (s : A -> Prop) : (term139 A B g _66350 s) = (term139 A B g _66350 s).
Proof. exact (eq_refl (term139 A B g _66350 s)). Qed.
Lemma lem5098016 {A B : Type'} (t : B -> Prop) (g : B -> A) (_66350 : B) (s : A -> Prop) : (term229 A B t g _66350 s) = (term230 A B t g _66350 s).
Proof. exact (MK_COMB (@lem5098014 B _66350 t) (@lem5098015 A B g _66350 s)). Qed.
Lemma lem5098017 {A B : Type'} (t : B -> Prop) (g : B -> A) (_66350 : B) (s : A -> Prop) : (term226 A B g s _66350 t) = (term230 A B t g _66350 s).
Proof. exact (TRANS (@lem5098009 A B t g _66350 s) (@lem5098016 A B t g _66350 s)). Qed.
Lemma lem5098020 {A B : Type'} (_66350 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term230 A B t g _66350 s.
Proof. exact (EQ_MP (@lem5098017 A B t g _66350 s) (@lem5098006 A B _66350 t s f g h1)). Qed.
Lemma lem5098021 {A B : Type'} (_66350 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term230 A B t g _66350 s.
Proof. exact (@lem5098020 A B _66350 t s f g h1). Qed.
Lemma lem5098022 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term230 A B t g y s.
Proof. exact (@lem5098021 A B y t s f g h1). Qed.
Lemma lem5098025 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g y) : term139 A B g y s.
Proof. exact (@lem5098022 A B y t s f g h1 (@lem5097977 A B t s f g y h2)). Qed.
Lemma lem5098026 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g y) : term231 A B g y s.
Proof. exact (fun h0 : term197 A B g y s => @lem5098025 A B t s f g y h1 h2). Qed.
Lemma lem5098028 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5098029 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term231 A B g y s) = (term139 A B g y s).
Proof. exact (@lem5098028 (term139 A B g y s)). Qed.
Lemma lem5098030 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g y) : term139 A B g y s.
Proof. exact (EQ_MP (@lem5098029 A B g y s) (@lem5098026 A B t s f g y h1 h2)). Qed.
Lemma lem5098033 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5098035 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) : (term197 A B g y s) = (term232 A B g y s).
Proof. exact (@lem5098033 (term139 A B g y s)). Qed.
Lemma lem5098038 {A B : Type'} (g : B -> A) (y : B) (s : A -> Prop) (h1 : term197 A B g y s) : term232 A B g y s.
Proof. exact (EQ_MP (@lem5098035 A B g y s) (@lem5097576 A B g y s h1)). Qed.
Lemma lem5098041 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : False.
Proof. exact (@lem5098038 A B g y s h2 (@lem5098030 A B t s f g y h1 h3)). Qed.
Lemma lem5098042 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : term218.
Proof. exact (fun h0 : ~ False => @lem5098041 A B t s f g y h1 h2 h3). Qed.
Lemma lem5098044 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5098045 : term218 = False.
Proof. exact (@lem5098044 False). Qed.
Lemma lem5098046 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098045) (@lem5098042 A B t s f g y h1 h2 h3)). Qed.
Lemma lem5098110 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : @IN B y t.
Proof. exact (proj1 (@lem5097252 A B t s f g y h1)). Qed.
Lemma lem5098111 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : term205 B y t.
Proof. exact (fun h0 : term189 B y t => @lem5098110 A B t s f g y h1). Qed.
Lemma lem5098113 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5098114 {B : Type'} (y : B) (t : B -> Prop) : (term205 B y t) = (@IN B y t).
Proof. exact (@lem5098113 (@IN B y t)). Qed.
Lemma lem5098115 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term142 A B t s f g y) : @IN B y t.
Proof. exact (EQ_MP (@lem5098114 B y t) (@lem5098111 A B t s f g y h1)). Qed.
Lemma lem5098121 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5098122 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : (term204 A B t f g _66352) = (term233 A B f g _66352 t).
Proof. exact (@lem5098121 ((term140 A B f g _66352) = _66352) (term189 B _66352 t)). Qed.
Lemma lem5098130 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5098131 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : (term234 A B t f g _66352) = (term235 A B f g _66352 t).
Proof. exact (MK_COMB (@lem5098130) (@lem5098122 A B f g _66352 t)). Qed.
Lemma lem5098139 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : (term233 A B f g _66352 t) = (term233 A B f g _66352 t).
Proof. exact (eq_refl (term233 A B f g _66352 t)). Qed.
Lemma lem5098140 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : ((term204 A B t f g _66352) = (term233 A B f g _66352 t)) = ((term233 A B f g _66352 t) = (term233 A B f g _66352 t)).
Proof. exact (MK_COMB (@lem5098131 A B f g _66352 t) (@lem5098139 A B f g _66352 t)). Qed.
Lemma lem5098142 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5098143 (x : Prop) : (x = x) = True.
Proof. exact (@lem5098142 Prop x). Qed.
Lemma lem5098144 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : ((term233 A B f g _66352 t) = (term233 A B f g _66352 t)) = True.
Proof. exact (@lem5098143 (term233 A B f g _66352 t)). Qed.
Lemma lem5098145 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : ((term204 A B t f g _66352) = (term233 A B f g _66352 t)) = True.
Proof. exact (TRANS (@lem5098140 A B f g _66352 t) (@lem5098144 A B f g _66352 t)). Qed.
Lemma lem5098146 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : True = ((term204 A B t f g _66352) = (term233 A B f g _66352 t)).
Proof. exact (SYM (@lem5098145 A B f g _66352 t)). Qed.
Lemma lem5098147 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) (t : B -> Prop) : (term204 A B t f g _66352) = (term233 A B f g _66352 t).
Proof. exact (EQ_MP (@lem5098146 A B f g _66352 t) (@lem0)). Qed.
Lemma lem5098148 {A B : Type'} (_66352 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term233 A B f g _66352 t.
Proof. exact (EQ_MP (@lem5098147 A B f g _66352 t) (@lem5097616 A B _66352 t s f g h1)). Qed.
Lemma lem5098150 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5098151 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66352 : B) : (term233 A B f g _66352 t) = (term236 A B t f g _66352).
Proof. exact (@lem5098150 (term189 B _66352 t) ((term140 A B f g _66352) = _66352)). Qed.
Lemma lem5098153 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5098154 {B : Type'} (_66352 : B) (t : B -> Prop) : (term212 B _66352 t) = (@IN B _66352 t).
Proof. exact (@lem5098153 (@IN B _66352 t)). Qed.
Lemma lem5098155 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5098156 {B : Type'} (_66352 : B) (t : B -> Prop) : (term213 B _66352 t) = (term214 B _66352 t).
Proof. exact (MK_COMB (@lem5098155) (@lem5098154 B _66352 t)). Qed.
Lemma lem5098157 {A B : Type'} (f : A -> B) (g : B -> A) (_66352 : B) : ((term140 A B f g _66352) = _66352) = ((term140 A B f g _66352) = _66352).
Proof. exact (eq_refl ((term140 A B f g _66352) = _66352)). Qed.
Lemma lem5098158 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66352 : B) : (term236 A B t f g _66352) = (term237 A B t f g _66352).
Proof. exact (MK_COMB (@lem5098156 B _66352 t) (@lem5098157 A B f g _66352)). Qed.
Lemma lem5098159 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66352 : B) : (term233 A B f g _66352 t) = (term237 A B t f g _66352).
Proof. exact (TRANS (@lem5098151 A B t f g _66352) (@lem5098158 A B t f g _66352)). Qed.
Lemma lem5098162 {A B : Type'} (_66352 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term237 A B t f g _66352.
Proof. exact (EQ_MP (@lem5098159 A B t f g _66352) (@lem5098148 A B _66352 t s f g h1)). Qed.
Lemma lem5098163 {A B : Type'} (_66352 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term237 A B t f g _66352.
Proof. exact (@lem5098162 A B _66352 t s f g h1). Qed.
Lemma lem5098164 {A B : Type'} (y : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term237 A B t f g y.
Proof. exact (@lem5098163 A B y t s f g h1). Qed.
Lemma lem5098167 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g y) : (term140 A B f g y) = y.
Proof. exact (@lem5098164 A B y t s f g h1 (@lem5098115 A B t s f g y h2)). Qed.
Lemma lem5098168 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g y) : term238 A B f g y.
Proof. exact (fun h0 : term198 A B f g y => @lem5098167 A B t s f g y h1 h2). Qed.
Lemma lem5098170 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5098171 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term238 A B f g y) = ((term140 A B f g y) = y).
Proof. exact (@lem5098170 ((term140 A B f g y) = y)). Qed.
Lemma lem5098172 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g y) : (term140 A B f g y) = y.
Proof. exact (EQ_MP (@lem5098171 A B f g y) (@lem5098168 A B t s f g y h1 h2)). Qed.
Lemma lem5098175 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5098177 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) : (term198 A B f g y) = (term239 A B f g y).
Proof. exact (@lem5098175 ((term140 A B f g y) = y)). Qed.
Lemma lem5098180 {A B : Type'} (f : A -> B) (g : B -> A) (y : B) (h1 : term198 A B f g y) : term239 A B f g y.
Proof. exact (EQ_MP (@lem5098177 A B f g y) (@lem5097604 A B f g y h1)). Qed.
Lemma lem5098183 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : False.
Proof. exact (@lem5098180 A B f g y h2 (@lem5098172 A B t s f g y h1 h3)). Qed.
Lemma lem5098184 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : term218.
Proof. exact (fun h0 : ~ False => @lem5098183 A B t s f g y h1 h2 h3). Qed.
Lemma lem5098186 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5098187 : term218 = False.
Proof. exact (@lem5098186 False). Qed.
Lemma lem5098188 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098187) (@lem5098184 A B t s f g y h1 h2 h3)). Qed.
Lemma lem5098189 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : (term198 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term198 A B f g y => @lem5098188 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5097604 A B f g y h2)). Qed.
Lemma lem5098190 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098189 A B t s f g y h1 h2 h3) (@lem5097604 A B f g y h2)). Qed.
Lemma lem5098191 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : (term197 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term197 A B g y s => @lem5098046 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5097576 A B g y s h2)). Qed.
Lemma lem5098192 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098191 A B t s f g y h1 h2 h3) (@lem5097576 A B g y s h2)). Qed.
Lemma lem5098193 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : (term193 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term193 A B g f x => @lem5097908 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5097548 A B g f x h2)). Qed.
Lemma lem5098194 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5098193 A B s t g f x h1 h2 h3) (@lem5097548 A B g f x h2)). Qed.
Lemma lem5098195 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : (term192 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term192 A B f x t => @lem5097766 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5097520 A B f x t h2)). Qed.
Lemma lem5098196 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5098195 A B s t g f x h1 h2 h3) (@lem5097520 A B f x t h2)). Qed.
Lemma lem5098197 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : (term198 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term198 A B f g y => @lem5098190 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5097476 A B f g y h2)). Qed.
Lemma lem5098198 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098197 A B t s f g y h1 h2 h3) (@lem5097476 A B f g y h2)). Qed.
Lemma lem5098199 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : (term197 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term197 A B g y s => @lem5098192 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5097422 A B g y s h2)). Qed.
Lemma lem5098200 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098199 A B t s f g y h1 h2 h3) (@lem5097422 A B g y s h2)). Qed.
Lemma lem5098201 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : (term193 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term193 A B g f x => @lem5098194 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5097368 A B g f x h2)). Qed.
Lemma lem5098202 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5098201 A B s t g f x h1 h2 h3) (@lem5097368 A B g f x h2)). Qed.
Lemma lem5098203 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : (term192 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term192 A B f x t => @lem5098196 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5097314 A B f x t h2)). Qed.
Lemma lem5098204 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5098203 A B s t g f x h1 h2 h3) (@lem5097314 A B f x t h2)). Qed.
Lemma lem5098205 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : (term198 A B f g y) = False.
Proof. exact (prop_ext (fun h4 : term198 A B f g y => @lem5098198 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5097476 A B f g y h2)). Qed.
Lemma lem5098206 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g y) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098205 A B t s f g y h1 h2 h3) (@lem5097476 A B f g y h2)). Qed.
Lemma lem5098207 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : (term197 A B g y s) = False.
Proof. exact (prop_ext (fun h4 : term197 A B g y s => @lem5098200 A B t s f g y h1 h2 h3) (fun h4 : False => @lem5097422 A B g y s h2)). Qed.
Lemma lem5098208 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term197 A B g y s) (h3 : term142 A B t s f g y) : False.
Proof. exact (EQ_MP (@lem5098207 A B t s f g y h1 h2 h3) (@lem5097422 A B g y s h2)). Qed.
Lemma lem5098209 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : (term193 A B g f x) = False.
Proof. exact (prop_ext (fun h4 : term193 A B g f x => @lem5098202 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5097368 A B g f x h2)). Qed.
Lemma lem5098210 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f x) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5098209 A B s t g f x h1 h2 h3) (@lem5097368 A B g f x h2)). Qed.
Lemma lem5098211 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : (term192 A B f x t) = False.
Proof. exact (prop_ext (fun h4 : term192 A B f x t => @lem5098204 A B s t g f x h1 h2 h3) (fun h4 : False => @lem5097314 A B f x t h2)). Qed.
Lemma lem5098212 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term192 A B f x t) (h3 : term126 A B s t g f x) : False.
Proof. exact (EQ_MP (@lem5098211 A B s t g f x h1 h2 h3) (@lem5097314 A B f x t h2)). Qed.
Lemma lem5098213 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g y) : False.
Proof. exact (or_elim (@lem5097257 A B t s f g y h2) (fun h0 : term197 A B g y s => @lem5098208 A B t s f g y h1 h0 h2) (fun h0 : term198 A B f g y => @lem5098206 A B t s f g y h1 h0 h2)). Qed.
Lemma lem5098214 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f x) : False.
Proof. exact (or_elim (@lem5097253 A B s t g f x h2) (fun h0 : term192 A B f x t => @lem5098212 A B s t g f x h1 h0 h2) (fun h0 : term193 A B g f x => @lem5098210 A B s t g f x h1 h0 h2)). Qed.
Lemma lem5098215 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term182 A B x t s f g y) : False.
Proof. exact (or_elim (@lem5097250 A B x t s f g y h3) (fun h0 : term126 A B s t g f x => @lem5098214 A B s t g f x h1 h0) (fun h0 : term142 A B t s f g y => @lem5098213 A B t s f g y h2 h0)). Qed.
Lemma lem5098216 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term182 A B x t s f g y) : (term182 A B x t s f g y) = False.
Proof. exact (prop_ext (fun h4 : term182 A B x t s f g y => @lem5098215 A B x t s f g y h1 h2 h3) (fun h4 : False => @lem5097250 A B x t s f g y h3)). Qed.
Lemma lem5098217 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term182 A B x t s f g y) : False.
Proof. exact (EQ_MP (@lem5098216 A B x t s f g y h1 h2 h3) (@lem5097250 A B x t s f g y h3)). Qed.
Lemma lem5098218 {A B : Type'} (x : A) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term185 A B x t s f g) : False.
Proof. exact (ex_elim (@lem5097117 A B x t s f g h3) (fun y : B => fun h0 : term184 A B x t s f g y => @lem5098217 A B x t s f g y h1 h2 h0)). Qed.
Lemma lem5098219 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term79 A B t s f g) : False.
Proof. exact (ex_elim (@lem5097116 A B t s f g h3) (fun x : A => fun h0 : term186 A B t s f g x => @lem5098218 A B x t s f g h1 h2 h0)). Qed.
Lemma lem5098220 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term79 A B t s f g) : (term79 A B t s f g) = False.
Proof. exact (prop_ext (fun h4 : term79 A B t s f g => @lem5098219 A B t s f g h1 h2 h3) (fun h4 : False => @lem5096781 A B t s f g h3)). Qed.
Lemma lem5098221 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term79 A B t s f g) : False.
Proof. exact (EQ_MP (@lem5098220 A B t s f g h1 h2 h3) (@lem5096781 A B t s f g h3)). Qed.
Lemma lem5098222 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term78 A B t s f g.
Proof. exact (fun h0 : term79 A B t s f g => @lem5098221 A B t s f g h1 h2 h0). Qed.
Lemma lem5098223 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term63 A B t s f g.
Proof. exact (EQ_MP (@lem5096780 A B t s f g) (@lem5098222 A B t s f g h1 h2)). Qed.
Lemma lem5098224 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term88 A B t s f g.
Proof. exact (fun h0 : term42 A B t s f g => @lem5098223 A B t s f g h1 h0). Qed.
Lemma lem5098225 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term90 A B t s f g.
Proof. exact (fun h0 : term41 A B s t g f => @lem5098224 A B s t g f h0). Qed.
Lemma lem5098230 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : term94 A B s f g.
Proof. exact (fun t : B -> Prop => @lem5098225 A B t s f g). Qed.
Lemma lem5098235 {A B : Type'} (f : A -> B) (g : B -> A) : term98 A B f g.
Proof. exact (fun s : A -> Prop => @lem5098230 A B s f g). Qed.
Lemma lem5098240 {A B : Type'} (g : B -> A) : term102 A B g.
Proof. exact (fun f : A -> B => @lem5098235 A B f g). Qed.
Lemma lem5098245 {A B : Type'} : term106 A B.
Proof. exact (fun g : B -> A => @lem5098240 A B g). Qed.
Lemma lem5098246 {A B : Type'} : term105 A B.
Proof. exact (EQ_MP (@lem5096774 A B) (@lem5098245 A B)). Qed.
Lemma lem5098247 {A B : Type'} (g : B -> A) : term240 A B g.
Proof. exact (@lem5098246 A B g). Qed.
Lemma lem5098248 {A B : Type'} (g : B -> A) : (term240 A B g) = (term101 A B g).
Proof. exact (eq_refl (term240 A B g)). Qed.
Lemma lem5098249 {A B : Type'} (g : B -> A) : term101 A B g.
Proof. exact (EQ_MP (@lem5098248 A B g) (@lem5098247 A B g)). Qed.
Lemma lem5098250 {A B : Type'} (g : B -> A) (f : A -> B) : term241 A B g f.
Proof. exact (@lem5098249 A B g f). Qed.
Lemma lem5098251 {A B : Type'} (f : A -> B) (g : B -> A) : (term241 A B g f) = (term97 A B f g).
Proof. exact (eq_refl (term241 A B g f)). Qed.
Lemma lem5098252 {A B : Type'} (f : A -> B) (g : B -> A) : term97 A B f g.
Proof. exact (EQ_MP (@lem5098251 A B f g) (@lem5098250 A B g f)). Qed.
Lemma lem5098253 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) : term242 A B f g s.
Proof. exact (@lem5098252 A B f g s). Qed.
Lemma lem5098254 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : (term242 A B f g s) = (term93 A B s f g).
Proof. exact (eq_refl (term242 A B f g s)). Qed.
Lemma lem5098255 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) : term93 A B s f g.
Proof. exact (EQ_MP (@lem5098254 A B s f g) (@lem5098253 A B f g s)). Qed.
Lemma lem5098256 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (t : B -> Prop) : term243 A B s f g t.
Proof. exact (@lem5098255 A B s f g t). Qed.
Lemma lem5098257 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term243 A B s f g t) = (term80 A B t s f g).
Proof. exact (eq_refl (term243 A B s f g t)). Qed.
Lemma lem5098258 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term80 A B t s f g.
Proof. exact (EQ_MP (@lem5098257 A B t s f g) (@lem5098256 A B s f g t)). Qed.
Lemma lem5098260 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : term80 A B t s f g.
Proof. exact (@lem5096530 A B t s f g (@lem5098258 A B t s f g)). Qed.
Lemma lem5098261 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term87 A B t s f g.
Proof. exact (@lem5098260 A B t s f g (@lem5096502 A B s t g f h1)). Qed.
Lemma lem5098262 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term78 A B t s f g.
Proof. exact (@lem5098261 A B s t g f h1 (@lem5096501 A B t s f g h2)). Qed.
Lemma lem5098263 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term79 A B t s f g) : False.
Proof. exact (@lem5098262 A B t s f g h1 h2 (@lem5096514 A B t s f g h3)). Qed.
Lemma lem5098264 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term79 A B t s f g) : (term79 A B t s f g) = False.
Proof. exact (prop_ext (fun h4 : term79 A B t s f g => @lem5098263 A B t s f g h1 h2 h3) (fun h4 : False => @lem5096514 A B t s f g h3)). Qed.
Lemma lem5098265 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term79 A B t s f g) : False.
Proof. exact (EQ_MP (@lem5098264 A B t s f g h1 h2 h3) (@lem5096514 A B t s f g h3)). Qed.
Lemma lem5098266 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term78 A B t s f g.
Proof. exact (fun h0 : term79 A B t s f g => @lem5098265 A B t s f g h1 h2 h0). Qed.
Lemma lem5098267 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term63 A B t s f g.
Proof. exact (EQ_MP (@lem5096513 A B t s f g) (@lem5098266 A B t s f g h1 h2)). Qed.
Lemma lem5098269 (p : Prop) : p = (term77 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5098270 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term244 A B s t g f) = (term245 A B s t g f).
Proof. exact (@lem5098269 (term244 A B s t g f)). Qed.
Lemma lem5098271 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term245 A B s t g f) = (term244 A B s t g f).
Proof. exact (SYM (@lem5098270 A B s t g f)). Qed.
Lemma lem5098272 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term246 A B s t g f) : term246 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5098275 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term247 A B s t g f) : term247 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5098276 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : term248 A B s t g f.
Proof. exact (fun h0 : term247 A B s t g f => @lem5098275 A B s t g f h0). Qed.
Lemma lem5098277 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term248 A B s t g f) : term248 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5098278 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term247 A B s t g f) : term247 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5098279 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term247 A B s t g f) (h2 : term248 A B s t g f) : term247 A B s t g f.
Proof. exact (@lem5098277 A B s t g f h2 (@lem5098278 A B s t g f h1)). Qed.
Lemma lem5098280 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term247 A B s t g f) : term249 A B s t g f.
Proof. exact (fun h0 : term248 A B s t g f => @lem5098279 A B s t g f h1 h0). Qed.
Lemma lem5098281 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term248 A B s t g f) : term248 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5098282 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term247 A B s t g f) (h2 : term248 A B s t g f) : term247 A B s t g f.
Proof. exact (@lem5098280 A B s t g f h1 (@lem5098281 A B s t g f h2)). Qed.
Lemma lem5098283 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term248 A B s t g f) : term248 A B s t g f.
Proof. exact (fun h0 : term247 A B s t g f => @lem5098282 A B s t g f h0 h1). Qed.
Lemma lem5098284 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : term250 A B s t g f.
Proof. exact (fun h0 : term248 A B s t g f => @lem5098283 A B s t g f h0). Qed.
Lemma lem5098287 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : term248 A B s t g f.
Proof. exact (@lem5098284 A B s t g f (@lem5098276 A B s t g f)). Qed.
Lemma lem5098288 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : term248 A B s t g f.
Proof. exact (@lem5098287 A B s t g f). Qed.
Lemma lem5098326 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem5098327 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term245 A B s t g f) = (term251 A B s t g f).
Proof. exact (@lem5098326 (term246 A B s t g f)). Qed.
Lemma lem5098329 (t : Prop) : (term85 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem5098330 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term251 A B s t g f) = (term244 A B s t g f).
Proof. exact (@lem5098329 (term244 A B s t g f)). Qed.
Lemma lem5098333 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term245 A B s t g f) = (term244 A B s t g f).
Proof. exact (TRANS (@lem5098327 A B s t g f) (@lem5098330 A B s t g f)). Qed.
Lemma lem5098350 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term86 A B t s f g) = (term86 A B t s f g).
Proof. exact (eq_refl (term86 A B t s f g)). Qed.
Lemma lem5098351 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term252 A B s t g f) = (term253 A B s t g f).
Proof. exact (MK_COMB (@lem5098350 A B t s f g) (@lem5098333 A B s t g f)). Qed.
Lemma lem5098354 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term89 A B s t g f) = (term89 A B s t g f).
Proof. exact (eq_refl (term89 A B s t g f)). Qed.
Lemma lem5098355 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term247 A B s t g f) = (term254 A B s t g f).
Proof. exact (MK_COMB (@lem5098354 A B s t g f) (@lem5098351 A B s t g f)). Qed.
Lemma lem5098358 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) : (term255 A B t g f) = (term256 A B t g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5098355 A B s t g f)). Qed.
Lemma lem5098359 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5098360 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) : (term257 A B t g f) = (term258 A B t g f).
Proof. exact (MK_COMB (@lem5098359 A) (@lem5098358 A B t g f)). Qed.
Lemma lem5098365 {A B : Type'} (g : B -> A) (f : A -> B) : (term259 A B g f) = (term260 A B g f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5098360 A B t g f)). Qed.
Lemma lem5098366 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5098367 {A B : Type'} (g : B -> A) (f : A -> B) : (term261 A B g f) = (term262 A B g f).
Proof. exact (MK_COMB (@lem5098366 B) (@lem5098365 A B g f)). Qed.
Lemma lem5098372 {A B : Type'} (f : A -> B) : (term263 A B f) = (term264 A B f).
Proof. exact (fun_ext (fun g : B -> A => @lem5098367 A B g f)). Qed.
Lemma lem5098373 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5098374 {A B : Type'} (f : A -> B) : (term265 A B f) = (term266 A B f).
Proof. exact (MK_COMB (@lem5098373 A B) (@lem5098372 A B f)). Qed.
Lemma lem5098379 {A B : Type'} : (term267 A B) = (term268 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5098374 A B f)). Qed.
Lemma lem5098380 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5098389 {A B : Type'} : (term269 A B) = (term270 A B).
Proof. exact (MK_COMB (@lem5098380 A B) (@lem5098379 A B)). Qed.
Lemma lem5098398 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term109 A B s t g f y) = (term109 A B s t g f y).
Proof. exact (eq_refl (term109 A B s t g f y)). Qed.
Lemma lem5098399 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term110 A B s t g f) = (term110 A B s t g f).
Proof. exact (fun_ext (fun y : A => @lem5098398 A B s t g f y)). Qed.
Lemma lem5098400 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5098401 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term41 A B s t g f) = (term41 A B s t g f).
Proof. exact (MK_COMB (@lem5098400 A) (@lem5098399 A B s t g f)). Qed.
Lemma lem5098410 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term107 A B t s f g x) = (term107 A B t s f g x).
Proof. exact (eq_refl (term107 A B t s f g x)). Qed.
Lemma lem5098411 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term108 A B t s f g) = (term108 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem5098410 A B t s f g x)). Qed.
Lemma lem5098412 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5098413 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term42 A B t s f g) = (term42 A B t s f g).
Proof. exact (MK_COMB (@lem5098412 B) (@lem5098411 A B t s f g)). Qed.
Lemma lem5098414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5098415 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term271 A B t s f g) = (term271 A B t s f g).
Proof. exact (MK_COMB (@lem5098414) (@lem5098413 A B t s f g)). Qed.
Lemma lem5098416 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term244 A B s t g f) = (term244 A B s t g f).
Proof. exact (MK_COMB (@lem5098415 A B t s f g) (@lem5098401 A B s t g f)). Qed.
Lemma lem5098425 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term107 A B t s f g y) = (term107 A B t s f g y).
Proof. exact (eq_refl (term107 A B t s f g y)). Qed.
Lemma lem5098426 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term108 A B t s f g) = (term108 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5098425 A B t s f g y)). Qed.
Lemma lem5098427 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5098428 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term42 A B t s f g) = (term42 A B t s f g).
Proof. exact (MK_COMB (@lem5098427 B) (@lem5098426 A B t s f g)). Qed.
Lemma lem5098429 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5098430 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term86 A B t s f g) = (term86 A B t s f g).
Proof. exact (MK_COMB (@lem5098429) (@lem5098428 A B t s f g)). Qed.
Lemma lem5098431 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term253 A B s t g f) = (term253 A B s t g f).
Proof. exact (MK_COMB (@lem5098430 A B t s f g) (@lem5098416 A B s t g f)). Qed.
Lemma lem5098440 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term109 A B s t g f x) = (term109 A B s t g f x).
Proof. exact (eq_refl (term109 A B s t g f x)). Qed.
Lemma lem5098441 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term110 A B s t g f) = (term110 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5098440 A B s t g f x)). Qed.
Lemma lem5098442 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5098443 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term41 A B s t g f) = (term41 A B s t g f).
Proof. exact (MK_COMB (@lem5098442 A) (@lem5098441 A B s t g f)). Qed.
Lemma lem5098444 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5098445 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term89 A B s t g f) = (term89 A B s t g f).
Proof. exact (MK_COMB (@lem5098444) (@lem5098443 A B s t g f)). Qed.
Lemma lem5098446 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term254 A B s t g f) = (term254 A B s t g f).
Proof. exact (MK_COMB (@lem5098445 A B s t g f) (@lem5098431 A B s t g f)). Qed.
Lemma lem5098447 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) : (term256 A B t g f) = (term256 A B t g f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5098446 A B s t g f)). Qed.
Lemma lem5098448 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5098449 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) : (term258 A B t g f) = (term258 A B t g f).
Proof. exact (MK_COMB (@lem5098448 A) (@lem5098447 A B t g f)). Qed.
Lemma lem5098450 {A B : Type'} (g : B -> A) (f : A -> B) : (term260 A B g f) = (term260 A B g f).
Proof. exact (fun_ext (fun t : B -> Prop => @lem5098449 A B t g f)). Qed.
Lemma lem5098451 {B : Type'} : (@all (B -> Prop)) = (@all (B -> Prop)).
Proof. exact (eq_refl (@all (B -> Prop))). Qed.
Lemma lem5098452 {A B : Type'} (g : B -> A) (f : A -> B) : (term262 A B g f) = (term262 A B g f).
Proof. exact (MK_COMB (@lem5098451 B) (@lem5098450 A B g f)). Qed.
Lemma lem5098453 {A B : Type'} (f : A -> B) : (term264 A B f) = (term264 A B f).
Proof. exact (fun_ext (fun g : B -> A => @lem5098452 A B g f)). Qed.
Lemma lem5098454 {A B : Type'} : (@all (B -> A)) = (@all (B -> A)).
Proof. exact (eq_refl (@all (B -> A))). Qed.
Lemma lem5098455 {A B : Type'} (f : A -> B) : (term266 A B f) = (term266 A B f).
Proof. exact (MK_COMB (@lem5098454 A B) (@lem5098453 A B f)). Qed.
Lemma lem5098456 {A B : Type'} : (term268 A B) = (term268 A B).
Proof. exact (fun_ext (fun f : A -> B => @lem5098455 A B f)). Qed.
Lemma lem5098457 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem5098458 {A B : Type'} : (term270 A B) = (term270 A B).
Proof. exact (MK_COMB (@lem5098457 A B) (@lem5098456 A B)). Qed.
Lemma lem5098531 {A B : Type'} : (term269 A B) = (term270 A B).
Proof. exact (TRANS (@lem5098389 A B) (@lem5098458 A B)). Qed.
Lemma lem5098532 {A B : Type'} : (term270 A B) = (term269 A B).
Proof. exact (SYM (@lem5098531 A B)). Qed.
Lemma lem5098533 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term41 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5098534 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term42 A B t s f g.
Proof. exact (h1). Qed.
Lemma lem5098536 (p : Prop) : p = (term77 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem5098537 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term244 A B s t g f) = (term245 A B s t g f).
Proof. exact (@lem5098536 (term244 A B s t g f)). Qed.
Lemma lem5098538 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term245 A B s t g f) = (term244 A B s t g f).
Proof. exact (SYM (@lem5098537 A B s t g f)). Qed.
Lemma lem5098539 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term246 A B s t g f) : term246 A B s t g f.
Proof. exact (h1). Qed.
Lemma lem5098550 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term109 A B s t g f x) = (term112 A B s t g f x).
Proof. exact (@lem17265 (@IN A x s) (term113 A B t g f x)). Qed.
Lemma lem5098551 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term110 A B s t g f) = (term114 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5098550 A B s t g f x)). Qed.
Lemma lem5098552 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5098605 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term41 A B s t g f) = (term115 A B s t g f).
Proof. exact (MK_COMB (@lem5098552 A) (@lem5098551 A B s t g f)). Qed.
Lemma lem5098606 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term115 A B s t g f.
Proof. exact (EQ_MP (@lem5098605 A B s t g f) (@lem5098533 A B s t g f h1)). Qed.
Lemma lem5098617 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term107 A B t s f g y) = (term116 A B t s f g y).
Proof. exact (@lem17265 (@IN B y t) (term117 A B s f g y)). Qed.
Lemma lem5098618 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term108 A B t s f g) = (term118 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5098617 A B t s f g y)). Qed.
Lemma lem5098619 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5098672 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term42 A B t s f g) = (term119 A B t s f g).
Proof. exact (MK_COMB (@lem5098619 B) (@lem5098618 A B t s f g)). Qed.
Lemma lem5098673 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term119 A B t s f g.
Proof. exact (EQ_MP (@lem5098672 A B t s f g) (@lem5098534 A B t s f g h1)). Qed.
Lemma lem5098681 {A B : Type'} (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term137 A B s f g x) = (term138 A B s f g x).
Proof. exact (@lem17045 (term139 A B g x s) ((term140 A B f g x) = x)). Qed.
Lemma lem5098683 {B : Type'} (x : B) (t : B -> Prop) : (term124 B x t) = (term124 B x t).
Proof. exact (eq_refl (term124 B x t)). Qed.
Lemma lem5098684 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term141 A B t s f g x) = (term142 A B t s f g x).
Proof. exact (MK_COMB (@lem5098683 B x t) (@lem5098681 A B s f g x)). Qed.
Lemma lem5098685 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term143 A B t s f g x) = (term141 A B t s f g x).
Proof. exact (@lem17362 (@IN B x t) (term117 A B s f g x)). Qed.
Lemma lem5098686 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term143 A B t s f g x) = (term142 A B t s f g x).
Proof. exact (TRANS (@lem5098685 A B t s f g x) (@lem5098684 A B t s f g x)). Qed.
Lemma lem5098687 {B : Type'} (P : B -> Prop) : (term128 B P) = (term129 B P).
Proof. exact (@lem18392 B P). Qed.
Lemma lem5098688 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term144 A B t s f g) = (term145 A B t s f g).
Proof. exact (@lem5098687 B (term108 A B t s f g)). Qed.
Lemma lem5098689 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term146 A B t s f g x) = (term107 A B t s f g x).
Proof. exact (eq_refl (term146 A B t s f g x)). Qed.
Lemma lem5098690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5098691 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term147 A B t s f g x) = (term143 A B t s f g x).
Proof. exact (MK_COMB (@lem5098690) (@lem5098689 A B t s f g x)). Qed.
Lemma lem5098692 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term147 A B t s f g x) = (term142 A B t s f g x).
Proof. exact (TRANS (@lem5098691 A B t s f g x) (@lem5098686 A B t s f g x)). Qed.
Lemma lem5098693 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term148 A B t s f g) = (term149 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem5098692 A B t s f g x)). Qed.
Lemma lem5098694 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5098695 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term145 A B t s f g) = (term150 A B t s f g).
Proof. exact (MK_COMB (@lem5098694 B) (@lem5098693 A B t s f g)). Qed.
Lemma lem5098696 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term144 A B t s f g) = (term150 A B t s f g).
Proof. exact (TRANS (@lem5098688 A B t s f g) (@lem5098695 A B t s f g)). Qed.
Lemma lem5098704 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term120 A B t g f y) = (term121 A B t g f y).
Proof. exact (@lem17045 (term122 A B f y t) ((term123 A B g f y) = y)). Qed.
Lemma lem5098706 {A : Type'} (y : A) (s : A -> Prop) : (term124 A y s) = (term124 A y s).
Proof. exact (eq_refl (term124 A y s)). Qed.
Lemma lem5098707 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term125 A B s t g f y) = (term126 A B s t g f y).
Proof. exact (MK_COMB (@lem5098706 A y s) (@lem5098704 A B t g f y)). Qed.
Lemma lem5098708 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term127 A B s t g f y) = (term125 A B s t g f y).
Proof. exact (@lem17362 (@IN A y s) (term113 A B t g f y)). Qed.
Lemma lem5098709 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term127 A B s t g f y) = (term126 A B s t g f y).
Proof. exact (TRANS (@lem5098708 A B s t g f y) (@lem5098707 A B s t g f y)). Qed.
Lemma lem5098710 {A : Type'} (P : A -> Prop) : (term128 A P) = (term129 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem5098711 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term130 A B s t g f) = (term131 A B s t g f).
Proof. exact (@lem5098710 A (term110 A B s t g f)). Qed.
Lemma lem5098712 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term132 A B s t g f y) = (term109 A B s t g f y).
Proof. exact (eq_refl (term132 A B s t g f y)). Qed.
Lemma lem5098713 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem5098714 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term133 A B s t g f y) = (term127 A B s t g f y).
Proof. exact (MK_COMB (@lem5098713) (@lem5098712 A B s t g f y)). Qed.
Lemma lem5098715 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term133 A B s t g f y) = (term126 A B s t g f y).
Proof. exact (TRANS (@lem5098714 A B s t g f y) (@lem5098709 A B s t g f y)). Qed.
Lemma lem5098716 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term134 A B s t g f) = (term135 A B s t g f).
Proof. exact (fun_ext (fun y : A => @lem5098715 A B s t g f y)). Qed.
Lemma lem5098717 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5098718 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term131 A B s t g f) = (term136 A B s t g f).
Proof. exact (MK_COMB (@lem5098717 A) (@lem5098716 A B s t g f)). Qed.
Lemma lem5098719 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term130 A B s t g f) = (term136 A B s t g f).
Proof. exact (TRANS (@lem5098711 A B s t g f) (@lem5098718 A B s t g f)). Qed.
Lemma lem5098720 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5098721 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term272 A B t s f g) = (term273 A B t s f g).
Proof. exact (MK_COMB (@lem5098720) (@lem5098696 A B t s f g)). Qed.
Lemma lem5098722 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term274 A B s t g f) = (term275 A B s t g f).
Proof. exact (MK_COMB (@lem5098721 A B t s f g) (@lem5098719 A B s t g f)). Qed.
Lemma lem5098723 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term246 A B s t g f) = (term274 A B s t g f).
Proof. exact (@lem17045 (term42 A B t s f g) (term41 A B s t g f)). Qed.
Lemma lem5098724 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term246 A B s t g f) = (term275 A B s t g f).
Proof. exact (TRANS (@lem5098723 A B s t g f) (@lem5098722 A B s t g f)). Qed.
Lemma lem5098825 {A : Type'} (P : A -> Prop) (Q : Prop) : (term155 A P Q) = (term156 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem5098826 {B : Type'} (P : B -> Prop) (Q : Prop) : (term155 B P Q) = (term156 B P Q).
Proof. exact (@lem5098825 B P Q). Qed.
Lemma lem5098827 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term276 A B s t g f) = (term277 A B s t g f).
Proof. exact (@lem5098826 B (term149 A B t s f g) (term136 A B s t g f)). Qed.
Lemma lem5098828 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term176 A B t s f g x) = (term142 A B t s f g x).
Proof. exact (eq_refl (term176 A B t s f g x)). Qed.
Lemma lem5098829 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term177 A B t s f g) = (term149 A B t s f g).
Proof. exact (fun_ext (fun x : B => @lem5098828 A B t s f g x)). Qed.
Lemma lem5098830 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5098831 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term178 A B t s f g) = (term150 A B t s f g).
Proof. exact (MK_COMB (@lem5098830 B) (@lem5098829 A B t s f g)). Qed.
Lemma lem5098832 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5098833 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term278 A B t s f g) = (term273 A B t s f g).
Proof. exact (MK_COMB (@lem5098832) (@lem5098831 A B t s f g)). Qed.
Lemma lem5098834 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term136 A B s t g f) = (term136 A B s t g f).
Proof. exact (eq_refl (term136 A B s t g f)). Qed.
Lemma lem5098835 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term276 A B s t g f) = (term275 A B s t g f).
Proof. exact (MK_COMB (@lem5098833 A B t s f g) (@lem5098834 A B s t g f)). Qed.
Lemma lem5098836 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5098837 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term279 A B s t g f) = (term280 A B s t g f).
Proof. exact (MK_COMB (@lem5098836) (@lem5098835 A B s t g f)). Qed.
Lemma lem5098838 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term176 A B t s f g x) = (term142 A B t s f g x).
Proof. exact (eq_refl (term176 A B t s f g x)). Qed.
Lemma lem5098839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem5098840 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term281 A B t s f g x) = (term282 A B t s f g x).
Proof. exact (MK_COMB (@lem5098839) (@lem5098838 A B t s f g x)). Qed.
Lemma lem5098841 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term136 A B s t g f) = (term136 A B s t g f).
Proof. exact (eq_refl (term136 A B s t g f)). Qed.
Lemma lem5098842 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term283 A B x s t g f) = (term284 A B x s t g f).
Proof. exact (MK_COMB (@lem5098840 A B t s f g x) (@lem5098841 A B s t g f)). Qed.
Lemma lem5098843 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term285 A B s t g f) = (term286 A B s t g f).
Proof. exact (fun_ext (fun x : B => @lem5098842 A B x s t g f)). Qed.
Lemma lem5098844 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5098845 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term277 A B s t g f) = (term287 A B s t g f).
Proof. exact (MK_COMB (@lem5098844 B) (@lem5098843 A B s t g f)). Qed.
Lemma lem5098846 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : ((term276 A B s t g f) = (term277 A B s t g f)) = ((term275 A B s t g f) = (term287 A B s t g f)).
Proof. exact (MK_COMB (@lem5098837 A B s t g f) (@lem5098845 A B s t g f)). Qed.
Lemma lem5098847 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term275 A B s t g f) = (term287 A B s t g f).
Proof. exact (EQ_MP (@lem5098846 A B s t g f) (@lem5098827 A B s t g f)). Qed.
Lemma lem5098849 {A : Type'} (P : Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem5098850 {A : Type'} (P : Prop) (Q : A -> Prop) : (term172 A P Q) = (term173 A P Q).
Proof. exact (@lem5098849 A P Q). Qed.
Lemma lem5098851 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term288 A B x s t g f) = (term289 A B x s t g f).
Proof. exact (@lem5098850 A (term142 A B t s f g x) (term135 A B s t g f)). Qed.
Lemma lem5098852 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term159 A B s t g f y) = (term126 A B s t g f y).
Proof. exact (eq_refl (term159 A B s t g f y)). Qed.
Lemma lem5098853 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term160 A B s t g f) = (term135 A B s t g f).
Proof. exact (fun_ext (fun y : A => @lem5098852 A B s t g f y)). Qed.
Lemma lem5098854 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5098855 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term161 A B s t g f) = (term136 A B s t g f).
Proof. exact (MK_COMB (@lem5098854 A) (@lem5098853 A B s t g f)). Qed.
Lemma lem5098856 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term282 A B t s f g x) = (term282 A B t s f g x).
Proof. exact (eq_refl (term282 A B t s f g x)). Qed.
Lemma lem5098857 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term288 A B x s t g f) = (term284 A B x s t g f).
Proof. exact (MK_COMB (@lem5098856 A B t s f g x) (@lem5098855 A B s t g f)). Qed.
Lemma lem5098858 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5098859 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term290 A B x s t g f) = (term291 A B x s t g f).
Proof. exact (MK_COMB (@lem5098858) (@lem5098857 A B x s t g f)). Qed.
Lemma lem5098860 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term159 A B s t g f y) = (term126 A B s t g f y).
Proof. exact (eq_refl (term159 A B s t g f y)). Qed.
Lemma lem5098861 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) : (term282 A B t s f g x) = (term282 A B t s f g x).
Proof. exact (eq_refl (term282 A B t s f g x)). Qed.
Lemma lem5098862 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) : (term292 A B x s t g f y) = (term293 A B x s t g f y).
Proof. exact (MK_COMB (@lem5098861 A B t s f g x) (@lem5098860 A B s t g f y)). Qed.
Lemma lem5098863 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term294 A B x s t g f) = (term295 A B x s t g f).
Proof. exact (fun_ext (fun y : A => @lem5098862 A B x s t g f y)). Qed.
Lemma lem5098864 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem5098865 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term289 A B x s t g f) = (term296 A B x s t g f).
Proof. exact (MK_COMB (@lem5098864 A) (@lem5098863 A B x s t g f)). Qed.
Lemma lem5098866 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : ((term288 A B x s t g f) = (term289 A B x s t g f)) = ((term284 A B x s t g f) = (term296 A B x s t g f)).
Proof. exact (MK_COMB (@lem5098859 A B x s t g f) (@lem5098865 A B x s t g f)). Qed.
Lemma lem5098867 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term284 A B x s t g f) = (term296 A B x s t g f).
Proof. exact (EQ_MP (@lem5098866 A B x s t g f) (@lem5098851 A B x s t g f)). Qed.
Lemma lem5098868 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term286 A B s t g f) = (term297 A B s t g f).
Proof. exact (fun_ext (fun x : B => @lem5098867 A B x s t g f)). Qed.
Lemma lem5098869 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem5098870 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term287 A B s t g f) = (term298 A B s t g f).
Proof. exact (MK_COMB (@lem5098869 B) (@lem5098868 A B s t g f)). Qed.
Lemma lem5098872 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term275 A B s t g f) = (term298 A B s t g f).
Proof. exact (TRANS (@lem5098847 A B s t g f) (@lem5098870 A B s t g f)). Qed.
Lemma lem5098873 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term246 A B s t g f) = (term298 A B s t g f).
Proof. exact (TRANS (@lem5098724 A B s t g f) (@lem5098872 A B s t g f)). Qed.
Lemma lem5098874 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term246 A B s t g f) : term298 A B s t g f.
Proof. exact (EQ_MP (@lem5098873 A B s t g f) (@lem5098539 A B s t g f h1)). Qed.
Lemma lem5098875 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term296 A B x s t g f) : term296 A B x s t g f.
Proof. exact (h1). Qed.
Lemma lem5098905 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term112 A B s t g f x) = (term112 A B s t g f x).
Proof. exact (eq_refl (term112 A B s t g f x)). Qed.
Lemma lem5098906 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term114 A B s t g f) = (term114 A B s t g f).
Proof. exact (fun_ext (fun x : A => @lem5098905 A B s t g f x)). Qed.
Lemma lem5098907 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5098908 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term115 A B s t g f) = (term115 A B s t g f).
Proof. exact (MK_COMB (@lem5098907 A) (@lem5098906 A B s t g f)). Qed.
Lemma lem5098909 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term115 A B s t g f.
Proof. exact (EQ_MP (@lem5098908 A B s t g f) (@lem5098606 A B s t g f h1)). Qed.
Lemma lem5098938 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term116 A B t s f g y) = (term116 A B t s f g y).
Proof. exact (eq_refl (term116 A B t s f g y)). Qed.
Lemma lem5098939 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term118 A B t s f g) = (term118 A B t s f g).
Proof. exact (fun_ext (fun y : B => @lem5098938 A B t s f g y)). Qed.
Lemma lem5098940 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5098941 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) : (term119 A B t s f g) = (term119 A B t s f g).
Proof. exact (MK_COMB (@lem5098940 B) (@lem5098939 A B t s f g)). Qed.
Lemma lem5098942 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term119 A B t s f g.
Proof. exact (EQ_MP (@lem5098941 A B t s f g) (@lem5098673 A B t s f g h1)). Qed.
Lemma lem5099008 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term293 A B x s t g f y) : term293 A B x s t g f y.
Proof. exact (h1). Qed.
Lemma lem5099009 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : term142 A B t s f g x.
Proof. exact (h1). Qed.
Lemma lem5099010 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : term126 A B s t g f y.
Proof. exact (h1). Qed.
Lemma lem5099011 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : term138 A B s f g x.
Proof. exact (proj2 (@lem5099009 A B t s f g x h1)). Qed.
Lemma lem5099015 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : term121 A B t g f y.
Proof. exact (proj2 (@lem5099010 A B s t g f y h1)). Qed.
Lemma lem5099059 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term116 A B t s f g y) = (term194 A B s t f g y).
Proof. exact (@lem19490 (term139 A B g y s) (term189 B y t) ((term140 A B f g y) = y)). Qed.
Lemma lem5099060 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term118 A B t s f g) = (term195 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5099059 A B s t f g y)). Qed.
Lemma lem5099061 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5099063 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term119 A B t s f g) = (term196 A B s t f g).
Proof. exact (MK_COMB (@lem5099061 B) (@lem5099060 A B s t f g)). Qed.
Lemma lem5099064 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term196 A B s t f g.
Proof. exact (EQ_MP (@lem5099063 A B s t f g) (@lem5098942 A B t s f g h1)). Qed.
Lemma lem5099072 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (h1 : term197 A B g x s) : term197 A B g x s.
Proof. exact (h1). Qed.
Lemma lem5099113 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (y : B) : (term116 A B t s f g y) = (term194 A B s t f g y).
Proof. exact (@lem19490 (term139 A B g y s) (term189 B y t) ((term140 A B f g y) = y)). Qed.
Lemma lem5099114 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term118 A B t s f g) = (term195 A B s t f g).
Proof. exact (fun_ext (fun y : B => @lem5099113 A B s t f g y)). Qed.
Lemma lem5099115 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem5099117 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) : (term119 A B t s f g) = (term196 A B s t f g).
Proof. exact (MK_COMB (@lem5099115 B) (@lem5099114 A B s t f g)). Qed.
Lemma lem5099118 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term196 A B s t f g.
Proof. exact (EQ_MP (@lem5099117 A B s t f g) (@lem5098942 A B t s f g h1)). Qed.
Lemma lem5099126 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) (h1 : term198 A B f g x) : term198 A B f g x.
Proof. exact (h1). Qed.
Lemma lem5099144 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term112 A B s t g f x) = (term188 A B t s g f x).
Proof. exact (@lem19490 (term122 A B f x t) (term189 A x s) ((term123 A B g f x) = x)). Qed.
Lemma lem5099145 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term114 A B s t g f) = (term190 A B t s g f).
Proof. exact (fun_ext (fun x : A => @lem5099144 A B t s g f x)). Qed.
Lemma lem5099146 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5099148 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term115 A B s t g f) = (term191 A B t s g f).
Proof. exact (MK_COMB (@lem5099146 A) (@lem5099145 A B t s g f)). Qed.
Lemma lem5099149 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term191 A B t s g f.
Proof. exact (EQ_MP (@lem5099148 A B t s g f) (@lem5098909 A B s t g f h1)). Qed.
Lemma lem5099180 {A B : Type'} (f : A -> B) (y : A) (t : B -> Prop) (h1 : term192 A B f y t) : term192 A B f y t.
Proof. exact (h1). Qed.
Lemma lem5099198 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (x : A) : (term112 A B s t g f x) = (term188 A B t s g f x).
Proof. exact (@lem19490 (term122 A B f x t) (term189 A x s) ((term123 A B g f x) = x)). Qed.
Lemma lem5099199 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term114 A B s t g f) = (term190 A B t s g f).
Proof. exact (fun_ext (fun x : A => @lem5099198 A B t s g f x)). Qed.
Lemma lem5099200 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5099202 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) : (term115 A B s t g f) = (term191 A B t s g f).
Proof. exact (MK_COMB (@lem5099200 A) (@lem5099199 A B t s g f)). Qed.
Lemma lem5099203 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term191 A B t s g f.
Proof. exact (EQ_MP (@lem5099202 A B t s g f) (@lem5098909 A B s t g f h1)). Qed.
Lemma lem5099234 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) (h1 : term193 A B g f y) : term193 A B g f y.
Proof. exact (h1). Qed.
Lemma lem5099238 {A B : Type'} (_66402 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term200 A B s t f g _66402.
Proof. exact (@lem5099064 A B t s f g h1 _66402). Qed.
Lemma lem5099239 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_66402 : B) : (term200 A B s t f g _66402) = (term194 A B s t f g _66402).
Proof. exact (eq_refl (term200 A B s t f g _66402)). Qed.
Lemma lem5099240 {A B : Type'} (_66402 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term194 A B s t f g _66402.
Proof. exact (EQ_MP (@lem5099239 A B s t f g _66402) (@lem5099238 A B _66402 t s f g h1)). Qed.
Lemma lem5099244 {A B : Type'} (_66404 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term200 A B s t f g _66404.
Proof. exact (@lem5099118 A B t s f g h1 _66404). Qed.
Lemma lem5099245 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (f : A -> B) (g : B -> A) (_66404 : B) : (term200 A B s t f g _66404) = (term194 A B s t f g _66404).
Proof. exact (eq_refl (term200 A B s t f g _66404)). Qed.
Lemma lem5099246 {A B : Type'} (_66404 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term194 A B s t f g _66404.
Proof. exact (EQ_MP (@lem5099245 A B s t f g _66404) (@lem5099244 A B _66404 t s f g h1)). Qed.
Lemma lem5099247 {A B : Type'} (_66405 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term199 A B t s g f _66405.
Proof. exact (@lem5099149 A B s t g f h1 _66405). Qed.
Lemma lem5099248 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (_66405 : A) : (term199 A B t s g f _66405) = (term188 A B t s g f _66405).
Proof. exact (eq_refl (term199 A B t s g f _66405)). Qed.
Lemma lem5099249 {A B : Type'} (_66405 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term188 A B t s g f _66405.
Proof. exact (EQ_MP (@lem5099248 A B t s g f _66405) (@lem5099247 A B _66405 s t g f h1)). Qed.
Lemma lem5099253 {A B : Type'} (_66407 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term199 A B t s g f _66407.
Proof. exact (@lem5099203 A B s t g f h1 _66407). Qed.
Lemma lem5099254 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (g : B -> A) (f : A -> B) (_66407 : A) : (term199 A B t s g f _66407) = (term188 A B t s g f _66407).
Proof. exact (eq_refl (term199 A B t s g f _66407)). Qed.
Lemma lem5099255 {A B : Type'} (_66407 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term188 A B t s g f _66407.
Proof. exact (EQ_MP (@lem5099254 A B t s g f _66407) (@lem5099253 A B _66407 s t g f h1)). Qed.
Lemma lem5099278 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (h1 : term197 A B g x s) : term197 A B g x s.
Proof. exact (h1). Qed.
Lemma lem5099284 {A B : Type'} (_66402 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term203 A B t g _66402 s.
Proof. exact (proj1 (@lem5099240 A B _66402 t s f g h1)). Qed.
Lemma lem5099306 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) (h1 : term198 A B f g x) : term198 A B f g x.
Proof. exact (h1). Qed.
Lemma lem5099318 {A B : Type'} (_66404 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term204 A B t f g _66404.
Proof. exact (proj2 (@lem5099246 A B _66404 t s f g h1)). Qed.
Lemma lem5099334 {A B : Type'} (f : A -> B) (y : A) (t : B -> Prop) (h1 : term192 A B f y t) : term192 A B f y t.
Proof. exact (h1). Qed.
Lemma lem5099352 {A B : Type'} (_66405 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term201 A B s f _66405 t.
Proof. exact (proj1 (@lem5099249 A B _66405 s t g f h1)). Qed.
Lemma lem5099362 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) (h1 : term193 A B g f y) : term193 A B g f y.
Proof. exact (h1). Qed.
Lemma lem5099386 {A B : Type'} (_66407 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term202 A B s g f _66407.
Proof. exact (proj2 (@lem5099255 A B _66407 s t g f h1)). Qed.
Lemma lem5099450 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : @IN B x t.
Proof. exact (proj1 (@lem5099009 A B t s f g x h1)). Qed.
Lemma lem5099451 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : term205 B x t.
Proof. exact (fun h0 : term189 B x t => @lem5099450 A B t s f g x h1). Qed.
Lemma lem5099453 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099454 {B : Type'} (x : B) (t : B -> Prop) : (term205 B x t) = (@IN B x t).
Proof. exact (@lem5099453 (@IN B x t)). Qed.
Lemma lem5099455 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : @IN B x t.
Proof. exact (EQ_MP (@lem5099454 B x t) (@lem5099451 A B t s f g x h1)). Qed.
Lemma lem5099461 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5099462 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : (term203 A B t g _66402 s) = (term226 A B g s _66402 t).
Proof. exact (@lem5099461 (term139 A B g _66402 s) (term189 B _66402 t)). Qed.
Lemma lem5099468 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5099469 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : (term227 A B t g _66402 s) = (term228 A B g s _66402 t).
Proof. exact (MK_COMB (@lem5099468) (@lem5099462 A B g s _66402 t)). Qed.
Lemma lem5099475 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : (term226 A B g s _66402 t) = (term226 A B g s _66402 t).
Proof. exact (eq_refl (term226 A B g s _66402 t)). Qed.
Lemma lem5099476 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : ((term203 A B t g _66402 s) = (term226 A B g s _66402 t)) = ((term226 A B g s _66402 t) = (term226 A B g s _66402 t)).
Proof. exact (MK_COMB (@lem5099469 A B g s _66402 t) (@lem5099475 A B g s _66402 t)). Qed.
Lemma lem5099478 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5099479 (x : Prop) : (x = x) = True.
Proof. exact (@lem5099478 Prop x). Qed.
Lemma lem5099480 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : ((term226 A B g s _66402 t) = (term226 A B g s _66402 t)) = True.
Proof. exact (@lem5099479 (term226 A B g s _66402 t)). Qed.
Lemma lem5099481 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : ((term203 A B t g _66402 s) = (term226 A B g s _66402 t)) = True.
Proof. exact (TRANS (@lem5099476 A B g s _66402 t) (@lem5099480 A B g s _66402 t)). Qed.
Lemma lem5099482 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : True = ((term203 A B t g _66402 s) = (term226 A B g s _66402 t)).
Proof. exact (SYM (@lem5099481 A B g s _66402 t)). Qed.
Lemma lem5099483 {A B : Type'} (g : B -> A) (s : A -> Prop) (_66402 : B) (t : B -> Prop) : (term203 A B t g _66402 s) = (term226 A B g s _66402 t).
Proof. exact (EQ_MP (@lem5099482 A B g s _66402 t) (@lem0)). Qed.
Lemma lem5099484 {A B : Type'} (_66402 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term226 A B g s _66402 t.
Proof. exact (EQ_MP (@lem5099483 A B g s _66402 t) (@lem5099284 A B _66402 t s f g h1)). Qed.
Lemma lem5099486 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5099487 {A B : Type'} (t : B -> Prop) (g : B -> A) (_66402 : B) (s : A -> Prop) : (term226 A B g s _66402 t) = (term229 A B t g _66402 s).
Proof. exact (@lem5099486 (term189 B _66402 t) (term139 A B g _66402 s)). Qed.
Lemma lem5099489 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5099490 {B : Type'} (_66402 : B) (t : B -> Prop) : (term212 B _66402 t) = (@IN B _66402 t).
Proof. exact (@lem5099489 (@IN B _66402 t)). Qed.
Lemma lem5099491 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5099492 {B : Type'} (_66402 : B) (t : B -> Prop) : (term213 B _66402 t) = (term214 B _66402 t).
Proof. exact (MK_COMB (@lem5099491) (@lem5099490 B _66402 t)). Qed.
Lemma lem5099493 {A B : Type'} (g : B -> A) (_66402 : B) (s : A -> Prop) : (term139 A B g _66402 s) = (term139 A B g _66402 s).
Proof. exact (eq_refl (term139 A B g _66402 s)). Qed.
Lemma lem5099494 {A B : Type'} (t : B -> Prop) (g : B -> A) (_66402 : B) (s : A -> Prop) : (term229 A B t g _66402 s) = (term230 A B t g _66402 s).
Proof. exact (MK_COMB (@lem5099492 B _66402 t) (@lem5099493 A B g _66402 s)). Qed.
Lemma lem5099495 {A B : Type'} (t : B -> Prop) (g : B -> A) (_66402 : B) (s : A -> Prop) : (term226 A B g s _66402 t) = (term230 A B t g _66402 s).
Proof. exact (TRANS (@lem5099487 A B t g _66402 s) (@lem5099494 A B t g _66402 s)). Qed.
Lemma lem5099498 {A B : Type'} (_66402 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term230 A B t g _66402 s.
Proof. exact (EQ_MP (@lem5099495 A B t g _66402 s) (@lem5099484 A B _66402 t s f g h1)). Qed.
Lemma lem5099499 {A B : Type'} (_66402 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term230 A B t g _66402 s.
Proof. exact (@lem5099498 A B _66402 t s f g h1). Qed.
Lemma lem5099500 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term230 A B t g x s.
Proof. exact (@lem5099499 A B x t s f g h1). Qed.
Lemma lem5099503 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g x) : term139 A B g x s.
Proof. exact (@lem5099500 A B x t s f g h1 (@lem5099455 A B t s f g x h2)). Qed.
Lemma lem5099504 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g x) : term231 A B g x s.
Proof. exact (fun h0 : term197 A B g x s => @lem5099503 A B t s f g x h1 h2). Qed.
Lemma lem5099506 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099507 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) : (term231 A B g x s) = (term139 A B g x s).
Proof. exact (@lem5099506 (term139 A B g x s)). Qed.
Lemma lem5099508 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g x) : term139 A B g x s.
Proof. exact (EQ_MP (@lem5099507 A B g x s) (@lem5099504 A B t s f g x h1 h2)). Qed.
Lemma lem5099511 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5099513 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) : (term197 A B g x s) = (term232 A B g x s).
Proof. exact (@lem5099511 (term139 A B g x s)). Qed.
Lemma lem5099516 {A B : Type'} (g : B -> A) (x : B) (s : A -> Prop) (h1 : term197 A B g x s) : term232 A B g x s.
Proof. exact (EQ_MP (@lem5099513 A B g x s) (@lem5099278 A B g x s h1)). Qed.
Lemma lem5099519 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : False.
Proof. exact (@lem5099516 A B g x s h2 (@lem5099508 A B t s f g x h1 h3)). Qed.
Lemma lem5099520 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : term218.
Proof. exact (fun h0 : ~ False => @lem5099519 A B t s f g x h1 h2 h3). Qed.
Lemma lem5099522 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099523 : term218 = False.
Proof. exact (@lem5099522 False). Qed.
Lemma lem5099524 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099523) (@lem5099520 A B t s f g x h1 h2 h3)). Qed.
Lemma lem5099588 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : @IN B x t.
Proof. exact (proj1 (@lem5099009 A B t s f g x h1)). Qed.
Lemma lem5099589 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : term205 B x t.
Proof. exact (fun h0 : term189 B x t => @lem5099588 A B t s f g x h1). Qed.
Lemma lem5099591 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099592 {B : Type'} (x : B) (t : B -> Prop) : (term205 B x t) = (@IN B x t).
Proof. exact (@lem5099591 (@IN B x t)). Qed.
Lemma lem5099593 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term142 A B t s f g x) : @IN B x t.
Proof. exact (EQ_MP (@lem5099592 B x t) (@lem5099589 A B t s f g x h1)). Qed.
Lemma lem5099599 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5099600 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : (term204 A B t f g _66404) = (term233 A B f g _66404 t).
Proof. exact (@lem5099599 ((term140 A B f g _66404) = _66404) (term189 B _66404 t)). Qed.
Lemma lem5099608 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5099609 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : (term234 A B t f g _66404) = (term235 A B f g _66404 t).
Proof. exact (MK_COMB (@lem5099608) (@lem5099600 A B f g _66404 t)). Qed.
Lemma lem5099617 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : (term233 A B f g _66404 t) = (term233 A B f g _66404 t).
Proof. exact (eq_refl (term233 A B f g _66404 t)). Qed.
Lemma lem5099618 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : ((term204 A B t f g _66404) = (term233 A B f g _66404 t)) = ((term233 A B f g _66404 t) = (term233 A B f g _66404 t)).
Proof. exact (MK_COMB (@lem5099609 A B f g _66404 t) (@lem5099617 A B f g _66404 t)). Qed.
Lemma lem5099620 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5099621 (x : Prop) : (x = x) = True.
Proof. exact (@lem5099620 Prop x). Qed.
Lemma lem5099622 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : ((term233 A B f g _66404 t) = (term233 A B f g _66404 t)) = True.
Proof. exact (@lem5099621 (term233 A B f g _66404 t)). Qed.
Lemma lem5099623 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : ((term204 A B t f g _66404) = (term233 A B f g _66404 t)) = True.
Proof. exact (TRANS (@lem5099618 A B f g _66404 t) (@lem5099622 A B f g _66404 t)). Qed.
Lemma lem5099624 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : True = ((term204 A B t f g _66404) = (term233 A B f g _66404 t)).
Proof. exact (SYM (@lem5099623 A B f g _66404 t)). Qed.
Lemma lem5099625 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) (t : B -> Prop) : (term204 A B t f g _66404) = (term233 A B f g _66404 t).
Proof. exact (EQ_MP (@lem5099624 A B f g _66404 t) (@lem0)). Qed.
Lemma lem5099626 {A B : Type'} (_66404 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term233 A B f g _66404 t.
Proof. exact (EQ_MP (@lem5099625 A B f g _66404 t) (@lem5099318 A B _66404 t s f g h1)). Qed.
Lemma lem5099628 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5099629 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66404 : B) : (term233 A B f g _66404 t) = (term236 A B t f g _66404).
Proof. exact (@lem5099628 (term189 B _66404 t) ((term140 A B f g _66404) = _66404)). Qed.
Lemma lem5099631 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5099632 {B : Type'} (_66404 : B) (t : B -> Prop) : (term212 B _66404 t) = (@IN B _66404 t).
Proof. exact (@lem5099631 (@IN B _66404 t)). Qed.
Lemma lem5099633 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5099634 {B : Type'} (_66404 : B) (t : B -> Prop) : (term213 B _66404 t) = (term214 B _66404 t).
Proof. exact (MK_COMB (@lem5099633) (@lem5099632 B _66404 t)). Qed.
Lemma lem5099635 {A B : Type'} (f : A -> B) (g : B -> A) (_66404 : B) : ((term140 A B f g _66404) = _66404) = ((term140 A B f g _66404) = _66404).
Proof. exact (eq_refl ((term140 A B f g _66404) = _66404)). Qed.
Lemma lem5099636 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66404 : B) : (term236 A B t f g _66404) = (term237 A B t f g _66404).
Proof. exact (MK_COMB (@lem5099634 B _66404 t) (@lem5099635 A B f g _66404)). Qed.
Lemma lem5099637 {A B : Type'} (t : B -> Prop) (f : A -> B) (g : B -> A) (_66404 : B) : (term233 A B f g _66404 t) = (term237 A B t f g _66404).
Proof. exact (TRANS (@lem5099629 A B t f g _66404) (@lem5099636 A B t f g _66404)). Qed.
Lemma lem5099640 {A B : Type'} (_66404 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term237 A B t f g _66404.
Proof. exact (EQ_MP (@lem5099637 A B t f g _66404) (@lem5099626 A B _66404 t s f g h1)). Qed.
Lemma lem5099641 {A B : Type'} (_66404 : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term237 A B t f g _66404.
Proof. exact (@lem5099640 A B _66404 t s f g h1). Qed.
Lemma lem5099642 {A B : Type'} (x : B) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term42 A B t s f g) : term237 A B t f g x.
Proof. exact (@lem5099641 A B x t s f g h1). Qed.
Lemma lem5099645 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g x) : (term140 A B f g x) = x.
Proof. exact (@lem5099642 A B x t s f g h1 (@lem5099593 A B t s f g x h2)). Qed.
Lemma lem5099646 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g x) : term238 A B f g x.
Proof. exact (fun h0 : term198 A B f g x => @lem5099645 A B t s f g x h1 h2). Qed.
Lemma lem5099648 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099649 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : (term238 A B f g x) = ((term140 A B f g x) = x).
Proof. exact (@lem5099648 ((term140 A B f g x) = x)). Qed.
Lemma lem5099650 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g x) : (term140 A B f g x) = x.
Proof. exact (EQ_MP (@lem5099649 A B f g x) (@lem5099646 A B t s f g x h1 h2)). Qed.
Lemma lem5099653 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5099655 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) : (term198 A B f g x) = (term239 A B f g x).
Proof. exact (@lem5099653 ((term140 A B f g x) = x)). Qed.
Lemma lem5099658 {A B : Type'} (f : A -> B) (g : B -> A) (x : B) (h1 : term198 A B f g x) : term239 A B f g x.
Proof. exact (EQ_MP (@lem5099655 A B f g x) (@lem5099306 A B f g x h1)). Qed.
Lemma lem5099661 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : False.
Proof. exact (@lem5099658 A B f g x h2 (@lem5099650 A B t s f g x h1 h3)). Qed.
Lemma lem5099662 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : term218.
Proof. exact (fun h0 : ~ False => @lem5099661 A B t s f g x h1 h2 h3). Qed.
Lemma lem5099664 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099665 : term218 = False.
Proof. exact (@lem5099664 False). Qed.
Lemma lem5099666 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099665) (@lem5099662 A B t s f g x h1 h2 h3)). Qed.
Lemma lem5099730 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : @IN A y s.
Proof. exact (proj1 (@lem5099010 A B s t g f y h1)). Qed.
Lemma lem5099731 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : term205 A y s.
Proof. exact (fun h0 : term189 A y s => @lem5099730 A B s t g f y h1). Qed.
Lemma lem5099733 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099734 {A : Type'} (y : A) (s : A -> Prop) : (term205 A y s) = (@IN A y s).
Proof. exact (@lem5099733 (@IN A y s)). Qed.
Lemma lem5099735 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : @IN A y s.
Proof. exact (EQ_MP (@lem5099734 A y s) (@lem5099731 A B s t g f y h1)). Qed.
Lemma lem5099741 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5099742 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : (term201 A B s f _66405 t) = (term207 A B f t _66405 s).
Proof. exact (@lem5099741 (term122 A B f _66405 t) (term189 A _66405 s)). Qed.
Lemma lem5099748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5099749 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : (term208 A B s f _66405 t) = (term209 A B f t _66405 s).
Proof. exact (MK_COMB (@lem5099748) (@lem5099742 A B f t _66405 s)). Qed.
Lemma lem5099755 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : (term207 A B f t _66405 s) = (term207 A B f t _66405 s).
Proof. exact (eq_refl (term207 A B f t _66405 s)). Qed.
Lemma lem5099756 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : ((term201 A B s f _66405 t) = (term207 A B f t _66405 s)) = ((term207 A B f t _66405 s) = (term207 A B f t _66405 s)).
Proof. exact (MK_COMB (@lem5099749 A B f t _66405 s) (@lem5099755 A B f t _66405 s)). Qed.
Lemma lem5099758 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5099759 (x : Prop) : (x = x) = True.
Proof. exact (@lem5099758 Prop x). Qed.
Lemma lem5099760 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : ((term207 A B f t _66405 s) = (term207 A B f t _66405 s)) = True.
Proof. exact (@lem5099759 (term207 A B f t _66405 s)). Qed.
Lemma lem5099761 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : ((term201 A B s f _66405 t) = (term207 A B f t _66405 s)) = True.
Proof. exact (TRANS (@lem5099756 A B f t _66405 s) (@lem5099760 A B f t _66405 s)). Qed.
Lemma lem5099762 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : True = ((term201 A B s f _66405 t) = (term207 A B f t _66405 s)).
Proof. exact (SYM (@lem5099761 A B f t _66405 s)). Qed.
Lemma lem5099763 {A B : Type'} (f : A -> B) (t : B -> Prop) (_66405 : A) (s : A -> Prop) : (term201 A B s f _66405 t) = (term207 A B f t _66405 s).
Proof. exact (EQ_MP (@lem5099762 A B f t _66405 s) (@lem0)). Qed.
Lemma lem5099764 {A B : Type'} (_66405 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term207 A B f t _66405 s.
Proof. exact (EQ_MP (@lem5099763 A B f t _66405 s) (@lem5099352 A B _66405 s t g f h1)). Qed.
Lemma lem5099766 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5099767 {A B : Type'} (s : A -> Prop) (f : A -> B) (_66405 : A) (t : B -> Prop) : (term207 A B f t _66405 s) = (term211 A B s f _66405 t).
Proof. exact (@lem5099766 (term189 A _66405 s) (term122 A B f _66405 t)). Qed.
Lemma lem5099769 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5099770 {A : Type'} (_66405 : A) (s : A -> Prop) : (term212 A _66405 s) = (@IN A _66405 s).
Proof. exact (@lem5099769 (@IN A _66405 s)). Qed.
Lemma lem5099771 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5099772 {A : Type'} (_66405 : A) (s : A -> Prop) : (term213 A _66405 s) = (term214 A _66405 s).
Proof. exact (MK_COMB (@lem5099771) (@lem5099770 A _66405 s)). Qed.
Lemma lem5099773 {A B : Type'} (f : A -> B) (_66405 : A) (t : B -> Prop) : (term122 A B f _66405 t) = (term122 A B f _66405 t).
Proof. exact (eq_refl (term122 A B f _66405 t)). Qed.
Lemma lem5099774 {A B : Type'} (s : A -> Prop) (f : A -> B) (_66405 : A) (t : B -> Prop) : (term211 A B s f _66405 t) = (term215 A B s f _66405 t).
Proof. exact (MK_COMB (@lem5099772 A _66405 s) (@lem5099773 A B f _66405 t)). Qed.
Lemma lem5099775 {A B : Type'} (s : A -> Prop) (f : A -> B) (_66405 : A) (t : B -> Prop) : (term207 A B f t _66405 s) = (term215 A B s f _66405 t).
Proof. exact (TRANS (@lem5099767 A B s f _66405 t) (@lem5099774 A B s f _66405 t)). Qed.
Lemma lem5099778 {A B : Type'} (_66405 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term215 A B s f _66405 t.
Proof. exact (EQ_MP (@lem5099775 A B s f _66405 t) (@lem5099764 A B _66405 s t g f h1)). Qed.
Lemma lem5099779 {A B : Type'} (_66405 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term215 A B s f _66405 t.
Proof. exact (@lem5099778 A B _66405 s t g f h1). Qed.
Lemma lem5099780 {A B : Type'} (y : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term215 A B s f y t.
Proof. exact (@lem5099779 A B y s t g f h1). Qed.
Lemma lem5099783 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f y) : term122 A B f y t.
Proof. exact (@lem5099780 A B y s t g f h1 (@lem5099735 A B s t g f y h2)). Qed.
Lemma lem5099784 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f y) : term216 A B f y t.
Proof. exact (fun h0 : term192 A B f y t => @lem5099783 A B s t g f y h1 h2). Qed.
Lemma lem5099786 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099787 {A B : Type'} (f : A -> B) (y : A) (t : B -> Prop) : (term216 A B f y t) = (term122 A B f y t).
Proof. exact (@lem5099786 (term122 A B f y t)). Qed.
Lemma lem5099788 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f y) : term122 A B f y t.
Proof. exact (EQ_MP (@lem5099787 A B f y t) (@lem5099784 A B s t g f y h1 h2)). Qed.
Lemma lem5099791 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5099793 {A B : Type'} (f : A -> B) (y : A) (t : B -> Prop) : (term192 A B f y t) = (term217 A B f y t).
Proof. exact (@lem5099791 (term122 A B f y t)). Qed.
Lemma lem5099796 {A B : Type'} (f : A -> B) (y : A) (t : B -> Prop) (h1 : term192 A B f y t) : term217 A B f y t.
Proof. exact (EQ_MP (@lem5099793 A B f y t) (@lem5099334 A B f y t h1)). Qed.
Lemma lem5099799 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : False.
Proof. exact (@lem5099796 A B f y t h2 (@lem5099788 A B s t g f y h1 h3)). Qed.
Lemma lem5099800 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : term218.
Proof. exact (fun h0 : ~ False => @lem5099799 A B s t g f y h1 h2 h3). Qed.
Lemma lem5099802 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099803 : term218 = False.
Proof. exact (@lem5099802 False). Qed.
Lemma lem5099804 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099803) (@lem5099800 A B s t g f y h1 h2 h3)). Qed.
Lemma lem5099868 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : @IN A y s.
Proof. exact (proj1 (@lem5099010 A B s t g f y h1)). Qed.
Lemma lem5099869 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : term205 A y s.
Proof. exact (fun h0 : term189 A y s => @lem5099868 A B s t g f y h1). Qed.
Lemma lem5099871 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099872 {A : Type'} (y : A) (s : A -> Prop) : (term205 A y s) = (@IN A y s).
Proof. exact (@lem5099871 (@IN A y s)). Qed.
Lemma lem5099873 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term126 A B s t g f y) : @IN A y s.
Proof. exact (EQ_MP (@lem5099872 A y s) (@lem5099869 A B s t g f y h1)). Qed.
Lemma lem5099879 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem5099880 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : (term202 A B s g f _66407) = (term219 A B g f _66407 s).
Proof. exact (@lem5099879 ((term123 A B g f _66407) = _66407) (term189 A _66407 s)). Qed.
Lemma lem5099888 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5099889 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : (term220 A B s g f _66407) = (term221 A B g f _66407 s).
Proof. exact (MK_COMB (@lem5099888) (@lem5099880 A B g f _66407 s)). Qed.
Lemma lem5099897 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : (term219 A B g f _66407 s) = (term219 A B g f _66407 s).
Proof. exact (eq_refl (term219 A B g f _66407 s)). Qed.
Lemma lem5099898 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : ((term202 A B s g f _66407) = (term219 A B g f _66407 s)) = ((term219 A B g f _66407 s) = (term219 A B g f _66407 s)).
Proof. exact (MK_COMB (@lem5099889 A B g f _66407 s) (@lem5099897 A B g f _66407 s)). Qed.
Lemma lem5099900 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem5099901 (x : Prop) : (x = x) = True.
Proof. exact (@lem5099900 Prop x). Qed.
Lemma lem5099902 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : ((term219 A B g f _66407 s) = (term219 A B g f _66407 s)) = True.
Proof. exact (@lem5099901 (term219 A B g f _66407 s)). Qed.
Lemma lem5099903 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : ((term202 A B s g f _66407) = (term219 A B g f _66407 s)) = True.
Proof. exact (TRANS (@lem5099898 A B g f _66407 s) (@lem5099902 A B g f _66407 s)). Qed.
Lemma lem5099904 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : True = ((term202 A B s g f _66407) = (term219 A B g f _66407 s)).
Proof. exact (SYM (@lem5099903 A B g f _66407 s)). Qed.
Lemma lem5099905 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) (s : A -> Prop) : (term202 A B s g f _66407) = (term219 A B g f _66407 s).
Proof. exact (EQ_MP (@lem5099904 A B g f _66407 s) (@lem0)). Qed.
Lemma lem5099906 {A B : Type'} (_66407 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term219 A B g f _66407 s.
Proof. exact (EQ_MP (@lem5099905 A B g f _66407 s) (@lem5099386 A B _66407 s t g f h1)). Qed.
Lemma lem5099908 (b : Prop) (a : Prop) : (a \/ b) = (term210 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem5099909 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66407 : A) : (term219 A B g f _66407 s) = (term222 A B s g f _66407).
Proof. exact (@lem5099908 (term189 A _66407 s) ((term123 A B g f _66407) = _66407)). Qed.
Lemma lem5099911 (a : Prop) : (term85 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem5099912 {A : Type'} (_66407 : A) (s : A -> Prop) : (term212 A _66407 s) = (@IN A _66407 s).
Proof. exact (@lem5099911 (@IN A _66407 s)). Qed.
Lemma lem5099913 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5099914 {A : Type'} (_66407 : A) (s : A -> Prop) : (term213 A _66407 s) = (term214 A _66407 s).
Proof. exact (MK_COMB (@lem5099913) (@lem5099912 A _66407 s)). Qed.
Lemma lem5099915 {A B : Type'} (g : B -> A) (f : A -> B) (_66407 : A) : ((term123 A B g f _66407) = _66407) = ((term123 A B g f _66407) = _66407).
Proof. exact (eq_refl ((term123 A B g f _66407) = _66407)). Qed.
Lemma lem5099916 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66407 : A) : (term222 A B s g f _66407) = (term223 A B s g f _66407).
Proof. exact (MK_COMB (@lem5099914 A _66407 s) (@lem5099915 A B g f _66407)). Qed.
Lemma lem5099917 {A B : Type'} (s : A -> Prop) (g : B -> A) (f : A -> B) (_66407 : A) : (term219 A B g f _66407 s) = (term223 A B s g f _66407).
Proof. exact (TRANS (@lem5099909 A B s g f _66407) (@lem5099916 A B s g f _66407)). Qed.
Lemma lem5099920 {A B : Type'} (_66407 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term223 A B s g f _66407.
Proof. exact (EQ_MP (@lem5099917 A B s g f _66407) (@lem5099906 A B _66407 s t g f h1)). Qed.
Lemma lem5099921 {A B : Type'} (_66407 : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term223 A B s g f _66407.
Proof. exact (@lem5099920 A B _66407 s t g f h1). Qed.
Lemma lem5099922 {A B : Type'} (y : A) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term223 A B s g f y.
Proof. exact (@lem5099921 A B y s t g f h1). Qed.
Lemma lem5099925 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f y) : (term123 A B g f y) = y.
Proof. exact (@lem5099922 A B y s t g f h1 (@lem5099873 A B s t g f y h2)). Qed.
Lemma lem5099926 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f y) : term224 A B g f y.
Proof. exact (fun h0 : term193 A B g f y => @lem5099925 A B s t g f y h1 h2). Qed.
Lemma lem5099928 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099929 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) : (term224 A B g f y) = ((term123 A B g f y) = y).
Proof. exact (@lem5099928 ((term123 A B g f y) = y)). Qed.
Lemma lem5099930 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f y) : (term123 A B g f y) = y.
Proof. exact (EQ_MP (@lem5099929 A B g f y) (@lem5099926 A B s t g f y h1 h2)). Qed.
Lemma lem5099933 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem5099935 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) : (term193 A B g f y) = (term225 A B g f y).
Proof. exact (@lem5099933 ((term123 A B g f y) = y)). Qed.
Lemma lem5099938 {A B : Type'} (g : B -> A) (f : A -> B) (y : A) (h1 : term193 A B g f y) : term225 A B g f y.
Proof. exact (EQ_MP (@lem5099935 A B g f y) (@lem5099362 A B g f y h1)). Qed.
Lemma lem5099941 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : False.
Proof. exact (@lem5099938 A B g f y h2 (@lem5099930 A B s t g f y h1 h3)). Qed.
Lemma lem5099942 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : term218.
Proof. exact (fun h0 : ~ False => @lem5099941 A B s t g f y h1 h2 h3). Qed.
Lemma lem5099944 (p : Prop) : (term206 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem5099945 : term218 = False.
Proof. exact (@lem5099944 False). Qed.
Lemma lem5099946 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099945) (@lem5099942 A B s t g f y h1 h2 h3)). Qed.
Lemma lem5099947 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : (term193 A B g f y) = False.
Proof. exact (prop_ext (fun h4 : term193 A B g f y => @lem5099946 A B s t g f y h1 h2 h3) (fun h4 : False => @lem5099362 A B g f y h2)). Qed.
Lemma lem5099948 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099947 A B s t g f y h1 h2 h3) (@lem5099362 A B g f y h2)). Qed.
Lemma lem5099949 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : (term192 A B f y t) = False.
Proof. exact (prop_ext (fun h4 : term192 A B f y t => @lem5099804 A B s t g f y h1 h2 h3) (fun h4 : False => @lem5099334 A B f y t h2)). Qed.
Lemma lem5099950 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099949 A B s t g f y h1 h2 h3) (@lem5099334 A B f y t h2)). Qed.
Lemma lem5099951 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : (term198 A B f g x) = False.
Proof. exact (prop_ext (fun h4 : term198 A B f g x => @lem5099666 A B t s f g x h1 h2 h3) (fun h4 : False => @lem5099306 A B f g x h2)). Qed.
Lemma lem5099952 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099951 A B t s f g x h1 h2 h3) (@lem5099306 A B f g x h2)). Qed.
Lemma lem5099953 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : (term197 A B g x s) = False.
Proof. exact (prop_ext (fun h4 : term197 A B g x s => @lem5099524 A B t s f g x h1 h2 h3) (fun h4 : False => @lem5099278 A B g x s h2)). Qed.
Lemma lem5099954 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099953 A B t s f g x h1 h2 h3) (@lem5099278 A B g x s h2)). Qed.
Lemma lem5099955 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : (term193 A B g f y) = False.
Proof. exact (prop_ext (fun h4 : term193 A B g f y => @lem5099948 A B s t g f y h1 h2 h3) (fun h4 : False => @lem5099234 A B g f y h2)). Qed.
Lemma lem5099956 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099955 A B s t g f y h1 h2 h3) (@lem5099234 A B g f y h2)). Qed.
Lemma lem5099957 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : (term192 A B f y t) = False.
Proof. exact (prop_ext (fun h4 : term192 A B f y t => @lem5099950 A B s t g f y h1 h2 h3) (fun h4 : False => @lem5099180 A B f y t h2)). Qed.
Lemma lem5099958 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099957 A B s t g f y h1 h2 h3) (@lem5099180 A B f y t h2)). Qed.
Lemma lem5099959 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : (term198 A B f g x) = False.
Proof. exact (prop_ext (fun h4 : term198 A B f g x => @lem5099952 A B t s f g x h1 h2 h3) (fun h4 : False => @lem5099126 A B f g x h2)). Qed.
Lemma lem5099960 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099959 A B t s f g x h1 h2 h3) (@lem5099126 A B f g x h2)). Qed.
Lemma lem5099961 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : (term197 A B g x s) = False.
Proof. exact (prop_ext (fun h4 : term197 A B g x s => @lem5099954 A B t s f g x h1 h2 h3) (fun h4 : False => @lem5099072 A B g x s h2)). Qed.
Lemma lem5099962 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099961 A B t s f g x h1 h2 h3) (@lem5099072 A B g x s h2)). Qed.
Lemma lem5099963 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : (term193 A B g f y) = False.
Proof. exact (prop_ext (fun h4 : term193 A B g f y => @lem5099956 A B s t g f y h1 h2 h3) (fun h4 : False => @lem5099234 A B g f y h2)). Qed.
Lemma lem5099964 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term193 A B g f y) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099963 A B s t g f y h1 h2 h3) (@lem5099234 A B g f y h2)). Qed.
Lemma lem5099965 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : (term192 A B f y t) = False.
Proof. exact (prop_ext (fun h4 : term192 A B f y t => @lem5099958 A B s t g f y h1 h2 h3) (fun h4 : False => @lem5099180 A B f y t h2)). Qed.
Lemma lem5099966 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term192 A B f y t) (h3 : term126 A B s t g f y) : False.
Proof. exact (EQ_MP (@lem5099965 A B s t g f y h1 h2 h3) (@lem5099180 A B f y t h2)). Qed.
Lemma lem5099967 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : (term198 A B f g x) = False.
Proof. exact (prop_ext (fun h4 : term198 A B f g x => @lem5099960 A B t s f g x h1 h2 h3) (fun h4 : False => @lem5099126 A B f g x h2)). Qed.
Lemma lem5099968 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term198 A B f g x) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099967 A B t s f g x h1 h2 h3) (@lem5099126 A B f g x h2)). Qed.
Lemma lem5099969 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : (term197 A B g x s) = False.
Proof. exact (prop_ext (fun h4 : term197 A B g x s => @lem5099962 A B t s f g x h1 h2 h3) (fun h4 : False => @lem5099072 A B g x s h2)). Qed.
Lemma lem5099970 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term197 A B g x s) (h3 : term142 A B t s f g x) : False.
Proof. exact (EQ_MP (@lem5099969 A B t s f g x h1 h2 h3) (@lem5099072 A B g x s h2)). Qed.
Lemma lem5099971 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term126 A B s t g f y) : False.
Proof. exact (or_elim (@lem5099015 A B s t g f y h2) (fun h0 : term192 A B f y t => @lem5099966 A B s t g f y h1 h0 h2) (fun h0 : term193 A B g f y => @lem5099964 A B s t g f y h1 h0 h2)). Qed.
Lemma lem5099972 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (x : B) (h1 : term42 A B t s f g) (h2 : term142 A B t s f g x) : False.
Proof. exact (or_elim (@lem5099011 A B t s f g x h2) (fun h0 : term197 A B g x s => @lem5099970 A B t s f g x h1 h0 h2) (fun h0 : term198 A B f g x => @lem5099968 A B t s f g x h1 h0 h2)). Qed.
Lemma lem5099973 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term293 A B x s t g f y) : False.
Proof. exact (or_elim (@lem5099008 A B x s t g f y h3) (fun h0 : term142 A B t s f g x => @lem5099972 A B t s f g x h2 h0) (fun h0 : term126 A B s t g f y => @lem5099971 A B s t g f y h1 h0)). Qed.
Lemma lem5099974 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term293 A B x s t g f y) : (term293 A B x s t g f y) = False.
Proof. exact (prop_ext (fun h4 : term293 A B x s t g f y => @lem5099973 A B x s t g f y h1 h2 h3) (fun h4 : False => @lem5099008 A B x s t g f y h3)). Qed.
Lemma lem5099975 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (y : A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term293 A B x s t g f y) : False.
Proof. exact (EQ_MP (@lem5099974 A B x s t g f y h1 h2 h3) (@lem5099008 A B x s t g f y h3)). Qed.
Lemma lem5099976 {A B : Type'} (x : B) (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term296 A B x s t g f) : False.
Proof. exact (ex_elim (@lem5098875 A B x s t g f h3) (fun y : A => fun h0 : term295 A B x s t g f y => @lem5099975 A B x s t g f y h1 h2 h0)). Qed.
Lemma lem5099977 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term246 A B s t g f) : False.
Proof. exact (ex_elim (@lem5098874 A B s t g f h3) (fun x : B => fun h0 : term297 A B s t g f x => @lem5099976 A B x s t g f h1 h2 h0)). Qed.
Lemma lem5099978 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term246 A B s t g f) : (term246 A B s t g f) = False.
Proof. exact (prop_ext (fun h4 : term246 A B s t g f => @lem5099977 A B s t g f h1 h2 h3) (fun h4 : False => @lem5098539 A B s t g f h3)). Qed.
Lemma lem5099979 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term246 A B s t g f) : False.
Proof. exact (EQ_MP (@lem5099978 A B s t g f h1 h2 h3) (@lem5098539 A B s t g f h3)). Qed.
Lemma lem5099980 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term245 A B s t g f.
Proof. exact (fun h0 : term246 A B s t g f => @lem5099979 A B s t g f h1 h2 h0). Qed.
Lemma lem5099981 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term244 A B s t g f.
Proof. exact (EQ_MP (@lem5098538 A B s t g f) (@lem5099980 A B t s f g h1 h2)). Qed.
Lemma lem5099982 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term253 A B s t g f.
Proof. exact (fun h0 : term42 A B t s f g => @lem5099981 A B t s f g h1 h0). Qed.
Lemma lem5099983 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : term254 A B s t g f.
Proof. exact (fun h0 : term41 A B s t g f => @lem5099982 A B s t g f h0). Qed.
Lemma lem5099988 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) : term258 A B t g f.
Proof. exact (fun s : A -> Prop => @lem5099983 A B s t g f). Qed.
Lemma lem5099993 {A B : Type'} (g : B -> A) (f : A -> B) : term262 A B g f.
Proof. exact (fun t : B -> Prop => @lem5099988 A B t g f). Qed.
Lemma lem5099998 {A B : Type'} (f : A -> B) : term266 A B f.
Proof. exact (fun g : B -> A => @lem5099993 A B g f). Qed.
Lemma lem5100003 {A B : Type'} : term270 A B.
Proof. exact (fun f : A -> B => @lem5099998 A B f). Qed.
Lemma lem5100004 {A B : Type'} : term269 A B.
Proof. exact (EQ_MP (@lem5098532 A B) (@lem5100003 A B)). Qed.
Lemma lem5100005 {A B : Type'} (f : A -> B) : term299 A B f.
Proof. exact (@lem5100004 A B f). Qed.
Lemma lem5100006 {A B : Type'} (f : A -> B) : (term299 A B f) = (term265 A B f).
Proof. exact (eq_refl (term299 A B f)). Qed.
Lemma lem5100007 {A B : Type'} (f : A -> B) : term265 A B f.
Proof. exact (EQ_MP (@lem5100006 A B f) (@lem5100005 A B f)). Qed.
Lemma lem5100008 {A B : Type'} (f : A -> B) (g : B -> A) : term300 A B f g.
Proof. exact (@lem5100007 A B f g). Qed.
Lemma lem5100009 {A B : Type'} (g : B -> A) (f : A -> B) : (term300 A B f g) = (term261 A B g f).
Proof. exact (eq_refl (term300 A B f g)). Qed.
Lemma lem5100010 {A B : Type'} (g : B -> A) (f : A -> B) : term261 A B g f.
Proof. exact (EQ_MP (@lem5100009 A B g f) (@lem5100008 A B f g)). Qed.
Lemma lem5100011 {A B : Type'} (g : B -> A) (f : A -> B) (t : B -> Prop) : term301 A B g f t.
Proof. exact (@lem5100010 A B g f t). Qed.
Lemma lem5100012 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) : (term301 A B g f t) = (term257 A B t g f).
Proof. exact (eq_refl (term301 A B g f t)). Qed.
Lemma lem5100013 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) : term257 A B t g f.
Proof. exact (EQ_MP (@lem5100012 A B t g f) (@lem5100011 A B g f t)). Qed.
Lemma lem5100014 {A B : Type'} (t : B -> Prop) (g : B -> A) (f : A -> B) (s : A -> Prop) : term302 A B t g f s.
Proof. exact (@lem5100013 A B t g f s). Qed.
Lemma lem5100015 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : (term302 A B t g f s) = (term247 A B s t g f).
Proof. exact (eq_refl (term302 A B t g f s)). Qed.
Lemma lem5100016 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : term247 A B s t g f.
Proof. exact (EQ_MP (@lem5100015 A B s t g f) (@lem5100014 A B t g f s)). Qed.
Lemma lem5100018 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) : term247 A B s t g f.
Proof. exact (@lem5098288 A B s t g f (@lem5100016 A B s t g f)). Qed.
Lemma lem5100019 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) : term252 A B s t g f.
Proof. exact (@lem5100018 A B s t g f (@lem5096502 A B s t g f h1)). Qed.
Lemma lem5100020 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term245 A B s t g f.
Proof. exact (@lem5100019 A B s t g f h1 (@lem5096501 A B t s f g h2)). Qed.
Lemma lem5100021 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term246 A B s t g f) : False.
Proof. exact (@lem5100020 A B t s f g h1 h2 (@lem5098272 A B s t g f h3)). Qed.
Lemma lem5100022 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term246 A B s t g f) : (term246 A B s t g f) = False.
Proof. exact (prop_ext (fun h4 : term246 A B s t g f => @lem5100021 A B s t g f h1 h2 h3) (fun h4 : False => @lem5098272 A B s t g f h3)). Qed.
Lemma lem5100023 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (g : B -> A) (f : A -> B) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) (h3 : term246 A B s t g f) : False.
Proof. exact (EQ_MP (@lem5100022 A B s t g f h1 h2 h3) (@lem5098272 A B s t g f h3)). Qed.
Lemma lem5100024 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term245 A B s t g f.
Proof. exact (fun h0 : term246 A B s t g f => @lem5100023 A B s t g f h1 h2 h0). Qed.
Lemma lem5100025 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term244 A B s t g f.
Proof. exact (EQ_MP (@lem5098271 A B s t g f) (@lem5100024 A B t s f g h1 h2)). Qed.
Lemma lem5100026 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term303 A B s t g.
Proof. exact (ex_intro (term304 A B s t g) f (@lem5100025 A B t s f g h1 h2)). Qed.
Lemma lem5100027 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term305 A B s t.
Proof. exact (ex_intro (term306 A B s t) g (@lem5100026 A B t s f g h1 h2)). Qed.
Lemma lem5100028 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term66 A B t s f.
Proof. exact (ex_intro (term67 A B t s f) g (@lem5098267 A B t s f g h1 h2)). Qed.
Lemma lem5100029 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term68 A B t s.
Proof. exact (ex_intro (term69 A B t s) f (@lem5100028 A B t s f g h1 h2)). Qed.
Lemma lem5100030 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term307 A B t s n.
Proof. exact (@lem5096509 A B t s n (@lem5100027 A B t s f g h1 h2)). Qed.
Lemma lem5100031 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term64 A B s t n.
Proof. exact (@lem5096505 A B s t n (@lem5100029 A B t s f g h1 h2)). Qed.
Lemma lem5100032 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term308 A B t s n.
Proof. exact (conj (@lem5100031 A B n t s f g h1 h2) (@lem5100030 A B n t s f g h1 h2)). Qed.
Lemma lem5100033 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (n : nat) : (term308 A B t s n) = ((@HAS_SIZE A s n) = (@HAS_SIZE B t n)).
Proof. exact (@lem32 (@HAS_SIZE A s n) (@HAS_SIZE B t n)). Qed.
Lemma lem5100034 {A B : Type'} (n : nat) (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : (@HAS_SIZE A s n) = (@HAS_SIZE B t n).
Proof. exact (EQ_MP (@lem5100033 A B s t n) (@lem5100032 A B n t s f g h1 h2)). Qed.
Lemma lem5100039 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term309 A B s t.
Proof. exact (fun n : nat => @lem5100034 A B n t s f g h1 h2). Qed.
Lemma lem5100040 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term63 A B t s f g) : term42 A B t s f g.
Proof. exact (proj2 (@lem5096500 A B t s f g h1)). Qed.
Lemma lem5100041 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term63 A B t s f g) : term41 A B s t g f.
Proof. exact (proj1 (@lem5096500 A B t s f g h1)). Qed.
Lemma lem5100042 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : (term42 A B t s f g) = (term309 A B s t).
Proof. exact (prop_ext (fun h3 : term42 A B t s f g => @lem5100039 A B t s f g h1 h2) (fun h3 : term309 A B s t => @lem5096501 A B t s f g h2)). Qed.
Lemma lem5100043 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term309 A B s t.
Proof. exact (EQ_MP (@lem5100042 A B t s f g h1 h2) (@lem5096501 A B t s f g h2)). Qed.
Lemma lem5100044 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : (term41 A B s t g f) = (term309 A B s t).
Proof. exact (prop_ext (fun h3 : term41 A B s t g f => @lem5100043 A B t s f g h1 h2) (fun h3 : term309 A B s t => @lem5096502 A B s t g f h1)). Qed.
Lemma lem5100045 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term42 A B t s f g) : term309 A B s t.
Proof. exact (EQ_MP (@lem5100044 A B t s f g h1 h2) (@lem5096502 A B s t g f h1)). Qed.
Lemma lem5100046 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term63 A B t s f g) : (term42 A B t s f g) = (term309 A B s t).
Proof. exact (prop_ext (fun h3 : term42 A B t s f g => @lem5100045 A B t s f g h1 h3) (fun h3 : term309 A B s t => @lem5100040 A B t s f g h2)). Qed.
Lemma lem5100047 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term41 A B s t g f) (h2 : term63 A B t s f g) : term309 A B s t.
Proof. exact (EQ_MP (@lem5100046 A B t s f g h1 h2) (@lem5100040 A B t s f g h2)). Qed.
Lemma lem5100048 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term63 A B t s f g) : (term41 A B s t g f) = (term309 A B s t).
Proof. exact (prop_ext (fun h2 : term41 A B s t g f => @lem5100047 A B t s f g h2 h1) (fun h2 : term309 A B s t => @lem5100041 A B t s f g h1)). Qed.
Lemma lem5100049 {A B : Type'} (t : B -> Prop) (s : A -> Prop) (f : A -> B) (g : B -> A) (h1 : term63 A B t s f g) : term309 A B s t.
Proof. exact (EQ_MP (@lem5100048 A B t s f g h1) (@lem5100041 A B t s f g h1)). Qed.
Lemma lem5100050 {A B : Type'} (f : A -> B) (g : B -> A) (s : A -> Prop) (t : B -> Prop) : term310 A B f g s t.
Proof. exact (fun h0 : term63 A B t s f g => @lem5100049 A B t s f g h0). Qed.
Lemma lem5100055 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : B -> Prop) : term311 A B f s t.
Proof. exact (fun g : B -> A => @lem5100050 A B f g s t). Qed.
Lemma lem5100060 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term312 A B s t.
Proof. exact (fun f : A -> B => @lem5100055 A B f s t). Qed.
Lemma lem5100065 {A B : Type'} (s : A -> Prop) : term313 A B s.
Proof. exact (fun t : B -> Prop => @lem5100060 A B s t). Qed.
Lemma lem5100070 {A B : Type'} : term314 A B.
Proof. exact (fun s : A -> Prop => @lem5100065 A B s). Qed.
