Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import IN_CROSS_term_abbrevs.
Require Import CROSS_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem4325237 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term0 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem4325238 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term0 _88435 _88436 P) = (term1 _88435 _88436 P).
Proof. exact (eq_refl (term0 _88435 _88436 P)). Qed.
Lemma lem4325239 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term1 _88435 _88436 P.
Proof. exact (EQ_MP (@lem4325238 _88435 _88436 P) (@lem4325237 _88435 _88436 P)). Qed.
Lemma lem4325240 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term2 _88435 _88436 P a.
Proof. exact (@lem4325239 _88435 _88436 P a). Qed.
Lemma lem4325241 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term2 _88435 _88436 P a) = (term3 _88435 _88436 P a).
Proof. exact (eq_refl (term2 _88435 _88436 P a)). Qed.
Lemma lem4325242 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term3 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem4325241 _88435 _88436 P a) (@lem4325240 _88435 _88436 P a)). Qed.
Lemma lem4325243 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term4 _88435 _88436 P a b.
Proof. exact (@lem4325242 _88435 _88436 P a b). Qed.
Lemma lem4325244 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term4 _88435 _88436 P a b) = ((term5 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term4 _88435 _88436 P a b)). Qed.
Lemma lem4325246 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term6 _103681 _103682 s.
Proof. exact (@lem4325236 _103681 _103682 s). Qed.
Lemma lem4325247 {_103681 _103682 : Type'} (s : _103682 -> Prop) : (term6 _103681 _103682 s) = (term7 _103681 _103682 s).
Proof. exact (eq_refl (term6 _103681 _103682 s)). Qed.
Lemma lem4325248 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term7 _103681 _103682 s.
Proof. exact (EQ_MP (@lem4325247 _103681 _103682 s) (@lem4325246 _103681 _103682 s)). Qed.
Lemma lem4325249 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : term8 _103681 _103682 s t.
Proof. exact (@lem4325248 _103681 _103682 s t). Qed.
Lemma lem4325250 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (term8 _103681 _103682 s t) = ((@CROSS _103681 _103682 s t) = (term9 _103681 _103682 s t)).
Proof. exact (eq_refl (term8 _103681 _103682 s t)). Qed.
Lemma lem4325271 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (@CROSS _103681 _103682 s t) = (term9 _103681 _103682 s t).
Proof. exact (EQ_MP (@lem4325250 _103681 _103682 s t) (@lem4325249 _103681 _103682 s t)). Qed.
Lemma lem4325272 {_103718 _103721 : Type'} (s : _103718 -> Prop) (t : _103721 -> Prop) : (@CROSS _103721 _103718 s t) = (term10 _103718 _103721 s t).
Proof. exact (@lem4325271 _103721 _103718 s t). Qed.
Lemma lem4325283 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term11 _103718 _103721 x y) = (term11 _103718 _103721 x y).
Proof. exact (eq_refl (term11 _103718 _103721 x y)). Qed.
Lemma lem4325284 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) : (term12 _103718 _103721 x y s t) = (term13 _103718 _103721 x y s t).
Proof. exact (MK_COMB (@lem4325283 _103718 _103721 x y) (@lem4325272 _103718 _103721 s t)). Qed.
Lemma lem4325286 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term5 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem4325244 _88435 _88436 P a b) (@lem4325243 _88435 _88436 P a b)). Qed.
Lemma lem4325287 {_103718 _103721 : Type'} (P : type1413 _103718 _103721) (a : _103718) (b : _103721) : (term14 _103718 _103721 a b P) = (P a b).
Proof. exact (@lem4325286 _103721 _103718 P a b). Qed.
Lemma lem4325288 {_103718 _103721 : Type'} (s : _103718 -> Prop) (t : _103721 -> Prop) (x : _103718) (y : _103721) : (term15 _103718 _103721 x y s t) = (term16 _103718 _103721 s t x y).
Proof. exact (@lem4325287 _103718 _103721 (term17 _103718 _103721 s t) x y). Qed.
Lemma lem4325289 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (t : _103721 -> Prop) : (term18 _103718 _103721 s t x) = (term19 _103718 _103721 x s t).
Proof. exact (eq_refl (term18 _103718 _103721 s t x)). Qed.
Lemma lem4325290 {_103721 : Type'} (y : _103721) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4325291 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (t : _103721 -> Prop) (y : _103721) : (term16 _103718 _103721 s t x y) = (term20 _103718 _103721 x s t y).
Proof. exact (MK_COMB (@lem4325289 _103718 _103721 x s t) (@lem4325290 _103721 y)). Qed.
Lemma lem4325292 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term20 _103718 _103721 x s t y) = (term21 _103718 _103721 x s y t).
Proof. exact (eq_refl (term20 _103718 _103721 x s t y)). Qed.
Lemma lem4325293 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term16 _103718 _103721 s t x y) = (term21 _103718 _103721 x s y t).
Proof. exact (TRANS (@lem4325291 _103718 _103721 x s t y) (@lem4325292 _103718 _103721 x s y t)). Qed.
Lemma lem4325294 {_103718 _103721 : Type'} (GEN_PVAR_130 : prod _103718 _103721) : (@SETSPEC (prod _103718 _103721) GEN_PVAR_130) = (@SETSPEC (prod _103718 _103721) GEN_PVAR_130).
Proof. exact (eq_refl (@SETSPEC (prod _103718 _103721) GEN_PVAR_130)). Qed.
Lemma lem4325295 {_103718 _103721 : Type'} (GEN_PVAR_130 : prod _103718 _103721) (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term22 _103718 _103721 GEN_PVAR_130 s t x y) = (term23 _103718 _103721 GEN_PVAR_130 x s y t).
Proof. exact (MK_COMB (@lem4325294 _103718 _103721 GEN_PVAR_130) (@lem4325293 _103718 _103721 x s y t)). Qed.
Lemma lem4325296 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (@pair _103718 _103721 x y) = (@pair _103718 _103721 x y).
Proof. exact (eq_refl (@pair _103718 _103721 x y)). Qed.
Lemma lem4325297 {_103718 _103721 : Type'} (GEN_PVAR_130 : prod _103718 _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) (x : _103718) (y : _103721) : (term24 _103718 _103721 GEN_PVAR_130 s t x y) = (term25 _103718 _103721 GEN_PVAR_130 s t x y).
Proof. exact (MK_COMB (@lem4325295 _103718 _103721 GEN_PVAR_130 x s y t) (@lem4325296 _103718 _103721 x y)). Qed.
Lemma lem4325298 {_103718 _103721 : Type'} (GEN_PVAR_130 : prod _103718 _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) (x : _103718) : (term26 _103718 _103721 GEN_PVAR_130 s t x) = (term27 _103718 _103721 GEN_PVAR_130 s t x).
Proof. exact (fun_ext (fun y : _103721 => @lem4325297 _103718 _103721 GEN_PVAR_130 s t x y)). Qed.
Lemma lem4325299 {_103721 : Type'} : (@ex _103721) = (@ex _103721).
Proof. exact (eq_refl (@ex _103721)). Qed.
Lemma lem4325300 {_103718 _103721 : Type'} (GEN_PVAR_130 : prod _103718 _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) (x : _103718) : (term28 _103718 _103721 GEN_PVAR_130 s t x) = (term29 _103718 _103721 GEN_PVAR_130 s t x).
Proof. exact (MK_COMB (@lem4325299 _103721) (@lem4325298 _103718 _103721 GEN_PVAR_130 s t x)). Qed.
Lemma lem4325301 {_103718 _103721 : Type'} (GEN_PVAR_130 : prod _103718 _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) : (term30 _103718 _103721 GEN_PVAR_130 s t) = (term31 _103718 _103721 GEN_PVAR_130 s t).
Proof. exact (fun_ext (fun x : _103718 => @lem4325300 _103718 _103721 GEN_PVAR_130 s t x)). Qed.
Lemma lem4325302 {_103718 : Type'} : (@ex _103718) = (@ex _103718).
Proof. exact (eq_refl (@ex _103718)). Qed.
Lemma lem4325303 {_103718 _103721 : Type'} (GEN_PVAR_130 : prod _103718 _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) : (term32 _103718 _103721 GEN_PVAR_130 s t) = (term33 _103718 _103721 GEN_PVAR_130 s t).
Proof. exact (MK_COMB (@lem4325302 _103718) (@lem4325301 _103718 _103721 GEN_PVAR_130 s t)). Qed.
Lemma lem4325304 {_103718 _103721 : Type'} (s : _103718 -> Prop) (t : _103721 -> Prop) : (term34 _103718 _103721 s t) = (term35 _103718 _103721 s t).
Proof. exact (fun_ext (fun GEN_PVAR_130 : prod _103718 _103721 => @lem4325303 _103718 _103721 GEN_PVAR_130 s t)). Qed.
Lemma lem4325305 {_103718 _103721 : Type'} : (@GSPEC (prod _103718 _103721)) = (@GSPEC (prod _103718 _103721)).
Proof. exact (eq_refl (@GSPEC (prod _103718 _103721))). Qed.
Lemma lem4325306 {_103718 _103721 : Type'} (s : _103718 -> Prop) (t : _103721 -> Prop) : (term36 _103718 _103721 s t) = (term10 _103718 _103721 s t).
Proof. exact (MK_COMB (@lem4325305 _103718 _103721) (@lem4325304 _103718 _103721 s t)). Qed.
Lemma lem4325307 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term11 _103718 _103721 x y) = (term11 _103718 _103721 x y).
Proof. exact (eq_refl (term11 _103718 _103721 x y)). Qed.
Lemma lem4325308 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) : (term15 _103718 _103721 x y s t) = (term13 _103718 _103721 x y s t).
Proof. exact (MK_COMB (@lem4325307 _103718 _103721 x y) (@lem4325306 _103718 _103721 s t)). Qed.
Lemma lem4325309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4325310 {_103718 _103721 : Type'} (x : _103718) (y : _103721) (s : _103718 -> Prop) (t : _103721 -> Prop) : (term37 _103718 _103721 x y s t) = (term38 _103718 _103721 x y s t).
Proof. exact (MK_COMB (@lem4325309) (@lem4325308 _103718 _103721 x y s t)). Qed.
Lemma lem4325311 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (t : _103721 -> Prop) : (term18 _103718 _103721 s t x) = (term19 _103718 _103721 x s t).
Proof. exact (eq_refl (term18 _103718 _103721 s t x)). Qed.
Lemma lem4325312 {_103721 : Type'} (y : _103721) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4325313 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (t : _103721 -> Prop) (y : _103721) : (term16 _103718 _103721 s t x y) = (term20 _103718 _103721 x s t y).
Proof. exact (MK_COMB (@lem4325311 _103718 _103721 x s t) (@lem4325312 _103721 y)). Qed.
Lemma lem4325314 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term20 _103718 _103721 x s t y) = (term21 _103718 _103721 x s y t).
Proof. exact (eq_refl (term20 _103718 _103721 x s t y)). Qed.
Lemma lem4325315 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term16 _103718 _103721 s t x y) = (term21 _103718 _103721 x s y t).
Proof. exact (TRANS (@lem4325313 _103718 _103721 x s t y) (@lem4325314 _103718 _103721 x s y t)). Qed.
Lemma lem4325316 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : ((term15 _103718 _103721 x y s t) = (term16 _103718 _103721 s t x y)) = ((term13 _103718 _103721 x y s t) = (term21 _103718 _103721 x s y t)).
Proof. exact (MK_COMB (@lem4325310 _103718 _103721 x y s t) (@lem4325315 _103718 _103721 x s y t)). Qed.
Lemma lem4325317 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term13 _103718 _103721 x y s t) = (term21 _103718 _103721 x s y t).
Proof. exact (EQ_MP (@lem4325316 _103718 _103721 x s y t) (@lem4325288 _103718 _103721 s t x y)). Qed.
Lemma lem4325320 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term12 _103718 _103721 x y s t) = (term21 _103718 _103721 x s y t).
Proof. exact (TRANS (@lem4325284 _103718 _103721 x y s t) (@lem4325317 _103718 _103721 x s y t)). Qed.
Lemma lem4325321 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4325322 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term39 _103718 _103721 x y s t) = (term40 _103718 _103721 x s y t).
Proof. exact (MK_COMB (@lem4325321) (@lem4325320 _103718 _103721 x s y t)). Qed.
Lemma lem4325325 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : (term21 _103718 _103721 x s y t) = (term21 _103718 _103721 x s y t).
Proof. exact (eq_refl (term21 _103718 _103721 x s y t)). Qed.
Lemma lem4325326 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : ((term12 _103718 _103721 x y s t) = (term21 _103718 _103721 x s y t)) = ((term21 _103718 _103721 x s y t) = (term21 _103718 _103721 x s y t)).
Proof. exact (MK_COMB (@lem4325322 _103718 _103721 x s y t) (@lem4325325 _103718 _103721 x s y t)). Qed.
Lemma lem4325328 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4325329 (x : Prop) : (x = x) = True.
Proof. exact (@lem4325328 Prop x). Qed.
Lemma lem4325330 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : ((term21 _103718 _103721 x s y t) = (term21 _103718 _103721 x s y t)) = True.
Proof. exact (@lem4325329 (term21 _103718 _103721 x s y t)). Qed.
Lemma lem4325331 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) (t : _103721 -> Prop) : ((term12 _103718 _103721 x y s t) = (term21 _103718 _103721 x s y t)) = True.
Proof. exact (TRANS (@lem4325326 _103718 _103721 x s y t) (@lem4325330 _103718 _103721 x s y t)). Qed.
Lemma lem4325332 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term41 _103718 _103721 x s y) = (term42 _103721).
Proof. exact (fun_ext (fun t : _103721 -> Prop => @lem4325331 _103718 _103721 x s y t)). Qed.
Lemma lem4325333 {_103721 : Type'} : (@all (_103721 -> Prop)) = (@all (_103721 -> Prop)).
Proof. exact (eq_refl (@all (_103721 -> Prop))). Qed.
Lemma lem4325334 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term43 _103718 _103721 x s y) = (term44 _103721).
Proof. exact (MK_COMB (@lem4325333 _103721) (@lem4325332 _103718 _103721 x s y)). Qed.
Lemma lem4325336 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325337 {_103721 : Type'} (t : Prop) : (term46 _103721 t) = t.
Proof. exact (@lem4325336 (_103721 -> Prop) t). Qed.
Lemma lem4325338 {_103721 : Type'} : (term44 _103721) = True.
Proof. exact (@lem4325337 _103721 True). Qed.
Lemma lem4325339 {_103718 _103721 : Type'} (x : _103718) (s : _103718 -> Prop) (y : _103721) : (term43 _103718 _103721 x s y) = True.
Proof. exact (TRANS (@lem4325334 _103718 _103721 x s y) (@lem4325338 _103721)). Qed.
Lemma lem4325340 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term47 _103718 _103721 x y) = (term42 _103718).
Proof. exact (fun_ext (fun s : _103718 -> Prop => @lem4325339 _103718 _103721 x s y)). Qed.
Lemma lem4325341 {_103718 : Type'} : (@all (_103718 -> Prop)) = (@all (_103718 -> Prop)).
Proof. exact (eq_refl (@all (_103718 -> Prop))). Qed.
Lemma lem4325342 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term48 _103718 _103721 x y) = (term44 _103718).
Proof. exact (MK_COMB (@lem4325341 _103718) (@lem4325340 _103718 _103721 x y)). Qed.
Lemma lem4325344 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325345 {_103718 : Type'} (t : Prop) : (term46 _103718 t) = t.
Proof. exact (@lem4325344 (_103718 -> Prop) t). Qed.
Lemma lem4325346 {_103718 : Type'} : (term44 _103718) = True.
Proof. exact (@lem4325345 _103718 True). Qed.
Lemma lem4325347 {_103718 _103721 : Type'} (x : _103718) (y : _103721) : (term48 _103718 _103721 x y) = True.
Proof. exact (TRANS (@lem4325342 _103718 _103721 x y) (@lem4325346 _103718)). Qed.
Lemma lem4325348 {_103718 _103721 : Type'} (x : _103718) : (term49 _103718 _103721 x) = (term50 _103721).
Proof. exact (fun_ext (fun y : _103721 => @lem4325347 _103718 _103721 x y)). Qed.
Lemma lem4325349 {_103721 : Type'} : (@all _103721) = (@all _103721).
Proof. exact (eq_refl (@all _103721)). Qed.
Lemma lem4325350 {_103718 _103721 : Type'} (x : _103718) : (term51 _103718 _103721 x) = (term52 _103721).
Proof. exact (MK_COMB (@lem4325349 _103721) (@lem4325348 _103718 _103721 x)). Qed.
Lemma lem4325352 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325353 {_103721 : Type'} (t : Prop) : (term45 _103721 t) = t.
Proof. exact (@lem4325352 _103721 t). Qed.
Lemma lem4325354 {_103721 : Type'} : (term52 _103721) = True.
Proof. exact (@lem4325353 _103721 True). Qed.
Lemma lem4325355 {_103718 _103721 : Type'} (x : _103718) : (term51 _103718 _103721 x) = True.
Proof. exact (TRANS (@lem4325350 _103718 _103721 x) (@lem4325354 _103721)). Qed.
Lemma lem4325356 {_103718 _103721 : Type'} : (term53 _103718 _103721) = (term50 _103718).
Proof. exact (fun_ext (fun x : _103718 => @lem4325355 _103718 _103721 x)). Qed.
Lemma lem4325357 {_103718 : Type'} : (@all _103718) = (@all _103718).
Proof. exact (eq_refl (@all _103718)). Qed.
Lemma lem4325358 {_103718 _103721 : Type'} : (term54 _103718 _103721) = (term52 _103718).
Proof. exact (MK_COMB (@lem4325357 _103718) (@lem4325356 _103718 _103721)). Qed.
Lemma lem4325360 {A : Type'} (t : Prop) : (term45 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4325361 {_103718 : Type'} (t : Prop) : (term45 _103718 t) = t.
Proof. exact (@lem4325360 _103718 t). Qed.
Lemma lem4325362 {_103718 : Type'} : (term52 _103718) = True.
Proof. exact (@lem4325361 _103718 True). Qed.
Lemma lem4325363 {_103718 _103721 : Type'} : (term54 _103718 _103721) = True.
Proof. exact (TRANS (@lem4325358 _103718 _103721) (@lem4325362 _103718)). Qed.
Lemma lem4325364 {_103718 _103721 : Type'} : True = (term54 _103718 _103721).
Proof. exact (SYM (@lem4325363 _103718 _103721)). Qed.
Lemma lem4325365 {_103718 _103721 : Type'} : term54 _103718 _103721.
Proof. exact (EQ_MP (@lem4325364 _103718 _103721) (@lem0)). Qed.
