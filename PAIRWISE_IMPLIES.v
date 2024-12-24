Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import PAIRWISE_IMPLIES_term_abbrevs.
Require Import ALL_MEM_spec.
Require Import DISJ_ACI_spec.
Require Import DISJ_ASSOC_spec.
Require Import list_INDUCT_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1110672_spec.
Require Import thm1110673_spec.
Require Import thm1110681_spec.
Require Import thm1110682_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm19490_spec.
Require Import thm19699_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem1231298 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem1231299 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem1231300 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem1231299 t1) (@lem1231298 t1)). Qed.
Lemma lem1231301 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem1231300 t1 t2). Qed.
Lemma lem1231302 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem1231303 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem1231302 t1 t2) (@lem1231301 t1 t2)). Qed.
Lemma lem1231304 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem1231303 t1 t2 t3). Qed.
Lemma lem1231305 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem1231306 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem1231305 t1 t2 t3) (@lem1231304 t1 t2 t3)). Qed.
Lemma lem1231307 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem1231306 t1 t2 t3)). Qed.
Lemma lem1231310 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (h1). Qed.
Lemma lem1231311 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) (h1 : (term7 _26777 l P) = (@List.Forall _26777 P l)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (SYM (@lem1231310 _26777 P l h1)). Qed.
Lemma lem1231312 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (h1). Qed.
Lemma lem1231313 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) (h1 : (@List.Forall _26777 P l) = (term7 _26777 l P)) : (term7 _26777 l P) = (@List.Forall _26777 P l).
Proof. exact (SYM (@lem1231312 _26777 l P h1)). Qed.
Lemma lem1231314 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : ((term7 _26777 l P) = (@List.Forall _26777 P l)) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (prop_ext (fun h1 : (term7 _26777 l P) = (@List.Forall _26777 P l) => @lem1231311 _26777 P l h1) (fun h1 : (@List.Forall _26777 P l) = (term7 _26777 l P) => @lem1231313 _26777 l P h1)). Qed.
Lemma lem1231315 {_26777 : Type'} (P : _26777 -> Prop) : (term8 _26777 P) = (term9 _26777 P).
Proof. exact (fun_ext (fun l : list _26777 => @lem1231314 _26777 l P)). Qed.
Lemma lem1231316 {_26777 : Type'} : (@all (list _26777)) = (@all (list _26777)).
Proof. exact (eq_refl (@all (list _26777))). Qed.
Lemma lem1231317 {_26777 : Type'} (P : _26777 -> Prop) : (term10 _26777 P) = (term11 _26777 P).
Proof. exact (MK_COMB (@lem1231316 _26777) (@lem1231315 _26777 P)). Qed.
Lemma lem1231318 {_26777 : Type'} : (term12 _26777) = (term13 _26777).
Proof. exact (fun_ext (fun P : _26777 -> Prop => @lem1231317 _26777 P)). Qed.
Lemma lem1231319 {_26777 : Type'} : (@all (_26777 -> Prop)) = (@all (_26777 -> Prop)).
Proof. exact (eq_refl (@all (_26777 -> Prop))). Qed.
Lemma lem1231320 {_26777 : Type'} : (term14 _26777) = (term15 _26777).
Proof. exact (MK_COMB (@lem1231319 _26777) (@lem1231318 _26777)). Qed.
Lemma lem1231321 {_26777 : Type'} : term15 _26777.
Proof. exact (EQ_MP (@lem1231320 _26777) (@lem1138070 _26777)). Qed.
Lemma lem1231324 {_26777 : Type'} (P : _26777 -> Prop) : term16 _26777 P.
Proof. exact (@lem1231321 _26777 P). Qed.
Lemma lem1231325 {_26777 : Type'} (P : _26777 -> Prop) : (term16 _26777 P) = (term11 _26777 P).
Proof. exact (eq_refl (term16 _26777 P)). Qed.
Lemma lem1231326 {_26777 : Type'} (P : _26777 -> Prop) : term11 _26777 P.
Proof. exact (EQ_MP (@lem1231325 _26777 P) (@lem1231324 _26777 P)). Qed.
Lemma lem1231327 {_26777 : Type'} (P : _26777 -> Prop) (l : list _26777) : term17 _26777 P l.
Proof. exact (@lem1231326 _26777 P l). Qed.
Lemma lem1231328 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (term17 _26777 P l) = ((@List.Forall _26777 P l) = (term7 _26777 l P)).
Proof. exact (eq_refl (term17 _26777 P l)). Qed.
Lemma lem1231332 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem1231333 {A : Type'} (P : type1143 A) (h1 : term18 A) : term19 A P.
Proof. exact (@lem1231332 A h1 P). Qed.
Lemma lem1231334 {A : Type'} (P : type1143 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem1231335 {A : Type'} (P : type1143 A) (h1 : term18 A) : term20 A P.
Proof. exact (EQ_MP (@lem1231334 A P) (@lem1231333 A P h1)). Qed.
Lemma lem1231336 {A : Type'} (P : type1143 A) (h1 : term21 A P) : term21 A P.
Proof. exact (h1). Qed.
Lemma lem1231337 {A : Type'} (P : type1143 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem1231335 A P h1 (@lem1231336 A P h2)). Qed.
Lemma lem1231338 {A : Type'} (P : type1143 A) (h1 : term21 A P) : term23 A P.
Proof. exact (fun h0 : term18 A => @lem1231337 A P h0 h1). Qed.
Lemma lem1231339 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (h1). Qed.
Lemma lem1231340 {A : Type'} (P : type1143 A) (h1 : term18 A) (h2 : term21 A P) : term22 A P.
Proof. exact (@lem1231338 A P h2 (@lem1231339 A h1)). Qed.
Lemma lem1231341 {A : Type'} (P : type1143 A) (h1 : term18 A) : term20 A P.
Proof. exact (fun h0 : term21 A P => @lem1231340 A P h1 h0). Qed.
Lemma lem1231342 {A : Type'} (h1 : term18 A) : term18 A.
Proof. exact (fun P : type1143 A => @lem1231341 A P h1). Qed.
Lemma lem1231343 {A : Type'} : term24 A.
Proof. exact (fun h0 : term18 A => @lem1231342 A h0). Qed.
Lemma lem1231344 {A : Type'} : term18 A.
Proof. exact (@lem1231343 A (@lem1071853 A)). Qed.
Lemma lem1231345 {A : Type'} (P : type1143 A) : term19 A P.
Proof. exact (@lem1231344 A P). Qed.
Lemma lem1231346 {A : Type'} (P : type1143 A) : (term19 A P) = (term20 A P).
Proof. exact (eq_refl (term19 A P)). Qed.
Lemma lem1231349 {A : Type'} (P : type1143 A) : term20 A P.
Proof. exact (EQ_MP (@lem1231346 A P) (@lem1231345 A P)). Qed.
Lemma lem1231350 {A : Type'} (P : type1143 A) : term20 A P.
Proof. exact (@lem1231349 A P). Qed.
Lemma lem1231351 {A : Type'} (R : type1402 A) (R' : type1402 A) : term25 A R R'.
Proof. exact (@lem1231350 A (term26 A R R')). Qed.
Lemma lem1231352 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term27 A R R') = (term28 A R R').
Proof. exact (eq_refl (term27 A R R')). Qed.
Lemma lem1231353 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231354 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term29 A R R') = (term30 A R R').
Proof. exact (MK_COMB (@lem1231353) (@lem1231352 A R R')). Qed.
Lemma lem1231355 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term31 A R R' a1) = (term32 A R R' a1).
Proof. exact (eq_refl (term31 A R R' a1)). Qed.
Lemma lem1231356 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231357 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term33 A R R' a1) = (term34 A R R' a1).
Proof. exact (MK_COMB (@lem1231356) (@lem1231355 A R R' a1)). Qed.
Lemma lem1231358 {A : Type'} (R : type1402 A) (R' : type1402 A) (a0 : A) (a1 : list A) : (term35 A R R' a0 a1) = (term36 A R R' a0 a1).
Proof. exact (eq_refl (term35 A R R' a0 a1)). Qed.
Lemma lem1231359 {A : Type'} (R : type1402 A) (R' : type1402 A) (a0 : A) (a1 : list A) : (term37 A R R' a0 a1) = (term38 A R R' a0 a1).
Proof. exact (MK_COMB (@lem1231357 A R R' a1) (@lem1231358 A R R' a0 a1)). Qed.
Lemma lem1231360 {A : Type'} (R : type1402 A) (R' : type1402 A) (a0 : A) : (term39 A R R' a0) = (term40 A R R' a0).
Proof. exact (fun_ext (fun a1 : list A => @lem1231359 A R R' a0 a1)). Qed.
Lemma lem1231361 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1231362 {A : Type'} (R : type1402 A) (R' : type1402 A) (a0 : A) : (term41 A R R' a0) = (term42 A R R' a0).
Proof. exact (MK_COMB (@lem1231361 A) (@lem1231360 A R R' a0)). Qed.
Lemma lem1231363 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term43 A R R') = (term44 A R R').
Proof. exact (fun_ext (fun a0 : A => @lem1231362 A R R' a0)). Qed.
Lemma lem1231364 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231365 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term45 A R R') = (term46 A R R').
Proof. exact (MK_COMB (@lem1231364 A) (@lem1231363 A R R')). Qed.
Lemma lem1231366 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term47 A R R') = (term48 A R R').
Proof. exact (MK_COMB (@lem1231354 A R R') (@lem1231365 A R R')). Qed.
Lemma lem1231367 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231368 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term49 A R R') = (term50 A R R').
Proof. exact (MK_COMB (@lem1231367) (@lem1231366 A R R')). Qed.
Lemma lem1231369 {A : Type'} (R : type1402 A) (R' : type1402 A) (l : list A) : (term31 A R R' l) = (term32 A R R' l).
Proof. exact (eq_refl (term31 A R R' l)). Qed.
Lemma lem1231370 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term51 A R R') = (term26 A R R').
Proof. exact (fun_ext (fun l : list A => @lem1231369 A R R' l)). Qed.
Lemma lem1231371 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1231372 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term52 A R R') = (term53 A R R').
Proof. exact (MK_COMB (@lem1231371 A) (@lem1231370 A R R')). Qed.
Lemma lem1231373 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term25 A R R') = (term54 A R R').
Proof. exact (MK_COMB (@lem1231368 A R R') (@lem1231372 A R R')). Qed.
Lemma lem1231374 {A : Type'} (R : type1402 A) (R' : type1402 A) : term54 A R R'.
Proof. exact (EQ_MP (@lem1231373 A R R') (@lem1231351 A R R')). Qed.
Lemma lem1231382 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (EQ_MP (@lem1110673 A r) (@lem1110672 A r)). Qed.
Lemma lem1231383 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (@lem1231382 A r). Qed.
Lemma lem1231384 {A : Type'} (R : type1402 A) : (@List.ForallOrdPairs A R (@nil A)) = True.
Proof. exact (@lem1231383 A R). Qed.
Lemma lem1231385 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231386 {A : Type'} (R : type1402 A) : (term55 A R) = (and True).
Proof. exact (MK_COMB (@lem1231385) (@lem1231384 A R)). Qed.
Lemma lem1231400 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1231401 {A : Type'} (x : A) : (@List.In A x (@nil A)) = False.
Proof. exact (@lem1231400 A x). Qed.
Lemma lem1231402 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231403 {A : Type'} (x : A) : (term56 A x) = (and False).
Proof. exact (MK_COMB (@lem1231402) (@lem1231401 A x)). Qed.
Lemma lem1231407 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1231408 {A : Type'} (x : A) : (@List.In A x (@nil A)) = False.
Proof. exact (@lem1231407 A x). Qed.
Lemma lem1231409 {A : Type'} (y : A) : (@List.In A y (@nil A)) = False.
Proof. exact (@lem1231408 A y). Qed.
Lemma lem1231410 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231411 {A : Type'} (y : A) : (term56 A y) = (and False).
Proof. exact (MK_COMB (@lem1231410) (@lem1231409 A y)). Qed.
Lemma lem1231412 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem1231413 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term57 A R x y) = (term58 A R x y).
Proof. exact (MK_COMB (@lem1231411 A y) (@lem1231412 A R x y)). Qed.
Lemma lem1231415 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1231416 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term58 A R x y) = False.
Proof. exact (@lem1231415 (R x y)). Qed.
Lemma lem1231417 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term57 A R x y) = False.
Proof. exact (TRANS (@lem1231413 A R x y) (@lem1231416 A R x y)). Qed.
Lemma lem1231418 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term59 A R x y) = (False /\ False).
Proof. exact (MK_COMB (@lem1231403 A x) (@lem1231417 A R x y)). Qed.
Lemma lem1231420 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem1231421 : (False /\ False) = False.
Proof. exact (@lem1231420 False). Qed.
Lemma lem1231422 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term59 A R x y) = False.
Proof. exact (TRANS (@lem1231418 A R x y) (@lem1231421)). Qed.
Lemma lem1231423 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231424 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term60 A R x y) = (imp False).
Proof. exact (MK_COMB (@lem1231423) (@lem1231422 A R x y)). Qed.
Lemma lem1231425 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (R' x y) = (R' x y).
Proof. exact (eq_refl (R' x y)). Qed.
Lemma lem1231426 {A : Type'} (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term61 A R R' x y) = (term62 A R' x y).
Proof. exact (MK_COMB (@lem1231424 A R x y) (@lem1231425 A R' x y)). Qed.
Lemma lem1231428 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1231429 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (term62 A R' x y) = True.
Proof. exact (@lem1231428 (R' x y)). Qed.
Lemma lem1231430 {A : Type'} (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term61 A R R' x y) = True.
Proof. exact (TRANS (@lem1231426 A R R' x y) (@lem1231429 A R' x y)). Qed.
Lemma lem1231431 {A : Type'} (R : type1402 A) (R' : type1402 A) (x : A) : (term63 A R R' x) = (term64 A).
Proof. exact (fun_ext (fun y : A => @lem1231430 A R R' x y)). Qed.
Lemma lem1231432 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231433 {A : Type'} (R : type1402 A) (R' : type1402 A) (x : A) : (term65 A R R' x) = (term66 A).
Proof. exact (MK_COMB (@lem1231432 A) (@lem1231431 A R R' x)). Qed.
Lemma lem1231435 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1231436 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (@lem1231435 A t). Qed.
Lemma lem1231437 {A : Type'} : (term66 A) = True.
Proof. exact (@lem1231436 A True). Qed.
Lemma lem1231438 {A : Type'} (R : type1402 A) (R' : type1402 A) (x : A) : (term65 A R R' x) = True.
Proof. exact (TRANS (@lem1231433 A R R' x) (@lem1231437 A)). Qed.
Lemma lem1231439 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term68 A R R') = (term64 A).
Proof. exact (fun_ext (fun x : A => @lem1231438 A R R' x)). Qed.
Lemma lem1231440 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231441 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term69 A R R') = (term66 A).
Proof. exact (MK_COMB (@lem1231440 A) (@lem1231439 A R R')). Qed.
Lemma lem1231443 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1231444 {A : Type'} (t : Prop) : (term67 A t) = t.
Proof. exact (@lem1231443 A t). Qed.
Lemma lem1231445 {A : Type'} : (term66 A) = True.
Proof. exact (@lem1231444 A True). Qed.
Lemma lem1231446 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term69 A R R') = True.
Proof. exact (TRANS (@lem1231441 A R R') (@lem1231445 A)). Qed.
Lemma lem1231447 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term70 A R R') = (True /\ True).
Proof. exact (MK_COMB (@lem1231386 A R) (@lem1231446 A R R')). Qed.
Lemma lem1231449 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1231450 : (True /\ True) = True.
Proof. exact (@lem1231449 True). Qed.
Lemma lem1231451 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term70 A R R') = True.
Proof. exact (TRANS (@lem1231447 A R R') (@lem1231450)). Qed.
Lemma lem1231452 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231453 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term71 A R R') = (imp True).
Proof. exact (MK_COMB (@lem1231452) (@lem1231451 A R R')). Qed.
Lemma lem1231455 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (EQ_MP (@lem1110673 A r) (@lem1110672 A r)). Qed.
Lemma lem1231456 {A : Type'} (r : type1402 A) : (@List.ForallOrdPairs A r (@nil A)) = True.
Proof. exact (@lem1231455 A r). Qed.
Lemma lem1231457 {A : Type'} (R' : type1402 A) : (@List.ForallOrdPairs A R' (@nil A)) = True.
Proof. exact (@lem1231456 A R'). Qed.
Lemma lem1231458 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term28 A R R') = (True -> True).
Proof. exact (MK_COMB (@lem1231453 A R R') (@lem1231457 A R')). Qed.
Lemma lem1231460 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1231461 : (True -> True) = True.
Proof. exact (@lem1231460 True). Qed.
Lemma lem1231462 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term28 A R R') = True.
Proof. exact (TRANS (@lem1231458 A R R') (@lem1231461)). Qed.
Lemma lem1231463 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231464 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term30 A R R') = (and True).
Proof. exact (MK_COMB (@lem1231463) (@lem1231462 A R R')). Qed.
Lemma lem1231498 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term72 A r h t) = (term73 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1231499 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term72 A r h t) = (term73 A h r t).
Proof. exact (@lem1231498 A h r t). Qed.
Lemma lem1231500 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term72 A R a0 a1) = (term73 A a0 R a1).
Proof. exact (@lem1231499 A a0 R a1). Qed.
Lemma lem1231504 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1231328 _26777 l P) (@lem1231327 _26777 P l)). Qed.
Lemma lem1231505 {A : Type'} (l : list A) (P : A -> Prop) : (@List.Forall A P l) = (term7 A l P).
Proof. exact (@lem1231504 A l P). Qed.
Lemma lem1231506 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term74 A R a0 a1) = (term75 A a1 R a0).
Proof. exact (@lem1231505 A a1 (R a0)). Qed.
Lemma lem1231513 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231514 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term76 A R a0 a1) = (term77 A a1 R a0).
Proof. exact (MK_COMB (@lem1231513) (@lem1231506 A a1 R a0)). Qed.
Lemma lem1231515 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1231516 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term73 A a0 R a1) = (term78 A a0 R a1).
Proof. exact (MK_COMB (@lem1231514 A a1 R a0) (@lem1231515 A R a1)). Qed.
Lemma lem1231519 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term72 A R a0 a1) = (term78 A a0 R a1).
Proof. exact (TRANS (@lem1231500 A a0 R a1) (@lem1231516 A a0 R a1)). Qed.
Lemma lem1231520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231521 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term79 A R a0 a1) = (term80 A a0 R a1).
Proof. exact (MK_COMB (@lem1231520) (@lem1231519 A a0 R a1)). Qed.
Lemma lem1231535 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term81 _25376 x h t) = (term82 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1231536 {A : Type'} (h : A) (x : A) (t : list A) : (term81 A x h t) = (term82 A h x t).
Proof. exact (@lem1231535 A h x t). Qed.
Lemma lem1231537 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term81 A x a0 a1) = (term82 A a0 x a1).
Proof. exact (@lem1231536 A a0 x a1). Qed.
Lemma lem1231542 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231543 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term83 A x a0 a1) = (term84 A a0 x a1).
Proof. exact (MK_COMB (@lem1231542) (@lem1231537 A a0 x a1)). Qed.
Lemma lem1231547 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term81 _25376 x h t) = (term82 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1231548 {A : Type'} (h : A) (x : A) (t : list A) : (term81 A x h t) = (term82 A h x t).
Proof. exact (@lem1231547 A h x t). Qed.
Lemma lem1231549 {A : Type'} (a0 : A) (y : A) (a1 : list A) : (term81 A y a0 a1) = (term82 A a0 y a1).
Proof. exact (@lem1231548 A a0 y a1). Qed.
Lemma lem1231554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231555 {A : Type'} (a0 : A) (y : A) (a1 : list A) : (term83 A y a0 a1) = (term84 A a0 y a1).
Proof. exact (MK_COMB (@lem1231554) (@lem1231549 A a0 y a1)). Qed.
Lemma lem1231556 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (R x y).
Proof. exact (eq_refl (R x y)). Qed.
Lemma lem1231557 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term85 A a0 a1 R x y) = (term86 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1231555 A a0 y a1) (@lem1231556 A R x y)). Qed.
Lemma lem1231560 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term87 A a0 a1 R x y) = (term88 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1231543 A a0 x a1) (@lem1231557 A a0 a1 R x y)). Qed.
Lemma lem1231563 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231564 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term89 A a0 a1 R x y) = (term90 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1231563) (@lem1231560 A a0 a1 R x y)). Qed.
Lemma lem1231565 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (R' x y) = (R' x y).
Proof. exact (eq_refl (R' x y)). Qed.
Lemma lem1231566 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term91 A a0 a1 R R' x y) = (term92 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1231564 A a0 a1 R x y) (@lem1231565 A R' x y)). Qed.
Lemma lem1231569 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term93 A a0 a1 R R' x) = (term94 A a0 a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1231566 A a0 a1 R R' x y)). Qed.
Lemma lem1231570 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231571 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term95 A a0 a1 R R' x) = (term96 A a0 a1 R R' x).
Proof. exact (MK_COMB (@lem1231570 A) (@lem1231569 A a0 a1 R R' x)). Qed.
Lemma lem1231576 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term97 A a0 a1 R R') = (term98 A a0 a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1231571 A a0 a1 R R' x)). Qed.
Lemma lem1231577 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231578 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term99 A a0 a1 R R') = (term100 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1231577 A) (@lem1231576 A a0 a1 R R')). Qed.
Lemma lem1231583 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term101 A a0 a1 R R') = (term102 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1231521 A a0 R a1) (@lem1231578 A a0 a1 R R')). Qed.
Lemma lem1231586 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231587 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term103 A a0 a1 R R') = (term104 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1231586) (@lem1231583 A a0 a1 R R')). Qed.
Lemma lem1231589 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term72 A r h t) = (term73 A h r t).
Proof. exact (EQ_MP (@lem1110682 A h r t) (@lem1110681 A h r t)). Qed.
Lemma lem1231590 {A : Type'} (h : A) (r : type1402 A) (t : list A) : (term72 A r h t) = (term73 A h r t).
Proof. exact (@lem1231589 A h r t). Qed.
Lemma lem1231591 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term72 A R' a0 a1) = (term73 A a0 R' a1).
Proof. exact (@lem1231590 A a0 R' a1). Qed.
Lemma lem1231595 {_26777 : Type'} (l : list _26777) (P : _26777 -> Prop) : (@List.Forall _26777 P l) = (term7 _26777 l P).
Proof. exact (EQ_MP (@lem1231328 _26777 l P) (@lem1231327 _26777 P l)). Qed.
Lemma lem1231596 {A : Type'} (l : list A) (P : A -> Prop) : (@List.Forall A P l) = (term7 A l P).
Proof. exact (@lem1231595 A l P). Qed.
Lemma lem1231597 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term74 A R' a0 a1) = (term75 A a1 R' a0).
Proof. exact (@lem1231596 A a1 (R' a0)). Qed.
Lemma lem1231604 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231605 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term76 A R' a0 a1) = (term77 A a1 R' a0).
Proof. exact (MK_COMB (@lem1231604) (@lem1231597 A a1 R' a0)). Qed.
Lemma lem1231606 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1231607 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term73 A a0 R' a1) = (term78 A a0 R' a1).
Proof. exact (MK_COMB (@lem1231605 A a1 R' a0) (@lem1231606 A R' a1)). Qed.
Lemma lem1231610 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term72 A R' a0 a1) = (term78 A a0 R' a1).
Proof. exact (TRANS (@lem1231591 A a0 R' a1) (@lem1231607 A a0 R' a1)). Qed.
Lemma lem1231611 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) (a1 : list A) : (term36 A R R' a0 a1) = (term105 A R a0 R' a1).
Proof. exact (MK_COMB (@lem1231587 A a0 a1 R R') (@lem1231610 A a0 R' a1)). Qed.
Lemma lem1231614 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term34 A R R' a1) = (term34 A R R' a1).
Proof. exact (eq_refl (term34 A R R' a1)). Qed.
Lemma lem1231615 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) (a1 : list A) : (term38 A R R' a0 a1) = (term106 A R a0 R' a1).
Proof. exact (MK_COMB (@lem1231614 A R R' a1) (@lem1231611 A R a0 R' a1)). Qed.
Lemma lem1231618 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) : (term40 A R R' a0) = (term107 A R a0 R').
Proof. exact (fun_ext (fun a1 : list A => @lem1231615 A R a0 R' a1)). Qed.
Lemma lem1231619 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1231620 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) : (term42 A R R' a0) = (term108 A R a0 R').
Proof. exact (MK_COMB (@lem1231619 A) (@lem1231618 A R a0 R')). Qed.
Lemma lem1231625 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term44 A R R') = (term109 A R R').
Proof. exact (fun_ext (fun a0 : A => @lem1231620 A R a0 R')). Qed.
Lemma lem1231626 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231627 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term46 A R R') = (term110 A R R').
Proof. exact (MK_COMB (@lem1231626 A) (@lem1231625 A R R')). Qed.
Lemma lem1231632 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term48 A R R') = (term111 A R R').
Proof. exact (MK_COMB (@lem1231464 A R R') (@lem1231627 A R R')). Qed.
Lemma lem1231634 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1231635 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term111 A R R') = (term110 A R R').
Proof. exact (@lem1231634 (term110 A R R')). Qed.
Lemma lem1231706 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term48 A R R') = (term110 A R R').
Proof. exact (TRANS (@lem1231632 A R R') (@lem1231635 A R R')). Qed.
Lemma lem1231707 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term110 A R R') = (term48 A R R').
Proof. exact (SYM (@lem1231706 A R R')). Qed.
Lemma lem1231709 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1231710 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term110 A R R') = (term113 A R R').
Proof. exact (@lem1231709 (term110 A R R')). Qed.
Lemma lem1231711 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term113 A R R') = (term110 A R R').
Proof. exact (SYM (@lem1231710 A R R')). Qed.
Lemma lem1231712 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term114 A R R') : term114 A R R'.
Proof. exact (h1). Qed.
Lemma lem1231715 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term113 A R R') : term113 A R R'.
Proof. exact (h1). Qed.
Lemma lem1231716 {A : Type'} (R : type1402 A) (R' : type1402 A) : term115 A R R'.
Proof. exact (fun h0 : term113 A R R' => @lem1231715 A R R' h0). Qed.
Lemma lem1231717 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term115 A R R') : term115 A R R'.
Proof. exact (h1). Qed.
Lemma lem1231718 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term113 A R R') : term113 A R R'.
Proof. exact (h1). Qed.
Lemma lem1231719 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term113 A R R') (h2 : term115 A R R') : term113 A R R'.
Proof. exact (@lem1231717 A R R' h2 (@lem1231718 A R R' h1)). Qed.
Lemma lem1231720 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term113 A R R') : term116 A R R'.
Proof. exact (fun h0 : term115 A R R' => @lem1231719 A R R' h1 h0). Qed.
Lemma lem1231721 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term115 A R R') : term115 A R R'.
Proof. exact (h1). Qed.
Lemma lem1231722 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term113 A R R') (h2 : term115 A R R') : term113 A R R'.
Proof. exact (@lem1231720 A R R' h1 (@lem1231721 A R R' h2)). Qed.
Lemma lem1231723 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term115 A R R') : term115 A R R'.
Proof. exact (fun h0 : term113 A R R' => @lem1231722 A R R' h0 h1). Qed.
Lemma lem1231724 {A : Type'} (R : type1402 A) (R' : type1402 A) : term117 A R R'.
Proof. exact (fun h0 : term115 A R R' => @lem1231723 A R R' h0). Qed.
Lemma lem1231727 {A : Type'} (R : type1402 A) (R' : type1402 A) : term115 A R R'.
Proof. exact (@lem1231724 A R R' (@lem1231716 A R R')). Qed.
Lemma lem1231728 {A : Type'} (R : type1402 A) (R' : type1402 A) : term115 A R R'.
Proof. exact (@lem1231727 A R R'). Qed.
Lemma lem1231738 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1231739 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term113 A R R') = (term118 A R R').
Proof. exact (@lem1231738 (term114 A R R')). Qed.
Lemma lem1231741 (t : Prop) : (term119 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1231742 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term118 A R R') = (term110 A R R').
Proof. exact (@lem1231741 (term110 A R R')). Qed.
Lemma lem1231747 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term113 A R R') = (term110 A R R').
Proof. exact (TRANS (@lem1231739 A R R') (@lem1231742 A R R')). Qed.
Lemma lem1231810 {A : Type'} (R' : type1402 A) : (term120 A R') = (term121 A R').
Proof. exact (fun_ext (fun R : type1402 A => @lem1231747 A R R')). Qed.
Lemma lem1231811 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1231812 {A : Type'} (R' : type1402 A) : (term122 A R') = (term123 A R').
Proof. exact (MK_COMB (@lem1231811 A) (@lem1231810 A R')). Qed.
Lemma lem1231817 {A : Type'} : (term124 A) = (term125 A).
Proof. exact (fun_ext (fun R' : type1402 A => @lem1231812 A R')). Qed.
Lemma lem1231818 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1231827 {A : Type'} : (term126 A) = (term127 A).
Proof. exact (MK_COMB (@lem1231818 A) (@lem1231817 A)). Qed.
Lemma lem1231828 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1231833 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term128 A a1 R' a0 x) = (term128 A a1 R' a0 x).
Proof. exact (eq_refl (term128 A a1 R' a0 x)). Qed.
Lemma lem1231834 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term129 A a1 R' a0) = (term129 A a1 R' a0).
Proof. exact (fun_ext (fun x : A => @lem1231833 A a1 R' a0 x)). Qed.
Lemma lem1231835 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231836 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term75 A a1 R' a0) = (term75 A a1 R' a0).
Proof. exact (MK_COMB (@lem1231835 A) (@lem1231834 A a1 R' a0)). Qed.
Lemma lem1231837 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231838 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term77 A a1 R' a0) = (term77 A a1 R' a0).
Proof. exact (MK_COMB (@lem1231837) (@lem1231836 A a1 R' a0)). Qed.
Lemma lem1231839 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term78 A a0 R' a1) = (term78 A a0 R' a1).
Proof. exact (MK_COMB (@lem1231838 A a1 R' a0) (@lem1231828 A R' a1)). Qed.
Lemma lem1231860 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term92 A a0 a1 R R' x y) = (term92 A a0 a1 R R' x y).
Proof. exact (eq_refl (term92 A a0 a1 R R' x y)). Qed.
Lemma lem1231861 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term94 A a0 a1 R R' x) = (term94 A a0 a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1231860 A a0 a1 R R' x y)). Qed.
Lemma lem1231862 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231863 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term96 A a0 a1 R R' x) = (term96 A a0 a1 R R' x).
Proof. exact (MK_COMB (@lem1231862 A) (@lem1231861 A a0 a1 R R' x)). Qed.
Lemma lem1231864 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term98 A a0 a1 R R') = (term98 A a0 a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1231863 A a0 a1 R R' x)). Qed.
Lemma lem1231865 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231866 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term100 A a0 a1 R R') = (term100 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1231865 A) (@lem1231864 A a0 a1 R R')). Qed.
Lemma lem1231867 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1231872 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term128 A a1 R a0 x) = (term128 A a1 R a0 x).
Proof. exact (eq_refl (term128 A a1 R a0 x)). Qed.
Lemma lem1231873 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term129 A a1 R a0) = (term129 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1231872 A a1 R a0 x)). Qed.
Lemma lem1231874 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231875 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term75 A a1 R a0) = (term75 A a1 R a0).
Proof. exact (MK_COMB (@lem1231874 A) (@lem1231873 A a1 R a0)). Qed.
Lemma lem1231876 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231877 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term77 A a1 R a0) = (term77 A a1 R a0).
Proof. exact (MK_COMB (@lem1231876) (@lem1231875 A a1 R a0)). Qed.
Lemma lem1231878 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term78 A a0 R a1) = (term78 A a0 R a1).
Proof. exact (MK_COMB (@lem1231877 A a1 R a0) (@lem1231867 A R a1)). Qed.
Lemma lem1231879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1231880 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term80 A a0 R a1) = (term80 A a0 R a1).
Proof. exact (MK_COMB (@lem1231879) (@lem1231878 A a0 R a1)). Qed.
Lemma lem1231881 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term102 A a0 a1 R R') = (term102 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1231880 A a0 R a1) (@lem1231866 A a0 a1 R R')). Qed.
Lemma lem1231882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231883 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term104 A a0 a1 R R') = (term104 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1231882) (@lem1231881 A a0 a1 R R')). Qed.
Lemma lem1231884 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) (a1 : list A) : (term105 A R a0 R' a1) = (term105 A R a0 R' a1).
Proof. exact (MK_COMB (@lem1231883 A a0 a1 R R') (@lem1231839 A a0 R' a1)). Qed.
Lemma lem1231885 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1231898 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term130 A a1 R R' x y) = (term130 A a1 R R' x y).
Proof. exact (eq_refl (term130 A a1 R R' x y)). Qed.
Lemma lem1231899 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term131 A a1 R R' x) = (term131 A a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1231898 A a1 R R' x y)). Qed.
Lemma lem1231900 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231901 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term132 A a1 R R' x) = (term132 A a1 R R' x).
Proof. exact (MK_COMB (@lem1231900 A) (@lem1231899 A a1 R R' x)). Qed.
Lemma lem1231902 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term133 A a1 R R') = (term133 A a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1231901 A a1 R R' x)). Qed.
Lemma lem1231903 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231904 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term134 A a1 R R') = (term134 A a1 R R').
Proof. exact (MK_COMB (@lem1231903 A) (@lem1231902 A a1 R R')). Qed.
Lemma lem1231907 {A : Type'} (R : type1402 A) (a1 : list A) : (term135 A R a1) = (term135 A R a1).
Proof. exact (eq_refl (term135 A R a1)). Qed.
Lemma lem1231908 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term136 A a1 R R') = (term136 A a1 R R').
Proof. exact (MK_COMB (@lem1231907 A R a1) (@lem1231904 A a1 R R')). Qed.
Lemma lem1231909 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231910 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term137 A a1 R R') = (term137 A a1 R R').
Proof. exact (MK_COMB (@lem1231909) (@lem1231908 A a1 R R')). Qed.
Lemma lem1231911 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term32 A R R' a1) = (term32 A R R' a1).
Proof. exact (MK_COMB (@lem1231910 A a1 R R') (@lem1231885 A R' a1)). Qed.
Lemma lem1231912 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1231913 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term34 A R R' a1) = (term34 A R R' a1).
Proof. exact (MK_COMB (@lem1231912) (@lem1231911 A R R' a1)). Qed.
Lemma lem1231914 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) (a1 : list A) : (term106 A R a0 R' a1) = (term106 A R a0 R' a1).
Proof. exact (MK_COMB (@lem1231913 A R R' a1) (@lem1231884 A R a0 R' a1)). Qed.
Lemma lem1231915 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) : (term107 A R a0 R') = (term107 A R a0 R').
Proof. exact (fun_ext (fun a1 : list A => @lem1231914 A R a0 R' a1)). Qed.
Lemma lem1231916 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1231917 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) : (term108 A R a0 R') = (term108 A R a0 R').
Proof. exact (MK_COMB (@lem1231916 A) (@lem1231915 A R a0 R')). Qed.
Lemma lem1231918 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term109 A R R') = (term109 A R R').
Proof. exact (fun_ext (fun a0 : A => @lem1231917 A R a0 R')). Qed.
Lemma lem1231919 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1231920 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term110 A R R') = (term110 A R R').
Proof. exact (MK_COMB (@lem1231919 A) (@lem1231918 A R R')). Qed.
Lemma lem1231921 {A : Type'} (R' : type1402 A) : (term121 A R') = (term121 A R').
Proof. exact (fun_ext (fun R : type1402 A => @lem1231920 A R R')). Qed.
Lemma lem1231922 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1231923 {A : Type'} (R' : type1402 A) : (term123 A R') = (term123 A R').
Proof. exact (MK_COMB (@lem1231922 A) (@lem1231921 A R')). Qed.
Lemma lem1231924 {A : Type'} : (term125 A) = (term125 A).
Proof. exact (fun_ext (fun R' : type1402 A => @lem1231923 A R')). Qed.
Lemma lem1231925 {A : Type'} : (@all (A -> A -> Prop)) = (@all (A -> A -> Prop)).
Proof. exact (eq_refl (@all (A -> A -> Prop))). Qed.
Lemma lem1231926 {A : Type'} : (term127 A) = (term127 A).
Proof. exact (MK_COMB (@lem1231925 A) (@lem1231924 A)). Qed.
Lemma lem1232023 {A : Type'} : (term126 A) = (term127 A).
Proof. exact (TRANS (@lem1231827 A) (@lem1231926 A)). Qed.
Lemma lem1232024 {A : Type'} : (term127 A) = (term126 A).
Proof. exact (SYM (@lem1232023 A)). Qed.
Lemma lem1232025 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term32 A R R' a1) : term32 A R R' a1.
Proof. exact (h1). Qed.
Lemma lem1232026 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term102 A a0 a1 R R'.
Proof. exact (h1). Qed.
Lemma lem1232028 (p : Prop) : p = (term112 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1232029 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term78 A a0 R' a1) = (term138 A a0 R' a1).
Proof. exact (@lem1232028 (term78 A a0 R' a1)). Qed.
Lemma lem1232030 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term138 A a0 R' a1) = (term78 A a0 R' a1).
Proof. exact (SYM (@lem1232029 A a0 R' a1)). Qed.
Lemma lem1232031 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) (h1 : term139 A a0 R' a1) : term139 A a0 R' a1.
Proof. exact (h1). Qed.
Lemma lem1232047 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term140 A a1 R R' x y) = (term141 A a1 R R' x y).
Proof. exact (@lem17362 (term142 A a1 R x y) (R' x y)). Qed.
Lemma lem1232048 {A : Type'} (P : A -> Prop) : (term143 A P) = (term144 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1232049 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term145 A a1 R R' x) = (term146 A a1 R R' x).
Proof. exact (@lem1232048 A (term131 A a1 R R' x)). Qed.
Lemma lem1232050 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term147 A a1 R R' x y) = (term130 A a1 R R' x y).
Proof. exact (eq_refl (term147 A a1 R R' x y)). Qed.
Lemma lem1232051 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1232052 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term148 A a1 R R' x y) = (term140 A a1 R R' x y).
Proof. exact (MK_COMB (@lem1232051) (@lem1232050 A a1 R R' x y)). Qed.
Lemma lem1232053 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term148 A a1 R R' x y) = (term141 A a1 R R' x y).
Proof. exact (TRANS (@lem1232052 A a1 R R' x y) (@lem1232047 A a1 R R' x y)). Qed.
Lemma lem1232054 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term149 A a1 R R' x) = (term150 A a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1232053 A a1 R R' x y)). Qed.
Lemma lem1232055 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232056 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term146 A a1 R R' x) = (term151 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232055 A) (@lem1232054 A a1 R R' x)). Qed.
Lemma lem1232057 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term145 A a1 R R' x) = (term151 A a1 R R' x).
Proof. exact (TRANS (@lem1232049 A a1 R R' x) (@lem1232056 A a1 R R' x)). Qed.
Lemma lem1232058 {A : Type'} (P : A -> Prop) : (term143 A P) = (term144 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1232059 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term152 A a1 R R') = (term153 A a1 R R').
Proof. exact (@lem1232058 A (term133 A a1 R R')). Qed.
Lemma lem1232060 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term154 A a1 R R' x) = (term132 A a1 R R' x).
Proof. exact (eq_refl (term154 A a1 R R' x)). Qed.
Lemma lem1232061 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1232062 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term155 A a1 R R' x) = (term145 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232061) (@lem1232060 A a1 R R' x)). Qed.
Lemma lem1232063 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term155 A a1 R R' x) = (term151 A a1 R R' x).
Proof. exact (TRANS (@lem1232062 A a1 R R' x) (@lem1232057 A a1 R R' x)). Qed.
Lemma lem1232064 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term156 A a1 R R') = (term157 A a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1232063 A a1 R R' x)). Qed.
Lemma lem1232065 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232066 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term153 A a1 R R') = (term158 A a1 R R').
Proof. exact (MK_COMB (@lem1232065 A) (@lem1232064 A a1 R R')). Qed.
Lemma lem1232067 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term152 A a1 R R') = (term158 A a1 R R').
Proof. exact (TRANS (@lem1232059 A a1 R R') (@lem1232066 A a1 R R')). Qed.
Lemma lem1232069 {A : Type'} (R : type1402 A) (a1 : list A) : (term159 A R a1) = (term159 A R a1).
Proof. exact (eq_refl (term159 A R a1)). Qed.
Lemma lem1232070 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term160 A a1 R R') = (term161 A a1 R R').
Proof. exact (MK_COMB (@lem1232069 A R a1) (@lem1232067 A a1 R R')). Qed.
Lemma lem1232071 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term162 A a1 R R') = (term160 A a1 R R').
Proof. exact (@lem17045 (@List.ForallOrdPairs A R a1) (term134 A a1 R R')). Qed.
Lemma lem1232072 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term162 A a1 R R') = (term161 A a1 R R').
Proof. exact (TRANS (@lem1232071 A a1 R R') (@lem1232070 A a1 R R')). Qed.
Lemma lem1232073 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232074 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232075 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term163 A a1 R R') = (term164 A a1 R R').
Proof. exact (MK_COMB (@lem1232074) (@lem1232072 A a1 R R')). Qed.
Lemma lem1232076 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term165 A R R' a1) = (term166 A R R' a1).
Proof. exact (MK_COMB (@lem1232075 A a1 R R') (@lem1232073 A R' a1)). Qed.
Lemma lem1232077 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term32 A R R' a1) = (term165 A R R' a1).
Proof. exact (@lem17265 (term136 A a1 R R') (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232078 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term32 A R R' a1) = (term166 A R R' a1).
Proof. exact (TRANS (@lem1232077 A R R' a1) (@lem1232076 A R R' a1)). Qed.
Lemma lem1232133 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1232134 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem1232133 A P Q). Qed.
Lemma lem1232135 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term169 A a1 R R') = (term170 A a1 R R').
Proof. exact (@lem1232134 A (term171 A R a1) (term157 A a1 R R')). Qed.
Lemma lem1232136 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term172 A a1 R R' x) = (term151 A a1 R R' x).
Proof. exact (eq_refl (term172 A a1 R R' x)). Qed.
Lemma lem1232137 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term173 A a1 R R') = (term157 A a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1232136 A a1 R R' x)). Qed.
Lemma lem1232138 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232139 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term174 A a1 R R') = (term158 A a1 R R').
Proof. exact (MK_COMB (@lem1232138 A) (@lem1232137 A a1 R R')). Qed.
Lemma lem1232140 {A : Type'} (R : type1402 A) (a1 : list A) : (term159 A R a1) = (term159 A R a1).
Proof. exact (eq_refl (term159 A R a1)). Qed.
Lemma lem1232141 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term169 A a1 R R') = (term161 A a1 R R').
Proof. exact (MK_COMB (@lem1232140 A R a1) (@lem1232139 A a1 R R')). Qed.
Lemma lem1232142 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1232143 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term175 A a1 R R') = (term176 A a1 R R').
Proof. exact (MK_COMB (@lem1232142) (@lem1232141 A a1 R R')). Qed.
Lemma lem1232144 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term172 A a1 R R' x) = (term151 A a1 R R' x).
Proof. exact (eq_refl (term172 A a1 R R' x)). Qed.
Lemma lem1232145 {A : Type'} (R : type1402 A) (a1 : list A) : (term159 A R a1) = (term159 A R a1).
Proof. exact (eq_refl (term159 A R a1)). Qed.
Lemma lem1232146 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term177 A a1 R R' x) = (term178 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232145 A R a1) (@lem1232144 A a1 R R' x)). Qed.
Lemma lem1232147 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term179 A a1 R R') = (term180 A a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1232146 A a1 R R' x)). Qed.
Lemma lem1232148 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232149 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term170 A a1 R R') = (term181 A a1 R R').
Proof. exact (MK_COMB (@lem1232148 A) (@lem1232147 A a1 R R')). Qed.
Lemma lem1232150 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : ((term169 A a1 R R') = (term170 A a1 R R')) = ((term161 A a1 R R') = (term181 A a1 R R')).
Proof. exact (MK_COMB (@lem1232143 A a1 R R') (@lem1232149 A a1 R R')). Qed.
Lemma lem1232151 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term161 A a1 R R') = (term181 A a1 R R').
Proof. exact (EQ_MP (@lem1232150 A a1 R R') (@lem1232135 A a1 R R')). Qed.
Lemma lem1232153 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem1232154 {A : Type'} (P : Prop) (Q : A -> Prop) : (term167 A P Q) = (term168 A P Q).
Proof. exact (@lem1232153 A P Q). Qed.
Lemma lem1232155 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term182 A a1 R R' x) = (term183 A a1 R R' x).
Proof. exact (@lem1232154 A (term171 A R a1) (term150 A a1 R R' x)). Qed.
Lemma lem1232156 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term184 A a1 R R' x y) = (term141 A a1 R R' x y).
Proof. exact (eq_refl (term184 A a1 R R' x y)). Qed.
Lemma lem1232157 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term185 A a1 R R' x) = (term150 A a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1232156 A a1 R R' x y)). Qed.
Lemma lem1232158 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232159 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term186 A a1 R R' x) = (term151 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232158 A) (@lem1232157 A a1 R R' x)). Qed.
Lemma lem1232160 {A : Type'} (R : type1402 A) (a1 : list A) : (term159 A R a1) = (term159 A R a1).
Proof. exact (eq_refl (term159 A R a1)). Qed.
Lemma lem1232161 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term182 A a1 R R' x) = (term178 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232160 A R a1) (@lem1232159 A a1 R R' x)). Qed.
Lemma lem1232162 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1232163 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term187 A a1 R R' x) = (term188 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232162) (@lem1232161 A a1 R R' x)). Qed.
Lemma lem1232164 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term184 A a1 R R' x y) = (term141 A a1 R R' x y).
Proof. exact (eq_refl (term184 A a1 R R' x y)). Qed.
Lemma lem1232165 {A : Type'} (R : type1402 A) (a1 : list A) : (term159 A R a1) = (term159 A R a1).
Proof. exact (eq_refl (term159 A R a1)). Qed.
Lemma lem1232166 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term189 A a1 R R' x y) = (term190 A a1 R R' x y).
Proof. exact (MK_COMB (@lem1232165 A R a1) (@lem1232164 A a1 R R' x y)). Qed.
Lemma lem1232167 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term191 A a1 R R' x) = (term192 A a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1232166 A a1 R R' x y)). Qed.
Lemma lem1232168 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232169 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term183 A a1 R R' x) = (term193 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232168 A) (@lem1232167 A a1 R R' x)). Qed.
Lemma lem1232170 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : ((term182 A a1 R R' x) = (term183 A a1 R R' x)) = ((term178 A a1 R R' x) = (term193 A a1 R R' x)).
Proof. exact (MK_COMB (@lem1232163 A a1 R R' x) (@lem1232169 A a1 R R' x)). Qed.
Lemma lem1232171 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term178 A a1 R R' x) = (term193 A a1 R R' x).
Proof. exact (EQ_MP (@lem1232170 A a1 R R' x) (@lem1232155 A a1 R R' x)). Qed.
Lemma lem1232172 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term180 A a1 R R') = (term194 A a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1232171 A a1 R R' x)). Qed.
Lemma lem1232173 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232174 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term181 A a1 R R') = (term195 A a1 R R').
Proof. exact (MK_COMB (@lem1232173 A) (@lem1232172 A a1 R R')). Qed.
Lemma lem1232175 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term161 A a1 R R') = (term195 A a1 R R').
Proof. exact (TRANS (@lem1232151 A a1 R R') (@lem1232174 A a1 R R')). Qed.
Lemma lem1232176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232177 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term164 A a1 R R') = (term196 A a1 R R').
Proof. exact (MK_COMB (@lem1232176) (@lem1232175 A a1 R R')). Qed.
Lemma lem1232178 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232179 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term166 A R R' a1) = (term197 A R R' a1).
Proof. exact (MK_COMB (@lem1232177 A a1 R R') (@lem1232178 A R' a1)). Qed.
Lemma lem1232181 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1232182 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (@lem1232181 A P Q). Qed.
Lemma lem1232183 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term200 A R R' a1) = (term201 A R R' a1).
Proof. exact (@lem1232182 A (term194 A a1 R R') (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232184 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term202 A a1 R R' x) = (term193 A a1 R R' x).
Proof. exact (eq_refl (term202 A a1 R R' x)). Qed.
Lemma lem1232185 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term203 A a1 R R') = (term194 A a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1232184 A a1 R R' x)). Qed.
Lemma lem1232186 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232187 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term204 A a1 R R') = (term195 A a1 R R').
Proof. exact (MK_COMB (@lem1232186 A) (@lem1232185 A a1 R R')). Qed.
Lemma lem1232188 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232189 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term205 A a1 R R') = (term196 A a1 R R').
Proof. exact (MK_COMB (@lem1232188) (@lem1232187 A a1 R R')). Qed.
Lemma lem1232190 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232191 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term200 A R R' a1) = (term197 A R R' a1).
Proof. exact (MK_COMB (@lem1232189 A a1 R R') (@lem1232190 A R' a1)). Qed.
Lemma lem1232192 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1232193 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term206 A R R' a1) = (term207 A R R' a1).
Proof. exact (MK_COMB (@lem1232192) (@lem1232191 A R R' a1)). Qed.
Lemma lem1232194 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term202 A a1 R R' x) = (term193 A a1 R R' x).
Proof. exact (eq_refl (term202 A a1 R R' x)). Qed.
Lemma lem1232195 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232196 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term208 A a1 R R' x) = (term209 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232195) (@lem1232194 A a1 R R' x)). Qed.
Lemma lem1232197 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232198 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : (term210 A R x R' a1) = (term211 A R x R' a1).
Proof. exact (MK_COMB (@lem1232196 A a1 R R' x) (@lem1232197 A R' a1)). Qed.
Lemma lem1232199 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term212 A R R' a1) = (term213 A R R' a1).
Proof. exact (fun_ext (fun x : A => @lem1232198 A R x R' a1)). Qed.
Lemma lem1232200 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232201 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term201 A R R' a1) = (term214 A R R' a1).
Proof. exact (MK_COMB (@lem1232200 A) (@lem1232199 A R R' a1)). Qed.
Lemma lem1232202 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : ((term200 A R R' a1) = (term201 A R R' a1)) = ((term197 A R R' a1) = (term214 A R R' a1)).
Proof. exact (MK_COMB (@lem1232193 A R R' a1) (@lem1232201 A R R' a1)). Qed.
Lemma lem1232203 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term197 A R R' a1) = (term214 A R R' a1).
Proof. exact (EQ_MP (@lem1232202 A R R' a1) (@lem1232183 A R R' a1)). Qed.
Lemma lem1232205 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1232206 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (@lem1232205 A P Q). Qed.
Lemma lem1232207 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : (term215 A R x R' a1) = (term216 A R x R' a1).
Proof. exact (@lem1232206 A (term192 A a1 R R' x) (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232208 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term217 A a1 R R' x y) = (term190 A a1 R R' x y).
Proof. exact (eq_refl (term217 A a1 R R' x y)). Qed.
Lemma lem1232209 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term218 A a1 R R' x) = (term192 A a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1232208 A a1 R R' x y)). Qed.
Lemma lem1232210 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232211 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term219 A a1 R R' x) = (term193 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232210 A) (@lem1232209 A a1 R R' x)). Qed.
Lemma lem1232212 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232213 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term220 A a1 R R' x) = (term209 A a1 R R' x).
Proof. exact (MK_COMB (@lem1232212) (@lem1232211 A a1 R R' x)). Qed.
Lemma lem1232214 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232215 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : (term215 A R x R' a1) = (term211 A R x R' a1).
Proof. exact (MK_COMB (@lem1232213 A a1 R R' x) (@lem1232214 A R' a1)). Qed.
Lemma lem1232216 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1232217 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : (term221 A R x R' a1) = (term222 A R x R' a1).
Proof. exact (MK_COMB (@lem1232216) (@lem1232215 A R x R' a1)). Qed.
Lemma lem1232218 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term217 A a1 R R' x y) = (term190 A a1 R R' x y).
Proof. exact (eq_refl (term217 A a1 R R' x y)). Qed.
Lemma lem1232219 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232220 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term223 A a1 R R' x y) = (term224 A a1 R R' x y).
Proof. exact (MK_COMB (@lem1232219) (@lem1232218 A a1 R R' x y)). Qed.
Lemma lem1232221 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232222 {A : Type'} (R : type1402 A) (x : A) (y : A) (R' : type1402 A) (a1 : list A) : (term225 A R x y R' a1) = (term226 A R x y R' a1).
Proof. exact (MK_COMB (@lem1232220 A a1 R R' x y) (@lem1232221 A R' a1)). Qed.
Lemma lem1232223 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : (term227 A R x R' a1) = (term228 A R x R' a1).
Proof. exact (fun_ext (fun y : A => @lem1232222 A R x y R' a1)). Qed.
Lemma lem1232224 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232225 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : (term216 A R x R' a1) = (term229 A R x R' a1).
Proof. exact (MK_COMB (@lem1232224 A) (@lem1232223 A R x R' a1)). Qed.
Lemma lem1232226 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : ((term215 A R x R' a1) = (term216 A R x R' a1)) = ((term211 A R x R' a1) = (term229 A R x R' a1)).
Proof. exact (MK_COMB (@lem1232217 A R x R' a1) (@lem1232225 A R x R' a1)). Qed.
Lemma lem1232227 {A : Type'} (R : type1402 A) (x : A) (R' : type1402 A) (a1 : list A) : (term211 A R x R' a1) = (term229 A R x R' a1).
Proof. exact (EQ_MP (@lem1232226 A R x R' a1) (@lem1232207 A R x R' a1)). Qed.
Lemma lem1232228 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term213 A R R' a1) = (term230 A R R' a1).
Proof. exact (fun_ext (fun x : A => @lem1232227 A R x R' a1)). Qed.
Lemma lem1232229 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232230 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term214 A R R' a1) = (term231 A R R' a1).
Proof. exact (MK_COMB (@lem1232229 A) (@lem1232228 A R R' a1)). Qed.
Lemma lem1232231 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term197 A R R' a1) = (term231 A R R' a1).
Proof. exact (TRANS (@lem1232203 A R R' a1) (@lem1232230 A R R' a1)). Qed.
Lemma lem1232233 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term166 A R R' a1) = (term231 A R R' a1).
Proof. exact (TRANS (@lem1232179 A R R' a1) (@lem1232231 A R R' a1)). Qed.
Lemma lem1232234 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) : (term32 A R R' a1) = (term231 A R R' a1).
Proof. exact (TRANS (@lem1232078 A R R' a1) (@lem1232233 A R R' a1)). Qed.
Lemma lem1232235 {A : Type'} (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term32 A R R' a1) : term231 A R R' a1.
Proof. exact (EQ_MP (@lem1232234 A R R' a1) (@lem1232025 A R R' a1 h1)). Qed.
Lemma lem1232242 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term128 A a1 R a0 x) = (term232 A a1 R a0 x).
Proof. exact (@lem17265 (@List.In A x a1) (R a0 x)). Qed.
Lemma lem1232243 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term129 A a1 R a0) = (term233 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1232242 A a1 R a0 x)). Qed.
Lemma lem1232244 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1232245 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term75 A a1 R a0) = (term234 A a1 R a0).
Proof. exact (MK_COMB (@lem1232244 A) (@lem1232243 A a1 R a0)). Qed.
Lemma lem1232246 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1232247 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1232248 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term77 A a1 R a0) = (term235 A a1 R a0).
Proof. exact (MK_COMB (@lem1232247) (@lem1232245 A a1 R a0)). Qed.
Lemma lem1232249 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term78 A a0 R a1) = (term236 A a0 R a1).
Proof. exact (MK_COMB (@lem1232248 A a1 R a0) (@lem1232246 A R a1)). Qed.
Lemma lem1232256 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term237 A a0 x a1) = (term238 A a0 x a1).
Proof. exact (@lem17160 (x = a0) (@List.In A x a1)). Qed.
Lemma lem1232263 {A : Type'} (a0 : A) (y : A) (a1 : list A) : (term237 A a0 y a1) = (term238 A a0 y a1).
Proof. exact (@lem17160 (y = a0) (@List.In A y a1)). Qed.
Lemma lem1232264 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term239 A R x y) = (term239 A R x y).
Proof. exact (eq_refl (term239 A R x y)). Qed.
Lemma lem1232265 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232266 {A : Type'} (a0 : A) (y : A) (a1 : list A) : (term240 A a0 y a1) = (term241 A a0 y a1).
Proof. exact (MK_COMB (@lem1232265) (@lem1232263 A a0 y a1)). Qed.
Lemma lem1232267 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term242 A a0 a1 R x y) = (term243 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1232266 A a0 y a1) (@lem1232264 A R x y)). Qed.
Lemma lem1232268 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term244 A a0 a1 R x y) = (term242 A a0 a1 R x y).
Proof. exact (@lem17045 (term82 A a0 y a1) (R x y)). Qed.
Lemma lem1232269 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term244 A a0 a1 R x y) = (term243 A a0 a1 R x y).
Proof. exact (TRANS (@lem1232268 A a0 a1 R x y) (@lem1232267 A a0 a1 R x y)). Qed.
Lemma lem1232270 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232271 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term240 A a0 x a1) = (term241 A a0 x a1).
Proof. exact (MK_COMB (@lem1232270) (@lem1232256 A a0 x a1)). Qed.
Lemma lem1232272 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term245 A a0 a1 R x y) = (term246 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1232271 A a0 x a1) (@lem1232269 A a0 a1 R x y)). Qed.
Lemma lem1232273 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term247 A a0 a1 R x y) = (term245 A a0 a1 R x y).
Proof. exact (@lem17045 (term82 A a0 x a1) (term86 A a0 a1 R x y)). Qed.
Lemma lem1232274 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term247 A a0 a1 R x y) = (term246 A a0 a1 R x y).
Proof. exact (TRANS (@lem1232273 A a0 a1 R x y) (@lem1232272 A a0 a1 R x y)). Qed.
Lemma lem1232275 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (R' x y) = (R' x y).
Proof. exact (eq_refl (R' x y)). Qed.
Lemma lem1232276 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232277 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term248 A a0 a1 R x y) = (term249 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1232276) (@lem1232274 A a0 a1 R x y)). Qed.
Lemma lem1232278 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term250 A a0 a1 R R' x y) = (term251 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1232277 A a0 a1 R x y) (@lem1232275 A R' x y)). Qed.
Lemma lem1232279 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term92 A a0 a1 R R' x y) = (term250 A a0 a1 R R' x y).
Proof. exact (@lem17265 (term88 A a0 a1 R x y) (R' x y)). Qed.
Lemma lem1232280 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term92 A a0 a1 R R' x y) = (term251 A a0 a1 R R' x y).
Proof. exact (TRANS (@lem1232279 A a0 a1 R R' x y) (@lem1232278 A a0 a1 R R' x y)). Qed.
Lemma lem1232281 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term94 A a0 a1 R R' x) = (term252 A a0 a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1232280 A a0 a1 R R' x y)). Qed.
Lemma lem1232282 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1232283 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term96 A a0 a1 R R' x) = (term253 A a0 a1 R R' x).
Proof. exact (MK_COMB (@lem1232282 A) (@lem1232281 A a0 a1 R R' x)). Qed.
Lemma lem1232284 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term98 A a0 a1 R R') = (term254 A a0 a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1232283 A a0 a1 R R' x)). Qed.
Lemma lem1232285 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1232286 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term100 A a0 a1 R R') = (term255 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1232285 A) (@lem1232284 A a0 a1 R R')). Qed.
Lemma lem1232287 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1232288 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term80 A a0 R a1) = (term256 A a0 R a1).
Proof. exact (MK_COMB (@lem1232287) (@lem1232249 A a0 R a1)). Qed.
Lemma lem1232393 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term102 A a0 a1 R R') = (term257 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1232288 A a0 R a1) (@lem1232286 A a0 a1 R R')). Qed.
Lemma lem1232394 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term257 A a0 a1 R R'.
Proof. exact (EQ_MP (@lem1232393 A a0 a1 R R') (@lem1232026 A a0 a1 R R' h1)). Qed.
Lemma lem1232401 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term258 A a1 R' a0 x) = (term259 A a1 R' a0 x).
Proof. exact (@lem17362 (@List.In A x a1) (R' a0 x)). Qed.
Lemma lem1232402 {A : Type'} (P : A -> Prop) : (term143 A P) = (term144 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem1232403 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term260 A a1 R' a0) = (term261 A a1 R' a0).
Proof. exact (@lem1232402 A (term129 A a1 R' a0)). Qed.
Lemma lem1232404 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term262 A a1 R' a0 x) = (term128 A a1 R' a0 x).
Proof. exact (eq_refl (term262 A a1 R' a0 x)). Qed.
Lemma lem1232405 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1232406 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term263 A a1 R' a0 x) = (term258 A a1 R' a0 x).
Proof. exact (MK_COMB (@lem1232405) (@lem1232404 A a1 R' a0 x)). Qed.
Lemma lem1232407 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term263 A a1 R' a0 x) = (term259 A a1 R' a0 x).
Proof. exact (TRANS (@lem1232406 A a1 R' a0 x) (@lem1232401 A a1 R' a0 x)). Qed.
Lemma lem1232408 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term264 A a1 R' a0) = (term265 A a1 R' a0).
Proof. exact (fun_ext (fun x : A => @lem1232407 A a1 R' a0 x)). Qed.
Lemma lem1232409 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232410 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term261 A a1 R' a0) = (term266 A a1 R' a0).
Proof. exact (MK_COMB (@lem1232409 A) (@lem1232408 A a1 R' a0)). Qed.
Lemma lem1232411 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term260 A a1 R' a0) = (term266 A a1 R' a0).
Proof. exact (TRANS (@lem1232403 A a1 R' a0) (@lem1232410 A a1 R' a0)). Qed.
Lemma lem1232412 {A : Type'} (R' : type1402 A) (a1 : list A) : (term171 A R' a1) = (term171 A R' a1).
Proof. exact (eq_refl (term171 A R' a1)). Qed.
Lemma lem1232413 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232414 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term267 A a1 R' a0) = (term268 A a1 R' a0).
Proof. exact (MK_COMB (@lem1232413) (@lem1232411 A a1 R' a0)). Qed.
Lemma lem1232415 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term269 A a0 R' a1) = (term270 A a0 R' a1).
Proof. exact (MK_COMB (@lem1232414 A a1 R' a0) (@lem1232412 A R' a1)). Qed.
Lemma lem1232416 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term139 A a0 R' a1) = (term269 A a0 R' a1).
Proof. exact (@lem17045 (term75 A a1 R' a0) (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232417 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term139 A a0 R' a1) = (term270 A a0 R' a1).
Proof. exact (TRANS (@lem1232416 A a0 R' a1) (@lem1232415 A a0 R' a1)). Qed.
Lemma lem1232468 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1232469 {A : Type'} (P : A -> Prop) (Q : Prop) : (term198 A P Q) = (term199 A P Q).
Proof. exact (@lem1232468 A P Q). Qed.
Lemma lem1232470 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term271 A a0 R' a1) = (term272 A a0 R' a1).
Proof. exact (@lem1232469 A (term265 A a1 R' a0) (term171 A R' a1)). Qed.
Lemma lem1232471 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term273 A a1 R' a0 x) = (term259 A a1 R' a0 x).
Proof. exact (eq_refl (term273 A a1 R' a0 x)). Qed.
Lemma lem1232472 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term274 A a1 R' a0) = (term265 A a1 R' a0).
Proof. exact (fun_ext (fun x : A => @lem1232471 A a1 R' a0 x)). Qed.
Lemma lem1232473 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232474 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term275 A a1 R' a0) = (term266 A a1 R' a0).
Proof. exact (MK_COMB (@lem1232473 A) (@lem1232472 A a1 R' a0)). Qed.
Lemma lem1232475 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232476 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) : (term276 A a1 R' a0) = (term268 A a1 R' a0).
Proof. exact (MK_COMB (@lem1232475) (@lem1232474 A a1 R' a0)). Qed.
Lemma lem1232477 {A : Type'} (R' : type1402 A) (a1 : list A) : (term171 A R' a1) = (term171 A R' a1).
Proof. exact (eq_refl (term171 A R' a1)). Qed.
Lemma lem1232478 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term271 A a0 R' a1) = (term270 A a0 R' a1).
Proof. exact (MK_COMB (@lem1232476 A a1 R' a0) (@lem1232477 A R' a1)). Qed.
Lemma lem1232479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1232480 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term277 A a0 R' a1) = (term278 A a0 R' a1).
Proof. exact (MK_COMB (@lem1232479) (@lem1232478 A a0 R' a1)). Qed.
Lemma lem1232481 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term273 A a1 R' a0 x) = (term259 A a1 R' a0 x).
Proof. exact (eq_refl (term273 A a1 R' a0 x)). Qed.
Lemma lem1232482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232483 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term279 A a1 R' a0 x) = (term280 A a1 R' a0 x).
Proof. exact (MK_COMB (@lem1232482) (@lem1232481 A a1 R' a0 x)). Qed.
Lemma lem1232484 {A : Type'} (R' : type1402 A) (a1 : list A) : (term171 A R' a1) = (term171 A R' a1).
Proof. exact (eq_refl (term171 A R' a1)). Qed.
Lemma lem1232485 {A : Type'} (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) : (term281 A a0 x R' a1) = (term282 A a0 x R' a1).
Proof. exact (MK_COMB (@lem1232483 A a1 R' a0 x) (@lem1232484 A R' a1)). Qed.
Lemma lem1232486 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term283 A a0 R' a1) = (term284 A a0 R' a1).
Proof. exact (fun_ext (fun x : A => @lem1232485 A a0 x R' a1)). Qed.
Lemma lem1232487 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem1232488 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term272 A a0 R' a1) = (term285 A a0 R' a1).
Proof. exact (MK_COMB (@lem1232487 A) (@lem1232486 A a0 R' a1)). Qed.
Lemma lem1232489 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : ((term271 A a0 R' a1) = (term272 A a0 R' a1)) = ((term270 A a0 R' a1) = (term285 A a0 R' a1)).
Proof. exact (MK_COMB (@lem1232480 A a0 R' a1) (@lem1232488 A a0 R' a1)). Qed.
Lemma lem1232491 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term270 A a0 R' a1) = (term285 A a0 R' a1).
Proof. exact (EQ_MP (@lem1232489 A a0 R' a1) (@lem1232470 A a0 R' a1)). Qed.
Lemma lem1232492 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) : (term139 A a0 R' a1) = (term285 A a0 R' a1).
Proof. exact (TRANS (@lem1232417 A a0 R' a1) (@lem1232491 A a0 R' a1)). Qed.
Lemma lem1232493 {A : Type'} (a0 : A) (R' : type1402 A) (a1 : list A) (h1 : term139 A a0 R' a1) : term285 A a0 R' a1.
Proof. exact (EQ_MP (@lem1232492 A a0 R' a1) (@lem1232031 A a0 R' a1 h1)). Qed.
Lemma lem1232494 {A : Type'} (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term282 A a0 x R' a1) : term282 A a0 x R' a1.
Proof. exact (h1). Qed.
Lemma lem1232495 {A : Type'} (R : type1402 A) (x' : A) (R' : type1402 A) (a1 : list A) (h1 : term229 A R x' R' a1) : term229 A R x' R' a1.
Proof. exact (h1). Qed.
Lemma lem1232496 {A : Type'} (R : type1402 A) (x' : A) (y : A) (R' : type1402 A) (a1 : list A) (h1 : term226 A R x' y R' a1) : term226 A R x' y R' a1.
Proof. exact (h1). Qed.
Lemma lem1232503 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232504 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1232503 A (A -> Prop) f x). Qed.
Lemma lem1232505 {A : Type'} (R' : type1402 A) (x : A) : (R' x) = (@I (A -> A -> Prop) R' x).
Proof. exact (@lem1232504 A R' x). Qed.
Lemma lem1232506 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1232507 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (R' x y) = (@I (A -> A -> Prop) R' x y).
Proof. exact (MK_COMB (@lem1232505 A R' x) (@lem1232506 A y)). Qed.
Lemma lem1232509 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232510 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1232509 A Prop f x). Qed.
Lemma lem1232511 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R' x y) = (term286 A R' x y).
Proof. exact (@lem1232510 A (@I (A -> A -> Prop) R' x) y). Qed.
Lemma lem1232513 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (R' x y) = (term286 A R' x y).
Proof. exact (TRANS (@lem1232507 A R' x y) (@lem1232511 A R' x y)). Qed.
Lemma lem1232514 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1232521 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232522 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1232521 A (A -> Prop) f x). Qed.
Lemma lem1232523 {A : Type'} (R : type1402 A) (x : A) : (R x) = (@I (A -> A -> Prop) R x).
Proof. exact (@lem1232522 A R x). Qed.
Lemma lem1232524 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1232525 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (@I (A -> A -> Prop) R x y).
Proof. exact (MK_COMB (@lem1232523 A R x) (@lem1232524 A y)). Qed.
Lemma lem1232527 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232528 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1232527 A Prop f x). Qed.
Lemma lem1232529 {A : Type'} (R : type1402 A) (x : A) (y : A) : (@I (A -> A -> Prop) R x y) = (term286 A R x y).
Proof. exact (@lem1232528 A (@I (A -> A -> Prop) R x) y). Qed.
Lemma lem1232531 {A : Type'} (R : type1402 A) (x : A) (y : A) : (R x y) = (term286 A R x y).
Proof. exact (TRANS (@lem1232525 A R x y) (@lem1232529 A R x y)). Qed.
Lemma lem1232532 {A : Type'} (R : type1402 A) (x : A) (y : A) : (term239 A R x y) = (term287 A R x y).
Proof. exact (MK_COMB (@lem1232514) (@lem1232531 A R x y)). Qed.
Lemma lem1232551 {A : Type'} (a0 : A) (y : A) (a1 : list A) : (term241 A a0 y a1) = (term241 A a0 y a1).
Proof. exact (eq_refl (term241 A a0 y a1)). Qed.
Lemma lem1232552 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term243 A a0 a1 R x y) = (term288 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1232551 A a0 y a1) (@lem1232532 A R x y)). Qed.
Lemma lem1232571 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term241 A a0 x a1) = (term241 A a0 x a1).
Proof. exact (eq_refl (term241 A a0 x a1)). Qed.
Lemma lem1232572 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term246 A a0 a1 R x y) = (term289 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1232571 A a0 x a1) (@lem1232552 A a0 a1 R x y)). Qed.
Lemma lem1232573 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232574 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term249 A a0 a1 R x y) = (term290 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1232573) (@lem1232572 A a0 a1 R x y)). Qed.
Lemma lem1232575 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term251 A a0 a1 R R' x y) = (term291 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1232574 A a0 a1 R x y) (@lem1232513 A R' x y)). Qed.
Lemma lem1232576 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term252 A a0 a1 R R' x) = (term292 A a0 a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1232575 A a0 a1 R R' x y)). Qed.
Lemma lem1232577 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1232578 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term253 A a0 a1 R R' x) = (term293 A a0 a1 R R' x).
Proof. exact (MK_COMB (@lem1232577 A) (@lem1232576 A a0 a1 R R' x)). Qed.
Lemma lem1232579 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term254 A a0 a1 R R') = (term294 A a0 a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1232578 A a0 a1 R R' x)). Qed.
Lemma lem1232580 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1232581 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term255 A a0 a1 R R') = (term295 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1232580 A) (@lem1232579 A a0 a1 R R')). Qed.
Lemma lem1232586 {A : Type'} (R : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1232593 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232594 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1232593 A (A -> Prop) f x). Qed.
Lemma lem1232595 {A : Type'} (R : type1402 A) (a0 : A) : (R a0) = (@I (A -> A -> Prop) R a0).
Proof. exact (@lem1232594 A R a0). Qed.
Lemma lem1232596 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1232597 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (@I (A -> A -> Prop) R a0 x).
Proof. exact (MK_COMB (@lem1232595 A R a0) (@lem1232596 A x)). Qed.
Lemma lem1232599 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232600 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1232599 A Prop f x). Qed.
Lemma lem1232601 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R a0 x) = (term286 A R a0 x).
Proof. exact (@lem1232600 A (@I (A -> A -> Prop) R a0) x). Qed.
Lemma lem1232603 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (R a0 x) = (term286 A R a0 x).
Proof. exact (TRANS (@lem1232597 A R a0 x) (@lem1232601 A R a0 x)). Qed.
Lemma lem1232612 {A : Type'} (x : A) (a1 : list A) : (term296 A x a1) = (term296 A x a1).
Proof. exact (eq_refl (term296 A x a1)). Qed.
Lemma lem1232613 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term232 A a1 R a0 x) = (term297 A a1 R a0 x).
Proof. exact (MK_COMB (@lem1232612 A x a1) (@lem1232603 A R a0 x)). Qed.
Lemma lem1232614 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term233 A a1 R a0) = (term298 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1232613 A a1 R a0 x)). Qed.
Lemma lem1232615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1232616 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term234 A a1 R a0) = (term299 A a1 R a0).
Proof. exact (MK_COMB (@lem1232615 A) (@lem1232614 A a1 R a0)). Qed.
Lemma lem1232617 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1232618 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term235 A a1 R a0) = (term300 A a1 R a0).
Proof. exact (MK_COMB (@lem1232617) (@lem1232616 A a1 R a0)). Qed.
Lemma lem1232619 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term236 A a0 R a1) = (term301 A a0 R a1).
Proof. exact (MK_COMB (@lem1232618 A a1 R a0) (@lem1232586 A R a1)). Qed.
Lemma lem1232620 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1232621 {A : Type'} (a0 : A) (R : type1402 A) (a1 : list A) : (term256 A a0 R a1) = (term302 A a0 R a1).
Proof. exact (MK_COMB (@lem1232620) (@lem1232619 A a0 R a1)). Qed.
Lemma lem1232622 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term257 A a0 a1 R R') = (term303 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1232621 A a0 R a1) (@lem1232581 A a0 a1 R R')). Qed.
Lemma lem1232623 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term303 A a0 a1 R R'.
Proof. exact (EQ_MP (@lem1232622 A a0 a1 R R') (@lem1232394 A a0 a1 R R' h1)). Qed.
Lemma lem1232630 {A : Type'} (R' : type1402 A) (a1 : list A) : (term171 A R' a1) = (term171 A R' a1).
Proof. exact (eq_refl (term171 A R' a1)). Qed.
Lemma lem1232631 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1232638 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232639 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1232638 A (A -> Prop) f x). Qed.
Lemma lem1232640 {A : Type'} (R' : type1402 A) (a0 : A) : (R' a0) = (@I (A -> A -> Prop) R' a0).
Proof. exact (@lem1232639 A R' a0). Qed.
Lemma lem1232641 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem1232642 {A : Type'} (R' : type1402 A) (a0 : A) (x : A) : (R' a0 x) = (@I (A -> A -> Prop) R' a0 x).
Proof. exact (MK_COMB (@lem1232640 A R' a0) (@lem1232641 A x)). Qed.
Lemma lem1232644 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232645 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1232644 A Prop f x). Qed.
Lemma lem1232646 {A : Type'} (R' : type1402 A) (a0 : A) (x : A) : (@I (A -> A -> Prop) R' a0 x) = (term286 A R' a0 x).
Proof. exact (@lem1232645 A (@I (A -> A -> Prop) R' a0) x). Qed.
Lemma lem1232648 {A : Type'} (R' : type1402 A) (a0 : A) (x : A) : (R' a0 x) = (term286 A R' a0 x).
Proof. exact (TRANS (@lem1232642 A R' a0 x) (@lem1232646 A R' a0 x)). Qed.
Lemma lem1232649 {A : Type'} (R' : type1402 A) (a0 : A) (x : A) : (term239 A R' a0 x) = (term287 A R' a0 x).
Proof. exact (MK_COMB (@lem1232631) (@lem1232648 A R' a0 x)). Qed.
Lemma lem1232656 {A : Type'} (x : A) (a1 : list A) : (term304 A x a1) = (term304 A x a1).
Proof. exact (eq_refl (term304 A x a1)). Qed.
Lemma lem1232657 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term259 A a1 R' a0 x) = (term305 A a1 R' a0 x).
Proof. exact (MK_COMB (@lem1232656 A x a1) (@lem1232649 A R' a0 x)). Qed.
Lemma lem1232658 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232659 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) : (term280 A a1 R' a0 x) = (term306 A a1 R' a0 x).
Proof. exact (MK_COMB (@lem1232658) (@lem1232657 A a1 R' a0 x)). Qed.
Lemma lem1232660 {A : Type'} (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) : (term282 A a0 x R' a1) = (term307 A a0 x R' a1).
Proof. exact (MK_COMB (@lem1232659 A a1 R' a0 x) (@lem1232630 A R' a1)). Qed.
Lemma lem1232661 {A : Type'} (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term282 A a0 x R' a1) : term307 A a0 x R' a1.
Proof. exact (EQ_MP (@lem1232660 A a0 x R' a1) (@lem1232494 A a0 x R' a1 h1)). Qed.
Lemma lem1232666 {A : Type'} (R' : type1402 A) (a1 : list A) : (@List.ForallOrdPairs A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (eq_refl (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1232667 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1232674 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232675 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1232674 A (A -> Prop) f x). Qed.
Lemma lem1232676 {A : Type'} (R' : type1402 A) (x' : A) : (R' x') = (@I (A -> A -> Prop) R' x').
Proof. exact (@lem1232675 A R' x'). Qed.
Lemma lem1232677 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1232678 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (R' x' y) = (@I (A -> A -> Prop) R' x' y).
Proof. exact (MK_COMB (@lem1232676 A R' x') (@lem1232677 A y)). Qed.
Lemma lem1232680 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232681 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1232680 A Prop f x). Qed.
Lemma lem1232682 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (@I (A -> A -> Prop) R' x' y) = (term286 A R' x' y).
Proof. exact (@lem1232681 A (@I (A -> A -> Prop) R' x') y). Qed.
Lemma lem1232684 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (R' x' y) = (term286 A R' x' y).
Proof. exact (TRANS (@lem1232678 A R' x' y) (@lem1232682 A R' x' y)). Qed.
Lemma lem1232685 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (term239 A R' x' y) = (term287 A R' x' y).
Proof. exact (MK_COMB (@lem1232667) (@lem1232684 A R' x' y)). Qed.
Lemma lem1232692 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232693 {A : Type'} (f : type1402 A) (x : A) : (f x) = (@I (A -> A -> Prop) f x).
Proof. exact (@lem1232692 A (A -> Prop) f x). Qed.
Lemma lem1232694 {A : Type'} (R : type1402 A) (x' : A) : (R x') = (@I (A -> A -> Prop) R x').
Proof. exact (@lem1232693 A R x'). Qed.
Lemma lem1232695 {A : Type'} (y : A) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem1232696 {A : Type'} (R : type1402 A) (x' : A) (y : A) : (R x' y) = (@I (A -> A -> Prop) R x' y).
Proof. exact (MK_COMB (@lem1232694 A R x') (@lem1232695 A y)). Qed.
Lemma lem1232698 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1232699 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1232698 A Prop f x). Qed.
Lemma lem1232700 {A : Type'} (R : type1402 A) (x' : A) (y : A) : (@I (A -> A -> Prop) R x' y) = (term286 A R x' y).
Proof. exact (@lem1232699 A (@I (A -> A -> Prop) R x') y). Qed.
Lemma lem1232702 {A : Type'} (R : type1402 A) (x' : A) (y : A) : (R x' y) = (term286 A R x' y).
Proof. exact (TRANS (@lem1232696 A R x' y) (@lem1232700 A R x' y)). Qed.
Lemma lem1232709 {A : Type'} (y : A) (a1 : list A) : (term304 A y a1) = (term304 A y a1).
Proof. exact (eq_refl (term304 A y a1)). Qed.
Lemma lem1232710 {A : Type'} (a1 : list A) (R : type1402 A) (x' : A) (y : A) : (term308 A a1 R x' y) = (term309 A a1 R x' y).
Proof. exact (MK_COMB (@lem1232709 A y a1) (@lem1232702 A R x' y)). Qed.
Lemma lem1232717 {A : Type'} (x' : A) (a1 : list A) : (term304 A x' a1) = (term304 A x' a1).
Proof. exact (eq_refl (term304 A x' a1)). Qed.
Lemma lem1232718 {A : Type'} (a1 : list A) (R : type1402 A) (x' : A) (y : A) : (term142 A a1 R x' y) = (term310 A a1 R x' y).
Proof. exact (MK_COMB (@lem1232717 A x' a1) (@lem1232710 A a1 R x' y)). Qed.
Lemma lem1232719 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1232720 {A : Type'} (a1 : list A) (R : type1402 A) (x' : A) (y : A) : (term311 A a1 R x' y) = (term312 A a1 R x' y).
Proof. exact (MK_COMB (@lem1232719) (@lem1232718 A a1 R x' y)). Qed.
Lemma lem1232721 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) : (term141 A a1 R R' x' y) = (term313 A a1 R R' x' y).
Proof. exact (MK_COMB (@lem1232720 A a1 R x' y) (@lem1232685 A R' x' y)). Qed.
Lemma lem1232730 {A : Type'} (R : type1402 A) (a1 : list A) : (term159 A R a1) = (term159 A R a1).
Proof. exact (eq_refl (term159 A R a1)). Qed.
Lemma lem1232731 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) : (term190 A a1 R R' x' y) = (term314 A a1 R R' x' y).
Proof. exact (MK_COMB (@lem1232730 A R a1) (@lem1232721 A a1 R R' x' y)). Qed.
Lemma lem1232732 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1232733 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) : (term224 A a1 R R' x' y) = (term315 A a1 R R' x' y).
Proof. exact (MK_COMB (@lem1232732) (@lem1232731 A a1 R R' x' y)). Qed.
Lemma lem1232734 {A : Type'} (R : type1402 A) (x' : A) (y : A) (R' : type1402 A) (a1 : list A) : (term226 A R x' y R' a1) = (term316 A R x' y R' a1).
Proof. exact (MK_COMB (@lem1232733 A a1 R R' x' y) (@lem1232666 A R' a1)). Qed.
Lemma lem1232735 {A : Type'} (R : type1402 A) (x' : A) (y : A) (R' : type1402 A) (a1 : list A) (h1 : term226 A R x' y R' a1) : term316 A R x' y R' a1.
Proof. exact (EQ_MP (@lem1232734 A R x' y R' a1) (@lem1232496 A R x' y R' a1 h1)). Qed.
Lemma lem1232736 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term295 A a0 a1 R R'.
Proof. exact (proj2 (@lem1232623 A a0 a1 R R' h1)). Qed.
Lemma lem1232737 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term301 A a0 R a1.
Proof. exact (proj1 (@lem1232623 A a0 a1 R R' h1)). Qed.
Lemma lem1232739 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term299 A a1 R a0.
Proof. exact (proj1 (@lem1232737 A a0 a1 R R' h1)). Qed.
Lemma lem1232740 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term314 A a1 R R' x' y) : term314 A a1 R R' x' y.
Proof. exact (h1). Qed.
Lemma lem1232743 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term313 A a1 R R' x' y.
Proof. exact (h1). Qed.
Lemma lem1232749 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term310 A a1 R x' y.
Proof. exact (proj1 (@lem1232743 A a1 R R' x' y h1)). Qed.
Lemma lem1232750 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term309 A a1 R x' y.
Proof. exact (proj2 (@lem1232749 A a1 R R' x' y h1)). Qed.
Lemma lem1232758 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : term305 A a1 R' a0 x.
Proof. exact (h1). Qed.
Lemma lem1232860 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term171 A R a1) : term171 A R a1.
Proof. exact (h1). Qed.
Lemma lem1232967 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term171 A R a1) : term171 A R a1.
Proof. exact (h1). Qed.
Lemma lem1232973 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (term286 A R' x y) = (term286 A R' x y).
Proof. exact (eq_refl (term286 A R' x y)). Qed.
Lemma lem1232990 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term288 A a0 a1 R x y) = (term317 A a0 a1 R x y).
Proof. exact (@lem19699 (term318 A y a0) (term319 A y a1) (term287 A R x y)). Qed.
Lemma lem1232997 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term241 A a0 x a1) = (term241 A a0 x a1).
Proof. exact (eq_refl (term241 A a0 x a1)). Qed.
Lemma lem1232998 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term289 A a0 a1 R x y) = (term320 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1232997 A a0 x a1) (@lem1232990 A a0 a1 R x y)). Qed.
Lemma lem1232999 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a0 a1 R x y) = (term321 A a0 a1 R x y).
Proof. exact (@lem19490 (term322 A a0 R x y) (term238 A a0 x a1) (term323 A a1 R x y)). Qed.
Lemma lem1233006 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term324 A a0 a1 R x y) = (term325 A a0 a1 R x y).
Proof. exact (@lem19699 (term318 A x a0) (term319 A x a1) (term323 A a1 R x y)). Qed.
Lemma lem1233013 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (x : A) (y : A) : (term326 A a1 a0 R x y) = (term327 A a1 a0 R x y).
Proof. exact (@lem19699 (term318 A x a0) (term319 A x a1) (term322 A a0 R x y)). Qed.
Lemma lem1233014 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1233015 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (x : A) (y : A) : (term328 A a1 a0 R x y) = (term329 A a1 a0 R x y).
Proof. exact (MK_COMB (@lem1233014) (@lem1233013 A a1 a0 R x y)). Qed.
Lemma lem1233016 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term321 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233015 A a1 a0 R x y) (@lem1233006 A a0 a1 R x y)). Qed.
Lemma lem1233017 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (TRANS (@lem1232999 A a0 a1 R x y) (@lem1233016 A a0 a1 R x y)). Qed.
Lemma lem1233018 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term289 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (TRANS (@lem1232998 A a0 a1 R x y) (@lem1233017 A a0 a1 R x y)). Qed.
Lemma lem1233019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1233020 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term290 A a0 a1 R x y) = (term331 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233019) (@lem1233018 A a0 a1 R x y)). Qed.
Lemma lem1233021 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term291 A a0 a1 R R' x y) = (term332 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1233020 A a0 a1 R x y) (@lem1232973 A R' x y)). Qed.
Lemma lem1233022 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term332 A a0 a1 R R' x y) = (term333 A a0 a1 R R' x y).
Proof. exact (@lem19699 (term327 A a1 a0 R x y) (term325 A a0 a1 R x y) (term286 A R' x y)). Qed.
Lemma lem1233029 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term334 A a0 a1 R R' x y) = (term335 A a0 a1 R R' x y).
Proof. exact (@lem19699 (term336 A a0 a1 R x y) (term337 A a1 R x y) (term286 A R' x y)). Qed.
Lemma lem1233036 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term338 A a1 a0 R R' x y) = (term339 A a1 a0 R R' x y).
Proof. exact (@lem19699 (term340 A a0 R x y) (term341 A a1 a0 R x y) (term286 A R' x y)). Qed.
Lemma lem1233037 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1233038 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term342 A a1 a0 R R' x y) = (term343 A a1 a0 R R' x y).
Proof. exact (MK_COMB (@lem1233037) (@lem1233036 A a1 a0 R R' x y)). Qed.
Lemma lem1233039 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term333 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1233038 A a1 a0 R R' x y) (@lem1233029 A a0 a1 R R' x y)). Qed.
Lemma lem1233040 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term332 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (TRANS (@lem1233022 A a0 a1 R R' x y) (@lem1233039 A a0 a1 R R' x y)). Qed.
Lemma lem1233041 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term291 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (TRANS (@lem1233021 A a0 a1 R R' x y) (@lem1233040 A a0 a1 R R' x y)). Qed.
Lemma lem1233042 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term292 A a0 a1 R R' x) = (term345 A a0 a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1233041 A a0 a1 R R' x y)). Qed.
Lemma lem1233043 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1233044 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term293 A a0 a1 R R' x) = (term346 A a0 a1 R R' x).
Proof. exact (MK_COMB (@lem1233043 A) (@lem1233042 A a0 a1 R R' x)). Qed.
Lemma lem1233045 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term294 A a0 a1 R R') = (term347 A a0 a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1233044 A a0 a1 R R' x)). Qed.
Lemma lem1233046 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1233048 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term295 A a0 a1 R R') = (term348 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1233046 A) (@lem1233045 A a0 a1 R R')). Qed.
Lemma lem1233049 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term348 A a0 a1 R R'.
Proof. exact (EQ_MP (@lem1233048 A a0 a1 R R') (@lem1232736 A a0 a1 R R' h1)). Qed.
Lemma lem1233092 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (term286 A R' x y) = (term286 A R' x y).
Proof. exact (eq_refl (term286 A R' x y)). Qed.
Lemma lem1233109 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term288 A a0 a1 R x y) = (term317 A a0 a1 R x y).
Proof. exact (@lem19699 (term318 A y a0) (term319 A y a1) (term287 A R x y)). Qed.
Lemma lem1233116 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term241 A a0 x a1) = (term241 A a0 x a1).
Proof. exact (eq_refl (term241 A a0 x a1)). Qed.
Lemma lem1233117 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term289 A a0 a1 R x y) = (term320 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233116 A a0 x a1) (@lem1233109 A a0 a1 R x y)). Qed.
Lemma lem1233118 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a0 a1 R x y) = (term321 A a0 a1 R x y).
Proof. exact (@lem19490 (term322 A a0 R x y) (term238 A a0 x a1) (term323 A a1 R x y)). Qed.
Lemma lem1233125 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term324 A a0 a1 R x y) = (term325 A a0 a1 R x y).
Proof. exact (@lem19699 (term318 A x a0) (term319 A x a1) (term323 A a1 R x y)). Qed.
Lemma lem1233132 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (x : A) (y : A) : (term326 A a1 a0 R x y) = (term327 A a1 a0 R x y).
Proof. exact (@lem19699 (term318 A x a0) (term319 A x a1) (term322 A a0 R x y)). Qed.
Lemma lem1233133 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1233134 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (x : A) (y : A) : (term328 A a1 a0 R x y) = (term329 A a1 a0 R x y).
Proof. exact (MK_COMB (@lem1233133) (@lem1233132 A a1 a0 R x y)). Qed.
Lemma lem1233135 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term321 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233134 A a1 a0 R x y) (@lem1233125 A a0 a1 R x y)). Qed.
Lemma lem1233136 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (TRANS (@lem1233118 A a0 a1 R x y) (@lem1233135 A a0 a1 R x y)). Qed.
Lemma lem1233137 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term289 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (TRANS (@lem1233117 A a0 a1 R x y) (@lem1233136 A a0 a1 R x y)). Qed.
Lemma lem1233138 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1233139 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term290 A a0 a1 R x y) = (term331 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233138) (@lem1233137 A a0 a1 R x y)). Qed.
Lemma lem1233140 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term291 A a0 a1 R R' x y) = (term332 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1233139 A a0 a1 R x y) (@lem1233092 A R' x y)). Qed.
Lemma lem1233141 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term332 A a0 a1 R R' x y) = (term333 A a0 a1 R R' x y).
Proof. exact (@lem19699 (term327 A a1 a0 R x y) (term325 A a0 a1 R x y) (term286 A R' x y)). Qed.
Lemma lem1233148 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term334 A a0 a1 R R' x y) = (term335 A a0 a1 R R' x y).
Proof. exact (@lem19699 (term336 A a0 a1 R x y) (term337 A a1 R x y) (term286 A R' x y)). Qed.
Lemma lem1233155 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term338 A a1 a0 R R' x y) = (term339 A a1 a0 R R' x y).
Proof. exact (@lem19699 (term340 A a0 R x y) (term341 A a1 a0 R x y) (term286 A R' x y)). Qed.
Lemma lem1233156 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1233157 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term342 A a1 a0 R R' x y) = (term343 A a1 a0 R R' x y).
Proof. exact (MK_COMB (@lem1233156) (@lem1233155 A a1 a0 R R' x y)). Qed.
Lemma lem1233158 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term333 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1233157 A a1 a0 R R' x y) (@lem1233148 A a0 a1 R R' x y)). Qed.
Lemma lem1233159 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term332 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (TRANS (@lem1233141 A a0 a1 R R' x y) (@lem1233158 A a0 a1 R R' x y)). Qed.
Lemma lem1233160 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term291 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (TRANS (@lem1233140 A a0 a1 R R' x y) (@lem1233159 A a0 a1 R R' x y)). Qed.
Lemma lem1233161 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term292 A a0 a1 R R' x) = (term345 A a0 a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1233160 A a0 a1 R R' x y)). Qed.
Lemma lem1233162 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1233163 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term293 A a0 a1 R R' x) = (term346 A a0 a1 R R' x).
Proof. exact (MK_COMB (@lem1233162 A) (@lem1233161 A a0 a1 R R' x)). Qed.
Lemma lem1233164 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term294 A a0 a1 R R') = (term347 A a0 a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1233163 A a0 a1 R R' x)). Qed.
Lemma lem1233165 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1233167 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term295 A a0 a1 R R') = (term348 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1233165 A) (@lem1233164 A a0 a1 R R')). Qed.
Lemma lem1233168 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term348 A a0 a1 R R'.
Proof. exact (EQ_MP (@lem1233167 A a0 a1 R R') (@lem1232736 A a0 a1 R R' h1)). Qed.
Lemma lem1233207 {A : Type'} (R' : type1402 A) (x : A) (y : A) : (term286 A R' x y) = (term286 A R' x y).
Proof. exact (eq_refl (term286 A R' x y)). Qed.
Lemma lem1233224 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term288 A a0 a1 R x y) = (term317 A a0 a1 R x y).
Proof. exact (@lem19699 (term318 A y a0) (term319 A y a1) (term287 A R x y)). Qed.
Lemma lem1233231 {A : Type'} (a0 : A) (x : A) (a1 : list A) : (term241 A a0 x a1) = (term241 A a0 x a1).
Proof. exact (eq_refl (term241 A a0 x a1)). Qed.
Lemma lem1233232 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term289 A a0 a1 R x y) = (term320 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233231 A a0 x a1) (@lem1233224 A a0 a1 R x y)). Qed.
Lemma lem1233233 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a0 a1 R x y) = (term321 A a0 a1 R x y).
Proof. exact (@lem19490 (term322 A a0 R x y) (term238 A a0 x a1) (term323 A a1 R x y)). Qed.
Lemma lem1233240 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term324 A a0 a1 R x y) = (term325 A a0 a1 R x y).
Proof. exact (@lem19699 (term318 A x a0) (term319 A x a1) (term323 A a1 R x y)). Qed.
Lemma lem1233247 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (x : A) (y : A) : (term326 A a1 a0 R x y) = (term327 A a1 a0 R x y).
Proof. exact (@lem19699 (term318 A x a0) (term319 A x a1) (term322 A a0 R x y)). Qed.
Lemma lem1233248 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1233249 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (x : A) (y : A) : (term328 A a1 a0 R x y) = (term329 A a1 a0 R x y).
Proof. exact (MK_COMB (@lem1233248) (@lem1233247 A a1 a0 R x y)). Qed.
Lemma lem1233250 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term321 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233249 A a1 a0 R x y) (@lem1233240 A a0 a1 R x y)). Qed.
Lemma lem1233251 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term320 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (TRANS (@lem1233233 A a0 a1 R x y) (@lem1233250 A a0 a1 R x y)). Qed.
Lemma lem1233252 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term289 A a0 a1 R x y) = (term330 A a0 a1 R x y).
Proof. exact (TRANS (@lem1233232 A a0 a1 R x y) (@lem1233251 A a0 a1 R x y)). Qed.
Lemma lem1233253 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1233254 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (x : A) (y : A) : (term290 A a0 a1 R x y) = (term331 A a0 a1 R x y).
Proof. exact (MK_COMB (@lem1233253) (@lem1233252 A a0 a1 R x y)). Qed.
Lemma lem1233255 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term291 A a0 a1 R R' x y) = (term332 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1233254 A a0 a1 R x y) (@lem1233207 A R' x y)). Qed.
Lemma lem1233256 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term332 A a0 a1 R R' x y) = (term333 A a0 a1 R R' x y).
Proof. exact (@lem19699 (term327 A a1 a0 R x y) (term325 A a0 a1 R x y) (term286 A R' x y)). Qed.
Lemma lem1233263 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term334 A a0 a1 R R' x y) = (term335 A a0 a1 R R' x y).
Proof. exact (@lem19699 (term336 A a0 a1 R x y) (term337 A a1 R x y) (term286 A R' x y)). Qed.
Lemma lem1233270 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term338 A a1 a0 R R' x y) = (term339 A a1 a0 R R' x y).
Proof. exact (@lem19699 (term340 A a0 R x y) (term341 A a1 a0 R x y) (term286 A R' x y)). Qed.
Lemma lem1233271 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1233272 {A : Type'} (a1 : list A) (a0 : A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term342 A a1 a0 R R' x y) = (term343 A a1 a0 R R' x y).
Proof. exact (MK_COMB (@lem1233271) (@lem1233270 A a1 a0 R R' x y)). Qed.
Lemma lem1233273 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term333 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (MK_COMB (@lem1233272 A a1 a0 R R' x y) (@lem1233263 A a0 a1 R R' x y)). Qed.
Lemma lem1233274 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term332 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (TRANS (@lem1233256 A a0 a1 R R' x y) (@lem1233273 A a0 a1 R R' x y)). Qed.
Lemma lem1233275 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) (y : A) : (term291 A a0 a1 R R' x y) = (term344 A a0 a1 R R' x y).
Proof. exact (TRANS (@lem1233255 A a0 a1 R R' x y) (@lem1233274 A a0 a1 R R' x y)). Qed.
Lemma lem1233276 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term292 A a0 a1 R R' x) = (term345 A a0 a1 R R' x).
Proof. exact (fun_ext (fun y : A => @lem1233275 A a0 a1 R R' x y)). Qed.
Lemma lem1233277 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1233278 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x : A) : (term293 A a0 a1 R R' x) = (term346 A a0 a1 R R' x).
Proof. exact (MK_COMB (@lem1233277 A) (@lem1233276 A a0 a1 R R' x)). Qed.
Lemma lem1233279 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term294 A a0 a1 R R') = (term347 A a0 a1 R R').
Proof. exact (fun_ext (fun x : A => @lem1233278 A a0 a1 R R' x)). Qed.
Lemma lem1233280 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1233282 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) : (term295 A a0 a1 R R') = (term348 A a0 a1 R R').
Proof. exact (MK_COMB (@lem1233280 A) (@lem1233279 A a0 a1 R R')). Qed.
Lemma lem1233283 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term348 A a0 a1 R R'.
Proof. exact (EQ_MP (@lem1233282 A a0 a1 R R') (@lem1232736 A a0 a1 R R' h1)). Qed.
Lemma lem1233291 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (x : A) : (term297 A a1 R a0 x) = (term297 A a1 R a0 x).
Proof. exact (eq_refl (term297 A a1 R a0 x)). Qed.
Lemma lem1233292 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term298 A a1 R a0) = (term298 A a1 R a0).
Proof. exact (fun_ext (fun x : A => @lem1233291 A a1 R a0 x)). Qed.
Lemma lem1233293 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1233295 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) : (term299 A a1 R a0) = (term299 A a1 R a0).
Proof. exact (MK_COMB (@lem1233293 A) (@lem1233292 A a1 R a0)). Qed.
Lemma lem1233296 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term299 A a1 R a0.
Proof. exact (EQ_MP (@lem1233295 A a1 R a0) (@lem1232739 A a0 a1 R R' h1)). Qed.
Lemma lem1233411 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : @List.ForallOrdPairs A R' a1) : @List.ForallOrdPairs A R' a1.
Proof. exact (h1). Qed.
Lemma lem1233415 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) : term171 A R' a1.
Proof. exact (h1). Qed.
Lemma lem1233434 {A : Type'} (_22555 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term349 A a0 a1 R R' _22555.
Proof. exact (@lem1233049 A a0 a1 R R' h1 _22555). Qed.
Lemma lem1233435 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) : (term349 A a0 a1 R R' _22555) = (term346 A a0 a1 R R' _22555).
Proof. exact (eq_refl (term349 A a0 a1 R R' _22555)). Qed.
Lemma lem1233436 {A : Type'} (_22555 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term346 A a0 a1 R R' _22555.
Proof. exact (EQ_MP (@lem1233435 A a0 a1 R R' _22555) (@lem1233434 A _22555 a0 a1 R R' h1)). Qed.
Lemma lem1233437 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term350 A a0 a1 R R' _22555 _22556.
Proof. exact (@lem1233436 A _22555 a0 a1 R R' h1 _22556). Qed.
Lemma lem1233438 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term350 A a0 a1 R R' _22555 _22556) = (term344 A a0 a1 R R' _22555 _22556).
Proof. exact (eq_refl (term350 A a0 a1 R R' _22555 _22556)). Qed.
Lemma lem1233439 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term344 A a0 a1 R R' _22555 _22556.
Proof. exact (EQ_MP (@lem1233438 A a0 a1 R R' _22555 _22556) (@lem1233437 A _22555 _22556 a0 a1 R R' h1)). Qed.
Lemma lem1233443 {A : Type'} (_22558 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term349 A a0 a1 R R' _22558.
Proof. exact (@lem1233168 A a0 a1 R R' h1 _22558). Qed.
Lemma lem1233444 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) : (term349 A a0 a1 R R' _22558) = (term346 A a0 a1 R R' _22558).
Proof. exact (eq_refl (term349 A a0 a1 R R' _22558)). Qed.
Lemma lem1233445 {A : Type'} (_22558 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term346 A a0 a1 R R' _22558.
Proof. exact (EQ_MP (@lem1233444 A a0 a1 R R' _22558) (@lem1233443 A _22558 a0 a1 R R' h1)). Qed.
Lemma lem1233446 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term350 A a0 a1 R R' _22558 _22559.
Proof. exact (@lem1233445 A _22558 a0 a1 R R' h1 _22559). Qed.
Lemma lem1233447 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term350 A a0 a1 R R' _22558 _22559) = (term344 A a0 a1 R R' _22558 _22559).
Proof. exact (eq_refl (term350 A a0 a1 R R' _22558 _22559)). Qed.
Lemma lem1233448 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term344 A a0 a1 R R' _22558 _22559.
Proof. exact (EQ_MP (@lem1233447 A a0 a1 R R' _22558 _22559) (@lem1233446 A _22558 _22559 a0 a1 R R' h1)). Qed.
Lemma lem1233452 {A : Type'} (_22561 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term349 A a0 a1 R R' _22561.
Proof. exact (@lem1233283 A a0 a1 R R' h1 _22561). Qed.
Lemma lem1233453 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) : (term349 A a0 a1 R R' _22561) = (term346 A a0 a1 R R' _22561).
Proof. exact (eq_refl (term349 A a0 a1 R R' _22561)). Qed.
Lemma lem1233454 {A : Type'} (_22561 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term346 A a0 a1 R R' _22561.
Proof. exact (EQ_MP (@lem1233453 A a0 a1 R R' _22561) (@lem1233452 A _22561 a0 a1 R R' h1)). Qed.
Lemma lem1233455 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term350 A a0 a1 R R' _22561 _22562.
Proof. exact (@lem1233454 A _22561 a0 a1 R R' h1 _22562). Qed.
Lemma lem1233456 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term350 A a0 a1 R R' _22561 _22562) = (term344 A a0 a1 R R' _22561 _22562).
Proof. exact (eq_refl (term350 A a0 a1 R R' _22561 _22562)). Qed.
Lemma lem1233457 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term344 A a0 a1 R R' _22561 _22562.
Proof. exact (EQ_MP (@lem1233456 A a0 a1 R R' _22561 _22562) (@lem1233455 A _22561 _22562 a0 a1 R R' h1)). Qed.
Lemma lem1233458 {A : Type'} (_22563 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term351 A a1 R a0 _22563.
Proof. exact (@lem1233296 A a0 a1 R R' h1 _22563). Qed.
Lemma lem1233459 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22563 : A) : (term351 A a1 R a0 _22563) = (term297 A a1 R a0 _22563).
Proof. exact (eq_refl (term351 A a1 R a0 _22563)). Qed.
Lemma lem1233482 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term335 A a0 a1 R R' _22555 _22556.
Proof. exact (proj2 (@lem1233439 A _22555 _22556 a0 a1 R R' h1)). Qed.
Lemma lem1233484 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term352 A a1 R R' _22555 _22556.
Proof. exact (proj2 (@lem1233482 A _22555 _22556 a0 a1 R R' h1)). Qed.
Lemma lem1233488 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term335 A a0 a1 R R' _22558 _22559.
Proof. exact (proj2 (@lem1233448 A _22558 _22559 a0 a1 R R' h1)). Qed.
Lemma lem1233490 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term352 A a1 R R' _22558 _22559.
Proof. exact (proj2 (@lem1233488 A _22558 _22559 a0 a1 R R' h1)). Qed.
Lemma lem1233494 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term335 A a0 a1 R R' _22561 _22562.
Proof. exact (proj2 (@lem1233457 A _22561 _22562 a0 a1 R R' h1)). Qed.
Lemma lem1233497 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term353 A a0 a1 R R' _22561 _22562.
Proof. exact (proj1 (@lem1233494 A _22561 _22562 a0 a1 R R' h1)). Qed.
Lemma lem1233515 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term171 A R a1) : term171 A R a1.
Proof. exact (h1). Qed.
Lemma lem1233601 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term171 A R a1) : term171 A R a1.
Proof. exact (h1). Qed.
Lemma lem1233685 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term287 A R' x' y.
Proof. exact (proj2 (@lem1232743 A a1 R R' x' y h1)). Qed.
Lemma lem1233717 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term352 A a1 R R' _22555 _22556) = (term354 A a1 R R' _22555 _22556).
Proof. exact (@lem1231307 (term319 A _22555 a1) (term323 A a1 R _22555 _22556) (term286 A R' _22555 _22556)). Qed.
Lemma lem1233724 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term355 A a1 R R' _22555 _22556) = (term356 A a1 R R' _22555 _22556).
Proof. exact (@lem1231307 (term319 A _22556 a1) (term287 A R _22555 _22556) (term286 A R' _22555 _22556)). Qed.
Lemma lem1233725 {A : Type'} (_22555 : A) (a1 : list A) : (term296 A _22555 a1) = (term296 A _22555 a1).
Proof. exact (eq_refl (term296 A _22555 a1)). Qed.
Lemma lem1233728 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term354 A a1 R R' _22555 _22556) = (term357 A a1 R R' _22555 _22556).
Proof. exact (MK_COMB (@lem1233725 A _22555 a1) (@lem1233724 A a1 R R' _22555 _22556)). Qed.
Lemma lem1233730 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term352 A a1 R R' _22555 _22556) = (term357 A a1 R R' _22555 _22556).
Proof. exact (TRANS (@lem1233717 A a1 R R' _22555 _22556) (@lem1233728 A a1 R R' _22555 _22556)). Qed.
Lemma lem1233731 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term357 A a1 R R' _22555 _22556.
Proof. exact (EQ_MP (@lem1233730 A a1 R R' _22555 _22556) (@lem1233484 A _22555 _22556 a0 a1 R R' h1)). Qed.
Lemma lem1233777 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term287 A R' x' y.
Proof. exact (proj2 (@lem1232743 A a1 R R' x' y h1)). Qed.
Lemma lem1233807 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term352 A a1 R R' _22558 _22559) = (term354 A a1 R R' _22558 _22559).
Proof. exact (@lem1231307 (term319 A _22558 a1) (term323 A a1 R _22558 _22559) (term286 A R' _22558 _22559)). Qed.
Lemma lem1233814 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term355 A a1 R R' _22558 _22559) = (term356 A a1 R R' _22558 _22559).
Proof. exact (@lem1231307 (term319 A _22559 a1) (term287 A R _22558 _22559) (term286 A R' _22558 _22559)). Qed.
Lemma lem1233815 {A : Type'} (_22558 : A) (a1 : list A) : (term296 A _22558 a1) = (term296 A _22558 a1).
Proof. exact (eq_refl (term296 A _22558 a1)). Qed.
Lemma lem1233818 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term354 A a1 R R' _22558 _22559) = (term357 A a1 R R' _22558 _22559).
Proof. exact (MK_COMB (@lem1233815 A _22558 a1) (@lem1233814 A a1 R R' _22558 _22559)). Qed.
Lemma lem1233820 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term352 A a1 R R' _22558 _22559) = (term357 A a1 R R' _22558 _22559).
Proof. exact (TRANS (@lem1233807 A a1 R R' _22558 _22559) (@lem1233818 A a1 R R' _22558 _22559)). Qed.
Lemma lem1233821 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term357 A a1 R R' _22558 _22559.
Proof. exact (EQ_MP (@lem1233820 A a1 R R' _22558 _22559) (@lem1233490 A _22558 _22559 a0 a1 R R' h1)). Qed.
Lemma lem1233863 {A : Type'} (_22563 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term297 A a1 R a0 _22563.
Proof. exact (EQ_MP (@lem1233459 A a1 R a0 _22563) (@lem1233458 A _22563 a0 a1 R R' h1)). Qed.
Lemma lem1233871 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : term287 A R' a0 x.
Proof. exact (proj2 (@lem1232758 A a1 R' a0 x h1)). Qed.
Lemma lem1233875 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term353 A a0 a1 R R' _22561 _22562) = (term358 A a0 a1 R R' _22561 _22562).
Proof. exact (@lem1231307 (term318 A _22561 a0) (term323 A a1 R _22561 _22562) (term286 A R' _22561 _22562)). Qed.
Lemma lem1233882 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term355 A a1 R R' _22561 _22562) = (term356 A a1 R R' _22561 _22562).
Proof. exact (@lem1231307 (term319 A _22562 a1) (term287 A R _22561 _22562) (term286 A R' _22561 _22562)). Qed.
Lemma lem1233883 {A : Type'} (_22561 : A) (a0 : A) : (term359 A _22561 a0) = (term359 A _22561 a0).
Proof. exact (eq_refl (term359 A _22561 a0)). Qed.
Lemma lem1233886 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term358 A a0 a1 R R' _22561 _22562) = (term360 A a0 a1 R R' _22561 _22562).
Proof. exact (MK_COMB (@lem1233883 A _22561 a0) (@lem1233882 A a1 R R' _22561 _22562)). Qed.
Lemma lem1233888 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term353 A a0 a1 R R' _22561 _22562) = (term360 A a0 a1 R R' _22561 _22562).
Proof. exact (TRANS (@lem1233875 A a0 a1 R R' _22561 _22562) (@lem1233886 A a0 a1 R R' _22561 _22562)). Qed.
Lemma lem1233889 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term360 A a0 a1 R R' _22561 _22562.
Proof. exact (EQ_MP (@lem1233888 A a0 a1 R R' _22561 _22562) (@lem1233497 A _22561 _22562 a0 a1 R R' h1)). Qed.
Lemma lem1233953 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : @List.ForallOrdPairs A R' a1) : @List.ForallOrdPairs A R' a1.
Proof. exact (h1). Qed.
Lemma lem1233955 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) : term171 A R' a1.
Proof. exact (h1). Qed.
Lemma lem1234109 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : @List.ForallOrdPairs A R a1.
Proof. exact (proj2 (@lem1232737 A a0 a1 R R' h1)). Qed.
Lemma lem1234110 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term361 A R a1.
Proof. exact (fun h0 : term171 A R a1 => @lem1234109 A a0 a1 R R' h1). Qed.
Lemma lem1234112 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234113 {A : Type'} (R : type1402 A) (a1 : list A) : (term361 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1234112 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1234114 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : @List.ForallOrdPairs A R a1.
Proof. exact (EQ_MP (@lem1234113 A R a1) (@lem1234110 A a0 a1 R R' h1)). Qed.
Lemma lem1234117 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1234119 {A : Type'} (R : type1402 A) (a1 : list A) : (term171 A R a1) = (term363 A R a1).
Proof. exact (@lem1234117 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1234122 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term171 A R a1) : term363 A R a1.
Proof. exact (EQ_MP (@lem1234119 A R a1) (@lem1233515 A R a1 h1)). Qed.
Lemma lem1234125 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (@lem1234122 A R a1 h1 (@lem1234114 A a0 a1 R R' h2)). Qed.
Lemma lem1234126 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : term364.
Proof. exact (fun h0 : ~ False => @lem1234125 A a0 a1 R R' h1 h2). Qed.
Lemma lem1234128 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234129 : term364 = False.
Proof. exact (@lem1234128 False). Qed.
Lemma lem1234130 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1234129) (@lem1234126 A a0 a1 R R' h1 h2)). Qed.
Lemma lem1234212 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : @List.ForallOrdPairs A R a1.
Proof. exact (proj2 (@lem1232737 A a0 a1 R R' h1)). Qed.
Lemma lem1234213 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term361 A R a1.
Proof. exact (fun h0 : term171 A R a1 => @lem1234212 A a0 a1 R R' h1). Qed.
Lemma lem1234215 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234216 {A : Type'} (R : type1402 A) (a1 : list A) : (term361 A R a1) = (@List.ForallOrdPairs A R a1).
Proof. exact (@lem1234215 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1234217 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : @List.ForallOrdPairs A R a1.
Proof. exact (EQ_MP (@lem1234216 A R a1) (@lem1234213 A a0 a1 R R' h1)). Qed.
Lemma lem1234220 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1234222 {A : Type'} (R : type1402 A) (a1 : list A) : (term171 A R a1) = (term363 A R a1).
Proof. exact (@lem1234220 (@List.ForallOrdPairs A R a1)). Qed.
Lemma lem1234225 {A : Type'} (R : type1402 A) (a1 : list A) (h1 : term171 A R a1) : term363 A R a1.
Proof. exact (EQ_MP (@lem1234222 A R a1) (@lem1233601 A R a1 h1)). Qed.
Lemma lem1234228 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (@lem1234225 A R a1 h1 (@lem1234217 A a0 a1 R R' h2)). Qed.
Lemma lem1234229 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : term364.
Proof. exact (fun h0 : ~ False => @lem1234228 A a0 a1 R R' h1 h2). Qed.
Lemma lem1234231 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234232 : term364 = False.
Proof. exact (@lem1234231 False). Qed.
Lemma lem1234233 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1234232) (@lem1234229 A a0 a1 R R' h1 h2)). Qed.
Lemma lem1234315 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A x' a1.
Proof. exact (proj1 (@lem1232749 A a1 R R' x' y h1)). Qed.
Lemma lem1234316 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term365 A x' a1.
Proof. exact (fun h0 : term319 A x' a1 => @lem1234315 A a1 R R' x' y h1). Qed.
Lemma lem1234318 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234319 {A : Type'} (x' : A) (a1 : list A) : (term365 A x' a1) = (@List.In A x' a1).
Proof. exact (@lem1234318 (@List.In A x' a1)). Qed.
Lemma lem1234320 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A x' a1.
Proof. exact (EQ_MP (@lem1234319 A x' a1) (@lem1234316 A a1 R R' x' y h1)). Qed.
Lemma lem1234322 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A y a1.
Proof. exact (proj1 (@lem1232750 A a1 R R' x' y h1)). Qed.
Lemma lem1234323 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term365 A y a1.
Proof. exact (fun h0 : term319 A y a1 => @lem1234322 A a1 R R' x' y h1). Qed.
Lemma lem1234325 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234326 {A : Type'} (y : A) (a1 : list A) : (term365 A y a1) = (@List.In A y a1).
Proof. exact (@lem1234325 (@List.In A y a1)). Qed.
Lemma lem1234327 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A y a1.
Proof. exact (EQ_MP (@lem1234326 A y a1) (@lem1234323 A a1 R R' x' y h1)). Qed.
Lemma lem1234329 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term286 A R x' y.
Proof. exact (proj2 (@lem1232750 A a1 R R' x' y h1)). Qed.
Lemma lem1234330 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term366 A R x' y.
Proof. exact (fun h0 : term287 A R x' y => @lem1234329 A a1 R R' x' y h1). Qed.
Lemma lem1234332 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234333 {A : Type'} (R : type1402 A) (x' : A) (y : A) : (term366 A R x' y) = (term286 A R x' y).
Proof. exact (@lem1234332 (term286 A R x' y)). Qed.
Lemma lem1234334 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term286 A R x' y.
Proof. exact (EQ_MP (@lem1234333 A R x' y) (@lem1234330 A a1 R R' x' y h1)). Qed.
Lemma lem1234350 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234351 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term356 A a1 R R' _22555 _22556) = (term367 A R a1 R' _22555 _22556).
Proof. exact (@lem1234350 (term287 A R _22555 _22556) (term319 A _22556 a1) (term286 A R' _22555 _22556)). Qed.
Lemma lem1234365 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1234366 {A : Type'} (R' : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term297 A a1 R' _22555 _22556) = (term368 A R' _22555 _22556 a1).
Proof. exact (@lem1234365 (term286 A R' _22555 _22556) (term319 A _22556 a1)). Qed.
Lemma lem1234372 {A : Type'} (R : type1402 A) (_22555 : A) (_22556 : A) : (term369 A R _22555 _22556) = (term369 A R _22555 _22556).
Proof. exact (eq_refl (term369 A R _22555 _22556)). Qed.
Lemma lem1234373 {A : Type'} (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term367 A R a1 R' _22555 _22556) = (term370 A R R' _22555 _22556 a1).
Proof. exact (MK_COMB (@lem1234372 A R _22555 _22556) (@lem1234366 A R' _22555 _22556 a1)). Qed.
Lemma lem1234377 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234378 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term370 A R R' _22555 _22556 a1) = (term371 A R' R _22555 _22556 a1).
Proof. exact (@lem1234377 (term286 A R' _22555 _22556) (term287 A R _22555 _22556) (term319 A _22556 a1)). Qed.
Lemma lem1234394 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term367 A R a1 R' _22555 _22556) = (term371 A R' R _22555 _22556 a1).
Proof. exact (TRANS (@lem1234373 A R R' _22555 _22556 a1) (@lem1234378 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234395 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term356 A a1 R R' _22555 _22556) = (term371 A R' R _22555 _22556 a1).
Proof. exact (TRANS (@lem1234351 A R a1 R' _22555 _22556) (@lem1234394 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234396 {A : Type'} (_22555 : A) (a1 : list A) : (term296 A _22555 a1) = (term296 A _22555 a1).
Proof. exact (eq_refl (term296 A _22555 a1)). Qed.
Lemma lem1234397 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term357 A a1 R R' _22555 _22556) = (term372 A R' R _22555 _22556 a1).
Proof. exact (MK_COMB (@lem1234396 A _22555 a1) (@lem1234395 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234401 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234402 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term372 A R' R _22555 _22556 a1) = (term373 A R' R _22555 _22556 a1).
Proof. exact (@lem1234401 (term286 A R' _22555 _22556) (term319 A _22555 a1) (term374 A R _22555 _22556 a1)). Qed.
Lemma lem1234416 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234417 {A : Type'} (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term375 A R _22555 _22556 a1) = (term376 A R _22555 _22556 a1).
Proof. exact (@lem1234416 (term287 A R _22555 _22556) (term319 A _22555 a1) (term319 A _22556 a1)). Qed.
Lemma lem1234433 {A : Type'} (R' : type1402 A) (_22555 : A) (_22556 : A) : (term377 A R' _22555 _22556) = (term377 A R' _22555 _22556).
Proof. exact (eq_refl (term377 A R' _22555 _22556)). Qed.
Lemma lem1234434 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term373 A R' R _22555 _22556 a1) = (term378 A R' R _22555 _22556 a1).
Proof. exact (MK_COMB (@lem1234433 A R' _22555 _22556) (@lem1234417 A R _22555 _22556 a1)). Qed.
Lemma lem1234445 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term372 A R' R _22555 _22556 a1) = (term378 A R' R _22555 _22556 a1).
Proof. exact (TRANS (@lem1234402 A R' R _22555 _22556 a1) (@lem1234434 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234446 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term357 A a1 R R' _22555 _22556) = (term378 A R' R _22555 _22556 a1).
Proof. exact (TRANS (@lem1234397 A R' R _22555 _22556 a1) (@lem1234445 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1234448 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term379 A a1 R R' _22555 _22556) = (term380 A R' R _22555 _22556 a1).
Proof. exact (MK_COMB (@lem1234447) (@lem1234446 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234472 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1234473 {A : Type'} (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term323 A a1 R _22555 _22556) = (term374 A R _22555 _22556 a1).
Proof. exact (@lem1234472 (term287 A R _22555 _22556) (term319 A _22556 a1)). Qed.
Lemma lem1234479 {A : Type'} (_22555 : A) (a1 : list A) : (term296 A _22555 a1) = (term296 A _22555 a1).
Proof. exact (eq_refl (term296 A _22555 a1)). Qed.
Lemma lem1234480 {A : Type'} (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term337 A a1 R _22555 _22556) = (term375 A R _22555 _22556 a1).
Proof. exact (MK_COMB (@lem1234479 A _22555 a1) (@lem1234473 A R _22555 _22556 a1)). Qed.
Lemma lem1234484 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234485 {A : Type'} (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term375 A R _22555 _22556 a1) = (term376 A R _22555 _22556 a1).
Proof. exact (@lem1234484 (term287 A R _22555 _22556) (term319 A _22555 a1) (term319 A _22556 a1)). Qed.
Lemma lem1234501 {A : Type'} (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term337 A a1 R _22555 _22556) = (term376 A R _22555 _22556 a1).
Proof. exact (TRANS (@lem1234480 A R _22555 _22556 a1) (@lem1234485 A R _22555 _22556 a1)). Qed.
Lemma lem1234502 {A : Type'} (R' : type1402 A) (_22555 : A) (_22556 : A) : (term377 A R' _22555 _22556) = (term377 A R' _22555 _22556).
Proof. exact (eq_refl (term377 A R' _22555 _22556)). Qed.
Lemma lem1234503 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : (term381 A R' a1 R _22555 _22556) = (term378 A R' R _22555 _22556 a1).
Proof. exact (MK_COMB (@lem1234502 A R' _22555 _22556) (@lem1234501 A R _22555 _22556 a1)). Qed.
Lemma lem1234514 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : ((term357 A a1 R R' _22555 _22556) = (term381 A R' a1 R _22555 _22556)) = ((term378 A R' R _22555 _22556 a1) = (term378 A R' R _22555 _22556 a1)).
Proof. exact (MK_COMB (@lem1234448 A R' R _22555 _22556 a1) (@lem1234503 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234516 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1234517 (x : Prop) : (x = x) = True.
Proof. exact (@lem1234516 Prop x). Qed.
Lemma lem1234518 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22555 : A) (_22556 : A) (a1 : list A) : ((term378 A R' R _22555 _22556 a1) = (term378 A R' R _22555 _22556 a1)) = True.
Proof. exact (@lem1234517 (term378 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234519 {A : Type'} (R' : type1402 A) (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : ((term357 A a1 R R' _22555 _22556) = (term381 A R' a1 R _22555 _22556)) = True.
Proof. exact (TRANS (@lem1234514 A R' R _22555 _22556 a1) (@lem1234518 A R' R _22555 _22556 a1)). Qed.
Lemma lem1234520 {A : Type'} (R' : type1402 A) (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : True = ((term357 A a1 R R' _22555 _22556) = (term381 A R' a1 R _22555 _22556)).
Proof. exact (SYM (@lem1234519 A R' a1 R _22555 _22556)). Qed.
Lemma lem1234521 {A : Type'} (R' : type1402 A) (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term357 A a1 R R' _22555 _22556) = (term381 A R' a1 R _22555 _22556).
Proof. exact (EQ_MP (@lem1234520 A R' a1 R _22555 _22556) (@lem0)). Qed.
Lemma lem1234522 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term381 A R' a1 R _22555 _22556.
Proof. exact (EQ_MP (@lem1234521 A R' a1 R _22555 _22556) (@lem1233731 A _22555 _22556 a0 a1 R R' h1)). Qed.
Lemma lem1234524 (b : Prop) (a : Prop) : (a \/ b) = (term382 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1234525 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term381 A R' a1 R _22555 _22556) = (term383 A a1 R R' _22555 _22556).
Proof. exact (@lem1234524 (term337 A a1 R _22555 _22556) (term286 A R' _22555 _22556)). Qed.
Lemma lem1234527 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1234528 {A : Type'} (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term386 A a1 R _22555 _22556) = (term387 A a1 R _22555 _22556).
Proof. exact (@lem1234527 (term319 A _22555 a1) (term323 A a1 R _22555 _22556)). Qed.
Lemma lem1234530 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1234531 {A : Type'} (_22555 : A) (a1 : list A) : (term388 A _22555 a1) = (@List.In A _22555 a1).
Proof. exact (@lem1234530 (@List.In A _22555 a1)). Qed.
Lemma lem1234532 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1234533 {A : Type'} (_22555 : A) (a1 : list A) : (term389 A _22555 a1) = (term304 A _22555 a1).
Proof. exact (MK_COMB (@lem1234532) (@lem1234531 A _22555 a1)). Qed.
Lemma lem1234535 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1234536 {A : Type'} (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term390 A a1 R _22555 _22556) = (term391 A a1 R _22555 _22556).
Proof. exact (@lem1234535 (term319 A _22556 a1) (term287 A R _22555 _22556)). Qed.
Lemma lem1234538 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1234539 {A : Type'} (_22556 : A) (a1 : list A) : (term388 A _22556 a1) = (@List.In A _22556 a1).
Proof. exact (@lem1234538 (@List.In A _22556 a1)). Qed.
Lemma lem1234540 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1234541 {A : Type'} (_22556 : A) (a1 : list A) : (term389 A _22556 a1) = (term304 A _22556 a1).
Proof. exact (MK_COMB (@lem1234540) (@lem1234539 A _22556 a1)). Qed.
Lemma lem1234543 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1234544 {A : Type'} (R : type1402 A) (_22555 : A) (_22556 : A) : (term392 A R _22555 _22556) = (term286 A R _22555 _22556).
Proof. exact (@lem1234543 (term286 A R _22555 _22556)). Qed.
Lemma lem1234545 {A : Type'} (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term391 A a1 R _22555 _22556) = (term309 A a1 R _22555 _22556).
Proof. exact (MK_COMB (@lem1234541 A _22556 a1) (@lem1234544 A R _22555 _22556)). Qed.
Lemma lem1234546 {A : Type'} (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term390 A a1 R _22555 _22556) = (term309 A a1 R _22555 _22556).
Proof. exact (TRANS (@lem1234536 A a1 R _22555 _22556) (@lem1234545 A a1 R _22555 _22556)). Qed.
Lemma lem1234547 {A : Type'} (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term387 A a1 R _22555 _22556) = (term310 A a1 R _22555 _22556).
Proof. exact (MK_COMB (@lem1234533 A _22555 a1) (@lem1234546 A a1 R _22555 _22556)). Qed.
Lemma lem1234548 {A : Type'} (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term386 A a1 R _22555 _22556) = (term310 A a1 R _22555 _22556).
Proof. exact (TRANS (@lem1234528 A a1 R _22555 _22556) (@lem1234547 A a1 R _22555 _22556)). Qed.
Lemma lem1234549 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1234550 {A : Type'} (a1 : list A) (R : type1402 A) (_22555 : A) (_22556 : A) : (term393 A a1 R _22555 _22556) = (term394 A a1 R _22555 _22556).
Proof. exact (MK_COMB (@lem1234549) (@lem1234548 A a1 R _22555 _22556)). Qed.
Lemma lem1234551 {A : Type'} (R' : type1402 A) (_22555 : A) (_22556 : A) : (term286 A R' _22555 _22556) = (term286 A R' _22555 _22556).
Proof. exact (eq_refl (term286 A R' _22555 _22556)). Qed.
Lemma lem1234552 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term383 A a1 R R' _22555 _22556) = (term395 A a1 R R' _22555 _22556).
Proof. exact (MK_COMB (@lem1234550 A a1 R _22555 _22556) (@lem1234551 A R' _22555 _22556)). Qed.
Lemma lem1234553 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22555 : A) (_22556 : A) : (term381 A R' a1 R _22555 _22556) = (term395 A a1 R R' _22555 _22556).
Proof. exact (TRANS (@lem1234525 A a1 R R' _22555 _22556) (@lem1234552 A a1 R R' _22555 _22556)). Qed.
Lemma lem1234555 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term309 A a1 R x' y.
Proof. exact (conj (@lem1234327 A a1 R R' x' y h1) (@lem1234334 A a1 R R' x' y h1)). Qed.
Lemma lem1234556 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term310 A a1 R x' y.
Proof. exact (conj (@lem1234320 A a1 R R' x' y h1) (@lem1234555 A a1 R R' x' y h1)). Qed.
Lemma lem1234558 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term395 A a1 R R' _22555 _22556.
Proof. exact (EQ_MP (@lem1234553 A a1 R R' _22555 _22556) (@lem1234522 A _22555 _22556 a0 a1 R R' h1)). Qed.
Lemma lem1234559 {A : Type'} (_22555 : A) (_22556 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term395 A a1 R R' _22555 _22556.
Proof. exact (@lem1234558 A _22555 _22556 a0 a1 R R' h1). Qed.
Lemma lem1234560 {A : Type'} (x' : A) (y : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term395 A a1 R R' x' y.
Proof. exact (@lem1234559 A x' y a0 a1 R R' h1). Qed.
Lemma lem1234563 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term286 A R' x' y.
Proof. exact (@lem1234560 A x' y a0 a1 R R' h1 (@lem1234556 A a1 R R' x' y h2)). Qed.
Lemma lem1234564 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term366 A R' x' y.
Proof. exact (fun h0 : term287 A R' x' y => @lem1234563 A a0 a1 R R' x' y h1 h2). Qed.
Lemma lem1234566 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234567 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (term366 A R' x' y) = (term286 A R' x' y).
Proof. exact (@lem1234566 (term286 A R' x' y)). Qed.
Lemma lem1234568 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term286 A R' x' y.
Proof. exact (EQ_MP (@lem1234567 A R' x' y) (@lem1234564 A a0 a1 R R' x' y h1 h2)). Qed.
Lemma lem1234571 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1234573 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (term287 A R' x' y) = (term396 A R' x' y).
Proof. exact (@lem1234571 (term286 A R' x' y)). Qed.
Lemma lem1234576 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term396 A R' x' y.
Proof. exact (EQ_MP (@lem1234573 A R' x' y) (@lem1233685 A a1 R R' x' y h1)). Qed.
Lemma lem1234579 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : False.
Proof. exact (@lem1234576 A a1 R R' x' y h2 (@lem1234568 A a0 a1 R R' x' y h1 h2)). Qed.
Lemma lem1234580 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term364.
Proof. exact (fun h0 : ~ False => @lem1234579 A a0 a1 R R' x' y h1 h2). Qed.
Lemma lem1234582 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234583 : term364 = False.
Proof. exact (@lem1234582 False). Qed.
Lemma lem1234584 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : False.
Proof. exact (EQ_MP (@lem1234583) (@lem1234580 A a0 a1 R R' x' y h1 h2)). Qed.
Lemma lem1234666 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A x' a1.
Proof. exact (proj1 (@lem1232749 A a1 R R' x' y h1)). Qed.
Lemma lem1234667 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term365 A x' a1.
Proof. exact (fun h0 : term319 A x' a1 => @lem1234666 A a1 R R' x' y h1). Qed.
Lemma lem1234669 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234670 {A : Type'} (x' : A) (a1 : list A) : (term365 A x' a1) = (@List.In A x' a1).
Proof. exact (@lem1234669 (@List.In A x' a1)). Qed.
Lemma lem1234671 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A x' a1.
Proof. exact (EQ_MP (@lem1234670 A x' a1) (@lem1234667 A a1 R R' x' y h1)). Qed.
Lemma lem1234673 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A y a1.
Proof. exact (proj1 (@lem1232750 A a1 R R' x' y h1)). Qed.
Lemma lem1234674 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term365 A y a1.
Proof. exact (fun h0 : term319 A y a1 => @lem1234673 A a1 R R' x' y h1). Qed.
Lemma lem1234676 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234677 {A : Type'} (y : A) (a1 : list A) : (term365 A y a1) = (@List.In A y a1).
Proof. exact (@lem1234676 (@List.In A y a1)). Qed.
Lemma lem1234678 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : @List.In A y a1.
Proof. exact (EQ_MP (@lem1234677 A y a1) (@lem1234674 A a1 R R' x' y h1)). Qed.
Lemma lem1234680 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term286 A R x' y.
Proof. exact (proj2 (@lem1232750 A a1 R R' x' y h1)). Qed.
Lemma lem1234681 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term366 A R x' y.
Proof. exact (fun h0 : term287 A R x' y => @lem1234680 A a1 R R' x' y h1). Qed.
Lemma lem1234683 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234684 {A : Type'} (R : type1402 A) (x' : A) (y : A) : (term366 A R x' y) = (term286 A R x' y).
Proof. exact (@lem1234683 (term286 A R x' y)). Qed.
Lemma lem1234685 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term286 A R x' y.
Proof. exact (EQ_MP (@lem1234684 A R x' y) (@lem1234681 A a1 R R' x' y h1)). Qed.
Lemma lem1234701 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234702 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term356 A a1 R R' _22558 _22559) = (term367 A R a1 R' _22558 _22559).
Proof. exact (@lem1234701 (term287 A R _22558 _22559) (term319 A _22559 a1) (term286 A R' _22558 _22559)). Qed.
Lemma lem1234716 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1234717 {A : Type'} (R' : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term297 A a1 R' _22558 _22559) = (term368 A R' _22558 _22559 a1).
Proof. exact (@lem1234716 (term286 A R' _22558 _22559) (term319 A _22559 a1)). Qed.
Lemma lem1234723 {A : Type'} (R : type1402 A) (_22558 : A) (_22559 : A) : (term369 A R _22558 _22559) = (term369 A R _22558 _22559).
Proof. exact (eq_refl (term369 A R _22558 _22559)). Qed.
Lemma lem1234724 {A : Type'} (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term367 A R a1 R' _22558 _22559) = (term370 A R R' _22558 _22559 a1).
Proof. exact (MK_COMB (@lem1234723 A R _22558 _22559) (@lem1234717 A R' _22558 _22559 a1)). Qed.
Lemma lem1234728 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234729 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term370 A R R' _22558 _22559 a1) = (term371 A R' R _22558 _22559 a1).
Proof. exact (@lem1234728 (term286 A R' _22558 _22559) (term287 A R _22558 _22559) (term319 A _22559 a1)). Qed.
Lemma lem1234745 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term367 A R a1 R' _22558 _22559) = (term371 A R' R _22558 _22559 a1).
Proof. exact (TRANS (@lem1234724 A R R' _22558 _22559 a1) (@lem1234729 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234746 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term356 A a1 R R' _22558 _22559) = (term371 A R' R _22558 _22559 a1).
Proof. exact (TRANS (@lem1234702 A R a1 R' _22558 _22559) (@lem1234745 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234747 {A : Type'} (_22558 : A) (a1 : list A) : (term296 A _22558 a1) = (term296 A _22558 a1).
Proof. exact (eq_refl (term296 A _22558 a1)). Qed.
Lemma lem1234748 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term357 A a1 R R' _22558 _22559) = (term372 A R' R _22558 _22559 a1).
Proof. exact (MK_COMB (@lem1234747 A _22558 a1) (@lem1234746 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234752 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234753 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term372 A R' R _22558 _22559 a1) = (term373 A R' R _22558 _22559 a1).
Proof. exact (@lem1234752 (term286 A R' _22558 _22559) (term319 A _22558 a1) (term374 A R _22558 _22559 a1)). Qed.
Lemma lem1234767 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234768 {A : Type'} (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term375 A R _22558 _22559 a1) = (term376 A R _22558 _22559 a1).
Proof. exact (@lem1234767 (term287 A R _22558 _22559) (term319 A _22558 a1) (term319 A _22559 a1)). Qed.
Lemma lem1234784 {A : Type'} (R' : type1402 A) (_22558 : A) (_22559 : A) : (term377 A R' _22558 _22559) = (term377 A R' _22558 _22559).
Proof. exact (eq_refl (term377 A R' _22558 _22559)). Qed.
Lemma lem1234785 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term373 A R' R _22558 _22559 a1) = (term378 A R' R _22558 _22559 a1).
Proof. exact (MK_COMB (@lem1234784 A R' _22558 _22559) (@lem1234768 A R _22558 _22559 a1)). Qed.
Lemma lem1234796 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term372 A R' R _22558 _22559 a1) = (term378 A R' R _22558 _22559 a1).
Proof. exact (TRANS (@lem1234753 A R' R _22558 _22559 a1) (@lem1234785 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234797 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term357 A a1 R R' _22558 _22559) = (term378 A R' R _22558 _22559 a1).
Proof. exact (TRANS (@lem1234748 A R' R _22558 _22559 a1) (@lem1234796 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234798 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1234799 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term379 A a1 R R' _22558 _22559) = (term380 A R' R _22558 _22559 a1).
Proof. exact (MK_COMB (@lem1234798) (@lem1234797 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234823 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1234824 {A : Type'} (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term323 A a1 R _22558 _22559) = (term374 A R _22558 _22559 a1).
Proof. exact (@lem1234823 (term287 A R _22558 _22559) (term319 A _22559 a1)). Qed.
Lemma lem1234830 {A : Type'} (_22558 : A) (a1 : list A) : (term296 A _22558 a1) = (term296 A _22558 a1).
Proof. exact (eq_refl (term296 A _22558 a1)). Qed.
Lemma lem1234831 {A : Type'} (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term337 A a1 R _22558 _22559) = (term375 A R _22558 _22559 a1).
Proof. exact (MK_COMB (@lem1234830 A _22558 a1) (@lem1234824 A R _22558 _22559 a1)). Qed.
Lemma lem1234835 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1234836 {A : Type'} (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term375 A R _22558 _22559 a1) = (term376 A R _22558 _22559 a1).
Proof. exact (@lem1234835 (term287 A R _22558 _22559) (term319 A _22558 a1) (term319 A _22559 a1)). Qed.
Lemma lem1234852 {A : Type'} (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term337 A a1 R _22558 _22559) = (term376 A R _22558 _22559 a1).
Proof. exact (TRANS (@lem1234831 A R _22558 _22559 a1) (@lem1234836 A R _22558 _22559 a1)). Qed.
Lemma lem1234853 {A : Type'} (R' : type1402 A) (_22558 : A) (_22559 : A) : (term377 A R' _22558 _22559) = (term377 A R' _22558 _22559).
Proof. exact (eq_refl (term377 A R' _22558 _22559)). Qed.
Lemma lem1234854 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : (term381 A R' a1 R _22558 _22559) = (term378 A R' R _22558 _22559 a1).
Proof. exact (MK_COMB (@lem1234853 A R' _22558 _22559) (@lem1234852 A R _22558 _22559 a1)). Qed.
Lemma lem1234865 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : ((term357 A a1 R R' _22558 _22559) = (term381 A R' a1 R _22558 _22559)) = ((term378 A R' R _22558 _22559 a1) = (term378 A R' R _22558 _22559 a1)).
Proof. exact (MK_COMB (@lem1234799 A R' R _22558 _22559 a1) (@lem1234854 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234867 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1234868 (x : Prop) : (x = x) = True.
Proof. exact (@lem1234867 Prop x). Qed.
Lemma lem1234869 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22558 : A) (_22559 : A) (a1 : list A) : ((term378 A R' R _22558 _22559 a1) = (term378 A R' R _22558 _22559 a1)) = True.
Proof. exact (@lem1234868 (term378 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234870 {A : Type'} (R' : type1402 A) (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : ((term357 A a1 R R' _22558 _22559) = (term381 A R' a1 R _22558 _22559)) = True.
Proof. exact (TRANS (@lem1234865 A R' R _22558 _22559 a1) (@lem1234869 A R' R _22558 _22559 a1)). Qed.
Lemma lem1234871 {A : Type'} (R' : type1402 A) (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : True = ((term357 A a1 R R' _22558 _22559) = (term381 A R' a1 R _22558 _22559)).
Proof. exact (SYM (@lem1234870 A R' a1 R _22558 _22559)). Qed.
Lemma lem1234872 {A : Type'} (R' : type1402 A) (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term357 A a1 R R' _22558 _22559) = (term381 A R' a1 R _22558 _22559).
Proof. exact (EQ_MP (@lem1234871 A R' a1 R _22558 _22559) (@lem0)). Qed.
Lemma lem1234873 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term381 A R' a1 R _22558 _22559.
Proof. exact (EQ_MP (@lem1234872 A R' a1 R _22558 _22559) (@lem1233821 A _22558 _22559 a0 a1 R R' h1)). Qed.
Lemma lem1234875 (b : Prop) (a : Prop) : (a \/ b) = (term382 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1234876 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term381 A R' a1 R _22558 _22559) = (term383 A a1 R R' _22558 _22559).
Proof. exact (@lem1234875 (term337 A a1 R _22558 _22559) (term286 A R' _22558 _22559)). Qed.
Lemma lem1234878 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1234879 {A : Type'} (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term386 A a1 R _22558 _22559) = (term387 A a1 R _22558 _22559).
Proof. exact (@lem1234878 (term319 A _22558 a1) (term323 A a1 R _22558 _22559)). Qed.
Lemma lem1234881 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1234882 {A : Type'} (_22558 : A) (a1 : list A) : (term388 A _22558 a1) = (@List.In A _22558 a1).
Proof. exact (@lem1234881 (@List.In A _22558 a1)). Qed.
Lemma lem1234883 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1234884 {A : Type'} (_22558 : A) (a1 : list A) : (term389 A _22558 a1) = (term304 A _22558 a1).
Proof. exact (MK_COMB (@lem1234883) (@lem1234882 A _22558 a1)). Qed.
Lemma lem1234886 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1234887 {A : Type'} (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term390 A a1 R _22558 _22559) = (term391 A a1 R _22558 _22559).
Proof. exact (@lem1234886 (term319 A _22559 a1) (term287 A R _22558 _22559)). Qed.
Lemma lem1234889 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1234890 {A : Type'} (_22559 : A) (a1 : list A) : (term388 A _22559 a1) = (@List.In A _22559 a1).
Proof. exact (@lem1234889 (@List.In A _22559 a1)). Qed.
Lemma lem1234891 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1234892 {A : Type'} (_22559 : A) (a1 : list A) : (term389 A _22559 a1) = (term304 A _22559 a1).
Proof. exact (MK_COMB (@lem1234891) (@lem1234890 A _22559 a1)). Qed.
Lemma lem1234894 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1234895 {A : Type'} (R : type1402 A) (_22558 : A) (_22559 : A) : (term392 A R _22558 _22559) = (term286 A R _22558 _22559).
Proof. exact (@lem1234894 (term286 A R _22558 _22559)). Qed.
Lemma lem1234896 {A : Type'} (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term391 A a1 R _22558 _22559) = (term309 A a1 R _22558 _22559).
Proof. exact (MK_COMB (@lem1234892 A _22559 a1) (@lem1234895 A R _22558 _22559)). Qed.
Lemma lem1234897 {A : Type'} (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term390 A a1 R _22558 _22559) = (term309 A a1 R _22558 _22559).
Proof. exact (TRANS (@lem1234887 A a1 R _22558 _22559) (@lem1234896 A a1 R _22558 _22559)). Qed.
Lemma lem1234898 {A : Type'} (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term387 A a1 R _22558 _22559) = (term310 A a1 R _22558 _22559).
Proof. exact (MK_COMB (@lem1234884 A _22558 a1) (@lem1234897 A a1 R _22558 _22559)). Qed.
Lemma lem1234899 {A : Type'} (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term386 A a1 R _22558 _22559) = (term310 A a1 R _22558 _22559).
Proof. exact (TRANS (@lem1234879 A a1 R _22558 _22559) (@lem1234898 A a1 R _22558 _22559)). Qed.
Lemma lem1234900 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1234901 {A : Type'} (a1 : list A) (R : type1402 A) (_22558 : A) (_22559 : A) : (term393 A a1 R _22558 _22559) = (term394 A a1 R _22558 _22559).
Proof. exact (MK_COMB (@lem1234900) (@lem1234899 A a1 R _22558 _22559)). Qed.
Lemma lem1234902 {A : Type'} (R' : type1402 A) (_22558 : A) (_22559 : A) : (term286 A R' _22558 _22559) = (term286 A R' _22558 _22559).
Proof. exact (eq_refl (term286 A R' _22558 _22559)). Qed.
Lemma lem1234903 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term383 A a1 R R' _22558 _22559) = (term395 A a1 R R' _22558 _22559).
Proof. exact (MK_COMB (@lem1234901 A a1 R _22558 _22559) (@lem1234902 A R' _22558 _22559)). Qed.
Lemma lem1234904 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22558 : A) (_22559 : A) : (term381 A R' a1 R _22558 _22559) = (term395 A a1 R R' _22558 _22559).
Proof. exact (TRANS (@lem1234876 A a1 R R' _22558 _22559) (@lem1234903 A a1 R R' _22558 _22559)). Qed.
Lemma lem1234906 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term309 A a1 R x' y.
Proof. exact (conj (@lem1234678 A a1 R R' x' y h1) (@lem1234685 A a1 R R' x' y h1)). Qed.
Lemma lem1234907 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term310 A a1 R x' y.
Proof. exact (conj (@lem1234671 A a1 R R' x' y h1) (@lem1234906 A a1 R R' x' y h1)). Qed.
Lemma lem1234909 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term395 A a1 R R' _22558 _22559.
Proof. exact (EQ_MP (@lem1234904 A a1 R R' _22558 _22559) (@lem1234873 A _22558 _22559 a0 a1 R R' h1)). Qed.
Lemma lem1234910 {A : Type'} (_22558 : A) (_22559 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term395 A a1 R R' _22558 _22559.
Proof. exact (@lem1234909 A _22558 _22559 a0 a1 R R' h1). Qed.
Lemma lem1234911 {A : Type'} (x' : A) (y : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term395 A a1 R R' x' y.
Proof. exact (@lem1234910 A x' y a0 a1 R R' h1). Qed.
Lemma lem1234914 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term286 A R' x' y.
Proof. exact (@lem1234911 A x' y a0 a1 R R' h1 (@lem1234907 A a1 R R' x' y h2)). Qed.
Lemma lem1234915 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term366 A R' x' y.
Proof. exact (fun h0 : term287 A R' x' y => @lem1234914 A a0 a1 R R' x' y h1 h2). Qed.
Lemma lem1234917 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234918 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (term366 A R' x' y) = (term286 A R' x' y).
Proof. exact (@lem1234917 (term286 A R' x' y)). Qed.
Lemma lem1234919 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term286 A R' x' y.
Proof. exact (EQ_MP (@lem1234918 A R' x' y) (@lem1234915 A a0 a1 R R' x' y h1 h2)). Qed.
Lemma lem1234922 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1234924 {A : Type'} (R' : type1402 A) (x' : A) (y : A) : (term287 A R' x' y) = (term396 A R' x' y).
Proof. exact (@lem1234922 (term286 A R' x' y)). Qed.
Lemma lem1234927 {A : Type'} (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term313 A a1 R R' x' y) : term396 A R' x' y.
Proof. exact (EQ_MP (@lem1234924 A R' x' y) (@lem1233777 A a1 R R' x' y h1)). Qed.
Lemma lem1234930 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : False.
Proof. exact (@lem1234927 A a1 R R' x' y h2 (@lem1234919 A a0 a1 R R' x' y h1 h2)). Qed.
Lemma lem1234931 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : term364.
Proof. exact (fun h0 : ~ False => @lem1234930 A a0 a1 R R' x' y h1 h2). Qed.
Lemma lem1234933 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1234934 : term364 = False.
Proof. exact (@lem1234933 False). Qed.
Lemma lem1234935 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (x' : A) (y : A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) : False.
Proof. exact (EQ_MP (@lem1234934) (@lem1234931 A a0 a1 R R' x' y h1 h2)). Qed.
Lemma lem1235017 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem1235018 {A : Type'} (x : A) : x = x.
Proof. exact (@lem1235017 A x). Qed.
Lemma lem1235019 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (@lem1235018 A a0). Qed.
Lemma lem1235020 {A : Type'} (a0 : A) : term397 A a0.
Proof. exact (fun h0 : term398 A a0 => @lem1235019 A a0). Qed.
Lemma lem1235022 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235023 {A : Type'} (a0 : A) : (term397 A a0) = (a0 = a0).
Proof. exact (@lem1235022 (a0 = a0)). Qed.
Lemma lem1235024 {A : Type'} (a0 : A) : a0 = a0.
Proof. exact (EQ_MP (@lem1235023 A a0) (@lem1235020 A a0)). Qed.
Lemma lem1235026 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : @List.In A x a1.
Proof. exact (proj1 (@lem1232758 A a1 R' a0 x h1)). Qed.
Lemma lem1235027 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : term365 A x a1.
Proof. exact (fun h0 : term319 A x a1 => @lem1235026 A a1 R' a0 x h1). Qed.
Lemma lem1235029 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235030 {A : Type'} (x : A) (a1 : list A) : (term365 A x a1) = (@List.In A x a1).
Proof. exact (@lem1235029 (@List.In A x a1)). Qed.
Lemma lem1235031 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : @List.In A x a1.
Proof. exact (EQ_MP (@lem1235030 A x a1) (@lem1235027 A a1 R' a0 x h1)). Qed.
Lemma lem1235033 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : @List.In A x a1.
Proof. exact (proj1 (@lem1232758 A a1 R' a0 x h1)). Qed.
Lemma lem1235034 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : term365 A x a1.
Proof. exact (fun h0 : term319 A x a1 => @lem1235033 A a1 R' a0 x h1). Qed.
Lemma lem1235036 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235037 {A : Type'} (x : A) (a1 : list A) : (term365 A x a1) = (@List.In A x a1).
Proof. exact (@lem1235036 (@List.In A x a1)). Qed.
Lemma lem1235038 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : @List.In A x a1.
Proof. exact (EQ_MP (@lem1235037 A x a1) (@lem1235034 A a1 R' a0 x h1)). Qed.
Lemma lem1235044 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1235045 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : (term297 A a1 R a0 _22563) = (term368 A R a0 _22563 a1).
Proof. exact (@lem1235044 (term286 A R a0 _22563) (term319 A _22563 a1)). Qed.
Lemma lem1235051 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235052 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : (term399 A a1 R a0 _22563) = (term400 A R a0 _22563 a1).
Proof. exact (MK_COMB (@lem1235051) (@lem1235045 A R a0 _22563 a1)). Qed.
Lemma lem1235058 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : (term368 A R a0 _22563 a1) = (term368 A R a0 _22563 a1).
Proof. exact (eq_refl (term368 A R a0 _22563 a1)). Qed.
Lemma lem1235059 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : ((term297 A a1 R a0 _22563) = (term368 A R a0 _22563 a1)) = ((term368 A R a0 _22563 a1) = (term368 A R a0 _22563 a1)).
Proof. exact (MK_COMB (@lem1235052 A R a0 _22563 a1) (@lem1235058 A R a0 _22563 a1)). Qed.
Lemma lem1235061 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1235062 (x : Prop) : (x = x) = True.
Proof. exact (@lem1235061 Prop x). Qed.
Lemma lem1235063 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : ((term368 A R a0 _22563 a1) = (term368 A R a0 _22563 a1)) = True.
Proof. exact (@lem1235062 (term368 A R a0 _22563 a1)). Qed.
Lemma lem1235064 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : ((term297 A a1 R a0 _22563) = (term368 A R a0 _22563 a1)) = True.
Proof. exact (TRANS (@lem1235059 A R a0 _22563 a1) (@lem1235063 A R a0 _22563 a1)). Qed.
Lemma lem1235065 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : True = ((term297 A a1 R a0 _22563) = (term368 A R a0 _22563 a1)).
Proof. exact (SYM (@lem1235064 A R a0 _22563 a1)). Qed.
Lemma lem1235066 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) (a1 : list A) : (term297 A a1 R a0 _22563) = (term368 A R a0 _22563 a1).
Proof. exact (EQ_MP (@lem1235065 A R a0 _22563 a1) (@lem0)). Qed.
Lemma lem1235067 {A : Type'} (_22563 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term368 A R a0 _22563 a1.
Proof. exact (EQ_MP (@lem1235066 A R a0 _22563 a1) (@lem1233863 A _22563 a0 a1 R R' h1)). Qed.
Lemma lem1235069 (b : Prop) (a : Prop) : (a \/ b) = (term382 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1235070 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22563 : A) : (term368 A R a0 _22563 a1) = (term401 A a1 R a0 _22563).
Proof. exact (@lem1235069 (term319 A _22563 a1) (term286 A R a0 _22563)). Qed.
Lemma lem1235072 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1235073 {A : Type'} (_22563 : A) (a1 : list A) : (term388 A _22563 a1) = (@List.In A _22563 a1).
Proof. exact (@lem1235072 (@List.In A _22563 a1)). Qed.
Lemma lem1235074 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1235075 {A : Type'} (_22563 : A) (a1 : list A) : (term402 A _22563 a1) = (term403 A _22563 a1).
Proof. exact (MK_COMB (@lem1235074) (@lem1235073 A _22563 a1)). Qed.
Lemma lem1235076 {A : Type'} (R : type1402 A) (a0 : A) (_22563 : A) : (term286 A R a0 _22563) = (term286 A R a0 _22563).
Proof. exact (eq_refl (term286 A R a0 _22563)). Qed.
Lemma lem1235077 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22563 : A) : (term401 A a1 R a0 _22563) = (term404 A a1 R a0 _22563).
Proof. exact (MK_COMB (@lem1235075 A _22563 a1) (@lem1235076 A R a0 _22563)). Qed.
Lemma lem1235078 {A : Type'} (a1 : list A) (R : type1402 A) (a0 : A) (_22563 : A) : (term368 A R a0 _22563 a1) = (term404 A a1 R a0 _22563).
Proof. exact (TRANS (@lem1235070 A a1 R a0 _22563) (@lem1235077 A a1 R a0 _22563)). Qed.
Lemma lem1235081 {A : Type'} (_22563 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term404 A a1 R a0 _22563.
Proof. exact (EQ_MP (@lem1235078 A a1 R a0 _22563) (@lem1235067 A _22563 a0 a1 R R' h1)). Qed.
Lemma lem1235082 {A : Type'} (_22563 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term404 A a1 R a0 _22563.
Proof. exact (@lem1235081 A _22563 a0 a1 R R' h1). Qed.
Lemma lem1235083 {A : Type'} (x : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term404 A a1 R a0 x.
Proof. exact (@lem1235082 A x a0 a1 R R' h1). Qed.
Lemma lem1235086 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term286 A R a0 x.
Proof. exact (@lem1235083 A x a0 a1 R R' h1 (@lem1235038 A a1 R' a0 x h2)). Qed.
Lemma lem1235087 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term366 A R a0 x.
Proof. exact (fun h0 : term287 A R a0 x => @lem1235086 A R a1 R' a0 x h1 h2). Qed.
Lemma lem1235089 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235090 {A : Type'} (R : type1402 A) (a0 : A) (x : A) : (term366 A R a0 x) = (term286 A R a0 x).
Proof. exact (@lem1235089 (term286 A R a0 x)). Qed.
Lemma lem1235091 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term286 A R a0 x.
Proof. exact (EQ_MP (@lem1235090 A R a0 x) (@lem1235087 A R a1 R' a0 x h1 h2)). Qed.
Lemma lem1235109 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1235110 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term356 A a1 R R' _22561 _22562) = (term367 A R a1 R' _22561 _22562).
Proof. exact (@lem1235109 (term287 A R _22561 _22562) (term319 A _22562 a1) (term286 A R' _22561 _22562)). Qed.
Lemma lem1235124 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1235125 {A : Type'} (R' : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term297 A a1 R' _22561 _22562) = (term368 A R' _22561 _22562 a1).
Proof. exact (@lem1235124 (term286 A R' _22561 _22562) (term319 A _22562 a1)). Qed.
Lemma lem1235131 {A : Type'} (R : type1402 A) (_22561 : A) (_22562 : A) : (term369 A R _22561 _22562) = (term369 A R _22561 _22562).
Proof. exact (eq_refl (term369 A R _22561 _22562)). Qed.
Lemma lem1235132 {A : Type'} (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term367 A R a1 R' _22561 _22562) = (term370 A R R' _22561 _22562 a1).
Proof. exact (MK_COMB (@lem1235131 A R _22561 _22562) (@lem1235125 A R' _22561 _22562 a1)). Qed.
Lemma lem1235136 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1235137 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term370 A R R' _22561 _22562 a1) = (term371 A R' R _22561 _22562 a1).
Proof. exact (@lem1235136 (term286 A R' _22561 _22562) (term287 A R _22561 _22562) (term319 A _22562 a1)). Qed.
Lemma lem1235153 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term367 A R a1 R' _22561 _22562) = (term371 A R' R _22561 _22562 a1).
Proof. exact (TRANS (@lem1235132 A R R' _22561 _22562 a1) (@lem1235137 A R' R _22561 _22562 a1)). Qed.
Lemma lem1235154 {A : Type'} (R' : type1402 A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term356 A a1 R R' _22561 _22562) = (term371 A R' R _22561 _22562 a1).
Proof. exact (TRANS (@lem1235110 A R a1 R' _22561 _22562) (@lem1235153 A R' R _22561 _22562 a1)). Qed.
Lemma lem1235155 {A : Type'} (_22561 : A) (a0 : A) : (term359 A _22561 a0) = (term359 A _22561 a0).
Proof. exact (eq_refl (term359 A _22561 a0)). Qed.
Lemma lem1235156 {A : Type'} (a0 : A) (R' : type1402 A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term360 A a0 a1 R R' _22561 _22562) = (term405 A a0 R' R _22561 _22562 a1).
Proof. exact (MK_COMB (@lem1235155 A _22561 a0) (@lem1235154 A R' R _22561 _22562 a1)). Qed.
Lemma lem1235160 (q : Prop) (p : Prop) (r : Prop) : (term5 p q r) = (term5 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem1235161 {A : Type'} (R' : type1402 A) (a0 : A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term405 A a0 R' R _22561 _22562 a1) = (term406 A R' a0 R _22561 _22562 a1).
Proof. exact (@lem1235160 (term286 A R' _22561 _22562) (term318 A _22561 a0) (term374 A R _22561 _22562 a1)). Qed.
Lemma lem1235189 {A : Type'} (R' : type1402 A) (a0 : A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term360 A a0 a1 R R' _22561 _22562) = (term406 A R' a0 R _22561 _22562 a1).
Proof. exact (TRANS (@lem1235156 A a0 R' R _22561 _22562 a1) (@lem1235161 A R' a0 R _22561 _22562 a1)). Qed.
Lemma lem1235190 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1235191 {A : Type'} (R' : type1402 A) (a0 : A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term407 A a0 a1 R R' _22561 _22562) = (term408 A R' a0 R _22561 _22562 a1).
Proof. exact (MK_COMB (@lem1235190) (@lem1235189 A R' a0 R _22561 _22562 a1)). Qed.
Lemma lem1235217 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1235218 {A : Type'} (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term323 A a1 R _22561 _22562) = (term374 A R _22561 _22562 a1).
Proof. exact (@lem1235217 (term287 A R _22561 _22562) (term319 A _22562 a1)). Qed.
Lemma lem1235224 {A : Type'} (_22561 : A) (a0 : A) : (term359 A _22561 a0) = (term359 A _22561 a0).
Proof. exact (eq_refl (term359 A _22561 a0)). Qed.
Lemma lem1235225 {A : Type'} (a0 : A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term336 A a0 a1 R _22561 _22562) = (term409 A a0 R _22561 _22562 a1).
Proof. exact (MK_COMB (@lem1235224 A _22561 a0) (@lem1235218 A R _22561 _22562 a1)). Qed.
Lemma lem1235236 {A : Type'} (R' : type1402 A) (_22561 : A) (_22562 : A) : (term377 A R' _22561 _22562) = (term377 A R' _22561 _22562).
Proof. exact (eq_refl (term377 A R' _22561 _22562)). Qed.
Lemma lem1235237 {A : Type'} (R' : type1402 A) (a0 : A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : (term410 A R' a0 a1 R _22561 _22562) = (term406 A R' a0 R _22561 _22562 a1).
Proof. exact (MK_COMB (@lem1235236 A R' _22561 _22562) (@lem1235225 A a0 R _22561 _22562 a1)). Qed.
Lemma lem1235248 {A : Type'} (R' : type1402 A) (a0 : A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : ((term360 A a0 a1 R R' _22561 _22562) = (term410 A R' a0 a1 R _22561 _22562)) = ((term406 A R' a0 R _22561 _22562 a1) = (term406 A R' a0 R _22561 _22562 a1)).
Proof. exact (MK_COMB (@lem1235191 A R' a0 R _22561 _22562 a1) (@lem1235237 A R' a0 R _22561 _22562 a1)). Qed.
Lemma lem1235250 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1235251 (x : Prop) : (x = x) = True.
Proof. exact (@lem1235250 Prop x). Qed.
Lemma lem1235252 {A : Type'} (R' : type1402 A) (a0 : A) (R : type1402 A) (_22561 : A) (_22562 : A) (a1 : list A) : ((term406 A R' a0 R _22561 _22562 a1) = (term406 A R' a0 R _22561 _22562 a1)) = True.
Proof. exact (@lem1235251 (term406 A R' a0 R _22561 _22562 a1)). Qed.
Lemma lem1235253 {A : Type'} (R' : type1402 A) (a0 : A) (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : ((term360 A a0 a1 R R' _22561 _22562) = (term410 A R' a0 a1 R _22561 _22562)) = True.
Proof. exact (TRANS (@lem1235248 A R' a0 R _22561 _22562 a1) (@lem1235252 A R' a0 R _22561 _22562 a1)). Qed.
Lemma lem1235254 {A : Type'} (R' : type1402 A) (a0 : A) (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : True = ((term360 A a0 a1 R R' _22561 _22562) = (term410 A R' a0 a1 R _22561 _22562)).
Proof. exact (SYM (@lem1235253 A R' a0 a1 R _22561 _22562)). Qed.
Lemma lem1235255 {A : Type'} (R' : type1402 A) (a0 : A) (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term360 A a0 a1 R R' _22561 _22562) = (term410 A R' a0 a1 R _22561 _22562).
Proof. exact (EQ_MP (@lem1235254 A R' a0 a1 R _22561 _22562) (@lem0)). Qed.
Lemma lem1235256 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term410 A R' a0 a1 R _22561 _22562.
Proof. exact (EQ_MP (@lem1235255 A R' a0 a1 R _22561 _22562) (@lem1233889 A _22561 _22562 a0 a1 R R' h1)). Qed.
Lemma lem1235258 (b : Prop) (a : Prop) : (a \/ b) = (term382 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1235259 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term410 A R' a0 a1 R _22561 _22562) = (term411 A a0 a1 R R' _22561 _22562).
Proof. exact (@lem1235258 (term336 A a0 a1 R _22561 _22562) (term286 A R' _22561 _22562)). Qed.
Lemma lem1235261 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1235262 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term412 A a0 a1 R _22561 _22562) = (term413 A a0 a1 R _22561 _22562).
Proof. exact (@lem1235261 (term318 A _22561 a0) (term323 A a1 R _22561 _22562)). Qed.
Lemma lem1235264 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1235265 {A : Type'} (_22561 : A) (a0 : A) : (term414 A _22561 a0) = (_22561 = a0).
Proof. exact (@lem1235264 (_22561 = a0)). Qed.
Lemma lem1235266 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1235267 {A : Type'} (_22561 : A) (a0 : A) : (term415 A _22561 a0) = (term416 A _22561 a0).
Proof. exact (MK_COMB (@lem1235266) (@lem1235265 A _22561 a0)). Qed.
Lemma lem1235269 (a : Prop) (b : Prop) : (term384 a b) = (term385 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem1235270 {A : Type'} (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term390 A a1 R _22561 _22562) = (term391 A a1 R _22561 _22562).
Proof. exact (@lem1235269 (term319 A _22562 a1) (term287 A R _22561 _22562)). Qed.
Lemma lem1235272 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1235273 {A : Type'} (_22562 : A) (a1 : list A) : (term388 A _22562 a1) = (@List.In A _22562 a1).
Proof. exact (@lem1235272 (@List.In A _22562 a1)). Qed.
Lemma lem1235274 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1235275 {A : Type'} (_22562 : A) (a1 : list A) : (term389 A _22562 a1) = (term304 A _22562 a1).
Proof. exact (MK_COMB (@lem1235274) (@lem1235273 A _22562 a1)). Qed.
Lemma lem1235277 (a : Prop) : (term119 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1235278 {A : Type'} (R : type1402 A) (_22561 : A) (_22562 : A) : (term392 A R _22561 _22562) = (term286 A R _22561 _22562).
Proof. exact (@lem1235277 (term286 A R _22561 _22562)). Qed.
Lemma lem1235279 {A : Type'} (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term391 A a1 R _22561 _22562) = (term309 A a1 R _22561 _22562).
Proof. exact (MK_COMB (@lem1235275 A _22562 a1) (@lem1235278 A R _22561 _22562)). Qed.
Lemma lem1235280 {A : Type'} (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term390 A a1 R _22561 _22562) = (term309 A a1 R _22561 _22562).
Proof. exact (TRANS (@lem1235270 A a1 R _22561 _22562) (@lem1235279 A a1 R _22561 _22562)). Qed.
Lemma lem1235281 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term413 A a0 a1 R _22561 _22562) = (term417 A a0 a1 R _22561 _22562).
Proof. exact (MK_COMB (@lem1235267 A _22561 a0) (@lem1235280 A a1 R _22561 _22562)). Qed.
Lemma lem1235282 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term412 A a0 a1 R _22561 _22562) = (term417 A a0 a1 R _22561 _22562).
Proof. exact (TRANS (@lem1235262 A a0 a1 R _22561 _22562) (@lem1235281 A a0 a1 R _22561 _22562)). Qed.
Lemma lem1235283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1235284 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (_22561 : A) (_22562 : A) : (term418 A a0 a1 R _22561 _22562) = (term419 A a0 a1 R _22561 _22562).
Proof. exact (MK_COMB (@lem1235283) (@lem1235282 A a0 a1 R _22561 _22562)). Qed.
Lemma lem1235285 {A : Type'} (R' : type1402 A) (_22561 : A) (_22562 : A) : (term286 A R' _22561 _22562) = (term286 A R' _22561 _22562).
Proof. exact (eq_refl (term286 A R' _22561 _22562)). Qed.
Lemma lem1235286 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term411 A a0 a1 R R' _22561 _22562) = (term420 A a0 a1 R R' _22561 _22562).
Proof. exact (MK_COMB (@lem1235284 A a0 a1 R _22561 _22562) (@lem1235285 A R' _22561 _22562)). Qed.
Lemma lem1235287 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (_22561 : A) (_22562 : A) : (term410 A R' a0 a1 R _22561 _22562) = (term420 A a0 a1 R R' _22561 _22562).
Proof. exact (TRANS (@lem1235259 A a0 a1 R R' _22561 _22562) (@lem1235286 A a0 a1 R R' _22561 _22562)). Qed.
Lemma lem1235289 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term309 A a1 R a0 x.
Proof. exact (conj (@lem1235031 A a1 R' a0 x h2) (@lem1235091 A R a1 R' a0 x h1 h2)). Qed.
Lemma lem1235290 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term421 A a1 R a0 x.
Proof. exact (conj (@lem1235024 A a0) (@lem1235289 A R a1 R' a0 x h1 h2)). Qed.
Lemma lem1235292 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term420 A a0 a1 R R' _22561 _22562.
Proof. exact (EQ_MP (@lem1235287 A a0 a1 R R' _22561 _22562) (@lem1235256 A _22561 _22562 a0 a1 R R' h1)). Qed.
Lemma lem1235293 {A : Type'} (_22561 : A) (_22562 : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term420 A a0 a1 R R' _22561 _22562.
Proof. exact (@lem1235292 A _22561 _22562 a0 a1 R R' h1). Qed.
Lemma lem1235294 {A : Type'} (x : A) (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term102 A a0 a1 R R') : term422 A a1 R R' a0 x.
Proof. exact (@lem1235293 A a0 x a0 a1 R R' h1). Qed.
Lemma lem1235297 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term286 A R' a0 x.
Proof. exact (@lem1235294 A x a0 a1 R R' h1 (@lem1235290 A R a1 R' a0 x h1 h2)). Qed.
Lemma lem1235298 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term366 A R' a0 x.
Proof. exact (fun h0 : term287 A R' a0 x => @lem1235297 A R a1 R' a0 x h1 h2). Qed.
Lemma lem1235300 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235301 {A : Type'} (R' : type1402 A) (a0 : A) (x : A) : (term366 A R' a0 x) = (term286 A R' a0 x).
Proof. exact (@lem1235300 (term286 A R' a0 x)). Qed.
Lemma lem1235302 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term286 A R' a0 x.
Proof. exact (EQ_MP (@lem1235301 A R' a0 x) (@lem1235298 A R a1 R' a0 x h1 h2)). Qed.
Lemma lem1235305 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1235307 {A : Type'} (R' : type1402 A) (a0 : A) (x : A) : (term287 A R' a0 x) = (term396 A R' a0 x).
Proof. exact (@lem1235305 (term286 A R' a0 x)). Qed.
Lemma lem1235310 {A : Type'} (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term305 A a1 R' a0 x) : term396 A R' a0 x.
Proof. exact (EQ_MP (@lem1235307 A R' a0 x) (@lem1233871 A a1 R' a0 x h1)). Qed.
Lemma lem1235313 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : False.
Proof. exact (@lem1235310 A a1 R' a0 x h2 (@lem1235302 A R a1 R' a0 x h1 h2)). Qed.
Lemma lem1235314 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : term364.
Proof. exact (fun h0 : ~ False => @lem1235313 A R a1 R' a0 x h1 h2). Qed.
Lemma lem1235316 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235317 : term364 = False.
Proof. exact (@lem1235316 False). Qed.
Lemma lem1235318 {A : Type'} (R : type1402 A) (a1 : list A) (R' : type1402 A) (a0 : A) (x : A) (h1 : term102 A a0 a1 R R') (h2 : term305 A a1 R' a0 x) : False.
Proof. exact (EQ_MP (@lem1235317) (@lem1235314 A R a1 R' a0 x h1 h2)). Qed.
Lemma lem1235400 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : @List.ForallOrdPairs A R' a1) : @List.ForallOrdPairs A R' a1.
Proof. exact (h1). Qed.
Lemma lem1235401 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : @List.ForallOrdPairs A R' a1) : term361 A R' a1.
Proof. exact (fun h0 : term171 A R' a1 => @lem1235400 A R' a1 h1). Qed.
Lemma lem1235403 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235404 {A : Type'} (R' : type1402 A) (a1 : list A) : (term361 A R' a1) = (@List.ForallOrdPairs A R' a1).
Proof. exact (@lem1235403 (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1235405 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : @List.ForallOrdPairs A R' a1) : @List.ForallOrdPairs A R' a1.
Proof. exact (EQ_MP (@lem1235404 A R' a1) (@lem1235401 A R' a1 h1)). Qed.
Lemma lem1235408 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1235410 {A : Type'} (R' : type1402 A) (a1 : list A) : (term171 A R' a1) = (term363 A R' a1).
Proof. exact (@lem1235408 (@List.ForallOrdPairs A R' a1)). Qed.
Lemma lem1235413 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) : term363 A R' a1.
Proof. exact (EQ_MP (@lem1235410 A R' a1) (@lem1233955 A R' a1 h1)). Qed.
Lemma lem1235416 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (@lem1235413 A R' a1 h1 (@lem1235405 A R' a1 h2)). Qed.
Lemma lem1235417 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : term364.
Proof. exact (fun h0 : ~ False => @lem1235416 A R' a1 h1 h2). Qed.
Lemma lem1235419 (p : Prop) : (term362 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1235420 : term364 = False.
Proof. exact (@lem1235419 False). Qed.
Lemma lem1235421 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (EQ_MP (@lem1235420) (@lem1235417 A R' a1 h1 h2)). Qed.
Lemma lem1235422 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : (term171 A R' a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R' a1 => @lem1235421 A R' a1 h1 h2) (fun h3 : False => @lem1233955 A R' a1 h1)). Qed.
Lemma lem1235423 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (EQ_MP (@lem1235422 A R' a1 h1 h2) (@lem1233955 A R' a1 h1)). Qed.
Lemma lem1235424 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : (@List.ForallOrdPairs A R' a1) = False.
Proof. exact (prop_ext (fun h3 : @List.ForallOrdPairs A R' a1 => @lem1235423 A R' a1 h1 h2) (fun h3 : False => @lem1233953 A R' a1 h2)). Qed.
Lemma lem1235425 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (EQ_MP (@lem1235424 A R' a1 h1 h2) (@lem1233953 A R' a1 h2)). Qed.
Lemma lem1235426 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : (term171 A R a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R a1 => @lem1234233 A a0 a1 R R' h1 h2) (fun h3 : False => @lem1233601 A R a1 h1)). Qed.
Lemma lem1235427 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1235426 A a0 a1 R R' h1 h2) (@lem1233601 A R a1 h1)). Qed.
Lemma lem1235428 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : (term171 A R a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R a1 => @lem1234130 A a0 a1 R R' h1 h2) (fun h3 : False => @lem1233515 A R a1 h1)). Qed.
Lemma lem1235429 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1235428 A a0 a1 R R' h1 h2) (@lem1233515 A R a1 h1)). Qed.
Lemma lem1235430 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : (term171 A R' a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R' a1 => @lem1235425 A R' a1 h1 h2) (fun h3 : False => @lem1233415 A R' a1 h1)). Qed.
Lemma lem1235431 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (EQ_MP (@lem1235430 A R' a1 h1 h2) (@lem1233415 A R' a1 h1)). Qed.
Lemma lem1235432 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : (@List.ForallOrdPairs A R' a1) = False.
Proof. exact (prop_ext (fun h3 : @List.ForallOrdPairs A R' a1 => @lem1235431 A R' a1 h1 h2) (fun h3 : False => @lem1233411 A R' a1 h2)). Qed.
Lemma lem1235433 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (EQ_MP (@lem1235432 A R' a1 h1 h2) (@lem1233411 A R' a1 h2)). Qed.
Lemma lem1235434 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : (term171 A R a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R a1 => @lem1235427 A a0 a1 R R' h1 h2) (fun h3 : False => @lem1232967 A R a1 h1)). Qed.
Lemma lem1235435 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1235434 A a0 a1 R R' h1 h2) (@lem1232967 A R a1 h1)). Qed.
Lemma lem1235436 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : (term171 A R a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R a1 => @lem1235429 A a0 a1 R R' h1 h2) (fun h3 : False => @lem1232860 A R a1 h1)). Qed.
Lemma lem1235437 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1235436 A a0 a1 R R' h1 h2) (@lem1232860 A R a1 h1)). Qed.
Lemma lem1235438 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : (term171 A R' a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R' a1 => @lem1235433 A R' a1 h1 h2) (fun h3 : False => @lem1233415 A R' a1 h1)). Qed.
Lemma lem1235439 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (EQ_MP (@lem1235438 A R' a1 h1 h2) (@lem1233415 A R' a1 h1)). Qed.
Lemma lem1235440 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : (@List.ForallOrdPairs A R' a1) = False.
Proof. exact (prop_ext (fun h3 : @List.ForallOrdPairs A R' a1 => @lem1235439 A R' a1 h1 h2) (fun h3 : False => @lem1233411 A R' a1 h2)). Qed.
Lemma lem1235441 {A : Type'} (R' : type1402 A) (a1 : list A) (h1 : term171 A R' a1) (h2 : @List.ForallOrdPairs A R' a1) : False.
Proof. exact (EQ_MP (@lem1235440 A R' a1 h1 h2) (@lem1233411 A R' a1 h2)). Qed.
Lemma lem1235442 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : (term171 A R a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R a1 => @lem1235435 A a0 a1 R R' h1 h2) (fun h3 : False => @lem1232967 A R a1 h1)). Qed.
Lemma lem1235443 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1235442 A a0 a1 R R' h1 h2) (@lem1232967 A R a1 h1)). Qed.
Lemma lem1235444 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : (term171 A R a1) = False.
Proof. exact (prop_ext (fun h3 : term171 A R a1 => @lem1235437 A a0 a1 R R' h1 h2) (fun h3 : False => @lem1232860 A R a1 h1)). Qed.
Lemma lem1235445 {A : Type'} (a0 : A) (a1 : list A) (R : type1402 A) (R' : type1402 A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') : False.
Proof. exact (EQ_MP (@lem1235444 A a0 a1 R R' h1 h2) (@lem1232860 A R a1 h1)). Qed.
Lemma lem1235446 {A : Type'} (R : type1402 A) (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term102 A a0 a1 R R') (h2 : @List.ForallOrdPairs A R' a1) (h3 : term282 A a0 x R' a1) : False.
Proof. exact (or_elim (@lem1232661 A a0 x R' a1 h3) (fun h0 : term305 A a1 R' a0 x => @lem1235318 A R a1 R' a0 x h1 h0) (fun h0 : term171 A R' a1 => @lem1235441 A R' a1 h0 h2)). Qed.
Lemma lem1235447 {A : Type'} (R : type1402 A) (x' : A) (y : A) (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term102 A a0 a1 R R') (h2 : term313 A a1 R R' x' y) (h3 : term282 A a0 x R' a1) : False.
Proof. exact (or_elim (@lem1232661 A a0 x R' a1 h3) (fun h0 : term305 A a1 R' a0 x => @lem1234584 A a0 a1 R R' x' y h1 h2) (fun h0 : term171 A R' a1 => @lem1234935 A a0 a1 R R' x' y h1 h2)). Qed.
Lemma lem1235448 {A : Type'} (R : type1402 A) (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term171 A R a1) (h2 : term102 A a0 a1 R R') (h3 : term282 A a0 x R' a1) : False.
Proof. exact (or_elim (@lem1232661 A a0 x R' a1 h3) (fun h0 : term305 A a1 R' a0 x => @lem1235445 A a0 a1 R R' h1 h2) (fun h0 : term171 A R' a1 => @lem1235443 A a0 a1 R R' h1 h2)). Qed.
Lemma lem1235449 {A : Type'} (R : type1402 A) (x' : A) (y : A) (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term102 A a0 a1 R R') (h2 : term314 A a1 R R' x' y) (h3 : term282 A a0 x R' a1) : False.
Proof. exact (or_elim (@lem1232740 A a1 R R' x' y h2) (fun h0 : term171 A R a1 => @lem1235448 A R a0 x R' a1 h0 h1 h3) (fun h0 : term313 A a1 R R' x' y => @lem1235447 A R x' y a0 x R' a1 h1 h0 h3)). Qed.
Lemma lem1235450 {A : Type'} (a0 : A) (x : A) (R : type1402 A) (x' : A) (y : A) (R' : type1402 A) (a1 : list A) (h1 : term102 A a0 a1 R R') (h2 : term282 A a0 x R' a1) (h3 : term226 A R x' y R' a1) : False.
Proof. exact (or_elim (@lem1232735 A R x' y R' a1 h3) (fun h0 : term314 A a1 R R' x' y => @lem1235449 A R x' y a0 x R' a1 h1 h0 h2) (fun h0 : @List.ForallOrdPairs A R' a1 => @lem1235446 A R a0 x R' a1 h1 h0 h2)). Qed.
Lemma lem1235451 {A : Type'} (x' : A) (R : type1402 A) (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term229 A R x' R' a1) (h2 : term102 A a0 a1 R R') (h3 : term282 A a0 x R' a1) : False.
Proof. exact (ex_elim (@lem1232495 A R x' R' a1 h1) (fun y : A => fun h0 : term228 A R x' R' a1 y => @lem1235450 A a0 x R x' y R' a1 h2 h3 h0)). Qed.
Lemma lem1235452 {A : Type'} (R : type1402 A) (a0 : A) (x : A) (R' : type1402 A) (a1 : list A) (h1 : term102 A a0 a1 R R') (h2 : term32 A R R' a1) (h3 : term282 A a0 x R' a1) : False.
Proof. exact (ex_elim (@lem1232235 A R R' a1 h2) (fun x' : A => fun h0 : term230 A R R' a1 x' => @lem1235451 A x' R a0 x R' a1 h0 h1 h3)). Qed.
Lemma lem1235453 {A : Type'} (a0 : A) (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term139 A a0 R' a1) (h2 : term102 A a0 a1 R R') (h3 : term32 A R R' a1) : False.
Proof. exact (ex_elim (@lem1232493 A a0 R' a1 h1) (fun x : A => fun h0 : term284 A a0 R' a1 x => @lem1235452 A R a0 x R' a1 h2 h3 h0)). Qed.
Lemma lem1235454 {A : Type'} (a0 : A) (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term139 A a0 R' a1) (h2 : term102 A a0 a1 R R') (h3 : term32 A R R' a1) : (term139 A a0 R' a1) = False.
Proof. exact (prop_ext (fun h4 : term139 A a0 R' a1 => @lem1235453 A a0 R R' a1 h1 h2 h3) (fun h4 : False => @lem1232031 A a0 R' a1 h1)). Qed.
Lemma lem1235455 {A : Type'} (a0 : A) (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term139 A a0 R' a1) (h2 : term102 A a0 a1 R R') (h3 : term32 A R R' a1) : False.
Proof. exact (EQ_MP (@lem1235454 A a0 R R' a1 h1 h2 h3) (@lem1232031 A a0 R' a1 h1)). Qed.
Lemma lem1235456 {A : Type'} (a0 : A) (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term102 A a0 a1 R R') (h2 : term32 A R R' a1) : term138 A a0 R' a1.
Proof. exact (fun h0 : term139 A a0 R' a1 => @lem1235455 A a0 R R' a1 h0 h1 h2). Qed.
Lemma lem1235457 {A : Type'} (a0 : A) (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term102 A a0 a1 R R') (h2 : term32 A R R' a1) : term78 A a0 R' a1.
Proof. exact (EQ_MP (@lem1232030 A a0 R' a1) (@lem1235456 A a0 R R' a1 h1 h2)). Qed.
Lemma lem1235458 {A : Type'} (a0 : A) (R : type1402 A) (R' : type1402 A) (a1 : list A) (h1 : term32 A R R' a1) : term105 A R a0 R' a1.
Proof. exact (fun h0 : term102 A a0 a1 R R' => @lem1235457 A a0 R R' a1 h0 h1). Qed.
Lemma lem1235459 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) (a1 : list A) : term106 A R a0 R' a1.
Proof. exact (fun h0 : term32 A R R' a1 => @lem1235458 A a0 R R' a1 h0). Qed.
Lemma lem1235464 {A : Type'} (R : type1402 A) (a0 : A) (R' : type1402 A) : term108 A R a0 R'.
Proof. exact (fun a1 : list A => @lem1235459 A R a0 R' a1). Qed.
Lemma lem1235469 {A : Type'} (R : type1402 A) (R' : type1402 A) : term110 A R R'.
Proof. exact (fun a0 : A => @lem1235464 A R a0 R'). Qed.
Lemma lem1235474 {A : Type'} (R' : type1402 A) : term123 A R'.
Proof. exact (fun R : type1402 A => @lem1235469 A R R'). Qed.
Lemma lem1235479 {A : Type'} : term127 A.
Proof. exact (fun R' : type1402 A => @lem1235474 A R'). Qed.
Lemma lem1235480 {A : Type'} : term126 A.
Proof. exact (EQ_MP (@lem1232024 A) (@lem1235479 A)). Qed.
Lemma lem1235481 {A : Type'} (R' : type1402 A) : term423 A R'.
Proof. exact (@lem1235480 A R'). Qed.
Lemma lem1235482 {A : Type'} (R' : type1402 A) : (term423 A R') = (term122 A R').
Proof. exact (eq_refl (term423 A R')). Qed.
Lemma lem1235483 {A : Type'} (R' : type1402 A) : term122 A R'.
Proof. exact (EQ_MP (@lem1235482 A R') (@lem1235481 A R')). Qed.
Lemma lem1235484 {A : Type'} (R' : type1402 A) (R : type1402 A) : term424 A R' R.
Proof. exact (@lem1235483 A R' R). Qed.
Lemma lem1235485 {A : Type'} (R : type1402 A) (R' : type1402 A) : (term424 A R' R) = (term113 A R R').
Proof. exact (eq_refl (term424 A R' R)). Qed.
Lemma lem1235486 {A : Type'} (R : type1402 A) (R' : type1402 A) : term113 A R R'.
Proof. exact (EQ_MP (@lem1235485 A R R') (@lem1235484 A R' R)). Qed.
Lemma lem1235488 {A : Type'} (R : type1402 A) (R' : type1402 A) : term113 A R R'.
Proof. exact (@lem1231728 A R R' (@lem1235486 A R R')). Qed.
Lemma lem1235489 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term114 A R R') : False.
Proof. exact (@lem1235488 A R R' (@lem1231712 A R R' h1)). Qed.
Lemma lem1235490 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term114 A R R') : (term114 A R R') = False.
Proof. exact (prop_ext (fun h2 : term114 A R R' => @lem1235489 A R R' h1) (fun h2 : False => @lem1231712 A R R' h1)). Qed.
Lemma lem1235491 {A : Type'} (R : type1402 A) (R' : type1402 A) (h1 : term114 A R R') : False.
Proof. exact (EQ_MP (@lem1235490 A R R' h1) (@lem1231712 A R R' h1)). Qed.
Lemma lem1235492 {A : Type'} (R : type1402 A) (R' : type1402 A) : term113 A R R'.
Proof. exact (fun h0 : term114 A R R' => @lem1235491 A R R' h0). Qed.
Lemma lem1235493 {A : Type'} (R : type1402 A) (R' : type1402 A) : term110 A R R'.
Proof. exact (EQ_MP (@lem1231711 A R R') (@lem1235492 A R R')). Qed.
Lemma lem1235494 {A : Type'} (R : type1402 A) (R' : type1402 A) : term48 A R R'.
Proof. exact (EQ_MP (@lem1231707 A R R') (@lem1235493 A R R')). Qed.
Lemma lem1235495 {A : Type'} (R : type1402 A) (R' : type1402 A) : term53 A R R'.
Proof. exact (@lem1231374 A R R' (@lem1235494 A R R')). Qed.
Lemma lem1235500 {A : Type'} (R : type1402 A) : term425 A R.
Proof. exact (fun R' : type1402 A => @lem1235495 A R R'). Qed.
Lemma lem1235505 {A : Type'} : term426 A.
Proof. exact (fun R : type1402 A => @lem1235500 A R). Qed.
