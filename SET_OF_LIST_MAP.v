Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import SET_OF_LIST_MAP_term_abbrevs.
Require Import IMAGE_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1097797_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Lemma lem4790290 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem4790291 {_110433 : Type'} (P : type1143 _110433) : term0 _110433 P.
Proof. exact (@lem4790290 _110433 P). Qed.
Lemma lem4790292 {_110431 _110433 : Type'} (f : _110433 -> _110431) : term1 _110431 _110433 f.
Proof. exact (@lem4790291 _110433 (term2 _110431 _110433 f)). Qed.
Lemma lem4790293 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term3 _110431 _110433 f) = ((term4 _110431 _110433 f) = (term5 _110431 _110433 f)).
Proof. exact (eq_refl (term3 _110431 _110433 f)). Qed.
Lemma lem4790294 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4790295 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term6 _110431 _110433 f) = (term7 _110431 _110433 f).
Proof. exact (MK_COMB (@lem4790294) (@lem4790293 _110431 _110433 f)). Qed.
Lemma lem4790296 {_110431 _110433 : Type'} (f : _110433 -> _110431) (t : list _110433) : (term8 _110431 _110433 f t) = ((term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)).
Proof. exact (eq_refl (term8 _110431 _110433 f t)). Qed.
Lemma lem4790297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4790298 {_110431 _110433 : Type'} (f : _110433 -> _110431) (t : list _110433) : (term11 _110431 _110433 f t) = (term12 _110431 _110433 f t).
Proof. exact (MK_COMB (@lem4790297) (@lem4790296 _110431 _110433 f t)). Qed.
Lemma lem4790299 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) (t : list _110433) : (term13 _110431 _110433 f h t) = ((term14 _110431 _110433 f h t) = (term15 _110431 _110433 f h t)).
Proof. exact (eq_refl (term13 _110431 _110433 f h t)). Qed.
Lemma lem4790300 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) (t : list _110433) : (term16 _110431 _110433 f h t) = (term17 _110431 _110433 f h t).
Proof. exact (MK_COMB (@lem4790298 _110431 _110433 f t) (@lem4790299 _110431 _110433 f h t)). Qed.
Lemma lem4790301 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) : (term18 _110431 _110433 f h) = (term19 _110431 _110433 f h).
Proof. exact (fun_ext (fun t : list _110433 => @lem4790300 _110431 _110433 f h t)). Qed.
Lemma lem4790302 {_110433 : Type'} : (@all (list _110433)) = (@all (list _110433)).
Proof. exact (eq_refl (@all (list _110433))). Qed.
Lemma lem4790303 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) : (term20 _110431 _110433 f h) = (term21 _110431 _110433 f h).
Proof. exact (MK_COMB (@lem4790302 _110433) (@lem4790301 _110431 _110433 f h)). Qed.
Lemma lem4790304 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term22 _110431 _110433 f) = (term23 _110431 _110433 f).
Proof. exact (fun_ext (fun h : _110433 => @lem4790303 _110431 _110433 f h)). Qed.
Lemma lem4790305 {_110433 : Type'} : (@all _110433) = (@all _110433).
Proof. exact (eq_refl (@all _110433)). Qed.
Lemma lem4790306 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term24 _110431 _110433 f) = (term25 _110431 _110433 f).
Proof. exact (MK_COMB (@lem4790305 _110433) (@lem4790304 _110431 _110433 f)). Qed.
Lemma lem4790307 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term26 _110431 _110433 f) = (term27 _110431 _110433 f).
Proof. exact (MK_COMB (@lem4790295 _110431 _110433 f) (@lem4790306 _110431 _110433 f)). Qed.
Lemma lem4790308 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4790309 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term28 _110431 _110433 f) = (term29 _110431 _110433 f).
Proof. exact (MK_COMB (@lem4790308) (@lem4790307 _110431 _110433 f)). Qed.
Lemma lem4790310 {_110431 _110433 : Type'} (f : _110433 -> _110431) (l : list _110433) : (term8 _110431 _110433 f l) = ((term9 _110431 _110433 f l) = (term10 _110431 _110433 f l)).
Proof. exact (eq_refl (term8 _110431 _110433 f l)). Qed.
Lemma lem4790311 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term30 _110431 _110433 f) = (term2 _110431 _110433 f).
Proof. exact (fun_ext (fun l : list _110433 => @lem4790310 _110431 _110433 f l)). Qed.
Lemma lem4790312 {_110433 : Type'} : (@all (list _110433)) = (@all (list _110433)).
Proof. exact (eq_refl (@all (list _110433))). Qed.
Lemma lem4790313 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term31 _110431 _110433 f) = (term32 _110431 _110433 f).
Proof. exact (MK_COMB (@lem4790312 _110433) (@lem4790311 _110431 _110433 f)). Qed.
Lemma lem4790314 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term1 _110431 _110433 f) = (term33 _110431 _110433 f).
Proof. exact (MK_COMB (@lem4790309 _110431 _110433 f) (@lem4790313 _110431 _110433 f)). Qed.
Lemma lem4790315 {_110431 _110433 : Type'} (f : _110433 -> _110431) : term33 _110431 _110433 f.
Proof. exact (EQ_MP (@lem4790314 _110431 _110433 f) (@lem4790292 _110431 _110433 f)). Qed.
Lemma lem4790329 {A B : Type'} : term34 A B.
Proof. exact (proj1 (@lem1097797 A B)). Qed.
Lemma lem4790330 {A B : Type'} (f : A -> B) : term35 A B f.
Proof. exact (@lem4790329 A B f). Qed.
Lemma lem4790331 {A B : Type'} (f : A -> B) : (term35 A B f) = ((@List.map A B f (@nil A)) = (@nil B)).
Proof. exact (eq_refl (term35 A B f)). Qed.
Lemma lem4790338 {A B : Type'} (f : A -> B) : (@List.map A B f (@nil A)) = (@nil B).
Proof. exact (EQ_MP (@lem4790331 A B f) (@lem4790330 A B f)). Qed.
Lemma lem4790339 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (@List.map _110433 _110431 f (@nil _110433)) = (@nil _110431).
Proof. exact (@lem4790338 _110433 _110431 f). Qed.
Lemma lem4790340 {_110431 : Type'} : (@set_of_list _110431) = (@set_of_list _110431).
Proof. exact (eq_refl (@set_of_list _110431)). Qed.
Lemma lem4790341 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term4 _110431 _110433 f) = (@set_of_list _110431 (@nil _110431)).
Proof. exact (MK_COMB (@lem4790340 _110431) (@lem4790339 _110431 _110433 f)). Qed.
Lemma lem4790343 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4790344 {_110431 : Type'} : (@set_of_list _110431 (@nil _110431)) = (@EMPTY _110431).
Proof. exact (@lem4790343 _110431). Qed.
Lemma lem4790345 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term4 _110431 _110433 f) = (@EMPTY _110431).
Proof. exact (TRANS (@lem4790341 _110431 _110433 f) (@lem4790344 _110431)). Qed.
Lemma lem4790346 {_110431 : Type'} : (@eq (_110431 -> Prop)) = (@eq (_110431 -> Prop)).
Proof. exact (eq_refl (@eq (_110431 -> Prop))). Qed.
Lemma lem4790347 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term36 _110431 _110433 f) = (@eq (_110431 -> Prop) (@EMPTY _110431)).
Proof. exact (MK_COMB (@lem4790346 _110431) (@lem4790345 _110431 _110433 f)). Qed.
Lemma lem4790349 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4790350 {_110433 : Type'} : (@set_of_list _110433 (@nil _110433)) = (@EMPTY _110433).
Proof. exact (@lem4790349 _110433). Qed.
Lemma lem4790351 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (@IMAGE _110433 _110431 f) = (@IMAGE _110433 _110431 f).
Proof. exact (eq_refl (@IMAGE _110433 _110431 f)). Qed.
Lemma lem4790352 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term5 _110431 _110433 f) = (@IMAGE _110433 _110431 f (@EMPTY _110433)).
Proof. exact (MK_COMB (@lem4790351 _110431 _110433 f) (@lem4790350 _110433)). Qed.
Lemma lem4790354 {_87477 _87481 : Type'} (f : _87477 -> _87481) : (@IMAGE _87477 _87481 f (@EMPTY _87477)) = (@EMPTY _87481).
Proof. exact (proj1 (@lem3366870 _87477 _87481 (@el _87477) f (@el (_87477 -> Prop)))). Qed.
Lemma lem4790355 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (@IMAGE _110433 _110431 f (@EMPTY _110433)) = (@EMPTY _110431).
Proof. exact (@lem4790354 _110433 _110431 f). Qed.
Lemma lem4790356 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term5 _110431 _110433 f) = (@EMPTY _110431).
Proof. exact (TRANS (@lem4790352 _110431 _110433 f) (@lem4790355 _110431 _110433 f)). Qed.
Lemma lem4790357 {_110431 _110433 : Type'} (f : _110433 -> _110431) : ((term4 _110431 _110433 f) = (term5 _110431 _110433 f)) = ((@EMPTY _110431) = (@EMPTY _110431)).
Proof. exact (MK_COMB (@lem4790347 _110431 _110433 f) (@lem4790356 _110431 _110433 f)). Qed.
Lemma lem4790359 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4790360 {_110431 : Type'} (x : _110431 -> Prop) : (x = x) = True.
Proof. exact (@lem4790359 (_110431 -> Prop) x). Qed.
Lemma lem4790361 {_110431 : Type'} : ((@EMPTY _110431) = (@EMPTY _110431)) = True.
Proof. exact (@lem4790360 _110431 (@EMPTY _110431)). Qed.
Lemma lem4790362 {_110431 _110433 : Type'} (f : _110433 -> _110431) : ((term4 _110431 _110433 f) = (term5 _110431 _110433 f)) = True.
Proof. exact (TRANS (@lem4790357 _110431 _110433 f) (@lem4790361 _110431)). Qed.
Lemma lem4790363 {_110431 _110433 : Type'} (f : _110433 -> _110431) : True = ((term4 _110431 _110433 f) = (term5 _110431 _110433 f)).
Proof. exact (SYM (@lem4790362 _110431 _110433 f)). Qed.
Lemma lem4790364 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (term4 _110431 _110433 f) = (term5 _110431 _110433 f).
Proof. exact (EQ_MP (@lem4790363 _110431 _110433 f) (@lem0)). Qed.
Lemma lem4790367 {A B : Type'} : term37 A B.
Proof. exact (proj2 (@lem1097797 A B)). Qed.
Lemma lem4790368 {A B : Type'} (f : A -> B) : term38 A B f.
Proof. exact (@lem4790367 A B f). Qed.
Lemma lem4790369 {A B : Type'} (f : A -> B) : (term38 A B f) = (term39 A B f).
Proof. exact (eq_refl (term38 A B f)). Qed.
Lemma lem4790370 {A B : Type'} (f : A -> B) : term39 A B f.
Proof. exact (EQ_MP (@lem4790369 A B f) (@lem4790368 A B f)). Qed.
Lemma lem4790371 {A B : Type'} (f : A -> B) (h : A) : term40 A B f h.
Proof. exact (@lem4790370 A B f h). Qed.
Lemma lem4790372 {A B : Type'} (h : A) (f : A -> B) : (term40 A B f h) = (term41 A B h f).
Proof. exact (eq_refl (term40 A B f h)). Qed.
Lemma lem4790373 {A B : Type'} (h : A) (f : A -> B) : term41 A B h f.
Proof. exact (EQ_MP (@lem4790372 A B h f) (@lem4790371 A B f h)). Qed.
Lemma lem4790374 {A B : Type'} (h : A) (f : A -> B) (t : list A) : term42 A B h f t.
Proof. exact (@lem4790373 A B h f t). Qed.
Lemma lem4790375 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term42 A B h f t) = ((term43 A B f h t) = (term44 A B h f t)).
Proof. exact (eq_refl (term42 A B h f t)). Qed.
Lemma lem4790386 {A B : Type'} (h : A) (f : A -> B) (t : list A) : (term43 A B f h t) = (term44 A B h f t).
Proof. exact (EQ_MP (@lem4790375 A B h f t) (@lem4790374 A B h f t)). Qed.
Lemma lem4790387 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) : (term45 _110431 _110433 f h t) = (term46 _110431 _110433 h f t).
Proof. exact (@lem4790386 _110433 _110431 h f t). Qed.
Lemma lem4790388 {_110431 : Type'} : (@set_of_list _110431) = (@set_of_list _110431).
Proof. exact (eq_refl (@set_of_list _110431)). Qed.
Lemma lem4790389 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) : (term14 _110431 _110433 f h t) = (term47 _110431 _110433 h f t).
Proof. exact (MK_COMB (@lem4790388 _110431) (@lem4790387 _110431 _110433 h f t)). Qed.
Lemma lem4790391 {A : Type'} (h : A) (t : list A) : (term48 A h t) = (term49 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4790392 {_110431 : Type'} (h : _110431) (t : list _110431) : (term48 _110431 h t) = (term49 _110431 h t).
Proof. exact (@lem4790391 _110431 h t). Qed.
Lemma lem4790393 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) : (term47 _110431 _110433 h f t) = (term50 _110431 _110433 h f t).
Proof. exact (@lem4790392 _110431 (f h) (@List.map _110433 _110431 f t)). Qed.
Lemma lem4790395 {_110431 _110433 : Type'} (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t).
Proof. exact (h1). Qed.
Lemma lem4790396 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) : (term51 _110431 _110433 f h) = (term51 _110431 _110433 f h).
Proof. exact (eq_refl (term51 _110431 _110433 f h)). Qed.
Lemma lem4790397 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : (term50 _110431 _110433 h f t) = (term52 _110431 _110433 h f t).
Proof. exact (MK_COMB (@lem4790396 _110431 _110433 f h) (@lem4790395 _110431 _110433 f t h1)). Qed.
Lemma lem4790398 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : (term47 _110431 _110433 h f t) = (term52 _110431 _110433 h f t).
Proof. exact (TRANS (@lem4790393 _110431 _110433 h f t) (@lem4790397 _110431 _110433 h f t h1)). Qed.
Lemma lem4790399 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : (term14 _110431 _110433 f h t) = (term52 _110431 _110433 h f t).
Proof. exact (TRANS (@lem4790389 _110431 _110433 h f t) (@lem4790398 _110431 _110433 h f t h1)). Qed.
Lemma lem4790400 {_110431 : Type'} : (@eq (_110431 -> Prop)) = (@eq (_110431 -> Prop)).
Proof. exact (eq_refl (@eq (_110431 -> Prop))). Qed.
Lemma lem4790401 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : (term53 _110431 _110433 f h t) = (term54 _110431 _110433 h f t).
Proof. exact (MK_COMB (@lem4790400 _110431) (@lem4790399 _110431 _110433 h f t h1)). Qed.
Lemma lem4790403 {A : Type'} (h : A) (t : list A) : (term48 A h t) = (term49 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4790404 {_110433 : Type'} (h : _110433) (t : list _110433) : (term48 _110433 h t) = (term49 _110433 h t).
Proof. exact (@lem4790403 _110433 h t). Qed.
Lemma lem4790405 {_110431 _110433 : Type'} (f : _110433 -> _110431) : (@IMAGE _110433 _110431 f) = (@IMAGE _110433 _110431 f).
Proof. exact (eq_refl (@IMAGE _110433 _110431 f)). Qed.
Lemma lem4790406 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) (t : list _110433) : (term15 _110431 _110433 f h t) = (term55 _110431 _110433 f h t).
Proof. exact (MK_COMB (@lem4790405 _110431 _110433 f) (@lem4790404 _110433 h t)). Qed.
Lemma lem4790408 {_87477 _87481 : Type'} (x : _87477) (f : _87477 -> _87481) (s : _87477 -> Prop) : (term56 _87477 _87481 f x s) = (term57 _87477 _87481 x f s).
Proof. exact (proj2 (@lem3366870 _87477 _87481 x f s)). Qed.
Lemma lem4790409 {_110431 _110433 : Type'} (x : _110433) (f : _110433 -> _110431) (s : _110433 -> Prop) : (term58 _110431 _110433 f x s) = (term59 _110431 _110433 x f s).
Proof. exact (@lem4790408 _110433 _110431 x f s). Qed.
Lemma lem4790410 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) : (term55 _110431 _110433 f h t) = (term52 _110431 _110433 h f t).
Proof. exact (@lem4790409 _110431 _110433 h f (@set_of_list _110433 t)). Qed.
Lemma lem4790411 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) : (term15 _110431 _110433 f h t) = (term52 _110431 _110433 h f t).
Proof. exact (TRANS (@lem4790406 _110431 _110433 f h t) (@lem4790410 _110431 _110433 h f t)). Qed.
Lemma lem4790412 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : ((term14 _110431 _110433 f h t) = (term15 _110431 _110433 f h t)) = ((term52 _110431 _110433 h f t) = (term52 _110431 _110433 h f t)).
Proof. exact (MK_COMB (@lem4790401 _110431 _110433 h f t h1) (@lem4790411 _110431 _110433 h f t)). Qed.
Lemma lem4790414 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4790415 {_110431 : Type'} (x : _110431 -> Prop) : (x = x) = True.
Proof. exact (@lem4790414 (_110431 -> Prop) x). Qed.
Lemma lem4790416 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) : ((term52 _110431 _110433 h f t) = (term52 _110431 _110433 h f t)) = True.
Proof. exact (@lem4790415 _110431 (term52 _110431 _110433 h f t)). Qed.
Lemma lem4790417 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : ((term14 _110431 _110433 f h t) = (term15 _110431 _110433 f h t)) = True.
Proof. exact (TRANS (@lem4790412 _110431 _110433 h f t h1) (@lem4790416 _110431 _110433 h f t)). Qed.
Lemma lem4790418 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : True = ((term14 _110431 _110433 f h t) = (term15 _110431 _110433 f h t)).
Proof. exact (SYM (@lem4790417 _110431 _110433 h f t h1)). Qed.
Lemma lem4790419 {_110431 _110433 : Type'} (h : _110433) (f : _110433 -> _110431) (t : list _110433) (h1 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t)) : (term14 _110431 _110433 f h t) = (term15 _110431 _110433 f h t).
Proof. exact (EQ_MP (@lem4790418 _110431 _110433 h f t h1) (@lem0)). Qed.
Lemma lem4790420 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) (t : list _110433) : term17 _110431 _110433 f h t.
Proof. exact (fun h0 : (term9 _110431 _110433 f t) = (term10 _110431 _110433 f t) => @lem4790419 _110431 _110433 h f t h0). Qed.
Lemma lem4790425 {_110431 _110433 : Type'} (f : _110433 -> _110431) (h : _110433) : term21 _110431 _110433 f h.
Proof. exact (fun t : list _110433 => @lem4790420 _110431 _110433 f h t). Qed.
Lemma lem4790430 {_110431 _110433 : Type'} (f : _110433 -> _110431) : term25 _110431 _110433 f.
Proof. exact (fun h : _110433 => @lem4790425 _110431 _110433 f h). Qed.
Lemma lem4790431 {_110431 _110433 : Type'} (f : _110433 -> _110431) : term27 _110431 _110433 f.
Proof. exact (conj (@lem4790364 _110431 _110433 f) (@lem4790430 _110431 _110433 f)). Qed.
Lemma lem4790432 {_110431 _110433 : Type'} (f : _110433 -> _110431) : term32 _110431 _110433 f.
Proof. exact (@lem4790315 _110431 _110433 f (@lem4790431 _110431 _110433 f)). Qed.
Lemma lem4790437 {_110431 _110433 : Type'} : term60 _110431 _110433.
Proof. exact (fun f : _110433 -> _110431 => @lem4790432 _110431 _110433 f). Qed.
