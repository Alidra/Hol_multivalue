Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CROSS_UNIV_term_abbrevs.
Require Import CROSS_spec.
Require Import EXTENSION_spec.
Require Import FORALL_PAIR_THM_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import IN_UNIV_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm7_spec.
Lemma lem4327266 {A : Type'} (x : A) : term0 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem4327267 {A : Type'} (x : A) : (term0 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term0 A x)). Qed.
Lemma lem4327268 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem4327267 A x) (@lem4327266 A x)). Qed.
Lemma lem4327269 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem4327271 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : term1 _5106 _5107 P.
Proof. exact (@lem49909 _5106 _5107 P). Qed.
Lemma lem4327272 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term1 _5106 _5107 P) = ((term2 _5106 _5107 P) = (term3 _5106 _5107 P)).
Proof. exact (eq_refl (term1 _5106 _5107 P)). Qed.
Lemma lem4327274 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term4 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem4327275 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term4 _88435 _88436 P) = (term5 _88435 _88436 P).
Proof. exact (eq_refl (term4 _88435 _88436 P)). Qed.
Lemma lem4327276 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term5 _88435 _88436 P.
Proof. exact (EQ_MP (@lem4327275 _88435 _88436 P) (@lem4327274 _88435 _88436 P)). Qed.
Lemma lem4327277 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term6 _88435 _88436 P a.
Proof. exact (@lem4327276 _88435 _88436 P a). Qed.
Lemma lem4327278 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term6 _88435 _88436 P a) = (term7 _88435 _88436 P a).
Proof. exact (eq_refl (term6 _88435 _88436 P a)). Qed.
Lemma lem4327279 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term7 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem4327278 _88435 _88436 P a) (@lem4327277 _88435 _88436 P a)). Qed.
Lemma lem4327280 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term8 _88435 _88436 P a b.
Proof. exact (@lem4327279 _88435 _88436 P a b). Qed.
Lemma lem4327281 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term8 _88435 _88436 P a b) = ((term9 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term8 _88435 _88436 P a b)). Qed.
Lemma lem4327283 {A : Type'} (s : A -> Prop) : term10 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4327284 {A : Type'} (s : A -> Prop) : (term10 A s) = (term11 A s).
Proof. exact (eq_refl (term10 A s)). Qed.
Lemma lem4327285 {A : Type'} (s : A -> Prop) : term11 A s.
Proof. exact (EQ_MP (@lem4327284 A s) (@lem4327283 A s)). Qed.
Lemma lem4327286 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term12 A s t.
Proof. exact (@lem4327285 A s t). Qed.
Lemma lem4327287 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term12 A s t) = ((s = t) = (term13 A s t)).
Proof. exact (eq_refl (term12 A s t)). Qed.
Lemma lem4327289 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term14 _103681 _103682 s.
Proof. exact (@lem4325236 _103681 _103682 s). Qed.
Lemma lem4327290 {_103681 _103682 : Type'} (s : _103682 -> Prop) : (term14 _103681 _103682 s) = (term15 _103681 _103682 s).
Proof. exact (eq_refl (term14 _103681 _103682 s)). Qed.
Lemma lem4327291 {_103681 _103682 : Type'} (s : _103682 -> Prop) : term15 _103681 _103682 s.
Proof. exact (EQ_MP (@lem4327290 _103681 _103682 s) (@lem4327289 _103681 _103682 s)). Qed.
Lemma lem4327292 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : term16 _103681 _103682 s t.
Proof. exact (@lem4327291 _103681 _103682 s t). Qed.
Lemma lem4327293 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (term16 _103681 _103682 s t) = ((@CROSS _103681 _103682 s t) = (term17 _103681 _103682 s t)).
Proof. exact (eq_refl (term16 _103681 _103682 s t)). Qed.
Lemma lem4327298 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term13 A s t).
Proof. exact (EQ_MP (@lem4327287 A s t) (@lem4327286 A s t)). Qed.
Lemma lem4327299 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = t) = (term18 A B s t).
Proof. exact (@lem4327298 (prod A B) s t). Qed.
Lemma lem4327300 {A B : Type'} : ((@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) = (term19 A B).
Proof. exact (@lem4327299 A B (@CROSS B A (@UNIV A) (@UNIV B)) (@UNIV (prod A B))). Qed.
Lemma lem4327306 {_5106 _5107 : Type'} (P : type1223 _5106 _5107) : (term2 _5106 _5107 P) = (term3 _5106 _5107 P).
Proof. exact (EQ_MP (@lem4327272 _5106 _5107 P) (@lem4327271 _5106 _5107 P)). Qed.
Lemma lem4327307 {A B : Type'} (P : type1210 A B) : (term20 A B P) = (term21 A B P).
Proof. exact (@lem4327306 B A P). Qed.
Lemma lem4327308 {A B : Type'} : (term22 A B) = (term23 A B).
Proof. exact (@lem4327307 A B (term24 A B)). Qed.
Lemma lem4327309 {A B : Type'} (x : prod A B) : (term25 A B x) = ((term26 A B x) = (@IN (prod A B) x (@UNIV (prod A B)))).
Proof. exact (eq_refl (term25 A B x)). Qed.
Lemma lem4327310 {A B : Type'} : (term27 A B) = (term24 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem4327309 A B x)). Qed.
Lemma lem4327311 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4327312 {A B : Type'} : (term22 A B) = (term19 A B).
Proof. exact (MK_COMB (@lem4327311 A B) (@lem4327310 A B)). Qed.
Lemma lem4327313 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327314 {A B : Type'} : (term28 A B) = (term29 A B).
Proof. exact (MK_COMB (@lem4327313) (@lem4327312 A B)). Qed.
Lemma lem4327315 {A B : Type'} (p1 : A) (p2 : B) : (term30 A B p1 p2) = ((term31 A B p1 p2) = (term32 A B p1 p2)).
Proof. exact (eq_refl (term30 A B p1 p2)). Qed.
Lemma lem4327316 {A B : Type'} (p1 : A) : (term33 A B p1) = (term34 A B p1).
Proof. exact (fun_ext (fun p2 : B => @lem4327315 A B p1 p2)). Qed.
Lemma lem4327317 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4327318 {A B : Type'} (p1 : A) : (term35 A B p1) = (term36 A B p1).
Proof. exact (MK_COMB (@lem4327317 B) (@lem4327316 A B p1)). Qed.
Lemma lem4327319 {A B : Type'} : (term37 A B) = (term38 A B).
Proof. exact (fun_ext (fun p1 : A => @lem4327318 A B p1)). Qed.
Lemma lem4327320 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4327321 {A B : Type'} : (term23 A B) = (term39 A B).
Proof. exact (MK_COMB (@lem4327320 A) (@lem4327319 A B)). Qed.
Lemma lem4327322 {A B : Type'} : ((term22 A B) = (term23 A B)) = ((term19 A B) = (term39 A B)).
Proof. exact (MK_COMB (@lem4327314 A B) (@lem4327321 A B)). Qed.
Lemma lem4327323 {A B : Type'} : (term19 A B) = (term39 A B).
Proof. exact (EQ_MP (@lem4327322 A B) (@lem4327308 A B)). Qed.
Lemma lem4327330 {A B : Type'} : ((@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) = (term39 A B).
Proof. exact (TRANS (@lem4327300 A B) (@lem4327323 A B)). Qed.
Lemma lem4327342 {_103681 _103682 : Type'} (s : _103682 -> Prop) (t : _103681 -> Prop) : (@CROSS _103681 _103682 s t) = (term17 _103681 _103682 s t).
Proof. exact (EQ_MP (@lem4327293 _103681 _103682 s t) (@lem4327292 _103681 _103682 s t)). Qed.
Lemma lem4327343 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (@CROSS B A s t) = (term40 A B s t).
Proof. exact (@lem4327342 B A s t). Qed.
Lemma lem4327344 {A B : Type'} : (@CROSS B A (@UNIV A) (@UNIV B)) = (term41 A B).
Proof. exact (@lem4327343 A B (@UNIV A) (@UNIV B)). Qed.
Lemma lem4327356 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4327269 A x) (@lem4327268 A x)). Qed.
Lemma lem4327357 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem4327356 A x). Qed.
Lemma lem4327358 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4327359 {A : Type'} (x : A) : (term42 A x) = (and True).
Proof. exact (MK_COMB (@lem4327358) (@lem4327357 A x)). Qed.
Lemma lem4327361 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4327269 A x) (@lem4327268 A x)). Qed.
Lemma lem4327362 {B : Type'} (x : B) : (@IN B x (@UNIV B)) = True.
Proof. exact (@lem4327361 B x). Qed.
Lemma lem4327363 {B : Type'} (y : B) : (@IN B y (@UNIV B)) = True.
Proof. exact (@lem4327362 B y). Qed.
Lemma lem4327364 {A B : Type'} (x : A) (y : B) : (term43 A B x y) = (True /\ True).
Proof. exact (MK_COMB (@lem4327359 A x) (@lem4327363 B y)). Qed.
Lemma lem4327366 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4327367 : (True /\ True) = True.
Proof. exact (@lem4327366 True). Qed.
Lemma lem4327368 {A B : Type'} (x : A) (y : B) : (term43 A B x y) = True.
Proof. exact (TRANS (@lem4327364 A B x y) (@lem4327367)). Qed.
Lemma lem4327369 {A B : Type'} (GEN_PVAR_130 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_130) = (@SETSPEC (prod A B) GEN_PVAR_130).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_130)). Qed.
Lemma lem4327370 {A B : Type'} (x : A) (y : B) (GEN_PVAR_130 : prod A B) : (term44 A B GEN_PVAR_130 x y) = (@SETSPEC (prod A B) GEN_PVAR_130 True).
Proof. exact (MK_COMB (@lem4327369 A B GEN_PVAR_130) (@lem4327368 A B x y)). Qed.
Lemma lem4327371 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4327372 {A B : Type'} (GEN_PVAR_130 : prod A B) (x : A) (y : B) : (term45 A B GEN_PVAR_130 x y) = (term46 A B GEN_PVAR_130 x y).
Proof. exact (MK_COMB (@lem4327370 A B x y GEN_PVAR_130) (@lem4327371 A B x y)). Qed.
Lemma lem4327373 {A B : Type'} (GEN_PVAR_130 : prod A B) (x : A) : (term47 A B GEN_PVAR_130 x) = (term48 A B GEN_PVAR_130 x).
Proof. exact (fun_ext (fun y : B => @lem4327372 A B GEN_PVAR_130 x y)). Qed.
Lemma lem4327374 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4327375 {A B : Type'} (GEN_PVAR_130 : prod A B) (x : A) : (term49 A B GEN_PVAR_130 x) = (term50 A B GEN_PVAR_130 x).
Proof. exact (MK_COMB (@lem4327374 B) (@lem4327373 A B GEN_PVAR_130 x)). Qed.
Lemma lem4327380 {A B : Type'} (GEN_PVAR_130 : prod A B) : (term51 A B GEN_PVAR_130) = (term52 A B GEN_PVAR_130).
Proof. exact (fun_ext (fun x : A => @lem4327375 A B GEN_PVAR_130 x)). Qed.
Lemma lem4327381 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4327382 {A B : Type'} (GEN_PVAR_130 : prod A B) : (term53 A B GEN_PVAR_130) = (term54 A B GEN_PVAR_130).
Proof. exact (MK_COMB (@lem4327381 A) (@lem4327380 A B GEN_PVAR_130)). Qed.
Lemma lem4327387 {A B : Type'} : (term55 A B) = (term56 A B).
Proof. exact (fun_ext (fun GEN_PVAR_130 : prod A B => @lem4327382 A B GEN_PVAR_130)). Qed.
Lemma lem4327388 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4327389 {A B : Type'} : (term41 A B) = (term57 A B).
Proof. exact (MK_COMB (@lem4327388 A B) (@lem4327387 A B)). Qed.
Lemma lem4327390 {A B : Type'} : (@CROSS B A (@UNIV A) (@UNIV B)) = (term57 A B).
Proof. exact (TRANS (@lem4327344 A B) (@lem4327389 A B)). Qed.
Lemma lem4327391 {A B : Type'} (p1 : A) (p2 : B) : (term58 A B p1 p2) = (term58 A B p1 p2).
Proof. exact (eq_refl (term58 A B p1 p2)). Qed.
Lemma lem4327392 {A B : Type'} (p1 : A) (p2 : B) : (term31 A B p1 p2) = (term59 A B p1 p2).
Proof. exact (MK_COMB (@lem4327391 A B p1 p2) (@lem4327390 A B)). Qed.
Lemma lem4327394 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term9 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem4327281 _88435 _88436 P a b) (@lem4327280 _88435 _88436 P a b)). Qed.
Lemma lem4327395 {A B : Type'} (P : type1413 A B) (a : A) (b : B) : (term60 A B a b P) = (P a b).
Proof. exact (@lem4327394 B A P a b). Qed.
Lemma lem4327396 {A B : Type'} (p1 : A) (p2 : B) : (term61 A B p1 p2) = (term62 A B p1 p2).
Proof. exact (@lem4327395 A B (term63 A B) p1 p2). Qed.
Lemma lem4327397 {A B : Type'} (x : A) : (term64 A B x) = (term65 B).
Proof. exact (eq_refl (term64 A B x)). Qed.
Lemma lem4327398 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4327399 {A B : Type'} (x : A) (y : B) : (term62 A B x y) = (term66 B y).
Proof. exact (MK_COMB (@lem4327397 A B x) (@lem4327398 B y)). Qed.
Lemma lem4327400 {B : Type'} (y : B) : (term66 B y) = True.
Proof. exact (eq_refl (term66 B y)). Qed.
Lemma lem4327401 {A B : Type'} (x : A) (y : B) : (term62 A B x y) = True.
Proof. exact (TRANS (@lem4327399 A B x y) (@lem4327400 B y)). Qed.
Lemma lem4327402 {A B : Type'} (GEN_PVAR_130 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_130) = (@SETSPEC (prod A B) GEN_PVAR_130).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_130)). Qed.
Lemma lem4327403 {A B : Type'} (x : A) (y : B) (GEN_PVAR_130 : prod A B) : (term67 A B GEN_PVAR_130 x y) = (@SETSPEC (prod A B) GEN_PVAR_130 True).
Proof. exact (MK_COMB (@lem4327402 A B GEN_PVAR_130) (@lem4327401 A B x y)). Qed.
Lemma lem4327404 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4327405 {A B : Type'} (GEN_PVAR_130 : prod A B) (x : A) (y : B) : (term68 A B GEN_PVAR_130 x y) = (term46 A B GEN_PVAR_130 x y).
Proof. exact (MK_COMB (@lem4327403 A B x y GEN_PVAR_130) (@lem4327404 A B x y)). Qed.
Lemma lem4327406 {A B : Type'} (GEN_PVAR_130 : prod A B) (x : A) : (term69 A B GEN_PVAR_130 x) = (term48 A B GEN_PVAR_130 x).
Proof. exact (fun_ext (fun y : B => @lem4327405 A B GEN_PVAR_130 x y)). Qed.
Lemma lem4327407 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4327408 {A B : Type'} (GEN_PVAR_130 : prod A B) (x : A) : (term70 A B GEN_PVAR_130 x) = (term50 A B GEN_PVAR_130 x).
Proof. exact (MK_COMB (@lem4327407 B) (@lem4327406 A B GEN_PVAR_130 x)). Qed.
Lemma lem4327409 {A B : Type'} (GEN_PVAR_130 : prod A B) : (term71 A B GEN_PVAR_130) = (term52 A B GEN_PVAR_130).
Proof. exact (fun_ext (fun x : A => @lem4327408 A B GEN_PVAR_130 x)). Qed.
Lemma lem4327410 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4327411 {A B : Type'} (GEN_PVAR_130 : prod A B) : (term72 A B GEN_PVAR_130) = (term54 A B GEN_PVAR_130).
Proof. exact (MK_COMB (@lem4327410 A) (@lem4327409 A B GEN_PVAR_130)). Qed.
Lemma lem4327412 {A B : Type'} : (term73 A B) = (term56 A B).
Proof. exact (fun_ext (fun GEN_PVAR_130 : prod A B => @lem4327411 A B GEN_PVAR_130)). Qed.
Lemma lem4327413 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4327414 {A B : Type'} : (term74 A B) = (term57 A B).
Proof. exact (MK_COMB (@lem4327413 A B) (@lem4327412 A B)). Qed.
Lemma lem4327415 {A B : Type'} (p1 : A) (p2 : B) : (term58 A B p1 p2) = (term58 A B p1 p2).
Proof. exact (eq_refl (term58 A B p1 p2)). Qed.
Lemma lem4327416 {A B : Type'} (p1 : A) (p2 : B) : (term61 A B p1 p2) = (term59 A B p1 p2).
Proof. exact (MK_COMB (@lem4327415 A B p1 p2) (@lem4327414 A B)). Qed.
Lemma lem4327417 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327418 {A B : Type'} (p1 : A) (p2 : B) : (term75 A B p1 p2) = (term76 A B p1 p2).
Proof. exact (MK_COMB (@lem4327417) (@lem4327416 A B p1 p2)). Qed.
Lemma lem4327419 {A B : Type'} (p1 : A) : (term64 A B p1) = (term65 B).
Proof. exact (eq_refl (term64 A B p1)). Qed.
Lemma lem4327420 {B : Type'} (p2 : B) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem4327421 {A B : Type'} (p1 : A) (p2 : B) : (term62 A B p1 p2) = (term66 B p2).
Proof. exact (MK_COMB (@lem4327419 A B p1) (@lem4327420 B p2)). Qed.
Lemma lem4327422 {B : Type'} (p2 : B) : (term66 B p2) = True.
Proof. exact (eq_refl (term66 B p2)). Qed.
Lemma lem4327423 {A B : Type'} (p1 : A) (p2 : B) : (term62 A B p1 p2) = True.
Proof. exact (TRANS (@lem4327421 A B p1 p2) (@lem4327422 B p2)). Qed.
Lemma lem4327424 {A B : Type'} (p1 : A) (p2 : B) : ((term61 A B p1 p2) = (term62 A B p1 p2)) = ((term59 A B p1 p2) = True).
Proof. exact (MK_COMB (@lem4327418 A B p1 p2) (@lem4327423 A B p1 p2)). Qed.
Lemma lem4327425 {A B : Type'} (p1 : A) (p2 : B) : (term59 A B p1 p2) = True.
Proof. exact (EQ_MP (@lem4327424 A B p1 p2) (@lem4327396 A B p1 p2)). Qed.
Lemma lem4327426 {A B : Type'} (p1 : A) (p2 : B) : (term31 A B p1 p2) = True.
Proof. exact (TRANS (@lem4327392 A B p1 p2) (@lem4327425 A B p1 p2)). Qed.
Lemma lem4327427 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4327428 {A B : Type'} (p1 : A) (p2 : B) : (term77 A B p1 p2) = (@eq Prop True).
Proof. exact (MK_COMB (@lem4327427) (@lem4327426 A B p1 p2)). Qed.
Lemma lem4327430 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem4327269 A x) (@lem4327268 A x)). Qed.
Lemma lem4327431 {A B : Type'} (x : prod A B) : (@IN (prod A B) x (@UNIV (prod A B))) = True.
Proof. exact (@lem4327430 (prod A B) x). Qed.
Lemma lem4327432 {A B : Type'} (p1 : A) (p2 : B) : (term32 A B p1 p2) = True.
Proof. exact (@lem4327431 A B (@pair A B p1 p2)). Qed.
Lemma lem4327433 {A B : Type'} (p1 : A) (p2 : B) : ((term31 A B p1 p2) = (term32 A B p1 p2)) = (True = True).
Proof. exact (MK_COMB (@lem4327428 A B p1 p2) (@lem4327432 A B p1 p2)). Qed.
Lemma lem4327435 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem4327436 : (True = True) = True.
Proof. exact (@lem4327435 True). Qed.
Lemma lem4327437 {A B : Type'} (p1 : A) (p2 : B) : ((term31 A B p1 p2) = (term32 A B p1 p2)) = True.
Proof. exact (TRANS (@lem4327433 A B p1 p2) (@lem4327436)). Qed.
Lemma lem4327438 {A B : Type'} (p1 : A) : (term34 A B p1) = (term65 B).
Proof. exact (fun_ext (fun p2 : B => @lem4327437 A B p1 p2)). Qed.
Lemma lem4327439 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4327440 {A B : Type'} (p1 : A) : (term36 A B p1) = (term78 B).
Proof. exact (MK_COMB (@lem4327439 B) (@lem4327438 A B p1)). Qed.
Lemma lem4327442 {A : Type'} (t : Prop) : (term79 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327443 {B : Type'} (t : Prop) : (term79 B t) = t.
Proof. exact (@lem4327442 B t). Qed.
Lemma lem4327444 {B : Type'} : (term78 B) = True.
Proof. exact (@lem4327443 B True). Qed.
Lemma lem4327445 {A B : Type'} (p1 : A) : (term36 A B p1) = True.
Proof. exact (TRANS (@lem4327440 A B p1) (@lem4327444 B)). Qed.
Lemma lem4327446 {A B : Type'} : (term38 A B) = (term65 A).
Proof. exact (fun_ext (fun p1 : A => @lem4327445 A B p1)). Qed.
Lemma lem4327447 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4327448 {A B : Type'} : (term39 A B) = (term78 A).
Proof. exact (MK_COMB (@lem4327447 A) (@lem4327446 A B)). Qed.
Lemma lem4327450 {A : Type'} (t : Prop) : (term79 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4327451 {A : Type'} (t : Prop) : (term79 A t) = t.
Proof. exact (@lem4327450 A t). Qed.
Lemma lem4327452 {A : Type'} : (term78 A) = True.
Proof. exact (@lem4327451 A True). Qed.
Lemma lem4327453 {A B : Type'} : (term39 A B) = True.
Proof. exact (TRANS (@lem4327448 A B) (@lem4327452 A)). Qed.
Lemma lem4327454 {A B : Type'} : ((@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))) = True.
Proof. exact (TRANS (@lem4327330 A B) (@lem4327453 A B)). Qed.
Lemma lem4327455 {A B : Type'} : True = ((@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B))).
Proof. exact (SYM (@lem4327454 A B)). Qed.
Lemma lem4327456 {A B : Type'} : (@CROSS B A (@UNIV A) (@UNIV B)) = (@UNIV (prod A B)).
Proof. exact (EQ_MP (@lem4327455 A B) (@lem0)). Qed.
