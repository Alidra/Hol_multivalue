Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_INTERSECTION_OF_INTERS_term_abbrevs.
Require Import FINITE_INTERSECTION_OF_IDEMPOT_spec.
Require Import INTERSECTION_OF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem4887283 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4887284 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4887285 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4887284 A P) (@lem4887283 A P)). Qed.
Lemma lem4887286 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4887285 A P Q). Qed.
Lemma lem4887287 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@INTERSECTION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4887290 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)) : (term4 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (h1). Qed.
Lemma lem4887291 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (SYM (@lem4887290 A P h1)). Qed.
Lemma lem4887292 {A : Type'} (P : type686 A) (h1 : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (h1). Qed.
Lemma lem4887293 {A : Type'} (P : type686 A) (h1 : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)) : (term4 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P).
Proof. exact (SYM (@lem4887292 A P h1)). Qed.
Lemma lem4887294 {A : Type'} (P : type686 A) : ((term4 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)).
Proof. exact (prop_ext (fun h1 : (term4 A P) = (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) => @lem4887291 A P h1) (fun h1 : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P) => @lem4887293 A P h1)). Qed.
Lemma lem4887295 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4887294 A P)). Qed.
Lemma lem4887296 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4887297 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4887296 A) (@lem4887295 A)). Qed.
Lemma lem4887298 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4887297 A) (@lem4886898 A)). Qed.
Lemma lem4887299 {A : Type'} (P : type686 A) : term9 A P.
Proof. exact (@lem4887298 A P). Qed.
Lemma lem4887300 {A : Type'} (P : type686 A) : (term9 A P) = ((@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P)).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4887302 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term10 A u P.
Proof. exact (h1). Qed.
Lemma lem4887303 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : term11 A u P.
Proof. exact (h1). Qed.
Lemma lem4887304 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : @FINITE (A -> Prop) u.
Proof. exact (h1). Qed.
Lemma lem4887306 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (EQ_MP (@lem4887300 A P) (@lem4887299 A P)). Qed.
Lemma lem4887307 {A : Type'} (P : type686 A) : (@INTERSECTION_OF A (@FINITE (A -> Prop)) P) = (term4 A P).
Proof. exact (@lem4887306 A P). Qed.
Lemma lem4887308 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (eq_refl (@INTERS A u)). Qed.
Lemma lem4887309 {A : Type'} (P : type686 A) (u : type686 A) : (term12 A P u) = (term13 A P u).
Proof. exact (MK_COMB (@lem4887307 A P) (@lem4887308 A u)). Qed.
Lemma lem4887310 {A : Type'} (P : type686 A) (u : type686 A) : (term13 A P u) = (term12 A P u).
Proof. exact (SYM (@lem4887309 A P u)). Qed.
Lemma lem4887312 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4887287 A P Q) (@lem4887286 A P Q)). Qed.
Lemma lem4887313 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4887312 A P Q). Qed.
Lemma lem4887314 {A : Type'} (P : type686 A) : (term4 A P) = (term14 A P).
Proof. exact (@lem4887313 A (@FINITE (A -> Prop)) (@INTERSECTION_OF A (@FINITE (A -> Prop)) P)). Qed.
Lemma lem4887315 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (eq_refl (@INTERS A u)). Qed.
Lemma lem4887316 {A : Type'} (P : type686 A) (u : type686 A) : (term13 A P u) = (term15 A P u).
Proof. exact (MK_COMB (@lem4887314 A P) (@lem4887315 A u)). Qed.
Lemma lem4887317 {A : Type'} (P : type686 A) (u : type686 A) : (term15 A P u) = (term13 A P u).
Proof. exact (SYM (@lem4887316 A P u)). Qed.
Lemma lem4887319 {A B : Type'} (f : A -> B) (y : A) : (term16 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4887320 {A : Type'} (f : type686 A) (y : A -> Prop) : (term17 A f y) = (f y).
Proof. exact (@lem4887319 (A -> Prop) Prop f y). Qed.
Lemma lem4887321 {A : Type'} (P : type686 A) (u : type686 A) : (term18 A P u) = (term15 A P u).
Proof. exact (@lem4887320 A (term14 A P) (@INTERS A u)). Qed.
Lemma lem4887322 {A : Type'} (P : type686 A) (s : A -> Prop) : (term19 A P s) = (term20 A P s).
Proof. exact (eq_refl (term19 A P s)). Qed.
Lemma lem4887323 {A : Type'} (P : type686 A) : (term21 A P) = (term14 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4887322 A P s)). Qed.
Lemma lem4887324 {A : Type'} (u : type686 A) : (@INTERS A u) = (@INTERS A u).
Proof. exact (eq_refl (@INTERS A u)). Qed.
Lemma lem4887325 {A : Type'} (P : type686 A) (u : type686 A) : (term18 A P u) = (term15 A P u).
Proof. exact (MK_COMB (@lem4887323 A P) (@lem4887324 A u)). Qed.
Lemma lem4887326 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4887327 {A : Type'} (P : type686 A) (u : type686 A) : (term22 A P u) = (term23 A P u).
Proof. exact (MK_COMB (@lem4887326) (@lem4887325 A P u)). Qed.
Lemma lem4887328 {A : Type'} (P : type686 A) (u : type686 A) : (term15 A P u) = (term24 A P u).
Proof. exact (eq_refl (term15 A P u)). Qed.
Lemma lem4887329 {A : Type'} (P : type686 A) (u : type686 A) : ((term18 A P u) = (term15 A P u)) = ((term15 A P u) = (term24 A P u)).
Proof. exact (MK_COMB (@lem4887327 A P u) (@lem4887328 A P u)). Qed.
Lemma lem4887330 {A : Type'} (P : type686 A) (u : type686 A) : (term15 A P u) = (term24 A P u).
Proof. exact (EQ_MP (@lem4887329 A P u) (@lem4887321 A P u)). Qed.
Lemma lem4887347 {A : Type'} (P : type686 A) (u : type686 A) : (term24 A P u) = (term15 A P u).
Proof. exact (SYM (@lem4887330 A P u)). Qed.
Lemma lem4887348 {A : Type'} (u : type686 A) : (@FINITE (A -> Prop) u) = ((@FINITE (A -> Prop) u) = True).
Proof. exact (@lem7 (@FINITE (A -> Prop) u)). Qed.
Lemma lem4887350 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : term25 A u P s.
Proof. exact (@lem4887303 A u P h1 s). Qed.
Lemma lem4887351 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term25 A u P s) = (term26 A u P s).
Proof. exact (eq_refl (term25 A u P s)). Qed.
Lemma lem4887352 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : term26 A u P s.
Proof. exact (EQ_MP (@lem4887351 A u P s) (@lem4887350 A s u P h1)). Qed.
Lemma lem4887353 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term26 A u P s) = ((term26 A u P s) = True).
Proof. exact (@lem7 (term26 A u P s)). Qed.
Lemma lem4887358 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = True.
Proof. exact (EQ_MP (@lem4887348 A u) (@lem4887304 A u h1)). Qed.
Lemma lem4887359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887360 {A : Type'} (u : type686 A) (h1 : @FINITE (A -> Prop) u) : (term27 A u) = (and True).
Proof. exact (MK_COMB (@lem4887359) (@lem4887358 A u h1)). Qed.
Lemma lem4887368 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term26 A u P s) = True.
Proof. exact (EQ_MP (@lem4887353 A u P s) (@lem4887352 A s u P h1)). Qed.
Lemma lem4887369 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term26 A u P s) = True.
Proof. exact (@lem4887368 A s u P h1). Qed.
Lemma lem4887370 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term26 A u P c) = True.
Proof. exact (@lem4887369 A c u P h1). Qed.
Lemma lem4887371 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term28 A u P) = (term29 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4887370 A c u P h1)). Qed.
Lemma lem4887372 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4887373 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term11 A u P) = (term30 A).
Proof. exact (MK_COMB (@lem4887372 A) (@lem4887371 A u P h1)). Qed.
Lemma lem4887375 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4887376 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem4887375 (A -> Prop) t). Qed.
Lemma lem4887377 {A : Type'} : (term30 A) = True.
Proof. exact (@lem4887376 A True). Qed.
Lemma lem4887378 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term11 A u P) = True.
Proof. exact (TRANS (@lem4887373 A u P h1) (@lem4887377 A)). Qed.
Lemma lem4887379 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4887380 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term33 A u P) = (and True).
Proof. exact (MK_COMB (@lem4887379) (@lem4887378 A u P h1)). Qed.
Lemma lem4887382 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4887383 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4887382 (A -> Prop) x). Qed.
Lemma lem4887384 {A : Type'} (u : type686 A) : ((@INTERS A u) = (@INTERS A u)) = True.
Proof. exact (@lem4887383 A (@INTERS A u)). Qed.
Lemma lem4887385 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term34 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4887380 A u P h1) (@lem4887384 A u)). Qed.
Lemma lem4887387 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887388 : (True /\ True) = True.
Proof. exact (@lem4887387 True). Qed.
Lemma lem4887389 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term11 A u P) : (term34 A P u) = True.
Proof. exact (TRANS (@lem4887385 A u P h1) (@lem4887388)). Qed.
Lemma lem4887390 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (term35 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4887360 A u h2) (@lem4887389 A u P h1)). Qed.
Lemma lem4887392 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4887393 : (True /\ True) = True.
Proof. exact (@lem4887392 True). Qed.
Lemma lem4887394 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (term35 A P u) = True.
Proof. exact (TRANS (@lem4887390 A P u h1 h2) (@lem4887393)). Qed.
Lemma lem4887395 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : True = (term35 A P u).
Proof. exact (SYM (@lem4887394 A P u h1 h2)). Qed.
Lemma lem4887396 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term35 A P u.
Proof. exact (EQ_MP (@lem4887395 A P u h1 h2) (@lem0)). Qed.
Lemma lem4887397 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term24 A P u.
Proof. exact (ex_intro (term36 A P u) u (@lem4887396 A P u h1 h2)). Qed.
Lemma lem4887398 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term15 A P u.
Proof. exact (EQ_MP (@lem4887347 A P u) (@lem4887397 A P u h1 h2)). Qed.
Lemma lem4887399 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term13 A P u.
Proof. exact (EQ_MP (@lem4887317 A P u) (@lem4887398 A P u h1 h2)). Qed.
Lemma lem4887400 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term12 A P u.
Proof. exact (EQ_MP (@lem4887310 A P u) (@lem4887399 A P u h1 h2)). Qed.
Lemma lem4887401 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term11 A u P.
Proof. exact (proj2 (@lem4887302 A u P h1)). Qed.
Lemma lem4887402 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : @FINITE (A -> Prop) u.
Proof. exact (proj1 (@lem4887302 A u P h1)). Qed.
Lemma lem4887403 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (term11 A u P) = (term12 A P u).
Proof. exact (prop_ext (fun h3 : term11 A u P => @lem4887400 A P u h1 h2) (fun h3 : term12 A P u => @lem4887303 A u P h1)). Qed.
Lemma lem4887404 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term12 A P u.
Proof. exact (EQ_MP (@lem4887403 A P u h1 h2) (@lem4887303 A u P h1)). Qed.
Lemma lem4887405 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : (@FINITE (A -> Prop) u) = (term12 A P u).
Proof. exact (prop_ext (fun h3 : @FINITE (A -> Prop) u => @lem4887404 A P u h1 h2) (fun h3 : term12 A P u => @lem4887304 A u h2)). Qed.
Lemma lem4887406 {A : Type'} (P : type686 A) (u : type686 A) (h1 : term11 A u P) (h2 : @FINITE (A -> Prop) u) : term12 A P u.
Proof. exact (EQ_MP (@lem4887405 A P u h1 h2) (@lem4887304 A u h2)). Qed.
Lemma lem4887407 {A : Type'} (u : type686 A) (P : type686 A) (h1 : @FINITE (A -> Prop) u) (h2 : term10 A u P) : (term11 A u P) = (term12 A P u).
Proof. exact (prop_ext (fun h3 : term11 A u P => @lem4887406 A P u h3 h1) (fun h3 : term12 A P u => @lem4887401 A u P h2)). Qed.
Lemma lem4887408 {A : Type'} (u : type686 A) (P : type686 A) (h1 : @FINITE (A -> Prop) u) (h2 : term10 A u P) : term12 A P u.
Proof. exact (EQ_MP (@lem4887407 A u P h1 h2) (@lem4887401 A u P h2)). Qed.
Lemma lem4887409 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (@FINITE (A -> Prop) u) = (term12 A P u).
Proof. exact (prop_ext (fun h2 : @FINITE (A -> Prop) u => @lem4887408 A u P h2 h1) (fun h2 : term12 A P u => @lem4887402 A u P h1)). Qed.
Lemma lem4887410 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term12 A P u.
Proof. exact (EQ_MP (@lem4887409 A u P h1) (@lem4887402 A u P h1)). Qed.
Lemma lem4887411 {A : Type'} (P : type686 A) (u : type686 A) : term37 A P u.
Proof. exact (fun h0 : term10 A u P => @lem4887410 A u P h0). Qed.
Lemma lem4887416 {A : Type'} (P : type686 A) : term38 A P.
Proof. exact (fun u : type686 A => @lem4887411 A P u). Qed.
Lemma lem4887421 {A : Type'} : term39 A.
Proof. exact (fun P : type686 A => @lem4887416 A P). Qed.
