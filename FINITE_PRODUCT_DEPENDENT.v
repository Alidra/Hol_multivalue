Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FINITE_PRODUCT_DEPENDENT_term_abbrevs.
Require Import DISJ_ASSOC_spec.
Require Import EXISTS_PAIR_THM_spec.
Require Import EXTENSION_spec.
Require Import FINITE_IMAGE_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import FINITE_RULES_spec.
Require Import FINITE_SUBSET_spec.
Require Import FINITE_UNION_spec.
Require Import FORALL_IN_GSPEC_spec.
Require Import IN_ELIM_PAIR_THM_spec.
Require Import IN_IMAGE_spec.
Require Import IN_INSERT_spec.
Require Import IN_UNION_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_IN_EMPTY_spec.
Require Import RIGHT_FORALL_IMP_THM_spec.
Require Import SUBSET_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19699_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3184747_spec.
Require Import thm3184750_spec.
Require Import thm4211_spec.
Require Import thm48805_spec.
Require Import thm48806_spec.
Require Import thm48811_spec.
Require Import thm48812_spec.
Require Import thm48920_spec.
Require Import thm51128_spec.
Require Import thm51159_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem4318349 (t1 : Prop) : term0 t1.
Proof. exact (@lem693 t1). Qed.
Lemma lem4318350 (t1 : Prop) : (term0 t1) = (term1 t1).
Proof. exact (eq_refl (term0 t1)). Qed.
Lemma lem4318351 (t1 : Prop) : term1 t1.
Proof. exact (EQ_MP (@lem4318350 t1) (@lem4318349 t1)). Qed.
Lemma lem4318352 (t1 : Prop) (t2 : Prop) : term2 t1 t2.
Proof. exact (@lem4318351 t1 t2). Qed.
Lemma lem4318353 (t1 : Prop) (t2 : Prop) : (term2 t1 t2) = (term3 t1 t2).
Proof. exact (eq_refl (term2 t1 t2)). Qed.
Lemma lem4318354 (t1 : Prop) (t2 : Prop) : term3 t1 t2.
Proof. exact (EQ_MP (@lem4318353 t1 t2) (@lem4318352 t1 t2)). Qed.
Lemma lem4318355 (t1 : Prop) (t2 : Prop) (t3 : Prop) : term4 t1 t2 t3.
Proof. exact (@lem4318354 t1 t2 t3). Qed.
Lemma lem4318356 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term4 t1 t2 t3) = ((term5 t1 t2 t3) = (term6 t1 t2 t3)).
Proof. exact (eq_refl (term4 t1 t2 t3)). Qed.
Lemma lem4318357 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term5 t1 t2 t3) = (term6 t1 t2 t3).
Proof. exact (EQ_MP (@lem4318356 t1 t2 t3) (@lem4318355 t1 t2 t3)). Qed.
Lemma lem4318358 (t1 : Prop) (t2 : Prop) (t3 : Prop) : (term6 t1 t2 t3) = (term5 t1 t2 t3).
Proof. exact (SYM (@lem4318357 t1 t2 t3)). Qed.
Lemma lem4318359 {A : Type'} (s : A -> Prop) : term7 A s.
Proof. exact (@lem3204949 A s). Qed.
Lemma lem4318360 {A : Type'} (s : A -> Prop) : (term7 A s) = (term8 A s).
Proof. exact (eq_refl (term7 A s)). Qed.
Lemma lem4318361 {A : Type'} (s : A -> Prop) : term8 A s.
Proof. exact (EQ_MP (@lem4318360 A s) (@lem4318359 A s)). Qed.
Lemma lem4318362 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term9 A s t.
Proof. exact (@lem4318361 A s t). Qed.
Lemma lem4318363 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term9 A s t) = (term10 A s t).
Proof. exact (eq_refl (term9 A s t)). Qed.
Lemma lem4318364 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term10 A s t.
Proof. exact (EQ_MP (@lem4318363 A s t) (@lem4318362 A s t)). Qed.
Lemma lem4318365 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term11 A s t x.
Proof. exact (@lem4318364 A s t x). Qed.
Lemma lem4318366 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term11 A s t x) = ((term12 A x s t) = (term13 A s x t)).
Proof. exact (eq_refl (term11 A s t x)). Qed.
Lemma lem4318368 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4318369 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem4318370 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem4318369 A x) (@lem4318368 A x)). Qed.
Lemma lem4318371 {A : Type'} (x : A) (y : A) : term16 A x y.
Proof. exact (@lem4318370 A x y). Qed.
Lemma lem4318372 {A : Type'} (y : A) (x : A) : (term16 A x y) = (term17 A y x).
Proof. exact (eq_refl (term16 A x y)). Qed.
Lemma lem4318373 {A : Type'} (y : A) (x : A) : term17 A y x.
Proof. exact (EQ_MP (@lem4318372 A y x) (@lem4318371 A x y)). Qed.
Lemma lem4318374 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term18 A y x s.
Proof. exact (@lem4318373 A y x s). Qed.
Lemma lem4318375 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term18 A y x s) = ((term19 A x y s) = (term20 A y x s)).
Proof. exact (eq_refl (term18 A y x s)). Qed.
Lemma lem4318408 {_83064 : Type'} : term21 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem4318409 {_83064 : Type'} (P : type919 _83064) : term22 _83064 P.
Proof. exact (@lem4318408 _83064 P). Qed.
Lemma lem4318410 {_83064 : Type'} (P : type919 _83064) : (term22 _83064 P) = (term23 _83064 P).
Proof. exact (eq_refl (term22 _83064 P)). Qed.
Lemma lem4318411 {_83064 : Type'} (P : type919 _83064) : term23 _83064 P.
Proof. exact (EQ_MP (@lem4318410 _83064 P) (@lem4318409 _83064 P)). Qed.
Lemma lem4318412 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term24 _83064 P x.
Proof. exact (@lem4318411 _83064 P x). Qed.
Lemma lem4318413 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term24 _83064 P x) = ((term25 _83064 x P) = (term26 _83064 P x)).
Proof. exact (eq_refl (term24 _83064 P x)). Qed.
Lemma lem4318415 {A B : Type'} (y : B) : term27 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4318416 {A B : Type'} (y : B) : (term27 A B y) = (term28 A B y).
Proof. exact (eq_refl (term27 A B y)). Qed.
Lemma lem4318417 {A B : Type'} (y : B) : term28 A B y.
Proof. exact (EQ_MP (@lem4318416 A B y) (@lem4318415 A B y)). Qed.
Lemma lem4318418 {A B : Type'} (y : B) (s : A -> Prop) : term29 A B y s.
Proof. exact (@lem4318417 A B y s). Qed.
Lemma lem4318419 {A B : Type'} (y : B) (s : A -> Prop) : (term29 A B y s) = (term30 A B y s).
Proof. exact (eq_refl (term29 A B y s)). Qed.
Lemma lem4318420 {A B : Type'} (y : B) (s : A -> Prop) : term30 A B y s.
Proof. exact (EQ_MP (@lem4318419 A B y s) (@lem4318418 A B y s)). Qed.
Lemma lem4318421 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term31 A B y s f.
Proof. exact (@lem4318420 A B y s f). Qed.
Lemma lem4318422 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term31 A B y s f) = ((term32 A B y f s) = (term33 A B y f s)).
Proof. exact (eq_refl (term31 A B y s f)). Qed.
Lemma lem4318424 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4318425 {A : Type'} (s : A -> Prop) : (term34 A s) = (term35 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem4318426 {A : Type'} (s : A -> Prop) : term35 A s.
Proof. exact (EQ_MP (@lem4318425 A s) (@lem4318424 A s)). Qed.
Lemma lem4318427 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term36 A s t.
Proof. exact (@lem4318426 A s t). Qed.
Lemma lem4318428 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = ((s = t) = (term37 A s t)).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem4318430 {A : Type'} (x : A) : term38 A x.
Proof. exact (@lem3204775 A x). Qed.
Lemma lem4318431 {A : Type'} (x : A) : (term38 A x) = (term39 A x).
Proof. exact (eq_refl (term38 A x)). Qed.
Lemma lem4318432 {A : Type'} (x : A) : term39 A x.
Proof. exact (EQ_MP (@lem4318431 A x) (@lem4318430 A x)). Qed.
Lemma lem4318433 {A : Type'} (x : A) : term40 A x.
Proof. exact (@lem82 (@IN A x (@EMPTY A))). Qed.
Lemma lem4318466 {_83064 : Type'} : term21 _83064.
Proof. exact (EQ_MP (@lem3184750 _83064) (@lem3184747 _83064)). Qed.
Lemma lem4318467 {_83064 : Type'} (P : type919 _83064) : term22 _83064 P.
Proof. exact (@lem4318466 _83064 P). Qed.
Lemma lem4318468 {_83064 : Type'} (P : type919 _83064) : (term22 _83064 P) = (term23 _83064 P).
Proof. exact (eq_refl (term22 _83064 P)). Qed.
Lemma lem4318469 {_83064 : Type'} (P : type919 _83064) : term23 _83064 P.
Proof. exact (EQ_MP (@lem4318468 _83064 P) (@lem4318467 _83064 P)). Qed.
Lemma lem4318470 {_83064 : Type'} (P : type919 _83064) (x : _83064) : term24 _83064 P x.
Proof. exact (@lem4318469 _83064 P x). Qed.
Lemma lem4318471 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term24 _83064 P x) = ((term25 _83064 x P) = (term26 _83064 P x)).
Proof. exact (eq_refl (term24 _83064 P x)). Qed.
Lemma lem4318473 {A : Type'} (s : A -> Prop) : term34 A s.
Proof. exact (@lem3181245 A s). Qed.
Lemma lem4318474 {A : Type'} (s : A -> Prop) : (term34 A s) = (term35 A s).
Proof. exact (eq_refl (term34 A s)). Qed.
Lemma lem4318475 {A : Type'} (s : A -> Prop) : term35 A s.
Proof. exact (EQ_MP (@lem4318474 A s) (@lem4318473 A s)). Qed.
Lemma lem4318476 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term36 A s t.
Proof. exact (@lem4318475 A s t). Qed.
Lemma lem4318477 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term36 A s t) = ((s = t) = (term37 A s t)).
Proof. exact (eq_refl (term36 A s t)). Qed.
Lemma lem4318479 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem4318480 {A : Type'} (P : type686 A) (h1 : term41 A) : term42 A P.
Proof. exact (@lem4318479 A h1 P). Qed.
Lemma lem4318481 {A : Type'} (P : type686 A) : (term42 A P) = (term43 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4318482 {A : Type'} (P : type686 A) (h1 : term41 A) : term43 A P.
Proof. exact (EQ_MP (@lem4318481 A P) (@lem4318480 A P h1)). Qed.
Lemma lem4318483 {A : Type'} (P : type686 A) (h1 : term44 A P) : term44 A P.
Proof. exact (h1). Qed.
Lemma lem4318484 {A : Type'} (P : type686 A) (h1 : term41 A) (h2 : term44 A P) : term45 A P.
Proof. exact (@lem4318482 A P h1 (@lem4318483 A P h2)). Qed.
Lemma lem4318485 {A : Type'} (P : type686 A) (h1 : term44 A P) : term46 A P.
Proof. exact (fun h0 : term41 A => @lem4318484 A P h0 h1). Qed.
Lemma lem4318486 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (h1). Qed.
Lemma lem4318487 {A : Type'} (P : type686 A) (h1 : term41 A) (h2 : term44 A P) : term45 A P.
Proof. exact (@lem4318485 A P h2 (@lem4318486 A h1)). Qed.
Lemma lem4318488 {A : Type'} (P : type686 A) (h1 : term41 A) : term43 A P.
Proof. exact (fun h0 : term44 A P => @lem4318487 A P h1 h0). Qed.
Lemma lem4318489 {A : Type'} (h1 : term41 A) : term41 A.
Proof. exact (fun P : type686 A => @lem4318488 A P h1). Qed.
Lemma lem4318490 {A : Type'} : term47 A.
Proof. exact (fun h0 : term41 A => @lem4318489 A h0). Qed.
Lemma lem4318491 {A : Type'} : term41 A.
Proof. exact (@lem4318490 A (@lem3558722 A)). Qed.
Lemma lem4318492 {A : Type'} (P : type686 A) : term42 A P.
Proof. exact (@lem4318491 A P). Qed.
Lemma lem4318493 {A : Type'} (P : type686 A) : (term42 A P) = (term43 A P).
Proof. exact (eq_refl (term42 A P)). Qed.
Lemma lem4318495 {A : Type'} (P : Prop) : term48 A P.
Proof. exact (@lem6534 A P). Qed.
Lemma lem4318496 {A : Type'} (P : Prop) : (term48 A P) = (term49 A P).
Proof. exact (eq_refl (term48 A P)). Qed.
Lemma lem4318497 {A : Type'} (P : Prop) : term49 A P.
Proof. exact (EQ_MP (@lem4318496 A P) (@lem4318495 A P)). Qed.
Lemma lem4318498 {A : Type'} (P : Prop) (Q : A -> Prop) : term50 A P Q.
Proof. exact (@lem4318497 A P Q). Qed.
Lemma lem4318499 {A : Type'} (P : Prop) (Q : A -> Prop) : (term50 A P Q) = ((term51 A P Q) = (term52 A P Q)).
Proof. exact (eq_refl (term50 A P Q)). Qed.
Lemma lem4318511 {A B : Type'} (h1 : term53 A B) : term53 A B.
Proof. exact (h1). Qed.
Lemma lem4318512 {A B : Type'} (f : A -> B) (h1 : term53 A B) : term54 A B f.
Proof. exact (@lem4318511 A B h1 f). Qed.
Lemma lem4318513 {A B : Type'} (f : A -> B) : (term54 A B f) = (term55 A B f).
Proof. exact (eq_refl (term54 A B f)). Qed.
Lemma lem4318514 {A B : Type'} (f : A -> B) (h1 : term53 A B) : term55 A B f.
Proof. exact (EQ_MP (@lem4318513 A B f) (@lem4318512 A B f h1)). Qed.
Lemma lem4318515 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term53 A B) : term56 A B f s.
Proof. exact (@lem4318514 A B f h1 s). Qed.
Lemma lem4318516 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term56 A B f s) = (term57 A B f s).
Proof. exact (eq_refl (term56 A B f s)). Qed.
Lemma lem4318517 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term53 A B) : term57 A B f s.
Proof. exact (EQ_MP (@lem4318516 A B f s) (@lem4318515 A B f s h1)). Qed.
Lemma lem4318518 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4318519 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term53 A B) (h2 : @FINITE A s) : term58 A B f s.
Proof. exact (@lem4318517 A B f s h1 (@lem4318518 A s h2)). Qed.
Lemma lem4318520 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term59 A B f s.
Proof. exact (fun h0 : term53 A B => @lem4318519 A B f s h0 h1). Qed.
Lemma lem4318521 {A B : Type'} (h1 : term53 A B) : term53 A B.
Proof. exact (h1). Qed.
Lemma lem4318522 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term53 A B) (h2 : @FINITE A s) : term58 A B f s.
Proof. exact (@lem4318520 A B f s h2 (@lem4318521 A B h1)). Qed.
Lemma lem4318523 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : term53 A B) : term57 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4318522 A B f s h1 h0). Qed.
Lemma lem4318524 {A B : Type'} (f : A -> B) (h1 : term53 A B) : term55 A B f.
Proof. exact (fun s : A -> Prop => @lem4318523 A B f s h1). Qed.
Lemma lem4318525 {A B : Type'} (h1 : term53 A B) : term53 A B.
Proof. exact (fun f : A -> B => @lem4318524 A B f h1). Qed.
Lemma lem4318526 {A B : Type'} : term60 A B.
Proof. exact (fun h0 : term53 A B => @lem4318525 A B h0). Qed.
Lemma lem4318527 {A B : Type'} : term53 A B.
Proof. exact (@lem4318526 A B (@lem3615104 A B)). Qed.
Lemma lem4318528 {A B : Type'} (f : A -> B) : term54 A B f.
Proof. exact (@lem4318527 A B f). Qed.
Lemma lem4318529 {A B : Type'} (f : A -> B) : (term54 A B f) = (term55 A B f).
Proof. exact (eq_refl (term54 A B f)). Qed.
Lemma lem4318530 {A B : Type'} (f : A -> B) : term55 A B f.
Proof. exact (EQ_MP (@lem4318529 A B f) (@lem4318528 A B f)). Qed.
Lemma lem4318531 {A B : Type'} (f : A -> B) (s : A -> Prop) : term56 A B f s.
Proof. exact (@lem4318530 A B f s). Qed.
Lemma lem4318532 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term56 A B f s) = (term57 A B f s).
Proof. exact (eq_refl (term56 A B f s)). Qed.
Lemma lem4318534 {_88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 : Type'} (Q : _89106 -> Prop) : term61 _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q.
Proof. exact (proj2 (@lem3435744 Prop _88961 _88962 _89029 _89030 _89031 _89106 _89107 _89108 _89109 _89110 Q)). Qed.
Lemma lem4318550 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) : term62 _88961 _88962 _89106 Q.
Proof. exact (proj1 (@lem4318534 _88961 _88962 Prop Prop Prop _89106 Prop Prop Prop Prop Q)). Qed.
Lemma lem4318551 {_88961 _88962 _89106 : Type'} (Q : _89106 -> Prop) (P : type1470 _88961 _88962) : term63 _88961 _88962 _89106 Q P.
Proof. exact (@lem4318550 _88961 _88962 _89106 Q P). Qed.
Lemma lem4318552 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : (term63 _88961 _88962 _89106 Q P) = (term64 _88961 _88962 _89106 P Q).
Proof. exact (eq_refl (term63 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4318553 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) : term64 _88961 _88962 _89106 P Q.
Proof. exact (EQ_MP (@lem4318552 _88961 _88962 _89106 P Q) (@lem4318551 _88961 _88962 _89106 Q P)). Qed.
Lemma lem4318554 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : term65 _88961 _88962 _89106 P Q f.
Proof. exact (@lem4318553 _88961 _88962 _89106 P Q f). Qed.
Lemma lem4318555 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term65 _88961 _88962 _89106 P Q f) = ((term66 _88961 _88962 _89106 P f Q) = (term67 _88961 _88962 _89106 P Q f)).
Proof. exact (eq_refl (term65 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4318564 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term68 _88435 _88436 P.
Proof. exact (@lem3405756 _88435 _88436 P). Qed.
Lemma lem4318565 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : (term68 _88435 _88436 P) = (term69 _88435 _88436 P).
Proof. exact (eq_refl (term68 _88435 _88436 P)). Qed.
Lemma lem4318566 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) : term69 _88435 _88436 P.
Proof. exact (EQ_MP (@lem4318565 _88435 _88436 P) (@lem4318564 _88435 _88436 P)). Qed.
Lemma lem4318567 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term70 _88435 _88436 P a.
Proof. exact (@lem4318566 _88435 _88436 P a). Qed.
Lemma lem4318568 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : (term70 _88435 _88436 P a) = (term71 _88435 _88436 P a).
Proof. exact (eq_refl (term70 _88435 _88436 P a)). Qed.
Lemma lem4318569 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) : term71 _88435 _88436 P a.
Proof. exact (EQ_MP (@lem4318568 _88435 _88436 P a) (@lem4318567 _88435 _88436 P a)). Qed.
Lemma lem4318570 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : term72 _88435 _88436 P a b.
Proof. exact (@lem4318569 _88435 _88436 P a b). Qed.
Lemma lem4318571 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term72 _88435 _88436 P a b) = ((term73 _88435 _88436 a b P) = (P a b)).
Proof. exact (eq_refl (term72 _88435 _88436 P a b)). Qed.
Lemma lem4318573 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : term74 _5131 _5132 P.
Proof. exact (@lem51006 _5131 _5132 P). Qed.
Lemma lem4318574 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term74 _5131 _5132 P) = ((term75 _5131 _5132 P) = (term76 _5131 _5132 P)).
Proof. exact (eq_refl (term74 _5131 _5132 P)). Qed.
Lemma lem4318576 {A B : Type'} (y : B) : term27 A B y.
Proof. exact (@lem3206070 A B y). Qed.
Lemma lem4318577 {A B : Type'} (y : B) : (term27 A B y) = (term28 A B y).
Proof. exact (eq_refl (term27 A B y)). Qed.
Lemma lem4318578 {A B : Type'} (y : B) : term28 A B y.
Proof. exact (EQ_MP (@lem4318577 A B y) (@lem4318576 A B y)). Qed.
Lemma lem4318579 {A B : Type'} (y : B) (s : A -> Prop) : term29 A B y s.
Proof. exact (@lem4318578 A B y s). Qed.
Lemma lem4318580 {A B : Type'} (y : B) (s : A -> Prop) : (term29 A B y s) = (term30 A B y s).
Proof. exact (eq_refl (term29 A B y s)). Qed.
Lemma lem4318581 {A B : Type'} (y : B) (s : A -> Prop) : term30 A B y s.
Proof. exact (EQ_MP (@lem4318580 A B y s) (@lem4318579 A B y s)). Qed.
Lemma lem4318582 {A B : Type'} (y : B) (s : A -> Prop) (f : A -> B) : term31 A B y s f.
Proof. exact (@lem4318581 A B y s f). Qed.
Lemma lem4318583 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term31 A B y s f) = ((term32 A B y f s) = (term33 A B y f s)).
Proof. exact (eq_refl (term31 A B y s f)). Qed.
Lemma lem4318585 {A : Type'} (s : A -> Prop) : term77 A s.
Proof. exact (@lem3194148 A s). Qed.
Lemma lem4318586 {A : Type'} (s : A -> Prop) : (term77 A s) = (term78 A s).
Proof. exact (eq_refl (term77 A s)). Qed.
Lemma lem4318587 {A : Type'} (s : A -> Prop) : term78 A s.
Proof. exact (EQ_MP (@lem4318586 A s) (@lem4318585 A s)). Qed.
Lemma lem4318588 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term79 A s t.
Proof. exact (@lem4318587 A s t). Qed.
Lemma lem4318589 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term79 A s t) = ((@SUBSET A s t) = (term80 A s t)).
Proof. exact (eq_refl (term79 A s t)). Qed.
Lemma lem4318591 {A : Type'} (h1 : term81 A) : term81 A.
Proof. exact (h1). Qed.
Lemma lem4318592 {A : Type'} (s : A -> Prop) (h1 : term81 A) : term82 A s.
Proof. exact (@lem4318591 A h1 s). Qed.
Lemma lem4318593 {A : Type'} (s : A -> Prop) : (term82 A s) = (term83 A s).
Proof. exact (eq_refl (term82 A s)). Qed.
Lemma lem4318594 {A : Type'} (s : A -> Prop) (h1 : term81 A) : term83 A s.
Proof. exact (EQ_MP (@lem4318593 A s) (@lem4318592 A s h1)). Qed.
Lemma lem4318595 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term81 A) : term84 A s t.
Proof. exact (@lem4318594 A s h1 t). Qed.
Lemma lem4318596 {A : Type'} (t : A -> Prop) (s : A -> Prop) : (term84 A s t) = (term85 A t s).
Proof. exact (eq_refl (term84 A s t)). Qed.
Lemma lem4318597 {A : Type'} (t : A -> Prop) (s : A -> Prop) (h1 : term81 A) : term85 A t s.
Proof. exact (EQ_MP (@lem4318596 A t s) (@lem4318595 A s t h1)). Qed.
Lemma lem4318598 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term86 A s t) : term86 A s t.
Proof. exact (h1). Qed.
Lemma lem4318599 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term81 A) (h2 : term86 A s t) : @FINITE A s.
Proof. exact (@lem4318597 A t s h1 (@lem4318598 A s t h2)). Qed.
Lemma lem4318600 {A : Type'} (s : A -> Prop) (t : A -> Prop) (h1 : term86 A s t) : term87 A s.
Proof. exact (fun h0 : term81 A => @lem4318599 A s t h0 h1). Qed.
Lemma lem4318601 {A : Type'} (s : A -> Prop) (h1 : term88 A s) : term88 A s.
Proof. exact (h1). Qed.
Lemma lem4318602 {A : Type'} (s : A -> Prop) (h1 : term88 A s) : term87 A s.
Proof. exact (ex_elim (@lem4318601 A s h1) (fun t : A -> Prop => fun h0 : term89 A s t => @lem4318600 A s t h0)). Qed.
Lemma lem4318603 {A : Type'} (h1 : term81 A) : term81 A.
Proof. exact (h1). Qed.
Lemma lem4318604 {A : Type'} (s : A -> Prop) (h1 : term81 A) (h2 : term88 A s) : @FINITE A s.
Proof. exact (@lem4318602 A s h2 (@lem4318603 A h1)). Qed.
Lemma lem4318605 {A : Type'} (s : A -> Prop) (h1 : term81 A) : term90 A s.
Proof. exact (fun h0 : term88 A s => @lem4318604 A s h1 h0). Qed.
Lemma lem4318606 {A : Type'} (h1 : term81 A) : term91 A.
Proof. exact (fun s : A -> Prop => @lem4318605 A s h1). Qed.
Lemma lem4318607 {A : Type'} : term92 A.
Proof. exact (fun h0 : term81 A => @lem4318606 A h0). Qed.
Lemma lem4318608 {A : Type'} : term91 A.
Proof. exact (@lem4318607 A (@lem3599924 A)). Qed.
Lemma lem4318609 {A : Type'} (s : A -> Prop) : term93 A s.
Proof. exact (@lem4318608 A s). Qed.
Lemma lem4318610 {A : Type'} (s : A -> Prop) : (term93 A s) = (term90 A s).
Proof. exact (eq_refl (term93 A s)). Qed.
Lemma lem4318612 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term94 A B s t) : term94 A B s t.
Proof. exact (h1). Qed.
Lemma lem4318613 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term95 A B s t) : term95 A B s t.
Proof. exact (h1). Qed.
Lemma lem4318614 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4318616 {A : Type'} (s : A -> Prop) : term90 A s.
Proof. exact (EQ_MP (@lem4318610 A s) (@lem4318609 A s)). Qed.
Lemma lem4318617 {C : Type'} (s : C -> Prop) : term90 C s.
Proof. exact (@lem4318616 C s). Qed.
Lemma lem4318618 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term96 A B C s t f.
Proof. exact (@lem4318617 C (term97 A B C s t f)). Qed.
Lemma lem4318644 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term80 A s t).
Proof. exact (EQ_MP (@lem4318589 A s t) (@lem4318588 A s t)). Qed.
Lemma lem4318645 {C : Type'} (s : C -> Prop) (t : C -> Prop) : (@SUBSET C s t) = (term80 C s t).
Proof. exact (@lem4318644 C s t). Qed.
Lemma lem4318646 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term98 A B C f s t) = (term99 A B C f s t).
Proof. exact (@lem4318645 C (term97 A B C s t f) (term100 A B C f s t)). Qed.
Lemma lem4318668 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term32 A B y f s) = (term33 A B y f s).
Proof. exact (EQ_MP (@lem4318583 A B y f s) (@lem4318582 A B y s f)). Qed.
Lemma lem4318669 {A B C : Type'} (y : C) (f : type1209 A B C) (s : type1210 A B) : (term101 A B C y f s) = (term102 A B C y f s).
Proof. exact (@lem4318668 (prod A B) C y f s). Qed.
Lemma lem4318670 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term103 A B C x f s t) = (term104 A B C x f s t).
Proof. exact (@lem4318669 A B C x (term105 A B C f) (term106 A B s t)). Qed.
Lemma lem4318676 {_5131 _5132 : Type'} (P : type1223 _5131 _5132) : (term75 _5131 _5132 P) = (term76 _5131 _5132 P).
Proof. exact (EQ_MP (@lem4318574 _5131 _5132 P) (@lem4318573 _5131 _5132 P)). Qed.
Lemma lem4318677 {A B : Type'} (P : type1210 A B) : (term107 A B P) = (term108 A B P).
Proof. exact (@lem4318676 B A P). Qed.
Lemma lem4318678 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term109 A B C x f s t) = (term110 A B C x f s t).
Proof. exact (@lem4318677 A B (term111 A B C x f s t)). Qed.
Lemma lem4318679 {A B C : Type'} (x : C) (f : type1412 A B C) (x' : prod A B) (s : A -> Prop) (t : type1413 A B) : (term112 A B C x f s t x') = (term113 A B C x f x' s t).
Proof. exact (eq_refl (term112 A B C x f s t x')). Qed.
Lemma lem4318680 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term114 A B C x f s t) = (term111 A B C x f s t).
Proof. exact (fun_ext (fun x' : prod A B => @lem4318679 A B C x f x' s t)). Qed.
Lemma lem4318681 {A B : Type'} : (@ex (prod A B)) = (@ex (prod A B)).
Proof. exact (eq_refl (@ex (prod A B))). Qed.
Lemma lem4318682 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term109 A B C x f s t) = (term104 A B C x f s t).
Proof. exact (MK_COMB (@lem4318681 A B) (@lem4318680 A B C x f s t)). Qed.
Lemma lem4318683 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4318684 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term115 A B C x f s t) = (term116 A B C x f s t).
Proof. exact (MK_COMB (@lem4318683) (@lem4318682 A B C x f s t)). Qed.
Lemma lem4318685 {A B C : Type'} (x : C) (f : type1412 A B C) (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term117 A B C x f s t p1 p2) = (term118 A B C x f p1 p2 s t).
Proof. exact (eq_refl (term117 A B C x f s t p1 p2)). Qed.
Lemma lem4318686 {A B C : Type'} (x : C) (f : type1412 A B C) (p1 : A) (s : A -> Prop) (t : type1413 A B) : (term119 A B C x f s t p1) = (term120 A B C x f p1 s t).
Proof. exact (fun_ext (fun p2 : B => @lem4318685 A B C x f p1 p2 s t)). Qed.
Lemma lem4318687 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4318688 {A B C : Type'} (x : C) (f : type1412 A B C) (p1 : A) (s : A -> Prop) (t : type1413 A B) : (term121 A B C x f s t p1) = (term122 A B C x f p1 s t).
Proof. exact (MK_COMB (@lem4318687 B) (@lem4318686 A B C x f p1 s t)). Qed.
Lemma lem4318689 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term123 A B C x f s t) = (term124 A B C x f s t).
Proof. exact (fun_ext (fun p1 : A => @lem4318688 A B C x f p1 s t)). Qed.
Lemma lem4318690 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4318691 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term110 A B C x f s t) = (term125 A B C x f s t).
Proof. exact (MK_COMB (@lem4318690 A) (@lem4318689 A B C x f s t)). Qed.
Lemma lem4318692 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : ((term109 A B C x f s t) = (term110 A B C x f s t)) = ((term104 A B C x f s t) = (term125 A B C x f s t)).
Proof. exact (MK_COMB (@lem4318684 A B C x f s t) (@lem4318691 A B C x f s t)). Qed.
Lemma lem4318693 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term104 A B C x f s t) = (term125 A B C x f s t).
Proof. exact (EQ_MP (@lem4318692 A B C x f s t) (@lem4318678 A B C x f s t)). Qed.
Lemma lem4318700 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term103 A B C x f s t) = (term125 A B C x f s t).
Proof. exact (TRANS (@lem4318670 A B C x f s t) (@lem4318693 A B C x f s t)). Qed.
Lemma lem4318711 {A B : Type'} (a0 : A) (a1 : B) : a0 = (term126 A B a0 a1).
Proof. exact (@lem51128 A B a0 a1). Qed.
Lemma lem4318712 {A B : Type'} (x : A) (y : B) : x = (term126 A B x y).
Proof. exact (@lem4318711 A B x y). Qed.
Lemma lem4318713 {A B : Type'} (a0 : A) (a1 : B) : a1 = (term127 A B a0 a1).
Proof. exact (@lem51159 A B a0 a1). Qed.
Lemma lem4318714 {A B : Type'} (x : A) (y : B) : y = (term127 A B x y).
Proof. exact (@lem4318713 A B x y). Qed.
Lemma lem4318715 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4318716 {A : Type'} : (term128 A) = (term128 A).
Proof. exact (eq_refl (term128 A)). Qed.
Lemma lem4318717 {A B : Type'} (x : A) (y : B) : (term129 A x) = (term130 A B x y).
Proof. exact (MK_COMB (@lem4318716 A) (@lem4318712 A B x y)). Qed.
Lemma lem4318718 {A B : Type'} (x : A) (y : B) : (term130 A B x y) = (term126 A B x y).
Proof. exact (eq_refl (term130 A B x y)). Qed.
Lemma lem4318719 {A : Type'} (x : A) : (term131 A x) = (term131 A x).
Proof. exact (eq_refl (term131 A x)). Qed.
Lemma lem4318720 {A B : Type'} (x : A) (y : B) : ((term129 A x) = (term130 A B x y)) = ((term129 A x) = (term126 A B x y)).
Proof. exact (MK_COMB (@lem4318719 A x) (@lem4318718 A B x y)). Qed.
Lemma lem4318721 {A : Type'} (x : A) : (term129 A x) = x.
Proof. exact (eq_refl (term129 A x)). Qed.
Lemma lem4318722 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem4318723 {A : Type'} (x : A) : (term131 A x) = (@eq A x).
Proof. exact (MK_COMB (@lem4318722 A) (@lem4318721 A x)). Qed.
Lemma lem4318724 {A B : Type'} (x : A) (y : B) : (term126 A B x y) = (term126 A B x y).
Proof. exact (eq_refl (term126 A B x y)). Qed.
Lemma lem4318725 {A B : Type'} (x : A) (y : B) : ((term129 A x) = (term126 A B x y)) = (x = (term126 A B x y)).
Proof. exact (MK_COMB (@lem4318723 A x) (@lem4318724 A B x y)). Qed.
Lemma lem4318726 {A B : Type'} (x : A) (y : B) : ((term129 A x) = (term130 A B x y)) = (x = (term126 A B x y)).
Proof. exact (TRANS (@lem4318720 A B x y) (@lem4318725 A B x y)). Qed.
Lemma lem4318727 {A B : Type'} (x : A) (y : B) : x = (term126 A B x y).
Proof. exact (EQ_MP (@lem4318726 A B x y) (@lem4318717 A B x y)). Qed.
Lemma lem4318728 {A : Type'} (x : A) : (@eq A x) = (@eq A x).
Proof. exact (eq_refl (@eq A x)). Qed.
Lemma lem4318729 {A B : Type'} (x : A) (y : B) : (x = x) = (x = (term126 A B x y)).
Proof. exact (MK_COMB (@lem4318728 A x) (@lem4318727 A B x y)). Qed.
Lemma lem4318730 {A B : Type'} (x : A) (y : B) : x = (term126 A B x y).
Proof. exact (EQ_MP (@lem4318729 A B x y) (@lem4318715 A x)). Qed.
Lemma lem4318731 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4318732 {B : Type'} : (term128 B) = (term128 B).
Proof. exact (eq_refl (term128 B)). Qed.
Lemma lem4318733 {A B : Type'} (x : A) (y : B) : (term129 B y) = (term132 A B x y).
Proof. exact (MK_COMB (@lem4318732 B) (@lem4318714 A B x y)). Qed.
Lemma lem4318734 {A B : Type'} (x : A) (y : B) : (term132 A B x y) = (term127 A B x y).
Proof. exact (eq_refl (term132 A B x y)). Qed.
Lemma lem4318735 {B : Type'} (y : B) : (term131 B y) = (term131 B y).
Proof. exact (eq_refl (term131 B y)). Qed.
Lemma lem4318736 {A B : Type'} (x : A) (y : B) : ((term129 B y) = (term132 A B x y)) = ((term129 B y) = (term127 A B x y)).
Proof. exact (MK_COMB (@lem4318735 B y) (@lem4318734 A B x y)). Qed.
Lemma lem4318737 {B : Type'} (y : B) : (term129 B y) = y.
Proof. exact (eq_refl (term129 B y)). Qed.
Lemma lem4318738 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4318739 {B : Type'} (y : B) : (term131 B y) = (@eq B y).
Proof. exact (MK_COMB (@lem4318738 B) (@lem4318737 B y)). Qed.
Lemma lem4318740 {A B : Type'} (x : A) (y : B) : (term127 A B x y) = (term127 A B x y).
Proof. exact (eq_refl (term127 A B x y)). Qed.
Lemma lem4318741 {A B : Type'} (x : A) (y : B) : ((term129 B y) = (term127 A B x y)) = (y = (term127 A B x y)).
Proof. exact (MK_COMB (@lem4318739 B y) (@lem4318740 A B x y)). Qed.
Lemma lem4318742 {A B : Type'} (x : A) (y : B) : ((term129 B y) = (term132 A B x y)) = (y = (term127 A B x y)).
Proof. exact (TRANS (@lem4318736 A B x y) (@lem4318741 A B x y)). Qed.
Lemma lem4318743 {A B : Type'} (x : A) (y : B) : y = (term127 A B x y).
Proof. exact (EQ_MP (@lem4318742 A B x y) (@lem4318733 A B x y)). Qed.
Lemma lem4318744 {B : Type'} (y : B) : (@eq B y) = (@eq B y).
Proof. exact (eq_refl (@eq B y)). Qed.
Lemma lem4318745 {A B : Type'} (x : A) (y : B) : (y = y) = (y = (term127 A B x y)).
Proof. exact (MK_COMB (@lem4318744 B y) (@lem4318743 A B x y)). Qed.
Lemma lem4318746 {A B : Type'} (x : A) (y : B) : y = (term127 A B x y).
Proof. exact (EQ_MP (@lem4318745 A B x y) (@lem4318731 B y)). Qed.
Lemma lem4318747 {A B C : Type'} (f : type1412 A B C) : (term133 A B C f) = (term133 A B C f).
Proof. exact (eq_refl (term133 A B C f)). Qed.
Lemma lem4318748 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term134 A B C f x) = (term135 A B C f x y).
Proof. exact (MK_COMB (@lem4318747 A B C f) (@lem4318730 A B x y)). Qed.
Lemma lem4318749 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term135 A B C f x y) = (term136 A B C f x y).
Proof. exact (eq_refl (term135 A B C f x y)). Qed.
Lemma lem4318750 {A B C : Type'} (f : type1412 A B C) (x : A) : (term137 A B C f x) = (term137 A B C f x).
Proof. exact (eq_refl (term137 A B C f x)). Qed.
Lemma lem4318751 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term134 A B C f x) = (term135 A B C f x y)) = ((term134 A B C f x) = (term136 A B C f x y)).
Proof. exact (MK_COMB (@lem4318750 A B C f x) (@lem4318749 A B C f x y)). Qed.
Lemma lem4318752 {A B C : Type'} (f : type1412 A B C) (x : A) : (term134 A B C f x) = (term138 A B C f x).
Proof. exact (eq_refl (term134 A B C f x)). Qed.
Lemma lem4318753 {B C : Type'} : (@eq (B -> C)) = (@eq (B -> C)).
Proof. exact (eq_refl (@eq (B -> C))). Qed.
Lemma lem4318754 {A B C : Type'} (f : type1412 A B C) (x : A) : (term137 A B C f x) = (term139 A B C f x).
Proof. exact (MK_COMB (@lem4318753 B C) (@lem4318752 A B C f x)). Qed.
Lemma lem4318755 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term136 A B C f x y) = (term136 A B C f x y).
Proof. exact (eq_refl (term136 A B C f x y)). Qed.
Lemma lem4318756 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term134 A B C f x) = (term136 A B C f x y)) = ((term138 A B C f x) = (term136 A B C f x y)).
Proof. exact (MK_COMB (@lem4318754 A B C f x) (@lem4318755 A B C f x y)). Qed.
Lemma lem4318757 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term134 A B C f x) = (term135 A B C f x y)) = ((term138 A B C f x) = (term136 A B C f x y)).
Proof. exact (TRANS (@lem4318751 A B C f x y) (@lem4318756 A B C f x y)). Qed.
Lemma lem4318758 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term138 A B C f x) = (term136 A B C f x y).
Proof. exact (EQ_MP (@lem4318757 A B C f x y) (@lem4318748 A B C f x y)). Qed.
Lemma lem4318759 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term140 A B C f x y) = (term141 A B C f x y).
Proof. exact (MK_COMB (@lem4318758 A B C f x y) (@lem4318746 A B x y)). Qed.
Lemma lem4318760 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term141 A B C f x y) = (term142 A B C f x y).
Proof. exact (eq_refl (term141 A B C f x y)). Qed.
Lemma lem4318761 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term143 A B C f x y) = (term143 A B C f x y).
Proof. exact (eq_refl (term143 A B C f x y)). Qed.
Lemma lem4318762 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term140 A B C f x y) = (term141 A B C f x y)) = ((term140 A B C f x y) = (term142 A B C f x y)).
Proof. exact (MK_COMB (@lem4318761 A B C f x y) (@lem4318760 A B C f x y)). Qed.
Lemma lem4318763 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term140 A B C f x y) = (f x y).
Proof. exact (eq_refl (term140 A B C f x y)). Qed.
Lemma lem4318764 {C : Type'} : (@eq C) = (@eq C).
Proof. exact (eq_refl (@eq C)). Qed.
Lemma lem4318765 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term143 A B C f x y) = (term144 A B C f x y).
Proof. exact (MK_COMB (@lem4318764 C) (@lem4318763 A B C f x y)). Qed.
Lemma lem4318766 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term142 A B C f x y) = (term142 A B C f x y).
Proof. exact (eq_refl (term142 A B C f x y)). Qed.
Lemma lem4318767 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term140 A B C f x y) = (term142 A B C f x y)) = ((f x y) = (term142 A B C f x y)).
Proof. exact (MK_COMB (@lem4318765 A B C f x y) (@lem4318766 A B C f x y)). Qed.
Lemma lem4318768 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : ((term140 A B C f x y) = (term141 A B C f x y)) = ((f x y) = (term142 A B C f x y)).
Proof. exact (TRANS (@lem4318762 A B C f x y) (@lem4318767 A B C f x y)). Qed.
Lemma lem4318769 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (f x y) = (term142 A B C f x y).
Proof. exact (EQ_MP (@lem4318768 A B C f x y) (@lem4318759 A B C f x y)). Qed.
Lemma lem4318770 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term142 A B C f x y) = (f x y).
Proof. exact (SYM (@lem4318769 A B C f x y)). Qed.
Lemma lem4318771 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term145 A B C f x y) = (term142 A B C f x y).
Proof. exact (eq_refl (term145 A B C f x y)). Qed.
Lemma lem4318772 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term145 A B C f x y) = (f x y).
Proof. exact (TRANS (@lem4318771 A B C f x y) (@lem4318770 A B C f x y)). Qed.
Lemma lem4318773 {A B C : Type'} (f : type1412 A B C) (x : A) : term146 A B C f x.
Proof. exact (fun y : B => @lem4318772 A B C f x y). Qed.
Lemma lem4318774 {A B C : Type'} (f : type1412 A B C) : term147 A B C f.
Proof. exact (fun x : A => @lem4318773 A B C f x). Qed.
Lemma lem4318775 {A B C : Type'} (f : type1412 A B C) : term148 A B C f.
Proof. exact (ex_intro (term149 A B C f) (term150 A B C f) (@lem4318774 A B C f)). Qed.
Lemma lem4318777 {A : Type'} (a : A) (b : A) : (a = b) = (@GEQ A a b).
Proof. exact (EQ_MP (@lem48806 A a b) (@lem48805 A a b)). Qed.
Lemma lem4318778 {C : Type'} (a : C) (b : C) : (a = b) = (@GEQ C a b).
Proof. exact (@lem4318777 C a b). Qed.
Lemma lem4318779 {A B C : Type'} (_49136 : type1209 A B C) (f : type1412 A B C) (x : A) (y : B) : ((term151 A B C _49136 x y) = (f x y)) = (term152 A B C _49136 f x y).
Proof. exact (@lem4318778 C (term151 A B C _49136 x y) (f x y)). Qed.
Lemma lem4318780 {A B C : Type'} (_49136 : type1209 A B C) (f : type1412 A B C) (x : A) : (term153 A B C _49136 f x) = (term154 A B C _49136 f x).
Proof. exact (fun_ext (fun y : B => @lem4318779 A B C _49136 f x y)). Qed.
Lemma lem4318781 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4318782 {A B C : Type'} (_49136 : type1209 A B C) (f : type1412 A B C) (x : A) : (term155 A B C _49136 f x) = (term156 A B C _49136 f x).
Proof. exact (MK_COMB (@lem4318781 B) (@lem4318780 A B C _49136 f x)). Qed.
Lemma lem4318783 {A B C : Type'} (_49136 : type1209 A B C) (f : type1412 A B C) : (term157 A B C _49136 f) = (term158 A B C _49136 f).
Proof. exact (fun_ext (fun x : A => @lem4318782 A B C _49136 f x)). Qed.
Lemma lem4318784 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4318785 {A B C : Type'} (_49136 : type1209 A B C) (f : type1412 A B C) : (term159 A B C _49136 f) = (term160 A B C _49136 f).
Proof. exact (MK_COMB (@lem4318784 A) (@lem4318783 A B C _49136 f)). Qed.
Lemma lem4318786 {A B C : Type'} (f : type1412 A B C) : (term149 A B C f) = (term161 A B C f).
Proof. exact (fun_ext (fun _49136 : type1209 A B C => @lem4318785 A B C _49136 f)). Qed.
Lemma lem4318787 {A B C : Type'} : (@ex ((prod A B) -> C)) = (@ex ((prod A B) -> C)).
Proof. exact (eq_refl (@ex ((prod A B) -> C))). Qed.
Lemma lem4318788 {A B C : Type'} (f : type1412 A B C) : (term148 A B C f) = (term162 A B C f).
Proof. exact (MK_COMB (@lem4318787 A B C) (@lem4318786 A B C f)). Qed.
Lemma lem4318789 {A B C : Type'} (f : type1412 A B C) : term162 A B C f.
Proof. exact (EQ_MP (@lem4318788 A B C f) (@lem4318775 A B C f)). Qed.
Lemma lem4318791 {_5076 : Type'} (P : _5076 -> Prop) : term163 _5076 P.
Proof. exact (EQ_MP (@lem48920 _5076 P) (@lem0)). Qed.
Lemma lem4318792 {A B C : Type'} (P : type322 A B C) : term164 A B C P.
Proof. exact (@lem4318791 (type1209 A B C) P). Qed.
Lemma lem4318793 {A B C : Type'} (f : type1412 A B C) : term165 A B C f.
Proof. exact (@lem4318792 A B C (term161 A B C f)). Qed.
Lemma lem4318794 {A B C : Type'} (f : type1412 A B C) : term166 A B C f.
Proof. exact (@lem4318793 A B C f (@lem4318789 A B C f)). Qed.
Lemma lem4318795 {A B C : Type'} (f : type1412 A B C) : (term166 A B C f) = (term167 A B C f).
Proof. exact (eq_refl (term166 A B C f)). Qed.
Lemma lem4318796 {A B C : Type'} (f : type1412 A B C) : term167 A B C f.
Proof. exact (EQ_MP (@lem4318795 A B C f) (@lem4318794 A B C f)). Qed.
Lemma lem4318797 {A B C : Type'} (f : type1412 A B C) (x : A) : term168 A B C f x.
Proof. exact (@lem4318796 A B C f x). Qed.
Lemma lem4318798 {A B C : Type'} (f : type1412 A B C) (x : A) : (term168 A B C f x) = (term169 A B C f x).
Proof. exact (eq_refl (term168 A B C f x)). Qed.
Lemma lem4318799 {A B C : Type'} (f : type1412 A B C) (x : A) : term169 A B C f x.
Proof. exact (EQ_MP (@lem4318798 A B C f x) (@lem4318797 A B C f x)). Qed.
Lemma lem4318800 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : term170 A B C f x y.
Proof. exact (@lem4318799 A B C f x y). Qed.
Lemma lem4318801 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term170 A B C f x y) = (term171 A B C f x y).
Proof. exact (eq_refl (term170 A B C f x y)). Qed.
Lemma lem4318802 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : term171 A B C f x y.
Proof. exact (EQ_MP (@lem4318801 A B C f x y) (@lem4318800 A B C f x y)). Qed.
Lemma lem4318804 {A : Type'} (a : A) (b : A) : (@GEQ A a b) = (a = b).
Proof. exact (EQ_MP (@lem48812 A a b) (@lem48811 A a b)). Qed.
Lemma lem4318805 {C : Type'} (a : C) (b : C) : (@GEQ C a b) = (a = b).
Proof. exact (@lem4318804 C a b). Qed.
Lemma lem4318806 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term171 A B C f x y) = ((term172 A B C f x y) = (f x y)).
Proof. exact (@lem4318805 C (term172 A B C f x y) (f x y)). Qed.
Lemma lem4318807 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term172 A B C f x y) = (f x y).
Proof. exact (EQ_MP (@lem4318806 A B C f x y) (@lem4318802 A B C f x y)). Qed.
Lemma lem4318808 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term172 A B C f x y) = (f x y).
Proof. exact (@lem4318807 A B C f x y). Qed.
Lemma lem4318809 {A B C : Type'} (f : type1412 A B C) (p1 : A) (p2 : B) : (term172 A B C f p1 p2) = (f p1 p2).
Proof. exact (@lem4318808 A B C f p1 p2). Qed.
Lemma lem4318810 {C : Type'} (x : C) : (@eq C x) = (@eq C x).
Proof. exact (eq_refl (@eq C x)). Qed.
Lemma lem4318811 {A B C : Type'} (x : C) (f : type1412 A B C) (p1 : A) (p2 : B) : (x = (term172 A B C f p1 p2)) = (x = (f p1 p2)).
Proof. exact (MK_COMB (@lem4318810 C x) (@lem4318809 A B C f p1 p2)). Qed.
Lemma lem4318814 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4318815 {A B C : Type'} (x : C) (f : type1412 A B C) (p1 : A) (p2 : B) : (term173 A B C x f p1 p2) = (term174 A B C x f p1 p2).
Proof. exact (MK_COMB (@lem4318814) (@lem4318811 A B C x f p1 p2)). Qed.
Lemma lem4318817 {_88435 _88436 : Type'} (P : type1470 _88435 _88436) (a : _88436) (b : _88435) : (term73 _88435 _88436 a b P) = (P a b).
Proof. exact (EQ_MP (@lem4318571 _88435 _88436 P a b) (@lem4318570 _88435 _88436 P a b)). Qed.
Lemma lem4318818 {A B : Type'} (P : type1413 A B) (a : A) (b : B) : (term175 A B a b P) = (P a b).
Proof. exact (@lem4318817 B A P a b). Qed.
Lemma lem4318819 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term176 A B p1 p2 s t) = (term177 A B s t p1 p2).
Proof. exact (@lem4318818 A B (term178 A B s t) p1 p2). Qed.
Lemma lem4318820 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term179 A B s t x) = (term180 A B s t x).
Proof. exact (eq_refl (term179 A B s t x)). Qed.
Lemma lem4318821 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4318822 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term177 A B s t x y) = (term181 A B s t x y).
Proof. exact (MK_COMB (@lem4318820 A B s t x) (@lem4318821 B y)). Qed.
Lemma lem4318823 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term181 A B s t x y) = (term182 A B s y t x).
Proof. exact (eq_refl (term181 A B s t x y)). Qed.
Lemma lem4318824 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term177 A B s t x y) = (term182 A B s y t x).
Proof. exact (TRANS (@lem4318822 A B s t x y) (@lem4318823 A B s y t x)). Qed.
Lemma lem4318825 {A B : Type'} (GEN_PVAR_125 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_125) = (@SETSPEC (prod A B) GEN_PVAR_125).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_125)). Qed.
Lemma lem4318826 {A B : Type'} (GEN_PVAR_125 : prod A B) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term183 A B GEN_PVAR_125 s t x y) = (term184 A B GEN_PVAR_125 s y t x).
Proof. exact (MK_COMB (@lem4318825 A B GEN_PVAR_125) (@lem4318824 A B s y t x)). Qed.
Lemma lem4318827 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4318828 {A B : Type'} (GEN_PVAR_125 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term185 A B GEN_PVAR_125 s t x y) = (term186 A B GEN_PVAR_125 s t x y).
Proof. exact (MK_COMB (@lem4318826 A B GEN_PVAR_125 s y t x) (@lem4318827 A B x y)). Qed.
Lemma lem4318829 {A B : Type'} (GEN_PVAR_125 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term187 A B GEN_PVAR_125 s t x) = (term188 A B GEN_PVAR_125 s t x).
Proof. exact (fun_ext (fun y : B => @lem4318828 A B GEN_PVAR_125 s t x y)). Qed.
Lemma lem4318830 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4318831 {A B : Type'} (GEN_PVAR_125 : prod A B) (s : A -> Prop) (t : type1413 A B) (x : A) : (term189 A B GEN_PVAR_125 s t x) = (term190 A B GEN_PVAR_125 s t x).
Proof. exact (MK_COMB (@lem4318830 B) (@lem4318829 A B GEN_PVAR_125 s t x)). Qed.
Lemma lem4318832 {A B : Type'} (GEN_PVAR_125 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term191 A B GEN_PVAR_125 s t) = (term192 A B GEN_PVAR_125 s t).
Proof. exact (fun_ext (fun x : A => @lem4318831 A B GEN_PVAR_125 s t x)). Qed.
Lemma lem4318833 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4318834 {A B : Type'} (GEN_PVAR_125 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term193 A B GEN_PVAR_125 s t) = (term194 A B GEN_PVAR_125 s t).
Proof. exact (MK_COMB (@lem4318833 A) (@lem4318832 A B GEN_PVAR_125 s t)). Qed.
Lemma lem4318835 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term195 A B s t) = (term196 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_125 : prod A B => @lem4318834 A B GEN_PVAR_125 s t)). Qed.
Lemma lem4318836 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4318837 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term197 A B s t) = (term106 A B s t).
Proof. exact (MK_COMB (@lem4318836 A B) (@lem4318835 A B s t)). Qed.
Lemma lem4318838 {A B : Type'} (p1 : A) (p2 : B) : (term198 A B p1 p2) = (term198 A B p1 p2).
Proof. exact (eq_refl (term198 A B p1 p2)). Qed.
Lemma lem4318839 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term176 A B p1 p2 s t) = (term199 A B p1 p2 s t).
Proof. exact (MK_COMB (@lem4318838 A B p1 p2) (@lem4318837 A B s t)). Qed.
Lemma lem4318840 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4318841 {A B : Type'} (p1 : A) (p2 : B) (s : A -> Prop) (t : type1413 A B) : (term200 A B p1 p2 s t) = (term201 A B p1 p2 s t).
Proof. exact (MK_COMB (@lem4318840) (@lem4318839 A B p1 p2 s t)). Qed.
Lemma lem4318842 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term179 A B s t p1) = (term180 A B s t p1).
Proof. exact (eq_refl (term179 A B s t p1)). Qed.
Lemma lem4318843 {B : Type'} (p2 : B) : p2 = p2.
Proof. exact (eq_refl p2). Qed.
Lemma lem4318844 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (p1 : A) (p2 : B) : (term177 A B s t p1 p2) = (term181 A B s t p1 p2).
Proof. exact (MK_COMB (@lem4318842 A B s t p1) (@lem4318843 B p2)). Qed.
Lemma lem4318845 {A B : Type'} (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term181 A B s t p1 p2) = (term182 A B s p2 t p1).
Proof. exact (eq_refl (term181 A B s t p1 p2)). Qed.
Lemma lem4318846 {A B : Type'} (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term177 A B s t p1 p2) = (term182 A B s p2 t p1).
Proof. exact (TRANS (@lem4318844 A B s t p1 p2) (@lem4318845 A B s p2 t p1)). Qed.
Lemma lem4318847 {A B : Type'} (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : ((term176 A B p1 p2 s t) = (term177 A B s t p1 p2)) = ((term199 A B p1 p2 s t) = (term182 A B s p2 t p1)).
Proof. exact (MK_COMB (@lem4318841 A B p1 p2 s t) (@lem4318846 A B s p2 t p1)). Qed.
Lemma lem4318848 {A B : Type'} (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term199 A B p1 p2 s t) = (term182 A B s p2 t p1).
Proof. exact (EQ_MP (@lem4318847 A B s p2 t p1) (@lem4318819 A B s t p1 p2)). Qed.
Lemma lem4318851 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term118 A B C x f p1 p2 s t) = (term202 A B C x f s p2 t p1).
Proof. exact (MK_COMB (@lem4318815 A B C x f p1 p2) (@lem4318848 A B s p2 t p1)). Qed.
Lemma lem4318854 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term120 A B C x f p1 s t) = (term203 A B C x f s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem4318851 A B C x f s p2 t p1)). Qed.
Lemma lem4318855 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4318856 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term122 A B C x f p1 s t) = (term204 A B C x f s t p1).
Proof. exact (MK_COMB (@lem4318855 B) (@lem4318854 A B C x f s t p1)). Qed.
Lemma lem4318863 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term124 A B C x f s t) = (term205 A B C x f s t).
Proof. exact (fun_ext (fun p1 : A => @lem4318856 A B C x f s t p1)). Qed.
Lemma lem4318864 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4318865 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term125 A B C x f s t) = (term206 A B C x f s t).
Proof. exact (MK_COMB (@lem4318864 A) (@lem4318863 A B C x f s t)). Qed.
Lemma lem4318872 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term103 A B C x f s t) = (term206 A B C x f s t).
Proof. exact (TRANS (@lem4318700 A B C x f s t) (@lem4318865 A B C x f s t)). Qed.
Lemma lem4318873 {A B C : Type'} (x : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term207 A B C x s t f) = (term207 A B C x s t f).
Proof. exact (eq_refl (term207 A B C x s t f)). Qed.
Lemma lem4318874 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term208 A B C x f s t) = (term209 A B C x f s t).
Proof. exact (MK_COMB (@lem4318873 A B C x s t f) (@lem4318872 A B C x f s t)). Qed.
Lemma lem4318877 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term210 A B C f s t) = (term211 A B C f s t).
Proof. exact (fun_ext (fun x : C => @lem4318874 A B C x f s t)). Qed.
Lemma lem4318878 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4318879 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term99 A B C f s t) = (term212 A B C f s t).
Proof. exact (MK_COMB (@lem4318878 C) (@lem4318877 A B C f s t)). Qed.
Lemma lem4318884 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term98 A B C f s t) = (term212 A B C f s t).
Proof. exact (TRANS (@lem4318646 A B C f s t) (@lem4318879 A B C f s t)). Qed.
Lemma lem4318885 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term213 A B C f s t) = (term213 A B C f s t).
Proof. exact (eq_refl (term213 A B C f s t)). Qed.
Lemma lem4318886 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term214 A B C f s t) = (term215 A B C f s t).
Proof. exact (MK_COMB (@lem4318885 A B C f s t) (@lem4318884 A B C f s t)). Qed.
Lemma lem4318889 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term215 A B C f s t) = (term214 A B C f s t).
Proof. exact (SYM (@lem4318886 A B C f s t)). Qed.
Lemma lem4318911 {_88961 _88962 _89106 : Type'} (P : type1470 _88961 _88962) (Q : _89106 -> Prop) (f : type1469 _88961 _88962 _89106) : (term66 _88961 _88962 _89106 P f Q) = (term67 _88961 _88962 _89106 P Q f).
Proof. exact (EQ_MP (@lem4318555 _88961 _88962 _89106 P Q f) (@lem4318554 _88961 _88962 _89106 P Q f)). Qed.
Lemma lem4318912 {A B C : Type'} (P : type1413 A B) (Q : C -> Prop) (f : type1412 A B C) : (term216 A B C P f Q) = (term217 A B C P Q f).
Proof. exact (@lem4318911 B A C P Q f). Qed.
Lemma lem4318913 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term218 A B C f s t) = (term219 A B C s t f).
Proof. exact (@lem4318912 A B C (term178 A B s t) (term220 A B C f s t) f). Qed.
Lemma lem4318914 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term179 A B s t x) = (term180 A B s t x).
Proof. exact (eq_refl (term179 A B s t x)). Qed.
Lemma lem4318915 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4318916 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term177 A B s t x y) = (term181 A B s t x y).
Proof. exact (MK_COMB (@lem4318914 A B s t x) (@lem4318915 B y)). Qed.
Lemma lem4318917 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term181 A B s t x y) = (term182 A B s y t x).
Proof. exact (eq_refl (term181 A B s t x y)). Qed.
Lemma lem4318918 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term177 A B s t x y) = (term182 A B s y t x).
Proof. exact (TRANS (@lem4318916 A B s t x y) (@lem4318917 A B s y t x)). Qed.
Lemma lem4318919 {C : Type'} (GEN_PVAR_126 : C) : (@SETSPEC C GEN_PVAR_126) = (@SETSPEC C GEN_PVAR_126).
Proof. exact (eq_refl (@SETSPEC C GEN_PVAR_126)). Qed.
Lemma lem4318920 {A B C : Type'} (GEN_PVAR_126 : C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term221 A B C GEN_PVAR_126 s t x y) = (term222 A B C GEN_PVAR_126 s y t x).
Proof. exact (MK_COMB (@lem4318919 C GEN_PVAR_126) (@lem4318918 A B s y t x)). Qed.
Lemma lem4318921 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (f x y) = (f x y).
Proof. exact (eq_refl (f x y)). Qed.
Lemma lem4318922 {A B C : Type'} (GEN_PVAR_126 : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) (x : A) (y : B) : (term223 A B C GEN_PVAR_126 s t f x y) = (term224 A B C GEN_PVAR_126 s t f x y).
Proof. exact (MK_COMB (@lem4318920 A B C GEN_PVAR_126 s y t x) (@lem4318921 A B C f x y)). Qed.
Lemma lem4318923 {A B C : Type'} (GEN_PVAR_126 : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) (x : A) : (term225 A B C GEN_PVAR_126 s t f x) = (term226 A B C GEN_PVAR_126 s t f x).
Proof. exact (fun_ext (fun y : B => @lem4318922 A B C GEN_PVAR_126 s t f x y)). Qed.
Lemma lem4318924 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4318925 {A B C : Type'} (GEN_PVAR_126 : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) (x : A) : (term227 A B C GEN_PVAR_126 s t f x) = (term228 A B C GEN_PVAR_126 s t f x).
Proof. exact (MK_COMB (@lem4318924 B) (@lem4318923 A B C GEN_PVAR_126 s t f x)). Qed.
Lemma lem4318926 {A B C : Type'} (GEN_PVAR_126 : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term229 A B C GEN_PVAR_126 s t f) = (term230 A B C GEN_PVAR_126 s t f).
Proof. exact (fun_ext (fun x : A => @lem4318925 A B C GEN_PVAR_126 s t f x)). Qed.
Lemma lem4318927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4318928 {A B C : Type'} (GEN_PVAR_126 : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term231 A B C GEN_PVAR_126 s t f) = (term232 A B C GEN_PVAR_126 s t f).
Proof. exact (MK_COMB (@lem4318927 A) (@lem4318926 A B C GEN_PVAR_126 s t f)). Qed.
Lemma lem4318929 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term233 A B C s t f) = (term234 A B C s t f).
Proof. exact (fun_ext (fun GEN_PVAR_126 : C => @lem4318928 A B C GEN_PVAR_126 s t f)). Qed.
Lemma lem4318930 {C : Type'} : (@GSPEC C) = (@GSPEC C).
Proof. exact (eq_refl (@GSPEC C)). Qed.
Lemma lem4318931 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term235 A B C s t f) = (term97 A B C s t f).
Proof. exact (MK_COMB (@lem4318930 C) (@lem4318929 A B C s t f)). Qed.
Lemma lem4318932 {C : Type'} (x : C) : (@IN C x) = (@IN C x).
Proof. exact (eq_refl (@IN C x)). Qed.
Lemma lem4318933 {A B C : Type'} (x : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term236 A B C x s t f) = (term237 A B C x s t f).
Proof. exact (MK_COMB (@lem4318932 C x) (@lem4318931 A B C s t f)). Qed.
Lemma lem4318934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4318935 {A B C : Type'} (x : C) (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : (term238 A B C x s t f) = (term207 A B C x s t f).
Proof. exact (MK_COMB (@lem4318934) (@lem4318933 A B C x s t f)). Qed.
Lemma lem4318936 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term239 A B C f s t x) = (term206 A B C x f s t).
Proof. exact (eq_refl (term239 A B C f s t x)). Qed.
Lemma lem4318937 {A B C : Type'} (x : C) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term240 A B C f s t x) = (term209 A B C x f s t).
Proof. exact (MK_COMB (@lem4318935 A B C x s t f) (@lem4318936 A B C x f s t)). Qed.
Lemma lem4318938 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term241 A B C f s t) = (term211 A B C f s t).
Proof. exact (fun_ext (fun x : C => @lem4318937 A B C x f s t)). Qed.
Lemma lem4318939 {C : Type'} : (@all C) = (@all C).
Proof. exact (eq_refl (@all C)). Qed.
Lemma lem4318940 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term218 A B C f s t) = (term212 A B C f s t).
Proof. exact (MK_COMB (@lem4318939 C) (@lem4318938 A B C f s t)). Qed.
Lemma lem4318941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4318942 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term242 A B C f s t) = (term243 A B C f s t).
Proof. exact (MK_COMB (@lem4318941) (@lem4318940 A B C f s t)). Qed.
Lemma lem4318943 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) : (term179 A B s t x) = (term180 A B s t x).
Proof. exact (eq_refl (term179 A B s t x)). Qed.
Lemma lem4318944 {B : Type'} (y : B) : y = y.
Proof. exact (eq_refl y). Qed.
Lemma lem4318945 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : A) (y : B) : (term177 A B s t x y) = (term181 A B s t x y).
Proof. exact (MK_COMB (@lem4318943 A B s t x) (@lem4318944 B y)). Qed.
Lemma lem4318946 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term181 A B s t x y) = (term182 A B s y t x).
Proof. exact (eq_refl (term181 A B s t x y)). Qed.
Lemma lem4318947 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term177 A B s t x y) = (term182 A B s y t x).
Proof. exact (TRANS (@lem4318945 A B s t x y) (@lem4318946 A B s y t x)). Qed.
Lemma lem4318948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4318949 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term244 A B s t x y) = (term245 A B s y t x).
Proof. exact (MK_COMB (@lem4318948) (@lem4318947 A B s y t x)). Qed.
Lemma lem4318950 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term246 A B C s t f x y) = (term247 A B C x y f s t).
Proof. exact (eq_refl (term246 A B C s t f x y)). Qed.
Lemma lem4318951 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term248 A B C s t f x y) = (term249 A B C x y f s t).
Proof. exact (MK_COMB (@lem4318949 A B s y t x) (@lem4318950 A B C x y f s t)). Qed.
Lemma lem4318952 {A B C : Type'} (x : A) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term250 A B C s t f x) = (term251 A B C x f s t).
Proof. exact (fun_ext (fun y : B => @lem4318951 A B C x y f s t)). Qed.
Lemma lem4318953 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4318954 {A B C : Type'} (x : A) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term252 A B C s t f x) = (term253 A B C x f s t).
Proof. exact (MK_COMB (@lem4318953 B) (@lem4318952 A B C x f s t)). Qed.
Lemma lem4318955 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term254 A B C s t f) = (term255 A B C f s t).
Proof. exact (fun_ext (fun x : A => @lem4318954 A B C x f s t)). Qed.
Lemma lem4318956 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4318957 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term219 A B C s t f) = (term256 A B C f s t).
Proof. exact (MK_COMB (@lem4318956 A) (@lem4318955 A B C f s t)). Qed.
Lemma lem4318958 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : ((term218 A B C f s t) = (term219 A B C s t f)) = ((term212 A B C f s t) = (term256 A B C f s t)).
Proof. exact (MK_COMB (@lem4318942 A B C f s t) (@lem4318957 A B C f s t)). Qed.
Lemma lem4318959 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term212 A B C f s t) = (term256 A B C f s t).
Proof. exact (EQ_MP (@lem4318958 A B C f s t) (@lem4318913 A B C s t f)). Qed.
Lemma lem4318986 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term213 A B C f s t) = (term213 A B C f s t).
Proof. exact (eq_refl (term213 A B C f s t)). Qed.
Lemma lem4318987 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term215 A B C f s t) = (term257 A B C f s t).
Proof. exact (MK_COMB (@lem4318986 A B C f s t) (@lem4318959 A B C f s t)). Qed.
Lemma lem4318990 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term257 A B C f s t) = (term215 A B C f s t).
Proof. exact (SYM (@lem4318987 A B C f s t)). Qed.
Lemma lem4318992 {A B : Type'} (f : A -> B) (s : A -> Prop) : term57 A B f s.
Proof. exact (EQ_MP (@lem4318532 A B f s) (@lem4318531 A B f s)). Qed.
Lemma lem4318993 {A B C : Type'} (f : type1209 A B C) (s : type1210 A B) : term258 A B C f s.
Proof. exact (@lem4318992 (prod A B) C f s). Qed.
Lemma lem4318994 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term259 A B C f s t.
Proof. exact (@lem4318993 A B C (term105 A B C f) (term106 A B s t)). Qed.
Lemma lem4318996 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4318997 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term256 A B C f s t) = (term261 A B C f s t).
Proof. exact (@lem4318996 (term256 A B C f s t)). Qed.
Lemma lem4318998 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term261 A B C f s t) = (term256 A B C f s t).
Proof. exact (SYM (@lem4318997 A B C f s t)). Qed.
Lemma lem4318999 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term262 A B C f s t) : term262 A B C f s t.
Proof. exact (h1). Qed.
Lemma lem4319002 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term261 A B C f s t) : term261 A B C f s t.
Proof. exact (h1). Qed.
Lemma lem4319003 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term263 A B C f s t.
Proof. exact (fun h0 : term261 A B C f s t => @lem4319002 A B C f s t h0). Qed.
Lemma lem4319004 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term263 A B C f s t) : term263 A B C f s t.
Proof. exact (h1). Qed.
Lemma lem4319005 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term261 A B C f s t) : term261 A B C f s t.
Proof. exact (h1). Qed.
Lemma lem4319006 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term261 A B C f s t) (h2 : term263 A B C f s t) : term261 A B C f s t.
Proof. exact (@lem4319004 A B C f s t h2 (@lem4319005 A B C f s t h1)). Qed.
Lemma lem4319007 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term261 A B C f s t) : term264 A B C f s t.
Proof. exact (fun h0 : term263 A B C f s t => @lem4319006 A B C f s t h1 h0). Qed.
Lemma lem4319008 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term263 A B C f s t) : term263 A B C f s t.
Proof. exact (h1). Qed.
Lemma lem4319009 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term261 A B C f s t) (h2 : term263 A B C f s t) : term261 A B C f s t.
Proof. exact (@lem4319007 A B C f s t h1 (@lem4319008 A B C f s t h2)). Qed.
Lemma lem4319010 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term263 A B C f s t) : term263 A B C f s t.
Proof. exact (fun h0 : term261 A B C f s t => @lem4319009 A B C f s t h0 h1). Qed.
Lemma lem4319011 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term265 A B C f s t.
Proof. exact (fun h0 : term263 A B C f s t => @lem4319010 A B C f s t h0). Qed.
Lemma lem4319014 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term263 A B C f s t.
Proof. exact (@lem4319011 A B C f s t (@lem4319003 A B C f s t)). Qed.
Lemma lem4319015 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term263 A B C f s t.
Proof. exact (@lem4319014 A B C f s t). Qed.
Lemma lem4319029 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4319030 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term261 A B C f s t) = (term266 A B C f s t).
Proof. exact (@lem4319029 (term262 A B C f s t)). Qed.
Lemma lem4319032 (t : Prop) : (term267 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4319033 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term266 A B C f s t) = (term256 A B C f s t).
Proof. exact (@lem4319032 (term256 A B C f s t)). Qed.
Lemma lem4319038 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term261 A B C f s t) = (term256 A B C f s t).
Proof. exact (TRANS (@lem4319030 A B C f s t) (@lem4319033 A B C f s t)). Qed.
Lemma lem4319103 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term268 A B C s t) = (term269 A B C s t).
Proof. exact (fun_ext (fun f : type1412 A B C => @lem4319038 A B C f s t)). Qed.
Lemma lem4319104 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem4319105 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term270 A B C s t) = (term271 A B C s t).
Proof. exact (MK_COMB (@lem4319104 A B C) (@lem4319103 A B C s t)). Qed.
Lemma lem4319110 {A B C : Type'} (t : type1413 A B) : (term272 A B C t) = (term273 A B C t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4319105 A B C s t)). Qed.
Lemma lem4319111 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4319112 {A B C : Type'} (t : type1413 A B) : (term274 A B C t) = (term275 A B C t).
Proof. exact (MK_COMB (@lem4319111 A) (@lem4319110 A B C t)). Qed.
Lemma lem4319117 {A B C : Type'} : (term276 A B C) = (term277 A B C).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4319112 A B C t)). Qed.
Lemma lem4319118 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4319127 {A B C : Type'} : (term278 A B C) = (term279 A B C).
Proof. exact (MK_COMB (@lem4319118 A B) (@lem4319117 A B C)). Qed.
Lemma lem4319136 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term280 A B C x y f s p2 t p1) = (term280 A B C x y f s p2 t p1).
Proof. exact (eq_refl (term280 A B C x y f s p2 t p1)). Qed.
Lemma lem4319137 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term281 A B C x y f s t p1) = (term281 A B C x y f s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem4319136 A B C x y f s p2 t p1)). Qed.
Lemma lem4319138 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4319139 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term282 A B C x y f s t p1) = (term282 A B C x y f s t p1).
Proof. exact (MK_COMB (@lem4319138 B) (@lem4319137 A B C x y f s t p1)). Qed.
Lemma lem4319140 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term283 A B C x y f s t) = (term283 A B C x y f s t).
Proof. exact (fun_ext (fun p1 : A => @lem4319139 A B C x y f s t p1)). Qed.
Lemma lem4319141 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4319142 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term247 A B C x y f s t) = (term247 A B C x y f s t).
Proof. exact (MK_COMB (@lem4319141 A) (@lem4319140 A B C x y f s t)). Qed.
Lemma lem4319149 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term245 A B s y t x) = (term245 A B s y t x).
Proof. exact (eq_refl (term245 A B s y t x)). Qed.
Lemma lem4319150 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term249 A B C x y f s t) = (term249 A B C x y f s t).
Proof. exact (MK_COMB (@lem4319149 A B s y t x) (@lem4319142 A B C x y f s t)). Qed.
Lemma lem4319151 {A B C : Type'} (x : A) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term251 A B C x f s t) = (term251 A B C x f s t).
Proof. exact (fun_ext (fun y : B => @lem4319150 A B C x y f s t)). Qed.
Lemma lem4319152 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4319153 {A B C : Type'} (x : A) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term253 A B C x f s t) = (term253 A B C x f s t).
Proof. exact (MK_COMB (@lem4319152 B) (@lem4319151 A B C x f s t)). Qed.
Lemma lem4319154 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term255 A B C f s t) = (term255 A B C f s t).
Proof. exact (fun_ext (fun x : A => @lem4319153 A B C x f s t)). Qed.
Lemma lem4319155 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4319156 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term256 A B C f s t) = (term256 A B C f s t).
Proof. exact (MK_COMB (@lem4319155 A) (@lem4319154 A B C f s t)). Qed.
Lemma lem4319157 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term269 A B C s t) = (term269 A B C s t).
Proof. exact (fun_ext (fun f : type1412 A B C => @lem4319156 A B C f s t)). Qed.
Lemma lem4319158 {A B C : Type'} : (@all (A -> B -> C)) = (@all (A -> B -> C)).
Proof. exact (eq_refl (@all (A -> B -> C))). Qed.
Lemma lem4319159 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term271 A B C s t) = (term271 A B C s t).
Proof. exact (MK_COMB (@lem4319158 A B C) (@lem4319157 A B C s t)). Qed.
Lemma lem4319160 {A B C : Type'} (t : type1413 A B) : (term273 A B C t) = (term273 A B C t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4319159 A B C s t)). Qed.
Lemma lem4319161 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4319162 {A B C : Type'} (t : type1413 A B) : (term275 A B C t) = (term275 A B C t).
Proof. exact (MK_COMB (@lem4319161 A) (@lem4319160 A B C t)). Qed.
Lemma lem4319163 {A B C : Type'} : (term277 A B C) = (term277 A B C).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4319162 A B C t)). Qed.
Lemma lem4319164 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4319165 {A B C : Type'} : (term279 A B C) = (term279 A B C).
Proof. exact (MK_COMB (@lem4319164 A B) (@lem4319163 A B C)). Qed.
Lemma lem4319218 {A B C : Type'} : (term278 A B C) = (term279 A B C).
Proof. exact (TRANS (@lem4319127 A B C) (@lem4319165 A B C)). Qed.
Lemma lem4319219 {A B C : Type'} : (term279 A B C) = (term278 A B C).
Proof. exact (SYM (@lem4319218 A B C)). Qed.
Lemma lem4319222 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4319223 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term247 A B C x y f s t) = (term284 A B C x y f s t).
Proof. exact (@lem4319222 (term247 A B C x y f s t)). Qed.
Lemma lem4319224 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term284 A B C x y f s t) = (term247 A B C x y f s t).
Proof. exact (SYM (@lem4319223 A B C x y f s t)). Qed.
Lemma lem4319225 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term285 A B C x y f s t.
Proof. exact (h1). Qed.
Lemma lem4319235 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term182 A B s y t x.
Proof. exact (h1). Qed.
Lemma lem4319243 {A B : Type'} (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term286 A B s p2 t p1) = (term287 A B s p2 t p1).
Proof. exact (@lem17045 (@IN A p1 s) (term288 A B p2 t p1)). Qed.
Lemma lem4319245 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (p1 : A) (p2 : B) : (term289 A B C x y f p1 p2) = (term289 A B C x y f p1 p2).
Proof. exact (eq_refl (term289 A B C x y f p1 p2)). Qed.
Lemma lem4319246 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term290 A B C x y f s p2 t p1) = (term291 A B C x y f s p2 t p1).
Proof. exact (MK_COMB (@lem4319245 A B C x y f p1 p2) (@lem4319243 A B s p2 t p1)). Qed.
Lemma lem4319247 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term292 A B C x y f s p2 t p1) = (term290 A B C x y f s p2 t p1).
Proof. exact (@lem17045 ((f x y) = (f p1 p2)) (term182 A B s p2 t p1)). Qed.
Lemma lem4319248 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term292 A B C x y f s p2 t p1) = (term291 A B C x y f s p2 t p1).
Proof. exact (TRANS (@lem4319247 A B C x y f s p2 t p1) (@lem4319246 A B C x y f s p2 t p1)). Qed.
Lemma lem4319249 {B : Type'} (P : B -> Prop) : (term293 B P) = (term294 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4319250 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term295 A B C x y f s t p1) = (term296 A B C x y f s t p1).
Proof. exact (@lem4319249 B (term281 A B C x y f s t p1)). Qed.
Lemma lem4319251 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term297 A B C x y f s t p1 p2) = (term280 A B C x y f s p2 t p1).
Proof. exact (eq_refl (term297 A B C x y f s t p1 p2)). Qed.
Lemma lem4319252 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4319253 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term298 A B C x y f s t p1 p2) = (term292 A B C x y f s p2 t p1).
Proof. exact (MK_COMB (@lem4319252) (@lem4319251 A B C x y f s p2 t p1)). Qed.
Lemma lem4319254 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term298 A B C x y f s t p1 p2) = (term291 A B C x y f s p2 t p1).
Proof. exact (TRANS (@lem4319253 A B C x y f s p2 t p1) (@lem4319248 A B C x y f s p2 t p1)). Qed.
Lemma lem4319255 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term299 A B C x y f s t p1) = (term300 A B C x y f s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem4319254 A B C x y f s p2 t p1)). Qed.
Lemma lem4319256 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4319257 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term296 A B C x y f s t p1) = (term301 A B C x y f s t p1).
Proof. exact (MK_COMB (@lem4319256 B) (@lem4319255 A B C x y f s t p1)). Qed.
Lemma lem4319258 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term295 A B C x y f s t p1) = (term301 A B C x y f s t p1).
Proof. exact (TRANS (@lem4319250 A B C x y f s t p1) (@lem4319257 A B C x y f s t p1)). Qed.
Lemma lem4319259 {A : Type'} (P : A -> Prop) : (term293 A P) = (term294 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4319260 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term285 A B C x y f s t) = (term302 A B C x y f s t).
Proof. exact (@lem4319259 A (term283 A B C x y f s t)). Qed.
Lemma lem4319261 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term303 A B C x y f s t p1) = (term282 A B C x y f s t p1).
Proof. exact (eq_refl (term303 A B C x y f s t p1)). Qed.
Lemma lem4319262 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4319263 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term304 A B C x y f s t p1) = (term295 A B C x y f s t p1).
Proof. exact (MK_COMB (@lem4319262) (@lem4319261 A B C x y f s t p1)). Qed.
Lemma lem4319264 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term304 A B C x y f s t p1) = (term301 A B C x y f s t p1).
Proof. exact (TRANS (@lem4319263 A B C x y f s t p1) (@lem4319258 A B C x y f s t p1)). Qed.
Lemma lem4319265 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term305 A B C x y f s t) = (term306 A B C x y f s t).
Proof. exact (fun_ext (fun p1 : A => @lem4319264 A B C x y f s t p1)). Qed.
Lemma lem4319266 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4319267 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term302 A B C x y f s t) = (term307 A B C x y f s t).
Proof. exact (MK_COMB (@lem4319266 A) (@lem4319265 A B C x y f s t)). Qed.
Lemma lem4319324 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term285 A B C x y f s t) = (term307 A B C x y f s t).
Proof. exact (TRANS (@lem4319260 A B C x y f s t) (@lem4319267 A B C x y f s t)). Qed.
Lemma lem4319325 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term307 A B C x y f s t.
Proof. exact (EQ_MP (@lem4319324 A B C x y f s t) (@lem4319225 A B C x y f s t h1)). Qed.
Lemma lem4319341 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term182 A B s y t x.
Proof. exact (h1). Qed.
Lemma lem4319378 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term291 A B C x y f s p2 t p1) = (term291 A B C x y f s p2 t p1).
Proof. exact (eq_refl (term291 A B C x y f s p2 t p1)). Qed.
Lemma lem4319379 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term300 A B C x y f s t p1) = (term300 A B C x y f s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem4319378 A B C x y f s p2 t p1)). Qed.
Lemma lem4319380 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4319381 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term301 A B C x y f s t p1) = (term301 A B C x y f s t p1).
Proof. exact (MK_COMB (@lem4319380 B) (@lem4319379 A B C x y f s t p1)). Qed.
Lemma lem4319382 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term306 A B C x y f s t) = (term306 A B C x y f s t).
Proof. exact (fun_ext (fun p1 : A => @lem4319381 A B C x y f s t p1)). Qed.
Lemma lem4319383 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4319384 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term307 A B C x y f s t) = (term307 A B C x y f s t).
Proof. exact (MK_COMB (@lem4319383 A) (@lem4319382 A B C x y f s t)). Qed.
Lemma lem4319385 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term307 A B C x y f s t.
Proof. exact (EQ_MP (@lem4319384 A B C x y f s t) (@lem4319325 A B C x y f s t h1)). Qed.
Lemma lem4319401 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (p2 : B) (t : type1413 A B) (p1 : A) : (term291 A B C x y f s p2 t p1) = (term291 A B C x y f s p2 t p1).
Proof. exact (eq_refl (term291 A B C x y f s p2 t p1)). Qed.
Lemma lem4319402 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term300 A B C x y f s t p1) = (term300 A B C x y f s t p1).
Proof. exact (fun_ext (fun p2 : B => @lem4319401 A B C x y f s p2 t p1)). Qed.
Lemma lem4319403 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4319404 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (p1 : A) : (term301 A B C x y f s t p1) = (term301 A B C x y f s t p1).
Proof. exact (MK_COMB (@lem4319403 B) (@lem4319402 A B C x y f s t p1)). Qed.
Lemma lem4319405 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term306 A B C x y f s t) = (term306 A B C x y f s t).
Proof. exact (fun_ext (fun p1 : A => @lem4319404 A B C x y f s t p1)). Qed.
Lemma lem4319406 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4319408 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term307 A B C x y f s t) = (term307 A B C x y f s t).
Proof. exact (MK_COMB (@lem4319406 A) (@lem4319405 A B C x y f s t)). Qed.
Lemma lem4319409 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term307 A B C x y f s t.
Proof. exact (EQ_MP (@lem4319408 A B C x y f s t) (@lem4319385 A B C x y f s t h1)). Qed.
Lemma lem4319418 {A B C : Type'} (_49138 : A) (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term308 A B C x y f s t _49138.
Proof. exact (@lem4319409 A B C x y f s t h1 _49138). Qed.
Lemma lem4319419 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (_49138 : A) : (term308 A B C x y f s t _49138) = (term301 A B C x y f s t _49138).
Proof. exact (eq_refl (term308 A B C x y f s t _49138)). Qed.
Lemma lem4319420 {A B C : Type'} (_49138 : A) (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term301 A B C x y f s t _49138.
Proof. exact (EQ_MP (@lem4319419 A B C x y f s t _49138) (@lem4319418 A B C _49138 x y f s t h1)). Qed.
Lemma lem4319421 {A B C : Type'} (_49138 : A) (_49139 : B) (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term309 A B C x y f s t _49138 _49139.
Proof. exact (@lem4319420 A B C _49138 x y f s t h1 _49139). Qed.
Lemma lem4319422 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (_49139 : B) (t : type1413 A B) (_49138 : A) : (term309 A B C x y f s t _49138 _49139) = (term291 A B C x y f s _49139 t _49138).
Proof. exact (eq_refl (term309 A B C x y f s t _49138 _49139)). Qed.
Lemma lem4319433 {A B C : Type'} (_49139 : B) (_49138 : A) (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term291 A B C x y f s _49139 t _49138.
Proof. exact (EQ_MP (@lem4319422 A B C x y f s _49139 t _49138) (@lem4319421 A B C _49138 _49139 x y f s t h1)). Qed.
Lemma lem4319510 {C : Type'} (x : C) : x = x.
Proof. exact (@lem21386 C x). Qed.
Lemma lem4319511 {C : Type'} (x : C) : x = x.
Proof. exact (@lem4319510 C x). Qed.
Lemma lem4319512 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (f x y) = (f x y).
Proof. exact (@lem4319511 C (f x y)). Qed.
Lemma lem4319513 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : term310 A B C f x y.
Proof. exact (fun h0 : term311 A B C f x y => @lem4319512 A B C f x y). Qed.
Lemma lem4319515 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4319516 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (term310 A B C f x y) = ((f x y) = (f x y)).
Proof. exact (@lem4319515 ((f x y) = (f x y))). Qed.
Lemma lem4319517 {A B C : Type'} (f : type1412 A B C) (x : A) (y : B) : (f x y) = (f x y).
Proof. exact (EQ_MP (@lem4319516 A B C f x y) (@lem4319513 A B C f x y)). Qed.
Lemma lem4319519 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : @IN A x s.
Proof. exact (proj1 (@lem4319341 A B s y t x h1)). Qed.
Lemma lem4319520 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term313 A x s.
Proof. exact (fun h0 : term314 A x s => @lem4319519 A B s y t x h1). Qed.
Lemma lem4319522 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4319523 {A : Type'} (x : A) (s : A -> Prop) : (term313 A x s) = (@IN A x s).
Proof. exact (@lem4319522 (@IN A x s)). Qed.
Lemma lem4319524 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : @IN A x s.
Proof. exact (EQ_MP (@lem4319523 A x s) (@lem4319520 A B s y t x h1)). Qed.
Lemma lem4319526 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term288 A B y t x.
Proof. exact (proj2 (@lem4319341 A B s y t x h1)). Qed.
Lemma lem4319527 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term315 A B y t x.
Proof. exact (fun h0 : term316 A B y t x => @lem4319526 A B s y t x h1). Qed.
Lemma lem4319529 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4319530 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term315 A B y t x) = (term288 A B y t x).
Proof. exact (@lem4319529 (term288 A B y t x)). Qed.
Lemma lem4319531 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term288 A B y t x.
Proof. exact (EQ_MP (@lem4319530 A B y t x) (@lem4319527 A B s y t x h1)). Qed.
Lemma lem4319533 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4319534 {A B : Type'} (s : A -> Prop) (_49139 : B) (t : type1413 A B) (_49138 : A) : (term287 A B s _49139 t _49138) = (term286 A B s _49139 t _49138).
Proof. exact (@lem4319533 (@IN A _49138 s) (term288 A B _49139 t _49138)). Qed.
Lemma lem4319535 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (_49138 : A) (_49139 : B) : (term289 A B C x y f _49138 _49139) = (term289 A B C x y f _49138 _49139).
Proof. exact (eq_refl (term289 A B C x y f _49138 _49139)). Qed.
Lemma lem4319536 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (_49139 : B) (t : type1413 A B) (_49138 : A) : (term291 A B C x y f s _49139 t _49138) = (term290 A B C x y f s _49139 t _49138).
Proof. exact (MK_COMB (@lem4319535 A B C x y f _49138 _49139) (@lem4319534 A B s _49139 t _49138)). Qed.
Lemma lem4319538 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4319539 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (_49139 : B) (t : type1413 A B) (_49138 : A) : (term290 A B C x y f s _49139 t _49138) = (term292 A B C x y f s _49139 t _49138).
Proof. exact (@lem4319538 ((f x y) = (f _49138 _49139)) (term182 A B s _49139 t _49138)). Qed.
Lemma lem4319540 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (_49139 : B) (t : type1413 A B) (_49138 : A) : (term291 A B C x y f s _49139 t _49138) = (term292 A B C x y f s _49139 t _49138).
Proof. exact (TRANS (@lem4319536 A B C x y f s _49139 t _49138) (@lem4319539 A B C x y f s _49139 t _49138)). Qed.
Lemma lem4319542 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4319543 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (_49139 : B) (t : type1413 A B) (_49138 : A) : (term292 A B C x y f s _49139 t _49138) = (term319 A B C x y f s _49139 t _49138).
Proof. exact (@lem4319542 (term280 A B C x y f s _49139 t _49138)). Qed.
Lemma lem4319544 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (_49139 : B) (t : type1413 A B) (_49138 : A) : (term291 A B C x y f s _49139 t _49138) = (term319 A B C x y f s _49139 t _49138).
Proof. exact (TRANS (@lem4319540 A B C x y f s _49139 t _49138) (@lem4319543 A B C x y f s _49139 t _49138)). Qed.
Lemma lem4319546 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term182 A B s y t x.
Proof. exact (conj (@lem4319524 A B s y t x h1) (@lem4319531 A B s y t x h1)). Qed.
Lemma lem4319547 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term320 A B C f s y t x.
Proof. exact (conj (@lem4319517 A B C f x y) (@lem4319546 A B s y t x h1)). Qed.
Lemma lem4319549 {A B C : Type'} (_49139 : B) (_49138 : A) (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term319 A B C x y f s _49139 t _49138.
Proof. exact (EQ_MP (@lem4319544 A B C x y f s _49139 t _49138) (@lem4319433 A B C _49139 _49138 x y f s t h1)). Qed.
Lemma lem4319550 {A B C : Type'} (_49139 : B) (_49138 : A) (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term319 A B C x y f s _49139 t _49138.
Proof. exact (@lem4319549 A B C _49139 _49138 x y f s t h1). Qed.
Lemma lem4319551 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term285 A B C x y f s t) : term321 A B C f s y t x.
Proof. exact (@lem4319550 A B C y x x y f s t h1). Qed.
Lemma lem4319554 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : False.
Proof. exact (@lem4319551 A B C x y f s t h1 (@lem4319547 A B C f s y t x h2)). Qed.
Lemma lem4319555 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : term322.
Proof. exact (fun h0 : ~ False => @lem4319554 A B C f s y t x h1 h2). Qed.
Lemma lem4319557 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4319558 : term322 = False.
Proof. exact (@lem4319557 False). Qed.
Lemma lem4319559 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : False.
Proof. exact (EQ_MP (@lem4319558) (@lem4319555 A B C f s y t x h1 h2)). Qed.
Lemma lem4319560 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : (term182 A B s y t x) = False.
Proof. exact (prop_ext (fun h3 : term182 A B s y t x => @lem4319559 A B C f s y t x h1 h2) (fun h3 : False => @lem4319341 A B s y t x h2)). Qed.
Lemma lem4319561 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : False.
Proof. exact (EQ_MP (@lem4319560 A B C f s y t x h1 h2) (@lem4319341 A B s y t x h2)). Qed.
Lemma lem4319562 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : (term182 A B s y t x) = False.
Proof. exact (prop_ext (fun h3 : term182 A B s y t x => @lem4319561 A B C f s y t x h1 h2) (fun h3 : False => @lem4319235 A B s y t x h2)). Qed.
Lemma lem4319563 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : False.
Proof. exact (EQ_MP (@lem4319562 A B C f s y t x h1 h2) (@lem4319235 A B s y t x h2)). Qed.
Lemma lem4319564 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : (term285 A B C x y f s t) = False.
Proof. exact (prop_ext (fun h3 : term285 A B C x y f s t => @lem4319563 A B C f s y t x h1 h2) (fun h3 : False => @lem4319225 A B C x y f s t h1)). Qed.
Lemma lem4319565 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term285 A B C x y f s t) (h2 : term182 A B s y t x) : False.
Proof. exact (EQ_MP (@lem4319564 A B C f s y t x h1 h2) (@lem4319225 A B C x y f s t h1)). Qed.
Lemma lem4319566 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term284 A B C x y f s t.
Proof. exact (fun h0 : term285 A B C x y f s t => @lem4319565 A B C f s y t x h0 h1). Qed.
Lemma lem4319567 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (h1 : term182 A B s y t x) : term247 A B C x y f s t.
Proof. exact (EQ_MP (@lem4319224 A B C x y f s t) (@lem4319566 A B C f s y t x h1)). Qed.
Lemma lem4319568 {A B C : Type'} (x : A) (y : B) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term249 A B C x y f s t.
Proof. exact (fun h0 : term182 A B s y t x => @lem4319567 A B C f s y t x h0). Qed.
Lemma lem4319573 {A B C : Type'} (x : A) (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term253 A B C x f s t.
Proof. exact (fun y : B => @lem4319568 A B C x y f s t). Qed.
Lemma lem4319578 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term256 A B C f s t.
Proof. exact (fun x : A => @lem4319573 A B C x f s t). Qed.
Lemma lem4319583 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : term271 A B C s t.
Proof. exact (fun f : type1412 A B C => @lem4319578 A B C f s t). Qed.
Lemma lem4319588 {A B C : Type'} (t : type1413 A B) : term275 A B C t.
Proof. exact (fun s : A -> Prop => @lem4319583 A B C s t). Qed.
Lemma lem4319593 {A B C : Type'} : term279 A B C.
Proof. exact (fun t : type1413 A B => @lem4319588 A B C t). Qed.
Lemma lem4319594 {A B C : Type'} : term278 A B C.
Proof. exact (EQ_MP (@lem4319219 A B C) (@lem4319593 A B C)). Qed.
Lemma lem4319595 {A B C : Type'} (t : type1413 A B) : term323 A B C t.
Proof. exact (@lem4319594 A B C t). Qed.
Lemma lem4319596 {A B C : Type'} (t : type1413 A B) : (term323 A B C t) = (term274 A B C t).
Proof. exact (eq_refl (term323 A B C t)). Qed.
Lemma lem4319597 {A B C : Type'} (t : type1413 A B) : term274 A B C t.
Proof. exact (EQ_MP (@lem4319596 A B C t) (@lem4319595 A B C t)). Qed.
Lemma lem4319598 {A B C : Type'} (t : type1413 A B) (s : A -> Prop) : term324 A B C t s.
Proof. exact (@lem4319597 A B C t s). Qed.
Lemma lem4319599 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : (term324 A B C t s) = (term270 A B C s t).
Proof. exact (eq_refl (term324 A B C t s)). Qed.
Lemma lem4319600 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) : term270 A B C s t.
Proof. exact (EQ_MP (@lem4319599 A B C s t) (@lem4319598 A B C t s)). Qed.
Lemma lem4319601 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term325 A B C s t f.
Proof. exact (@lem4319600 A B C s t f). Qed.
Lemma lem4319602 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : (term325 A B C s t f) = (term261 A B C f s t).
Proof. exact (eq_refl (term325 A B C s t f)). Qed.
Lemma lem4319603 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term261 A B C f s t.
Proof. exact (EQ_MP (@lem4319602 A B C f s t) (@lem4319601 A B C s t f)). Qed.
Lemma lem4319605 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term261 A B C f s t.
Proof. exact (@lem4319015 A B C f s t (@lem4319603 A B C f s t)). Qed.
Lemma lem4319606 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term262 A B C f s t) : False.
Proof. exact (@lem4319605 A B C f s t (@lem4318999 A B C f s t h1)). Qed.
Lemma lem4319607 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term262 A B C f s t) : (term262 A B C f s t) = False.
Proof. exact (prop_ext (fun h2 : term262 A B C f s t => @lem4319606 A B C f s t h1) (fun h2 : False => @lem4318999 A B C f s t h1)). Qed.
Lemma lem4319608 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term262 A B C f s t) : False.
Proof. exact (EQ_MP (@lem4319607 A B C f s t h1) (@lem4318999 A B C f s t h1)). Qed.
Lemma lem4319609 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term261 A B C f s t.
Proof. exact (fun h0 : term262 A B C f s t => @lem4319608 A B C f s t h0). Qed.
Lemma lem4319610 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) : term256 A B C f s t.
Proof. exact (EQ_MP (@lem4318998 A B C f s t) (@lem4319609 A B C f s t)). Qed.
Lemma lem4319616 {A : Type'} (P : Prop) (Q : A -> Prop) : (term51 A P Q) = (term52 A P Q).
Proof. exact (EQ_MP (@lem4318499 A P Q) (@lem4318498 A P Q)). Qed.
Lemma lem4319617 {A B : Type'} (P : Prop) (Q : type475 A B) : (term326 A B P Q) = (term327 A B P Q).
Proof. exact (@lem4319616 (type1413 A B) P Q). Qed.
Lemma lem4319618 {A B : Type'} (s : A -> Prop) : (term328 A B s) = (term329 A B s).
Proof. exact (@lem4319617 A B (@FINITE A s) (term330 A B s)). Qed.
Lemma lem4319619 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term331 A B s t) = (term332 A B s t).
Proof. exact (eq_refl (term331 A B s t)). Qed.
Lemma lem4319620 {A : Type'} (s : A -> Prop) : (term333 A s) = (term333 A s).
Proof. exact (eq_refl (term333 A s)). Qed.
Lemma lem4319621 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term334 A B s t) = (term335 A B s t).
Proof. exact (MK_COMB (@lem4319620 A s) (@lem4319619 A B s t)). Qed.
Lemma lem4319622 {A B : Type'} (s : A -> Prop) : (term336 A B s) = (term337 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4319621 A B s t)). Qed.
Lemma lem4319623 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4319624 {A B : Type'} (s : A -> Prop) : (term328 A B s) = (term338 A B s).
Proof. exact (MK_COMB (@lem4319623 A B) (@lem4319622 A B s)). Qed.
Lemma lem4319625 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4319626 {A B : Type'} (s : A -> Prop) : (term339 A B s) = (term340 A B s).
Proof. exact (MK_COMB (@lem4319625) (@lem4319624 A B s)). Qed.
Lemma lem4319627 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term331 A B s t) = (term332 A B s t).
Proof. exact (eq_refl (term331 A B s t)). Qed.
Lemma lem4319628 {A B : Type'} (s : A -> Prop) : (term341 A B s) = (term330 A B s).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4319627 A B s t)). Qed.
Lemma lem4319629 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4319630 {A B : Type'} (s : A -> Prop) : (term342 A B s) = (term343 A B s).
Proof. exact (MK_COMB (@lem4319629 A B) (@lem4319628 A B s)). Qed.
Lemma lem4319631 {A : Type'} (s : A -> Prop) : (term333 A s) = (term333 A s).
Proof. exact (eq_refl (term333 A s)). Qed.
Lemma lem4319632 {A B : Type'} (s : A -> Prop) : (term329 A B s) = (term344 A B s).
Proof. exact (MK_COMB (@lem4319631 A s) (@lem4319630 A B s)). Qed.
Lemma lem4319633 {A B : Type'} (s : A -> Prop) : ((term328 A B s) = (term329 A B s)) = ((term338 A B s) = (term344 A B s)).
Proof. exact (MK_COMB (@lem4319626 A B s) (@lem4319632 A B s)). Qed.
Lemma lem4319634 {A B : Type'} (s : A -> Prop) : (term338 A B s) = (term344 A B s).
Proof. exact (EQ_MP (@lem4319633 A B s) (@lem4319618 A B s)). Qed.
Lemma lem4319699 {A B : Type'} : (term345 A B) = (term346 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4319634 A B s)). Qed.
Lemma lem4319700 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4319701 {A B : Type'} : (term347 A B) = (term348 A B).
Proof. exact (MK_COMB (@lem4319700 A) (@lem4319699 A B)). Qed.
Lemma lem4319726 {A B : Type'} : (term348 A B) = (term347 A B).
Proof. exact (SYM (@lem4319701 A B)). Qed.
Lemma lem4319728 {A : Type'} (P : type686 A) : term43 A P.
Proof. exact (EQ_MP (@lem4318493 A P) (@lem4318492 A P)). Qed.
Lemma lem4319729 {A : Type'} (P : type686 A) : term43 A P.
Proof. exact (@lem4319728 A P). Qed.
Lemma lem4319730 {A B : Type'} : term349 A B.
Proof. exact (@lem4319729 A (term350 A B)). Qed.
Lemma lem4319731 {A B : Type'} : (term351 A B) = (term352 A B).
Proof. exact (eq_refl (term351 A B)). Qed.
Lemma lem4319732 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4319733 {A B : Type'} : (term353 A B) = (term354 A B).
Proof. exact (MK_COMB (@lem4319732) (@lem4319731 A B)). Qed.
Lemma lem4319734 {A B : Type'} (s : A -> Prop) : (term355 A B s) = (term343 A B s).
Proof. exact (eq_refl (term355 A B s)). Qed.
Lemma lem4319735 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4319736 {A B : Type'} (s : A -> Prop) : (term356 A B s) = (term357 A B s).
Proof. exact (MK_COMB (@lem4319735) (@lem4319734 A B s)). Qed.
Lemma lem4319737 {A : Type'} (x : A) (s : A -> Prop) : (term358 A x s) = (term358 A x s).
Proof. exact (eq_refl (term358 A x s)). Qed.
Lemma lem4319738 {A B : Type'} (x : A) (s : A -> Prop) : (term359 A B x s) = (term360 A B x s).
Proof. exact (MK_COMB (@lem4319736 A B s) (@lem4319737 A x s)). Qed.
Lemma lem4319739 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4319740 {A B : Type'} (x : A) (s : A -> Prop) : (term361 A B x s) = (term362 A B x s).
Proof. exact (MK_COMB (@lem4319739) (@lem4319738 A B x s)). Qed.
Lemma lem4319741 {A B : Type'} (x : A) (s : A -> Prop) : (term363 A B x s) = (term364 A B x s).
Proof. exact (eq_refl (term363 A B x s)). Qed.
Lemma lem4319742 {A B : Type'} (x : A) (s : A -> Prop) : (term365 A B x s) = (term366 A B x s).
Proof. exact (MK_COMB (@lem4319740 A B x s) (@lem4319741 A B x s)). Qed.
Lemma lem4319743 {A B : Type'} (x : A) : (term367 A B x) = (term368 A B x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4319742 A B x s)). Qed.
Lemma lem4319744 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4319745 {A B : Type'} (x : A) : (term369 A B x) = (term370 A B x).
Proof. exact (MK_COMB (@lem4319744 A) (@lem4319743 A B x)). Qed.
Lemma lem4319746 {A B : Type'} : (term371 A B) = (term372 A B).
Proof. exact (fun_ext (fun x : A => @lem4319745 A B x)). Qed.
Lemma lem4319747 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4319748 {A B : Type'} : (term373 A B) = (term374 A B).
Proof. exact (MK_COMB (@lem4319747 A) (@lem4319746 A B)). Qed.
Lemma lem4319749 {A B : Type'} : (term375 A B) = (term376 A B).
Proof. exact (MK_COMB (@lem4319733 A B) (@lem4319748 A B)). Qed.
Lemma lem4319750 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4319751 {A B : Type'} : (term377 A B) = (term378 A B).
Proof. exact (MK_COMB (@lem4319750) (@lem4319749 A B)). Qed.
Lemma lem4319752 {A B : Type'} (s : A -> Prop) : (term355 A B s) = (term343 A B s).
Proof. exact (eq_refl (term355 A B s)). Qed.
Lemma lem4319753 {A : Type'} (s : A -> Prop) : (term333 A s) = (term333 A s).
Proof. exact (eq_refl (term333 A s)). Qed.
Lemma lem4319754 {A B : Type'} (s : A -> Prop) : (term379 A B s) = (term344 A B s).
Proof. exact (MK_COMB (@lem4319753 A s) (@lem4319752 A B s)). Qed.
Lemma lem4319755 {A B : Type'} : (term380 A B) = (term346 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4319754 A B s)). Qed.
Lemma lem4319756 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4319757 {A B : Type'} : (term381 A B) = (term348 A B).
Proof. exact (MK_COMB (@lem4319756 A) (@lem4319755 A B)). Qed.
Lemma lem4319758 {A B : Type'} : (term349 A B) = (term382 A B).
Proof. exact (MK_COMB (@lem4319751 A B) (@lem4319757 A B)). Qed.
Lemma lem4319759 {A B : Type'} : term382 A B.
Proof. exact (EQ_MP (@lem4319758 A B) (@lem4319730 A B)). Qed.
Lemma lem4319770 {A : Type'} : @FINITE A (@EMPTY A).
Proof. exact (proj1 (@lem3197565 A)). Qed.
Lemma lem4319771 {A : Type'} : (@FINITE A (@EMPTY A)) = ((@FINITE A (@EMPTY A)) = True).
Proof. exact (@lem7 (@FINITE A (@EMPTY A))). Qed.
Lemma lem4319782 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : (term383 A B t) = (@EMPTY (prod A B)).
Proof. exact (h1). Qed.
Lemma lem4319783 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : (term383 A B t) = (@EMPTY (prod A B)).
Proof. exact (@lem4319782 A B t h1). Qed.
Lemma lem4319784 {A B : Type'} : (@FINITE (prod A B)) = (@FINITE (prod A B)).
Proof. exact (eq_refl (@FINITE (prod A B))). Qed.
Lemma lem4319785 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : (term384 A B t) = (@FINITE (prod A B) (@EMPTY (prod A B))).
Proof. exact (MK_COMB (@lem4319784 A B) (@lem4319783 A B t h1)). Qed.
Lemma lem4319787 {A : Type'} : (@FINITE A (@EMPTY A)) = True.
Proof. exact (EQ_MP (@lem4319771 A) (@lem4319770 A)). Qed.
Lemma lem4319788 {A B : Type'} : (@FINITE (prod A B) (@EMPTY (prod A B))) = True.
Proof. exact (@lem4319787 (prod A B)). Qed.
Lemma lem4319789 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : (term384 A B t) = True.
Proof. exact (TRANS (@lem4319785 A B t h1) (@lem4319788 A B)). Qed.
Lemma lem4319790 {A B : Type'} (t : type1413 A B) : (term385 A B t) = (term385 A B t).
Proof. exact (eq_refl (term385 A B t)). Qed.
Lemma lem4319791 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : (term386 A B t) = (term387 A B t).
Proof. exact (MK_COMB (@lem4319790 A B t) (@lem4319789 A B t h1)). Qed.
Lemma lem4319793 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4319794 {A B : Type'} (t : type1413 A B) : (term387 A B t) = True.
Proof. exact (@lem4319793 (term388 A B t)). Qed.
Lemma lem4319795 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : (term386 A B t) = True.
Proof. exact (TRANS (@lem4319791 A B t h1) (@lem4319794 A B t)). Qed.
Lemma lem4319796 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : True = (term386 A B t).
Proof. exact (SYM (@lem4319795 A B t h1)). Qed.
Lemma lem4319797 {A B : Type'} (t : type1413 A B) (h1 : (term383 A B t) = (@EMPTY (prod A B))) : term386 A B t.
Proof. exact (EQ_MP (@lem4319796 A B t h1) (@lem0)). Qed.
Lemma lem4319801 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term37 A s t).
Proof. exact (EQ_MP (@lem4318477 A s t) (@lem4318476 A s t)). Qed.
Lemma lem4319802 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = t) = (term389 A B s t).
Proof. exact (@lem4319801 (prod A B) s t). Qed.
Lemma lem4319803 {A B : Type'} (t : type1413 A B) : ((term383 A B t) = (@EMPTY (prod A B))) = (term390 A B t).
Proof. exact (@lem4319802 A B (term383 A B t) (@EMPTY (prod A B))). Qed.
Lemma lem4319813 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term25 _83064 x P) = (term26 _83064 P x).
Proof. exact (EQ_MP (@lem4318471 _83064 P x) (@lem4318470 _83064 P x)). Qed.
Lemma lem4319814 {A B : Type'} (P : type914 A B) (x : prod A B) : (term391 A B x P) = (term392 A B P x).
Proof. exact (@lem4319813 (prod A B) P x). Qed.
Lemma lem4319815 {A B : Type'} (t : type1413 A B) (x : prod A B) : (term393 A B x t) = (term394 A B t x).
Proof. exact (@lem4319814 A B (term395 A B t) x). Qed.
Lemma lem4319816 {A B : Type'} (GEN_PVAR_124 : prod A B) (t : type1413 A B) : (term396 A B t GEN_PVAR_124) = (term397 A B GEN_PVAR_124 t).
Proof. exact (eq_refl (term396 A B t GEN_PVAR_124)). Qed.
Lemma lem4319817 {A B : Type'} (t : type1413 A B) : (term398 A B t) = (term399 A B t).
Proof. exact (fun_ext (fun GEN_PVAR_124 : prod A B => @lem4319816 A B GEN_PVAR_124 t)). Qed.
Lemma lem4319818 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4319819 {A B : Type'} (t : type1413 A B) : (term400 A B t) = (term383 A B t).
Proof. exact (MK_COMB (@lem4319818 A B) (@lem4319817 A B t)). Qed.
Lemma lem4319820 {A B : Type'} (x : prod A B) : (@IN (prod A B) x) = (@IN (prod A B) x).
Proof. exact (eq_refl (@IN (prod A B) x)). Qed.
Lemma lem4319821 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term393 A B x t) = (term401 A B x t).
Proof. exact (MK_COMB (@lem4319820 A B x) (@lem4319819 A B t)). Qed.
Lemma lem4319822 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4319823 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term402 A B x t) = (term403 A B x t).
Proof. exact (MK_COMB (@lem4319822) (@lem4319821 A B x t)). Qed.
Lemma lem4319824 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term394 A B t x) = (term404 A B x t).
Proof. exact (eq_refl (term394 A B t x)). Qed.
Lemma lem4319825 {A B : Type'} (x : prod A B) (t : type1413 A B) : ((term393 A B x t) = (term394 A B t x)) = ((term401 A B x t) = (term404 A B x t)).
Proof. exact (MK_COMB (@lem4319823 A B x t) (@lem4319824 A B x t)). Qed.
Lemma lem4319826 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term401 A B x t) = (term404 A B x t).
Proof. exact (EQ_MP (@lem4319825 A B x t) (@lem4319815 A B t x)). Qed.
Lemma lem4319836 {A B : Type'} (f : A -> B) (y : A) : (term405 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4319837 {A B : Type'} (f : type1532 A B) (y : Prop) : (term406 A B f y) = (f y).
Proof. exact (@lem4319836 Prop (type1210 A B) f y). Qed.
Lemma lem4319838 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (x' : A) : (term407 A B x y t x') = (term408 A B x y t x').
Proof. exact (@lem4319837 A B (term409 A B x) (term410 A B y t x')). Qed.
Lemma lem4319839 {A B : Type'} (p : Prop) (x : prod A B) : (term411 A B x p) = (term412 A B p x).
Proof. exact (eq_refl (term411 A B x p)). Qed.
Lemma lem4319840 {A B : Type'} (x : prod A B) : (term413 A B x) = (term409 A B x).
Proof. exact (fun_ext (fun p : Prop => @lem4319839 A B p x)). Qed.
Lemma lem4319841 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term410 A B y t x) = (term410 A B y t x).
Proof. exact (eq_refl (term410 A B y t x)). Qed.
Lemma lem4319842 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (x' : A) : (term407 A B x y t x') = (term408 A B x y t x').
Proof. exact (MK_COMB (@lem4319840 A B x) (@lem4319841 A B y t x')). Qed.
Lemma lem4319843 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem4319844 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (x' : A) : (term414 A B x y t x') = (term415 A B x y t x').
Proof. exact (MK_COMB (@lem4319843 A B) (@lem4319842 A B x y t x')). Qed.
Lemma lem4319845 {A B : Type'} (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term408 A B x' y t x) = (term416 A B y t x x').
Proof. exact (eq_refl (term408 A B x' y t x)). Qed.
Lemma lem4319846 {A B : Type'} (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : ((term407 A B x' y t x) = (term408 A B x' y t x)) = ((term408 A B x' y t x) = (term416 A B y t x x')).
Proof. exact (MK_COMB (@lem4319844 A B x' y t x) (@lem4319845 A B y t x x')). Qed.
Lemma lem4319847 {A B : Type'} (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term408 A B x' y t x) = (term416 A B y t x x').
Proof. exact (EQ_MP (@lem4319846 A B y t x x') (@lem4319838 A B x' y t x)). Qed.
Lemma lem4319853 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4318433 A x (@lem4318432 A x)). Qed.
Lemma lem4319854 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4319853 A x). Qed.
Lemma lem4319855 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4319856 {A : Type'} (x : A) : (term417 A x) = (and False).
Proof. exact (MK_COMB (@lem4319855) (@lem4319854 A x)). Qed.
Lemma lem4319857 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term288 A B y t x) = (term288 A B y t x).
Proof. exact (eq_refl (term288 A B y t x)). Qed.
Lemma lem4319858 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term410 A B y t x) = (term418 A B y t x).
Proof. exact (MK_COMB (@lem4319856 A x) (@lem4319857 A B y t x)). Qed.
Lemma lem4319860 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4319861 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term418 A B y t x) = False.
Proof. exact (@lem4319860 (term288 A B y t x)). Qed.
Lemma lem4319862 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term410 A B y t x) = False.
Proof. exact (TRANS (@lem4319858 A B y t x) (@lem4319861 A B y t x)). Qed.
Lemma lem4319863 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4319864 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term419 A B y t x) = (and False).
Proof. exact (MK_COMB (@lem4319863) (@lem4319862 A B y t x)). Qed.
Lemma lem4319869 {A B : Type'} (x : prod A B) (t : prod A B) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem4319870 {A B : Type'} (y : B) (t : type1413 A B) (x : A) (x' : prod A B) (t' : prod A B) : (term420 A B y t x x' t') = (term421 A B x' t').
Proof. exact (MK_COMB (@lem4319864 A B y t x) (@lem4319869 A B x' t')). Qed.
Lemma lem4319872 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem4319873 {A B : Type'} (x : prod A B) (t : prod A B) : (term421 A B x t) = False.
Proof. exact (@lem4319872 (x = t)). Qed.
Lemma lem4319874 {A B : Type'} (y : B) (t : type1413 A B) (x : A) (x' : prod A B) (t' : prod A B) : (term420 A B y t x x' t') = False.
Proof. exact (TRANS (@lem4319870 A B y t x x' t') (@lem4319873 A B x' t')). Qed.
Lemma lem4319875 {A B : Type'} (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term416 A B y t x x') = (term422 A B).
Proof. exact (fun_ext (fun t' : prod A B => @lem4319874 A B y t x x' t')). Qed.
Lemma lem4319876 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (x' : A) : (term408 A B x y t x') = (term422 A B).
Proof. exact (TRANS (@lem4319847 A B y t x' x) (@lem4319875 A B y t x' x)). Qed.
Lemma lem4319877 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4319878 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) (y : B) : (term423 A B x t x' y) = (term424 A B x' y).
Proof. exact (MK_COMB (@lem4319876 A B x y t x') (@lem4319877 A B x' y)). Qed.
Lemma lem4319880 {A B : Type'} (f : A -> B) (y : A) : (term405 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4319881 {A B : Type'} (f : type1210 A B) (y : prod A B) : (term425 A B f y) = (f y).
Proof. exact (@lem4319880 (prod A B) Prop f y). Qed.
Lemma lem4319882 {A B : Type'} (x : A) (y : B) : (term426 A B x y) = (term424 A B x y).
Proof. exact (@lem4319881 A B (term422 A B) (@pair A B x y)). Qed.
Lemma lem4319883 {A B : Type'} (t : prod A B) : (term427 A B t) = False.
Proof. exact (eq_refl (term427 A B t)). Qed.
Lemma lem4319884 {A B : Type'} : (term428 A B) = (term422 A B).
Proof. exact (fun_ext (fun t : prod A B => @lem4319883 A B t)). Qed.
Lemma lem4319885 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4319886 {A B : Type'} (x : A) (y : B) : (term426 A B x y) = (term424 A B x y).
Proof. exact (MK_COMB (@lem4319884 A B) (@lem4319885 A B x y)). Qed.
Lemma lem4319887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4319888 {A B : Type'} (x : A) (y : B) : (term429 A B x y) = (term430 A B x y).
Proof. exact (MK_COMB (@lem4319887) (@lem4319886 A B x y)). Qed.
Lemma lem4319889 {A B : Type'} (x : A) (y : B) : (term424 A B x y) = False.
Proof. exact (eq_refl (term424 A B x y)). Qed.
Lemma lem4319890 {A B : Type'} (x : A) (y : B) : ((term426 A B x y) = (term424 A B x y)) = ((term424 A B x y) = False).
Proof. exact (MK_COMB (@lem4319888 A B x y) (@lem4319889 A B x y)). Qed.
Lemma lem4319891 {A B : Type'} (x : A) (y : B) : (term424 A B x y) = False.
Proof. exact (EQ_MP (@lem4319890 A B x y) (@lem4319882 A B x y)). Qed.
Lemma lem4319892 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) (y : B) : (term423 A B x t x' y) = False.
Proof. exact (TRANS (@lem4319878 A B x t x' y) (@lem4319891 A B x' y)). Qed.
Lemma lem4319893 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) : (term431 A B x t x') = (term432 B).
Proof. exact (fun_ext (fun y : B => @lem4319892 A B x t x' y)). Qed.
Lemma lem4319894 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4319895 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) : (term433 A B x t x') = (term434 B).
Proof. exact (MK_COMB (@lem4319894 B) (@lem4319893 A B x t x')). Qed.
Lemma lem4319897 {A : Type'} (t : Prop) : (term435 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem4319898 {B : Type'} (t : Prop) : (term435 B t) = t.
Proof. exact (@lem4319897 B t). Qed.
Lemma lem4319899 {B : Type'} : (term434 B) = False.
Proof. exact (@lem4319898 B False). Qed.
Lemma lem4319900 {A B : Type'} (x : prod A B) (t : type1413 A B) (x' : A) : (term433 A B x t x') = False.
Proof. exact (TRANS (@lem4319895 A B x t x') (@lem4319899 B)). Qed.
Lemma lem4319901 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term436 A B x t) = (term432 A).
Proof. exact (fun_ext (fun x' : A => @lem4319900 A B x t x')). Qed.
Lemma lem4319902 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4319903 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term404 A B x t) = (term434 A).
Proof. exact (MK_COMB (@lem4319902 A) (@lem4319901 A B x t)). Qed.
Lemma lem4319905 {A : Type'} (t : Prop) : (term435 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem4319906 {A : Type'} (t : Prop) : (term435 A t) = t.
Proof. exact (@lem4319905 A t). Qed.
Lemma lem4319907 {A : Type'} : (term434 A) = False.
Proof. exact (@lem4319906 A False). Qed.
Lemma lem4319908 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term404 A B x t) = False.
Proof. exact (TRANS (@lem4319903 A B x t) (@lem4319907 A)). Qed.
Lemma lem4319909 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term401 A B x t) = False.
Proof. exact (TRANS (@lem4319826 A B x t) (@lem4319908 A B x t)). Qed.
Lemma lem4319910 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4319911 {A B : Type'} (x : prod A B) (t : type1413 A B) : (term403 A B x t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem4319910) (@lem4319909 A B x t)). Qed.
Lemma lem4319913 {A : Type'} (x : A) : (@IN A x (@EMPTY A)) = False.
Proof. exact (@lem4318433 A x (@lem4318432 A x)). Qed.
Lemma lem4319914 {A B : Type'} (x : prod A B) : (@IN (prod A B) x (@EMPTY (prod A B))) = False.
Proof. exact (@lem4319913 (prod A B) x). Qed.
Lemma lem4319915 {A B : Type'} (t : type1413 A B) (x : prod A B) : ((term401 A B x t) = (@IN (prod A B) x (@EMPTY (prod A B)))) = (False = False).
Proof. exact (MK_COMB (@lem4319911 A B x t) (@lem4319914 A B x)). Qed.
Lemma lem4319917 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem4319918 : (False = False) = (~ False).
Proof. exact (@lem4319917 False). Qed.
Lemma lem4319920 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem4319921 : (False = False) = True.
Proof. exact (TRANS (@lem4319918) (@lem4319920)). Qed.
Lemma lem4319922 {A B : Type'} (t : type1413 A B) (x : prod A B) : ((term401 A B x t) = (@IN (prod A B) x (@EMPTY (prod A B)))) = True.
Proof. exact (TRANS (@lem4319915 A B t x) (@lem4319921)). Qed.
Lemma lem4319923 {A B : Type'} (t : type1413 A B) : (term437 A B t) = (term438 A B).
Proof. exact (fun_ext (fun x : prod A B => @lem4319922 A B t x)). Qed.
Lemma lem4319924 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4319925 {A B : Type'} (t : type1413 A B) : (term390 A B t) = (term439 A B).
Proof. exact (MK_COMB (@lem4319924 A B) (@lem4319923 A B t)). Qed.
Lemma lem4319927 {A : Type'} (t : Prop) : (term440 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4319928 {A B : Type'} (t : Prop) : (term441 A B t) = t.
Proof. exact (@lem4319927 (prod A B) t). Qed.
Lemma lem4319929 {A B : Type'} : (term439 A B) = True.
Proof. exact (@lem4319928 A B True). Qed.
Lemma lem4319930 {A B : Type'} (t : type1413 A B) : (term390 A B t) = True.
Proof. exact (TRANS (@lem4319925 A B t) (@lem4319929 A B)). Qed.
Lemma lem4319931 {A B : Type'} (t : type1413 A B) : ((term383 A B t) = (@EMPTY (prod A B))) = True.
Proof. exact (TRANS (@lem4319803 A B t) (@lem4319930 A B t)). Qed.
Lemma lem4319932 {A B : Type'} (t : type1413 A B) : True = ((term383 A B t) = (@EMPTY (prod A B))).
Proof. exact (SYM (@lem4319931 A B t)). Qed.
Lemma lem4319933 {A B : Type'} (t : type1413 A B) : (term383 A B t) = (@EMPTY (prod A B)).
Proof. exact (EQ_MP (@lem4319932 A B t) (@lem0)). Qed.
Lemma lem4319934 {A B : Type'} (t : type1413 A B) : ((term383 A B t) = (@EMPTY (prod A B))) = (term386 A B t).
Proof. exact (prop_ext (fun h1 : (term383 A B t) = (@EMPTY (prod A B)) => @lem4319797 A B t h1) (fun h1 : term386 A B t => @lem4319933 A B t)). Qed.
Lemma lem4319935 {A B : Type'} (t : type1413 A B) : term386 A B t.
Proof. exact (EQ_MP (@lem4319934 A B t) (@lem4319933 A B t)). Qed.
Lemma lem4319940 {A B : Type'} : term352 A B.
Proof. exact (fun t : type1413 A B => @lem4319935 A B t). Qed.
Lemma lem4319941 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term360 A B a s) : term360 A B a s.
Proof. exact (h1). Qed.
Lemma lem4319942 {A : Type'} (a : A) (s : A -> Prop) (h1 : term358 A a s) : term358 A a s.
Proof. exact (h1). Qed.
Lemma lem4319943 {A B : Type'} (s : A -> Prop) (h1 : term343 A B s) : term343 A B s.
Proof. exact (h1). Qed.
Lemma lem4319945 {A : Type'} (a : A) (s : A -> Prop) (h1 : term314 A a s) : term314 A a s.
Proof. exact (h1). Qed.
Lemma lem4319947 {A : Type'} (s : A -> Prop) : term442 A s.
Proof. exact (@lem3606772 A s). Qed.
Lemma lem4319948 {A : Type'} (s : A -> Prop) : (term442 A s) = (term443 A s).
Proof. exact (eq_refl (term442 A s)). Qed.
Lemma lem4319949 {A : Type'} (s : A -> Prop) : term443 A s.
Proof. exact (EQ_MP (@lem4319948 A s) (@lem4319947 A s)). Qed.
Lemma lem4319950 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term444 A s t.
Proof. exact (@lem4319949 A s t). Qed.
Lemma lem4319951 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term444 A s t) = ((term445 A s t) = (term446 A s t)).
Proof. exact (eq_refl (term444 A s t)). Qed.
Lemma lem4319953 {A B : Type'} (f : A -> B) : term54 A B f.
Proof. exact (@lem3615104 A B f). Qed.
Lemma lem4319954 {A B : Type'} (f : A -> B) : (term54 A B f) = (term55 A B f).
Proof. exact (eq_refl (term54 A B f)). Qed.
Lemma lem4319955 {A B : Type'} (f : A -> B) : term55 A B f.
Proof. exact (EQ_MP (@lem4319954 A B f) (@lem4319953 A B f)). Qed.
Lemma lem4319956 {A B : Type'} (f : A -> B) (s : A -> Prop) : term56 A B f s.
Proof. exact (@lem4319955 A B f s). Qed.
Lemma lem4319957 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term56 A B f s) = (term57 A B f s).
Proof. exact (eq_refl (term56 A B f s)). Qed.
Lemma lem4319958 {A B : Type'} (f : A -> B) (s : A -> Prop) : term57 A B f s.
Proof. exact (EQ_MP (@lem4319957 A B f s) (@lem4319956 A B f s)). Qed.
Lemma lem4319959 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4319960 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : term58 A B f s.
Proof. exact (@lem4319958 A B f s (@lem4319959 A s h1)). Qed.
Lemma lem4319961 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term58 A B f s) = ((term58 A B f s) = True).
Proof. exact (@lem7 (term58 A B f s)). Qed.
Lemma lem4319962 {A B : Type'} (f : A -> B) (s : A -> Prop) (h1 : @FINITE A s) : (term58 A B f s) = True.
Proof. exact (EQ_MP (@lem4319961 A B f s) (@lem4319960 A B f s h1)). Qed.
Lemma lem4319968 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3205665 A x). Qed.
Lemma lem4319969 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem4319970 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem4319969 A x) (@lem4319968 A x)). Qed.
Lemma lem4319971 {A : Type'} (x : A) (y : A) : term16 A x y.
Proof. exact (@lem4319970 A x y). Qed.
Lemma lem4319972 {A : Type'} (y : A) (x : A) : (term16 A x y) = (term17 A y x).
Proof. exact (eq_refl (term16 A x y)). Qed.
Lemma lem4319973 {A : Type'} (y : A) (x : A) : term17 A y x.
Proof. exact (EQ_MP (@lem4319972 A y x) (@lem4319971 A x y)). Qed.
Lemma lem4319974 {A : Type'} (y : A) (x : A) (s : A -> Prop) : term18 A y x s.
Proof. exact (@lem4319973 A y x s). Qed.
Lemma lem4319975 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term18 A y x s) = ((term19 A x y s) = (term20 A y x s)).
Proof. exact (eq_refl (term18 A y x s)). Qed.
Lemma lem4319977 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term343 A B s) : term331 A B s t.
Proof. exact (@lem4319943 A B s h1 t). Qed.
Lemma lem4319978 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term331 A B s t) = (term332 A B s t).
Proof. exact (eq_refl (term331 A B s t)). Qed.
Lemma lem4319979 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term343 A B s) : term332 A B s t.
Proof. exact (EQ_MP (@lem4319978 A B s t) (@lem4319977 A B t s h1)). Qed.
Lemma lem4319980 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term95 A B s t) : term95 A B s t.
Proof. exact (h1). Qed.
Lemma lem4319981 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : term343 A B s) : term447 A B s t.
Proof. exact (@lem4319979 A B t s h2 (@lem4319980 A B s t h1)). Qed.
Lemma lem4319982 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term447 A B s t) = ((term447 A B s t) = True).
Proof. exact (@lem7 (term447 A B s t)). Qed.
Lemma lem4319983 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : term343 A B s) : (term447 A B s t) = True.
Proof. exact (EQ_MP (@lem4319982 A B s t) (@lem4319981 A B t s h1 h2)). Qed.
Lemma lem4319989 {A : Type'} (a : A) (s : A -> Prop) : term448 A a s.
Proof. exact (@lem82 (@IN A a s)). Qed.
Lemma lem4319996 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term449 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4319997 (p : Prop) (q : Prop) (p' : Prop) : term450 p q p'.
Proof. exact (fun q' : Prop => @lem4319996 p q p' q'). Qed.
Lemma lem4319998 (p : Prop) (q : Prop) : term451 p q.
Proof. exact (fun p' : Prop => @lem4319997 p q p'). Qed.
Lemma lem4319999 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term452 A B a s t.
Proof. exact (@lem4319998 (term453 A B a s t) (term454 A B a s t)). Qed.
Lemma lem4320000 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : term455 A B a s t p'.
Proof. exact (@lem4319999 A B a s t p'). Qed.
Lemma lem4320001 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : (term455 A B a s t p') = (term456 A B a s t p').
Proof. exact (eq_refl (term455 A B a s t p')). Qed.
Lemma lem4320002 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) : term456 A B a s t p'.
Proof. exact (EQ_MP (@lem4320001 A B a s t p') (@lem4320000 A B a s t p')). Qed.
Lemma lem4320003 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : term457 A B a s t p' q'.
Proof. exact (@lem4320002 A B a s t p' q'). Qed.
Lemma lem4320004 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : (term457 A B a s t p' q') = (term458 A B a s t p' q').
Proof. exact (eq_refl (term457 A B a s t p' q')). Qed.
Lemma lem4320005 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (p' : Prop) (q' : Prop) : term458 A B a s t p' q'.
Proof. exact (EQ_MP (@lem4320004 A B a s t p' q') (@lem4320003 A B a s t p' q')). Qed.
Lemma lem4320013 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term449 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4320014 (p : Prop) (q : Prop) (p' : Prop) : term450 p q p'.
Proof. exact (fun q' : Prop => @lem4320013 p q p' q'). Qed.
Lemma lem4320015 (p : Prop) (q : Prop) : term451 p q.
Proof. exact (fun p' : Prop => @lem4320014 p q p'). Qed.
Lemma lem4320016 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) : term459 A B a s t x'.
Proof. exact (@lem4320015 (term19 A x' a s) (term460 A B t x')). Qed.
Lemma lem4320017 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) : term461 A B a s t x' p'.
Proof. exact (@lem4320016 A B a s t x' p'). Qed.
Lemma lem4320018 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) : (term461 A B a s t x' p') = (term462 A B a s t x' p').
Proof. exact (eq_refl (term461 A B a s t x' p')). Qed.
Lemma lem4320019 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) : term462 A B a s t x' p'.
Proof. exact (EQ_MP (@lem4320018 A B a s t x' p') (@lem4320017 A B a s t x' p')). Qed.
Lemma lem4320020 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) (q' : Prop) : term463 A B a s t x' p' q'.
Proof. exact (@lem4320019 A B a s t x' p' q'). Qed.
Lemma lem4320021 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) (q' : Prop) : (term463 A B a s t x' p' q') = (term464 A B a s t x' p' q').
Proof. exact (eq_refl (term463 A B a s t x' p' q')). Qed.
Lemma lem4320022 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) (q' : Prop) : term464 A B a s t x' p' q'.
Proof. exact (EQ_MP (@lem4320021 A B a s t x' p' q') (@lem4320020 A B a s t x' p' q')). Qed.
Lemma lem4320024 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem4319975 A y x s) (@lem4319974 A y x s)). Qed.
Lemma lem4320025 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (@lem4320024 A y x s). Qed.
Lemma lem4320026 {A : Type'} (a : A) (x' : A) (s : A -> Prop) : (term19 A x' a s) = (term20 A a x' s).
Proof. exact (@lem4320025 A a x' s). Qed.
Lemma lem4320031 {A B : Type'} (t : type1413 A B) (a : A) (x' : A) (s : A -> Prop) (q' : Prop) : term465 A B t a x' s q'.
Proof. exact (@lem4320022 A B a s t x' (term20 A a x' s) q'). Qed.
Lemma lem4320032 {A B : Type'} (t : type1413 A B) (a : A) (x' : A) (s : A -> Prop) (q' : Prop) : term466 A B t a x' s q'.
Proof. exact (@lem4320031 A B t a x' s q' (@lem4320026 A a x' s)). Qed.
Lemma lem4320036 {A B : Type'} (t : type1413 A B) (x' : A) : (term460 A B t x') = (term460 A B t x').
Proof. exact (eq_refl (term460 A B t x')). Qed.
Lemma lem4320037 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) : term467 A B a s t x'.
Proof. exact (fun h0 : term20 A a x' s => @lem4320036 A B t x'). Qed.
Lemma lem4320038 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) : term468 A B a s t x'.
Proof. exact (@lem4320032 A B t a x' s (term460 A B t x')). Qed.
Lemma lem4320039 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) : (term469 A B a s t x') = (term470 A B a s t x').
Proof. exact (@lem4320038 A B a s t x' (@lem4320037 A B a s t x')). Qed.
Lemma lem4320071 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term471 A B a s t) = (term472 A B a s t).
Proof. exact (fun_ext (fun x' : A => @lem4320039 A B a s t x')). Qed.
Lemma lem4320103 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4320104 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term453 A B a s t) = (term473 A B a s t).
Proof. exact (MK_COMB (@lem4320103 A) (@lem4320071 A B a s t)). Qed.
Lemma lem4320140 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (q' : Prop) : term474 A B a s t q'.
Proof. exact (@lem4320005 A B a s t (term473 A B a s t) q'). Qed.
Lemma lem4320141 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (q' : Prop) : term475 A B a s t q'.
Proof. exact (@lem4320140 A B a s t q' (@lem4320104 A B a s t)). Qed.
Lemma lem4320142 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term473 A B a s t.
Proof. exact (h1). Qed.
Lemma lem4320143 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term476 A B a s t x'.
Proof. exact (@lem4320142 A B a s t h1 x'). Qed.
Lemma lem4320144 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x' : A) : (term476 A B a s t x') = (term470 A B a s t x').
Proof. exact (eq_refl (term476 A B a s t x')). Qed.
Lemma lem4320145 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term470 A B a s t x'.
Proof. exact (EQ_MP (@lem4320144 A B a s t x') (@lem4320143 A B x' a s t h1)). Qed.
Lemma lem4320146 {A : Type'} (a : A) (x' : A) (s : A -> Prop) (h1 : term20 A a x' s) : term20 A a x' s.
Proof. exact (h1). Qed.
Lemma lem4320147 {A B : Type'} (t : type1413 A B) (a : A) (x' : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term20 A a x' s) : term460 A B t x'.
Proof. exact (@lem4320145 A B x' a s t h1 (@lem4320146 A a x' s h2)). Qed.
Lemma lem4320148 {A B : Type'} (t : type1413 A B) (x' : A) : (term460 A B t x') = ((term460 A B t x') = True).
Proof. exact (@lem7 (term460 A B t x')). Qed.
Lemma lem4320149 {A B : Type'} (t : type1413 A B) (a : A) (x' : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term20 A a x' s) : (term460 A B t x') = True.
Proof. exact (EQ_MP (@lem4320148 A B t x') (@lem4320147 A B t a x' s h1 h2)). Qed.
Lemma lem4320156 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : (term477 A B a s t) = (term478 A B a s t)) : (term477 A B a s t) = (term478 A B a s t).
Proof. exact (h1). Qed.
Lemma lem4320157 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : (term477 A B a s t) = (term478 A B a s t)) : (term477 A B a s t) = (term478 A B a s t).
Proof. exact (@lem4320156 A B a s t h1). Qed.
Lemma lem4320168 {A B : Type'} : (@FINITE (prod A B)) = (@FINITE (prod A B)).
Proof. exact (eq_refl (@FINITE (prod A B))). Qed.
Lemma lem4320169 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : (term477 A B a s t) = (term478 A B a s t)) : (term454 A B a s t) = (term479 A B a s t).
Proof. exact (MK_COMB (@lem4320168 A B) (@lem4320157 A B a s t h1)). Qed.
Lemma lem4320171 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term445 A s t) = (term446 A s t).
Proof. exact (EQ_MP (@lem4319951 A s t) (@lem4319950 A s t)). Qed.
Lemma lem4320172 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (term480 A B s t) = (term481 A B s t).
Proof. exact (@lem4320171 (prod A B) s t). Qed.
Lemma lem4320173 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term479 A B a s t) = (term482 A B a s t).
Proof. exact (@lem4320172 A B (term483 A B t a) (term106 A B s t)). Qed.
Lemma lem4320177 {A B : Type'} (f : A -> B) (s : A -> Prop) : term484 A B f s.
Proof. exact (fun h0 : @FINITE A s => @lem4319962 A B f s h0). Qed.
Lemma lem4320178 {A B : Type'} (f : type1478 A B) (s : B -> Prop) : term485 A B f s.
Proof. exact (@lem4320177 B (prod A B) f s). Qed.
Lemma lem4320179 {A B : Type'} (t : type1413 A B) (a : A) : term486 A B t a.
Proof. exact (@lem4320178 A B (term487 A B a) (t a)). Qed.
Lemma lem4320181 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term488 A B a s t x'.
Proof. exact (fun h0 : term20 A a x' s => @lem4320149 A B t a x' s h1 h0). Qed.
Lemma lem4320182 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term488 A B a s t x'.
Proof. exact (@lem4320181 A B x' a s t h1). Qed.
Lemma lem4320183 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term489 A B s t a.
Proof. exact (@lem4320182 A B a a s t h1). Qed.
Lemma lem4320187 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4320188 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem4320187 A x). Qed.
Lemma lem4320189 {A : Type'} (a : A) : (a = a) = True.
Proof. exact (@lem4320188 A a). Qed.
Lemma lem4320190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4320191 {A : Type'} (a : A) : (term490 A a) = (or True).
Proof. exact (MK_COMB (@lem4320190) (@lem4320189 A a)). Qed.
Lemma lem4320193 {A : Type'} (a : A) (s : A -> Prop) (h1 : term314 A a s) : (@IN A a s) = False.
Proof. exact (@lem4319989 A a s (@lem4319945 A a s h1)). Qed.
Lemma lem4320194 {A : Type'} (a : A) (s : A -> Prop) (h1 : term314 A a s) : (term491 A a s) = (True \/ False).
Proof. exact (MK_COMB (@lem4320191 A a) (@lem4320193 A a s h1)). Qed.
Lemma lem4320196 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem4320197 : (True \/ False) = True.
Proof. exact (@lem4320196 False). Qed.
Lemma lem4320198 {A : Type'} (a : A) (s : A -> Prop) (h1 : term314 A a s) : (term491 A a s) = True.
Proof. exact (TRANS (@lem4320194 A a s h1) (@lem4320197)). Qed.
Lemma lem4320199 {A : Type'} (a : A) (s : A -> Prop) (h1 : term314 A a s) : True = (term491 A a s).
Proof. exact (SYM (@lem4320198 A a s h1)). Qed.
Lemma lem4320200 {A : Type'} (a : A) (s : A -> Prop) (h1 : term314 A a s) : term491 A a s.
Proof. exact (EQ_MP (@lem4320199 A a s h1) (@lem0)). Qed.
Lemma lem4320201 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term314 A a s) : (term460 A B t a) = True.
Proof. exact (@lem4320183 A B a s t h1 (@lem4320200 A a s h2)). Qed.
Lemma lem4320202 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term314 A a s) : True = (term460 A B t a).
Proof. exact (SYM (@lem4320201 A B t a s h1 h2)). Qed.
Lemma lem4320203 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term314 A a s) : term460 A B t a.
Proof. exact (EQ_MP (@lem4320202 A B t a s h1 h2) (@lem0)). Qed.
Lemma lem4320204 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term314 A a s) : (term492 A B t a) = True.
Proof. exact (@lem4320179 A B t a (@lem4320203 A B t a s h1 h2)). Qed.
Lemma lem4320205 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4320206 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term314 A a s) : (term493 A B t a) = (and True).
Proof. exact (MK_COMB (@lem4320205) (@lem4320204 A B t a s h1 h2)). Qed.
Lemma lem4320208 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term343 A B s) : term494 A B s t.
Proof. exact (fun h0 : term95 A B s t => @lem4319983 A B t s h0 h1). Qed.
Lemma lem4320209 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term343 A B s) : term494 A B s t.
Proof. exact (@lem4320208 A B t s h1). Qed.
Lemma lem4320217 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term449 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4320218 (p : Prop) (q : Prop) (p' : Prop) : term450 p q p'.
Proof. exact (fun q' : Prop => @lem4320217 p q p' q'). Qed.
Lemma lem4320219 (p : Prop) (q : Prop) : term451 p q.
Proof. exact (fun p' : Prop => @lem4320218 p q p'). Qed.
Lemma lem4320220 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) : term495 A B s t x'.
Proof. exact (@lem4320219 (@IN A x' s) (term460 A B t x')). Qed.
Lemma lem4320221 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) : term496 A B s t x' p'.
Proof. exact (@lem4320220 A B s t x' p'). Qed.
Lemma lem4320222 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) : (term496 A B s t x' p') = (term497 A B s t x' p').
Proof. exact (eq_refl (term496 A B s t x' p')). Qed.
Lemma lem4320223 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) : term497 A B s t x' p'.
Proof. exact (EQ_MP (@lem4320222 A B s t x' p') (@lem4320221 A B s t x' p')). Qed.
Lemma lem4320224 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) (q' : Prop) : term498 A B s t x' p' q'.
Proof. exact (@lem4320223 A B s t x' p' q'). Qed.
Lemma lem4320225 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) (q' : Prop) : (term498 A B s t x' p' q') = (term499 A B s t x' p' q').
Proof. exact (eq_refl (term498 A B s t x' p' q')). Qed.
Lemma lem4320226 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (p' : Prop) (q' : Prop) : term499 A B s t x' p' q'.
Proof. exact (EQ_MP (@lem4320225 A B s t x' p' q') (@lem4320224 A B s t x' p' q')). Qed.
Lemma lem4320227 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = (@IN A x' s).
Proof. exact (eq_refl (@IN A x' s)). Qed.
Lemma lem4320228 {A B : Type'} (t : type1413 A B) (x' : A) (s : A -> Prop) (q' : Prop) : term500 A B t x' s q'.
Proof. exact (@lem4320226 A B s t x' (@IN A x' s) q'). Qed.
Lemma lem4320229 {A B : Type'} (t : type1413 A B) (x' : A) (s : A -> Prop) (q' : Prop) : term501 A B t x' s q'.
Proof. exact (@lem4320228 A B t x' s q' (@lem4320227 A x' s)). Qed.
Lemma lem4320230 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem4320231 {A : Type'} (x' : A) (s : A -> Prop) : (@IN A x' s) = ((@IN A x' s) = True).
Proof. exact (@lem7 (@IN A x' s)). Qed.
Lemma lem4320234 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term488 A B a s t x'.
Proof. exact (fun h0 : term20 A a x' s => @lem4320149 A B t a x' s h1 h0). Qed.
Lemma lem4320235 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term488 A B a s t x'.
Proof. exact (@lem4320234 A B x' a s t h1). Qed.
Lemma lem4320241 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : (@IN A x' s) = True.
Proof. exact (EQ_MP (@lem4320231 A x' s) (@lem4320230 A x' s h1)). Qed.
Lemma lem4320242 {A : Type'} (x' : A) (a : A) : (term502 A x' a) = (term502 A x' a).
Proof. exact (eq_refl (term502 A x' a)). Qed.
Lemma lem4320243 {A : Type'} (a : A) (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : (term20 A a x' s) = (term503 A x' a).
Proof. exact (MK_COMB (@lem4320242 A x' a) (@lem4320241 A x' s h1)). Qed.
Lemma lem4320245 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4320246 {A : Type'} (x' : A) (a : A) : (term503 A x' a) = True.
Proof. exact (@lem4320245 (x' = a)). Qed.
Lemma lem4320247 {A : Type'} (a : A) (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : (term20 A a x' s) = True.
Proof. exact (TRANS (@lem4320243 A a x' s h1) (@lem4320246 A x' a)). Qed.
Lemma lem4320248 {A : Type'} (a : A) (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : True = (term20 A a x' s).
Proof. exact (SYM (@lem4320247 A a x' s h1)). Qed.
Lemma lem4320249 {A : Type'} (a : A) (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : term20 A a x' s.
Proof. exact (EQ_MP (@lem4320248 A a x' s h1) (@lem0)). Qed.
Lemma lem4320250 {A B : Type'} (a : A) (t : type1413 A B) (x' : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : @IN A x' s) : (term460 A B t x') = True.
Proof. exact (@lem4320235 A B x' a s t h1 (@lem4320249 A a x' s h2)). Qed.
Lemma lem4320251 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term504 A B s t x'.
Proof. exact (fun h0 : @IN A x' s => @lem4320250 A B a t x' s h1 h0). Qed.
Lemma lem4320252 {A B : Type'} (t : type1413 A B) (x' : A) (s : A -> Prop) : term505 A B t x' s.
Proof. exact (@lem4320229 A B t x' s True). Qed.
Lemma lem4320253 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : (term506 A B s t x') = (term507 A x' s).
Proof. exact (@lem4320252 A B t x' s (@lem4320251 A B x' a s t h1)). Qed.
Lemma lem4320255 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4320256 {A : Type'} (x' : A) (s : A -> Prop) : (term507 A x' s) = True.
Proof. exact (@lem4320255 (@IN A x' s)). Qed.
Lemma lem4320257 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : (term506 A B s t x') = True.
Proof. exact (TRANS (@lem4320253 A B x' a s t h1) (@lem4320256 A x' s)). Qed.
Lemma lem4320258 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : (term508 A B s t) = (term509 A).
Proof. exact (fun_ext (fun x' : A => @lem4320257 A B x' a s t h1)). Qed.
Lemma lem4320259 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4320260 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : (term95 A B s t) = (term510 A).
Proof. exact (MK_COMB (@lem4320259 A) (@lem4320258 A B a s t h1)). Qed.
Lemma lem4320262 {A : Type'} (t : Prop) : (term440 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4320263 {A : Type'} (t : Prop) : (term440 A t) = t.
Proof. exact (@lem4320262 A t). Qed.
Lemma lem4320264 {A : Type'} : (term510 A) = True.
Proof. exact (@lem4320263 A True). Qed.
Lemma lem4320265 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : (term95 A B s t) = True.
Proof. exact (TRANS (@lem4320260 A B a s t h1) (@lem4320264 A)). Qed.
Lemma lem4320266 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : True = (term95 A B s t).
Proof. exact (SYM (@lem4320265 A B a s t h1)). Qed.
Lemma lem4320267 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) : term95 A B s t.
Proof. exact (EQ_MP (@lem4320266 A B a s t h1) (@lem0)). Qed.
Lemma lem4320268 {A B : Type'} (a : A) (t : type1413 A B) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term343 A B s) : (term447 A B s t) = True.
Proof. exact (@lem4320209 A B t s h2 (@lem4320267 A B a s t h1)). Qed.
Lemma lem4320269 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term343 A B s) (h3 : term314 A a s) : (term482 A B a s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4320206 A B t a s h1 h3) (@lem4320268 A B a t s h1 h2)). Qed.
Lemma lem4320271 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4320272 : (True /\ True) = True.
Proof. exact (@lem4320271 True). Qed.
Lemma lem4320273 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term343 A B s) (h3 : term314 A a s) : (term482 A B a s t) = True.
Proof. exact (TRANS (@lem4320269 A B t a s h1 h2 h3) (@lem4320272)). Qed.
Lemma lem4320274 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term473 A B a s t) (h2 : term343 A B s) (h3 : term314 A a s) : (term479 A B a s t) = True.
Proof. exact (TRANS (@lem4320173 A B a s t) (@lem4320273 A B t a s h1 h2 h3)). Qed.
Lemma lem4320275 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term473 A B a s t) (h2 : term343 A B s) (h3 : term314 A a s) (h4 : (term477 A B a s t) = (term478 A B a s t)) : (term454 A B a s t) = True.
Proof. exact (TRANS (@lem4320169 A B a s t h4) (@lem4320274 A B t a s h1 h2 h3)). Qed.
Lemma lem4320276 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term343 A B s) (h2 : term314 A a s) (h3 : (term477 A B a s t) = (term478 A B a s t)) : term511 A B a s t.
Proof. exact (fun h0 : term473 A B a s t => @lem4320275 A B a s t h0 h1 h2 h3). Qed.
Lemma lem4320277 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term512 A B a s t.
Proof. exact (@lem4320141 A B a s t True). Qed.
Lemma lem4320278 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term343 A B s) (h2 : term314 A a s) (h3 : (term477 A B a s t) = (term478 A B a s t)) : (term513 A B a s t) = (term514 A B a s t).
Proof. exact (@lem4320277 A B a s t (@lem4320276 A B a s t h1 h2 h3)). Qed.
Lemma lem4320280 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4320281 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term514 A B a s t) = True.
Proof. exact (@lem4320280 (term473 A B a s t)). Qed.
Lemma lem4320282 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term343 A B s) (h2 : term314 A a s) (h3 : (term477 A B a s t) = (term478 A B a s t)) : (term513 A B a s t) = True.
Proof. exact (TRANS (@lem4320278 A B a s t h1 h2 h3) (@lem4320281 A B a s t)). Qed.
Lemma lem4320283 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term343 A B s) (h2 : term314 A a s) (h3 : (term477 A B a s t) = (term478 A B a s t)) : True = (term513 A B a s t).
Proof. exact (SYM (@lem4320282 A B a s t h1 h2 h3)). Qed.
Lemma lem4320284 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term343 A B s) (h2 : term314 A a s) (h3 : (term477 A B a s t) = (term478 A B a s t)) : term513 A B a s t.
Proof. exact (EQ_MP (@lem4320283 A B a s t h1 h2 h3) (@lem0)). Qed.
Lemma lem4320288 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term37 A s t).
Proof. exact (EQ_MP (@lem4318428 A s t) (@lem4318427 A s t)). Qed.
Lemma lem4320289 {A B : Type'} (s : type1210 A B) (t : type1210 A B) : (s = t) = (term389 A B s t).
Proof. exact (@lem4320288 (prod A B) s t). Qed.
Lemma lem4320290 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : ((term477 A B a s t) = (term478 A B a s t)) = (term515 A B a s t).
Proof. exact (@lem4320289 A B (term477 A B a s t) (term478 A B a s t)). Qed.
Lemma lem4320300 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term25 _83064 x P) = (term26 _83064 P x).
Proof. exact (EQ_MP (@lem4318413 _83064 P x) (@lem4318412 _83064 P x)). Qed.
Lemma lem4320301 {A B : Type'} (P : type914 A B) (x : prod A B) : (term391 A B x P) = (term392 A B P x).
Proof. exact (@lem4320300 (prod A B) P x). Qed.
Lemma lem4320302 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term516 A B x a s t) = (term517 A B a s t x).
Proof. exact (@lem4320301 A B (term518 A B a s t) x). Qed.
Lemma lem4320303 {A B : Type'} (GEN_PVAR_122 : prod A B) (a : A) (s : A -> Prop) (t : type1413 A B) : (term519 A B a s t GEN_PVAR_122) = (term520 A B GEN_PVAR_122 a s t).
Proof. exact (eq_refl (term519 A B a s t GEN_PVAR_122)). Qed.
Lemma lem4320304 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term521 A B a s t) = (term522 A B a s t).
Proof. exact (fun_ext (fun GEN_PVAR_122 : prod A B => @lem4320303 A B GEN_PVAR_122 a s t)). Qed.
Lemma lem4320305 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4320306 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term523 A B a s t) = (term477 A B a s t).
Proof. exact (MK_COMB (@lem4320305 A B) (@lem4320304 A B a s t)). Qed.
Lemma lem4320307 {A B : Type'} (x : prod A B) : (@IN (prod A B) x) = (@IN (prod A B) x).
Proof. exact (eq_refl (@IN (prod A B) x)). Qed.
Lemma lem4320308 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (t : type1413 A B) : (term516 A B x a s t) = (term524 A B x a s t).
Proof. exact (MK_COMB (@lem4320307 A B x) (@lem4320306 A B a s t)). Qed.
Lemma lem4320309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4320310 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (t : type1413 A B) : (term525 A B x a s t) = (term526 A B x a s t).
Proof. exact (MK_COMB (@lem4320309) (@lem4320308 A B x a s t)). Qed.
Lemma lem4320311 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (t : type1413 A B) : (term517 A B a s t x) = (term527 A B x a s t).
Proof. exact (eq_refl (term517 A B a s t x)). Qed.
Lemma lem4320312 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (t : type1413 A B) : ((term516 A B x a s t) = (term517 A B a s t x)) = ((term524 A B x a s t) = (term527 A B x a s t)).
Proof. exact (MK_COMB (@lem4320310 A B x a s t) (@lem4320311 A B x a s t)). Qed.
Lemma lem4320313 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (t : type1413 A B) : (term524 A B x a s t) = (term527 A B x a s t).
Proof. exact (EQ_MP (@lem4320312 A B x a s t) (@lem4320302 A B a s t x)). Qed.
Lemma lem4320323 {A B : Type'} (f : A -> B) (y : A) : (term405 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4320324 {A B : Type'} (f : type1532 A B) (y : Prop) : (term406 A B f y) = (f y).
Proof. exact (@lem4320323 Prop (type1210 A B) f y). Qed.
Lemma lem4320325 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term528 A B x a s y t x') = (term529 A B x a s y t x').
Proof. exact (@lem4320324 A B (term409 A B x) (term530 A B a s y t x')). Qed.
Lemma lem4320326 {A B : Type'} (p : Prop) (x : prod A B) : (term411 A B x p) = (term412 A B p x).
Proof. exact (eq_refl (term411 A B x p)). Qed.
Lemma lem4320327 {A B : Type'} (x : prod A B) : (term413 A B x) = (term409 A B x).
Proof. exact (fun_ext (fun p : Prop => @lem4320326 A B p x)). Qed.
Lemma lem4320328 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term530 A B a s y t x) = (term530 A B a s y t x).
Proof. exact (eq_refl (term530 A B a s y t x)). Qed.
Lemma lem4320329 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term528 A B x a s y t x') = (term529 A B x a s y t x').
Proof. exact (MK_COMB (@lem4320327 A B x) (@lem4320328 A B a s y t x')). Qed.
Lemma lem4320330 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem4320331 {A B : Type'} (x : prod A B) (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term531 A B x a s y t x') = (term532 A B x a s y t x').
Proof. exact (MK_COMB (@lem4320330 A B) (@lem4320329 A B x a s y t x')). Qed.
Lemma lem4320332 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term529 A B x' a s y t x) = (term533 A B a s y t x x').
Proof. exact (eq_refl (term529 A B x' a s y t x)). Qed.
Lemma lem4320333 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : ((term528 A B x' a s y t x) = (term529 A B x' a s y t x)) = ((term529 A B x' a s y t x) = (term533 A B a s y t x x')).
Proof. exact (MK_COMB (@lem4320331 A B x' a s y t x) (@lem4320332 A B a s y t x x')). Qed.
Lemma lem4320334 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term529 A B x' a s y t x) = (term533 A B a s y t x x').
Proof. exact (EQ_MP (@lem4320333 A B a s y t x x') (@lem4320325 A B x' a s y t x)). Qed.
Lemma lem4320340 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (EQ_MP (@lem4318375 A y x s) (@lem4318374 A y x s)). Qed.
Lemma lem4320341 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term19 A x y s) = (term20 A y x s).
Proof. exact (@lem4320340 A y x s). Qed.
Lemma lem4320342 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term19 A x a s) = (term20 A a x s).
Proof. exact (@lem4320341 A a x s). Qed.
Lemma lem4320349 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4320350 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term534 A x a s) = (term535 A a x s).
Proof. exact (MK_COMB (@lem4320349) (@lem4320342 A a x s)). Qed.
Lemma lem4320351 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term288 A B y t x) = (term288 A B y t x).
Proof. exact (eq_refl (term288 A B y t x)). Qed.
Lemma lem4320352 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term530 A B a s y t x) = (term536 A B a s y t x).
Proof. exact (MK_COMB (@lem4320350 A a x s) (@lem4320351 A B y t x)). Qed.
Lemma lem4320355 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4320356 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term537 A B a s y t x) = (term538 A B a s y t x).
Proof. exact (MK_COMB (@lem4320355) (@lem4320352 A B a s y t x)). Qed.
Lemma lem4320361 {A B : Type'} (x : prod A B) (t : prod A B) : (x = t) = (x = t).
Proof. exact (eq_refl (x = t)). Qed.
Lemma lem4320362 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) (t' : prod A B) : (term539 A B a s y t x x' t') = (term540 A B a s y t x x' t').
Proof. exact (MK_COMB (@lem4320356 A B a s y t x) (@lem4320361 A B x' t')). Qed.
Lemma lem4320365 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term533 A B a s y t x x') = (term541 A B a s y t x x').
Proof. exact (fun_ext (fun t' : prod A B => @lem4320362 A B a s y t x x' t')). Qed.
Lemma lem4320366 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term529 A B x' a s y t x) = (term541 A B a s y t x x').
Proof. exact (TRANS (@lem4320334 A B a s y t x x') (@lem4320365 A B a s y t x x')). Qed.
Lemma lem4320367 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4320368 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term542 A B x a s t x' y) = (term543 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4320366 A B a s y t x' x) (@lem4320367 A B x' y)). Qed.
Lemma lem4320370 {A B : Type'} (f : A -> B) (y : A) : (term405 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4320371 {A B : Type'} (f : type1210 A B) (y : prod A B) : (term425 A B f y) = (f y).
Proof. exact (@lem4320370 (prod A B) Prop f y). Qed.
Lemma lem4320372 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term544 A B a s t x x' y) = (term543 A B a s t x x' y).
Proof. exact (@lem4320371 A B (term541 A B a s y t x' x) (@pair A B x' y)). Qed.
Lemma lem4320373 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) (t' : prod A B) : (term545 A B a s y t x x' t') = (term540 A B a s y t x x' t').
Proof. exact (eq_refl (term545 A B a s y t x x' t')). Qed.
Lemma lem4320374 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term546 A B a s y t x x') = (term541 A B a s y t x x').
Proof. exact (fun_ext (fun t' : prod A B => @lem4320373 A B a s y t x x' t')). Qed.
Lemma lem4320375 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4320376 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term544 A B a s t x x' y) = (term543 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4320374 A B a s y t x' x) (@lem4320375 A B x' y)). Qed.
Lemma lem4320377 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4320378 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term547 A B a s t x x' y) = (term548 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4320377) (@lem4320376 A B a s t x x' y)). Qed.
Lemma lem4320379 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term543 A B a s t x x' y) = (term549 A B a s t x x' y).
Proof. exact (eq_refl (term543 A B a s t x x' y)). Qed.
Lemma lem4320380 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : ((term544 A B a s t x x' y) = (term543 A B a s t x x' y)) = ((term543 A B a s t x x' y) = (term549 A B a s t x x' y)).
Proof. exact (MK_COMB (@lem4320378 A B a s t x x' y) (@lem4320379 A B a s t x x' y)). Qed.
Lemma lem4320381 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term543 A B a s t x x' y) = (term549 A B a s t x x' y).
Proof. exact (EQ_MP (@lem4320380 A B a s t x x' y) (@lem4320372 A B a s t x x' y)). Qed.
Lemma lem4320396 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term542 A B x a s t x' y) = (term549 A B a s t x x' y).
Proof. exact (TRANS (@lem4320368 A B a s t x x' y) (@lem4320381 A B a s t x x' y)). Qed.
Lemma lem4320397 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term550 A B x a s t x') = (term551 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4320396 A B a s t x x' y)). Qed.
Lemma lem4320398 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4320399 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term552 A B x a s t x') = (term553 A B a s t x x').
Proof. exact (MK_COMB (@lem4320398 B) (@lem4320397 A B a s t x x')). Qed.
Lemma lem4320404 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term554 A B x a s t) = (term555 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4320399 A B a s t x x')). Qed.
Lemma lem4320405 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4320406 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term527 A B x a s t) = (term556 A B a s t x).
Proof. exact (MK_COMB (@lem4320405 A) (@lem4320404 A B a s t x)). Qed.
Lemma lem4320411 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term524 A B x a s t) = (term556 A B a s t x).
Proof. exact (TRANS (@lem4320313 A B x a s t) (@lem4320406 A B a s t x)). Qed.
Lemma lem4320412 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4320413 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term526 A B x a s t) = (term557 A B a s t x).
Proof. exact (MK_COMB (@lem4320412) (@lem4320411 A B a s t x)). Qed.
Lemma lem4320415 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term12 A x s t) = (term13 A s x t).
Proof. exact (EQ_MP (@lem4318366 A s x t) (@lem4318365 A s t x)). Qed.
Lemma lem4320416 {A B : Type'} (s : type1210 A B) (x : prod A B) (t : type1210 A B) : (term558 A B x s t) = (term559 A B s x t).
Proof. exact (@lem4320415 (prod A B) s x t). Qed.
Lemma lem4320417 {A B : Type'} (a : A) (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term560 A B x a s t) = (term561 A B a x s t).
Proof. exact (@lem4320416 A B (term483 A B t a) x (term106 A B s t)). Qed.
Lemma lem4320421 {A B : Type'} (y : B) (f : A -> B) (s : A -> Prop) : (term32 A B y f s) = (term33 A B y f s).
Proof. exact (EQ_MP (@lem4318422 A B y f s) (@lem4318421 A B y s f)). Qed.
Lemma lem4320422 {A B : Type'} (y : prod A B) (f : type1478 A B) (s : B -> Prop) : (term562 A B y f s) = (term563 A B y f s).
Proof. exact (@lem4320421 B (prod A B) y f s). Qed.
Lemma lem4320423 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term564 A B x t a) = (term565 A B x t a).
Proof. exact (@lem4320422 A B x (term487 A B a) (t a)). Qed.
Lemma lem4320435 {A B : Type'} (f : A -> B) (y : A) : (term405 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4320436 {A B : Type'} (f : type1478 A B) (y : B) : (term566 A B f y) = (f y).
Proof. exact (@lem4320435 B (prod A B) f y). Qed.
Lemma lem4320437 {A B : Type'} (a : A) (x : B) : (term567 A B a x) = (term568 A B a x).
Proof. exact (@lem4320436 A B (term487 A B a) x). Qed.
Lemma lem4320438 {A B : Type'} (a : A) (y : B) : (term568 A B a y) = (@pair A B a y).
Proof. exact (eq_refl (term568 A B a y)). Qed.
Lemma lem4320439 {A B : Type'} (a : A) : (term569 A B a) = (term487 A B a).
Proof. exact (fun_ext (fun y : B => @lem4320438 A B a y)). Qed.
Lemma lem4320440 {B : Type'} (x : B) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4320441 {A B : Type'} (a : A) (x : B) : (term567 A B a x) = (term568 A B a x).
Proof. exact (MK_COMB (@lem4320439 A B a) (@lem4320440 B x)). Qed.
Lemma lem4320442 {A B : Type'} : (@eq (prod A B)) = (@eq (prod A B)).
Proof. exact (eq_refl (@eq (prod A B))). Qed.
Lemma lem4320443 {A B : Type'} (a : A) (x : B) : (term570 A B a x) = (term571 A B a x).
Proof. exact (MK_COMB (@lem4320442 A B) (@lem4320441 A B a x)). Qed.
Lemma lem4320444 {A B : Type'} (a : A) (x : B) : (term568 A B a x) = (@pair A B a x).
Proof. exact (eq_refl (term568 A B a x)). Qed.
Lemma lem4320445 {A B : Type'} (a : A) (x : B) : ((term567 A B a x) = (term568 A B a x)) = ((term568 A B a x) = (@pair A B a x)).
Proof. exact (MK_COMB (@lem4320443 A B a x) (@lem4320444 A B a x)). Qed.
Lemma lem4320446 {A B : Type'} (a : A) (x : B) : (term568 A B a x) = (@pair A B a x).
Proof. exact (EQ_MP (@lem4320445 A B a x) (@lem4320437 A B a x)). Qed.
Lemma lem4320447 {A B : Type'} (x : prod A B) : (@eq (prod A B) x) = (@eq (prod A B) x).
Proof. exact (eq_refl (@eq (prod A B) x)). Qed.
Lemma lem4320448 {A B : Type'} (x : prod A B) (a : A) (x' : B) : (x = (term568 A B a x')) = (x = (@pair A B a x')).
Proof. exact (MK_COMB (@lem4320447 A B x) (@lem4320446 A B a x')). Qed.
Lemma lem4320453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4320454 {A B : Type'} (x : prod A B) (a : A) (x' : B) : (term572 A B x a x') = (term573 A B x a x').
Proof. exact (MK_COMB (@lem4320453) (@lem4320448 A B x a x')). Qed.
Lemma lem4320455 {A B : Type'} (x : B) (t : type1413 A B) (a : A) : (term288 A B x t a) = (term288 A B x t a).
Proof. exact (eq_refl (term288 A B x t a)). Qed.
Lemma lem4320456 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term574 A B x x' t a) = (term575 A B x x' t a).
Proof. exact (MK_COMB (@lem4320454 A B x a x') (@lem4320455 A B x' t a)). Qed.
Lemma lem4320459 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term576 A B x t a) = (term577 A B x t a).
Proof. exact (fun_ext (fun x' : B => @lem4320456 A B x x' t a)). Qed.
Lemma lem4320460 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4320461 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term565 A B x t a) = (term578 A B x t a).
Proof. exact (MK_COMB (@lem4320460 B) (@lem4320459 A B x t a)). Qed.
Lemma lem4320466 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term564 A B x t a) = (term578 A B x t a).
Proof. exact (TRANS (@lem4320423 A B x t a) (@lem4320461 A B x t a)). Qed.
Lemma lem4320467 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4320468 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term579 A B x t a) = (term580 A B x t a).
Proof. exact (MK_COMB (@lem4320467) (@lem4320466 A B x t a)). Qed.
Lemma lem4320470 {_83064 : Type'} (P : type919 _83064) (x : _83064) : (term25 _83064 x P) = (term26 _83064 P x).
Proof. exact (EQ_MP (@lem4318413 _83064 P x) (@lem4318412 _83064 P x)). Qed.
Lemma lem4320471 {A B : Type'} (P : type914 A B) (x : prod A B) : (term391 A B x P) = (term392 A B P x).
Proof. exact (@lem4320470 (prod A B) P x). Qed.
Lemma lem4320472 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term581 A B x s t) = (term582 A B s t x).
Proof. exact (@lem4320471 A B (term583 A B s t) x). Qed.
Lemma lem4320473 {A B : Type'} (GEN_PVAR_123 : prod A B) (s : A -> Prop) (t : type1413 A B) : (term584 A B s t GEN_PVAR_123) = (term194 A B GEN_PVAR_123 s t).
Proof. exact (eq_refl (term584 A B s t GEN_PVAR_123)). Qed.
Lemma lem4320474 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term585 A B s t) = (term196 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_123 : prod A B => @lem4320473 A B GEN_PVAR_123 s t)). Qed.
Lemma lem4320475 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4320476 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term586 A B s t) = (term106 A B s t).
Proof. exact (MK_COMB (@lem4320475 A B) (@lem4320474 A B s t)). Qed.
Lemma lem4320477 {A B : Type'} (x : prod A B) : (@IN (prod A B) x) = (@IN (prod A B) x).
Proof. exact (eq_refl (@IN (prod A B) x)). Qed.
Lemma lem4320478 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term581 A B x s t) = (term587 A B x s t).
Proof. exact (MK_COMB (@lem4320477 A B x) (@lem4320476 A B s t)). Qed.
Lemma lem4320479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4320480 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term588 A B x s t) = (term589 A B x s t).
Proof. exact (MK_COMB (@lem4320479) (@lem4320478 A B x s t)). Qed.
Lemma lem4320481 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term582 A B s t x) = (term590 A B x s t).
Proof. exact (eq_refl (term582 A B s t x)). Qed.
Lemma lem4320482 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : ((term581 A B x s t) = (term582 A B s t x)) = ((term587 A B x s t) = (term590 A B x s t)).
Proof. exact (MK_COMB (@lem4320480 A B x s t) (@lem4320481 A B x s t)). Qed.
Lemma lem4320483 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) : (term587 A B x s t) = (term590 A B x s t).
Proof. exact (EQ_MP (@lem4320482 A B x s t) (@lem4320472 A B s t x)). Qed.
Lemma lem4320493 {A B : Type'} (f : A -> B) (y : A) : (term405 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4320494 {A B : Type'} (f : type1532 A B) (y : Prop) : (term406 A B f y) = (f y).
Proof. exact (@lem4320493 Prop (type1210 A B) f y). Qed.
Lemma lem4320495 {A B : Type'} (x : prod A B) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term591 A B x s y t x') = (term592 A B x s y t x').
Proof. exact (@lem4320494 A B (term409 A B x) (term182 A B s y t x')). Qed.
Lemma lem4320496 {A B : Type'} (p : Prop) (x : prod A B) : (term411 A B x p) = (term412 A B p x).
Proof. exact (eq_refl (term411 A B x p)). Qed.
Lemma lem4320497 {A B : Type'} (x : prod A B) : (term413 A B x) = (term409 A B x).
Proof. exact (fun_ext (fun p : Prop => @lem4320496 A B p x)). Qed.
Lemma lem4320498 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term182 A B s y t x) = (term182 A B s y t x).
Proof. exact (eq_refl (term182 A B s y t x)). Qed.
Lemma lem4320499 {A B : Type'} (x : prod A B) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term591 A B x s y t x') = (term592 A B x s y t x').
Proof. exact (MK_COMB (@lem4320497 A B x) (@lem4320498 A B s y t x')). Qed.
Lemma lem4320500 {A B : Type'} : (@eq ((prod A B) -> Prop)) = (@eq ((prod A B) -> Prop)).
Proof. exact (eq_refl (@eq ((prod A B) -> Prop))). Qed.
Lemma lem4320501 {A B : Type'} (x : prod A B) (s : A -> Prop) (y : B) (t : type1413 A B) (x' : A) : (term593 A B x s y t x') = (term594 A B x s y t x').
Proof. exact (MK_COMB (@lem4320500 A B) (@lem4320499 A B x s y t x')). Qed.
Lemma lem4320502 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term592 A B x' s y t x) = (term595 A B s y t x x').
Proof. exact (eq_refl (term592 A B x' s y t x)). Qed.
Lemma lem4320503 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : ((term591 A B x' s y t x) = (term592 A B x' s y t x)) = ((term592 A B x' s y t x) = (term595 A B s y t x x')).
Proof. exact (MK_COMB (@lem4320501 A B x' s y t x) (@lem4320502 A B s y t x x')). Qed.
Lemma lem4320504 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term592 A B x' s y t x) = (term595 A B s y t x x').
Proof. exact (EQ_MP (@lem4320503 A B s y t x x') (@lem4320495 A B x' s y t x)). Qed.
Lemma lem4320513 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4320514 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term596 A B x s t x' y) = (term597 A B s t x x' y).
Proof. exact (MK_COMB (@lem4320504 A B s y t x' x) (@lem4320513 A B x' y)). Qed.
Lemma lem4320516 {A B : Type'} (f : A -> B) (y : A) : (term405 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4320517 {A B : Type'} (f : type1210 A B) (y : prod A B) : (term425 A B f y) = (f y).
Proof. exact (@lem4320516 (prod A B) Prop f y). Qed.
Lemma lem4320518 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term598 A B s t x x' y) = (term597 A B s t x x' y).
Proof. exact (@lem4320517 A B (term595 A B s y t x' x) (@pair A B x' y)). Qed.
Lemma lem4320519 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) (t' : prod A B) : (term599 A B s y t x x' t') = (term600 A B s y t x x' t').
Proof. exact (eq_refl (term599 A B s y t x x' t')). Qed.
Lemma lem4320520 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) (x' : prod A B) : (term601 A B s y t x x') = (term595 A B s y t x x').
Proof. exact (fun_ext (fun t' : prod A B => @lem4320519 A B s y t x x' t')). Qed.
Lemma lem4320521 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4320522 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term598 A B s t x x' y) = (term597 A B s t x x' y).
Proof. exact (MK_COMB (@lem4320520 A B s y t x' x) (@lem4320521 A B x' y)). Qed.
Lemma lem4320523 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4320524 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term602 A B s t x x' y) = (term603 A B s t x x' y).
Proof. exact (MK_COMB (@lem4320523) (@lem4320522 A B s t x x' y)). Qed.
Lemma lem4320525 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term597 A B s t x x' y) = (term604 A B s t x x' y).
Proof. exact (eq_refl (term597 A B s t x x' y)). Qed.
Lemma lem4320526 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : ((term598 A B s t x x' y) = (term597 A B s t x x' y)) = ((term597 A B s t x x' y) = (term604 A B s t x x' y)).
Proof. exact (MK_COMB (@lem4320524 A B s t x x' y) (@lem4320525 A B s t x x' y)). Qed.
Lemma lem4320527 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term597 A B s t x x' y) = (term604 A B s t x x' y).
Proof. exact (EQ_MP (@lem4320526 A B s t x x' y) (@lem4320518 A B s t x x' y)). Qed.
Lemma lem4320536 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term596 A B x s t x' y) = (term604 A B s t x x' y).
Proof. exact (TRANS (@lem4320514 A B s t x x' y) (@lem4320527 A B s t x x' y)). Qed.
Lemma lem4320537 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term605 A B x s t x') = (term606 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4320536 A B s t x x' y)). Qed.
Lemma lem4320538 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4320539 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term607 A B x s t x') = (term608 A B s t x x').
Proof. exact (MK_COMB (@lem4320538 B) (@lem4320537 A B s t x x')). Qed.
Lemma lem4320544 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term609 A B x s t) = (term610 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4320539 A B s t x x')). Qed.
Lemma lem4320545 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4320546 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term590 A B x s t) = (term611 A B s t x).
Proof. exact (MK_COMB (@lem4320545 A) (@lem4320544 A B s t x)). Qed.
Lemma lem4320551 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term587 A B x s t) = (term611 A B s t x).
Proof. exact (TRANS (@lem4320483 A B x s t) (@lem4320546 A B s t x)). Qed.
Lemma lem4320552 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term561 A B a x s t) = (term612 A B a s t x).
Proof. exact (MK_COMB (@lem4320468 A B x t a) (@lem4320551 A B s t x)). Qed.
Lemma lem4320555 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term560 A B x a s t) = (term612 A B a s t x).
Proof. exact (TRANS (@lem4320417 A B a x s t) (@lem4320552 A B a s t x)). Qed.
Lemma lem4320556 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : ((term524 A B x a s t) = (term560 A B x a s t)) = ((term556 A B a s t x) = (term612 A B a s t x)).
Proof. exact (MK_COMB (@lem4320413 A B a s t x) (@lem4320555 A B a s t x)). Qed.
Lemma lem4320561 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term613 A B a s t) = (term614 A B a s t).
Proof. exact (fun_ext (fun x : prod A B => @lem4320556 A B a s t x)). Qed.
Lemma lem4320562 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4320563 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term515 A B a s t) = (term615 A B a s t).
Proof. exact (MK_COMB (@lem4320562 A B) (@lem4320561 A B a s t)). Qed.
Lemma lem4320568 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : ((term477 A B a s t) = (term478 A B a s t)) = (term615 A B a s t).
Proof. exact (TRANS (@lem4320290 A B a s t) (@lem4320563 A B a s t)). Qed.
Lemma lem4320569 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term615 A B a s t) = ((term477 A B a s t) = (term478 A B a s t)).
Proof. exact (SYM (@lem4320568 A B a s t)). Qed.
Lemma lem4320571 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4320572 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term615 A B a s t) = (term616 A B a s t).
Proof. exact (@lem4320571 (term615 A B a s t)). Qed.
Lemma lem4320573 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term616 A B a s t) = (term615 A B a s t).
Proof. exact (SYM (@lem4320572 A B a s t)). Qed.
Lemma lem4320574 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term617 A B a s t) : term617 A B a s t.
Proof. exact (h1). Qed.
Lemma lem4320577 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term616 A B a s t) : term616 A B a s t.
Proof. exact (h1). Qed.
Lemma lem4320578 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term618 A B a s t.
Proof. exact (fun h0 : term616 A B a s t => @lem4320577 A B a s t h0). Qed.
Lemma lem4320579 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term618 A B a s t) : term618 A B a s t.
Proof. exact (h1). Qed.
Lemma lem4320580 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term616 A B a s t) : term616 A B a s t.
Proof. exact (h1). Qed.
Lemma lem4320581 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term616 A B a s t) (h2 : term618 A B a s t) : term616 A B a s t.
Proof. exact (@lem4320579 A B a s t h2 (@lem4320580 A B a s t h1)). Qed.
Lemma lem4320582 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term616 A B a s t) : term619 A B a s t.
Proof. exact (fun h0 : term618 A B a s t => @lem4320581 A B a s t h1 h0). Qed.
Lemma lem4320583 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term618 A B a s t) : term618 A B a s t.
Proof. exact (h1). Qed.
Lemma lem4320584 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term616 A B a s t) (h2 : term618 A B a s t) : term616 A B a s t.
Proof. exact (@lem4320582 A B a s t h1 (@lem4320583 A B a s t h2)). Qed.
Lemma lem4320585 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term618 A B a s t) : term618 A B a s t.
Proof. exact (fun h0 : term616 A B a s t => @lem4320584 A B a s t h0 h1). Qed.
Lemma lem4320586 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term620 A B a s t.
Proof. exact (fun h0 : term618 A B a s t => @lem4320585 A B a s t h0). Qed.
Lemma lem4320589 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term618 A B a s t.
Proof. exact (@lem4320586 A B a s t (@lem4320578 A B a s t)). Qed.
Lemma lem4320590 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term618 A B a s t.
Proof. exact (@lem4320589 A B a s t). Qed.
Lemma lem4320604 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4320605 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term616 A B a s t) = (term621 A B a s t).
Proof. exact (@lem4320604 (term617 A B a s t)). Qed.
Lemma lem4320607 (t : Prop) : (term267 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4320608 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term621 A B a s t) = (term615 A B a s t).
Proof. exact (@lem4320607 (term615 A B a s t)). Qed.
Lemma lem4320613 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term616 A B a s t) = (term615 A B a s t).
Proof. exact (TRANS (@lem4320605 A B a s t) (@lem4320608 A B a s t)). Qed.
Lemma lem4320780 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term622 A B s t) = (term623 A B s t).
Proof. exact (fun_ext (fun a : A => @lem4320613 A B a s t)). Qed.
Lemma lem4320781 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4320782 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term624 A B s t) = (term625 A B s t).
Proof. exact (MK_COMB (@lem4320781 A) (@lem4320780 A B s t)). Qed.
Lemma lem4320787 {A B : Type'} (t : type1413 A B) : (term626 A B t) = (term627 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4320782 A B s t)). Qed.
Lemma lem4320788 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4320789 {A B : Type'} (t : type1413 A B) : (term628 A B t) = (term629 A B t).
Proof. exact (MK_COMB (@lem4320788 A) (@lem4320787 A B t)). Qed.
Lemma lem4320794 {A B : Type'} : (term630 A B) = (term631 A B).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4320789 A B t)). Qed.
Lemma lem4320795 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4320804 {A B : Type'} : (term632 A B) = (term633 A B).
Proof. exact (MK_COMB (@lem4320795 A B) (@lem4320794 A B)). Qed.
Lemma lem4320813 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term604 A B s t x x' y) = (term604 A B s t x x' y).
Proof. exact (eq_refl (term604 A B s t x x' y)). Qed.
Lemma lem4320814 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term606 A B s t x x') = (term606 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4320813 A B s t x x' y)). Qed.
Lemma lem4320815 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4320816 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term608 A B s t x x') = (term608 A B s t x x').
Proof. exact (MK_COMB (@lem4320815 B) (@lem4320814 A B s t x x')). Qed.
Lemma lem4320817 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term610 A B s t x) = (term610 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4320816 A B s t x x')). Qed.
Lemma lem4320818 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4320819 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term611 A B s t x) = (term611 A B s t x).
Proof. exact (MK_COMB (@lem4320818 A) (@lem4320817 A B s t x)). Qed.
Lemma lem4320824 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term575 A B x x' t a) = (term575 A B x x' t a).
Proof. exact (eq_refl (term575 A B x x' t a)). Qed.
Lemma lem4320825 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term577 A B x t a) = (term577 A B x t a).
Proof. exact (fun_ext (fun x' : B => @lem4320824 A B x x' t a)). Qed.
Lemma lem4320826 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4320827 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term578 A B x t a) = (term578 A B x t a).
Proof. exact (MK_COMB (@lem4320826 B) (@lem4320825 A B x t a)). Qed.
Lemma lem4320828 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4320829 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term580 A B x t a) = (term580 A B x t a).
Proof. exact (MK_COMB (@lem4320828) (@lem4320827 A B x t a)). Qed.
Lemma lem4320830 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term612 A B a s t x) = (term612 A B a s t x).
Proof. exact (MK_COMB (@lem4320829 A B x t a) (@lem4320819 A B s t x)). Qed.
Lemma lem4320843 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term549 A B a s t x x' y) = (term549 A B a s t x x' y).
Proof. exact (eq_refl (term549 A B a s t x x' y)). Qed.
Lemma lem4320844 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term551 A B a s t x x') = (term551 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4320843 A B a s t x x' y)). Qed.
Lemma lem4320845 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4320846 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term553 A B a s t x x') = (term553 A B a s t x x').
Proof. exact (MK_COMB (@lem4320845 B) (@lem4320844 A B a s t x x')). Qed.
Lemma lem4320847 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term555 A B a s t x) = (term555 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4320846 A B a s t x x')). Qed.
Lemma lem4320848 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4320849 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term556 A B a s t x) = (term556 A B a s t x).
Proof. exact (MK_COMB (@lem4320848 A) (@lem4320847 A B a s t x)). Qed.
Lemma lem4320850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4320851 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term557 A B a s t x) = (term557 A B a s t x).
Proof. exact (MK_COMB (@lem4320850) (@lem4320849 A B a s t x)). Qed.
Lemma lem4320852 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : ((term556 A B a s t x) = (term612 A B a s t x)) = ((term556 A B a s t x) = (term612 A B a s t x)).
Proof. exact (MK_COMB (@lem4320851 A B a s t x) (@lem4320830 A B a s t x)). Qed.
Lemma lem4320853 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term614 A B a s t) = (term614 A B a s t).
Proof. exact (fun_ext (fun x : prod A B => @lem4320852 A B a s t x)). Qed.
Lemma lem4320854 {A B : Type'} : (@all (prod A B)) = (@all (prod A B)).
Proof. exact (eq_refl (@all (prod A B))). Qed.
Lemma lem4320855 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term615 A B a s t) = (term615 A B a s t).
Proof. exact (MK_COMB (@lem4320854 A B) (@lem4320853 A B a s t)). Qed.
Lemma lem4320856 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term623 A B s t) = (term623 A B s t).
Proof. exact (fun_ext (fun a : A => @lem4320855 A B a s t)). Qed.
Lemma lem4320857 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4320858 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term625 A B s t) = (term625 A B s t).
Proof. exact (MK_COMB (@lem4320857 A) (@lem4320856 A B s t)). Qed.
Lemma lem4320859 {A B : Type'} (t : type1413 A B) : (term627 A B t) = (term627 A B t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4320858 A B s t)). Qed.
Lemma lem4320860 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4320861 {A B : Type'} (t : type1413 A B) : (term629 A B t) = (term629 A B t).
Proof. exact (MK_COMB (@lem4320860 A) (@lem4320859 A B t)). Qed.
Lemma lem4320862 {A B : Type'} : (term631 A B) = (term631 A B).
Proof. exact (fun_ext (fun t : type1413 A B => @lem4320861 A B t)). Qed.
Lemma lem4320863 {A B : Type'} : (@all (A -> B -> Prop)) = (@all (A -> B -> Prop)).
Proof. exact (eq_refl (@all (A -> B -> Prop))). Qed.
Lemma lem4320864 {A B : Type'} : (term633 A B) = (term633 A B).
Proof. exact (MK_COMB (@lem4320863 A B) (@lem4320862 A B)). Qed.
Lemma lem4320935 {A B : Type'} : (term632 A B) = (term633 A B).
Proof. exact (TRANS (@lem4320804 A B) (@lem4320864 A B)). Qed.
Lemma lem4320936 {A B : Type'} : (term633 A B) = (term632 A B).
Proof. exact (SYM (@lem4320935 A B)). Qed.
Lemma lem4320938 (p : Prop) : p = (term260 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4320939 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : ((term556 A B a s t x) = (term612 A B a s t x)) = (term634 A B a s t x).
Proof. exact (@lem4320938 ((term556 A B a s t x) = (term612 A B a s t x))). Qed.
Lemma lem4320940 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term634 A B a s t x) = ((term556 A B a s t x) = (term612 A B a s t x)).
Proof. exact (SYM (@lem4320939 A B a s t x)). Qed.
Lemma lem4320941 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term635 A B a s t x) : term635 A B a s t x.
Proof. exact (h1). Qed.
Lemma lem4320950 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term636 A a x s) = (term637 A a x s).
Proof. exact (@lem17160 (x = a) (@IN A x s)). Qed.
Lemma lem4320954 {A B : Type'} (y : B) (t : type1413 A B) (x : A) : (term316 A B y t x) = (term316 A B y t x).
Proof. exact (eq_refl (term316 A B y t x)). Qed.
Lemma lem4320956 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4320957 {A : Type'} (a : A) (x : A) (s : A -> Prop) : (term638 A a x s) = (term639 A a x s).
Proof. exact (MK_COMB (@lem4320956) (@lem4320950 A a x s)). Qed.
Lemma lem4320958 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term640 A B a s y t x) = (term641 A B a s y t x).
Proof. exact (MK_COMB (@lem4320957 A a x s) (@lem4320954 A B y t x)). Qed.
Lemma lem4320959 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term642 A B a s y t x) = (term640 A B a s y t x).
Proof. exact (@lem17045 (term20 A a x s) (term288 A B y t x)). Qed.
Lemma lem4320960 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term642 A B a s y t x) = (term641 A B a s y t x).
Proof. exact (TRANS (@lem4320959 A B a s y t x) (@lem4320958 A B a s y t x)). Qed.
Lemma lem4320964 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term643 A B x x' y) = (term643 A B x x' y).
Proof. exact (eq_refl (term643 A B x x' y)). Qed.
Lemma lem4320966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4320967 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term644 A B a s y t x) = (term645 A B a s y t x).
Proof. exact (MK_COMB (@lem4320966) (@lem4320960 A B a s y t x)). Qed.
Lemma lem4320968 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term646 A B a s t x x' y) = (term647 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4320967 A B a s y t x') (@lem4320964 A B x x' y)). Qed.
Lemma lem4320969 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term648 A B a s t x x' y) = (term646 A B a s t x x' y).
Proof. exact (@lem17045 (term536 A B a s y t x') (x = (@pair A B x' y))). Qed.
Lemma lem4320970 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term648 A B a s t x x' y) = (term647 A B a s t x x' y).
Proof. exact (TRANS (@lem4320969 A B a s t x x' y) (@lem4320968 A B a s t x x' y)). Qed.
Lemma lem4320973 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term549 A B a s t x x' y) = (term549 A B a s t x x' y).
Proof. exact (eq_refl (term549 A B a s t x x' y)). Qed.
Lemma lem4320974 {B : Type'} (P : B -> Prop) : (term293 B P) = (term294 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4320975 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term649 A B a s t x x') = (term650 A B a s t x x').
Proof. exact (@lem4320974 B (term551 A B a s t x x')). Qed.
Lemma lem4320976 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term651 A B a s t x x' y) = (term549 A B a s t x x' y).
Proof. exact (eq_refl (term651 A B a s t x x' y)). Qed.
Lemma lem4320977 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4320978 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term652 A B a s t x x' y) = (term648 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4320977) (@lem4320976 A B a s t x x' y)). Qed.
Lemma lem4320979 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term652 A B a s t x x' y) = (term647 A B a s t x x' y).
Proof. exact (TRANS (@lem4320978 A B a s t x x' y) (@lem4320970 A B a s t x x' y)). Qed.
Lemma lem4320980 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term653 A B a s t x x') = (term654 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4320979 A B a s t x x' y)). Qed.
Lemma lem4320981 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4320982 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term650 A B a s t x x') = (term655 A B a s t x x').
Proof. exact (MK_COMB (@lem4320981 B) (@lem4320980 A B a s t x x')). Qed.
Lemma lem4320983 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term649 A B a s t x x') = (term655 A B a s t x x').
Proof. exact (TRANS (@lem4320975 A B a s t x x') (@lem4320982 A B a s t x x')). Qed.
Lemma lem4320984 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term551 A B a s t x x') = (term551 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4320973 A B a s t x x' y)). Qed.
Lemma lem4320985 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4320986 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term553 A B a s t x x') = (term553 A B a s t x x').
Proof. exact (MK_COMB (@lem4320985 B) (@lem4320984 A B a s t x x')). Qed.
Lemma lem4320987 {A : Type'} (P : A -> Prop) : (term293 A P) = (term294 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4320988 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term656 A B a s t x) = (term657 A B a s t x).
Proof. exact (@lem4320987 A (term555 A B a s t x)). Qed.
Lemma lem4320989 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term658 A B a s t x x') = (term553 A B a s t x x').
Proof. exact (eq_refl (term658 A B a s t x x')). Qed.
Lemma lem4320990 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4320991 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term659 A B a s t x x') = (term649 A B a s t x x').
Proof. exact (MK_COMB (@lem4320990) (@lem4320989 A B a s t x x')). Qed.
Lemma lem4320992 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term659 A B a s t x x') = (term655 A B a s t x x').
Proof. exact (TRANS (@lem4320991 A B a s t x x') (@lem4320983 A B a s t x x')). Qed.
Lemma lem4320993 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term660 A B a s t x) = (term661 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4320992 A B a s t x x')). Qed.
Lemma lem4320994 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4320995 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term657 A B a s t x) = (term662 A B a s t x).
Proof. exact (MK_COMB (@lem4320994 A) (@lem4320993 A B a s t x)). Qed.
Lemma lem4320996 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term656 A B a s t x) = (term662 A B a s t x).
Proof. exact (TRANS (@lem4320988 A B a s t x) (@lem4320995 A B a s t x)). Qed.
Lemma lem4320997 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term555 A B a s t x) = (term555 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4320986 A B a s t x x')). Qed.
Lemma lem4320998 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4320999 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term556 A B a s t x) = (term556 A B a s t x).
Proof. exact (MK_COMB (@lem4320998 A) (@lem4320997 A B a s t x)). Qed.
Lemma lem4321008 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term663 A B x x' t a) = (term664 A B x x' t a).
Proof. exact (@lem17045 (x = (@pair A B a x')) (term288 A B x' t a)). Qed.
Lemma lem4321011 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term575 A B x x' t a) = (term575 A B x x' t a).
Proof. exact (eq_refl (term575 A B x x' t a)). Qed.
Lemma lem4321012 {B : Type'} (P : B -> Prop) : (term293 B P) = (term294 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4321013 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term665 A B x t a) = (term666 A B x t a).
Proof. exact (@lem4321012 B (term577 A B x t a)). Qed.
Lemma lem4321014 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term667 A B x t a x') = (term575 A B x x' t a).
Proof. exact (eq_refl (term667 A B x t a x')). Qed.
Lemma lem4321015 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4321016 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term668 A B x t a x') = (term663 A B x x' t a).
Proof. exact (MK_COMB (@lem4321015) (@lem4321014 A B x x' t a)). Qed.
Lemma lem4321017 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term668 A B x t a x') = (term664 A B x x' t a).
Proof. exact (TRANS (@lem4321016 A B x x' t a) (@lem4321008 A B x x' t a)). Qed.
Lemma lem4321018 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term669 A B x t a) = (term670 A B x t a).
Proof. exact (fun_ext (fun x' : B => @lem4321017 A B x x' t a)). Qed.
Lemma lem4321019 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4321020 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term666 A B x t a) = (term671 A B x t a).
Proof. exact (MK_COMB (@lem4321019 B) (@lem4321018 A B x t a)). Qed.
Lemma lem4321021 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term665 A B x t a) = (term671 A B x t a).
Proof. exact (TRANS (@lem4321013 A B x t a) (@lem4321020 A B x t a)). Qed.
Lemma lem4321022 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term577 A B x t a) = (term577 A B x t a).
Proof. exact (fun_ext (fun x' : B => @lem4321011 A B x x' t a)). Qed.
Lemma lem4321023 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321024 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term578 A B x t a) = (term578 A B x t a).
Proof. exact (MK_COMB (@lem4321023 B) (@lem4321022 A B x t a)). Qed.
Lemma lem4321033 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term286 A B s y t x) = (term287 A B s y t x).
Proof. exact (@lem17045 (@IN A x s) (term288 A B y t x)). Qed.
Lemma lem4321037 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term643 A B x x' y) = (term643 A B x x' y).
Proof. exact (eq_refl (term643 A B x x' y)). Qed.
Lemma lem4321039 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321040 {A B : Type'} (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term672 A B s y t x) = (term673 A B s y t x).
Proof. exact (MK_COMB (@lem4321039) (@lem4321033 A B s y t x)). Qed.
Lemma lem4321041 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term674 A B s t x x' y) = (term675 A B s t x x' y).
Proof. exact (MK_COMB (@lem4321040 A B s y t x') (@lem4321037 A B x x' y)). Qed.
Lemma lem4321042 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term676 A B s t x x' y) = (term674 A B s t x x' y).
Proof. exact (@lem17045 (term182 A B s y t x') (x = (@pair A B x' y))). Qed.
Lemma lem4321043 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term676 A B s t x x' y) = (term675 A B s t x x' y).
Proof. exact (TRANS (@lem4321042 A B s t x x' y) (@lem4321041 A B s t x x' y)). Qed.
Lemma lem4321046 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term604 A B s t x x' y) = (term604 A B s t x x' y).
Proof. exact (eq_refl (term604 A B s t x x' y)). Qed.
Lemma lem4321047 {B : Type'} (P : B -> Prop) : (term293 B P) = (term294 B P).
Proof. exact (@lem18394 B P). Qed.
Lemma lem4321048 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term677 A B s t x x') = (term678 A B s t x x').
Proof. exact (@lem4321047 B (term606 A B s t x x')). Qed.
Lemma lem4321049 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term679 A B s t x x' y) = (term604 A B s t x x' y).
Proof. exact (eq_refl (term679 A B s t x x' y)). Qed.
Lemma lem4321050 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4321051 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term680 A B s t x x' y) = (term676 A B s t x x' y).
Proof. exact (MK_COMB (@lem4321050) (@lem4321049 A B s t x x' y)). Qed.
Lemma lem4321052 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term680 A B s t x x' y) = (term675 A B s t x x' y).
Proof. exact (TRANS (@lem4321051 A B s t x x' y) (@lem4321043 A B s t x x' y)). Qed.
Lemma lem4321053 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term681 A B s t x x') = (term682 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4321052 A B s t x x' y)). Qed.
Lemma lem4321054 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4321055 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term678 A B s t x x') = (term683 A B s t x x').
Proof. exact (MK_COMB (@lem4321054 B) (@lem4321053 A B s t x x')). Qed.
Lemma lem4321056 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term677 A B s t x x') = (term683 A B s t x x').
Proof. exact (TRANS (@lem4321048 A B s t x x') (@lem4321055 A B s t x x')). Qed.
Lemma lem4321057 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term606 A B s t x x') = (term606 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4321046 A B s t x x' y)). Qed.
Lemma lem4321058 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321059 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term608 A B s t x x') = (term608 A B s t x x').
Proof. exact (MK_COMB (@lem4321058 B) (@lem4321057 A B s t x x')). Qed.
Lemma lem4321060 {A : Type'} (P : A -> Prop) : (term293 A P) = (term294 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem4321061 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term684 A B s t x) = (term685 A B s t x).
Proof. exact (@lem4321060 A (term610 A B s t x)). Qed.
Lemma lem4321062 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term686 A B s t x x') = (term608 A B s t x x').
Proof. exact (eq_refl (term686 A B s t x x')). Qed.
Lemma lem4321063 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4321064 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term687 A B s t x x') = (term677 A B s t x x').
Proof. exact (MK_COMB (@lem4321063) (@lem4321062 A B s t x x')). Qed.
Lemma lem4321065 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term687 A B s t x x') = (term683 A B s t x x').
Proof. exact (TRANS (@lem4321064 A B s t x x') (@lem4321056 A B s t x x')). Qed.
Lemma lem4321066 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term688 A B s t x) = (term689 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321065 A B s t x x')). Qed.
Lemma lem4321067 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4321068 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term685 A B s t x) = (term690 A B s t x).
Proof. exact (MK_COMB (@lem4321067 A) (@lem4321066 A B s t x)). Qed.
Lemma lem4321069 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term684 A B s t x) = (term690 A B s t x).
Proof. exact (TRANS (@lem4321061 A B s t x) (@lem4321068 A B s t x)). Qed.
Lemma lem4321070 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term610 A B s t x) = (term610 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321059 A B s t x x')). Qed.
Lemma lem4321071 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321072 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term611 A B s t x) = (term611 A B s t x).
Proof. exact (MK_COMB (@lem4321071 A) (@lem4321070 A B s t x)). Qed.
Lemma lem4321073 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321074 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term691 A B x t a) = (term692 A B x t a).
Proof. exact (MK_COMB (@lem4321073) (@lem4321021 A B x t a)). Qed.
Lemma lem4321075 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term693 A B a s t x) = (term694 A B a s t x).
Proof. exact (MK_COMB (@lem4321074 A B x t a) (@lem4321069 A B s t x)). Qed.
Lemma lem4321076 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term695 A B a s t x) = (term693 A B a s t x).
Proof. exact (@lem17160 (term578 A B x t a) (term611 A B s t x)). Qed.
Lemma lem4321077 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term695 A B a s t x) = (term694 A B a s t x).
Proof. exact (TRANS (@lem4321076 A B a s t x) (@lem4321075 A B a s t x)). Qed.
Lemma lem4321078 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321079 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term580 A B x t a) = (term580 A B x t a).
Proof. exact (MK_COMB (@lem4321078) (@lem4321024 A B x t a)). Qed.
Lemma lem4321080 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term612 A B a s t x) = (term612 A B a s t x).
Proof. exact (MK_COMB (@lem4321079 A B x t a) (@lem4321072 A B s t x)). Qed.
Lemma lem4321081 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321082 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term696 A B a s t x) = (term697 A B a s t x).
Proof. exact (MK_COMB (@lem4321081) (@lem4320996 A B a s t x)). Qed.
Lemma lem4321083 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term698 A B a s t x) = (term699 A B a s t x).
Proof. exact (MK_COMB (@lem4321082 A B a s t x) (@lem4321080 A B a s t x)). Qed.
Lemma lem4321084 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321085 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term700 A B a s t x) = (term700 A B a s t x).
Proof. exact (MK_COMB (@lem4321084) (@lem4320999 A B a s t x)). Qed.
Lemma lem4321086 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term701 A B a s t x) = (term702 A B a s t x).
Proof. exact (MK_COMB (@lem4321085 A B a s t x) (@lem4321077 A B a s t x)). Qed.
Lemma lem4321087 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321088 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term703 A B a s t x) = (term704 A B a s t x).
Proof. exact (MK_COMB (@lem4321087) (@lem4321086 A B a s t x)). Qed.
Lemma lem4321089 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term705 A B a s t x) = (term706 A B a s t x).
Proof. exact (MK_COMB (@lem4321088 A B a s t x) (@lem4321083 A B a s t x)). Qed.
Lemma lem4321090 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term635 A B a s t x) = (term705 A B a s t x).
Proof. exact (@lem17646 (term556 A B a s t x) (term612 A B a s t x)). Qed.
Lemma lem4321091 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term635 A B a s t x) = (term706 A B a s t x).
Proof. exact (TRANS (@lem4321090 A B a s t x) (@lem4321089 A B a s t x)). Qed.
Lemma lem4321398 {A : Type'} (P : A -> Prop) (Q : Prop) : (term707 A P Q) = (term708 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4321399 {A : Type'} (P : A -> Prop) (Q : Prop) : (term707 A P Q) = (term708 A P Q).
Proof. exact (@lem4321398 A P Q). Qed.
Lemma lem4321400 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term709 A B a s t x) = (term710 A B a s t x).
Proof. exact (@lem4321399 A (term555 A B a s t x) (term694 A B a s t x)). Qed.
Lemma lem4321401 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term658 A B a s t x x') = (term553 A B a s t x x').
Proof. exact (eq_refl (term658 A B a s t x x')). Qed.
Lemma lem4321402 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term711 A B a s t x) = (term555 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321401 A B a s t x x')). Qed.
Lemma lem4321403 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321404 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term712 A B a s t x) = (term556 A B a s t x).
Proof. exact (MK_COMB (@lem4321403 A) (@lem4321402 A B a s t x)). Qed.
Lemma lem4321405 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321406 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term713 A B a s t x) = (term700 A B a s t x).
Proof. exact (MK_COMB (@lem4321405) (@lem4321404 A B a s t x)). Qed.
Lemma lem4321407 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term694 A B a s t x) = (term694 A B a s t x).
Proof. exact (eq_refl (term694 A B a s t x)). Qed.
Lemma lem4321408 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term709 A B a s t x) = (term702 A B a s t x).
Proof. exact (MK_COMB (@lem4321406 A B a s t x) (@lem4321407 A B a s t x)). Qed.
Lemma lem4321409 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321410 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term714 A B a s t x) = (term715 A B a s t x).
Proof. exact (MK_COMB (@lem4321409) (@lem4321408 A B a s t x)). Qed.
Lemma lem4321411 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term658 A B a s t x x') = (term553 A B a s t x x').
Proof. exact (eq_refl (term658 A B a s t x x')). Qed.
Lemma lem4321412 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321413 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term716 A B a s t x x') = (term717 A B a s t x x').
Proof. exact (MK_COMB (@lem4321412) (@lem4321411 A B a s t x x')). Qed.
Lemma lem4321414 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term694 A B a s t x) = (term694 A B a s t x).
Proof. exact (eq_refl (term694 A B a s t x)). Qed.
Lemma lem4321415 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term718 A B x a s t x') = (term719 A B x a s t x').
Proof. exact (MK_COMB (@lem4321413 A B a s t x' x) (@lem4321414 A B a s t x')). Qed.
Lemma lem4321416 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term720 A B a s t x) = (term721 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321415 A B x' a s t x)). Qed.
Lemma lem4321417 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321418 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term710 A B a s t x) = (term722 A B a s t x).
Proof. exact (MK_COMB (@lem4321417 A) (@lem4321416 A B a s t x)). Qed.
Lemma lem4321419 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : ((term709 A B a s t x) = (term710 A B a s t x)) = ((term702 A B a s t x) = (term722 A B a s t x)).
Proof. exact (MK_COMB (@lem4321410 A B a s t x) (@lem4321418 A B a s t x)). Qed.
Lemma lem4321420 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term702 A B a s t x) = (term722 A B a s t x).
Proof. exact (EQ_MP (@lem4321419 A B a s t x) (@lem4321400 A B a s t x)). Qed.
Lemma lem4321422 {A : Type'} (P : A -> Prop) (Q : Prop) : (term707 A P Q) = (term708 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4321423 {B : Type'} (P : B -> Prop) (Q : Prop) : (term707 B P Q) = (term708 B P Q).
Proof. exact (@lem4321422 B P Q). Qed.
Lemma lem4321424 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term723 A B x a s t x') = (term724 A B x a s t x').
Proof. exact (@lem4321423 B (term551 A B a s t x' x) (term694 A B a s t x')). Qed.
Lemma lem4321425 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term651 A B a s t x x' y) = (term549 A B a s t x x' y).
Proof. exact (eq_refl (term651 A B a s t x x' y)). Qed.
Lemma lem4321426 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term725 A B a s t x x') = (term551 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4321425 A B a s t x x' y)). Qed.
Lemma lem4321427 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321428 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term726 A B a s t x x') = (term553 A B a s t x x').
Proof. exact (MK_COMB (@lem4321427 B) (@lem4321426 A B a s t x x')). Qed.
Lemma lem4321429 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321430 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term727 A B a s t x x') = (term717 A B a s t x x').
Proof. exact (MK_COMB (@lem4321429) (@lem4321428 A B a s t x x')). Qed.
Lemma lem4321431 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term694 A B a s t x) = (term694 A B a s t x).
Proof. exact (eq_refl (term694 A B a s t x)). Qed.
Lemma lem4321432 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term723 A B x a s t x') = (term719 A B x a s t x').
Proof. exact (MK_COMB (@lem4321430 A B a s t x' x) (@lem4321431 A B a s t x')). Qed.
Lemma lem4321433 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321434 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term728 A B x a s t x') = (term729 A B x a s t x').
Proof. exact (MK_COMB (@lem4321433) (@lem4321432 A B x a s t x')). Qed.
Lemma lem4321435 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term651 A B a s t x x' y) = (term549 A B a s t x x' y).
Proof. exact (eq_refl (term651 A B a s t x x' y)). Qed.
Lemma lem4321436 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321437 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term730 A B a s t x x' y) = (term731 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4321436) (@lem4321435 A B a s t x x' y)). Qed.
Lemma lem4321438 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term694 A B a s t x) = (term694 A B a s t x).
Proof. exact (eq_refl (term694 A B a s t x)). Qed.
Lemma lem4321439 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term732 A B x y a s t x') = (term733 A B x y a s t x').
Proof. exact (MK_COMB (@lem4321437 A B a s t x' x y) (@lem4321438 A B a s t x')). Qed.
Lemma lem4321440 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term734 A B x a s t x') = (term735 A B x a s t x').
Proof. exact (fun_ext (fun y : B => @lem4321439 A B x y a s t x')). Qed.
Lemma lem4321441 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321442 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term724 A B x a s t x') = (term736 A B x a s t x').
Proof. exact (MK_COMB (@lem4321441 B) (@lem4321440 A B x a s t x')). Qed.
Lemma lem4321443 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term723 A B x a s t x') = (term724 A B x a s t x')) = ((term719 A B x a s t x') = (term736 A B x a s t x')).
Proof. exact (MK_COMB (@lem4321434 A B x a s t x') (@lem4321442 A B x a s t x')). Qed.
Lemma lem4321444 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term719 A B x a s t x') = (term736 A B x a s t x').
Proof. exact (EQ_MP (@lem4321443 A B x a s t x') (@lem4321424 A B x a s t x')). Qed.
Lemma lem4321445 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term721 A B a s t x) = (term737 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321444 A B x' a s t x)). Qed.
Lemma lem4321446 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321447 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term722 A B a s t x) = (term738 A B a s t x).
Proof. exact (MK_COMB (@lem4321446 A) (@lem4321445 A B a s t x)). Qed.
Lemma lem4321448 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term702 A B a s t x) = (term738 A B a s t x).
Proof. exact (TRANS (@lem4321420 A B a s t x) (@lem4321447 A B a s t x)). Qed.
Lemma lem4321449 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321450 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term704 A B a s t x) = (term739 A B a s t x).
Proof. exact (MK_COMB (@lem4321449) (@lem4321448 A B a s t x)). Qed.
Lemma lem4321454 {A : Type'} (P : A -> Prop) (Q : Prop) : (term740 A P Q) = (term741 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4321455 {B : Type'} (P : B -> Prop) (Q : Prop) : (term740 B P Q) = (term741 B P Q).
Proof. exact (@lem4321454 B P Q). Qed.
Lemma lem4321456 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term742 A B a s t x) = (term743 A B a s t x).
Proof. exact (@lem4321455 B (term577 A B x t a) (term611 A B s t x)). Qed.
Lemma lem4321457 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term667 A B x t a x') = (term575 A B x x' t a).
Proof. exact (eq_refl (term667 A B x t a x')). Qed.
Lemma lem4321458 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term744 A B x t a) = (term577 A B x t a).
Proof. exact (fun_ext (fun x' : B => @lem4321457 A B x x' t a)). Qed.
Lemma lem4321459 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321460 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term745 A B x t a) = (term578 A B x t a).
Proof. exact (MK_COMB (@lem4321459 B) (@lem4321458 A B x t a)). Qed.
Lemma lem4321461 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321462 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term746 A B x t a) = (term580 A B x t a).
Proof. exact (MK_COMB (@lem4321461) (@lem4321460 A B x t a)). Qed.
Lemma lem4321463 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term611 A B s t x) = (term611 A B s t x).
Proof. exact (eq_refl (term611 A B s t x)). Qed.
Lemma lem4321464 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term742 A B a s t x) = (term612 A B a s t x).
Proof. exact (MK_COMB (@lem4321462 A B x t a) (@lem4321463 A B s t x)). Qed.
Lemma lem4321465 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321466 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term747 A B a s t x) = (term748 A B a s t x).
Proof. exact (MK_COMB (@lem4321465) (@lem4321464 A B a s t x)). Qed.
Lemma lem4321467 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term667 A B x t a x') = (term575 A B x x' t a).
Proof. exact (eq_refl (term667 A B x t a x')). Qed.
Lemma lem4321468 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321469 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term749 A B x t a x') = (term750 A B x x' t a).
Proof. exact (MK_COMB (@lem4321468) (@lem4321467 A B x x' t a)). Qed.
Lemma lem4321470 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term611 A B s t x) = (term611 A B s t x).
Proof. exact (eq_refl (term611 A B s t x)). Qed.
Lemma lem4321471 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term751 A B a x s t x') = (term752 A B x a s t x').
Proof. exact (MK_COMB (@lem4321469 A B x' x t a) (@lem4321470 A B s t x')). Qed.
Lemma lem4321472 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term753 A B a s t x) = (term754 A B a s t x).
Proof. exact (fun_ext (fun x' : B => @lem4321471 A B x' a s t x)). Qed.
Lemma lem4321473 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321474 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term743 A B a s t x) = (term755 A B a s t x).
Proof. exact (MK_COMB (@lem4321473 B) (@lem4321472 A B a s t x)). Qed.
Lemma lem4321475 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : ((term742 A B a s t x) = (term743 A B a s t x)) = ((term612 A B a s t x) = (term755 A B a s t x)).
Proof. exact (MK_COMB (@lem4321466 A B a s t x) (@lem4321474 A B a s t x)). Qed.
Lemma lem4321476 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term612 A B a s t x) = (term755 A B a s t x).
Proof. exact (EQ_MP (@lem4321475 A B a s t x) (@lem4321456 A B a s t x)). Qed.
Lemma lem4321478 {A : Type'} (P : Prop) (Q : A -> Prop) : (term756 A P Q) = (term757 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4321479 {A : Type'} (P : Prop) (Q : A -> Prop) : (term756 A P Q) = (term757 A P Q).
Proof. exact (@lem4321478 A P Q). Qed.
Lemma lem4321480 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term758 A B x a s t x') = (term759 A B x a s t x').
Proof. exact (@lem4321479 A (term575 A B x' x t a) (term610 A B s t x')). Qed.
Lemma lem4321481 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term686 A B s t x x') = (term608 A B s t x x').
Proof. exact (eq_refl (term686 A B s t x x')). Qed.
Lemma lem4321482 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term760 A B s t x) = (term610 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321481 A B s t x x')). Qed.
Lemma lem4321483 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321484 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term761 A B s t x) = (term611 A B s t x).
Proof. exact (MK_COMB (@lem4321483 A) (@lem4321482 A B s t x)). Qed.
Lemma lem4321485 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term750 A B x x' t a) = (term750 A B x x' t a).
Proof. exact (eq_refl (term750 A B x x' t a)). Qed.
Lemma lem4321486 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term758 A B x a s t x') = (term752 A B x a s t x').
Proof. exact (MK_COMB (@lem4321485 A B x' x t a) (@lem4321484 A B s t x')). Qed.
Lemma lem4321487 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321488 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term762 A B x a s t x') = (term763 A B x a s t x').
Proof. exact (MK_COMB (@lem4321487) (@lem4321486 A B x a s t x')). Qed.
Lemma lem4321489 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term686 A B s t x x') = (term608 A B s t x x').
Proof. exact (eq_refl (term686 A B s t x x')). Qed.
Lemma lem4321490 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term750 A B x x' t a) = (term750 A B x x' t a).
Proof. exact (eq_refl (term750 A B x x' t a)). Qed.
Lemma lem4321491 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term764 A B x a s t x' x'') = (term765 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321490 A B x' x t a) (@lem4321489 A B s t x' x'')). Qed.
Lemma lem4321492 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term766 A B x a s t x') = (term767 A B x a s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4321491 A B x a s t x' x'')). Qed.
Lemma lem4321493 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321494 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term759 A B x a s t x') = (term768 A B x a s t x').
Proof. exact (MK_COMB (@lem4321493 A) (@lem4321492 A B x a s t x')). Qed.
Lemma lem4321495 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term758 A B x a s t x') = (term759 A B x a s t x')) = ((term752 A B x a s t x') = (term768 A B x a s t x')).
Proof. exact (MK_COMB (@lem4321488 A B x a s t x') (@lem4321494 A B x a s t x')). Qed.
Lemma lem4321496 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term752 A B x a s t x') = (term768 A B x a s t x').
Proof. exact (EQ_MP (@lem4321495 A B x a s t x') (@lem4321480 A B x a s t x')). Qed.
Lemma lem4321498 {A : Type'} (P : Prop) (Q : A -> Prop) : (term756 A P Q) = (term757 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4321499 {B : Type'} (P : Prop) (Q : B -> Prop) : (term756 B P Q) = (term757 B P Q).
Proof. exact (@lem4321498 B P Q). Qed.
Lemma lem4321500 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term769 A B x a s t x' x'') = (term770 A B x a s t x' x'').
Proof. exact (@lem4321499 B (term575 A B x' x t a) (term606 A B s t x' x'')). Qed.
Lemma lem4321501 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term679 A B s t x x' y) = (term604 A B s t x x' y).
Proof. exact (eq_refl (term679 A B s t x x' y)). Qed.
Lemma lem4321502 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term771 A B s t x x') = (term606 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4321501 A B s t x x' y)). Qed.
Lemma lem4321503 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321504 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term772 A B s t x x') = (term608 A B s t x x').
Proof. exact (MK_COMB (@lem4321503 B) (@lem4321502 A B s t x x')). Qed.
Lemma lem4321505 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term750 A B x x' t a) = (term750 A B x x' t a).
Proof. exact (eq_refl (term750 A B x x' t a)). Qed.
Lemma lem4321506 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term769 A B x a s t x' x'') = (term765 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321505 A B x' x t a) (@lem4321504 A B s t x' x'')). Qed.
Lemma lem4321507 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321508 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term773 A B x a s t x' x'') = (term774 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321507) (@lem4321506 A B x a s t x' x'')). Qed.
Lemma lem4321509 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term679 A B s t x x' y) = (term604 A B s t x x' y).
Proof. exact (eq_refl (term679 A B s t x x' y)). Qed.
Lemma lem4321510 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term750 A B x x' t a) = (term750 A B x x' t a).
Proof. exact (eq_refl (term750 A B x x' t a)). Qed.
Lemma lem4321511 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y : B) : (term775 A B x a s t x' x'' y) = (term776 A B x a s t x' x'' y).
Proof. exact (MK_COMB (@lem4321510 A B x' x t a) (@lem4321509 A B s t x' x'' y)). Qed.
Lemma lem4321512 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term777 A B x a s t x' x'') = (term778 A B x a s t x' x'').
Proof. exact (fun_ext (fun y : B => @lem4321511 A B x a s t x' x'' y)). Qed.
Lemma lem4321513 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321514 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term770 A B x a s t x' x'') = (term779 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321513 B) (@lem4321512 A B x a s t x' x'')). Qed.
Lemma lem4321515 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : ((term769 A B x a s t x' x'') = (term770 A B x a s t x' x'')) = ((term765 A B x a s t x' x'') = (term779 A B x a s t x' x'')).
Proof. exact (MK_COMB (@lem4321508 A B x a s t x' x'') (@lem4321514 A B x a s t x' x'')). Qed.
Lemma lem4321516 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term765 A B x a s t x' x'') = (term779 A B x a s t x' x'').
Proof. exact (EQ_MP (@lem4321515 A B x a s t x' x'') (@lem4321500 A B x a s t x' x'')). Qed.
Lemma lem4321517 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term767 A B x a s t x') = (term780 A B x a s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4321516 A B x a s t x' x'')). Qed.
Lemma lem4321518 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321519 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term768 A B x a s t x') = (term781 A B x a s t x').
Proof. exact (MK_COMB (@lem4321518 A) (@lem4321517 A B x a s t x')). Qed.
Lemma lem4321520 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term752 A B x a s t x') = (term781 A B x a s t x').
Proof. exact (TRANS (@lem4321496 A B x a s t x') (@lem4321519 A B x a s t x')). Qed.
Lemma lem4321521 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term754 A B a s t x) = (term782 A B a s t x).
Proof. exact (fun_ext (fun x' : B => @lem4321520 A B x' a s t x)). Qed.
Lemma lem4321522 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321523 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term755 A B a s t x) = (term783 A B a s t x).
Proof. exact (MK_COMB (@lem4321522 B) (@lem4321521 A B a s t x)). Qed.
Lemma lem4321524 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term612 A B a s t x) = (term783 A B a s t x).
Proof. exact (TRANS (@lem4321476 A B a s t x) (@lem4321523 A B a s t x)). Qed.
Lemma lem4321525 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (eq_refl (term697 A B a s t x)). Qed.
Lemma lem4321526 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term699 A B a s t x) = (term784 A B a s t x).
Proof. exact (MK_COMB (@lem4321525 A B a s t x) (@lem4321524 A B a s t x)). Qed.
Lemma lem4321528 {A : Type'} (P : Prop) (Q : A -> Prop) : (term785 A P Q) = (term786 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4321529 {B : Type'} (P : Prop) (Q : B -> Prop) : (term785 B P Q) = (term786 B P Q).
Proof. exact (@lem4321528 B P Q). Qed.
Lemma lem4321530 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term787 A B a s t x) = (term788 A B a s t x).
Proof. exact (@lem4321529 B (term662 A B a s t x) (term782 A B a s t x)). Qed.
Lemma lem4321531 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term789 A B a s t x' x) = (term781 A B x a s t x').
Proof. exact (eq_refl (term789 A B a s t x' x)). Qed.
Lemma lem4321532 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term790 A B a s t x) = (term782 A B a s t x).
Proof. exact (fun_ext (fun x' : B => @lem4321531 A B x' a s t x)). Qed.
Lemma lem4321533 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321534 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term791 A B a s t x) = (term783 A B a s t x).
Proof. exact (MK_COMB (@lem4321533 B) (@lem4321532 A B a s t x)). Qed.
Lemma lem4321535 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (eq_refl (term697 A B a s t x)). Qed.
Lemma lem4321536 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term787 A B a s t x) = (term784 A B a s t x).
Proof. exact (MK_COMB (@lem4321535 A B a s t x) (@lem4321534 A B a s t x)). Qed.
Lemma lem4321537 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321538 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term792 A B a s t x) = (term793 A B a s t x).
Proof. exact (MK_COMB (@lem4321537) (@lem4321536 A B a s t x)). Qed.
Lemma lem4321539 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term789 A B a s t x' x) = (term781 A B x a s t x').
Proof. exact (eq_refl (term789 A B a s t x' x)). Qed.
Lemma lem4321540 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (eq_refl (term697 A B a s t x)). Qed.
Lemma lem4321541 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term794 A B a s t x' x) = (term795 A B x a s t x').
Proof. exact (MK_COMB (@lem4321540 A B a s t x') (@lem4321539 A B x a s t x')). Qed.
Lemma lem4321542 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term796 A B a s t x) = (term797 A B a s t x).
Proof. exact (fun_ext (fun x' : B => @lem4321541 A B x' a s t x)). Qed.
Lemma lem4321543 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321544 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term788 A B a s t x) = (term798 A B a s t x).
Proof. exact (MK_COMB (@lem4321543 B) (@lem4321542 A B a s t x)). Qed.
Lemma lem4321545 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : ((term787 A B a s t x) = (term788 A B a s t x)) = ((term784 A B a s t x) = (term798 A B a s t x)).
Proof. exact (MK_COMB (@lem4321538 A B a s t x) (@lem4321544 A B a s t x)). Qed.
Lemma lem4321546 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term784 A B a s t x) = (term798 A B a s t x).
Proof. exact (EQ_MP (@lem4321545 A B a s t x) (@lem4321530 A B a s t x)). Qed.
Lemma lem4321548 {A : Type'} (P : Prop) (Q : A -> Prop) : (term785 A P Q) = (term786 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4321549 {A : Type'} (P : Prop) (Q : A -> Prop) : (term785 A P Q) = (term786 A P Q).
Proof. exact (@lem4321548 A P Q). Qed.
Lemma lem4321550 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term799 A B x a s t x') = (term800 A B x a s t x').
Proof. exact (@lem4321549 A (term662 A B a s t x') (term780 A B x a s t x')). Qed.
Lemma lem4321551 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term801 A B x a s t x' x'') = (term779 A B x a s t x' x'').
Proof. exact (eq_refl (term801 A B x a s t x' x'')). Qed.
Lemma lem4321552 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term802 A B x a s t x') = (term780 A B x a s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4321551 A B x a s t x' x'')). Qed.
Lemma lem4321553 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321554 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term803 A B x a s t x') = (term781 A B x a s t x').
Proof. exact (MK_COMB (@lem4321553 A) (@lem4321552 A B x a s t x')). Qed.
Lemma lem4321555 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (eq_refl (term697 A B a s t x)). Qed.
Lemma lem4321556 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term799 A B x a s t x') = (term795 A B x a s t x').
Proof. exact (MK_COMB (@lem4321555 A B a s t x') (@lem4321554 A B x a s t x')). Qed.
Lemma lem4321557 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321558 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term804 A B x a s t x') = (term805 A B x a s t x').
Proof. exact (MK_COMB (@lem4321557) (@lem4321556 A B x a s t x')). Qed.
Lemma lem4321559 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term801 A B x a s t x' x'') = (term779 A B x a s t x' x'').
Proof. exact (eq_refl (term801 A B x a s t x' x'')). Qed.
Lemma lem4321560 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (eq_refl (term697 A B a s t x)). Qed.
Lemma lem4321561 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term806 A B x a s t x' x'') = (term807 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321560 A B a s t x') (@lem4321559 A B x a s t x' x'')). Qed.
Lemma lem4321562 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term808 A B x a s t x') = (term809 A B x a s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4321561 A B x a s t x' x'')). Qed.
Lemma lem4321563 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321564 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term800 A B x a s t x') = (term810 A B x a s t x').
Proof. exact (MK_COMB (@lem4321563 A) (@lem4321562 A B x a s t x')). Qed.
Lemma lem4321565 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term799 A B x a s t x') = (term800 A B x a s t x')) = ((term795 A B x a s t x') = (term810 A B x a s t x')).
Proof. exact (MK_COMB (@lem4321558 A B x a s t x') (@lem4321564 A B x a s t x')). Qed.
Lemma lem4321566 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term795 A B x a s t x') = (term810 A B x a s t x').
Proof. exact (EQ_MP (@lem4321565 A B x a s t x') (@lem4321550 A B x a s t x')). Qed.
Lemma lem4321568 {A : Type'} (P : Prop) (Q : A -> Prop) : (term785 A P Q) = (term786 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4321569 {B : Type'} (P : Prop) (Q : B -> Prop) : (term785 B P Q) = (term786 B P Q).
Proof. exact (@lem4321568 B P Q). Qed.
Lemma lem4321570 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term811 A B x a s t x' x'') = (term812 A B x a s t x' x'').
Proof. exact (@lem4321569 B (term662 A B a s t x') (term778 A B x a s t x' x'')). Qed.
Lemma lem4321571 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y : B) : (term813 A B x a s t x' x'' y) = (term776 A B x a s t x' x'' y).
Proof. exact (eq_refl (term813 A B x a s t x' x'' y)). Qed.
Lemma lem4321572 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term814 A B x a s t x' x'') = (term778 A B x a s t x' x'').
Proof. exact (fun_ext (fun y : B => @lem4321571 A B x a s t x' x'' y)). Qed.
Lemma lem4321573 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321574 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term815 A B x a s t x' x'') = (term779 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321573 B) (@lem4321572 A B x a s t x' x'')). Qed.
Lemma lem4321575 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (eq_refl (term697 A B a s t x)). Qed.
Lemma lem4321576 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term811 A B x a s t x' x'') = (term807 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321575 A B a s t x') (@lem4321574 A B x a s t x' x'')). Qed.
Lemma lem4321577 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321578 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term816 A B x a s t x' x'') = (term817 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321577) (@lem4321576 A B x a s t x' x'')). Qed.
Lemma lem4321579 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y : B) : (term813 A B x a s t x' x'' y) = (term776 A B x a s t x' x'' y).
Proof. exact (eq_refl (term813 A B x a s t x' x'' y)). Qed.
Lemma lem4321580 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (eq_refl (term697 A B a s t x)). Qed.
Lemma lem4321581 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y : B) : (term818 A B x a s t x' x'' y) = (term819 A B x a s t x' x'' y).
Proof. exact (MK_COMB (@lem4321580 A B a s t x') (@lem4321579 A B x a s t x' x'' y)). Qed.
Lemma lem4321582 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term820 A B x a s t x' x'') = (term821 A B x a s t x' x'').
Proof. exact (fun_ext (fun y : B => @lem4321581 A B x a s t x' x'' y)). Qed.
Lemma lem4321583 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321584 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term812 A B x a s t x' x'') = (term822 A B x a s t x' x'').
Proof. exact (MK_COMB (@lem4321583 B) (@lem4321582 A B x a s t x' x'')). Qed.
Lemma lem4321585 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : ((term811 A B x a s t x' x'') = (term812 A B x a s t x' x'')) = ((term807 A B x a s t x' x'') = (term822 A B x a s t x' x'')).
Proof. exact (MK_COMB (@lem4321578 A B x a s t x' x'') (@lem4321584 A B x a s t x' x'')). Qed.
Lemma lem4321586 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term807 A B x a s t x' x'') = (term822 A B x a s t x' x'').
Proof. exact (EQ_MP (@lem4321585 A B x a s t x' x'') (@lem4321570 A B x a s t x' x'')). Qed.
Lemma lem4321587 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term809 A B x a s t x') = (term823 A B x a s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4321586 A B x a s t x' x'')). Qed.
Lemma lem4321588 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321589 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term810 A B x a s t x') = (term824 A B x a s t x').
Proof. exact (MK_COMB (@lem4321588 A) (@lem4321587 A B x a s t x')). Qed.
Lemma lem4321590 {A B : Type'} (x : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term795 A B x a s t x') = (term824 A B x a s t x').
Proof. exact (TRANS (@lem4321566 A B x a s t x') (@lem4321589 A B x a s t x')). Qed.
Lemma lem4321591 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term797 A B a s t x) = (term825 A B a s t x).
Proof. exact (fun_ext (fun x' : B => @lem4321590 A B x' a s t x)). Qed.
Lemma lem4321592 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321593 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term798 A B a s t x) = (term826 A B a s t x).
Proof. exact (MK_COMB (@lem4321592 B) (@lem4321591 A B a s t x)). Qed.
Lemma lem4321594 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term784 A B a s t x) = (term826 A B a s t x).
Proof. exact (TRANS (@lem4321546 A B a s t x) (@lem4321593 A B a s t x)). Qed.
Lemma lem4321595 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term699 A B a s t x) = (term826 A B a s t x).
Proof. exact (TRANS (@lem4321526 A B a s t x) (@lem4321594 A B a s t x)). Qed.
Lemma lem4321596 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term706 A B a s t x) = (term827 A B a s t x).
Proof. exact (MK_COMB (@lem4321450 A B a s t x) (@lem4321595 A B a s t x)). Qed.
Lemma lem4321600 {A : Type'} (P : A -> Prop) (Q : Prop) : (term740 A P Q) = (term741 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem4321601 {A : Type'} (P : A -> Prop) (Q : Prop) : (term740 A P Q) = (term741 A P Q).
Proof. exact (@lem4321600 A P Q). Qed.
Lemma lem4321602 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term828 A B a s t x) = (term829 A B a s t x).
Proof. exact (@lem4321601 A (term737 A B a s t x) (term826 A B a s t x)). Qed.
Lemma lem4321603 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term830 A B a s t x' x) = (term736 A B x a s t x').
Proof. exact (eq_refl (term830 A B a s t x' x)). Qed.
Lemma lem4321604 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term831 A B a s t x) = (term737 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321603 A B x' a s t x)). Qed.
Lemma lem4321605 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321606 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term832 A B a s t x) = (term738 A B a s t x).
Proof. exact (MK_COMB (@lem4321605 A) (@lem4321604 A B a s t x)). Qed.
Lemma lem4321607 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321608 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term833 A B a s t x) = (term739 A B a s t x).
Proof. exact (MK_COMB (@lem4321607) (@lem4321606 A B a s t x)). Qed.
Lemma lem4321609 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term826 A B a s t x) = (term826 A B a s t x).
Proof. exact (eq_refl (term826 A B a s t x)). Qed.
Lemma lem4321610 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term828 A B a s t x) = (term827 A B a s t x).
Proof. exact (MK_COMB (@lem4321608 A B a s t x) (@lem4321609 A B a s t x)). Qed.
Lemma lem4321611 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321612 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term834 A B a s t x) = (term835 A B a s t x).
Proof. exact (MK_COMB (@lem4321611) (@lem4321610 A B a s t x)). Qed.
Lemma lem4321613 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term830 A B a s t x' x) = (term736 A B x a s t x').
Proof. exact (eq_refl (term830 A B a s t x' x)). Qed.
Lemma lem4321614 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321615 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term836 A B a s t x' x) = (term837 A B x a s t x').
Proof. exact (MK_COMB (@lem4321614) (@lem4321613 A B x a s t x')). Qed.
Lemma lem4321616 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term826 A B a s t x) = (term826 A B a s t x).
Proof. exact (eq_refl (term826 A B a s t x)). Qed.
Lemma lem4321617 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term838 A B x a s t x') = (term839 A B x a s t x').
Proof. exact (MK_COMB (@lem4321615 A B x a s t x') (@lem4321616 A B a s t x')). Qed.
Lemma lem4321618 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term840 A B a s t x) = (term841 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321617 A B x' a s t x)). Qed.
Lemma lem4321619 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321620 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term829 A B a s t x) = (term842 A B a s t x).
Proof. exact (MK_COMB (@lem4321619 A) (@lem4321618 A B a s t x)). Qed.
Lemma lem4321621 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : ((term828 A B a s t x) = (term829 A B a s t x)) = ((term827 A B a s t x) = (term842 A B a s t x)).
Proof. exact (MK_COMB (@lem4321612 A B a s t x) (@lem4321620 A B a s t x)). Qed.
Lemma lem4321622 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term827 A B a s t x) = (term842 A B a s t x).
Proof. exact (EQ_MP (@lem4321621 A B a s t x) (@lem4321602 A B a s t x)). Qed.
Lemma lem4321624 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term843 A P Q) = (term844 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4321625 {B : Type'} (P : B -> Prop) (Q : B -> Prop) : (term843 B P Q) = (term844 B P Q).
Proof. exact (@lem4321624 B P Q). Qed.
Lemma lem4321626 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term845 A B x a s t x') = (term846 A B x a s t x').
Proof. exact (@lem4321625 B (term735 A B x a s t x') (term825 A B a s t x')). Qed.
Lemma lem4321627 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term847 A B x a s t x' y) = (term733 A B x y a s t x').
Proof. exact (eq_refl (term847 A B x a s t x' y)). Qed.
Lemma lem4321628 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term848 A B x a s t x') = (term735 A B x a s t x').
Proof. exact (fun_ext (fun y : B => @lem4321627 A B x y a s t x')). Qed.
Lemma lem4321629 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321630 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term849 A B x a s t x') = (term736 A B x a s t x').
Proof. exact (MK_COMB (@lem4321629 B) (@lem4321628 A B x a s t x')). Qed.
Lemma lem4321631 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321632 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term850 A B x a s t x') = (term837 A B x a s t x').
Proof. exact (MK_COMB (@lem4321631) (@lem4321630 A B x a s t x')). Qed.
Lemma lem4321633 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term851 A B a s t x y) = (term824 A B y a s t x).
Proof. exact (eq_refl (term851 A B a s t x y)). Qed.
Lemma lem4321634 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term852 A B a s t x) = (term825 A B a s t x).
Proof. exact (fun_ext (fun y : B => @lem4321633 A B y a s t x)). Qed.
Lemma lem4321635 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321636 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term853 A B a s t x) = (term826 A B a s t x).
Proof. exact (MK_COMB (@lem4321635 B) (@lem4321634 A B a s t x)). Qed.
Lemma lem4321637 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term845 A B x a s t x') = (term839 A B x a s t x').
Proof. exact (MK_COMB (@lem4321632 A B x a s t x') (@lem4321636 A B a s t x')). Qed.
Lemma lem4321638 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321639 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term854 A B x a s t x') = (term855 A B x a s t x').
Proof. exact (MK_COMB (@lem4321638) (@lem4321637 A B x a s t x')). Qed.
Lemma lem4321640 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term847 A B x a s t x' y) = (term733 A B x y a s t x').
Proof. exact (eq_refl (term847 A B x a s t x' y)). Qed.
Lemma lem4321641 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321642 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term856 A B x a s t x' y) = (term857 A B x y a s t x').
Proof. exact (MK_COMB (@lem4321641) (@lem4321640 A B x y a s t x')). Qed.
Lemma lem4321643 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term851 A B a s t x y) = (term824 A B y a s t x).
Proof. exact (eq_refl (term851 A B a s t x y)). Qed.
Lemma lem4321644 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term858 A B x a s t x' y) = (term859 A B x y a s t x').
Proof. exact (MK_COMB (@lem4321642 A B x y a s t x') (@lem4321643 A B y a s t x')). Qed.
Lemma lem4321645 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term860 A B x a s t x') = (term861 A B x a s t x').
Proof. exact (fun_ext (fun y : B => @lem4321644 A B x y a s t x')). Qed.
Lemma lem4321646 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321647 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term846 A B x a s t x') = (term862 A B x a s t x').
Proof. exact (MK_COMB (@lem4321646 B) (@lem4321645 A B x a s t x')). Qed.
Lemma lem4321648 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term845 A B x a s t x') = (term846 A B x a s t x')) = ((term839 A B x a s t x') = (term862 A B x a s t x')).
Proof. exact (MK_COMB (@lem4321639 A B x a s t x') (@lem4321647 A B x a s t x')). Qed.
Lemma lem4321649 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term839 A B x a s t x') = (term862 A B x a s t x').
Proof. exact (EQ_MP (@lem4321648 A B x a s t x') (@lem4321626 A B x a s t x')). Qed.
Lemma lem4321652 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term863 A B x a s t x') = (term863 A B x a s t x').
Proof. exact (eq_refl (term863 A B x a s t x')). Qed.
Lemma lem4321653 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term863 A B x a s t x') = ((term839 A B x a s t x') = (term862 A B x a s t x')).
Proof. exact (eq_refl (term863 A B x a s t x')). Qed.
Lemma lem4321654 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term864 A B x a s t x') = (term864 A B x a s t x').
Proof. exact (eq_refl (term864 A B x a s t x')). Qed.
Lemma lem4321655 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term863 A B x a s t x') = (term863 A B x a s t x')) = ((term863 A B x a s t x') = ((term839 A B x a s t x') = (term862 A B x a s t x'))).
Proof. exact (MK_COMB (@lem4321654 A B x a s t x') (@lem4321653 A B x a s t x')). Qed.
Lemma lem4321656 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term863 A B x a s t x') = ((term839 A B x a s t x') = (term862 A B x a s t x')).
Proof. exact (eq_refl (term863 A B x a s t x')). Qed.
Lemma lem4321657 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321658 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term864 A B x a s t x') = (term865 A B x a s t x').
Proof. exact (MK_COMB (@lem4321657) (@lem4321656 A B x a s t x')). Qed.
Lemma lem4321659 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term839 A B x a s t x') = (term862 A B x a s t x')) = ((term839 A B x a s t x') = (term862 A B x a s t x')).
Proof. exact (eq_refl ((term839 A B x a s t x') = (term862 A B x a s t x'))). Qed.
Lemma lem4321660 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term863 A B x a s t x') = ((term839 A B x a s t x') = (term862 A B x a s t x'))) = (((term839 A B x a s t x') = (term862 A B x a s t x')) = ((term839 A B x a s t x') = (term862 A B x a s t x'))).
Proof. exact (MK_COMB (@lem4321658 A B x a s t x') (@lem4321659 A B x a s t x')). Qed.
Lemma lem4321661 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term863 A B x a s t x') = (term863 A B x a s t x')) = (((term839 A B x a s t x') = (term862 A B x a s t x')) = ((term839 A B x a s t x') = (term862 A B x a s t x'))).
Proof. exact (TRANS (@lem4321655 A B x a s t x') (@lem4321660 A B x a s t x')). Qed.
Lemma lem4321662 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term839 A B x a s t x') = (term862 A B x a s t x')) = ((term839 A B x a s t x') = (term862 A B x a s t x')).
Proof. exact (EQ_MP (@lem4321661 A B x a s t x') (@lem4321652 A B x a s t x')). Qed.
Lemma lem4321663 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term839 A B x a s t x') = (term862 A B x a s t x').
Proof. exact (EQ_MP (@lem4321662 A B x a s t x') (@lem4321649 A B x a s t x')). Qed.
Lemma lem4321665 {A : Type'} (P : Prop) (Q : A -> Prop) : (term756 A P Q) = (term757 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4321666 {A : Type'} (P : Prop) (Q : A -> Prop) : (term756 A P Q) = (term757 A P Q).
Proof. exact (@lem4321665 A P Q). Qed.
Lemma lem4321667 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term866 A B x y a s t x') = (term867 A B x y a s t x').
Proof. exact (@lem4321666 A (term733 A B x y a s t x') (term823 A B y a s t x')). Qed.
Lemma lem4321668 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term868 A B y a s t x x') = (term822 A B y a s t x x').
Proof. exact (eq_refl (term868 A B y a s t x x')). Qed.
Lemma lem4321669 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term869 A B y a s t x) = (term823 A B y a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321668 A B y a s t x x')). Qed.
Lemma lem4321670 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321671 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term870 A B y a s t x) = (term824 A B y a s t x).
Proof. exact (MK_COMB (@lem4321670 A) (@lem4321669 A B y a s t x)). Qed.
Lemma lem4321672 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term857 A B x y a s t x') = (term857 A B x y a s t x').
Proof. exact (eq_refl (term857 A B x y a s t x')). Qed.
Lemma lem4321673 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term866 A B x y a s t x') = (term859 A B x y a s t x').
Proof. exact (MK_COMB (@lem4321672 A B x y a s t x') (@lem4321671 A B y a s t x')). Qed.
Lemma lem4321674 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321675 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term871 A B x y a s t x') = (term872 A B x y a s t x').
Proof. exact (MK_COMB (@lem4321674) (@lem4321673 A B x y a s t x')). Qed.
Lemma lem4321676 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term868 A B y a s t x x') = (term822 A B y a s t x x').
Proof. exact (eq_refl (term868 A B y a s t x x')). Qed.
Lemma lem4321677 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term857 A B x y a s t x') = (term857 A B x y a s t x').
Proof. exact (eq_refl (term857 A B x y a s t x')). Qed.
Lemma lem4321678 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term873 A B x y a s t x' x'') = (term874 A B x y a s t x' x'').
Proof. exact (MK_COMB (@lem4321677 A B x y a s t x') (@lem4321676 A B y a s t x' x'')). Qed.
Lemma lem4321679 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term875 A B x y a s t x') = (term876 A B x y a s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4321678 A B x y a s t x' x'')). Qed.
Lemma lem4321680 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321681 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term867 A B x y a s t x') = (term877 A B x y a s t x').
Proof. exact (MK_COMB (@lem4321680 A) (@lem4321679 A B x y a s t x')). Qed.
Lemma lem4321682 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : ((term866 A B x y a s t x') = (term867 A B x y a s t x')) = ((term859 A B x y a s t x') = (term877 A B x y a s t x')).
Proof. exact (MK_COMB (@lem4321675 A B x y a s t x') (@lem4321681 A B x y a s t x')). Qed.
Lemma lem4321683 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term859 A B x y a s t x') = (term877 A B x y a s t x').
Proof. exact (EQ_MP (@lem4321682 A B x y a s t x') (@lem4321667 A B x y a s t x')). Qed.
Lemma lem4321685 {A : Type'} (P : Prop) (Q : A -> Prop) : (term756 A P Q) = (term757 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem4321686 {B : Type'} (P : Prop) (Q : B -> Prop) : (term756 B P Q) = (term757 B P Q).
Proof. exact (@lem4321685 B P Q). Qed.
Lemma lem4321687 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term878 A B x y a s t x' x'') = (term879 A B x y a s t x' x'').
Proof. exact (@lem4321686 B (term733 A B x y a s t x') (term821 A B y a s t x' x'')). Qed.
Lemma lem4321688 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y' : B) : (term880 A B y a s t x x' y') = (term819 A B y a s t x x' y').
Proof. exact (eq_refl (term880 A B y a s t x x' y')). Qed.
Lemma lem4321689 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term881 A B y a s t x x') = (term821 A B y a s t x x').
Proof. exact (fun_ext (fun y' : B => @lem4321688 A B y a s t x x' y')). Qed.
Lemma lem4321690 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321691 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term882 A B y a s t x x') = (term822 A B y a s t x x').
Proof. exact (MK_COMB (@lem4321690 B) (@lem4321689 A B y a s t x x')). Qed.
Lemma lem4321692 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term857 A B x y a s t x') = (term857 A B x y a s t x').
Proof. exact (eq_refl (term857 A B x y a s t x')). Qed.
Lemma lem4321693 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term878 A B x y a s t x' x'') = (term874 A B x y a s t x' x'').
Proof. exact (MK_COMB (@lem4321692 A B x y a s t x') (@lem4321691 A B y a s t x' x'')). Qed.
Lemma lem4321694 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4321695 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term883 A B x y a s t x' x'') = (term884 A B x y a s t x' x'').
Proof. exact (MK_COMB (@lem4321694) (@lem4321693 A B x y a s t x' x'')). Qed.
Lemma lem4321696 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y' : B) : (term880 A B y a s t x x' y') = (term819 A B y a s t x x' y').
Proof. exact (eq_refl (term880 A B y a s t x x' y')). Qed.
Lemma lem4321697 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term857 A B x y a s t x') = (term857 A B x y a s t x').
Proof. exact (eq_refl (term857 A B x y a s t x')). Qed.
Lemma lem4321698 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) (y' : B) : (term885 A B x y a s t x' x'' y') = (term886 A B x y a s t x' x'' y').
Proof. exact (MK_COMB (@lem4321697 A B x y a s t x') (@lem4321696 A B y a s t x' x'' y')). Qed.
Lemma lem4321699 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term887 A B x y a s t x' x'') = (term888 A B x y a s t x' x'').
Proof. exact (fun_ext (fun y' : B => @lem4321698 A B x y a s t x' x'' y')). Qed.
Lemma lem4321700 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321701 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term879 A B x y a s t x' x'') = (term889 A B x y a s t x' x'').
Proof. exact (MK_COMB (@lem4321700 B) (@lem4321699 A B x y a s t x' x'')). Qed.
Lemma lem4321702 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : ((term878 A B x y a s t x' x'') = (term879 A B x y a s t x' x'')) = ((term874 A B x y a s t x' x'') = (term889 A B x y a s t x' x'')).
Proof. exact (MK_COMB (@lem4321695 A B x y a s t x' x'') (@lem4321701 A B x y a s t x' x'')). Qed.
Lemma lem4321703 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) (x'' : A) : (term874 A B x y a s t x' x'') = (term889 A B x y a s t x' x'').
Proof. exact (EQ_MP (@lem4321702 A B x y a s t x' x'') (@lem4321687 A B x y a s t x' x'')). Qed.
Lemma lem4321704 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term876 A B x y a s t x') = (term890 A B x y a s t x').
Proof. exact (fun_ext (fun x'' : A => @lem4321703 A B x y a s t x' x'')). Qed.
Lemma lem4321705 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321706 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term877 A B x y a s t x') = (term891 A B x y a s t x').
Proof. exact (MK_COMB (@lem4321705 A) (@lem4321704 A B x y a s t x')). Qed.
Lemma lem4321707 {A B : Type'} (x : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term859 A B x y a s t x') = (term891 A B x y a s t x').
Proof. exact (TRANS (@lem4321683 A B x y a s t x') (@lem4321706 A B x y a s t x')). Qed.
Lemma lem4321708 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term861 A B x a s t x') = (term892 A B x a s t x').
Proof. exact (fun_ext (fun y : B => @lem4321707 A B x y a s t x')). Qed.
Lemma lem4321709 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4321710 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term862 A B x a s t x') = (term893 A B x a s t x').
Proof. exact (MK_COMB (@lem4321709 B) (@lem4321708 A B x a s t x')). Qed.
Lemma lem4321711 {A B : Type'} (x : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x' : prod A B) : (term839 A B x a s t x') = (term893 A B x a s t x').
Proof. exact (TRANS (@lem4321663 A B x a s t x') (@lem4321710 A B x a s t x')). Qed.
Lemma lem4321712 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term841 A B a s t x) = (term894 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321711 A B x' a s t x)). Qed.
Lemma lem4321713 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4321714 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term842 A B a s t x) = (term895 A B a s t x).
Proof. exact (MK_COMB (@lem4321713 A) (@lem4321712 A B a s t x)). Qed.
Lemma lem4321715 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term827 A B a s t x) = (term895 A B a s t x).
Proof. exact (TRANS (@lem4321622 A B a s t x) (@lem4321714 A B a s t x)). Qed.
Lemma lem4321717 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term706 A B a s t x) = (term895 A B a s t x).
Proof. exact (TRANS (@lem4321596 A B a s t x) (@lem4321715 A B a s t x)). Qed.
Lemma lem4321718 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term635 A B a s t x) = (term895 A B a s t x).
Proof. exact (TRANS (@lem4321091 A B a s t x) (@lem4321717 A B a s t x)). Qed.
Lemma lem4321719 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term635 A B a s t x) : term895 A B a s t x.
Proof. exact (EQ_MP (@lem4321718 A B a s t x) (@lem4320941 A B a s t x h1)). Qed.
Lemma lem4321720 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term893 A B x' a s t x) : term893 A B x' a s t x.
Proof. exact (h1). Qed.
Lemma lem4321721 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term891 A B x' y a s t x) : term891 A B x' y a s t x.
Proof. exact (h1). Qed.
Lemma lem4321722 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (h1 : term889 A B x' y a s t x x'') : term889 A B x' y a s t x x''.
Proof. exact (h1). Qed.
Lemma lem4321723 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term886 A B x' y a s t x x'' y') : term886 A B x' y a s t x x'' y'.
Proof. exact (h1). Qed.
Lemma lem4321772 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) : (term776 A B y a s t x x'' y') = (term776 A B y a s t x x'' y').
Proof. exact (eq_refl (term776 A B y a s t x x'' y')). Qed.
Lemma lem4321815 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term647 A B a s t x x' y) = (term647 A B a s t x x' y).
Proof. exact (eq_refl (term647 A B a s t x x' y)). Qed.
Lemma lem4321816 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term654 A B a s t x x') = (term654 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4321815 A B a s t x x' y)). Qed.
Lemma lem4321817 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4321818 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term655 A B a s t x x') = (term655 A B a s t x x').
Proof. exact (MK_COMB (@lem4321817 B) (@lem4321816 A B a s t x x')). Qed.
Lemma lem4321819 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term661 A B a s t x) = (term661 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321818 A B a s t x x')). Qed.
Lemma lem4321820 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4321821 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term662 A B a s t x) = (term662 A B a s t x).
Proof. exact (MK_COMB (@lem4321820 A) (@lem4321819 A B a s t x)). Qed.
Lemma lem4321822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321823 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term697 A B a s t x) = (term697 A B a s t x).
Proof. exact (MK_COMB (@lem4321822) (@lem4321821 A B a s t x)). Qed.
Lemma lem4321824 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) : (term819 A B y a s t x x'' y') = (term819 A B y a s t x x'' y').
Proof. exact (MK_COMB (@lem4321823 A B a s t x) (@lem4321772 A B y a s t x x'' y')). Qed.
Lemma lem4321857 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term675 A B s t x x' y) = (term675 A B s t x x' y).
Proof. exact (eq_refl (term675 A B s t x x' y)). Qed.
Lemma lem4321858 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term682 A B s t x x') = (term682 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4321857 A B s t x x' y)). Qed.
Lemma lem4321859 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4321860 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term683 A B s t x x') = (term683 A B s t x x').
Proof. exact (MK_COMB (@lem4321859 B) (@lem4321858 A B s t x x')). Qed.
Lemma lem4321861 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term689 A B s t x) = (term689 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4321860 A B s t x x')). Qed.
Lemma lem4321862 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4321863 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term690 A B s t x) = (term690 A B s t x).
Proof. exact (MK_COMB (@lem4321862 A) (@lem4321861 A B s t x)). Qed.
Lemma lem4321886 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term664 A B x x' t a) = (term664 A B x x' t a).
Proof. exact (eq_refl (term664 A B x x' t a)). Qed.
Lemma lem4321887 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term670 A B x t a) = (term670 A B x t a).
Proof. exact (fun_ext (fun x' : B => @lem4321886 A B x x' t a)). Qed.
Lemma lem4321888 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4321889 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term671 A B x t a) = (term671 A B x t a).
Proof. exact (MK_COMB (@lem4321888 B) (@lem4321887 A B x t a)). Qed.
Lemma lem4321890 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4321891 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term692 A B x t a) = (term692 A B x t a).
Proof. exact (MK_COMB (@lem4321890) (@lem4321889 A B x t a)). Qed.
Lemma lem4321892 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term694 A B a s t x) = (term694 A B a s t x).
Proof. exact (MK_COMB (@lem4321891 A B x t a) (@lem4321863 A B s t x)). Qed.
Lemma lem4321929 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term731 A B a s t x x' y) = (term731 A B a s t x x' y).
Proof. exact (eq_refl (term731 A B a s t x x' y)). Qed.
Lemma lem4321930 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term733 A B x' y a s t x) = (term733 A B x' y a s t x).
Proof. exact (MK_COMB (@lem4321929 A B a s t x x' y) (@lem4321892 A B a s t x)). Qed.
Lemma lem4321931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4321932 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term857 A B x' y a s t x) = (term857 A B x' y a s t x).
Proof. exact (MK_COMB (@lem4321931) (@lem4321930 A B x' y a s t x)). Qed.
Lemma lem4321933 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) : (term886 A B x' y a s t x x'' y') = (term886 A B x' y a s t x x'' y').
Proof. exact (MK_COMB (@lem4321932 A B x' y a s t x) (@lem4321824 A B y a s t x x'' y')). Qed.
Lemma lem4321934 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term886 A B x' y a s t x x'' y') : term886 A B x' y a s t x x'' y'.
Proof. exact (EQ_MP (@lem4321933 A B x' y a s t x x'' y') (@lem4321723 A B x' y a s t x x'' y' h1)). Qed.
Lemma lem4321935 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term733 A B x' y a s t x.
Proof. exact (h1). Qed.
Lemma lem4321936 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term819 A B y a s t x x'' y'.
Proof. exact (h1). Qed.
Lemma lem4321937 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term694 A B a s t x.
Proof. exact (proj2 (@lem4321935 A B x' y a s t x h1)). Qed.
Lemma lem4321938 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term549 A B a s t x x' y.
Proof. exact (proj1 (@lem4321935 A B x' y a s t x h1)). Qed.
Lemma lem4321939 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term690 A B s t x.
Proof. exact (proj2 (@lem4321937 A B x' y a s t x h1)). Qed.
Lemma lem4321940 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term671 A B x t a.
Proof. exact (proj1 (@lem4321937 A B x' y a s t x h1)). Qed.
Lemma lem4321942 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term536 A B a s y t x'.
Proof. exact (proj1 (@lem4321938 A B x' y a s t x h1)). Qed.
Lemma lem4321944 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term20 A a x' s.
Proof. exact (proj1 (@lem4321942 A B x' y a s t x h1)). Qed.
Lemma lem4321947 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term776 A B y a s t x x'' y'.
Proof. exact (proj2 (@lem4321936 A B y a s t x x'' y' h1)). Qed.
Lemma lem4321948 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term662 A B a s t x.
Proof. exact (proj1 (@lem4321936 A B y a s t x x'' y' h1)). Qed.
Lemma lem4321949 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : term575 A B x y t a.
Proof. exact (h1). Qed.
Lemma lem4321950 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term604 A B s t x x'' y'.
Proof. exact (h1). Qed.
Lemma lem4321954 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term182 A B s y' t x''.
Proof. exact (proj1 (@lem4321950 A B s t x x'' y' h1)). Qed.
Lemma lem4321964 {A B : Type'} (x : prod A B) (x' : B) (t : type1413 A B) (a : A) : (term664 A B x x' t a) = (term664 A B x x' t a).
Proof. exact (eq_refl (term664 A B x x' t a)). Qed.
Lemma lem4321965 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term670 A B x t a) = (term670 A B x t a).
Proof. exact (fun_ext (fun x' : B => @lem4321964 A B x x' t a)). Qed.
Lemma lem4321966 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4321968 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) : (term671 A B x t a) = (term671 A B x t a).
Proof. exact (MK_COMB (@lem4321966 B) (@lem4321965 A B x t a)). Qed.
Lemma lem4321969 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term671 A B x t a.
Proof. exact (EQ_MP (@lem4321968 A B x t a) (@lem4321940 A B x' y a s t x h1)). Qed.
Lemma lem4322003 {A : Type'} (x' : A) (a : A) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem4322030 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term675 A B s t x x' y) = (term675 A B s t x x' y).
Proof. exact (eq_refl (term675 A B s t x x' y)). Qed.
Lemma lem4322031 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term682 A B s t x x') = (term682 A B s t x x').
Proof. exact (fun_ext (fun y : B => @lem4322030 A B s t x x' y)). Qed.
Lemma lem4322032 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4322033 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term683 A B s t x x') = (term683 A B s t x x').
Proof. exact (MK_COMB (@lem4322032 B) (@lem4322031 A B s t x x')). Qed.
Lemma lem4322034 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term689 A B s t x) = (term689 A B s t x).
Proof. exact (fun_ext (fun x' : A => @lem4322033 A B s t x x')). Qed.
Lemma lem4322035 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4322037 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term690 A B s t x) = (term690 A B s t x).
Proof. exact (MK_COMB (@lem4322035 A) (@lem4322034 A B s t x)). Qed.
Lemma lem4322038 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term690 A B s t x.
Proof. exact (EQ_MP (@lem4322037 A B s t x) (@lem4321939 A B x' y a s t x h1)). Qed.
Lemma lem4322050 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem4322052 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term643 A B x x' y) = (term643 A B x x' y).
Proof. exact (eq_refl (term643 A B x x' y)). Qed.
Lemma lem4322069 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term641 A B a s y t x) = (term896 A B a s y t x).
Proof. exact (@lem19699 (term897 A x a) (term314 A x s) (term316 A B y t x)). Qed.
Lemma lem4322070 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4322071 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term645 A B a s y t x) = (term898 A B a s y t x).
Proof. exact (MK_COMB (@lem4322070) (@lem4322069 A B a s y t x)). Qed.
Lemma lem4322072 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term647 A B a s t x x' y) = (term899 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4322071 A B a s y t x') (@lem4322052 A B x x' y)). Qed.
Lemma lem4322079 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term899 A B a s t x x' y) = (term900 A B a s t x x' y).
Proof. exact (@lem19699 (term901 A B a y t x') (term287 A B s y t x') (term643 A B x x' y)). Qed.
Lemma lem4322080 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term647 A B a s t x x' y) = (term900 A B a s t x x' y).
Proof. exact (TRANS (@lem4322072 A B a s t x x' y) (@lem4322079 A B a s t x x' y)). Qed.
Lemma lem4322081 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term654 A B a s t x x') = (term902 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4322080 A B a s t x x' y)). Qed.
Lemma lem4322082 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4322083 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term655 A B a s t x x') = (term903 A B a s t x x').
Proof. exact (MK_COMB (@lem4322082 B) (@lem4322081 A B a s t x x')). Qed.
Lemma lem4322084 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term661 A B a s t x) = (term904 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4322083 A B a s t x x')). Qed.
Lemma lem4322085 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4322087 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term662 A B a s t x) = (term905 A B a s t x).
Proof. exact (MK_COMB (@lem4322085 A) (@lem4322084 A B a s t x)). Qed.
Lemma lem4322088 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term905 A B a s t x.
Proof. exact (EQ_MP (@lem4322087 A B a s t x) (@lem4321948 A B y a s t x x'' y' h1)). Qed.
Lemma lem4322098 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term643 A B x x' y) = (term643 A B x x' y).
Proof. exact (eq_refl (term643 A B x x' y)). Qed.
Lemma lem4322115 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term641 A B a s y t x) = (term896 A B a s y t x).
Proof. exact (@lem19699 (term897 A x a) (term314 A x s) (term316 A B y t x)). Qed.
Lemma lem4322116 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4322117 {A B : Type'} (a : A) (s : A -> Prop) (y : B) (t : type1413 A B) (x : A) : (term645 A B a s y t x) = (term898 A B a s y t x).
Proof. exact (MK_COMB (@lem4322116) (@lem4322115 A B a s y t x)). Qed.
Lemma lem4322118 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term647 A B a s t x x' y) = (term899 A B a s t x x' y).
Proof. exact (MK_COMB (@lem4322117 A B a s y t x') (@lem4322098 A B x x' y)). Qed.
Lemma lem4322125 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term899 A B a s t x x' y) = (term900 A B a s t x x' y).
Proof. exact (@lem19699 (term901 A B a y t x') (term287 A B s y t x') (term643 A B x x' y)). Qed.
Lemma lem4322126 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (y : B) : (term647 A B a s t x x' y) = (term900 A B a s t x x' y).
Proof. exact (TRANS (@lem4322118 A B a s t x x' y) (@lem4322125 A B a s t x x' y)). Qed.
Lemma lem4322127 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term654 A B a s t x x') = (term902 A B a s t x x').
Proof. exact (fun_ext (fun y : B => @lem4322126 A B a s t x x' y)). Qed.
Lemma lem4322128 {B : Type'} : (@all B) = (@all B).
Proof. exact (eq_refl (@all B)). Qed.
Lemma lem4322129 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) : (term655 A B a s t x x') = (term903 A B a s t x x').
Proof. exact (MK_COMB (@lem4322128 B) (@lem4322127 A B a s t x x')). Qed.
Lemma lem4322130 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term661 A B a s t x) = (term904 A B a s t x).
Proof. exact (fun_ext (fun x' : A => @lem4322129 A B a s t x x')). Qed.
Lemma lem4322131 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4322133 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term662 A B a s t x) = (term905 A B a s t x).
Proof. exact (MK_COMB (@lem4322131 A) (@lem4322130 A B a s t x)). Qed.
Lemma lem4322134 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term905 A B a s t x.
Proof. exact (EQ_MP (@lem4322133 A B a s t x) (@lem4321948 A B y a s t x x'' y' h1)). Qed.
Lemma lem4322147 {A B : Type'} (_49162 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term906 A B x t a _49162.
Proof. exact (@lem4321969 A B x' y a s t x h1 _49162). Qed.
Lemma lem4322148 {A B : Type'} (x : prod A B) (_49162 : B) (t : type1413 A B) (a : A) : (term906 A B x t a _49162) = (term664 A B x _49162 t a).
Proof. exact (eq_refl (term906 A B x t a _49162)). Qed.
Lemma lem4322159 {A B : Type'} (_49166 : A) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term907 A B s t x _49166.
Proof. exact (@lem4322038 A B x' y a s t x h1 _49166). Qed.
Lemma lem4322160 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49166 : A) : (term907 A B s t x _49166) = (term683 A B s t x _49166).
Proof. exact (eq_refl (term907 A B s t x _49166)). Qed.
Lemma lem4322161 {A B : Type'} (_49166 : A) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term683 A B s t x _49166.
Proof. exact (EQ_MP (@lem4322160 A B s t x _49166) (@lem4322159 A B _49166 x' y a s t x h1)). Qed.
Lemma lem4322162 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term908 A B s t x _49166 _49167.
Proof. exact (@lem4322161 A B _49166 x' y a s t x h1 _49167). Qed.
Lemma lem4322163 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49166 : A) (_49167 : B) : (term908 A B s t x _49166 _49167) = (term675 A B s t x _49166 _49167).
Proof. exact (eq_refl (term908 A B s t x _49166 _49167)). Qed.
Lemma lem4322164 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term675 A B s t x _49166 _49167.
Proof. exact (EQ_MP (@lem4322163 A B s t x _49166 _49167) (@lem4322162 A B _49166 _49167 x' y a s t x h1)). Qed.
Lemma lem4322165 {A B : Type'} (_49168 : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term909 A B a s t x _49168.
Proof. exact (@lem4322088 A B y a s t x x'' y' h1 _49168). Qed.
Lemma lem4322166 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49168 : A) : (term909 A B a s t x _49168) = (term903 A B a s t x _49168).
Proof. exact (eq_refl (term909 A B a s t x _49168)). Qed.
Lemma lem4322167 {A B : Type'} (_49168 : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term903 A B a s t x _49168.
Proof. exact (EQ_MP (@lem4322166 A B a s t x _49168) (@lem4322165 A B _49168 y a s t x x'' y' h1)). Qed.
Lemma lem4322168 {A B : Type'} (_49168 : A) (_49169 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term910 A B a s t x _49168 _49169.
Proof. exact (@lem4322167 A B _49168 y a s t x x'' y' h1 _49169). Qed.
Lemma lem4322169 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49168 : A) (_49169 : B) : (term910 A B a s t x _49168 _49169) = (term900 A B a s t x _49168 _49169).
Proof. exact (eq_refl (term910 A B a s t x _49168 _49169)). Qed.
Lemma lem4322170 {A B : Type'} (_49168 : A) (_49169 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term900 A B a s t x _49168 _49169.
Proof. exact (EQ_MP (@lem4322169 A B a s t x _49168 _49169) (@lem4322168 A B _49168 _49169 y a s t x x'' y' h1)). Qed.
Lemma lem4322171 {A B : Type'} (_49170 : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term909 A B a s t x _49170.
Proof. exact (@lem4322134 A B y a s t x x'' y' h1 _49170). Qed.
Lemma lem4322172 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49170 : A) : (term909 A B a s t x _49170) = (term903 A B a s t x _49170).
Proof. exact (eq_refl (term909 A B a s t x _49170)). Qed.
Lemma lem4322173 {A B : Type'} (_49170 : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term903 A B a s t x _49170.
Proof. exact (EQ_MP (@lem4322172 A B a s t x _49170) (@lem4322171 A B _49170 y a s t x x'' y' h1)). Qed.
Lemma lem4322174 {A B : Type'} (_49170 : A) (_49171 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term910 A B a s t x _49170 _49171.
Proof. exact (@lem4322173 A B _49170 y a s t x x'' y' h1 _49171). Qed.
Lemma lem4322175 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49170 : A) (_49171 : B) : (term910 A B a s t x _49170 _49171) = (term900 A B a s t x _49170 _49171).
Proof. exact (eq_refl (term910 A B a s t x _49170 _49171)). Qed.
Lemma lem4322176 {A B : Type'} (_49170 : A) (_49171 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term900 A B a s t x _49170 _49171.
Proof. exact (EQ_MP (@lem4322175 A B a s t x _49170 _49171) (@lem4322174 A B _49170 _49171 y a s t x x'' y' h1)). Qed.
Lemma lem4322178 {A B : Type'} (_49168 : A) (_49169 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term911 A B a t x _49168 _49169.
Proof. exact (proj1 (@lem4322170 A B _49168 _49169 y a s t x x'' y' h1)). Qed.
Lemma lem4322179 {A B : Type'} (_49170 : A) (_49171 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term675 A B s t x _49170 _49171.
Proof. exact (proj2 (@lem4322176 A B _49170 _49171 y a s t x x'' y' h1)). Qed.
Lemma lem4322200 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : x = (@pair A B x' y).
Proof. exact (proj2 (@lem4321938 A B x' y a s t x h1)). Qed.
Lemma lem4322202 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term288 A B y t x'.
Proof. exact (proj2 (@lem4321942 A B x' y a s t x h1)). Qed.
Lemma lem4322204 {A : Type'} (x' : A) (a : A) (h1 : x' = a) : x' = a.
Proof. exact (h1). Qed.
Lemma lem4322221 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49166 : A) (_49167 : B) : (term675 A B s t x _49166 _49167) = (term912 A B s t x _49166 _49167).
Proof. exact (@lem4318358 (term314 A _49166 s) (term316 A B _49167 t _49166) (term643 A B x _49166 _49167)). Qed.
Lemma lem4322222 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term912 A B s t x _49166 _49167.
Proof. exact (EQ_MP (@lem4322221 A B s t x _49166 _49167) (@lem4322164 A B _49166 _49167 x' y a s t x h1)). Qed.
Lemma lem4322224 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : x = (@pair A B x' y).
Proof. exact (proj2 (@lem4321938 A B x' y a s t x h1)). Qed.
Lemma lem4322228 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem4322230 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : x = (@pair A B a y).
Proof. exact (proj1 (@lem4321949 A B x y t a h1)). Qed.
Lemma lem4322243 {A B : Type'} (a : A) (t : type1413 A B) (x : prod A B) (_49168 : A) (_49169 : B) : (term911 A B a t x _49168 _49169) = (term913 A B a t x _49168 _49169).
Proof. exact (@lem4318358 (term897 A _49168 a) (term316 A B _49169 t _49168) (term643 A B x _49168 _49169)). Qed.
Lemma lem4322244 {A B : Type'} (_49168 : A) (_49169 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term913 A B a t x _49168 _49169.
Proof. exact (EQ_MP (@lem4322243 A B a t x _49168 _49169) (@lem4322178 A B _49168 _49169 y a s t x x'' y' h1)). Qed.
Lemma lem4322258 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : x = (@pair A B x'' y').
Proof. exact (proj2 (@lem4321950 A B s t x x'' y' h1)). Qed.
Lemma lem4322285 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49170 : A) (_49171 : B) : (term675 A B s t x _49170 _49171) = (term912 A B s t x _49170 _49171).
Proof. exact (@lem4318358 (term314 A _49170 s) (term316 A B _49171 t _49170) (term643 A B x _49170 _49171)). Qed.
Lemma lem4322286 {A B : Type'} (_49170 : A) (_49171 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : term912 A B s t x _49170 _49171.
Proof. exact (EQ_MP (@lem4322285 A B s t x _49170 _49171) (@lem4322179 A B _49170 _49171 y a s t x x'' y' h1)). Qed.
Lemma lem4322314 {A B : Type'} (_49162 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term664 A B x _49162 t a.
Proof. exact (EQ_MP (@lem4322148 A B x _49162 t a) (@lem4322147 A B _49162 x' y a s t x h1)). Qed.
Lemma lem4322329 {A B : Type'} (x : prod A B) (y : B) : (term914 A B x y) = (term914 A B x y).
Proof. exact (eq_refl (term914 A B x y)). Qed.
Lemma lem4322330 {A B : Type'} (x : prod A B) (y : B) (x' : A) (a : A) (h1 : x' = a) : (term915 A B x y x') = (term915 A B x y a).
Proof. exact (MK_COMB (@lem4322329 A B x y) (@lem4322204 A x' a h1)). Qed.
Lemma lem4322331 {A B : Type'} (x : prod A B) (a : A) (y : B) : (term915 A B x y a) = (x = (@pair A B a y)).
Proof. exact (eq_refl (term915 A B x y a)). Qed.
Lemma lem4322332 {A B : Type'} (x : prod A B) (y : B) (x' : A) : (term916 A B x y x') = (term916 A B x y x').
Proof. exact (eq_refl (term916 A B x y x')). Qed.
Lemma lem4322333 {A B : Type'} (x' : A) (x : prod A B) (a : A) (y : B) : ((term915 A B x y x') = (term915 A B x y a)) = ((term915 A B x y x') = (x = (@pair A B a y))).
Proof. exact (MK_COMB (@lem4322332 A B x y x') (@lem4322331 A B x a y)). Qed.
Lemma lem4322334 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term915 A B x y x') = (x = (@pair A B x' y)).
Proof. exact (eq_refl (term915 A B x y x')). Qed.
Lemma lem4322335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4322336 {A B : Type'} (x : prod A B) (x' : A) (y : B) : (term916 A B x y x') = (term917 A B x x' y).
Proof. exact (MK_COMB (@lem4322335) (@lem4322334 A B x x' y)). Qed.
Lemma lem4322337 {A B : Type'} (x : prod A B) (a : A) (y : B) : (x = (@pair A B a y)) = (x = (@pair A B a y)).
Proof. exact (eq_refl (x = (@pair A B a y))). Qed.
Lemma lem4322338 {A B : Type'} (x' : A) (x : prod A B) (a : A) (y : B) : ((term915 A B x y x') = (x = (@pair A B a y))) = ((x = (@pair A B x' y)) = (x = (@pair A B a y))).
Proof. exact (MK_COMB (@lem4322336 A B x x' y) (@lem4322337 A B x a y)). Qed.
Lemma lem4322339 {A B : Type'} (x' : A) (x : prod A B) (a : A) (y : B) : ((term915 A B x y x') = (term915 A B x y a)) = ((x = (@pair A B x' y)) = (x = (@pair A B a y))).
Proof. exact (TRANS (@lem4322333 A B x' x a y) (@lem4322338 A B x' x a y)). Qed.
Lemma lem4322340 {A B : Type'} (x : prod A B) (y : B) (x' : A) (a : A) (h1 : x' = a) : (x = (@pair A B x' y)) = (x = (@pair A B a y)).
Proof. exact (EQ_MP (@lem4322339 A B x' x a y) (@lem4322330 A B x y x' a h1)). Qed.
Lemma lem4322341 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : x = (@pair A B a y).
Proof. exact (EQ_MP (@lem4322340 A B x y x' a h2) (@lem4322200 A B x' y a s t x h1)). Qed.
Lemma lem4322342 {A B : Type'} (y : B) (t : type1413 A B) : (term918 A B y t) = (term918 A B y t).
Proof. exact (eq_refl (term918 A B y t)). Qed.
Lemma lem4322343 {A B : Type'} (y : B) (t : type1413 A B) (x' : A) (a : A) (h1 : x' = a) : (term919 A B y t x') = (term919 A B y t a).
Proof. exact (MK_COMB (@lem4322342 A B y t) (@lem4322204 A x' a h1)). Qed.
Lemma lem4322344 {A B : Type'} (y : B) (t : type1413 A B) (a : A) : (term919 A B y t a) = (term288 A B y t a).
Proof. exact (eq_refl (term919 A B y t a)). Qed.
Lemma lem4322345 {A B : Type'} (y : B) (t : type1413 A B) (x' : A) : (term920 A B y t x') = (term920 A B y t x').
Proof. exact (eq_refl (term920 A B y t x')). Qed.
Lemma lem4322346 {A B : Type'} (x' : A) (y : B) (t : type1413 A B) (a : A) : ((term919 A B y t x') = (term919 A B y t a)) = ((term919 A B y t x') = (term288 A B y t a)).
Proof. exact (MK_COMB (@lem4322345 A B y t x') (@lem4322344 A B y t a)). Qed.
Lemma lem4322347 {A B : Type'} (y : B) (t : type1413 A B) (x' : A) : (term919 A B y t x') = (term288 A B y t x').
Proof. exact (eq_refl (term919 A B y t x')). Qed.
Lemma lem4322348 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4322349 {A B : Type'} (y : B) (t : type1413 A B) (x' : A) : (term920 A B y t x') = (term921 A B y t x').
Proof. exact (MK_COMB (@lem4322348) (@lem4322347 A B y t x')). Qed.
Lemma lem4322350 {A B : Type'} (y : B) (t : type1413 A B) (a : A) : (term288 A B y t a) = (term288 A B y t a).
Proof. exact (eq_refl (term288 A B y t a)). Qed.
Lemma lem4322351 {A B : Type'} (x' : A) (y : B) (t : type1413 A B) (a : A) : ((term919 A B y t x') = (term288 A B y t a)) = ((term288 A B y t x') = (term288 A B y t a)).
Proof. exact (MK_COMB (@lem4322349 A B y t x') (@lem4322350 A B y t a)). Qed.
Lemma lem4322352 {A B : Type'} (x' : A) (y : B) (t : type1413 A B) (a : A) : ((term919 A B y t x') = (term919 A B y t a)) = ((term288 A B y t x') = (term288 A B y t a)).
Proof. exact (TRANS (@lem4322346 A B x' y t a) (@lem4322351 A B x' y t a)). Qed.
Lemma lem4322353 {A B : Type'} (y : B) (t : type1413 A B) (x' : A) (a : A) (h1 : x' = a) : (term288 A B y t x') = (term288 A B y t a).
Proof. exact (EQ_MP (@lem4322352 A B x' y t a) (@lem4322343 A B y t x' a h1)). Qed.
Lemma lem4322369 {A B : Type'} (_49162 : B) (t : type1413 A B) (a : A) : (term922 A B _49162 t a) = (term922 A B _49162 t a).
Proof. exact (eq_refl (term922 A B _49162 t a)). Qed.
Lemma lem4322370 {A B : Type'} (_49162 : B) (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : (term923 A B _49162 t a x) = (term924 A B _49162 t a y).
Proof. exact (MK_COMB (@lem4322369 A B _49162 t a) (@lem4322341 A B y s t x x' a h1 h2)). Qed.
Lemma lem4322371 {A B : Type'} (y : B) (_49162 : B) (t : type1413 A B) (a : A) : (term924 A B _49162 t a y) = (term925 A B y _49162 t a).
Proof. exact (eq_refl (term924 A B _49162 t a y)). Qed.
Lemma lem4322372 {A B : Type'} (_49162 : B) (t : type1413 A B) (a : A) (x : prod A B) : (term926 A B _49162 t a x) = (term926 A B _49162 t a x).
Proof. exact (eq_refl (term926 A B _49162 t a x)). Qed.
Lemma lem4322373 {A B : Type'} (x : prod A B) (y : B) (_49162 : B) (t : type1413 A B) (a : A) : ((term923 A B _49162 t a x) = (term924 A B _49162 t a y)) = ((term923 A B _49162 t a x) = (term925 A B y _49162 t a)).
Proof. exact (MK_COMB (@lem4322372 A B _49162 t a x) (@lem4322371 A B y _49162 t a)). Qed.
Lemma lem4322374 {A B : Type'} (x : prod A B) (_49162 : B) (t : type1413 A B) (a : A) : (term923 A B _49162 t a x) = (term664 A B x _49162 t a).
Proof. exact (eq_refl (term923 A B _49162 t a x)). Qed.
Lemma lem4322375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4322376 {A B : Type'} (x : prod A B) (_49162 : B) (t : type1413 A B) (a : A) : (term926 A B _49162 t a x) = (term927 A B x _49162 t a).
Proof. exact (MK_COMB (@lem4322375) (@lem4322374 A B x _49162 t a)). Qed.
Lemma lem4322377 {A B : Type'} (y : B) (_49162 : B) (t : type1413 A B) (a : A) : (term925 A B y _49162 t a) = (term925 A B y _49162 t a).
Proof. exact (eq_refl (term925 A B y _49162 t a)). Qed.
Lemma lem4322378 {A B : Type'} (x : prod A B) (y : B) (_49162 : B) (t : type1413 A B) (a : A) : ((term923 A B _49162 t a x) = (term925 A B y _49162 t a)) = ((term664 A B x _49162 t a) = (term925 A B y _49162 t a)).
Proof. exact (MK_COMB (@lem4322376 A B x _49162 t a) (@lem4322377 A B y _49162 t a)). Qed.
Lemma lem4322379 {A B : Type'} (x : prod A B) (y : B) (_49162 : B) (t : type1413 A B) (a : A) : ((term923 A B _49162 t a x) = (term924 A B _49162 t a y)) = ((term664 A B x _49162 t a) = (term925 A B y _49162 t a)).
Proof. exact (TRANS (@lem4322373 A B x y _49162 t a) (@lem4322378 A B x y _49162 t a)). Qed.
Lemma lem4322380 {A B : Type'} (_49162 : B) (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : (term664 A B x _49162 t a) = (term925 A B y _49162 t a).
Proof. exact (EQ_MP (@lem4322379 A B x y _49162 t a) (@lem4322370 A B _49162 y s t x x' a h1 h2)). Qed.
Lemma lem4322381 {A B : Type'} (_49162 : B) (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term925 A B y _49162 t a.
Proof. exact (EQ_MP (@lem4322380 A B _49162 y s t x x' a h1 h2) (@lem4322314 A B _49162 x' y a s t x h1)). Qed.
Lemma lem4322436 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_49166 : A) (_49167 : B) : (term928 A B s t _49166 _49167) = (term928 A B s t _49166 _49167).
Proof. exact (eq_refl (term928 A B s t _49166 _49167)). Qed.
Lemma lem4322437 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : (term929 A B s t _49166 _49167 x) = (term930 A B s t _49166 _49167 x' y).
Proof. exact (MK_COMB (@lem4322436 A B s t _49166 _49167) (@lem4322224 A B x' y a s t x h1)). Qed.
Lemma lem4322438 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term930 A B s t _49166 _49167 x' y) = (term931 A B s t x' y _49166 _49167).
Proof. exact (eq_refl (term930 A B s t _49166 _49167 x' y)). Qed.
Lemma lem4322439 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_49166 : A) (_49167 : B) (x : prod A B) : (term932 A B s t _49166 _49167 x) = (term932 A B s t _49166 _49167 x).
Proof. exact (eq_refl (term932 A B s t _49166 _49167 x)). Qed.
Lemma lem4322440 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : ((term929 A B s t _49166 _49167 x) = (term930 A B s t _49166 _49167 x' y)) = ((term929 A B s t _49166 _49167 x) = (term931 A B s t x' y _49166 _49167)).
Proof. exact (MK_COMB (@lem4322439 A B s t _49166 _49167 x) (@lem4322438 A B s t x' y _49166 _49167)). Qed.
Lemma lem4322441 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49166 : A) (_49167 : B) : (term929 A B s t _49166 _49167 x) = (term912 A B s t x _49166 _49167).
Proof. exact (eq_refl (term929 A B s t _49166 _49167 x)). Qed.
Lemma lem4322442 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4322443 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49166 : A) (_49167 : B) : (term932 A B s t _49166 _49167 x) = (term933 A B s t x _49166 _49167).
Proof. exact (MK_COMB (@lem4322442) (@lem4322441 A B s t x _49166 _49167)). Qed.
Lemma lem4322444 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term931 A B s t x' y _49166 _49167) = (term931 A B s t x' y _49166 _49167).
Proof. exact (eq_refl (term931 A B s t x' y _49166 _49167)). Qed.
Lemma lem4322445 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : ((term929 A B s t _49166 _49167 x) = (term931 A B s t x' y _49166 _49167)) = ((term912 A B s t x _49166 _49167) = (term931 A B s t x' y _49166 _49167)).
Proof. exact (MK_COMB (@lem4322443 A B s t x _49166 _49167) (@lem4322444 A B s t x' y _49166 _49167)). Qed.
Lemma lem4322446 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : ((term929 A B s t _49166 _49167 x) = (term930 A B s t _49166 _49167 x' y)) = ((term912 A B s t x _49166 _49167) = (term931 A B s t x' y _49166 _49167)).
Proof. exact (TRANS (@lem4322440 A B x s t x' y _49166 _49167) (@lem4322445 A B x s t x' y _49166 _49167)). Qed.
Lemma lem4322447 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : (term912 A B s t x _49166 _49167) = (term931 A B s t x' y _49166 _49167).
Proof. exact (EQ_MP (@lem4322446 A B x s t x' y _49166 _49167) (@lem4322437 A B _49166 _49167 x' y a s t x h1)). Qed.
Lemma lem4322448 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term931 A B s t x' y _49166 _49167.
Proof. exact (EQ_MP (@lem4322447 A B _49166 _49167 x' y a s t x h1) (@lem4322222 A B _49166 _49167 x' y a s t x h1)). Qed.
Lemma lem4322476 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem4322505 {A B : Type'} (a : A) (t : type1413 A B) (_49168 : A) (_49169 : B) : (term934 A B a t _49168 _49169) = (term934 A B a t _49168 _49169).
Proof. exact (eq_refl (term934 A B a t _49168 _49169)). Qed.
Lemma lem4322506 {A B : Type'} (_49168 : A) (_49169 : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : (term935 A B a t _49168 _49169 x) = (term936 A B t _49168 _49169 a y).
Proof. exact (MK_COMB (@lem4322505 A B a t _49168 _49169) (@lem4322230 A B x y t a h1)). Qed.
Lemma lem4322507 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term936 A B t _49168 _49169 a y) = (term937 A B t a y _49168 _49169).
Proof. exact (eq_refl (term936 A B t _49168 _49169 a y)). Qed.
Lemma lem4322508 {A B : Type'} (a : A) (t : type1413 A B) (_49168 : A) (_49169 : B) (x : prod A B) : (term938 A B a t _49168 _49169 x) = (term938 A B a t _49168 _49169 x).
Proof. exact (eq_refl (term938 A B a t _49168 _49169 x)). Qed.
Lemma lem4322509 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : ((term935 A B a t _49168 _49169 x) = (term936 A B t _49168 _49169 a y)) = ((term935 A B a t _49168 _49169 x) = (term937 A B t a y _49168 _49169)).
Proof. exact (MK_COMB (@lem4322508 A B a t _49168 _49169 x) (@lem4322507 A B t a y _49168 _49169)). Qed.
Lemma lem4322510 {A B : Type'} (a : A) (t : type1413 A B) (x : prod A B) (_49168 : A) (_49169 : B) : (term935 A B a t _49168 _49169 x) = (term913 A B a t x _49168 _49169).
Proof. exact (eq_refl (term935 A B a t _49168 _49169 x)). Qed.
Lemma lem4322511 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4322512 {A B : Type'} (a : A) (t : type1413 A B) (x : prod A B) (_49168 : A) (_49169 : B) : (term938 A B a t _49168 _49169 x) = (term939 A B a t x _49168 _49169).
Proof. exact (MK_COMB (@lem4322511) (@lem4322510 A B a t x _49168 _49169)). Qed.
Lemma lem4322513 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term937 A B t a y _49168 _49169) = (term937 A B t a y _49168 _49169).
Proof. exact (eq_refl (term937 A B t a y _49168 _49169)). Qed.
Lemma lem4322514 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : ((term935 A B a t _49168 _49169 x) = (term937 A B t a y _49168 _49169)) = ((term913 A B a t x _49168 _49169) = (term937 A B t a y _49168 _49169)).
Proof. exact (MK_COMB (@lem4322512 A B a t x _49168 _49169) (@lem4322513 A B t a y _49168 _49169)). Qed.
Lemma lem4322515 {A B : Type'} (x : prod A B) (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : ((term935 A B a t _49168 _49169 x) = (term936 A B t _49168 _49169 a y)) = ((term913 A B a t x _49168 _49169) = (term937 A B t a y _49168 _49169)).
Proof. exact (TRANS (@lem4322509 A B x t a y _49168 _49169) (@lem4322514 A B x t a y _49168 _49169)). Qed.
Lemma lem4322516 {A B : Type'} (_49168 : A) (_49169 : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : (term913 A B a t x _49168 _49169) = (term937 A B t a y _49168 _49169).
Proof. exact (EQ_MP (@lem4322515 A B x t a y _49168 _49169) (@lem4322506 A B _49168 _49169 x y t a h1)). Qed.
Lemma lem4322517 {A B : Type'} (_49168 : A) (_49169 : B) (s : A -> Prop) (x'' : A) (y' : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term819 A B y a s t x x'' y') (h2 : term575 A B x y t a) : term937 A B t a y _49168 _49169.
Proof. exact (EQ_MP (@lem4322516 A B _49168 _49169 x y t a h2) (@lem4322244 A B _49168 _49169 y a s t x x'' y' h1)). Qed.
Lemma lem4322586 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_49170 : A) (_49171 : B) : (term928 A B s t _49170 _49171) = (term928 A B s t _49170 _49171).
Proof. exact (eq_refl (term928 A B s t _49170 _49171)). Qed.
Lemma lem4322587 {A B : Type'} (_49170 : A) (_49171 : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : (term929 A B s t _49170 _49171 x) = (term930 A B s t _49170 _49171 x'' y').
Proof. exact (MK_COMB (@lem4322586 A B s t _49170 _49171) (@lem4322258 A B s t x x'' y' h1)). Qed.
Lemma lem4322588 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term930 A B s t _49170 _49171 x'' y') = (term931 A B s t x'' y' _49170 _49171).
Proof. exact (eq_refl (term930 A B s t _49170 _49171 x'' y')). Qed.
Lemma lem4322589 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (_49170 : A) (_49171 : B) (x : prod A B) : (term932 A B s t _49170 _49171 x) = (term932 A B s t _49170 _49171 x).
Proof. exact (eq_refl (term932 A B s t _49170 _49171 x)). Qed.
Lemma lem4322590 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : ((term929 A B s t _49170 _49171 x) = (term930 A B s t _49170 _49171 x'' y')) = ((term929 A B s t _49170 _49171 x) = (term931 A B s t x'' y' _49170 _49171)).
Proof. exact (MK_COMB (@lem4322589 A B s t _49170 _49171 x) (@lem4322588 A B s t x'' y' _49170 _49171)). Qed.
Lemma lem4322591 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49170 : A) (_49171 : B) : (term929 A B s t _49170 _49171 x) = (term912 A B s t x _49170 _49171).
Proof. exact (eq_refl (term929 A B s t _49170 _49171 x)). Qed.
Lemma lem4322592 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4322593 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (_49170 : A) (_49171 : B) : (term932 A B s t _49170 _49171 x) = (term933 A B s t x _49170 _49171).
Proof. exact (MK_COMB (@lem4322592) (@lem4322591 A B s t x _49170 _49171)). Qed.
Lemma lem4322594 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term931 A B s t x'' y' _49170 _49171) = (term931 A B s t x'' y' _49170 _49171).
Proof. exact (eq_refl (term931 A B s t x'' y' _49170 _49171)). Qed.
Lemma lem4322595 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : ((term929 A B s t _49170 _49171 x) = (term931 A B s t x'' y' _49170 _49171)) = ((term912 A B s t x _49170 _49171) = (term931 A B s t x'' y' _49170 _49171)).
Proof. exact (MK_COMB (@lem4322593 A B s t x _49170 _49171) (@lem4322594 A B s t x'' y' _49170 _49171)). Qed.
Lemma lem4322596 {A B : Type'} (x : prod A B) (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : ((term929 A B s t _49170 _49171 x) = (term930 A B s t _49170 _49171 x'' y')) = ((term912 A B s t x _49170 _49171) = (term931 A B s t x'' y' _49170 _49171)).
Proof. exact (TRANS (@lem4322590 A B x s t x'' y' _49170 _49171) (@lem4322595 A B x s t x'' y' _49170 _49171)). Qed.
Lemma lem4322597 {A B : Type'} (_49170 : A) (_49171 : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : (term912 A B s t x _49170 _49171) = (term931 A B s t x'' y' _49170 _49171).
Proof. exact (EQ_MP (@lem4322596 A B x s t x'' y' _49170 _49171) (@lem4322587 A B _49170 _49171 s t x x'' y' h1)). Qed.
Lemma lem4322598 {A B : Type'} (_49170 : A) (_49171 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') (h2 : term604 A B s t x x'' y') : term931 A B s t x'' y' _49170 _49171.
Proof. exact (EQ_MP (@lem4322597 A B _49170 _49171 s t x x'' y' h2) (@lem4322286 A B _49170 _49171 y a s t x x'' y' h1)). Qed.
Lemma lem4322671 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem21386 (prod A B) x). Qed.
Lemma lem4322672 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem4322671 A B x). Qed.
Lemma lem4322673 {A B : Type'} (a : A) (y : B) : (@pair A B a y) = (@pair A B a y).
Proof. exact (@lem4322672 A B (@pair A B a y)). Qed.
Lemma lem4322674 {A B : Type'} (a : A) (y : B) : term940 A B a y.
Proof. exact (fun h0 : term941 A B a y => @lem4322673 A B a y). Qed.
Lemma lem4322676 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322677 {A B : Type'} (a : A) (y : B) : (term940 A B a y) = ((@pair A B a y) = (@pair A B a y)).
Proof. exact (@lem4322676 ((@pair A B a y) = (@pair A B a y))). Qed.
Lemma lem4322678 {A B : Type'} (a : A) (y : B) : (@pair A B a y) = (@pair A B a y).
Proof. exact (EQ_MP (@lem4322677 A B a y) (@lem4322674 A B a y)). Qed.
Lemma lem4322680 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term288 A B y t a.
Proof. exact (EQ_MP (@lem4322353 A B y t x' a h2) (@lem4322202 A B x' y a s t x h1)). Qed.
Lemma lem4322681 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term315 A B y t a.
Proof. exact (fun h0 : term316 A B y t a => @lem4322680 A B y s t x x' a h1 h2). Qed.
Lemma lem4322683 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322684 {A B : Type'} (y : B) (t : type1413 A B) (a : A) : (term315 A B y t a) = (term288 A B y t a).
Proof. exact (@lem4322683 (term288 A B y t a)). Qed.
Lemma lem4322685 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term288 A B y t a.
Proof. exact (EQ_MP (@lem4322684 A B y t a) (@lem4322681 A B y s t x x' a h1 h2)). Qed.
Lemma lem4322687 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4322688 {A B : Type'} (y : B) (_49162 : B) (t : type1413 A B) (a : A) : (term925 A B y _49162 t a) = (term942 A B y _49162 t a).
Proof. exact (@lem4322687 ((@pair A B a y) = (@pair A B a _49162)) (term288 A B _49162 t a)). Qed.
Lemma lem4322690 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4322691 {A B : Type'} (y : B) (_49162 : B) (t : type1413 A B) (a : A) : (term942 A B y _49162 t a) = (term943 A B y _49162 t a).
Proof. exact (@lem4322690 (term944 A B y _49162 t a)). Qed.
Lemma lem4322692 {A B : Type'} (y : B) (_49162 : B) (t : type1413 A B) (a : A) : (term925 A B y _49162 t a) = (term943 A B y _49162 t a).
Proof. exact (TRANS (@lem4322688 A B y _49162 t a) (@lem4322691 A B y _49162 t a)). Qed.
Lemma lem4322694 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term945 A B y t a.
Proof. exact (conj (@lem4322678 A B a y) (@lem4322685 A B y s t x x' a h1 h2)). Qed.
Lemma lem4322696 {A B : Type'} (_49162 : B) (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term943 A B y _49162 t a.
Proof. exact (EQ_MP (@lem4322692 A B y _49162 t a) (@lem4322381 A B _49162 y s t x x' a h1 h2)). Qed.
Lemma lem4322697 {A B : Type'} (_49162 : B) (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term943 A B y _49162 t a.
Proof. exact (@lem4322696 A B _49162 y s t x x' a h1 h2). Qed.
Lemma lem4322698 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term946 A B y t a.
Proof. exact (@lem4322697 A B y y s t x x' a h1 h2). Qed.
Lemma lem4322701 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : False.
Proof. exact (@lem4322698 A B y s t x x' a h1 h2 (@lem4322694 A B y s t x x' a h1 h2)). Qed.
Lemma lem4322702 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : term322.
Proof. exact (fun h0 : ~ False => @lem4322701 A B y s t x x' a h1 h2). Qed.
Lemma lem4322704 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322705 : term322 = False.
Proof. exact (@lem4322704 False). Qed.
Lemma lem4322779 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (h1). Qed.
Lemma lem4322780 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : term313 A x' s.
Proof. exact (fun h0 : term314 A x' s => @lem4322779 A x' s h1). Qed.
Lemma lem4322782 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322783 {A : Type'} (x' : A) (s : A -> Prop) : (term313 A x' s) = (@IN A x' s).
Proof. exact (@lem4322782 (@IN A x' s)). Qed.
Lemma lem4322784 {A : Type'} (x' : A) (s : A -> Prop) (h1 : @IN A x' s) : @IN A x' s.
Proof. exact (EQ_MP (@lem4322783 A x' s) (@lem4322780 A x' s h1)). Qed.
Lemma lem4322786 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term288 A B y t x'.
Proof. exact (proj2 (@lem4321942 A B x' y a s t x h1)). Qed.
Lemma lem4322787 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term315 A B y t x'.
Proof. exact (fun h0 : term316 A B y t x' => @lem4322786 A B x' y a s t x h1). Qed.
Lemma lem4322789 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322790 {A B : Type'} (y : B) (t : type1413 A B) (x' : A) : (term315 A B y t x') = (term288 A B y t x').
Proof. exact (@lem4322789 (term288 A B y t x')). Qed.
Lemma lem4322791 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term288 A B y t x'.
Proof. exact (EQ_MP (@lem4322790 A B y t x') (@lem4322787 A B x' y a s t x h1)). Qed.
Lemma lem4322793 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem21386 (prod A B) x). Qed.
Lemma lem4322794 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem4322793 A B x). Qed.
Lemma lem4322795 {A B : Type'} (x' : A) (y : B) : (@pair A B x' y) = (@pair A B x' y).
Proof. exact (@lem4322794 A B (@pair A B x' y)). Qed.
Lemma lem4322796 {A B : Type'} (x' : A) (y : B) : term940 A B x' y.
Proof. exact (fun h0 : term941 A B x' y => @lem4322795 A B x' y). Qed.
Lemma lem4322798 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322799 {A B : Type'} (x' : A) (y : B) : (term940 A B x' y) = ((@pair A B x' y) = (@pair A B x' y)).
Proof. exact (@lem4322798 ((@pair A B x' y) = (@pair A B x' y))). Qed.
Lemma lem4322800 {A B : Type'} (x' : A) (y : B) : (@pair A B x' y) = (@pair A B x' y).
Proof. exact (EQ_MP (@lem4322799 A B x' y) (@lem4322796 A B x' y)). Qed.
Lemma lem4322802 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4322803 {A B : Type'} (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term947 A B t x' y _49166 _49167) = (term948 A B t x' y _49166 _49167).
Proof. exact (@lem4322802 (term288 A B _49167 t _49166) ((@pair A B x' y) = (@pair A B _49166 _49167))). Qed.
Lemma lem4322804 {A : Type'} (_49166 : A) (s : A -> Prop) : (term949 A _49166 s) = (term949 A _49166 s).
Proof. exact (eq_refl (term949 A _49166 s)). Qed.
Lemma lem4322805 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term931 A B s t x' y _49166 _49167) = (term950 A B s t x' y _49166 _49167).
Proof. exact (MK_COMB (@lem4322804 A _49166 s) (@lem4322803 A B t x' y _49166 _49167)). Qed.
Lemma lem4322807 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4322808 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term950 A B s t x' y _49166 _49167) = (term951 A B s t x' y _49166 _49167).
Proof. exact (@lem4322807 (@IN A _49166 s) (term952 A B t x' y _49166 _49167)). Qed.
Lemma lem4322809 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term931 A B s t x' y _49166 _49167) = (term951 A B s t x' y _49166 _49167).
Proof. exact (TRANS (@lem4322805 A B s t x' y _49166 _49167) (@lem4322808 A B s t x' y _49166 _49167)). Qed.
Lemma lem4322811 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4322812 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term951 A B s t x' y _49166 _49167) = (term953 A B s t x' y _49166 _49167).
Proof. exact (@lem4322811 (term954 A B s t x' y _49166 _49167)). Qed.
Lemma lem4322813 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x' : A) (y : B) (_49166 : A) (_49167 : B) : (term931 A B s t x' y _49166 _49167) = (term953 A B s t x' y _49166 _49167).
Proof. exact (TRANS (@lem4322809 A B s t x' y _49166 _49167) (@lem4322812 A B s t x' y _49166 _49167)). Qed.
Lemma lem4322815 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term955 A B t x' y.
Proof. exact (conj (@lem4322791 A B x' y a s t x h1) (@lem4322800 A B x' y)). Qed.
Lemma lem4322816 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : term956 A B s t x' y.
Proof. exact (conj (@lem4322784 A x' s h2) (@lem4322815 A B x' y a s t x h1)). Qed.
Lemma lem4322818 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term953 A B s t x' y _49166 _49167.
Proof. exact (EQ_MP (@lem4322813 A B s t x' y _49166 _49167) (@lem4322448 A B _49166 _49167 x' y a s t x h1)). Qed.
Lemma lem4322819 {A B : Type'} (_49166 : A) (_49167 : B) (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term953 A B s t x' y _49166 _49167.
Proof. exact (@lem4322818 A B _49166 _49167 x' y a s t x h1). Qed.
Lemma lem4322820 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : term957 A B s t x' y.
Proof. exact (@lem4322819 A B x' y x' y a s t x h1). Qed.
Lemma lem4322823 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : False.
Proof. exact (@lem4322820 A B x' y a s t x h1 (@lem4322816 A B y a t x x' s h1 h2)). Qed.
Lemma lem4322824 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : term322.
Proof. exact (fun h0 : ~ False => @lem4322823 A B y a t x x' s h1 h2). Qed.
Lemma lem4322826 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322827 : term322 = False.
Proof. exact (@lem4322826 False). Qed.
Lemma lem4322828 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem4322827) (@lem4322824 A B y a t x x' s h1 h2)). Qed.
Lemma lem4322901 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem4322902 {A : Type'} (x : A) : x = x.
Proof. exact (@lem4322901 A x). Qed.
Lemma lem4322903 {A : Type'} (a : A) : a = a.
Proof. exact (@lem4322902 A a). Qed.
Lemma lem4322904 {A : Type'} (a : A) : term958 A a.
Proof. exact (fun h0 : term959 A a => @lem4322903 A a). Qed.
Lemma lem4322906 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322907 {A : Type'} (a : A) : (term958 A a) = (a = a).
Proof. exact (@lem4322906 (a = a)). Qed.
Lemma lem4322908 {A : Type'} (a : A) : a = a.
Proof. exact (EQ_MP (@lem4322907 A a) (@lem4322904 A a)). Qed.
Lemma lem4322910 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : term288 A B y t a.
Proof. exact (proj2 (@lem4321949 A B x y t a h1)). Qed.
Lemma lem4322911 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : term315 A B y t a.
Proof. exact (fun h0 : term316 A B y t a => @lem4322910 A B x y t a h1). Qed.
Lemma lem4322913 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322914 {A B : Type'} (y : B) (t : type1413 A B) (a : A) : (term315 A B y t a) = (term288 A B y t a).
Proof. exact (@lem4322913 (term288 A B y t a)). Qed.
Lemma lem4322915 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : term288 A B y t a.
Proof. exact (EQ_MP (@lem4322914 A B y t a) (@lem4322911 A B x y t a h1)). Qed.
Lemma lem4322917 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem21386 (prod A B) x). Qed.
Lemma lem4322918 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem4322917 A B x). Qed.
Lemma lem4322919 {A B : Type'} (a : A) (y : B) : (@pair A B a y) = (@pair A B a y).
Proof. exact (@lem4322918 A B (@pair A B a y)). Qed.
Lemma lem4322920 {A B : Type'} (a : A) (y : B) : term940 A B a y.
Proof. exact (fun h0 : term941 A B a y => @lem4322919 A B a y). Qed.
Lemma lem4322922 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322923 {A B : Type'} (a : A) (y : B) : (term940 A B a y) = ((@pair A B a y) = (@pair A B a y)).
Proof. exact (@lem4322922 ((@pair A B a y) = (@pair A B a y))). Qed.
Lemma lem4322924 {A B : Type'} (a : A) (y : B) : (@pair A B a y) = (@pair A B a y).
Proof. exact (EQ_MP (@lem4322923 A B a y) (@lem4322920 A B a y)). Qed.
Lemma lem4322926 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4322927 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term947 A B t a y _49168 _49169) = (term948 A B t a y _49168 _49169).
Proof. exact (@lem4322926 (term288 A B _49169 t _49168) ((@pair A B a y) = (@pair A B _49168 _49169))). Qed.
Lemma lem4322928 {A : Type'} (_49168 : A) (a : A) : (term960 A _49168 a) = (term960 A _49168 a).
Proof. exact (eq_refl (term960 A _49168 a)). Qed.
Lemma lem4322929 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term937 A B t a y _49168 _49169) = (term961 A B t a y _49168 _49169).
Proof. exact (MK_COMB (@lem4322928 A _49168 a) (@lem4322927 A B t a y _49168 _49169)). Qed.
Lemma lem4322931 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4322932 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term961 A B t a y _49168 _49169) = (term962 A B t a y _49168 _49169).
Proof. exact (@lem4322931 (_49168 = a) (term952 A B t a y _49168 _49169)). Qed.
Lemma lem4322933 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term937 A B t a y _49168 _49169) = (term962 A B t a y _49168 _49169).
Proof. exact (TRANS (@lem4322929 A B t a y _49168 _49169) (@lem4322932 A B t a y _49168 _49169)). Qed.
Lemma lem4322935 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4322936 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term962 A B t a y _49168 _49169) = (term963 A B t a y _49168 _49169).
Proof. exact (@lem4322935 (term964 A B t a y _49168 _49169)). Qed.
Lemma lem4322937 {A B : Type'} (t : type1413 A B) (a : A) (y : B) (_49168 : A) (_49169 : B) : (term937 A B t a y _49168 _49169) = (term963 A B t a y _49168 _49169).
Proof. exact (TRANS (@lem4322933 A B t a y _49168 _49169) (@lem4322936 A B t a y _49168 _49169)). Qed.
Lemma lem4322939 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : term955 A B t a y.
Proof. exact (conj (@lem4322915 A B x y t a h1) (@lem4322924 A B a y)). Qed.
Lemma lem4322940 {A B : Type'} (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term575 A B x y t a) : term965 A B t a y.
Proof. exact (conj (@lem4322908 A a) (@lem4322939 A B x y t a h1)). Qed.
Lemma lem4322942 {A B : Type'} (_49168 : A) (_49169 : B) (s : A -> Prop) (x'' : A) (y' : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term819 A B y a s t x x'' y') (h2 : term575 A B x y t a) : term963 A B t a y _49168 _49169.
Proof. exact (EQ_MP (@lem4322937 A B t a y _49168 _49169) (@lem4322517 A B _49168 _49169 s x'' y' x y t a h1 h2)). Qed.
Lemma lem4322943 {A B : Type'} (_49168 : A) (_49169 : B) (s : A -> Prop) (x'' : A) (y' : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term819 A B y a s t x x'' y') (h2 : term575 A B x y t a) : term963 A B t a y _49168 _49169.
Proof. exact (@lem4322942 A B _49168 _49169 s x'' y' x y t a h1 h2). Qed.
Lemma lem4322944 {A B : Type'} (s : A -> Prop) (x'' : A) (y' : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term819 A B y a s t x x'' y') (h2 : term575 A B x y t a) : term966 A B t a y.
Proof. exact (@lem4322943 A B a y s x'' y' x y t a h1 h2). Qed.
Lemma lem4322947 {A B : Type'} (s : A -> Prop) (x'' : A) (y' : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term819 A B y a s t x x'' y') (h2 : term575 A B x y t a) : False.
Proof. exact (@lem4322944 A B s x'' y' x y t a h1 h2 (@lem4322940 A B x y t a h2)). Qed.
Lemma lem4322948 {A B : Type'} (s : A -> Prop) (x'' : A) (y' : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term819 A B y a s t x x'' y') (h2 : term575 A B x y t a) : term322.
Proof. exact (fun h0 : ~ False => @lem4322947 A B s x'' y' x y t a h1 h2). Qed.
Lemma lem4322950 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4322951 : term322 = False.
Proof. exact (@lem4322950 False). Qed.
Lemma lem4323025 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : @IN A x'' s.
Proof. exact (proj1 (@lem4321954 A B s t x x'' y' h1)). Qed.
Lemma lem4323026 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term313 A x'' s.
Proof. exact (fun h0 : term314 A x'' s => @lem4323025 A B s t x x'' y' h1). Qed.
Lemma lem4323028 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4323029 {A : Type'} (x'' : A) (s : A -> Prop) : (term313 A x'' s) = (@IN A x'' s).
Proof. exact (@lem4323028 (@IN A x'' s)). Qed.
Lemma lem4323030 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : @IN A x'' s.
Proof. exact (EQ_MP (@lem4323029 A x'' s) (@lem4323026 A B s t x x'' y' h1)). Qed.
Lemma lem4323032 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term288 A B y' t x''.
Proof. exact (proj2 (@lem4321954 A B s t x x'' y' h1)). Qed.
Lemma lem4323033 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term315 A B y' t x''.
Proof. exact (fun h0 : term316 A B y' t x'' => @lem4323032 A B s t x x'' y' h1). Qed.
Lemma lem4323035 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4323036 {A B : Type'} (y' : B) (t : type1413 A B) (x'' : A) : (term315 A B y' t x'') = (term288 A B y' t x'').
Proof. exact (@lem4323035 (term288 A B y' t x'')). Qed.
Lemma lem4323037 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term288 A B y' t x''.
Proof. exact (EQ_MP (@lem4323036 A B y' t x'') (@lem4323033 A B s t x x'' y' h1)). Qed.
Lemma lem4323039 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem21386 (prod A B) x). Qed.
Lemma lem4323040 {A B : Type'} (x : prod A B) : x = x.
Proof. exact (@lem4323039 A B x). Qed.
Lemma lem4323041 {A B : Type'} (x'' : A) (y' : B) : (@pair A B x'' y') = (@pair A B x'' y').
Proof. exact (@lem4323040 A B (@pair A B x'' y')). Qed.
Lemma lem4323042 {A B : Type'} (x'' : A) (y' : B) : term940 A B x'' y'.
Proof. exact (fun h0 : term941 A B x'' y' => @lem4323041 A B x'' y'). Qed.
Lemma lem4323044 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4323045 {A B : Type'} (x'' : A) (y' : B) : (term940 A B x'' y') = ((@pair A B x'' y') = (@pair A B x'' y')).
Proof. exact (@lem4323044 ((@pair A B x'' y') = (@pair A B x'' y'))). Qed.
Lemma lem4323046 {A B : Type'} (x'' : A) (y' : B) : (@pair A B x'' y') = (@pair A B x'' y').
Proof. exact (EQ_MP (@lem4323045 A B x'' y') (@lem4323042 A B x'' y')). Qed.
Lemma lem4323048 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4323049 {A B : Type'} (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term947 A B t x'' y' _49170 _49171) = (term948 A B t x'' y' _49170 _49171).
Proof. exact (@lem4323048 (term288 A B _49171 t _49170) ((@pair A B x'' y') = (@pair A B _49170 _49171))). Qed.
Lemma lem4323050 {A : Type'} (_49170 : A) (s : A -> Prop) : (term949 A _49170 s) = (term949 A _49170 s).
Proof. exact (eq_refl (term949 A _49170 s)). Qed.
Lemma lem4323051 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term931 A B s t x'' y' _49170 _49171) = (term950 A B s t x'' y' _49170 _49171).
Proof. exact (MK_COMB (@lem4323050 A _49170 s) (@lem4323049 A B t x'' y' _49170 _49171)). Qed.
Lemma lem4323053 (a : Prop) (b : Prop) : (term317 a b) = (term318 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem4323054 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term950 A B s t x'' y' _49170 _49171) = (term951 A B s t x'' y' _49170 _49171).
Proof. exact (@lem4323053 (@IN A _49170 s) (term952 A B t x'' y' _49170 _49171)). Qed.
Lemma lem4323055 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term931 A B s t x'' y' _49170 _49171) = (term951 A B s t x'' y' _49170 _49171).
Proof. exact (TRANS (@lem4323051 A B s t x'' y' _49170 _49171) (@lem4323054 A B s t x'' y' _49170 _49171)). Qed.
Lemma lem4323057 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4323058 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term951 A B s t x'' y' _49170 _49171) = (term953 A B s t x'' y' _49170 _49171).
Proof. exact (@lem4323057 (term954 A B s t x'' y' _49170 _49171)). Qed.
Lemma lem4323059 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x'' : A) (y' : B) (_49170 : A) (_49171 : B) : (term931 A B s t x'' y' _49170 _49171) = (term953 A B s t x'' y' _49170 _49171).
Proof. exact (TRANS (@lem4323055 A B s t x'' y' _49170 _49171) (@lem4323058 A B s t x'' y' _49170 _49171)). Qed.
Lemma lem4323061 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term955 A B t x'' y'.
Proof. exact (conj (@lem4323037 A B s t x x'' y' h1) (@lem4323046 A B x'' y')). Qed.
Lemma lem4323062 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term604 A B s t x x'' y') : term956 A B s t x'' y'.
Proof. exact (conj (@lem4323030 A B s t x x'' y' h1) (@lem4323061 A B s t x x'' y' h1)). Qed.
Lemma lem4323064 {A B : Type'} (_49170 : A) (_49171 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') (h2 : term604 A B s t x x'' y') : term953 A B s t x'' y' _49170 _49171.
Proof. exact (EQ_MP (@lem4323059 A B s t x'' y' _49170 _49171) (@lem4322598 A B _49170 _49171 y a s t x x'' y' h1 h2)). Qed.
Lemma lem4323065 {A B : Type'} (_49170 : A) (_49171 : B) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') (h2 : term604 A B s t x x'' y') : term953 A B s t x'' y' _49170 _49171.
Proof. exact (@lem4323064 A B _49170 _49171 y a s t x x'' y' h1 h2). Qed.
Lemma lem4323066 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') (h2 : term604 A B s t x x'' y') : term957 A B s t x'' y'.
Proof. exact (@lem4323065 A B x'' y' y a s t x x'' y' h1 h2). Qed.
Lemma lem4323069 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') (h2 : term604 A B s t x x'' y') : False.
Proof. exact (@lem4323066 A B y a s t x x'' y' h1 h2 (@lem4323062 A B s t x x'' y' h2)). Qed.
Lemma lem4323070 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') (h2 : term604 A B s t x x'' y') : term322.
Proof. exact (fun h0 : ~ False => @lem4323069 A B y a s t x x'' y' h1 h2). Qed.
Lemma lem4323072 (p : Prop) : (term312 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4323073 : term322 = False.
Proof. exact (@lem4323072 False). Qed.
Lemma lem4323075 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') (h2 : term604 A B s t x x'' y') : False.
Proof. exact (EQ_MP (@lem4323073) (@lem4323070 A B y a s t x x'' y' h1 h2)). Qed.
Lemma lem4323076 {A B : Type'} (s : A -> Prop) (x'' : A) (y' : B) (x : prod A B) (y : B) (t : type1413 A B) (a : A) (h1 : term819 A B y a s t x x'' y') (h2 : term575 A B x y t a) : False.
Proof. exact (EQ_MP (@lem4322951) (@lem4322948 A B s x'' y' x y t a h1 h2)). Qed.
Lemma lem4323077 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : (@IN A x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x' s => @lem4322828 A B y a t x x' s h1 h2) (fun h3 : False => @lem4322476 A x' s h2)). Qed.
Lemma lem4323079 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem4323077 A B y a t x x' s h1 h2) (@lem4322476 A x' s h2)). Qed.
Lemma lem4323081 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4322705) (@lem4322702 A B y s t x x' a h1 h2)). Qed.
Lemma lem4323082 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : (@IN A x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x' s => @lem4323079 A B y a t x x' s h1 h2) (fun h3 : False => @lem4322228 A x' s h2)). Qed.
Lemma lem4323083 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem4323082 A B y a t x x' s h1 h2) (@lem4322228 A x' s h2)). Qed.
Lemma lem4323084 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem4323081 A B y s t x x' a h1 h2) (fun h3 : False => @lem4322204 A x' a h2)). Qed.
Lemma lem4323085 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4323084 A B y s t x x' a h1 h2) (@lem4322204 A x' a h2)). Qed.
Lemma lem4323086 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : (@IN A x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x' s => @lem4323083 A B y a t x x' s h1 h2) (fun h3 : False => @lem4322050 A x' s h2)). Qed.
Lemma lem4323087 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem4323086 A B y a t x x' s h1 h2) (@lem4322050 A x' s h2)). Qed.
Lemma lem4323088 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem4323085 A B y s t x x' a h1 h2) (fun h3 : False => @lem4322003 A x' a h2)). Qed.
Lemma lem4323089 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4323088 A B y s t x x' a h1 h2) (@lem4322003 A x' a h2)). Qed.
Lemma lem4323090 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : (@IN A x' s) = False.
Proof. exact (prop_ext (fun h3 : @IN A x' s => @lem4323087 A B y a t x x' s h1 h2) (fun h3 : False => @lem4322050 A x' s h2)). Qed.
Lemma lem4323091 {A B : Type'} (y : B) (a : A) (t : type1413 A B) (x : prod A B) (x' : A) (s : A -> Prop) (h1 : term733 A B x' y a s t x) (h2 : @IN A x' s) : False.
Proof. exact (EQ_MP (@lem4323090 A B y a t x x' s h1 h2) (@lem4322050 A x' s h2)). Qed.
Lemma lem4323092 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : (x' = a) = False.
Proof. exact (prop_ext (fun h3 : x' = a => @lem4323089 A B y s t x x' a h1 h2) (fun h3 : False => @lem4322003 A x' a h2)). Qed.
Lemma lem4323093 {A B : Type'} (y : B) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x' : A) (a : A) (h1 : term733 A B x' y a s t x) (h2 : x' = a) : False.
Proof. exact (EQ_MP (@lem4323092 A B y s t x x' a h1 h2) (@lem4322003 A x' a h2)). Qed.
Lemma lem4323094 {A B : Type'} (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term819 A B y a s t x x'' y') : False.
Proof. exact (or_elim (@lem4321947 A B y a s t x x'' y' h1) (fun h0 : term575 A B x y t a => @lem4323076 A B s x'' y' x y t a h1 h0) (fun h0 : term604 A B s t x x'' y' => @lem4323075 A B y a s t x x'' y' h1 h0)). Qed.
Lemma lem4323095 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term733 A B x' y a s t x) : False.
Proof. exact (or_elim (@lem4321944 A B x' y a s t x h1) (fun h0 : x' = a => @lem4323093 A B y s t x x' a h1 h0) (fun h0 : @IN A x' s => @lem4323091 A B y a t x x' s h1 h0)). Qed.
Lemma lem4323096 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term886 A B x' y a s t x x'' y') : False.
Proof. exact (or_elim (@lem4321934 A B x' y a s t x x'' y' h1) (fun h0 : term733 A B x' y a s t x => @lem4323095 A B x' y a s t x h0) (fun h0 : term819 A B y a s t x x'' y' => @lem4323094 A B y a s t x x'' y' h0)). Qed.
Lemma lem4323097 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term886 A B x' y a s t x x'' y') : (term886 A B x' y a s t x x'' y') = False.
Proof. exact (prop_ext (fun h2 : term886 A B x' y a s t x x'' y' => @lem4323096 A B x' y a s t x x'' y' h1) (fun h2 : False => @lem4321934 A B x' y a s t x x'' y' h1)). Qed.
Lemma lem4323098 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (y' : B) (h1 : term886 A B x' y a s t x x'' y') : False.
Proof. exact (EQ_MP (@lem4323097 A B x' y a s t x x'' y' h1) (@lem4321934 A B x' y a s t x x'' y' h1)). Qed.
Lemma lem4323099 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (x'' : A) (h1 : term889 A B x' y a s t x x'') : False.
Proof. exact (ex_elim (@lem4321722 A B x' y a s t x x'' h1) (fun y' : B => fun h0 : term888 A B x' y a s t x x'' y' => @lem4323098 A B x' y a s t x x'' y' h0)). Qed.
Lemma lem4323100 {A B : Type'} (x' : A) (y : B) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term891 A B x' y a s t x) : False.
Proof. exact (ex_elim (@lem4321721 A B x' y a s t x h1) (fun x'' : A => fun h0 : term890 A B x' y a s t x x'' => @lem4323099 A B x' y a s t x x'' h0)). Qed.
Lemma lem4323101 {A B : Type'} (x' : A) (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term893 A B x' a s t x) : False.
Proof. exact (ex_elim (@lem4321720 A B x' a s t x h1) (fun y : B => fun h0 : term892 A B x' a s t x y => @lem4323100 A B x' y a s t x h0)). Qed.
Lemma lem4323102 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term635 A B a s t x) : False.
Proof. exact (ex_elim (@lem4321719 A B a s t x h1) (fun x' : A => fun h0 : term894 A B a s t x x' => @lem4323101 A B x' a s t x h0)). Qed.
Lemma lem4323103 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term635 A B a s t x) : (term635 A B a s t x) = False.
Proof. exact (prop_ext (fun h2 : term635 A B a s t x => @lem4323102 A B a s t x h1) (fun h2 : False => @lem4320941 A B a s t x h1)). Qed.
Lemma lem4323104 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) (h1 : term635 A B a s t x) : False.
Proof. exact (EQ_MP (@lem4323103 A B a s t x h1) (@lem4320941 A B a s t x h1)). Qed.
Lemma lem4323105 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : term634 A B a s t x.
Proof. exact (fun h0 : term635 A B a s t x => @lem4323104 A B a s t x h0). Qed.
Lemma lem4323106 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (x : prod A B) : (term556 A B a s t x) = (term612 A B a s t x).
Proof. exact (EQ_MP (@lem4320940 A B a s t x) (@lem4323105 A B a s t x)). Qed.
Lemma lem4323111 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term615 A B a s t.
Proof. exact (fun x : prod A B => @lem4323106 A B a s t x). Qed.
Lemma lem4323116 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term625 A B s t.
Proof. exact (fun a : A => @lem4323111 A B a s t). Qed.
Lemma lem4323121 {A B : Type'} (t : type1413 A B) : term629 A B t.
Proof. exact (fun s : A -> Prop => @lem4323116 A B s t). Qed.
Lemma lem4323126 {A B : Type'} : term633 A B.
Proof. exact (fun t : type1413 A B => @lem4323121 A B t). Qed.
Lemma lem4323127 {A B : Type'} : term632 A B.
Proof. exact (EQ_MP (@lem4320936 A B) (@lem4323126 A B)). Qed.
Lemma lem4323128 {A B : Type'} (t : type1413 A B) : term967 A B t.
Proof. exact (@lem4323127 A B t). Qed.
Lemma lem4323129 {A B : Type'} (t : type1413 A B) : (term967 A B t) = (term628 A B t).
Proof. exact (eq_refl (term967 A B t)). Qed.
Lemma lem4323130 {A B : Type'} (t : type1413 A B) : term628 A B t.
Proof. exact (EQ_MP (@lem4323129 A B t) (@lem4323128 A B t)). Qed.
Lemma lem4323131 {A B : Type'} (t : type1413 A B) (s : A -> Prop) : term968 A B t s.
Proof. exact (@lem4323130 A B t s). Qed.
Lemma lem4323132 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term968 A B t s) = (term624 A B s t).
Proof. exact (eq_refl (term968 A B t s)). Qed.
Lemma lem4323133 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term624 A B s t.
Proof. exact (EQ_MP (@lem4323132 A B s t) (@lem4323131 A B t s)). Qed.
Lemma lem4323134 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (a : A) : term969 A B s t a.
Proof. exact (@lem4323133 A B s t a). Qed.
Lemma lem4323135 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term969 A B s t a) = (term616 A B a s t).
Proof. exact (eq_refl (term969 A B s t a)). Qed.
Lemma lem4323136 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term616 A B a s t.
Proof. exact (EQ_MP (@lem4323135 A B a s t) (@lem4323134 A B s t a)). Qed.
Lemma lem4323138 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term616 A B a s t.
Proof. exact (@lem4320590 A B a s t (@lem4323136 A B a s t)). Qed.
Lemma lem4323139 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term617 A B a s t) : False.
Proof. exact (@lem4323138 A B a s t (@lem4320574 A B a s t h1)). Qed.
Lemma lem4323140 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term617 A B a s t) : (term617 A B a s t) = False.
Proof. exact (prop_ext (fun h2 : term617 A B a s t => @lem4323139 A B a s t h1) (fun h2 : False => @lem4320574 A B a s t h1)). Qed.
Lemma lem4323141 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) (h1 : term617 A B a s t) : False.
Proof. exact (EQ_MP (@lem4323140 A B a s t h1) (@lem4320574 A B a s t h1)). Qed.
Lemma lem4323142 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term616 A B a s t.
Proof. exact (fun h0 : term617 A B a s t => @lem4323141 A B a s t h0). Qed.
Lemma lem4323143 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : term615 A B a s t.
Proof. exact (EQ_MP (@lem4320573 A B a s t) (@lem4323142 A B a s t)). Qed.
Lemma lem4323144 {A B : Type'} (a : A) (s : A -> Prop) (t : type1413 A B) : (term477 A B a s t) = (term478 A B a s t).
Proof. exact (EQ_MP (@lem4320569 A B a s t) (@lem4323143 A B a s t)). Qed.
Lemma lem4323145 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term314 A a s) : ((term477 A B a s t) = (term478 A B a s t)) = (term513 A B a s t).
Proof. exact (prop_ext (fun h3 : (term477 A B a s t) = (term478 A B a s t) => @lem4320284 A B a s t h1 h2 h3) (fun h3 : term513 A B a s t => @lem4323144 A B a s t)). Qed.
Lemma lem4323146 {A B : Type'} (t : type1413 A B) (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term314 A a s) : term513 A B a s t.
Proof. exact (EQ_MP (@lem4323145 A B t a s h1 h2) (@lem4323144 A B a s t)). Qed.
Lemma lem4323151 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term314 A a s) : term364 A B a s.
Proof. exact (fun t : type1413 A B => @lem4323146 A B t a s h1 h2). Qed.
Lemma lem4323152 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term360 A B a s) : term358 A a s.
Proof. exact (proj2 (@lem4319941 A B a s h1)). Qed.
Lemma lem4323153 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term360 A B a s) : term343 A B s.
Proof. exact (proj1 (@lem4319941 A B a s h1)). Qed.
Lemma lem4323155 {A : Type'} (a : A) (s : A -> Prop) (h1 : term358 A a s) : term314 A a s.
Proof. exact (proj1 (@lem4319942 A a s h1)). Qed.
Lemma lem4323156 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term314 A a s) : (term314 A a s) = (term364 A B a s).
Proof. exact (prop_ext (fun h3 : term314 A a s => @lem4323151 A B a s h1 h2) (fun h3 : term364 A B a s => @lem4319945 A a s h2)). Qed.
Lemma lem4323157 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term314 A a s) : term364 A B a s.
Proof. exact (EQ_MP (@lem4323156 A B a s h1 h2) (@lem4319945 A a s h2)). Qed.
Lemma lem4323158 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term358 A a s) : (term314 A a s) = (term364 A B a s).
Proof. exact (prop_ext (fun h3 : term314 A a s => @lem4323157 A B a s h1 h3) (fun h3 : term364 A B a s => @lem4323155 A a s h2)). Qed.
Lemma lem4323159 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term358 A a s) : term364 A B a s.
Proof. exact (EQ_MP (@lem4323158 A B a s h1 h2) (@lem4323155 A a s h2)). Qed.
Lemma lem4323160 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term358 A a s) : (term343 A B s) = (term364 A B a s).
Proof. exact (prop_ext (fun h3 : term343 A B s => @lem4323159 A B a s h1 h2) (fun h3 : term364 A B a s => @lem4319943 A B s h1)). Qed.
Lemma lem4323161 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term358 A a s) : term364 A B a s.
Proof. exact (EQ_MP (@lem4323160 A B a s h1 h2) (@lem4319943 A B s h1)). Qed.
Lemma lem4323162 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term360 A B a s) : (term358 A a s) = (term364 A B a s).
Proof. exact (prop_ext (fun h3 : term358 A a s => @lem4323161 A B a s h1 h3) (fun h3 : term364 A B a s => @lem4323152 A B a s h2)). Qed.
Lemma lem4323163 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term343 A B s) (h2 : term360 A B a s) : term364 A B a s.
Proof. exact (EQ_MP (@lem4323162 A B a s h1 h2) (@lem4323152 A B a s h2)). Qed.
Lemma lem4323164 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term360 A B a s) : (term343 A B s) = (term364 A B a s).
Proof. exact (prop_ext (fun h2 : term343 A B s => @lem4323163 A B a s h2 h1) (fun h2 : term364 A B a s => @lem4323153 A B a s h1)). Qed.
Lemma lem4323165 {A B : Type'} (a : A) (s : A -> Prop) (h1 : term360 A B a s) : term364 A B a s.
Proof. exact (EQ_MP (@lem4323164 A B a s h1) (@lem4323153 A B a s h1)). Qed.
Lemma lem4323166 {A B : Type'} (a : A) (s : A -> Prop) : term366 A B a s.
Proof. exact (fun h0 : term360 A B a s => @lem4323165 A B a s h0). Qed.
Lemma lem4323171 {A B : Type'} (a : A) : term370 A B a.
Proof. exact (fun s : A -> Prop => @lem4323166 A B a s). Qed.
Lemma lem4323176 {A B : Type'} : term374 A B.
Proof. exact (fun a : A => @lem4323171 A B a). Qed.
Lemma lem4323177 {A B : Type'} : term376 A B.
Proof. exact (conj (@lem4319940 A B) (@lem4323176 A B)). Qed.
Lemma lem4323178 {A B : Type'} : term348 A B.
Proof. exact (@lem4319759 A B (@lem4323177 A B)). Qed.
Lemma lem4323179 {A B : Type'} : term347 A B.
Proof. exact (EQ_MP (@lem4319726 A B) (@lem4323178 A B)). Qed.
Lemma lem4323180 {A B : Type'} (s : A -> Prop) : term970 A B s.
Proof. exact (@lem4323179 A B s). Qed.
Lemma lem4323181 {A B : Type'} (s : A -> Prop) : (term970 A B s) = (term338 A B s).
Proof. exact (eq_refl (term970 A B s)). Qed.
Lemma lem4323182 {A B : Type'} (s : A -> Prop) : term338 A B s.
Proof. exact (EQ_MP (@lem4323181 A B s) (@lem4323180 A B s)). Qed.
Lemma lem4323183 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term971 A B s t.
Proof. exact (@lem4323182 A B s t). Qed.
Lemma lem4323184 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : (term971 A B s t) = (term335 A B s t).
Proof. exact (eq_refl (term971 A B s t)). Qed.
Lemma lem4323185 {A B : Type'} (s : A -> Prop) (t : type1413 A B) : term335 A B s t.
Proof. exact (EQ_MP (@lem4323184 A B s t) (@lem4323183 A B s t)). Qed.
Lemma lem4323186 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : @FINITE A s) : term332 A B s t.
Proof. exact (@lem4323185 A B s t (@lem4318614 A s h1)). Qed.
Lemma lem4323187 {A B : Type'} (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term447 A B s t.
Proof. exact (@lem4323186 A B t s h2 (@lem4318613 A B s t h1)). Qed.
Lemma lem4323188 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term972 A B C f s t.
Proof. exact (@lem4318994 A B C f s t (@lem4323187 A B t s h1 h2)). Qed.
Lemma lem4323189 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term257 A B C f s t.
Proof. exact (conj (@lem4323188 A B C f t s h1 h2) (@lem4319610 A B C f s t)). Qed.
Lemma lem4323190 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term215 A B C f s t.
Proof. exact (EQ_MP (@lem4318990 A B C f s t) (@lem4323189 A B C f t s h1 h2)). Qed.
Lemma lem4323191 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term214 A B C f s t.
Proof. exact (EQ_MP (@lem4318889 A B C f s t) (@lem4323190 A B C f t s h1 h2)). Qed.
Lemma lem4323192 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term973 A B C s t f.
Proof. exact (ex_intro (term974 A B C s t f) (term100 A B C f s t) (@lem4323191 A B C f t s h1 h2)). Qed.
Lemma lem4323193 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term975 A B C s t f.
Proof. exact (@lem4318618 A B C s t f (@lem4323192 A B C f t s h1 h2)). Qed.
Lemma lem4323194 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term94 A B s t) : term95 A B s t.
Proof. exact (proj2 (@lem4318612 A B s t h1)). Qed.
Lemma lem4323195 {A B : Type'} (s : A -> Prop) (t : type1413 A B) (h1 : term94 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem4318612 A B s t h1)). Qed.
Lemma lem4323196 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : (term95 A B s t) = (term975 A B C s t f).
Proof. exact (prop_ext (fun h3 : term95 A B s t => @lem4323193 A B C f t s h1 h2) (fun h3 : term975 A B C s t f => @lem4318613 A B s t h1)). Qed.
Lemma lem4323197 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term975 A B C s t f.
Proof. exact (EQ_MP (@lem4323196 A B C f t s h1 h2) (@lem4318613 A B s t h1)). Qed.
Lemma lem4323198 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : (@FINITE A s) = (term975 A B C s t f).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4323197 A B C f t s h1 h2) (fun h3 : term975 A B C s t f => @lem4318614 A s h2)). Qed.
Lemma lem4323199 {A B C : Type'} (f : type1412 A B C) (t : type1413 A B) (s : A -> Prop) (h1 : term95 A B s t) (h2 : @FINITE A s) : term975 A B C s t f.
Proof. exact (EQ_MP (@lem4323198 A B C f t s h1 h2) (@lem4318614 A s h2)). Qed.
Lemma lem4323200 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : @FINITE A s) (h2 : term94 A B s t) : (term95 A B s t) = (term975 A B C s t f).
Proof. exact (prop_ext (fun h3 : term95 A B s t => @lem4323199 A B C f t s h3 h1) (fun h3 : term975 A B C s t f => @lem4323194 A B s t h2)). Qed.
Lemma lem4323201 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : @FINITE A s) (h2 : term94 A B s t) : term975 A B C s t f.
Proof. exact (EQ_MP (@lem4323200 A B C f s t h1 h2) (@lem4323194 A B s t h2)). Qed.
Lemma lem4323202 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term94 A B s t) : (@FINITE A s) = (term975 A B C s t f).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem4323201 A B C f s t h2 h1) (fun h2 : term975 A B C s t f => @lem4323195 A B s t h1)). Qed.
Lemma lem4323203 {A B C : Type'} (f : type1412 A B C) (s : A -> Prop) (t : type1413 A B) (h1 : term94 A B s t) : term975 A B C s t f.
Proof. exact (EQ_MP (@lem4323202 A B C f s t h1) (@lem4323195 A B s t h1)). Qed.
Lemma lem4323204 {A B C : Type'} (s : A -> Prop) (t : type1413 A B) (f : type1412 A B C) : term976 A B C s t f.
Proof. exact (fun h0 : term94 A B s t => @lem4323203 A B C f s t h0). Qed.
Lemma lem4323209 {A B C : Type'} (s : A -> Prop) (f : type1412 A B C) : term977 A B C s f.
Proof. exact (fun t : type1413 A B => @lem4323204 A B C s t f). Qed.
Lemma lem4323214 {A B C : Type'} (f : type1412 A B C) : term978 A B C f.
Proof. exact (fun s : A -> Prop => @lem4323209 A B C s f). Qed.
Lemma lem4323219 {A B C : Type'} : term979 A B C.
Proof. exact (fun f : type1412 A B C => @lem4323214 A B C f). Qed.
