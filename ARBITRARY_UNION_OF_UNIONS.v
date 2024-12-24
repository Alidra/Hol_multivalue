Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ARBITRARY_UNION_OF_UNIONS_term_abbrevs.
Require Import ARBITRARY_spec.
Require Import ARBITRARY_UNION_OF_IDEMPOT_spec.
Require Import UNION_OF_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem4868383 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4841086 A P). Qed.
Lemma lem4868384 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4868385 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4868384 A P) (@lem4868383 A P)). Qed.
Lemma lem4868386 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4868385 A P Q). Qed.
Lemma lem4868387 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@UNION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4868390 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@UNION_OF A (@ARBITRARY A) P)) : (term4 A P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (h1). Qed.
Lemma lem4868391 {A : Type'} (P : type686 A) (h1 : (term4 A P) = (@UNION_OF A (@ARBITRARY A) P)) : (@UNION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (SYM (@lem4868390 A P h1)). Qed.
Lemma lem4868392 {A : Type'} (P : type686 A) (h1 : (@UNION_OF A (@ARBITRARY A) P) = (term4 A P)) : (@UNION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (h1). Qed.
Lemma lem4868393 {A : Type'} (P : type686 A) (h1 : (@UNION_OF A (@ARBITRARY A) P) = (term4 A P)) : (term4 A P) = (@UNION_OF A (@ARBITRARY A) P).
Proof. exact (SYM (@lem4868392 A P h1)). Qed.
Lemma lem4868394 {A : Type'} (P : type686 A) : ((term4 A P) = (@UNION_OF A (@ARBITRARY A) P)) = ((@UNION_OF A (@ARBITRARY A) P) = (term4 A P)).
Proof. exact (prop_ext (fun h1 : (term4 A P) = (@UNION_OF A (@ARBITRARY A) P) => @lem4868391 A P h1) (fun h1 : (@UNION_OF A (@ARBITRARY A) P) = (term4 A P) => @lem4868393 A P h1)). Qed.
Lemma lem4868395 {A : Type'} : (term5 A) = (term6 A).
Proof. exact (fun_ext (fun P : type686 A => @lem4868394 A P)). Qed.
Lemma lem4868396 {A : Type'} : (@all ((A -> Prop) -> Prop)) = (@all ((A -> Prop) -> Prop)).
Proof. exact (eq_refl (@all ((A -> Prop) -> Prop))). Qed.
Lemma lem4868397 {A : Type'} : (term7 A) = (term8 A).
Proof. exact (MK_COMB (@lem4868396 A) (@lem4868395 A)). Qed.
Lemma lem4868398 {A : Type'} : term8 A.
Proof. exact (EQ_MP (@lem4868397 A) (@lem4868151 A)). Qed.
Lemma lem4868399 {A : Type'} (P : type686 A) : term9 A P.
Proof. exact (@lem4868398 A P). Qed.
Lemma lem4868400 {A : Type'} (P : type686 A) : (term9 A P) = ((@UNION_OF A (@ARBITRARY A) P) = (term4 A P)).
Proof. exact (eq_refl (term9 A P)). Qed.
Lemma lem4868402 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term10 A u P.
Proof. exact (h1). Qed.
Lemma lem4868404 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (EQ_MP (@lem4868400 A P) (@lem4868399 A P)). Qed.
Lemma lem4868405 {A : Type'} (P : type686 A) : (@UNION_OF A (@ARBITRARY A) P) = (term4 A P).
Proof. exact (@lem4868404 A P). Qed.
Lemma lem4868406 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4868407 {A : Type'} (P : type686 A) (u : type686 A) : (term11 A P u) = (term12 A P u).
Proof. exact (MK_COMB (@lem4868405 A P) (@lem4868406 A u)). Qed.
Lemma lem4868408 {A : Type'} (P : type686 A) (u : type686 A) : (term12 A P u) = (term11 A P u).
Proof. exact (SYM (@lem4868407 A P u)). Qed.
Lemma lem4868410 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4868387 A P Q) (@lem4868386 A P Q)). Qed.
Lemma lem4868411 {A : Type'} (P : type180 A) (Q : type686 A) : (@UNION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4868410 A P Q). Qed.
Lemma lem4868412 {A : Type'} (P : type686 A) : (term4 A P) = (term13 A P).
Proof. exact (@lem4868411 A (@ARBITRARY A) (@UNION_OF A (@ARBITRARY A) P)). Qed.
Lemma lem4868413 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4868414 {A : Type'} (P : type686 A) (u : type686 A) : (term12 A P u) = (term14 A P u).
Proof. exact (MK_COMB (@lem4868412 A P) (@lem4868413 A u)). Qed.
Lemma lem4868415 {A : Type'} (P : type686 A) (u : type686 A) : (term14 A P u) = (term12 A P u).
Proof. exact (SYM (@lem4868414 A P u)). Qed.
Lemma lem4868417 {A B : Type'} (f : A -> B) (y : A) : (term15 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4868418 {A : Type'} (f : type686 A) (y : A -> Prop) : (term16 A f y) = (f y).
Proof. exact (@lem4868417 (A -> Prop) Prop f y). Qed.
Lemma lem4868419 {A : Type'} (P : type686 A) (u : type686 A) : (term17 A P u) = (term14 A P u).
Proof. exact (@lem4868418 A (term13 A P) (@UNIONS A u)). Qed.
Lemma lem4868420 {A : Type'} (P : type686 A) (s : A -> Prop) : (term18 A P s) = (term19 A P s).
Proof. exact (eq_refl (term18 A P s)). Qed.
Lemma lem4868421 {A : Type'} (P : type686 A) : (term20 A P) = (term13 A P).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4868420 A P s)). Qed.
Lemma lem4868422 {A : Type'} (u : type686 A) : (@UNIONS A u) = (@UNIONS A u).
Proof. exact (eq_refl (@UNIONS A u)). Qed.
Lemma lem4868423 {A : Type'} (P : type686 A) (u : type686 A) : (term17 A P u) = (term14 A P u).
Proof. exact (MK_COMB (@lem4868421 A P) (@lem4868422 A u)). Qed.
Lemma lem4868424 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4868425 {A : Type'} (P : type686 A) (u : type686 A) : (term21 A P u) = (term22 A P u).
Proof. exact (MK_COMB (@lem4868424) (@lem4868423 A P u)). Qed.
Lemma lem4868426 {A : Type'} (P : type686 A) (u : type686 A) : (term14 A P u) = (term23 A P u).
Proof. exact (eq_refl (term14 A P u)). Qed.
Lemma lem4868427 {A : Type'} (P : type686 A) (u : type686 A) : ((term17 A P u) = (term14 A P u)) = ((term14 A P u) = (term23 A P u)).
Proof. exact (MK_COMB (@lem4868425 A P u) (@lem4868426 A P u)). Qed.
Lemma lem4868428 {A : Type'} (P : type686 A) (u : type686 A) : (term14 A P u) = (term23 A P u).
Proof. exact (EQ_MP (@lem4868427 A P u) (@lem4868419 A P u)). Qed.
Lemma lem4868445 {A : Type'} (P : type686 A) (u : type686 A) : (term23 A P u) = (term14 A P u).
Proof. exact (SYM (@lem4868428 A P u)). Qed.
Lemma lem4868446 {A : Type'} (s : type686 A) : term24 A s.
Proof. exact (@lem4853019 A s). Qed.
Lemma lem4868447 {A : Type'} (s : type686 A) : (term24 A s) = ((@ARBITRARY A s) = True).
Proof. exact (eq_refl (term24 A s)). Qed.
Lemma lem4868449 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term25 A u P s.
Proof. exact (@lem4868402 A u P h1 s). Qed.
Lemma lem4868450 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term25 A u P s) = (term26 A u P s).
Proof. exact (eq_refl (term25 A u P s)). Qed.
Lemma lem4868451 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term26 A u P s.
Proof. exact (EQ_MP (@lem4868450 A u P s) (@lem4868449 A s u P h1)). Qed.
Lemma lem4868452 {A : Type'} (u : type686 A) (P : type686 A) (s : A -> Prop) : (term26 A u P s) = ((term26 A u P s) = True).
Proof. exact (@lem7 (term26 A u P s)). Qed.
Lemma lem4868457 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (EQ_MP (@lem4868447 A s) (@lem4868446 A s)). Qed.
Lemma lem4868458 {A : Type'} (s : type686 A) : (@ARBITRARY A s) = True.
Proof. exact (@lem4868457 A s). Qed.
Lemma lem4868459 {A : Type'} (u : type686 A) : (@ARBITRARY A u) = True.
Proof. exact (@lem4868458 A u). Qed.
Lemma lem4868460 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868461 {A : Type'} (u : type686 A) : (term27 A u) = (and True).
Proof. exact (MK_COMB (@lem4868460) (@lem4868459 A u)). Qed.
Lemma lem4868469 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term26 A u P s) = True.
Proof. exact (EQ_MP (@lem4868452 A u P s) (@lem4868451 A s u P h1)). Qed.
Lemma lem4868470 {A : Type'} (s : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term26 A u P s) = True.
Proof. exact (@lem4868469 A s u P h1). Qed.
Lemma lem4868471 {A : Type'} (c : A -> Prop) (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term26 A u P c) = True.
Proof. exact (@lem4868470 A c u P h1). Qed.
Lemma lem4868472 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term28 A u P) = (term29 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4868471 A c u P h1)). Qed.
Lemma lem4868473 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4868474 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term10 A u P) = (term30 A).
Proof. exact (MK_COMB (@lem4868473 A) (@lem4868472 A u P h1)). Qed.
Lemma lem4868476 {A : Type'} (t : Prop) : (term31 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4868477 {A : Type'} (t : Prop) : (term32 A t) = t.
Proof. exact (@lem4868476 (A -> Prop) t). Qed.
Lemma lem4868478 {A : Type'} : (term30 A) = True.
Proof. exact (@lem4868477 A True). Qed.
Lemma lem4868479 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term10 A u P) = True.
Proof. exact (TRANS (@lem4868474 A u P h1) (@lem4868478 A)). Qed.
Lemma lem4868480 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4868481 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term33 A u P) = (and True).
Proof. exact (MK_COMB (@lem4868480) (@lem4868479 A u P h1)). Qed.
Lemma lem4868483 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4868484 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4868483 (A -> Prop) x). Qed.
Lemma lem4868485 {A : Type'} (u : type686 A) : ((@UNIONS A u) = (@UNIONS A u)) = True.
Proof. exact (@lem4868484 A (@UNIONS A u)). Qed.
Lemma lem4868486 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term34 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4868481 A u P h1) (@lem4868485 A u)). Qed.
Lemma lem4868488 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4868489 : (True /\ True) = True.
Proof. exact (@lem4868488 True). Qed.
Lemma lem4868490 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term34 A P u) = True.
Proof. exact (TRANS (@lem4868486 A u P h1) (@lem4868489)). Qed.
Lemma lem4868491 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term35 A P u) = (True /\ True).
Proof. exact (MK_COMB (@lem4868461 A u) (@lem4868490 A u P h1)). Qed.
Lemma lem4868493 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4868494 : (True /\ True) = True.
Proof. exact (@lem4868493 True). Qed.
Lemma lem4868495 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term35 A P u) = True.
Proof. exact (TRANS (@lem4868491 A u P h1) (@lem4868494)). Qed.
Lemma lem4868496 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : True = (term35 A P u).
Proof. exact (SYM (@lem4868495 A u P h1)). Qed.
Lemma lem4868497 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term35 A P u.
Proof. exact (EQ_MP (@lem4868496 A u P h1) (@lem0)). Qed.
Lemma lem4868498 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term23 A P u.
Proof. exact (ex_intro (term36 A P u) u (@lem4868497 A u P h1)). Qed.
Lemma lem4868499 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term14 A P u.
Proof. exact (EQ_MP (@lem4868445 A P u) (@lem4868498 A u P h1)). Qed.
Lemma lem4868500 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term12 A P u.
Proof. exact (EQ_MP (@lem4868415 A P u) (@lem4868499 A u P h1)). Qed.
Lemma lem4868501 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term11 A P u.
Proof. exact (EQ_MP (@lem4868408 A P u) (@lem4868500 A u P h1)). Qed.
Lemma lem4868502 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : (term10 A u P) = (term11 A P u).
Proof. exact (prop_ext (fun h2 : term10 A u P => @lem4868501 A u P h1) (fun h2 : term11 A P u => @lem4868402 A u P h1)). Qed.
Lemma lem4868503 {A : Type'} (u : type686 A) (P : type686 A) (h1 : term10 A u P) : term11 A P u.
Proof. exact (EQ_MP (@lem4868502 A u P h1) (@lem4868402 A u P h1)). Qed.
Lemma lem4868504 {A : Type'} (P : type686 A) (u : type686 A) : term37 A P u.
Proof. exact (fun h0 : term10 A u P => @lem4868503 A u P h0). Qed.
Lemma lem4868509 {A : Type'} (P : type686 A) : term38 A P.
Proof. exact (fun u : type686 A => @lem4868504 A P u). Qed.
Lemma lem4868514 {A : Type'} : term39 A.
Proof. exact (fun P : type686 A => @lem4868509 A P). Qed.
