Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_PRODUCT_term_abbrevs.
Require Import HAS_SIZE_spec.
Require Import HAS_SIZE_PRODUCT_DEPENDENT_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1820_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4323392 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4318348 A B s). Qed.
Lemma lem4323393 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4323394 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4323393 A B s) (@lem4323392 A B s)). Qed.
Lemma lem4323395 {A B : Type'} (s : A -> Prop) : term2 A B s.
Proof. exact (@lem4323394 A B s (@CARD A s)). Qed.
Lemma lem4323396 {A B : Type'} (s : A -> Prop) : (term2 A B s) = (term3 A B s).
Proof. exact (eq_refl (term2 A B s)). Qed.
Lemma lem4323397 {A B : Type'} (s : A -> Prop) : term3 A B s.
Proof. exact (EQ_MP (@lem4323396 A B s) (@lem4323395 A B s)). Qed.
Lemma lem4323398 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term4 A B s t.
Proof. exact (@lem4323397 A B s (term5 A B t)). Qed.
Lemma lem4323399 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : (term4 A B s t) = (term6 A B t s).
Proof. exact (eq_refl (term4 A B s t)). Qed.
Lemma lem4323400 {A B : Type'} (t : B -> Prop) (s : A -> Prop) : term6 A B t s.
Proof. exact (EQ_MP (@lem4323399 A B t s) (@lem4323398 A B s t)). Qed.
Lemma lem4323401 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term7 A B s t.
Proof. exact (@lem4323400 A B t s (@CARD B t)). Qed.
Lemma lem4323402 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term7 A B s t) = (term8 A B s t).
Proof. exact (eq_refl (term7 A B s t)). Qed.
Lemma lem4323403 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term8 A B s t.
Proof. exact (EQ_MP (@lem4323402 A B s t) (@lem4323401 A B s t)). Qed.
Lemma lem4323404 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term9 A B s t) : term9 A B s t.
Proof. exact (h1). Qed.
Lemma lem4323405 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : @FINITE B t.
Proof. exact (h1). Qed.
Lemma lem4323406 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4323407 {_100044 : Type'} (s : _100044 -> Prop) : term10 _100044 s.
Proof. exact (@lem3863773 _100044 s). Qed.
Lemma lem4323408 {_100044 : Type'} (s : _100044 -> Prop) : (term10 _100044 s) = (term11 _100044 s).
Proof. exact (eq_refl (term10 _100044 s)). Qed.
Lemma lem4323409 {_100044 : Type'} (s : _100044 -> Prop) : term11 _100044 s.
Proof. exact (EQ_MP (@lem4323408 _100044 s) (@lem4323407 _100044 s)). Qed.
Lemma lem4323410 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : term12 _100044 s n.
Proof. exact (@lem4323409 _100044 s n). Qed.
Lemma lem4323411 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (term12 _100044 s n) = ((@HAS_SIZE _100044 s n) = (term13 _100044 s n)).
Proof. exact (eq_refl (term12 _100044 s n)). Qed.
Lemma lem4323413 {A : Type'} (s : A -> Prop) : (@FINITE A s) = ((@FINITE A s) = True).
Proof. exact (@lem7 (@FINITE A s)). Qed.
Lemma lem4323415 {B : Type'} (t : B -> Prop) : (@FINITE B t) = ((@FINITE B t) = True).
Proof. exact (@lem7 (@FINITE B t)). Qed.
Lemma lem4323420 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4323421 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem4323420 p q p' q'). Qed.
Lemma lem4323422 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem4323421 p q p'). Qed.
Lemma lem4323423 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term17 A B s t.
Proof. exact (@lem4323422 (term8 A B s t) ((term18 A B s t) = (term19 A B s t))). Qed.
Lemma lem4323424 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term20 A B s t p'.
Proof. exact (@lem4323423 A B s t p'). Qed.
Lemma lem4323425 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : (term20 A B s t p') = (term21 A B s t p').
Proof. exact (eq_refl (term20 A B s t p')). Qed.
Lemma lem4323426 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term21 A B s t p'.
Proof. exact (EQ_MP (@lem4323425 A B s t p') (@lem4323424 A B s t p')). Qed.
Lemma lem4323427 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term22 A B s t p' q'.
Proof. exact (@lem4323426 A B s t p' q'). Qed.
Lemma lem4323428 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : (term22 A B s t p' q') = (term23 A B s t p' q').
Proof. exact (eq_refl (term22 A B s t p' q')). Qed.
Lemma lem4323429 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term23 A B s t p' q'.
Proof. exact (EQ_MP (@lem4323428 A B s t p' q') (@lem4323427 A B s t p' q')). Qed.
Lemma lem4323433 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4323434 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem4323433 p q p' q'). Qed.
Lemma lem4323435 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem4323434 p q p'). Qed.
Lemma lem4323436 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term24 A B s t.
Proof. exact (@lem4323435 (term25 A B s t) (term26 A B s t)). Qed.
Lemma lem4323437 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term27 A B s t p'.
Proof. exact (@lem4323436 A B s t p'). Qed.
Lemma lem4323438 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : (term27 A B s t p') = (term28 A B s t p').
Proof. exact (eq_refl (term27 A B s t p')). Qed.
Lemma lem4323439 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) : term28 A B s t p'.
Proof. exact (EQ_MP (@lem4323438 A B s t p') (@lem4323437 A B s t p')). Qed.
Lemma lem4323440 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term29 A B s t p' q'.
Proof. exact (@lem4323439 A B s t p' q'). Qed.
Lemma lem4323441 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : (term29 A B s t p' q') = (term30 A B s t p' q').
Proof. exact (eq_refl (term29 A B s t p' q')). Qed.
Lemma lem4323442 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (p' : Prop) (q' : Prop) : term30 A B s t p' q'.
Proof. exact (EQ_MP (@lem4323441 A B s t p' q') (@lem4323440 A B s t p' q')). Qed.
Lemma lem4323446 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term13 _100044 s n).
Proof. exact (EQ_MP (@lem4323411 _100044 s n) (@lem4323410 _100044 s n)). Qed.
Lemma lem4323447 {A : Type'} (s : A -> Prop) (n : nat) : (@HAS_SIZE A s n) = (term13 A s n).
Proof. exact (@lem4323446 A s n). Qed.
Lemma lem4323448 {A : Type'} (s : A -> Prop) : (term31 A s) = (term32 A s).
Proof. exact (@lem4323447 A s (@CARD A s)). Qed.
Lemma lem4323452 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (@FINITE A s) = True.
Proof. exact (EQ_MP (@lem4323413 A s) (@lem4323406 A s h1)). Qed.
Lemma lem4323453 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4323454 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term33 A s) = (and True).
Proof. exact (MK_COMB (@lem4323453) (@lem4323452 A s h1)). Qed.
Lemma lem4323456 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4323457 (x : nat) : (x = x) = True.
Proof. exact (@lem4323456 nat x). Qed.
Lemma lem4323458 {A : Type'} (s : A -> Prop) : ((@CARD A s) = (@CARD A s)) = True.
Proof. exact (@lem4323457 (@CARD A s)). Qed.
Lemma lem4323459 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term32 A s) = (True /\ True).
Proof. exact (MK_COMB (@lem4323454 A s h1) (@lem4323458 A s)). Qed.
Lemma lem4323461 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4323462 : (True /\ True) = True.
Proof. exact (@lem4323461 True). Qed.
Lemma lem4323463 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term32 A s) = True.
Proof. exact (TRANS (@lem4323459 A s h1) (@lem4323462)). Qed.
Lemma lem4323464 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term31 A s) = True.
Proof. exact (TRANS (@lem4323448 A s) (@lem4323463 A s h1)). Qed.
Lemma lem4323465 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4323466 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : (term34 A s) = (and True).
Proof. exact (MK_COMB (@lem4323465) (@lem4323464 A s h1)). Qed.
Lemma lem4323474 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term14 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4323475 (p : Prop) (q : Prop) (p' : Prop) : term15 p q p'.
Proof. exact (fun q' : Prop => @lem4323474 p q p' q'). Qed.
Lemma lem4323476 (p : Prop) (q : Prop) : term16 p q.
Proof. exact (fun p' : Prop => @lem4323475 p q p'). Qed.
Lemma lem4323477 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) : term35 A B s x t.
Proof. exact (@lem4323476 (@IN A x s) (term36 A B x t)). Qed.
Lemma lem4323478 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (p' : Prop) : term37 A B s x t p'.
Proof. exact (@lem4323477 A B s x t p'). Qed.
Lemma lem4323479 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (p' : Prop) : (term37 A B s x t p') = (term38 A B s x t p').
Proof. exact (eq_refl (term37 A B s x t p')). Qed.
Lemma lem4323480 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (p' : Prop) : term38 A B s x t p'.
Proof. exact (EQ_MP (@lem4323479 A B s x t p') (@lem4323478 A B s x t p')). Qed.
Lemma lem4323481 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (p' : Prop) (q' : Prop) : term39 A B s x t p' q'.
Proof. exact (@lem4323480 A B s x t p' q'). Qed.
Lemma lem4323482 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (p' : Prop) (q' : Prop) : (term39 A B s x t p' q') = (term40 A B s x t p' q').
Proof. exact (eq_refl (term39 A B s x t p' q')). Qed.
Lemma lem4323483 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (p' : Prop) (q' : Prop) : term40 A B s x t p' q'.
Proof. exact (EQ_MP (@lem4323482 A B s x t p' q') (@lem4323481 A B s x t p' q')). Qed.
Lemma lem4323484 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem4323485 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (q' : Prop) : term41 A B t x s q'.
Proof. exact (@lem4323483 A B s x t (@IN A x s) q'). Qed.
Lemma lem4323486 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) (q' : Prop) : term42 A B t x s q'.
Proof. exact (@lem4323485 A B t x s q' (@lem4323484 A x s)). Qed.
Lemma lem4323491 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term13 _100044 s n).
Proof. exact (EQ_MP (@lem4323411 _100044 s n) (@lem4323410 _100044 s n)). Qed.
Lemma lem4323492 {B : Type'} (s : B -> Prop) (n : nat) : (@HAS_SIZE B s n) = (term13 B s n).
Proof. exact (@lem4323491 B s n). Qed.
Lemma lem4323493 {A B : Type'} (x : A) (t : B -> Prop) : (term36 A B x t) = (term43 A B x t).
Proof. exact (@lem4323492 B (term44 A B t x) (@CARD B t)). Qed.
Lemma lem4323497 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4323498 {A B : Type'} (f : type1413 A B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (@lem4323497 A (B -> Prop) f y). Qed.
Lemma lem4323499 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (@lem4323498 A B (term5 A B t) x). Qed.
Lemma lem4323500 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323501 {A B : Type'} (t : B -> Prop) : (term48 A B t) = (term5 A B t).
Proof. exact (fun_ext (fun x : A => @lem4323500 A B x t)). Qed.
Lemma lem4323502 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4323503 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (MK_COMB (@lem4323501 A B t) (@lem4323502 A x)). Qed.
Lemma lem4323504 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem4323505 {A B : Type'} (t : B -> Prop) (x : A) : (term49 A B t x) = (term50 A B t x).
Proof. exact (MK_COMB (@lem4323504 B) (@lem4323503 A B t x)). Qed.
Lemma lem4323506 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323507 {A B : Type'} (x : A) (t : B -> Prop) : ((term47 A B t x) = (term44 A B t x)) = ((term44 A B t x) = t).
Proof. exact (MK_COMB (@lem4323505 A B t x) (@lem4323506 A B x t)). Qed.
Lemma lem4323508 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (EQ_MP (@lem4323507 A B x t) (@lem4323499 A B t x)). Qed.
Lemma lem4323509 {B : Type'} : (@FINITE B) = (@FINITE B).
Proof. exact (eq_refl (@FINITE B)). Qed.
Lemma lem4323510 {A B : Type'} (x : A) (t : B -> Prop) : (term51 A B t x) = (@FINITE B t).
Proof. exact (MK_COMB (@lem4323509 B) (@lem4323508 A B x t)). Qed.
Lemma lem4323512 {B : Type'} (t : B -> Prop) (h1 : @FINITE B t) : (@FINITE B t) = True.
Proof. exact (EQ_MP (@lem4323415 B t) (@lem4323405 B t h1)). Qed.
Lemma lem4323513 {A B : Type'} (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term51 A B t x) = True.
Proof. exact (TRANS (@lem4323510 A B x t) (@lem4323512 B t h1)). Qed.
Lemma lem4323514 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4323515 {A B : Type'} (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term52 A B t x) = (and True).
Proof. exact (MK_COMB (@lem4323514) (@lem4323513 A B x t h1)). Qed.
Lemma lem4323519 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4323520 {A B : Type'} (f : type1413 A B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (@lem4323519 A (B -> Prop) f y). Qed.
Lemma lem4323521 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (@lem4323520 A B (term5 A B t) x). Qed.
Lemma lem4323522 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323523 {A B : Type'} (t : B -> Prop) : (term48 A B t) = (term5 A B t).
Proof. exact (fun_ext (fun x : A => @lem4323522 A B x t)). Qed.
Lemma lem4323524 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4323525 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (MK_COMB (@lem4323523 A B t) (@lem4323524 A x)). Qed.
Lemma lem4323526 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem4323527 {A B : Type'} (t : B -> Prop) (x : A) : (term49 A B t x) = (term50 A B t x).
Proof. exact (MK_COMB (@lem4323526 B) (@lem4323525 A B t x)). Qed.
Lemma lem4323528 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323529 {A B : Type'} (x : A) (t : B -> Prop) : ((term47 A B t x) = (term44 A B t x)) = ((term44 A B t x) = t).
Proof. exact (MK_COMB (@lem4323527 A B t x) (@lem4323528 A B x t)). Qed.
Lemma lem4323530 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (EQ_MP (@lem4323529 A B x t) (@lem4323521 A B t x)). Qed.
Lemma lem4323531 {B : Type'} : (@CARD B) = (@CARD B).
Proof. exact (eq_refl (@CARD B)). Qed.
Lemma lem4323532 {A B : Type'} (x : A) (t : B -> Prop) : (term53 A B t x) = (@CARD B t).
Proof. exact (MK_COMB (@lem4323531 B) (@lem4323530 A B x t)). Qed.
Lemma lem4323533 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4323534 {A B : Type'} (x : A) (t : B -> Prop) : (term54 A B t x) = (term55 B t).
Proof. exact (MK_COMB (@lem4323533) (@lem4323532 A B x t)). Qed.
Lemma lem4323535 {B : Type'} (t : B -> Prop) : (@CARD B t) = (@CARD B t).
Proof. exact (eq_refl (@CARD B t)). Qed.
Lemma lem4323536 {A B : Type'} (x : A) (t : B -> Prop) : ((term53 A B t x) = (@CARD B t)) = ((@CARD B t) = (@CARD B t)).
Proof. exact (MK_COMB (@lem4323534 A B x t) (@lem4323535 B t)). Qed.
Lemma lem4323538 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4323539 (x : nat) : (x = x) = True.
Proof. exact (@lem4323538 nat x). Qed.
Lemma lem4323540 {B : Type'} (t : B -> Prop) : ((@CARD B t) = (@CARD B t)) = True.
Proof. exact (@lem4323539 (@CARD B t)). Qed.
Lemma lem4323541 {A B : Type'} (x : A) (t : B -> Prop) : ((term53 A B t x) = (@CARD B t)) = True.
Proof. exact (TRANS (@lem4323536 A B x t) (@lem4323540 B t)). Qed.
Lemma lem4323542 {A B : Type'} (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term43 A B x t) = (True /\ True).
Proof. exact (MK_COMB (@lem4323515 A B x t h1) (@lem4323541 A B x t)). Qed.
Lemma lem4323544 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4323545 : (True /\ True) = True.
Proof. exact (@lem4323544 True). Qed.
Lemma lem4323546 {A B : Type'} (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term43 A B x t) = True.
Proof. exact (TRANS (@lem4323542 A B x t h1) (@lem4323545)). Qed.
Lemma lem4323547 {A B : Type'} (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term36 A B x t) = True.
Proof. exact (TRANS (@lem4323493 A B x t) (@lem4323546 A B x t h1)). Qed.
Lemma lem4323548 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (h1 : @FINITE B t) : term56 A B s x t.
Proof. exact (fun h0 : @IN A x s => @lem4323547 A B x t h1). Qed.
Lemma lem4323549 {A B : Type'} (t : B -> Prop) (x : A) (s : A -> Prop) : term57 A B t x s.
Proof. exact (@lem4323486 A B t x s True). Qed.
Lemma lem4323550 {A B : Type'} (x : A) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) : (term58 A B s x t) = (term59 A x s).
Proof. exact (@lem4323549 A B t x s (@lem4323548 A B s x t h1)). Qed.
Lemma lem4323552 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4323553 {A : Type'} (x : A) (s : A -> Prop) : (term59 A x s) = True.
Proof. exact (@lem4323552 (@IN A x s)). Qed.
Lemma lem4323554 {A B : Type'} (s : A -> Prop) (x : A) (t : B -> Prop) (h1 : @FINITE B t) : (term58 A B s x t) = True.
Proof. exact (TRANS (@lem4323550 A B x s t h1) (@lem4323553 A x s)). Qed.
Lemma lem4323555 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) : (term60 A B s t) = (term61 A).
Proof. exact (fun_ext (fun x : A => @lem4323554 A B s x t h1)). Qed.
Lemma lem4323556 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4323557 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) : (term62 A B s t) = (term63 A).
Proof. exact (MK_COMB (@lem4323556 A) (@lem4323555 A B s t h1)). Qed.
Lemma lem4323559 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4323560 {A : Type'} (t : Prop) : (term64 A t) = t.
Proof. exact (@lem4323559 A t). Qed.
Lemma lem4323561 {A : Type'} : (term63 A) = True.
Proof. exact (@lem4323560 A True). Qed.
Lemma lem4323562 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE B t) : (term62 A B s t) = True.
Proof. exact (TRANS (@lem4323557 A B s t h1) (@lem4323561 A)). Qed.
Lemma lem4323563 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term25 A B s t) = (True /\ True).
Proof. exact (MK_COMB (@lem4323466 A s h1) (@lem4323562 A B s t h2)). Qed.
Lemma lem4323565 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4323566 : (True /\ True) = True.
Proof. exact (@lem4323565 True). Qed.
Lemma lem4323567 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term25 A B s t) = True.
Proof. exact (TRANS (@lem4323563 A B s t h1 h2) (@lem4323566)). Qed.
Lemma lem4323568 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term65 A B s t q'.
Proof. exact (@lem4323442 A B s t True q'). Qed.
Lemma lem4323569 {A B : Type'} (q' : Prop) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term66 A B s t q'.
Proof. exact (@lem4323568 A B s t q' (@lem4323567 A B s t h1 h2)). Qed.
Lemma lem4323576 {_100044 : Type'} (s : _100044 -> Prop) (n : nat) : (@HAS_SIZE _100044 s n) = (term13 _100044 s n).
Proof. exact (EQ_MP (@lem4323411 _100044 s n) (@lem4323410 _100044 s n)). Qed.
Lemma lem4323577 {A B : Type'} (s : type1210 A B) (n : nat) : (@HAS_SIZE (prod A B) s n) = (term67 A B s n).
Proof. exact (@lem4323576 (prod A B) s n). Qed.
Lemma lem4323578 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term26 A B s t) = (term68 A B s t).
Proof. exact (@lem4323577 A B (term69 A B s t) (term19 A B s t)). Qed.
Lemma lem4323592 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4323593 {A B : Type'} (f : type1413 A B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (@lem4323592 A (B -> Prop) f y). Qed.
Lemma lem4323594 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (@lem4323593 A B (term5 A B t) x). Qed.
Lemma lem4323595 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323596 {A B : Type'} (t : B -> Prop) : (term48 A B t) = (term5 A B t).
Proof. exact (fun_ext (fun x : A => @lem4323595 A B x t)). Qed.
Lemma lem4323597 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4323598 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (MK_COMB (@lem4323596 A B t) (@lem4323597 A x)). Qed.
Lemma lem4323599 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem4323600 {A B : Type'} (t : B -> Prop) (x : A) : (term49 A B t x) = (term50 A B t x).
Proof. exact (MK_COMB (@lem4323599 B) (@lem4323598 A B t x)). Qed.
Lemma lem4323601 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323602 {A B : Type'} (x : A) (t : B -> Prop) : ((term47 A B t x) = (term44 A B t x)) = ((term44 A B t x) = t).
Proof. exact (MK_COMB (@lem4323600 A B t x) (@lem4323601 A B x t)). Qed.
Lemma lem4323603 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (EQ_MP (@lem4323602 A B x t) (@lem4323594 A B t x)). Qed.
Lemma lem4323604 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4323605 {A B : Type'} (x : A) (y : B) (t : B -> Prop) : (term70 A B y t x) = (@IN B y t).
Proof. exact (MK_COMB (@lem4323604 B y) (@lem4323603 A B x t)). Qed.
Lemma lem4323606 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term71 A x s).
Proof. exact (eq_refl (term71 A x s)). Qed.
Lemma lem4323607 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term72 A B s y t x) = (term73 A B x s y t).
Proof. exact (MK_COMB (@lem4323606 A x s) (@lem4323605 A B x y t)). Qed.
Lemma lem4323610 {A B : Type'} (GEN_PVAR_121 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_121) = (@SETSPEC (prod A B) GEN_PVAR_121).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_121)). Qed.
Lemma lem4323611 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term74 A B GEN_PVAR_121 s y t x) = (term75 A B GEN_PVAR_121 x s y t).
Proof. exact (MK_COMB (@lem4323610 A B GEN_PVAR_121) (@lem4323607 A B x s y t)). Qed.
Lemma lem4323614 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4323615 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) (y : B) : (term76 A B GEN_PVAR_121 s t x y) = (term77 A B GEN_PVAR_121 s t x y).
Proof. exact (MK_COMB (@lem4323611 A B GEN_PVAR_121 x s y t) (@lem4323614 A B x y)). Qed.
Lemma lem4323618 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) : (term78 A B GEN_PVAR_121 s t x) = (term79 A B GEN_PVAR_121 s t x).
Proof. exact (fun_ext (fun y : B => @lem4323615 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4323621 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4323622 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) : (term80 A B GEN_PVAR_121 s t x) = (term81 A B GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4323621 B) (@lem4323618 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4323629 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) : (term82 A B GEN_PVAR_121 s t) = (term83 A B GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4323622 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4323636 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4323637 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) : (term84 A B GEN_PVAR_121 s t) = (term85 A B GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4323636 A) (@lem4323629 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4323648 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term86 A B s t) = (term87 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4323637 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4323659 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4323660 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term69 A B s t) = (term88 A B s t).
Proof. exact (MK_COMB (@lem4323659 A B) (@lem4323648 A B s t)). Qed.
Lemma lem4323671 {A B : Type'} : (@FINITE (prod A B)) = (@FINITE (prod A B)).
Proof. exact (eq_refl (@FINITE (prod A B))). Qed.
Lemma lem4323672 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term89 A B s t) = (term90 A B s t).
Proof. exact (MK_COMB (@lem4323671 A B) (@lem4323660 A B s t)). Qed.
Lemma lem4323683 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4323684 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term91 A B s t) = (term92 A B s t).
Proof. exact (MK_COMB (@lem4323683) (@lem4323672 A B s t)). Qed.
Lemma lem4323708 {A B : Type'} (f : A -> B) (y : A) : (term45 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4323709 {A B : Type'} (f : type1413 A B) (y : A) : (term46 A B f y) = (f y).
Proof. exact (@lem4323708 A (B -> Prop) f y). Qed.
Lemma lem4323710 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (@lem4323709 A B (term5 A B t) x). Qed.
Lemma lem4323711 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323712 {A B : Type'} (t : B -> Prop) : (term48 A B t) = (term5 A B t).
Proof. exact (fun_ext (fun x : A => @lem4323711 A B x t)). Qed.
Lemma lem4323713 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem4323714 {A B : Type'} (t : B -> Prop) (x : A) : (term47 A B t x) = (term44 A B t x).
Proof. exact (MK_COMB (@lem4323712 A B t) (@lem4323713 A x)). Qed.
Lemma lem4323715 {B : Type'} : (@eq (B -> Prop)) = (@eq (B -> Prop)).
Proof. exact (eq_refl (@eq (B -> Prop))). Qed.
Lemma lem4323716 {A B : Type'} (t : B -> Prop) (x : A) : (term49 A B t x) = (term50 A B t x).
Proof. exact (MK_COMB (@lem4323715 B) (@lem4323714 A B t x)). Qed.
Lemma lem4323717 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (eq_refl (term44 A B t x)). Qed.
Lemma lem4323718 {A B : Type'} (x : A) (t : B -> Prop) : ((term47 A B t x) = (term44 A B t x)) = ((term44 A B t x) = t).
Proof. exact (MK_COMB (@lem4323716 A B t x) (@lem4323717 A B x t)). Qed.
Lemma lem4323719 {A B : Type'} (x : A) (t : B -> Prop) : (term44 A B t x) = t.
Proof. exact (EQ_MP (@lem4323718 A B x t) (@lem4323710 A B t x)). Qed.
Lemma lem4323720 {B : Type'} (y : B) : (@IN B y) = (@IN B y).
Proof. exact (eq_refl (@IN B y)). Qed.
Lemma lem4323721 {A B : Type'} (x : A) (y : B) (t : B -> Prop) : (term70 A B y t x) = (@IN B y t).
Proof. exact (MK_COMB (@lem4323720 B y) (@lem4323719 A B x t)). Qed.
Lemma lem4323722 {A : Type'} (x : A) (s : A -> Prop) : (term71 A x s) = (term71 A x s).
Proof. exact (eq_refl (term71 A x s)). Qed.
Lemma lem4323723 {A B : Type'} (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term72 A B s y t x) = (term73 A B x s y t).
Proof. exact (MK_COMB (@lem4323722 A x s) (@lem4323721 A B x y t)). Qed.
Lemma lem4323726 {A B : Type'} (GEN_PVAR_121 : prod A B) : (@SETSPEC (prod A B) GEN_PVAR_121) = (@SETSPEC (prod A B) GEN_PVAR_121).
Proof. exact (eq_refl (@SETSPEC (prod A B) GEN_PVAR_121)). Qed.
Lemma lem4323727 {A B : Type'} (GEN_PVAR_121 : prod A B) (x : A) (s : A -> Prop) (y : B) (t : B -> Prop) : (term74 A B GEN_PVAR_121 s y t x) = (term75 A B GEN_PVAR_121 x s y t).
Proof. exact (MK_COMB (@lem4323726 A B GEN_PVAR_121) (@lem4323723 A B x s y t)). Qed.
Lemma lem4323730 {A B : Type'} (x : A) (y : B) : (@pair A B x y) = (@pair A B x y).
Proof. exact (eq_refl (@pair A B x y)). Qed.
Lemma lem4323731 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) (y : B) : (term76 A B GEN_PVAR_121 s t x y) = (term77 A B GEN_PVAR_121 s t x y).
Proof. exact (MK_COMB (@lem4323727 A B GEN_PVAR_121 x s y t) (@lem4323730 A B x y)). Qed.
Lemma lem4323734 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) : (term78 A B GEN_PVAR_121 s t x) = (term79 A B GEN_PVAR_121 s t x).
Proof. exact (fun_ext (fun y : B => @lem4323731 A B GEN_PVAR_121 s t x y)). Qed.
Lemma lem4323737 {B : Type'} : (@ex B) = (@ex B).
Proof. exact (eq_refl (@ex B)). Qed.
Lemma lem4323738 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) (x : A) : (term80 A B GEN_PVAR_121 s t x) = (term81 A B GEN_PVAR_121 s t x).
Proof. exact (MK_COMB (@lem4323737 B) (@lem4323734 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4323745 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) : (term82 A B GEN_PVAR_121 s t) = (term83 A B GEN_PVAR_121 s t).
Proof. exact (fun_ext (fun x : A => @lem4323738 A B GEN_PVAR_121 s t x)). Qed.
Lemma lem4323752 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4323753 {A B : Type'} (GEN_PVAR_121 : prod A B) (s : A -> Prop) (t : B -> Prop) : (term84 A B GEN_PVAR_121 s t) = (term85 A B GEN_PVAR_121 s t).
Proof. exact (MK_COMB (@lem4323752 A) (@lem4323745 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4323764 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term86 A B s t) = (term87 A B s t).
Proof. exact (fun_ext (fun GEN_PVAR_121 : prod A B => @lem4323753 A B GEN_PVAR_121 s t)). Qed.
Lemma lem4323775 {A B : Type'} : (@GSPEC (prod A B)) = (@GSPEC (prod A B)).
Proof. exact (eq_refl (@GSPEC (prod A B))). Qed.
Lemma lem4323776 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term69 A B s t) = (term88 A B s t).
Proof. exact (MK_COMB (@lem4323775 A B) (@lem4323764 A B s t)). Qed.
Lemma lem4323787 {A B : Type'} : (@CARD (prod A B)) = (@CARD (prod A B)).
Proof. exact (eq_refl (@CARD (prod A B))). Qed.
Lemma lem4323788 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term93 A B s t) = (term18 A B s t).
Proof. exact (MK_COMB (@lem4323787 A B) (@lem4323776 A B s t)). Qed.
Lemma lem4323799 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4323800 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term94 A B s t) = (term95 A B s t).
Proof. exact (MK_COMB (@lem4323799) (@lem4323788 A B s t)). Qed.
Lemma lem4323811 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term19 A B s t) = (term19 A B s t).
Proof. exact (eq_refl (term19 A B s t)). Qed.
Lemma lem4323812 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term93 A B s t) = (term19 A B s t)) = ((term18 A B s t) = (term19 A B s t)).
Proof. exact (MK_COMB (@lem4323800 A B s t) (@lem4323811 A B s t)). Qed.
Lemma lem4323825 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term68 A B s t) = (term96 A B s t).
Proof. exact (MK_COMB (@lem4323684 A B s t) (@lem4323812 A B s t)). Qed.
Lemma lem4323850 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term26 A B s t) = (term96 A B s t).
Proof. exact (TRANS (@lem4323578 A B s t) (@lem4323825 A B s t)). Qed.
Lemma lem4323851 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term97 A B s t.
Proof. exact (fun h0 : True => @lem4323850 A B s t). Qed.
Lemma lem4323852 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term98 A B s t.
Proof. exact (@lem4323569 A B (term96 A B s t) s t h1 h2). Qed.
Lemma lem4323853 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term8 A B s t) = (term99 A B s t).
Proof. exact (@lem4323852 A B s t h1 h2 (@lem4323851 A B s t)). Qed.
Lemma lem4323855 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem4323856 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term99 A B s t) = (term96 A B s t).
Proof. exact (@lem4323855 (term96 A B s t)). Qed.
Lemma lem4323881 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term8 A B s t) = (term96 A B s t).
Proof. exact (TRANS (@lem4323853 A B s t h1 h2) (@lem4323856 A B s t)). Qed.
Lemma lem4323882 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (q' : Prop) : term100 A B s t q'.
Proof. exact (@lem4323429 A B s t (term96 A B s t) q'). Qed.
Lemma lem4323883 {A B : Type'} (q' : Prop) (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term101 A B s t q'.
Proof. exact (@lem4323882 A B s t q' (@lem4323881 A B s t h1 h2)). Qed.
Lemma lem4323884 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term96 A B s t) : term96 A B s t.
Proof. exact (h1). Qed.
Lemma lem4323892 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term96 A B s t) : (term18 A B s t) = (term19 A B s t).
Proof. exact (proj2 (@lem4323884 A B s t h1)). Qed.
Lemma lem4323893 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term96 A B s t) : (term18 A B s t) = (term19 A B s t).
Proof. exact (@lem4323892 A B s t h1). Qed.
Lemma lem4323894 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4323895 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term96 A B s t) : (term95 A B s t) = (term102 A B s t).
Proof. exact (MK_COMB (@lem4323894) (@lem4323893 A B s t h1)). Qed.
Lemma lem4323896 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term19 A B s t) = (term19 A B s t).
Proof. exact (eq_refl (term19 A B s t)). Qed.
Lemma lem4323897 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term96 A B s t) : ((term18 A B s t) = (term19 A B s t)) = ((term19 A B s t) = (term19 A B s t)).
Proof. exact (MK_COMB (@lem4323895 A B s t h1) (@lem4323896 A B s t)). Qed.
Lemma lem4323899 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4323900 (x : nat) : (x = x) = True.
Proof. exact (@lem4323899 nat x). Qed.
Lemma lem4323901 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : ((term19 A B s t) = (term19 A B s t)) = True.
Proof. exact (@lem4323900 (term19 A B s t)). Qed.
Lemma lem4323902 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term96 A B s t) : ((term18 A B s t) = (term19 A B s t)) = True.
Proof. exact (TRANS (@lem4323897 A B s t h1) (@lem4323901 A B s t)). Qed.
Lemma lem4323903 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term103 A B s t.
Proof. exact (fun h0 : term96 A B s t => @lem4323902 A B s t h0). Qed.
Lemma lem4323904 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term104 A B s t.
Proof. exact (@lem4323883 A B True s t h1 h2). Qed.
Lemma lem4323905 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term105 A B s t) = (term106 A B s t).
Proof. exact (@lem4323904 A B s t h1 h2 (@lem4323903 A B s t)). Qed.
Lemma lem4323907 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4323908 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : (term106 A B s t) = True.
Proof. exact (@lem4323907 (term96 A B s t)). Qed.
Lemma lem4323909 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term105 A B s t) = True.
Proof. exact (TRANS (@lem4323905 A B s t h1 h2) (@lem4323908 A B s t)). Qed.
Lemma lem4323910 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : True = (term105 A B s t).
Proof. exact (SYM (@lem4323909 A B s t h1 h2)). Qed.
Lemma lem4323911 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : term105 A B s t.
Proof. exact (EQ_MP (@lem4323910 A B s t h1 h2) (@lem0)). Qed.
Lemma lem4323912 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term18 A B s t) = (term19 A B s t).
Proof. exact (@lem4323911 A B s t h1 h2 (@lem4323403 A B s t)). Qed.
Lemma lem4323913 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term9 A B s t) : @FINITE B t.
Proof. exact (proj2 (@lem4323404 A B s t h1)). Qed.
Lemma lem4323914 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term9 A B s t) : @FINITE A s.
Proof. exact (proj1 (@lem4323404 A B s t h1)). Qed.
Lemma lem4323915 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (@FINITE B t) = ((term18 A B s t) = (term19 A B s t)).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4323912 A B s t h1 h2) (fun h3 : (term18 A B s t) = (term19 A B s t) => @lem4323405 B t h2)). Qed.
Lemma lem4323916 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term18 A B s t) = (term19 A B s t).
Proof. exact (EQ_MP (@lem4323915 A B s t h1 h2) (@lem4323405 B t h2)). Qed.
Lemma lem4323917 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (@FINITE A s) = ((term18 A B s t) = (term19 A B s t)).
Proof. exact (prop_ext (fun h3 : @FINITE A s => @lem4323916 A B s t h1 h2) (fun h3 : (term18 A B s t) = (term19 A B s t) => @lem4323406 A s h1)). Qed.
Lemma lem4323918 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : @FINITE B t) : (term18 A B s t) = (term19 A B s t).
Proof. exact (EQ_MP (@lem4323917 A B s t h1 h2) (@lem4323406 A s h1)). Qed.
Lemma lem4323919 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term9 A B s t) : (@FINITE B t) = ((term18 A B s t) = (term19 A B s t)).
Proof. exact (prop_ext (fun h3 : @FINITE B t => @lem4323918 A B s t h1 h3) (fun h3 : (term18 A B s t) = (term19 A B s t) => @lem4323913 A B s t h2)). Qed.
Lemma lem4323920 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : @FINITE A s) (h2 : term9 A B s t) : (term18 A B s t) = (term19 A B s t).
Proof. exact (EQ_MP (@lem4323919 A B s t h1 h2) (@lem4323913 A B s t h2)). Qed.
Lemma lem4323921 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term9 A B s t) : (@FINITE A s) = ((term18 A B s t) = (term19 A B s t)).
Proof. exact (prop_ext (fun h2 : @FINITE A s => @lem4323920 A B s t h2 h1) (fun h2 : (term18 A B s t) = (term19 A B s t) => @lem4323914 A B s t h1)). Qed.
Lemma lem4323922 {A B : Type'} (s : A -> Prop) (t : B -> Prop) (h1 : term9 A B s t) : (term18 A B s t) = (term19 A B s t).
Proof. exact (EQ_MP (@lem4323921 A B s t h1) (@lem4323914 A B s t h1)). Qed.
Lemma lem4323923 {A B : Type'} (s : A -> Prop) (t : B -> Prop) : term107 A B s t.
Proof. exact (fun h0 : term9 A B s t => @lem4323922 A B s t h0). Qed.
Lemma lem4323928 {A B : Type'} (s : A -> Prop) : term108 A B s.
Proof. exact (fun t : B -> Prop => @lem4323923 A B s t). Qed.
Lemma lem4323933 {A B : Type'} : term109 A B.
Proof. exact (fun s : A -> Prop => @lem4323928 A B s). Qed.
