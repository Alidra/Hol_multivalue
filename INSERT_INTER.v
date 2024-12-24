Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INSERT_INTER_term_abbrevs.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm13473_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17646_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211692_spec.
Require Import thm3211693_spec.
Require Import thm3211710_spec.
Require Import thm3211711_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Lemma lem3282380 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (_476 : type686 A) (_477 : A -> Prop) : (term0 A _476 _475 _474 _477) = (term1 A _474 _475 _476 _477).
Proof. exact (@lem13473 (A -> Prop) _474 _475 _476 _477). Qed.
Lemma lem3282381 {A : Type'} (_474 : A -> Prop) (_475 : Prop) (x : A) (s : A -> Prop) (t : A -> Prop) (_477 : A -> Prop) : (term2 A x s t _475 _474 _477) = (term3 A _474 _475 x s t _477).
Proof. exact (@lem3282380 A _474 _475 (term4 A x s t) _477). Qed.
Lemma lem3282382 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term5 A x s t) = (term6 A x s t).
Proof. exact (@lem3282381 A (term7 A x s t) (@IN A x t) x s t (@INTER A s t)). Qed.
Lemma lem3282383 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term8 A x s t) = ((term9 A x s t) = (@INTER A s t)).
Proof. exact (eq_refl (term8 A x s t)). Qed.
Lemma lem3282384 {A : Type'} (x : A) (t : A -> Prop) : (term10 A x t) = (term10 A x t).
Proof. exact (eq_refl (term10 A x t)). Qed.
Lemma lem3282385 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term11 A x s t) = (term12 A x s t).
Proof. exact (MK_COMB (@lem3282384 A x t) (@lem3282383 A x s t)). Qed.
Lemma lem3282386 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term13 A x s t) = ((term9 A x s t) = (term7 A x s t)).
Proof. exact (eq_refl (term13 A x s t)). Qed.
Lemma lem3282387 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (term14 A x t).
Proof. exact (eq_refl (term14 A x t)). Qed.
Lemma lem3282388 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term15 A x s t) = (term16 A x s t).
Proof. exact (MK_COMB (@lem3282387 A x t) (@lem3282386 A x s t)). Qed.
Lemma lem3282389 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3282390 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term17 A x s t) = (term18 A x s t).
Proof. exact (MK_COMB (@lem3282389) (@lem3282388 A x s t)). Qed.
Lemma lem3282391 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term6 A x s t) = (term19 A x s t).
Proof. exact (MK_COMB (@lem3282390 A x s t) (@lem3282385 A x s t)). Qed.
Lemma lem3282392 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term5 A x s t) = ((term9 A x s t) = (term20 A x s t)).
Proof. exact (eq_refl (term5 A x s t)). Qed.
Lemma lem3282393 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3282394 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term21 A x s t) = (term22 A x s t).
Proof. exact (MK_COMB (@lem3282393) (@lem3282392 A x s t)). Qed.
Lemma lem3282395 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term5 A x s t) = (term6 A x s t)) = (((term9 A x s t) = (term20 A x s t)) = (term19 A x s t)).
Proof. exact (MK_COMB (@lem3282394 A x s t) (@lem3282391 A x s t)). Qed.
Lemma lem3282396 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (term20 A x s t)) = (term19 A x s t).
Proof. exact (EQ_MP (@lem3282395 A x s t) (@lem3282382 A x s t)). Qed.
Lemma lem3282397 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term19 A x s t) = ((term9 A x s t) = (term20 A x s t)).
Proof. exact (SYM (@lem3282396 A x s t)). Qed.
Lemma lem3282398 {A : Type'} (x : A) (t : A -> Prop) (h1 : @IN A x t) : @IN A x t.
Proof. exact (h1). Qed.
Lemma lem3282415 {A : Type'} (x : A) (t : A -> Prop) (h1 : term23 A x t) : term23 A x t.
Proof. exact (h1). Qed.
Lemma lem3282437 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3282438 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3282437 A s t). Qed.
Lemma lem3282439 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (term7 A x s t)) = (term25 A x s t).
Proof. exact (@lem3282438 A (term9 A x s t) (term7 A x s t)). Qed.
Lemma lem3282448 {A : Type'} (x : A) (t : A -> Prop) : (term14 A x t) = (term14 A x t).
Proof. exact (eq_refl (term14 A x t)). Qed.
Lemma lem3282449 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term16 A x s t) = (term26 A x s t).
Proof. exact (MK_COMB (@lem3282448 A x t) (@lem3282439 A x s t)). Qed.
Lemma lem3282452 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term16 A x s t).
Proof. exact (SYM (@lem3282449 A x s t)). Qed.
Lemma lem3282456 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3282457 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3282456 A P x). Qed.
Lemma lem3282458 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3282457 A t x). Qed.
Lemma lem3282459 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3282460 {A : Type'} (t : A -> Prop) (x : A) : (term14 A x t) = (term27 A t x).
Proof. exact (MK_COMB (@lem3282459) (@lem3282458 A t x)). Qed.
Lemma lem3282468 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3282469 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3282468 A s x t). Qed.
Lemma lem3282470 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term30 A x' x s t) = (term31 A x s x' t).
Proof. exact (@lem3282469 A (@INSERT A x s) x' t). Qed.
Lemma lem3282474 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3282475 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3282474 A y x s). Qed.
Lemma lem3282476 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term32 A x' x s) = (term33 A x x' s).
Proof. exact (@lem3282475 A x x' s). Qed.
Lemma lem3282482 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3282483 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3282482 A P x). Qed.
Lemma lem3282484 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3282483 A s x'). Qed.
Lemma lem3282485 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3282486 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term33 A x x' s) = (term35 A x s x').
Proof. exact (MK_COMB (@lem3282485 A x' x) (@lem3282484 A s x')). Qed.
Lemma lem3282489 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x' x s) = (term35 A x s x').
Proof. exact (TRANS (@lem3282476 A x x' s) (@lem3282486 A x s x')). Qed.
Lemma lem3282490 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3282491 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x' x s) = (term37 A x s x').
Proof. exact (MK_COMB (@lem3282490) (@lem3282489 A x s x')). Qed.
Lemma lem3282493 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3282494 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3282493 A P x). Qed.
Lemma lem3282495 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3282494 A t x'). Qed.
Lemma lem3282496 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term31 A x s x' t) = (term38 A x s t x').
Proof. exact (MK_COMB (@lem3282491 A x s x') (@lem3282495 A t x')). Qed.
Lemma lem3282499 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term30 A x' x s t) = (term38 A x s t x').
Proof. exact (TRANS (@lem3282470 A x s x' t) (@lem3282496 A x s t x')). Qed.
Lemma lem3282500 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3282501 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term39 A x' x s t) = (term40 A x s t x').
Proof. exact (MK_COMB (@lem3282500) (@lem3282499 A x s t x')). Qed.
Lemma lem3282503 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3282504 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3282503 A y x s). Qed.
Lemma lem3282505 {A : Type'} (x : A) (x' : A) (s : A -> Prop) (t : A -> Prop) : (term41 A x' x s t) = (term42 A x x' s t).
Proof. exact (@lem3282504 A x x' (@INTER A s t)). Qed.
Lemma lem3282511 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3282512 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3282511 A s x t). Qed.
Lemma lem3282513 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term28 A x' s t) = (term29 A s x' t).
Proof. exact (@lem3282512 A s x' t). Qed.
Lemma lem3282517 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3282518 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3282517 A P x). Qed.
Lemma lem3282519 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3282518 A s x'). Qed.
Lemma lem3282520 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3282521 {A : Type'} (s : A -> Prop) (x' : A) : (term43 A x' s) = (term44 A s x').
Proof. exact (MK_COMB (@lem3282520) (@lem3282519 A s x')). Qed.
Lemma lem3282523 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3282524 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3282523 A P x). Qed.
Lemma lem3282525 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3282524 A t x'). Qed.
Lemma lem3282526 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term29 A s x' t) = (term45 A s t x').
Proof. exact (MK_COMB (@lem3282521 A s x') (@lem3282525 A t x')). Qed.
Lemma lem3282529 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term28 A x' s t) = (term45 A s t x').
Proof. exact (TRANS (@lem3282513 A s x' t) (@lem3282526 A s t x')). Qed.
Lemma lem3282530 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3282531 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term42 A x x' s t) = (term46 A x s t x').
Proof. exact (MK_COMB (@lem3282530 A x' x) (@lem3282529 A s t x')). Qed.
Lemma lem3282534 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term41 A x' x s t) = (term46 A x s t x').
Proof. exact (TRANS (@lem3282505 A x x' s t) (@lem3282531 A x s t x')). Qed.
Lemma lem3282535 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term30 A x' x s t) = (term41 A x' x s t)) = ((term38 A x s t x') = (term46 A x s t x')).
Proof. exact (MK_COMB (@lem3282501 A x s t x') (@lem3282534 A x s t x')). Qed.
Lemma lem3282538 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term47 A x s t) = (term48 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3282535 A x s t x')). Qed.
Lemma lem3282539 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3282540 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term25 A x s t) = (term49 A x s t).
Proof. exact (MK_COMB (@lem3282539 A) (@lem3282538 A x s t)). Qed.
Lemma lem3282545 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term26 A x s t) = (term50 A x s t).
Proof. exact (MK_COMB (@lem3282460 A t x) (@lem3282540 A x s t)). Qed.
Lemma lem3282548 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term50 A x s t) = (term26 A x s t).
Proof. exact (SYM (@lem3282545 A x s t)). Qed.
Lemma lem3282550 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3282551 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term50 A x s t) = (term52 A x s t).
Proof. exact (@lem3282550 (term50 A x s t)). Qed.
Lemma lem3282552 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term52 A x s t) = (term50 A x s t).
Proof. exact (SYM (@lem3282551 A x s t)). Qed.
Lemma lem3282553 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A x s t) : term53 A x s t.
Proof. exact (h1). Qed.
Lemma lem3282556 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) : term52 A x s t.
Proof. exact (h1). Qed.
Lemma lem3282557 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term54 A x s t.
Proof. exact (fun h0 : term52 A x s t => @lem3282556 A x s t h0). Qed.
Lemma lem3282558 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term54 A x s t) : term54 A x s t.
Proof. exact (h1). Qed.
Lemma lem3282559 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) : term52 A x s t.
Proof. exact (h1). Qed.
Lemma lem3282560 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) (h2 : term54 A x s t) : term52 A x s t.
Proof. exact (@lem3282558 A x s t h2 (@lem3282559 A x s t h1)). Qed.
Lemma lem3282561 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) : term55 A x s t.
Proof. exact (fun h0 : term54 A x s t => @lem3282560 A x s t h1 h0). Qed.
Lemma lem3282562 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term54 A x s t) : term54 A x s t.
Proof. exact (h1). Qed.
Lemma lem3282563 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term52 A x s t) (h2 : term54 A x s t) : term52 A x s t.
Proof. exact (@lem3282561 A x s t h1 (@lem3282562 A x s t h2)). Qed.
Lemma lem3282564 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term54 A x s t) : term54 A x s t.
Proof. exact (fun h0 : term52 A x s t => @lem3282563 A x s t h0 h1). Qed.
Lemma lem3282565 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term56 A x s t.
Proof. exact (fun h0 : term54 A x s t => @lem3282564 A x s t h0). Qed.
Lemma lem3282568 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term54 A x s t.
Proof. exact (@lem3282565 A x s t (@lem3282557 A x s t)). Qed.
Lemma lem3282569 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term54 A x s t.
Proof. exact (@lem3282568 A x s t). Qed.
Lemma lem3282583 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3282584 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term52 A x s t) = (term57 A x s t).
Proof. exact (@lem3282583 (term53 A x s t)). Qed.
Lemma lem3282586 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3282587 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term57 A x s t) = (term50 A x s t).
Proof. exact (@lem3282586 (term50 A x s t)). Qed.
Lemma lem3282590 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term52 A x s t) = (term50 A x s t).
Proof. exact (TRANS (@lem3282584 A x s t) (@lem3282587 A x s t)). Qed.
Lemma lem3282603 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term59 A s t) = (term60 A s t).
Proof. exact (fun_ext (fun x : A => @lem3282590 A x s t)). Qed.
Lemma lem3282604 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3282605 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term61 A s t) = (term62 A s t).
Proof. exact (MK_COMB (@lem3282604 A) (@lem3282603 A s t)). Qed.
Lemma lem3282610 {A : Type'} (t : A -> Prop) : (term63 A t) = (term64 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3282605 A s t)). Qed.
Lemma lem3282611 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3282612 {A : Type'} (t : A -> Prop) : (term65 A t) = (term66 A t).
Proof. exact (MK_COMB (@lem3282611 A) (@lem3282610 A t)). Qed.
Lemma lem3282617 {A : Type'} : (term67 A) = (term68 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3282612 A t)). Qed.
Lemma lem3282618 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3282627 {A : Type'} : (term69 A) = (term70 A).
Proof. exact (MK_COMB (@lem3282618 A) (@lem3282617 A)). Qed.
Lemma lem3282648 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term46 A x s t x')) = ((term38 A x s t x') = (term46 A x s t x')).
Proof. exact (eq_refl ((term38 A x s t x') = (term46 A x s t x'))). Qed.
Lemma lem3282649 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term48 A x s t) = (term48 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3282648 A x s t x')). Qed.
Lemma lem3282650 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3282651 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term49 A x s t) = (term49 A x s t).
Proof. exact (MK_COMB (@lem3282650 A) (@lem3282649 A x s t)). Qed.
Lemma lem3282654 {A : Type'} (t : A -> Prop) (x : A) : (term27 A t x) = (term27 A t x).
Proof. exact (eq_refl (term27 A t x)). Qed.
Lemma lem3282655 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term50 A x s t) = (term50 A x s t).
Proof. exact (MK_COMB (@lem3282654 A t x) (@lem3282651 A x s t)). Qed.
Lemma lem3282656 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term60 A s t) = (term60 A s t).
Proof. exact (fun_ext (fun x : A => @lem3282655 A x s t)). Qed.
Lemma lem3282657 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3282658 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term62 A s t) = (term62 A s t).
Proof. exact (MK_COMB (@lem3282657 A) (@lem3282656 A s t)). Qed.
Lemma lem3282659 {A : Type'} (t : A -> Prop) : (term64 A t) = (term64 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3282658 A s t)). Qed.
Lemma lem3282660 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3282661 {A : Type'} (t : A -> Prop) : (term66 A t) = (term66 A t).
Proof. exact (MK_COMB (@lem3282660 A) (@lem3282659 A t)). Qed.
Lemma lem3282662 {A : Type'} : (term68 A) = (term68 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3282661 A t)). Qed.
Lemma lem3282663 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3282664 {A : Type'} : (term70 A) = (term70 A).
Proof. exact (MK_COMB (@lem3282663 A) (@lem3282662 A)). Qed.
Lemma lem3282701 {A : Type'} : (term69 A) = (term70 A).
Proof. exact (TRANS (@lem3282627 A) (@lem3282664 A)). Qed.
Lemma lem3282702 {A : Type'} : (term70 A) = (term69 A).
Proof. exact (SYM (@lem3282701 A)). Qed.
Lemma lem3282705 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3282706 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term46 A x s t x')) = (term71 A x s t x').
Proof. exact (@lem3282705 ((term38 A x s t x') = (term46 A x s t x'))). Qed.
Lemma lem3282707 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term71 A x s t x') = ((term38 A x s t x') = (term46 A x s t x')).
Proof. exact (SYM (@lem3282706 A x s t x')). Qed.
Lemma lem3282708 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s t x') : term72 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3282714 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3282723 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term73 A x s x') = (term74 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3282727 {A : Type'} (t : A -> Prop) (x' : A) : (term75 A t x') = (term75 A t x').
Proof. exact (eq_refl (term75 A t x')). Qed.
Lemma lem3282729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3282730 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term76 A x s x') = (term77 A x s x').
Proof. exact (MK_COMB (@lem3282729) (@lem3282723 A x s x')). Qed.
Lemma lem3282731 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A x s t x') = (term79 A x s t x').
Proof. exact (MK_COMB (@lem3282730 A x s x') (@lem3282727 A t x')). Qed.
Lemma lem3282732 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A x s t x') = (term78 A x s t x').
Proof. exact (@lem17045 (term35 A x s x') (t x')). Qed.
Lemma lem3282733 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A x s t x') = (term79 A x s t x').
Proof. exact (TRANS (@lem3282732 A x s t x') (@lem3282731 A x s t x')). Qed.
Lemma lem3282747 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term81 A s t x') = (term82 A s t x').
Proof. exact (@lem17045 (s x') (t x')). Qed.
Lemma lem3282752 {A : Type'} (x' : A) (x : A) : (term83 A x' x) = (term83 A x' x).
Proof. exact (eq_refl (term83 A x' x)). Qed.
Lemma lem3282753 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term84 A x s t x') = (term85 A x s t x').
Proof. exact (MK_COMB (@lem3282752 A x' x) (@lem3282747 A s t x')). Qed.
Lemma lem3282754 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term86 A x s t x') = (term84 A x s t x').
Proof. exact (@lem17160 (x' = x) (term45 A s t x')). Qed.
Lemma lem3282755 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term86 A x s t x') = (term85 A x s t x').
Proof. exact (TRANS (@lem3282754 A x s t x') (@lem3282753 A x s t x')). Qed.
Lemma lem3282758 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term46 A x s t x') = (term46 A x s t x').
Proof. exact (eq_refl (term46 A x s t x')). Qed.
Lemma lem3282759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3282760 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term87 A x s t x') = (term88 A x s t x').
Proof. exact (MK_COMB (@lem3282759) (@lem3282733 A x s t x')). Qed.
Lemma lem3282761 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term89 A x s t x') = (term90 A x s t x').
Proof. exact (MK_COMB (@lem3282760 A x s t x') (@lem3282758 A x s t x')). Qed.
Lemma lem3282763 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term91 A x s t x') = (term91 A x s t x').
Proof. exact (eq_refl (term91 A x s t x')). Qed.
Lemma lem3282764 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term92 A x s t x') = (term93 A x s t x').
Proof. exact (MK_COMB (@lem3282763 A x s t x') (@lem3282755 A x s t x')). Qed.
Lemma lem3282765 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3282766 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term94 A x s t x') = (term95 A x s t x').
Proof. exact (MK_COMB (@lem3282765) (@lem3282764 A x s t x')). Qed.
Lemma lem3282767 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term96 A x s t x') = (term97 A x s t x').
Proof. exact (MK_COMB (@lem3282766 A x s t x') (@lem3282761 A x s t x')). Qed.
Lemma lem3282768 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term72 A x s t x') = (term96 A x s t x').
Proof. exact (@lem17646 (term38 A x s t x') (term46 A x s t x')). Qed.
Lemma lem3282773 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term72 A x s t x') = (term97 A x s t x').
Proof. exact (TRANS (@lem3282768 A x s t x') (@lem3282767 A x s t x')). Qed.
Lemma lem3282778 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3282868 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term72 A x s t x') : term97 A x s t x'.
Proof. exact (EQ_MP (@lem3282773 A x s t x') (@lem3282708 A x s t x' h1)). Qed.
Lemma lem3282869 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : term93 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3282870 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term90 A x s t x') : term90 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3282871 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : term85 A x s t x'.
Proof. exact (proj2 (@lem3282869 A x s t x' h1)). Qed.
Lemma lem3282872 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : term38 A x s t x'.
Proof. exact (proj1 (@lem3282869 A x s t x' h1)). Qed.
Lemma lem3282873 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : term82 A s t x'.
Proof. exact (proj2 (@lem3282871 A x s t x' h1)). Qed.
Lemma lem3282876 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : term35 A x s x'.
Proof. exact (proj1 (@lem3282872 A x s t x' h1)). Qed.
Lemma lem3282883 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term90 A x s t x') : term46 A x s t x'.
Proof. exact (proj2 (@lem3282870 A x s t x' h1)). Qed.
Lemma lem3282884 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term90 A x s t x') : term79 A x s t x'.
Proof. exact (proj1 (@lem3282870 A x s t x' h1)). Qed.
Lemma lem3282886 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') : term45 A s t x'.
Proof. exact (h1). Qed.
Lemma lem3282887 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3282893 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3282912 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3282932 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3282936 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3282952 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3282956 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') : term75 A s x'.
Proof. exact (h1). Qed.
Lemma lem3282976 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3282984 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3282996 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3283000 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3283004 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3283040 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3283044 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : term98 A x' x.
Proof. exact (proj1 (@lem3282871 A x s t x' h1)). Qed.
Lemma lem3283048 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3283056 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : t x'.
Proof. exact (proj2 (@lem3282872 A x s t x' h1)). Qed.
Lemma lem3283058 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3283060 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3283068 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3283070 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') : term75 A s x'.
Proof. exact (h1). Qed.
Lemma lem3283080 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3283084 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3283086 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term98 A x' x.
Proof. exact (proj1 (@lem3282887 A x s x' h1)). Qed.
Lemma lem3283090 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3283092 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3283094 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3283104 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term75 A s x'.
Proof. exact (proj2 (@lem3282893 A x s x' h1)). Qed.
Lemma lem3283112 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3283141 {A : Type'} (x : A) : (term99 A x) = (term99 A x).
Proof. exact (eq_refl (term99 A x)). Qed.
Lemma lem3283142 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term100 A x x') = (term101 A x).
Proof. exact (MK_COMB (@lem3283141 A x) (@lem3283048 A x' x h1)). Qed.
Lemma lem3283143 {A : Type'} (x : A) : (term101 A x) = (term102 A x).
Proof. exact (eq_refl (term101 A x)). Qed.
Lemma lem3283144 {A : Type'} (x : A) (x' : A) : (term103 A x x') = (term103 A x x').
Proof. exact (eq_refl (term103 A x x')). Qed.
Lemma lem3283145 {A : Type'} (x' : A) (x : A) : ((term100 A x x') = (term101 A x)) = ((term100 A x x') = (term102 A x)).
Proof. exact (MK_COMB (@lem3283144 A x x') (@lem3283143 A x)). Qed.
Lemma lem3283146 {A : Type'} (x' : A) (x : A) : (term100 A x x') = (term98 A x' x).
Proof. exact (eq_refl (term100 A x x')). Qed.
Lemma lem3283147 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3283148 {A : Type'} (x' : A) (x : A) : (term103 A x x') = (term104 A x' x).
Proof. exact (MK_COMB (@lem3283147) (@lem3283146 A x' x)). Qed.
Lemma lem3283149 {A : Type'} (x : A) : (term102 A x) = (term102 A x).
Proof. exact (eq_refl (term102 A x)). Qed.
Lemma lem3283150 {A : Type'} (x' : A) (x : A) : ((term100 A x x') = (term102 A x)) = ((term98 A x' x) = (term102 A x)).
Proof. exact (MK_COMB (@lem3283148 A x' x) (@lem3283149 A x)). Qed.
Lemma lem3283151 {A : Type'} (x' : A) (x : A) : ((term100 A x x') = (term101 A x)) = ((term98 A x' x) = (term102 A x)).
Proof. exact (TRANS (@lem3283145 A x' x) (@lem3283150 A x' x)). Qed.
Lemma lem3283152 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term98 A x' x) = (term102 A x).
Proof. exact (EQ_MP (@lem3283151 A x' x) (@lem3283142 A x' x h1)). Qed.
Lemma lem3283153 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : term102 A x.
Proof. exact (EQ_MP (@lem3283152 A x' x h2) (@lem3283044 A x s t x' h1)). Qed.
Lemma lem3283221 {A : Type'} (t : A -> Prop) : (term105 A t) = (term105 A t).
Proof. exact (eq_refl (term105 A t)). Qed.
Lemma lem3283222 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term106 A t x') = (term106 A t x).
Proof. exact (MK_COMB (@lem3283221 A t) (@lem3283058 A x' x h1)). Qed.
Lemma lem3283223 {A : Type'} (t : A -> Prop) (x : A) : (term106 A t x) = (t x).
Proof. exact (eq_refl (term106 A t x)). Qed.
Lemma lem3283224 {A : Type'} (t : A -> Prop) (x' : A) : (term107 A t x') = (term107 A t x').
Proof. exact (eq_refl (term107 A t x')). Qed.
Lemma lem3283225 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (term106 A t x)) = ((term106 A t x') = (t x)).
Proof. exact (MK_COMB (@lem3283224 A t x') (@lem3283223 A t x)). Qed.
Lemma lem3283226 {A : Type'} (t : A -> Prop) (x' : A) : (term106 A t x') = (t x').
Proof. exact (eq_refl (term106 A t x')). Qed.
Lemma lem3283227 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3283228 {A : Type'} (t : A -> Prop) (x' : A) : (term107 A t x') = (term108 A t x').
Proof. exact (MK_COMB (@lem3283227) (@lem3283226 A t x')). Qed.
Lemma lem3283229 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3283230 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (t x)) = ((t x') = (t x)).
Proof. exact (MK_COMB (@lem3283228 A t x') (@lem3283229 A t x)). Qed.
Lemma lem3283231 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (term106 A t x)) = ((t x') = (t x)).
Proof. exact (TRANS (@lem3283225 A x' t x) (@lem3283230 A x' t x)). Qed.
Lemma lem3283232 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (EQ_MP (@lem3283231 A x' t x) (@lem3283222 A t x' x h1)). Qed.
Lemma lem3283234 {A : Type'} (t : A -> Prop) : (term109 A t) = (term109 A t).
Proof. exact (eq_refl (term109 A t)). Qed.
Lemma lem3283235 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term110 A t x') = (term110 A t x).
Proof. exact (MK_COMB (@lem3283234 A t) (@lem3283058 A x' x h1)). Qed.
Lemma lem3283236 {A : Type'} (t : A -> Prop) (x : A) : (term110 A t x) = (term75 A t x).
Proof. exact (eq_refl (term110 A t x)). Qed.
Lemma lem3283237 {A : Type'} (t : A -> Prop) (x' : A) : (term111 A t x') = (term111 A t x').
Proof. exact (eq_refl (term111 A t x')). Qed.
Lemma lem3283238 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term110 A t x)) = ((term110 A t x') = (term75 A t x)).
Proof. exact (MK_COMB (@lem3283237 A t x') (@lem3283236 A t x)). Qed.
Lemma lem3283239 {A : Type'} (t : A -> Prop) (x' : A) : (term110 A t x') = (term75 A t x').
Proof. exact (eq_refl (term110 A t x')). Qed.
Lemma lem3283240 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3283241 {A : Type'} (t : A -> Prop) (x' : A) : (term111 A t x') = (term112 A t x').
Proof. exact (MK_COMB (@lem3283240) (@lem3283239 A t x')). Qed.
Lemma lem3283242 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term75 A t x).
Proof. exact (eq_refl (term75 A t x)). Qed.
Lemma lem3283243 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term75 A t x)) = ((term75 A t x') = (term75 A t x)).
Proof. exact (MK_COMB (@lem3283241 A t x') (@lem3283242 A t x)). Qed.
Lemma lem3283244 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term110 A t x)) = ((term75 A t x') = (term75 A t x)).
Proof. exact (TRANS (@lem3283238 A x' t x) (@lem3283243 A x' t x)). Qed.
Lemma lem3283245 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term75 A t x') = (term75 A t x).
Proof. exact (EQ_MP (@lem3283244 A x' t x) (@lem3283235 A t x' x h1)). Qed.
Lemma lem3283246 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : x' = x) : term75 A t x.
Proof. exact (EQ_MP (@lem3283245 A t x' x h2) (@lem3283060 A t x' h1)). Qed.
Lemma lem3283275 {A : Type'} (x : A) : (term99 A x) = (term99 A x).
Proof. exact (eq_refl (term99 A x)). Qed.
Lemma lem3283276 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term100 A x x') = (term101 A x).
Proof. exact (MK_COMB (@lem3283275 A x) (@lem3283084 A x' x h1)). Qed.
Lemma lem3283277 {A : Type'} (x : A) : (term101 A x) = (term102 A x).
Proof. exact (eq_refl (term101 A x)). Qed.
Lemma lem3283278 {A : Type'} (x : A) (x' : A) : (term103 A x x') = (term103 A x x').
Proof. exact (eq_refl (term103 A x x')). Qed.
Lemma lem3283279 {A : Type'} (x' : A) (x : A) : ((term100 A x x') = (term101 A x)) = ((term100 A x x') = (term102 A x)).
Proof. exact (MK_COMB (@lem3283278 A x x') (@lem3283277 A x)). Qed.
Lemma lem3283280 {A : Type'} (x' : A) (x : A) : (term100 A x x') = (term98 A x' x).
Proof. exact (eq_refl (term100 A x x')). Qed.
Lemma lem3283281 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3283282 {A : Type'} (x' : A) (x : A) : (term103 A x x') = (term104 A x' x).
Proof. exact (MK_COMB (@lem3283281) (@lem3283280 A x' x)). Qed.
Lemma lem3283283 {A : Type'} (x : A) : (term102 A x) = (term102 A x).
Proof. exact (eq_refl (term102 A x)). Qed.
Lemma lem3283284 {A : Type'} (x' : A) (x : A) : ((term100 A x x') = (term102 A x)) = ((term98 A x' x) = (term102 A x)).
Proof. exact (MK_COMB (@lem3283282 A x' x) (@lem3283283 A x)). Qed.
Lemma lem3283285 {A : Type'} (x' : A) (x : A) : ((term100 A x x') = (term101 A x)) = ((term98 A x' x) = (term102 A x)).
Proof. exact (TRANS (@lem3283279 A x' x) (@lem3283284 A x' x)). Qed.
Lemma lem3283286 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : (term98 A x' x) = (term102 A x).
Proof. exact (EQ_MP (@lem3283285 A x' x) (@lem3283276 A x' x h1)). Qed.
Lemma lem3283287 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : term102 A x.
Proof. exact (EQ_MP (@lem3283286 A x' x h2) (@lem3283086 A x s x' h1)). Qed.
Lemma lem3283328 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3283329 {A : Type'} (t : A -> Prop) : (term109 A t) = (term109 A t).
Proof. exact (eq_refl (term109 A t)). Qed.
Lemma lem3283330 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term110 A t x') = (term110 A t x).
Proof. exact (MK_COMB (@lem3283329 A t) (@lem3283092 A x' x h1)). Qed.
Lemma lem3283331 {A : Type'} (t : A -> Prop) (x : A) : (term110 A t x) = (term75 A t x).
Proof. exact (eq_refl (term110 A t x)). Qed.
Lemma lem3283332 {A : Type'} (t : A -> Prop) (x' : A) : (term111 A t x') = (term111 A t x').
Proof. exact (eq_refl (term111 A t x')). Qed.
Lemma lem3283333 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term110 A t x)) = ((term110 A t x') = (term75 A t x)).
Proof. exact (MK_COMB (@lem3283332 A t x') (@lem3283331 A t x)). Qed.
Lemma lem3283334 {A : Type'} (t : A -> Prop) (x' : A) : (term110 A t x') = (term75 A t x').
Proof. exact (eq_refl (term110 A t x')). Qed.
Lemma lem3283335 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3283336 {A : Type'} (t : A -> Prop) (x' : A) : (term111 A t x') = (term112 A t x').
Proof. exact (MK_COMB (@lem3283335) (@lem3283334 A t x')). Qed.
Lemma lem3283337 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term75 A t x).
Proof. exact (eq_refl (term75 A t x)). Qed.
Lemma lem3283338 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term75 A t x)) = ((term75 A t x') = (term75 A t x)).
Proof. exact (MK_COMB (@lem3283336 A t x') (@lem3283337 A t x)). Qed.
Lemma lem3283339 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term110 A t x)) = ((term75 A t x') = (term75 A t x)).
Proof. exact (TRANS (@lem3283333 A x' t x) (@lem3283338 A x' t x)). Qed.
Lemma lem3283340 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term75 A t x') = (term75 A t x).
Proof. exact (EQ_MP (@lem3283339 A x' t x) (@lem3283330 A t x' x h1)). Qed.
Lemma lem3283341 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : x' = x) : term75 A t x.
Proof. exact (EQ_MP (@lem3283340 A t x' x h2) (@lem3283094 A t x' h1)). Qed.
Lemma lem3283369 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3283370 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3283369 A x). Qed.
Lemma lem3283371 {A : Type'} (x : A) : term113 A x.
Proof. exact (fun h0 : term102 A x => @lem3283370 A x). Qed.
Lemma lem3283373 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283374 {A : Type'} (x : A) : (term113 A x) = (x = x).
Proof. exact (@lem3283373 (x = x)). Qed.
Lemma lem3283375 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3283374 A x) (@lem3283371 A x)). Qed.
Lemma lem3283378 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283380 {A : Type'} (x : A) : (term102 A x) = (term115 A x).
Proof. exact (@lem3283378 (x = x)). Qed.
Lemma lem3283383 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : term115 A x.
Proof. exact (EQ_MP (@lem3283380 A x) (@lem3283153 A s t x' x h1 h2)). Qed.
Lemma lem3283386 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : False.
Proof. exact (@lem3283383 A s t x' x h1 h2 (@lem3283375 A x)). Qed.
Lemma lem3283387 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : term116.
Proof. exact (fun h0 : ~ False => @lem3283386 A s t x' x h1 h2). Qed.
Lemma lem3283389 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283390 : term116 = False.
Proof. exact (@lem3283389 False). Qed.
Lemma lem3283407 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3283232 A t x' x h2) (@lem3283056 A x s t x' h1)). Qed.
Lemma lem3283408 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : term117 A t x.
Proof. exact (fun h0 : term75 A t x => @lem3283407 A s t x' x h1 h2). Qed.
Lemma lem3283410 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283411 {A : Type'} (t : A -> Prop) (x : A) : (term117 A t x) = (t x).
Proof. exact (@lem3283410 (t x)). Qed.
Lemma lem3283412 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3283411 A t x) (@lem3283408 A s t x' x h1 h2)). Qed.
Lemma lem3283415 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283417 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term118 A t x).
Proof. exact (@lem3283415 (t x)). Qed.
Lemma lem3283420 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : x' = x) : term118 A t x.
Proof. exact (EQ_MP (@lem3283417 A t x) (@lem3283246 A t x' x h1 h2)). Qed.
Lemma lem3283423 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (@lem3283420 A t x' x h1 h3 (@lem3283412 A s t x' x h2 h3)). Qed.
Lemma lem3283424 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : term116.
Proof. exact (fun h0 : ~ False => @lem3283423 A s t x' x h1 h2 h3). Qed.
Lemma lem3283426 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283427 : term116 = False.
Proof. exact (@lem3283426 False). Qed.
Lemma lem3283456 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3283457 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term117 A s x'.
Proof. exact (fun h0 : term75 A s x' => @lem3283456 A s x' h1). Qed.
Lemma lem3283459 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283460 {A : Type'} (s : A -> Prop) (x' : A) : (term117 A s x') = (s x').
Proof. exact (@lem3283459 (s x')). Qed.
Lemma lem3283461 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3283460 A s x') (@lem3283457 A s x' h1)). Qed.
Lemma lem3283464 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283466 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (term118 A s x').
Proof. exact (@lem3283464 (s x')). Qed.
Lemma lem3283469 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') : term118 A s x'.
Proof. exact (EQ_MP (@lem3283466 A s x') (@lem3283070 A s x' h1)). Qed.
Lemma lem3283472 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (@lem3283469 A s x' h1 (@lem3283461 A s x' h2)). Qed.
Lemma lem3283473 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : term116.
Proof. exact (fun h0 : ~ False => @lem3283472 A s x' h1 h2). Qed.
Lemma lem3283475 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283476 : term116 = False.
Proof. exact (@lem3283475 False). Qed.
Lemma lem3283477 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3283476) (@lem3283473 A s x' h1 h2)). Qed.
Lemma lem3283505 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : t x'.
Proof. exact (proj2 (@lem3282872 A x s t x' h1)). Qed.
Lemma lem3283506 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : term117 A t x'.
Proof. exact (fun h0 : term75 A t x' => @lem3283505 A x s t x' h1). Qed.
Lemma lem3283508 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283509 {A : Type'} (t : A -> Prop) (x' : A) : (term117 A t x') = (t x').
Proof. exact (@lem3283508 (t x')). Qed.
Lemma lem3283510 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : t x'.
Proof. exact (EQ_MP (@lem3283509 A t x') (@lem3283506 A x s t x' h1)). Qed.
Lemma lem3283513 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283515 {A : Type'} (t : A -> Prop) (x' : A) : (term75 A t x') = (term118 A t x').
Proof. exact (@lem3283513 (t x')). Qed.
Lemma lem3283518 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term118 A t x'.
Proof. exact (EQ_MP (@lem3283515 A t x') (@lem3283080 A t x' h1)). Qed.
Lemma lem3283521 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : False.
Proof. exact (@lem3283518 A t x' h1 (@lem3283510 A x s t x' h2)). Qed.
Lemma lem3283522 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : term116.
Proof. exact (fun h0 : ~ False => @lem3283521 A x s t x' h1 h2). Qed.
Lemma lem3283524 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283525 : term116 = False.
Proof. exact (@lem3283524 False). Qed.
Lemma lem3283526 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : False.
Proof. exact (EQ_MP (@lem3283525) (@lem3283522 A x s t x' h1 h2)). Qed.
Lemma lem3283554 {A : Type'} (x : A) : x = x.
Proof. exact (@lem21386 A x). Qed.
Lemma lem3283555 {A : Type'} (x : A) : x = x.
Proof. exact (@lem3283554 A x). Qed.
Lemma lem3283556 {A : Type'} (x : A) : term113 A x.
Proof. exact (fun h0 : term102 A x => @lem3283555 A x). Qed.
Lemma lem3283558 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283559 {A : Type'} (x : A) : (term113 A x) = (x = x).
Proof. exact (@lem3283558 (x = x)). Qed.
Lemma lem3283560 {A : Type'} (x : A) : x = x.
Proof. exact (EQ_MP (@lem3283559 A x) (@lem3283556 A x)). Qed.
Lemma lem3283563 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283565 {A : Type'} (x : A) : (term102 A x) = (term115 A x).
Proof. exact (@lem3283563 (x = x)). Qed.
Lemma lem3283568 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : term115 A x.
Proof. exact (EQ_MP (@lem3283565 A x) (@lem3283287 A s x' x h1 h2)). Qed.
Lemma lem3283571 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (@lem3283568 A s x' x h1 h2 (@lem3283560 A x)). Qed.
Lemma lem3283572 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : term116.
Proof. exact (fun h0 : ~ False => @lem3283571 A s x' x h1 h2). Qed.
Lemma lem3283574 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283575 : term116 = False.
Proof. exact (@lem3283574 False). Qed.
Lemma lem3283578 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (h1). Qed.
Lemma lem3283579 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : term117 A t x.
Proof. exact (fun h0 : term75 A t x => @lem3283578 A t x h1). Qed.
Lemma lem3283581 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283582 {A : Type'} (t : A -> Prop) (x : A) : (term117 A t x) = (t x).
Proof. exact (@lem3283581 (t x)). Qed.
Lemma lem3283583 {A : Type'} (t : A -> Prop) (x : A) (h1 : t x) : t x.
Proof. exact (EQ_MP (@lem3283582 A t x) (@lem3283579 A t x h1)). Qed.
Lemma lem3283586 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283588 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term118 A t x).
Proof. exact (@lem3283586 (t x)). Qed.
Lemma lem3283591 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : x' = x) : term118 A t x.
Proof. exact (EQ_MP (@lem3283588 A t x) (@lem3283341 A t x' x h1 h2)). Qed.
Lemma lem3283594 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (@lem3283591 A t x' x h1 h3 (@lem3283583 A t x h2)). Qed.
Lemma lem3283595 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : term116.
Proof. exact (fun h0 : ~ False => @lem3283594 A t x' x h1 h2 h3). Qed.
Lemma lem3283597 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283598 : term116 = False.
Proof. exact (@lem3283597 False). Qed.
Lemma lem3283599 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283598) (@lem3283595 A t x' x h1 h2 h3)). Qed.
Lemma lem3283627 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') : s x'.
Proof. exact (proj1 (@lem3282886 A s t x' h1)). Qed.
Lemma lem3283628 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') : term117 A s x'.
Proof. exact (fun h0 : term75 A s x' => @lem3283627 A s t x' h1). Qed.
Lemma lem3283630 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283631 {A : Type'} (s : A -> Prop) (x' : A) : (term117 A s x') = (s x').
Proof. exact (@lem3283630 (s x')). Qed.
Lemma lem3283632 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') : s x'.
Proof. exact (EQ_MP (@lem3283631 A s x') (@lem3283628 A s t x' h1)). Qed.
Lemma lem3283635 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283637 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (term118 A s x').
Proof. exact (@lem3283635 (s x')). Qed.
Lemma lem3283640 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term118 A s x'.
Proof. exact (EQ_MP (@lem3283637 A s x') (@lem3283104 A x s x' h1)). Qed.
Lemma lem3283643 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s x') (h2 : term45 A s t x') : False.
Proof. exact (@lem3283640 A x s x' h1 (@lem3283632 A s t x' h2)). Qed.
Lemma lem3283644 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s x') (h2 : term45 A s t x') : term116.
Proof. exact (fun h0 : ~ False => @lem3283643 A x s t x' h1 h2). Qed.
Lemma lem3283646 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283647 : term116 = False.
Proof. exact (@lem3283646 False). Qed.
Lemma lem3283648 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s x') (h2 : term45 A s t x') : False.
Proof. exact (EQ_MP (@lem3283647) (@lem3283644 A x s t x' h1 h2)). Qed.
Lemma lem3283650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') : t x'.
Proof. exact (proj2 (@lem3282886 A s t x' h1)). Qed.
Lemma lem3283651 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') : term117 A t x'.
Proof. exact (fun h0 : term75 A t x' => @lem3283650 A s t x' h1). Qed.
Lemma lem3283653 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283654 {A : Type'} (t : A -> Prop) (x' : A) : (term117 A t x') = (t x').
Proof. exact (@lem3283653 (t x')). Qed.
Lemma lem3283655 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') : t x'.
Proof. exact (EQ_MP (@lem3283654 A t x') (@lem3283651 A s t x' h1)). Qed.
Lemma lem3283658 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3283660 {A : Type'} (t : A -> Prop) (x' : A) : (term75 A t x') = (term118 A t x').
Proof. exact (@lem3283658 (t x')). Qed.
Lemma lem3283663 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term118 A t x'.
Proof. exact (EQ_MP (@lem3283660 A t x') (@lem3283112 A t x' h1)). Qed.
Lemma lem3283666 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : False.
Proof. exact (@lem3283663 A t x' h1 (@lem3283655 A s t x' h2)). Qed.
Lemma lem3283667 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : term116.
Proof. exact (fun h0 : ~ False => @lem3283666 A s t x' h1 h2). Qed.
Lemma lem3283669 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3283670 : term116 = False.
Proof. exact (@lem3283669 False). Qed.
Lemma lem3283671 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : False.
Proof. exact (EQ_MP (@lem3283670) (@lem3283667 A s t x' h1 h2)). Qed.
Lemma lem3283672 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3283599 A t x' x h1 h2 h3) (fun h4 : False => @lem3283328 A t x h2)). Qed.
Lemma lem3283674 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283672 A t x' x h1 h2 h3) (@lem3283328 A t x h2)). Qed.
Lemma lem3283675 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283575) (@lem3283572 A s x' x h1 h2)). Qed.
Lemma lem3283676 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283427) (@lem3283424 A s t x' x h1 h2 h3)). Qed.
Lemma lem3283677 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283390) (@lem3283387 A s t x' x h1 h2)). Qed.
Lemma lem3283678 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3283671 A s t x' h1 h2) (fun h3 : False => @lem3283112 A t x' h1)). Qed.
Lemma lem3283679 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : False.
Proof. exact (EQ_MP (@lem3283678 A s t x' h1 h2) (@lem3283112 A t x' h1)). Qed.
Lemma lem3283680 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3283674 A t x' x h1 h2 h3) (fun h4 : False => @lem3283094 A t x' h1)). Qed.
Lemma lem3283681 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283680 A t x' x h1 h2 h3) (@lem3283094 A t x' h1)). Qed.
Lemma lem3283682 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3283681 A t x' x h1 h2 h3) (fun h4 : False => @lem3283092 A x' x h3)). Qed.
Lemma lem3283683 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283682 A t x' x h1 h2 h3) (@lem3283092 A x' x h3)). Qed.
Lemma lem3283684 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3283683 A t x' x h1 h2 h3) (fun h4 : False => @lem3283090 A t x h2)). Qed.
Lemma lem3283685 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283684 A t x' x h1 h2 h3) (@lem3283090 A t x h2)). Qed.
Lemma lem3283686 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3283675 A s x' x h1 h2) (fun h3 : False => @lem3283084 A x' x h2)). Qed.
Lemma lem3283687 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283686 A s x' x h1 h2) (@lem3283084 A x' x h2)). Qed.
Lemma lem3283688 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3283526 A x s t x' h1 h2) (fun h3 : False => @lem3283080 A t x' h1)). Qed.
Lemma lem3283689 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : False.
Proof. exact (EQ_MP (@lem3283688 A x s t x' h1 h2) (@lem3283080 A t x' h1)). Qed.
Lemma lem3283690 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (term75 A s x') = False.
Proof. exact (prop_ext (fun h3 : term75 A s x' => @lem3283477 A s x' h1 h2) (fun h3 : False => @lem3283070 A s x' h1)). Qed.
Lemma lem3283691 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3283690 A s x' h1 h2) (@lem3283070 A s x' h1)). Qed.
Lemma lem3283692 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3283691 A s x' h1 h2) (fun h3 : False => @lem3283068 A s x' h2)). Qed.
Lemma lem3283693 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3283692 A s x' h1 h2) (@lem3283068 A s x' h2)). Qed.
Lemma lem3283694 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3283676 A s t x' x h1 h2 h3) (fun h4 : False => @lem3283060 A t x' h1)). Qed.
Lemma lem3283695 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283694 A s t x' x h1 h2 h3) (@lem3283060 A t x' h1)). Qed.
Lemma lem3283696 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3283695 A s t x' x h1 h2 h3) (fun h4 : False => @lem3283058 A x' x h3)). Qed.
Lemma lem3283697 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283696 A s t x' x h1 h2 h3) (@lem3283058 A x' x h3)). Qed.
Lemma lem3283698 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3283677 A s t x' x h1 h2) (fun h3 : False => @lem3283048 A x' x h2)). Qed.
Lemma lem3283699 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283698 A s t x' x h1 h2) (@lem3283048 A x' x h2)). Qed.
Lemma lem3283700 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3283679 A s t x' h1 h2) (fun h3 : False => @lem3283040 A t x' h1)). Qed.
Lemma lem3283701 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : False.
Proof. exact (EQ_MP (@lem3283700 A s t x' h1 h2) (@lem3283040 A t x' h1)). Qed.
Lemma lem3283702 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3283685 A t x' x h1 h2 h3) (fun h4 : False => @lem3283004 A t x' h1)). Qed.
Lemma lem3283703 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283702 A t x' x h1 h2 h3) (@lem3283004 A t x' h1)). Qed.
Lemma lem3283704 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3283703 A t x' x h1 h2 h3) (fun h4 : False => @lem3283000 A x' x h3)). Qed.
Lemma lem3283705 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283704 A t x' x h1 h2 h3) (@lem3283000 A x' x h3)). Qed.
Lemma lem3283706 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3283705 A t x' x h1 h2 h3) (fun h4 : False => @lem3282996 A t x h2)). Qed.
Lemma lem3283707 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283706 A t x' x h1 h2 h3) (@lem3282996 A t x h2)). Qed.
Lemma lem3283708 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3283687 A s x' x h1 h2) (fun h3 : False => @lem3282984 A x' x h2)). Qed.
Lemma lem3283709 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283708 A s x' x h1 h2) (@lem3282984 A x' x h2)). Qed.
Lemma lem3283710 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3283689 A x s t x' h1 h2) (fun h3 : False => @lem3282976 A t x' h1)). Qed.
Lemma lem3283711 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : False.
Proof. exact (EQ_MP (@lem3283710 A x s t x' h1 h2) (@lem3282976 A t x' h1)). Qed.
Lemma lem3283712 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (term75 A s x') = False.
Proof. exact (prop_ext (fun h3 : term75 A s x' => @lem3283693 A s x' h1 h2) (fun h3 : False => @lem3282956 A s x' h1)). Qed.
Lemma lem3283713 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3283712 A s x' h1 h2) (@lem3282956 A s x' h1)). Qed.
Lemma lem3283714 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3283713 A s x' h1 h2) (fun h3 : False => @lem3282952 A s x' h2)). Qed.
Lemma lem3283715 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3283714 A s x' h1 h2) (@lem3282952 A s x' h2)). Qed.
Lemma lem3283716 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3283697 A s t x' x h1 h2 h3) (fun h4 : False => @lem3282936 A t x' h1)). Qed.
Lemma lem3283717 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283716 A s t x' x h1 h2 h3) (@lem3282936 A t x' h1)). Qed.
Lemma lem3283718 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3283717 A s t x' x h1 h2 h3) (fun h4 : False => @lem3282932 A x' x h3)). Qed.
Lemma lem3283719 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283718 A s t x' x h1 h2 h3) (@lem3282932 A x' x h3)). Qed.
Lemma lem3283720 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3283699 A s t x' x h1 h2) (fun h3 : False => @lem3282912 A x' x h2)). Qed.
Lemma lem3283721 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283720 A s t x' x h1 h2) (@lem3282912 A x' x h2)). Qed.
Lemma lem3283722 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3283701 A s t x' h1 h2) (fun h3 : False => @lem3283040 A t x' h1)). Qed.
Lemma lem3283723 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term45 A s t x') : False.
Proof. exact (EQ_MP (@lem3283722 A s t x' h1 h2) (@lem3283040 A t x' h1)). Qed.
Lemma lem3283724 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3283707 A t x' x h1 h2 h3) (fun h4 : False => @lem3283004 A t x' h1)). Qed.
Lemma lem3283725 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283724 A t x' x h1 h2 h3) (@lem3283004 A t x' h1)). Qed.
Lemma lem3283726 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3283725 A t x' x h1 h2 h3) (fun h4 : False => @lem3283000 A x' x h3)). Qed.
Lemma lem3283727 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283726 A t x' x h1 h2 h3) (@lem3283000 A x' x h3)). Qed.
Lemma lem3283728 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : (t x) = False.
Proof. exact (prop_ext (fun h4 : t x => @lem3283727 A t x' x h1 h2 h3) (fun h4 : False => @lem3282996 A t x h2)). Qed.
Lemma lem3283729 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : t x) (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283728 A t x' x h1 h2 h3) (@lem3282996 A t x h2)). Qed.
Lemma lem3283730 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3283709 A s x' x h1 h2) (fun h3 : False => @lem3282984 A x' x h2)). Qed.
Lemma lem3283731 {A : Type'} (s : A -> Prop) (x' : A) (x : A) (h1 : term74 A x s x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283730 A s x' x h1 h2) (@lem3282984 A x' x h2)). Qed.
Lemma lem3283732 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3283711 A x s t x' h1 h2) (fun h3 : False => @lem3282976 A t x' h1)). Qed.
Lemma lem3283733 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term93 A x s t x') : False.
Proof. exact (EQ_MP (@lem3283732 A x s t x' h1 h2) (@lem3282976 A t x' h1)). Qed.
Lemma lem3283734 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (term75 A s x') = False.
Proof. exact (prop_ext (fun h3 : term75 A s x' => @lem3283715 A s x' h1 h2) (fun h3 : False => @lem3282956 A s x' h1)). Qed.
Lemma lem3283735 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3283734 A s x' h1 h2) (@lem3282956 A s x' h1)). Qed.
Lemma lem3283736 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3283735 A s x' h1 h2) (fun h3 : False => @lem3282952 A s x' h2)). Qed.
Lemma lem3283737 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3283736 A s x' h1 h2) (@lem3282952 A s x' h2)). Qed.
Lemma lem3283738 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3283719 A s t x' x h1 h2 h3) (fun h4 : False => @lem3282936 A t x' h1)). Qed.
Lemma lem3283739 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283738 A s t x' x h1 h2 h3) (@lem3282936 A t x' h1)). Qed.
Lemma lem3283740 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3283739 A s t x' x h1 h2 h3) (fun h4 : False => @lem3282932 A x' x h3)). Qed.
Lemma lem3283741 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term93 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283740 A s t x' x h1 h2 h3) (@lem3282932 A x' x h3)). Qed.
Lemma lem3283742 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h3 : x' = x => @lem3283721 A s t x' x h1 h2) (fun h3 : False => @lem3282912 A x' x h2)). Qed.
Lemma lem3283743 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : False.
Proof. exact (EQ_MP (@lem3283742 A s t x' x h1 h2) (@lem3282912 A x' x h2)). Qed.
Lemma lem3283744 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term45 A s t x') (h2 : term90 A x s t x') : False.
Proof. exact (or_elim (@lem3282884 A x s t x' h2) (fun h0 : term74 A x s x' => @lem3283648 A x s t x' h0 h1) (fun h0 : term75 A t x' => @lem3283723 A s t x' h0 h1)). Qed.
Lemma lem3283745 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : t x) (h2 : term90 A x s t x') (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3282884 A x s t x' h2) (fun h0 : term74 A x s x' => @lem3283731 A s x' x h0 h3) (fun h0 : term75 A t x' => @lem3283729 A t x' x h0 h1 h3)). Qed.
Lemma lem3283746 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : t x) (h2 : term90 A x s t x') : False.
Proof. exact (or_elim (@lem3282883 A x s t x' h2) (fun h0 : x' = x => @lem3283745 A s t x' x h1 h2 h0) (fun h0 : term45 A s t x' => @lem3283744 A x s t x' h0 h2)). Qed.
Lemma lem3283747 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term93 A x s t x') : False.
Proof. exact (or_elim (@lem3282873 A x s t x' h2) (fun h0 : term75 A s x' => @lem3283737 A s x' h0 h1) (fun h0 : term75 A t x' => @lem3283733 A x s t x' h0 h2)). Qed.
Lemma lem3283748 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term93 A x s t x') (h2 : x' = x) : False.
Proof. exact (or_elim (@lem3282873 A x s t x' h1) (fun h0 : term75 A s x' => @lem3283743 A s t x' x h1 h2) (fun h0 : term75 A t x' => @lem3283741 A s t x' x h0 h1 h2)). Qed.
Lemma lem3283749 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term93 A x s t x') : False.
Proof. exact (or_elim (@lem3282876 A x s t x' h1) (fun h0 : x' = x => @lem3283748 A s t x' x h1 h0) (fun h0 : s x' => @lem3283747 A x s t x' h0 h1)). Qed.
Lemma lem3283750 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term72 A x s t x') (h2 : t x) : False.
Proof. exact (or_elim (@lem3282868 A x s t x' h1) (fun h0 : term93 A x s t x' => @lem3283749 A x s t x' h0) (fun h0 : term90 A x s t x' => @lem3283746 A x s t x' h2 h0)). Qed.
Lemma lem3283751 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term72 A x s t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3283750 A s x' t x h1 h2) (fun h3 : False => @lem3282778 A t x h2)). Qed.
Lemma lem3283752 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term72 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3283751 A s x' t x h1 h2) (@lem3282778 A t x h2)). Qed.
Lemma lem3283753 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term72 A x s t x') (h2 : t x) : (t x) = False.
Proof. exact (prop_ext (fun h3 : t x => @lem3283752 A s x' t x h1 h2) (fun h3 : False => @lem3282714 A t x h2)). Qed.
Lemma lem3283754 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term72 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3283753 A s x' t x h1 h2) (@lem3282714 A t x h2)). Qed.
Lemma lem3283755 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term72 A x s t x') (h2 : t x) : (term72 A x s t x') = False.
Proof. exact (prop_ext (fun h3 : term72 A x s t x' => @lem3283754 A s x' t x h1 h2) (fun h3 : False => @lem3282708 A x s t x' h1)). Qed.
Lemma lem3283756 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term72 A x s t x') (h2 : t x) : False.
Proof. exact (EQ_MP (@lem3283755 A s x' t x h1 h2) (@lem3282708 A x s t x' h1)). Qed.
Lemma lem3283757 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : term71 A x s t x'.
Proof. exact (fun h0 : term72 A x s t x' => @lem3283756 A s x' t x h0 h1). Qed.
Lemma lem3283758 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : t x) : (term38 A x s t x') = (term46 A x s t x').
Proof. exact (EQ_MP (@lem3282707 A x s t x') (@lem3283757 A s x' t x h1)). Qed.
Lemma lem3283763 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : t x) : term49 A x s t.
Proof. exact (fun x' : A => @lem3283758 A s x' t x h1). Qed.
Lemma lem3283764 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term50 A x s t.
Proof. exact (fun h0 : t x => @lem3283763 A s t x h0). Qed.
Lemma lem3283769 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term62 A s t.
Proof. exact (fun x : A => @lem3283764 A x s t). Qed.
Lemma lem3283774 {A : Type'} (t : A -> Prop) : term66 A t.
Proof. exact (fun s : A -> Prop => @lem3283769 A s t). Qed.
Lemma lem3283779 {A : Type'} : term70 A.
Proof. exact (fun t : A -> Prop => @lem3283774 A t). Qed.
Lemma lem3283780 {A : Type'} : term69 A.
Proof. exact (EQ_MP (@lem3282702 A) (@lem3283779 A)). Qed.
Lemma lem3283781 {A : Type'} (t : A -> Prop) : term119 A t.
Proof. exact (@lem3283780 A t). Qed.
Lemma lem3283782 {A : Type'} (t : A -> Prop) : (term119 A t) = (term65 A t).
Proof. exact (eq_refl (term119 A t)). Qed.
Lemma lem3283783 {A : Type'} (t : A -> Prop) : term65 A t.
Proof. exact (EQ_MP (@lem3283782 A t) (@lem3283781 A t)). Qed.
Lemma lem3283784 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term120 A t s.
Proof. exact (@lem3283783 A t s). Qed.
Lemma lem3283785 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term120 A t s) = (term61 A s t).
Proof. exact (eq_refl (term120 A t s)). Qed.
Lemma lem3283786 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term61 A s t.
Proof. exact (EQ_MP (@lem3283785 A s t) (@lem3283784 A t s)). Qed.
Lemma lem3283787 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term121 A s t x.
Proof. exact (@lem3283786 A s t x). Qed.
Lemma lem3283788 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term121 A s t x) = (term52 A x s t).
Proof. exact (eq_refl (term121 A s t x)). Qed.
Lemma lem3283789 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term52 A x s t.
Proof. exact (EQ_MP (@lem3283788 A x s t) (@lem3283787 A s t x)). Qed.
Lemma lem3283791 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term52 A x s t.
Proof. exact (@lem3282569 A x s t (@lem3283789 A x s t)). Qed.
Lemma lem3283792 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A x s t) : False.
Proof. exact (@lem3283791 A x s t (@lem3282553 A x s t h1)). Qed.
Lemma lem3283793 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A x s t) : (term53 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term53 A x s t => @lem3283792 A x s t h1) (fun h2 : False => @lem3282553 A x s t h1)). Qed.
Lemma lem3283794 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term53 A x s t) : False.
Proof. exact (EQ_MP (@lem3283793 A x s t h1) (@lem3282553 A x s t h1)). Qed.
Lemma lem3283795 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term52 A x s t.
Proof. exact (fun h0 : term53 A x s t => @lem3283794 A x s t h0). Qed.
Lemma lem3283796 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term50 A x s t.
Proof. exact (EQ_MP (@lem3282552 A x s t) (@lem3283795 A x s t)). Qed.
Lemma lem3283797 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term26 A x s t.
Proof. exact (EQ_MP (@lem3282548 A x s t) (@lem3283796 A x s t)). Qed.
Lemma lem3283798 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term16 A x s t.
Proof. exact (EQ_MP (@lem3282452 A x s t) (@lem3283797 A x s t)). Qed.
Lemma lem3283804 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3283805 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term24 A s t).
Proof. exact (@lem3283804 A s t). Qed.
Lemma lem3283806 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : ((term9 A x s t) = (@INTER A s t)) = (term122 A x s t).
Proof. exact (@lem3283805 A (term9 A x s t) (@INTER A s t)). Qed.
Lemma lem3283815 {A : Type'} (x : A) (t : A -> Prop) : (term10 A x t) = (term10 A x t).
Proof. exact (eq_refl (term10 A x t)). Qed.
Lemma lem3283816 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term12 A x s t) = (term123 A x s t).
Proof. exact (MK_COMB (@lem3283815 A x t) (@lem3283806 A x s t)). Qed.
Lemma lem3283819 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term123 A x s t) = (term12 A x s t).
Proof. exact (SYM (@lem3283816 A x s t)). Qed.
Lemma lem3283823 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3283824 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3283823 A P x). Qed.
Lemma lem3283825 {A : Type'} (t : A -> Prop) (x : A) : (@IN A x t) = (t x).
Proof. exact (@lem3283824 A t x). Qed.
Lemma lem3283826 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3283827 {A : Type'} (t : A -> Prop) (x : A) : (term23 A x t) = (term75 A t x).
Proof. exact (MK_COMB (@lem3283826) (@lem3283825 A t x)). Qed.
Lemma lem3283828 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3283829 {A : Type'} (t : A -> Prop) (x : A) : (term10 A x t) = (term124 A t x).
Proof. exact (MK_COMB (@lem3283828) (@lem3283827 A t x)). Qed.
Lemma lem3283837 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3283838 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3283837 A s x t). Qed.
Lemma lem3283839 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (t : A -> Prop) : (term30 A x' x s t) = (term31 A x s x' t).
Proof. exact (@lem3283838 A (@INSERT A x s) x' t). Qed.
Lemma lem3283843 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (EQ_MP (@lem3211693 A y x s) (@lem3211692 A y x s)). Qed.
Lemma lem3283844 {A : Type'} (y : A) (x : A) (s : A -> Prop) : (term32 A x y s) = (term33 A y x s).
Proof. exact (@lem3283843 A y x s). Qed.
Lemma lem3283845 {A : Type'} (x : A) (x' : A) (s : A -> Prop) : (term32 A x' x s) = (term33 A x x' s).
Proof. exact (@lem3283844 A x x' s). Qed.
Lemma lem3283851 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3283852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3283851 A P x). Qed.
Lemma lem3283853 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3283852 A s x'). Qed.
Lemma lem3283854 {A : Type'} (x' : A) (x : A) : (term34 A x' x) = (term34 A x' x).
Proof. exact (eq_refl (term34 A x' x)). Qed.
Lemma lem3283855 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term33 A x x' s) = (term35 A x s x').
Proof. exact (MK_COMB (@lem3283854 A x' x) (@lem3283853 A s x')). Qed.
Lemma lem3283858 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term32 A x' x s) = (term35 A x s x').
Proof. exact (TRANS (@lem3283845 A x x' s) (@lem3283855 A x s x')). Qed.
Lemma lem3283859 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3283860 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term36 A x' x s) = (term37 A x s x').
Proof. exact (MK_COMB (@lem3283859) (@lem3283858 A x s x')). Qed.
Lemma lem3283862 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3283863 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3283862 A P x). Qed.
Lemma lem3283864 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3283863 A t x'). Qed.
Lemma lem3283865 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term31 A x s x' t) = (term38 A x s t x').
Proof. exact (MK_COMB (@lem3283860 A x s x') (@lem3283864 A t x')). Qed.
Lemma lem3283868 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term30 A x' x s t) = (term38 A x s t x').
Proof. exact (TRANS (@lem3283839 A x s x' t) (@lem3283865 A x s t x')). Qed.
Lemma lem3283869 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3283870 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term39 A x' x s t) = (term40 A x s t x').
Proof. exact (MK_COMB (@lem3283869) (@lem3283868 A x s t x')). Qed.
Lemma lem3283872 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (EQ_MP (@lem3211711 A s x t) (@lem3211710 A s t x)). Qed.
Lemma lem3283873 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) : (term28 A x s t) = (term29 A s x t).
Proof. exact (@lem3283872 A s x t). Qed.
Lemma lem3283874 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) : (term28 A x' s t) = (term29 A s x' t).
Proof. exact (@lem3283873 A s x' t). Qed.
Lemma lem3283878 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3283879 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3283878 A P x). Qed.
Lemma lem3283880 {A : Type'} (s : A -> Prop) (x' : A) : (@IN A x' s) = (s x').
Proof. exact (@lem3283879 A s x'). Qed.
Lemma lem3283881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3283882 {A : Type'} (s : A -> Prop) (x' : A) : (term43 A x' s) = (term44 A s x').
Proof. exact (MK_COMB (@lem3283881) (@lem3283880 A s x')). Qed.
Lemma lem3283884 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3283885 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (@lem3283884 A P x). Qed.
Lemma lem3283886 {A : Type'} (t : A -> Prop) (x' : A) : (@IN A x' t) = (t x').
Proof. exact (@lem3283885 A t x'). Qed.
Lemma lem3283887 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term29 A s x' t) = (term45 A s t x').
Proof. exact (MK_COMB (@lem3283882 A s x') (@lem3283886 A t x')). Qed.
Lemma lem3283890 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term28 A x' s t) = (term45 A s t x').
Proof. exact (TRANS (@lem3283874 A s x' t) (@lem3283887 A s t x')). Qed.
Lemma lem3283891 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term30 A x' x s t) = (term28 A x' s t)) = ((term38 A x s t x') = (term45 A s t x')).
Proof. exact (MK_COMB (@lem3283870 A x s t x') (@lem3283890 A s t x')). Qed.
Lemma lem3283894 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term125 A x s t) = (term126 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3283891 A x s t x')). Qed.
Lemma lem3283895 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3283896 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term122 A x s t) = (term127 A x s t).
Proof. exact (MK_COMB (@lem3283895 A) (@lem3283894 A x s t)). Qed.
Lemma lem3283901 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term123 A x s t) = (term128 A x s t).
Proof. exact (MK_COMB (@lem3283829 A t x) (@lem3283896 A x s t)). Qed.
Lemma lem3283904 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term128 A x s t) = (term123 A x s t).
Proof. exact (SYM (@lem3283901 A x s t)). Qed.
Lemma lem3283906 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3283907 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term128 A x s t) = (term129 A x s t).
Proof. exact (@lem3283906 (term128 A x s t)). Qed.
Lemma lem3283908 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term129 A x s t) = (term128 A x s t).
Proof. exact (SYM (@lem3283907 A x s t)). Qed.
Lemma lem3283909 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term130 A x s t) : term130 A x s t.
Proof. exact (h1). Qed.
Lemma lem3283912 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term129 A x s t) : term129 A x s t.
Proof. exact (h1). Qed.
Lemma lem3283913 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term131 A x s t.
Proof. exact (fun h0 : term129 A x s t => @lem3283912 A x s t h0). Qed.
Lemma lem3283914 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term131 A x s t) : term131 A x s t.
Proof. exact (h1). Qed.
Lemma lem3283915 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term129 A x s t) : term129 A x s t.
Proof. exact (h1). Qed.
Lemma lem3283916 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term129 A x s t) (h2 : term131 A x s t) : term129 A x s t.
Proof. exact (@lem3283914 A x s t h2 (@lem3283915 A x s t h1)). Qed.
Lemma lem3283917 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term129 A x s t) : term132 A x s t.
Proof. exact (fun h0 : term131 A x s t => @lem3283916 A x s t h1 h0). Qed.
Lemma lem3283918 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term131 A x s t) : term131 A x s t.
Proof. exact (h1). Qed.
Lemma lem3283919 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term129 A x s t) (h2 : term131 A x s t) : term129 A x s t.
Proof. exact (@lem3283917 A x s t h1 (@lem3283918 A x s t h2)). Qed.
Lemma lem3283920 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term131 A x s t) : term131 A x s t.
Proof. exact (fun h0 : term129 A x s t => @lem3283919 A x s t h0 h1). Qed.
Lemma lem3283921 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term133 A x s t.
Proof. exact (fun h0 : term131 A x s t => @lem3283920 A x s t h0). Qed.
Lemma lem3283924 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term131 A x s t.
Proof. exact (@lem3283921 A x s t (@lem3283913 A x s t)). Qed.
Lemma lem3283925 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term131 A x s t.
Proof. exact (@lem3283924 A x s t). Qed.
Lemma lem3283939 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3283940 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term129 A x s t) = (term134 A x s t).
Proof. exact (@lem3283939 (term130 A x s t)). Qed.
Lemma lem3283942 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3283943 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term134 A x s t) = (term128 A x s t).
Proof. exact (@lem3283942 (term128 A x s t)). Qed.
Lemma lem3283946 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term129 A x s t) = (term128 A x s t).
Proof. exact (TRANS (@lem3283940 A x s t) (@lem3283943 A x s t)). Qed.
Lemma lem3283957 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term135 A s t) = (term136 A s t).
Proof. exact (fun_ext (fun x : A => @lem3283946 A x s t)). Qed.
Lemma lem3283958 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3283959 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term137 A s t) = (term138 A s t).
Proof. exact (MK_COMB (@lem3283958 A) (@lem3283957 A s t)). Qed.
Lemma lem3283964 {A : Type'} (t : A -> Prop) : (term139 A t) = (term140 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3283959 A s t)). Qed.
Lemma lem3283965 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3283966 {A : Type'} (t : A -> Prop) : (term141 A t) = (term142 A t).
Proof. exact (MK_COMB (@lem3283965 A) (@lem3283964 A t)). Qed.
Lemma lem3283971 {A : Type'} : (term143 A) = (term144 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3283966 A t)). Qed.
Lemma lem3283972 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3283981 {A : Type'} : (term145 A) = (term146 A).
Proof. exact (MK_COMB (@lem3283972 A) (@lem3283971 A)). Qed.
Lemma lem3283998 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term45 A s t x')) = ((term38 A x s t x') = (term45 A s t x')).
Proof. exact (eq_refl ((term38 A x s t x') = (term45 A s t x'))). Qed.
Lemma lem3283999 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term126 A x s t) = (term126 A x s t).
Proof. exact (fun_ext (fun x' : A => @lem3283998 A x s t x')). Qed.
Lemma lem3284000 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3284001 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term127 A x s t) = (term127 A x s t).
Proof. exact (MK_COMB (@lem3284000 A) (@lem3283999 A x s t)). Qed.
Lemma lem3284006 {A : Type'} (t : A -> Prop) (x : A) : (term124 A t x) = (term124 A t x).
Proof. exact (eq_refl (term124 A t x)). Qed.
Lemma lem3284007 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term128 A x s t) = (term128 A x s t).
Proof. exact (MK_COMB (@lem3284006 A t x) (@lem3284001 A x s t)). Qed.
Lemma lem3284008 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term136 A s t) = (term136 A s t).
Proof. exact (fun_ext (fun x : A => @lem3284007 A x s t)). Qed.
Lemma lem3284009 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3284010 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term138 A s t) = (term138 A s t).
Proof. exact (MK_COMB (@lem3284009 A) (@lem3284008 A s t)). Qed.
Lemma lem3284011 {A : Type'} (t : A -> Prop) : (term140 A t) = (term140 A t).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3284010 A s t)). Qed.
Lemma lem3284012 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3284013 {A : Type'} (t : A -> Prop) : (term142 A t) = (term142 A t).
Proof. exact (MK_COMB (@lem3284012 A) (@lem3284011 A t)). Qed.
Lemma lem3284014 {A : Type'} : (term144 A) = (term144 A).
Proof. exact (fun_ext (fun t : A -> Prop => @lem3284013 A t)). Qed.
Lemma lem3284015 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3284016 {A : Type'} : (term146 A) = (term146 A).
Proof. exact (MK_COMB (@lem3284015 A) (@lem3284014 A)). Qed.
Lemma lem3284051 {A : Type'} : (term145 A) = (term146 A).
Proof. exact (TRANS (@lem3283981 A) (@lem3284016 A)). Qed.
Lemma lem3284052 {A : Type'} : (term146 A) = (term145 A).
Proof. exact (SYM (@lem3284051 A)). Qed.
Lemma lem3284055 (p : Prop) : p = (term51 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3284056 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : ((term38 A x s t x') = (term45 A s t x')) = (term147 A x s t x').
Proof. exact (@lem3284055 ((term38 A x s t x') = (term45 A s t x'))). Qed.
Lemma lem3284057 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term147 A x s t x') = ((term38 A x s t x') = (term45 A s t x')).
Proof. exact (SYM (@lem3284056 A x s t x')). Qed.
Lemma lem3284058 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term148 A x s t x') : term148 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3284064 {A : Type'} (t : A -> Prop) (x : A) (h1 : term75 A t x) : term75 A t x.
Proof. exact (h1). Qed.
Lemma lem3284073 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term73 A x s x') = (term74 A x s x').
Proof. exact (@lem17160 (x' = x) (s x')). Qed.
Lemma lem3284077 {A : Type'} (t : A -> Prop) (x' : A) : (term75 A t x') = (term75 A t x').
Proof. exact (eq_refl (term75 A t x')). Qed.
Lemma lem3284079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3284080 {A : Type'} (x : A) (s : A -> Prop) (x' : A) : (term76 A x s x') = (term77 A x s x').
Proof. exact (MK_COMB (@lem3284079) (@lem3284073 A x s x')). Qed.
Lemma lem3284081 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term78 A x s t x') = (term79 A x s t x').
Proof. exact (MK_COMB (@lem3284080 A x s x') (@lem3284077 A t x')). Qed.
Lemma lem3284082 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A x s t x') = (term78 A x s t x').
Proof. exact (@lem17045 (term35 A x s x') (t x')). Qed.
Lemma lem3284083 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term80 A x s t x') = (term79 A x s t x').
Proof. exact (TRANS (@lem3284082 A x s t x') (@lem3284081 A x s t x')). Qed.
Lemma lem3284095 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term81 A s t x') = (term82 A s t x').
Proof. exact (@lem17045 (s x') (t x')). Qed.
Lemma lem3284098 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) : (term45 A s t x') = (term45 A s t x').
Proof. exact (eq_refl (term45 A s t x')). Qed.
Lemma lem3284099 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3284100 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term87 A x s t x') = (term88 A x s t x').
Proof. exact (MK_COMB (@lem3284099) (@lem3284083 A x s t x')). Qed.
Lemma lem3284101 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term149 A x s t x') = (term150 A x s t x').
Proof. exact (MK_COMB (@lem3284100 A x s t x') (@lem3284098 A s t x')). Qed.
Lemma lem3284103 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term91 A x s t x') = (term91 A x s t x').
Proof. exact (eq_refl (term91 A x s t x')). Qed.
Lemma lem3284104 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term151 A x s t x') = (term152 A x s t x').
Proof. exact (MK_COMB (@lem3284103 A x s t x') (@lem3284095 A s t x')). Qed.
Lemma lem3284105 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3284106 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term153 A x s t x') = (term154 A x s t x').
Proof. exact (MK_COMB (@lem3284105) (@lem3284104 A x s t x')). Qed.
Lemma lem3284107 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term155 A x s t x') = (term156 A x s t x').
Proof. exact (MK_COMB (@lem3284106 A x s t x') (@lem3284101 A x s t x')). Qed.
Lemma lem3284108 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term148 A x s t x') = (term155 A x s t x').
Proof. exact (@lem17646 (term38 A x s t x') (term45 A s t x')). Qed.
Lemma lem3284113 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) : (term148 A x s t x') = (term156 A x s t x').
Proof. exact (TRANS (@lem3284108 A x s t x') (@lem3284107 A x s t x')). Qed.
Lemma lem3284120 {A : Type'} (t : A -> Prop) (x : A) (h1 : term75 A t x) : term75 A t x.
Proof. exact (h1). Qed.
Lemma lem3284192 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term148 A x s t x') : term156 A x s t x'.
Proof. exact (EQ_MP (@lem3284113 A x s t x') (@lem3284058 A x s t x' h1)). Qed.
Lemma lem3284193 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : term152 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3284194 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : term150 A x s t x'.
Proof. exact (h1). Qed.
Lemma lem3284195 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : term82 A s t x'.
Proof. exact (proj2 (@lem3284193 A x s t x' h1)). Qed.
Lemma lem3284196 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : term38 A x s t x'.
Proof. exact (proj1 (@lem3284193 A x s t x' h1)). Qed.
Lemma lem3284198 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : term35 A x s x'.
Proof. exact (proj1 (@lem3284196 A x s t x' h1)). Qed.
Lemma lem3284205 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : term45 A s t x'.
Proof. exact (proj2 (@lem3284194 A x s t x' h1)). Qed.
Lemma lem3284206 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : term79 A x s t x'.
Proof. exact (proj1 (@lem3284194 A x s t x' h1)). Qed.
Lemma lem3284209 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term74 A x s x'.
Proof. exact (h1). Qed.
Lemma lem3284216 {A : Type'} (t : A -> Prop) (x : A) (h1 : term75 A t x) : term75 A t x.
Proof. exact (h1). Qed.
Lemma lem3284224 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3284240 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3284244 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3284256 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3284260 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') : term75 A s x'.
Proof. exact (h1). Qed.
Lemma lem3284276 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3284312 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3284314 {A : Type'} (t : A -> Prop) (x : A) (h1 : term75 A t x) : term75 A t x.
Proof. exact (h1). Qed.
Lemma lem3284316 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : t x'.
Proof. exact (proj2 (@lem3284196 A x s t x' h1)). Qed.
Lemma lem3284318 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3284324 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : t x'.
Proof. exact (proj2 (@lem3284196 A x s t x' h1)). Qed.
Lemma lem3284326 {A : Type'} (x' : A) (x : A) (h1 : x' = x) : x' = x.
Proof. exact (h1). Qed.
Lemma lem3284328 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3284334 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3284336 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') : term75 A s x'.
Proof. exact (h1). Qed.
Lemma lem3284344 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3284354 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term75 A s x'.
Proof. exact (proj2 (@lem3284209 A x s x' h1)). Qed.
Lemma lem3284362 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term75 A t x'.
Proof. exact (h1). Qed.
Lemma lem3284390 {A : Type'} (t : A -> Prop) (x : A) (h1 : term75 A t x) : term75 A t x.
Proof. exact (h1). Qed.
Lemma lem3284391 {A : Type'} (t : A -> Prop) : (term105 A t) = (term105 A t).
Proof. exact (eq_refl (term105 A t)). Qed.
Lemma lem3284392 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term106 A t x') = (term106 A t x).
Proof. exact (MK_COMB (@lem3284391 A t) (@lem3284318 A x' x h1)). Qed.
Lemma lem3284393 {A : Type'} (t : A -> Prop) (x : A) : (term106 A t x) = (t x).
Proof. exact (eq_refl (term106 A t x)). Qed.
Lemma lem3284394 {A : Type'} (t : A -> Prop) (x' : A) : (term107 A t x') = (term107 A t x').
Proof. exact (eq_refl (term107 A t x')). Qed.
Lemma lem3284395 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (term106 A t x)) = ((term106 A t x') = (t x)).
Proof. exact (MK_COMB (@lem3284394 A t x') (@lem3284393 A t x)). Qed.
Lemma lem3284396 {A : Type'} (t : A -> Prop) (x' : A) : (term106 A t x') = (t x').
Proof. exact (eq_refl (term106 A t x')). Qed.
Lemma lem3284397 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3284398 {A : Type'} (t : A -> Prop) (x' : A) : (term107 A t x') = (term108 A t x').
Proof. exact (MK_COMB (@lem3284397) (@lem3284396 A t x')). Qed.
Lemma lem3284399 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3284400 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (t x)) = ((t x') = (t x)).
Proof. exact (MK_COMB (@lem3284398 A t x') (@lem3284399 A t x)). Qed.
Lemma lem3284401 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (term106 A t x)) = ((t x') = (t x)).
Proof. exact (TRANS (@lem3284395 A x' t x) (@lem3284400 A x' t x)). Qed.
Lemma lem3284402 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (EQ_MP (@lem3284401 A x' t x) (@lem3284392 A t x' x h1)). Qed.
Lemma lem3284445 {A : Type'} (t : A -> Prop) : (term105 A t) = (term105 A t).
Proof. exact (eq_refl (term105 A t)). Qed.
Lemma lem3284446 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term106 A t x') = (term106 A t x).
Proof. exact (MK_COMB (@lem3284445 A t) (@lem3284326 A x' x h1)). Qed.
Lemma lem3284447 {A : Type'} (t : A -> Prop) (x : A) : (term106 A t x) = (t x).
Proof. exact (eq_refl (term106 A t x)). Qed.
Lemma lem3284448 {A : Type'} (t : A -> Prop) (x' : A) : (term107 A t x') = (term107 A t x').
Proof. exact (eq_refl (term107 A t x')). Qed.
Lemma lem3284449 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (term106 A t x)) = ((term106 A t x') = (t x)).
Proof. exact (MK_COMB (@lem3284448 A t x') (@lem3284447 A t x)). Qed.
Lemma lem3284450 {A : Type'} (t : A -> Prop) (x' : A) : (term106 A t x') = (t x').
Proof. exact (eq_refl (term106 A t x')). Qed.
Lemma lem3284451 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3284452 {A : Type'} (t : A -> Prop) (x' : A) : (term107 A t x') = (term108 A t x').
Proof. exact (MK_COMB (@lem3284451) (@lem3284450 A t x')). Qed.
Lemma lem3284453 {A : Type'} (t : A -> Prop) (x : A) : (t x) = (t x).
Proof. exact (eq_refl (t x)). Qed.
Lemma lem3284454 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (t x)) = ((t x') = (t x)).
Proof. exact (MK_COMB (@lem3284452 A t x') (@lem3284453 A t x)). Qed.
Lemma lem3284455 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term106 A t x') = (term106 A t x)) = ((t x') = (t x)).
Proof. exact (TRANS (@lem3284449 A x' t x) (@lem3284454 A x' t x)). Qed.
Lemma lem3284456 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (t x') = (t x).
Proof. exact (EQ_MP (@lem3284455 A x' t x) (@lem3284446 A t x' x h1)). Qed.
Lemma lem3284458 {A : Type'} (t : A -> Prop) : (term109 A t) = (term109 A t).
Proof. exact (eq_refl (term109 A t)). Qed.
Lemma lem3284459 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term110 A t x') = (term110 A t x).
Proof. exact (MK_COMB (@lem3284458 A t) (@lem3284326 A x' x h1)). Qed.
Lemma lem3284460 {A : Type'} (t : A -> Prop) (x : A) : (term110 A t x) = (term75 A t x).
Proof. exact (eq_refl (term110 A t x)). Qed.
Lemma lem3284461 {A : Type'} (t : A -> Prop) (x' : A) : (term111 A t x') = (term111 A t x').
Proof. exact (eq_refl (term111 A t x')). Qed.
Lemma lem3284462 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term110 A t x)) = ((term110 A t x') = (term75 A t x)).
Proof. exact (MK_COMB (@lem3284461 A t x') (@lem3284460 A t x)). Qed.
Lemma lem3284463 {A : Type'} (t : A -> Prop) (x' : A) : (term110 A t x') = (term75 A t x').
Proof. exact (eq_refl (term110 A t x')). Qed.
Lemma lem3284464 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3284465 {A : Type'} (t : A -> Prop) (x' : A) : (term111 A t x') = (term112 A t x').
Proof. exact (MK_COMB (@lem3284464) (@lem3284463 A t x')). Qed.
Lemma lem3284466 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term75 A t x).
Proof. exact (eq_refl (term75 A t x)). Qed.
Lemma lem3284467 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term75 A t x)) = ((term75 A t x') = (term75 A t x)).
Proof. exact (MK_COMB (@lem3284465 A t x') (@lem3284466 A t x)). Qed.
Lemma lem3284468 {A : Type'} (x' : A) (t : A -> Prop) (x : A) : ((term110 A t x') = (term110 A t x)) = ((term75 A t x') = (term75 A t x)).
Proof. exact (TRANS (@lem3284462 A x' t x) (@lem3284467 A x' t x)). Qed.
Lemma lem3284469 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : x' = x) : (term75 A t x') = (term75 A t x).
Proof. exact (EQ_MP (@lem3284468 A x' t x) (@lem3284459 A t x' x h1)). Qed.
Lemma lem3284470 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : x' = x) : term75 A t x.
Proof. exact (EQ_MP (@lem3284469 A t x' x h2) (@lem3284328 A t x' h1)). Qed.
Lemma lem3284472 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term152 A x s t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3284402 A t x' x h2) (@lem3284316 A x s t x' h1)). Qed.
Lemma lem3284473 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term152 A x s t x') (h2 : x' = x) : term117 A t x.
Proof. exact (fun h0 : term75 A t x => @lem3284472 A s t x' x h1 h2). Qed.
Lemma lem3284475 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284476 {A : Type'} (t : A -> Prop) (x : A) : (term117 A t x) = (t x).
Proof. exact (@lem3284475 (t x)). Qed.
Lemma lem3284477 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term152 A x s t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3284476 A t x) (@lem3284473 A s t x' x h1 h2)). Qed.
Lemma lem3284480 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3284482 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term118 A t x).
Proof. exact (@lem3284480 (t x)). Qed.
Lemma lem3284485 {A : Type'} (t : A -> Prop) (x : A) (h1 : term75 A t x) : term118 A t x.
Proof. exact (EQ_MP (@lem3284482 A t x) (@lem3284390 A t x h1)). Qed.
Lemma lem3284488 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (@lem3284485 A t x h1 (@lem3284477 A s t x' x h2 h3)). Qed.
Lemma lem3284489 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : term116.
Proof. exact (fun h0 : ~ False => @lem3284488 A s t x' x h1 h2 h3). Qed.
Lemma lem3284491 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284492 : term116 = False.
Proof. exact (@lem3284491 False). Qed.
Lemma lem3284493 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284492) (@lem3284489 A s t x' x h1 h2 h3)). Qed.
Lemma lem3284495 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term152 A x s t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3284456 A t x' x h2) (@lem3284324 A x s t x' h1)). Qed.
Lemma lem3284496 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term152 A x s t x') (h2 : x' = x) : term117 A t x.
Proof. exact (fun h0 : term75 A t x => @lem3284495 A s t x' x h1 h2). Qed.
Lemma lem3284498 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284499 {A : Type'} (t : A -> Prop) (x : A) : (term117 A t x) = (t x).
Proof. exact (@lem3284498 (t x)). Qed.
Lemma lem3284500 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term152 A x s t x') (h2 : x' = x) : t x.
Proof. exact (EQ_MP (@lem3284499 A t x) (@lem3284496 A s t x' x h1 h2)). Qed.
Lemma lem3284503 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3284505 {A : Type'} (t : A -> Prop) (x : A) : (term75 A t x) = (term118 A t x).
Proof. exact (@lem3284503 (t x)). Qed.
Lemma lem3284508 {A : Type'} (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : x' = x) : term118 A t x.
Proof. exact (EQ_MP (@lem3284505 A t x) (@lem3284470 A t x' x h1 h2)). Qed.
Lemma lem3284511 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (@lem3284508 A t x' x h1 h3 (@lem3284500 A s t x' x h2 h3)). Qed.
Lemma lem3284512 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : term116.
Proof. exact (fun h0 : ~ False => @lem3284511 A s t x' x h1 h2 h3). Qed.
Lemma lem3284514 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284515 : term116 = False.
Proof. exact (@lem3284514 False). Qed.
Lemma lem3284518 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (h1). Qed.
Lemma lem3284519 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : term117 A s x'.
Proof. exact (fun h0 : term75 A s x' => @lem3284518 A s x' h1). Qed.
Lemma lem3284521 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284522 {A : Type'} (s : A -> Prop) (x' : A) : (term117 A s x') = (s x').
Proof. exact (@lem3284521 (s x')). Qed.
Lemma lem3284523 {A : Type'} (s : A -> Prop) (x' : A) (h1 : s x') : s x'.
Proof. exact (EQ_MP (@lem3284522 A s x') (@lem3284519 A s x' h1)). Qed.
Lemma lem3284526 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3284528 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (term118 A s x').
Proof. exact (@lem3284526 (s x')). Qed.
Lemma lem3284531 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') : term118 A s x'.
Proof. exact (EQ_MP (@lem3284528 A s x') (@lem3284336 A s x' h1)). Qed.
Lemma lem3284534 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (@lem3284531 A s x' h1 (@lem3284523 A s x' h2)). Qed.
Lemma lem3284535 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : term116.
Proof. exact (fun h0 : ~ False => @lem3284534 A s x' h1 h2). Qed.
Lemma lem3284537 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284538 : term116 = False.
Proof. exact (@lem3284537 False). Qed.
Lemma lem3284539 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3284538) (@lem3284535 A s x' h1 h2)). Qed.
Lemma lem3284541 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : t x'.
Proof. exact (proj2 (@lem3284196 A x s t x' h1)). Qed.
Lemma lem3284542 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : term117 A t x'.
Proof. exact (fun h0 : term75 A t x' => @lem3284541 A x s t x' h1). Qed.
Lemma lem3284544 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284545 {A : Type'} (t : A -> Prop) (x' : A) : (term117 A t x') = (t x').
Proof. exact (@lem3284544 (t x')). Qed.
Lemma lem3284546 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term152 A x s t x') : t x'.
Proof. exact (EQ_MP (@lem3284545 A t x') (@lem3284542 A x s t x' h1)). Qed.
Lemma lem3284549 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3284551 {A : Type'} (t : A -> Prop) (x' : A) : (term75 A t x') = (term118 A t x').
Proof. exact (@lem3284549 (t x')). Qed.
Lemma lem3284554 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term118 A t x'.
Proof. exact (EQ_MP (@lem3284551 A t x') (@lem3284344 A t x' h1)). Qed.
Lemma lem3284557 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : False.
Proof. exact (@lem3284554 A t x' h1 (@lem3284546 A x s t x' h2)). Qed.
Lemma lem3284558 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : term116.
Proof. exact (fun h0 : ~ False => @lem3284557 A x s t x' h1 h2). Qed.
Lemma lem3284560 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284561 : term116 = False.
Proof. exact (@lem3284560 False). Qed.
Lemma lem3284562 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284561) (@lem3284558 A x s t x' h1 h2)). Qed.
Lemma lem3284590 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : s x'.
Proof. exact (proj1 (@lem3284205 A x s t x' h1)). Qed.
Lemma lem3284591 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : term117 A s x'.
Proof. exact (fun h0 : term75 A s x' => @lem3284590 A x s t x' h1). Qed.
Lemma lem3284593 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284594 {A : Type'} (s : A -> Prop) (x' : A) : (term117 A s x') = (s x').
Proof. exact (@lem3284593 (s x')). Qed.
Lemma lem3284595 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : s x'.
Proof. exact (EQ_MP (@lem3284594 A s x') (@lem3284591 A x s t x' h1)). Qed.
Lemma lem3284598 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3284600 {A : Type'} (s : A -> Prop) (x' : A) : (term75 A s x') = (term118 A s x').
Proof. exact (@lem3284598 (s x')). Qed.
Lemma lem3284603 {A : Type'} (x : A) (s : A -> Prop) (x' : A) (h1 : term74 A x s x') : term118 A s x'.
Proof. exact (EQ_MP (@lem3284600 A s x') (@lem3284354 A x s x' h1)). Qed.
Lemma lem3284606 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s x') (h2 : term150 A x s t x') : False.
Proof. exact (@lem3284603 A x s x' h1 (@lem3284595 A x s t x' h2)). Qed.
Lemma lem3284607 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s x') (h2 : term150 A x s t x') : term116.
Proof. exact (fun h0 : ~ False => @lem3284606 A x s t x' h1 h2). Qed.
Lemma lem3284609 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284610 : term116 = False.
Proof. exact (@lem3284609 False). Qed.
Lemma lem3284611 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term74 A x s x') (h2 : term150 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284610) (@lem3284607 A x s t x' h1 h2)). Qed.
Lemma lem3284613 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : t x'.
Proof. exact (proj2 (@lem3284205 A x s t x' h1)). Qed.
Lemma lem3284614 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : term117 A t x'.
Proof. exact (fun h0 : term75 A t x' => @lem3284613 A x s t x' h1). Qed.
Lemma lem3284616 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284617 {A : Type'} (t : A -> Prop) (x' : A) : (term117 A t x') = (t x').
Proof. exact (@lem3284616 (t x')). Qed.
Lemma lem3284618 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : t x'.
Proof. exact (EQ_MP (@lem3284617 A t x') (@lem3284614 A x s t x' h1)). Qed.
Lemma lem3284621 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3284623 {A : Type'} (t : A -> Prop) (x' : A) : (term75 A t x') = (term118 A t x').
Proof. exact (@lem3284621 (t x')). Qed.
Lemma lem3284626 {A : Type'} (t : A -> Prop) (x' : A) (h1 : term75 A t x') : term118 A t x'.
Proof. exact (EQ_MP (@lem3284623 A t x') (@lem3284362 A t x' h1)). Qed.
Lemma lem3284629 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : False.
Proof. exact (@lem3284626 A t x' h1 (@lem3284618 A x s t x' h2)). Qed.
Lemma lem3284630 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : term116.
Proof. exact (fun h0 : ~ False => @lem3284629 A x s t x' h1 h2). Qed.
Lemma lem3284632 (p : Prop) : (term114 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3284633 : term116 = False.
Proof. exact (@lem3284632 False). Qed.
Lemma lem3284634 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284633) (@lem3284630 A x s t x' h1 h2)). Qed.
Lemma lem3284635 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284515) (@lem3284512 A s t x' x h1 h2 h3)). Qed.
Lemma lem3284636 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : (term75 A t x) = False.
Proof. exact (prop_ext (fun h4 : term75 A t x => @lem3284493 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284390 A t x h1)). Qed.
Lemma lem3284638 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284636 A s t x' x h1 h2 h3) (@lem3284390 A t x h1)). Qed.
Lemma lem3284639 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3284634 A x s t x' h1 h2) (fun h3 : False => @lem3284362 A t x' h1)). Qed.
Lemma lem3284640 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284639 A x s t x' h1 h2) (@lem3284362 A t x' h1)). Qed.
Lemma lem3284641 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3284562 A x s t x' h1 h2) (fun h3 : False => @lem3284344 A t x' h1)). Qed.
Lemma lem3284642 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284641 A x s t x' h1 h2) (@lem3284344 A t x' h1)). Qed.
Lemma lem3284643 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (term75 A s x') = False.
Proof. exact (prop_ext (fun h3 : term75 A s x' => @lem3284539 A s x' h1 h2) (fun h3 : False => @lem3284336 A s x' h1)). Qed.
Lemma lem3284644 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3284643 A s x' h1 h2) (@lem3284336 A s x' h1)). Qed.
Lemma lem3284645 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3284644 A s x' h1 h2) (fun h3 : False => @lem3284334 A s x' h2)). Qed.
Lemma lem3284646 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3284645 A s x' h1 h2) (@lem3284334 A s x' h2)). Qed.
Lemma lem3284647 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3284635 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284328 A t x' h1)). Qed.
Lemma lem3284648 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284647 A s t x' x h1 h2 h3) (@lem3284328 A t x' h1)). Qed.
Lemma lem3284649 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3284648 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284326 A x' x h3)). Qed.
Lemma lem3284650 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284649 A s t x' x h1 h2 h3) (@lem3284326 A x' x h3)). Qed.
Lemma lem3284651 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3284638 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284318 A x' x h3)). Qed.
Lemma lem3284652 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284651 A s t x' x h1 h2 h3) (@lem3284318 A x' x h3)). Qed.
Lemma lem3284653 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : (term75 A t x) = False.
Proof. exact (prop_ext (fun h4 : term75 A t x => @lem3284652 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284314 A t x h1)). Qed.
Lemma lem3284654 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284653 A s t x' x h1 h2 h3) (@lem3284314 A t x h1)). Qed.
Lemma lem3284655 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3284640 A x s t x' h1 h2) (fun h3 : False => @lem3284312 A t x' h1)). Qed.
Lemma lem3284656 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284655 A x s t x' h1 h2) (@lem3284312 A t x' h1)). Qed.
Lemma lem3284657 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3284642 A x s t x' h1 h2) (fun h3 : False => @lem3284276 A t x' h1)). Qed.
Lemma lem3284658 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284657 A x s t x' h1 h2) (@lem3284276 A t x' h1)). Qed.
Lemma lem3284659 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (term75 A s x') = False.
Proof. exact (prop_ext (fun h3 : term75 A s x' => @lem3284646 A s x' h1 h2) (fun h3 : False => @lem3284260 A s x' h1)). Qed.
Lemma lem3284660 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3284659 A s x' h1 h2) (@lem3284260 A s x' h1)). Qed.
Lemma lem3284661 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3284660 A s x' h1 h2) (fun h3 : False => @lem3284256 A s x' h2)). Qed.
Lemma lem3284662 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3284661 A s x' h1 h2) (@lem3284256 A s x' h2)). Qed.
Lemma lem3284663 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3284650 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284244 A t x' h1)). Qed.
Lemma lem3284664 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284663 A s t x' x h1 h2 h3) (@lem3284244 A t x' h1)). Qed.
Lemma lem3284665 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3284664 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284240 A x' x h3)). Qed.
Lemma lem3284666 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284665 A s t x' x h1 h2 h3) (@lem3284240 A x' x h3)). Qed.
Lemma lem3284667 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3284654 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284224 A x' x h3)). Qed.
Lemma lem3284668 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284667 A s t x' x h1 h2 h3) (@lem3284224 A x' x h3)). Qed.
Lemma lem3284669 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : (term75 A t x) = False.
Proof. exact (prop_ext (fun h4 : term75 A t x => @lem3284668 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284216 A t x h1)). Qed.
Lemma lem3284670 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284669 A s t x' x h1 h2 h3) (@lem3284216 A t x h1)). Qed.
Lemma lem3284671 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3284656 A x s t x' h1 h2) (fun h3 : False => @lem3284312 A t x' h1)). Qed.
Lemma lem3284672 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term150 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284671 A x s t x' h1 h2) (@lem3284312 A t x' h1)). Qed.
Lemma lem3284673 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : (term75 A t x') = False.
Proof. exact (prop_ext (fun h3 : term75 A t x' => @lem3284658 A x s t x' h1 h2) (fun h3 : False => @lem3284276 A t x' h1)). Qed.
Lemma lem3284674 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x') (h2 : term152 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284673 A x s t x' h1 h2) (@lem3284276 A t x' h1)). Qed.
Lemma lem3284675 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (term75 A s x') = False.
Proof. exact (prop_ext (fun h3 : term75 A s x' => @lem3284662 A s x' h1 h2) (fun h3 : False => @lem3284260 A s x' h1)). Qed.
Lemma lem3284676 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3284675 A s x' h1 h2) (@lem3284260 A s x' h1)). Qed.
Lemma lem3284677 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : (s x') = False.
Proof. exact (prop_ext (fun h3 : s x' => @lem3284676 A s x' h1 h2) (fun h3 : False => @lem3284256 A s x' h2)). Qed.
Lemma lem3284678 {A : Type'} (s : A -> Prop) (x' : A) (h1 : term75 A s x') (h2 : s x') : False.
Proof. exact (EQ_MP (@lem3284677 A s x' h1 h2) (@lem3284256 A s x' h2)). Qed.
Lemma lem3284679 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : (term75 A t x') = False.
Proof. exact (prop_ext (fun h4 : term75 A t x' => @lem3284666 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284244 A t x' h1)). Qed.
Lemma lem3284680 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284679 A s t x' x h1 h2 h3) (@lem3284244 A t x' h1)). Qed.
Lemma lem3284681 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3284680 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284240 A x' x h3)). Qed.
Lemma lem3284682 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x') (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284681 A s t x' x h1 h2 h3) (@lem3284240 A x' x h3)). Qed.
Lemma lem3284683 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : (x' = x) = False.
Proof. exact (prop_ext (fun h4 : x' = x => @lem3284670 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284224 A x' x h3)). Qed.
Lemma lem3284684 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284683 A s t x' x h1 h2 h3) (@lem3284224 A x' x h3)). Qed.
Lemma lem3284685 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : (term75 A t x) = False.
Proof. exact (prop_ext (fun h4 : term75 A t x => @lem3284684 A s t x' x h1 h2 h3) (fun h4 : False => @lem3284216 A t x h1)). Qed.
Lemma lem3284686 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (EQ_MP (@lem3284685 A s t x' x h1 h2 h3) (@lem3284216 A t x h1)). Qed.
Lemma lem3284687 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term150 A x s t x') : False.
Proof. exact (or_elim (@lem3284206 A x s t x' h1) (fun h0 : term74 A x s x' => @lem3284611 A x s t x' h0 h1) (fun h0 : term75 A t x' => @lem3284672 A x s t x' h0 h1)). Qed.
Lemma lem3284688 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : s x') (h2 : term152 A x s t x') : False.
Proof. exact (or_elim (@lem3284195 A x s t x' h2) (fun h0 : term75 A s x' => @lem3284678 A s x' h0 h1) (fun h0 : term75 A t x' => @lem3284674 A x s t x' h0 h2)). Qed.
Lemma lem3284689 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x' : A) (x : A) (h1 : term75 A t x) (h2 : term152 A x s t x') (h3 : x' = x) : False.
Proof. exact (or_elim (@lem3284195 A x s t x' h2) (fun h0 : term75 A s x' => @lem3284686 A s t x' x h1 h2 h3) (fun h0 : term75 A t x' => @lem3284682 A s t x' x h0 h2 h3)). Qed.
Lemma lem3284690 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term152 A x s t x') : False.
Proof. exact (or_elim (@lem3284198 A x s t x' h2) (fun h0 : x' = x => @lem3284689 A s t x' x h1 h2 h0) (fun h0 : s x' => @lem3284688 A x s t x' h0 h2)). Qed.
Lemma lem3284691 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term148 A x s t x') : False.
Proof. exact (or_elim (@lem3284192 A x s t x' h2) (fun h0 : term152 A x s t x' => @lem3284690 A x s t x' h1 h0) (fun h0 : term150 A x s t x' => @lem3284687 A x s t x' h0)). Qed.
Lemma lem3284692 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term148 A x s t x') : (term75 A t x) = False.
Proof. exact (prop_ext (fun h3 : term75 A t x => @lem3284691 A x s t x' h1 h2) (fun h3 : False => @lem3284120 A t x h1)). Qed.
Lemma lem3284693 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term148 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284692 A x s t x' h1 h2) (@lem3284120 A t x h1)). Qed.
Lemma lem3284694 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term148 A x s t x') : (term75 A t x) = False.
Proof. exact (prop_ext (fun h3 : term75 A t x => @lem3284693 A x s t x' h1 h2) (fun h3 : False => @lem3284064 A t x h1)). Qed.
Lemma lem3284695 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term148 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284694 A x s t x' h1 h2) (@lem3284064 A t x h1)). Qed.
Lemma lem3284696 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term148 A x s t x') : (term148 A x s t x') = False.
Proof. exact (prop_ext (fun h3 : term148 A x s t x' => @lem3284695 A x s t x' h1 h2) (fun h3 : False => @lem3284058 A x s t x' h2)). Qed.
Lemma lem3284697 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (x' : A) (h1 : term75 A t x) (h2 : term148 A x s t x') : False.
Proof. exact (EQ_MP (@lem3284696 A x s t x' h1 h2) (@lem3284058 A x s t x' h2)). Qed.
Lemma lem3284698 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term75 A t x) : term147 A x s t x'.
Proof. exact (fun h0 : term148 A x s t x' => @lem3284697 A x s t x' h1 h0). Qed.
Lemma lem3284699 {A : Type'} (s : A -> Prop) (x' : A) (t : A -> Prop) (x : A) (h1 : term75 A t x) : (term38 A x s t x') = (term45 A s t x').
Proof. exact (EQ_MP (@lem3284057 A x s t x') (@lem3284698 A s x' t x h1)). Qed.
Lemma lem3284704 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) (h1 : term75 A t x) : term127 A x s t.
Proof. exact (fun x' : A => @lem3284699 A s x' t x h1). Qed.
Lemma lem3284705 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term128 A x s t.
Proof. exact (fun h0 : term75 A t x => @lem3284704 A s t x h0). Qed.
Lemma lem3284710 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term138 A s t.
Proof. exact (fun x : A => @lem3284705 A x s t). Qed.
Lemma lem3284715 {A : Type'} (t : A -> Prop) : term142 A t.
Proof. exact (fun s : A -> Prop => @lem3284710 A s t). Qed.
Lemma lem3284720 {A : Type'} : term146 A.
Proof. exact (fun t : A -> Prop => @lem3284715 A t). Qed.
Lemma lem3284721 {A : Type'} : term145 A.
Proof. exact (EQ_MP (@lem3284052 A) (@lem3284720 A)). Qed.
Lemma lem3284722 {A : Type'} (t : A -> Prop) : term157 A t.
Proof. exact (@lem3284721 A t). Qed.
Lemma lem3284723 {A : Type'} (t : A -> Prop) : (term157 A t) = (term141 A t).
Proof. exact (eq_refl (term157 A t)). Qed.
Lemma lem3284724 {A : Type'} (t : A -> Prop) : term141 A t.
Proof. exact (EQ_MP (@lem3284723 A t) (@lem3284722 A t)). Qed.
Lemma lem3284725 {A : Type'} (t : A -> Prop) (s : A -> Prop) : term158 A t s.
Proof. exact (@lem3284724 A t s). Qed.
Lemma lem3284726 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (term158 A t s) = (term137 A s t).
Proof. exact (eq_refl (term158 A t s)). Qed.
Lemma lem3284727 {A : Type'} (s : A -> Prop) (t : A -> Prop) : term137 A s t.
Proof. exact (EQ_MP (@lem3284726 A s t) (@lem3284725 A t s)). Qed.
Lemma lem3284728 {A : Type'} (s : A -> Prop) (t : A -> Prop) (x : A) : term159 A s t x.
Proof. exact (@lem3284727 A s t x). Qed.
Lemma lem3284729 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term159 A s t x) = (term129 A x s t).
Proof. exact (eq_refl (term159 A s t x)). Qed.
Lemma lem3284730 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term129 A x s t.
Proof. exact (EQ_MP (@lem3284729 A x s t) (@lem3284728 A s t x)). Qed.
Lemma lem3284732 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term129 A x s t.
Proof. exact (@lem3283925 A x s t (@lem3284730 A x s t)). Qed.
Lemma lem3284733 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term130 A x s t) : False.
Proof. exact (@lem3284732 A x s t (@lem3283909 A x s t h1)). Qed.
Lemma lem3284734 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term130 A x s t) : (term130 A x s t) = False.
Proof. exact (prop_ext (fun h2 : term130 A x s t => @lem3284733 A x s t h1) (fun h2 : False => @lem3283909 A x s t h1)). Qed.
Lemma lem3284735 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) (h1 : term130 A x s t) : False.
Proof. exact (EQ_MP (@lem3284734 A x s t h1) (@lem3283909 A x s t h1)). Qed.
Lemma lem3284736 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term129 A x s t.
Proof. exact (fun h0 : term130 A x s t => @lem3284735 A x s t h0). Qed.
Lemma lem3284737 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term128 A x s t.
Proof. exact (EQ_MP (@lem3283908 A x s t) (@lem3284736 A x s t)). Qed.
Lemma lem3284738 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term123 A x s t.
Proof. exact (EQ_MP (@lem3283904 A x s t) (@lem3284737 A x s t)). Qed.
Lemma lem3284739 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term12 A x s t.
Proof. exact (EQ_MP (@lem3283819 A x s t) (@lem3284738 A x s t)). Qed.
Lemma lem3284742 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term9 A x s t) = (@INTER A s t).
Proof. exact (@lem3284739 A x s t (@lem3282415 A x t h1)). Qed.
Lemma lem3284743 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term23 A x t) = ((term9 A x s t) = (@INTER A s t)).
Proof. exact (prop_ext (fun h2 : term23 A x t => @lem3284742 A s x t h1) (fun h2 : (term9 A x s t) = (@INTER A s t) => @lem3282415 A x t h1)). Qed.
Lemma lem3284744 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : term23 A x t) : (term9 A x s t) = (@INTER A s t).
Proof. exact (EQ_MP (@lem3284743 A s x t h1) (@lem3282415 A x t h1)). Qed.
Lemma lem3284745 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term12 A x s t.
Proof. exact (fun h0 : term23 A x t => @lem3284744 A s x t h0). Qed.
Lemma lem3284746 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (term9 A x s t) = (term7 A x s t).
Proof. exact (@lem3283798 A x s t (@lem3282398 A x t h1)). Qed.
Lemma lem3284747 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (@IN A x t) = ((term9 A x s t) = (term7 A x s t)).
Proof. exact (prop_ext (fun h2 : @IN A x t => @lem3284746 A s x t h1) (fun h2 : (term9 A x s t) = (term7 A x s t) => @lem3282398 A x t h1)). Qed.
Lemma lem3284748 {A : Type'} (s : A -> Prop) (x : A) (t : A -> Prop) (h1 : @IN A x t) : (term9 A x s t) = (term7 A x s t).
Proof. exact (EQ_MP (@lem3284747 A s x t h1) (@lem3282398 A x t h1)). Qed.
Lemma lem3284749 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term16 A x s t.
Proof. exact (fun h0 : @IN A x t => @lem3284748 A s x t h0). Qed.
Lemma lem3284750 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : term19 A x s t.
Proof. exact (conj (@lem3284749 A x s t) (@lem3284745 A x s t)). Qed.
Lemma lem3284751 {A : Type'} (x : A) (s : A -> Prop) (t : A -> Prop) : (term9 A x s t) = (term20 A x s t).
Proof. exact (EQ_MP (@lem3282397 A x s t) (@lem3284750 A x s t)). Qed.
Lemma lem3284756 {A : Type'} (x : A) (s : A -> Prop) : term160 A x s.
Proof. exact (fun t : A -> Prop => @lem3284751 A x s t). Qed.
Lemma lem3284761 {A : Type'} (x : A) : term161 A x.
Proof. exact (fun s : A -> Prop => @lem3284756 A x s). Qed.
Lemma lem3284766 {A : Type'} : term162 A.
Proof. exact (fun x : A => @lem3284761 A x). Qed.
