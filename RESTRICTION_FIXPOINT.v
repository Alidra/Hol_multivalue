Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import RESTRICTION_FIXPOINT_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import FUN_EQ_THM_spec.
Require Import IN_EXTENSIONAL_spec.
Require Import RESTRICTION_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17646_spec.
Require Import thm1832_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm20425_spec.
Require Import thm20611_spec.
Require Import thm20612_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Lemma lem4388371 {A B : Type'} (s : A -> Prop) : term0 A B s.
Proof. exact (@lem4386626 A B s). Qed.
Lemma lem4388372 {A B : Type'} (s : A -> Prop) : (term0 A B s) = (term1 A B s).
Proof. exact (eq_refl (term0 A B s)). Qed.
Lemma lem4388373 {A B : Type'} (s : A -> Prop) : term1 A B s.
Proof. exact (EQ_MP (@lem4388372 A B s) (@lem4388371 A B s)). Qed.
Lemma lem4388374 {A B : Type'} (s : A -> Prop) (f : A -> B) : term2 A B s f.
Proof. exact (@lem4388373 A B s f). Qed.
Lemma lem4388375 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term2 A B s f) = (term3 A B s f).
Proof. exact (eq_refl (term2 A B s f)). Qed.
Lemma lem4388376 {A B : Type'} (s : A -> Prop) (f : A -> B) : term3 A B s f.
Proof. exact (EQ_MP (@lem4388375 A B s f) (@lem4388374 A B s f)). Qed.
Lemma lem4388377 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term4 A B s f x.
Proof. exact (@lem4388376 A B s f x). Qed.
Lemma lem4388378 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term4 A B s f x) = ((@RESTRICTION A B s f x) = (term5 A B s f x)).
Proof. exact (eq_refl (term4 A B s f x)). Qed.
Lemma lem4388380 {A B : Type'} (f : A -> B) : term6 A B f.
Proof. exact (@lem9220 A B f). Qed.
Lemma lem4388381 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (eq_refl (term6 A B f)). Qed.
Lemma lem4388382 {A B : Type'} (f : A -> B) : term7 A B f.
Proof. exact (EQ_MP (@lem4388381 A B f) (@lem4388380 A B f)). Qed.
Lemma lem4388383 {A B : Type'} (f : A -> B) (g : A -> B) : term8 A B f g.
Proof. exact (@lem4388382 A B f g). Qed.
Lemma lem4388384 {A B : Type'} (f : A -> B) (g : A -> B) : (term8 A B f g) = ((f = g) = (term9 A B f g)).
Proof. exact (eq_refl (term8 A B f g)). Qed.
Lemma lem4388386 {A B : Type'} (s : A -> Prop) : term10 A B s.
Proof. exact (@lem4382932 A B s). Qed.
Lemma lem4388387 {A B : Type'} (s : A -> Prop) : (term10 A B s) = (term11 A B s).
Proof. exact (eq_refl (term10 A B s)). Qed.
Lemma lem4388388 {A B : Type'} (s : A -> Prop) : term11 A B s.
Proof. exact (EQ_MP (@lem4388387 A B s) (@lem4388386 A B s)). Qed.
Lemma lem4388389 {A B : Type'} (s : A -> Prop) (f : A -> B) : term12 A B s f.
Proof. exact (@lem4388388 A B s f). Qed.
Lemma lem4388390 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term12 A B s f) = ((term13 A B f s) = (term14 A B s f)).
Proof. exact (eq_refl (term12 A B s f)). Qed.
Lemma lem4388407 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (EQ_MP (@lem4388384 A B f g) (@lem4388383 A B f g)). Qed.
Lemma lem4388408 {A B : Type'} (f : A -> B) (g : A -> B) : (f = g) = (term9 A B f g).
Proof. exact (@lem4388407 A B f g). Qed.
Lemma lem4388409 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((@RESTRICTION A B s f) = f) = (term15 A B s f).
Proof. exact (@lem4388408 A B (@RESTRICTION A B s f) f). Qed.
Lemma lem4388419 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (EQ_MP (@lem4388378 A B s f x) (@lem4388377 A B s f x)). Qed.
Lemma lem4388420 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (@RESTRICTION A B s f x) = (term5 A B s f x).
Proof. exact (@lem4388419 A B s f x). Qed.
Lemma lem4388421 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4388422 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term16 A B s f x) = (term17 A B s f x).
Proof. exact (MK_COMB (@lem4388421 B) (@lem4388420 A B s f x)). Qed.
Lemma lem4388423 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4388424 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((@RESTRICTION A B s f x) = (f x)) = ((term5 A B s f x) = (f x)).
Proof. exact (MK_COMB (@lem4388422 A B s f x) (@lem4388423 A B f x)). Qed.
Lemma lem4388429 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term18 A B s f) = (term19 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388424 A B s f x)). Qed.
Lemma lem4388430 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4388431 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term15 A B s f) = (term20 A B s f).
Proof. exact (MK_COMB (@lem4388430 A) (@lem4388429 A B s f)). Qed.
Lemma lem4388436 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((@RESTRICTION A B s f) = f) = (term20 A B s f).
Proof. exact (TRANS (@lem4388409 A B s f) (@lem4388431 A B s f)). Qed.
Lemma lem4388437 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4388438 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term21 A B s f) = (term22 A B s f).
Proof. exact (MK_COMB (@lem4388437) (@lem4388436 A B s f)). Qed.
Lemma lem4388440 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term13 A B f s) = (term14 A B s f).
Proof. exact (EQ_MP (@lem4388390 A B s f) (@lem4388389 A B s f)). Qed.
Lemma lem4388441 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term13 A B f s) = (term14 A B s f).
Proof. exact (@lem4388440 A B s f). Qed.
Lemma lem4388452 {A B : Type'} (s : A -> Prop) (f : A -> B) : (((@RESTRICTION A B s f) = f) = (term13 A B f s)) = ((term20 A B s f) = (term14 A B s f)).
Proof. exact (MK_COMB (@lem4388438 A B s f) (@lem4388441 A B s f)). Qed.
Lemma lem4388457 {A B : Type'} (s : A -> Prop) : (term23 A B s) = (term24 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4388452 A B s f)). Qed.
Lemma lem4388458 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4388459 {A B : Type'} (s : A -> Prop) : (term25 A B s) = (term26 A B s).
Proof. exact (MK_COMB (@lem4388458 A B) (@lem4388457 A B s)). Qed.
Lemma lem4388464 {A B : Type'} : (term27 A B) = (term28 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4388459 A B s)). Qed.
Lemma lem4388465 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4388466 {A B : Type'} : (term29 A B) = (term30 A B).
Proof. exact (MK_COMB (@lem4388465 A) (@lem4388464 A B)). Qed.
Lemma lem4388471 {A B : Type'} : (term30 A B) = (term29 A B).
Proof. exact (SYM (@lem4388466 A B)). Qed.
Lemma lem4388473 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4388474 {A B : Type'} : (term30 A B) = (term32 A B).
Proof. exact (@lem4388473 (term30 A B)). Qed.
Lemma lem4388475 {A B : Type'} : (term32 A B) = (term30 A B).
Proof. exact (SYM (@lem4388474 A B)). Qed.
Lemma lem4388476 {A B : Type'} (h1 : term33 A B) : term33 A B.
Proof. exact (h1). Qed.
Lemma lem4388479 {A B : Type'} (h1 : term32 A B) : term32 A B.
Proof. exact (h1). Qed.
Lemma lem4388480 {A B : Type'} : term34 A B.
Proof. exact (fun h0 : term32 A B => @lem4388479 A B h0). Qed.
Lemma lem4388481 {A B : Type'} (h1 : term34 A B) : term34 A B.
Proof. exact (h1). Qed.
Lemma lem4388482 {A B : Type'} (h1 : term32 A B) : term32 A B.
Proof. exact (h1). Qed.
Lemma lem4388483 {A B : Type'} (h1 : term32 A B) (h2 : term34 A B) : term32 A B.
Proof. exact (@lem4388481 A B h2 (@lem4388482 A B h1)). Qed.
Lemma lem4388484 {A B : Type'} (h1 : term32 A B) : term35 A B.
Proof. exact (fun h0 : term34 A B => @lem4388483 A B h1 h0). Qed.
Lemma lem4388485 {A B : Type'} (h1 : term34 A B) : term34 A B.
Proof. exact (h1). Qed.
Lemma lem4388486 {A B : Type'} (h1 : term32 A B) (h2 : term34 A B) : term32 A B.
Proof. exact (@lem4388484 A B h1 (@lem4388485 A B h2)). Qed.
Lemma lem4388487 {A B : Type'} (h1 : term34 A B) : term34 A B.
Proof. exact (fun h0 : term32 A B => @lem4388486 A B h0 h1). Qed.
Lemma lem4388488 {A B : Type'} : term36 A B.
Proof. exact (fun h0 : term34 A B => @lem4388487 A B h0). Qed.
Lemma lem4388491 {A B : Type'} : term34 A B.
Proof. exact (@lem4388488 A B (@lem4388480 A B)). Qed.
Lemma lem4388492 {A B : Type'} : term34 A B.
Proof. exact (@lem4388491 A B). Qed.
Lemma lem4388494 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem4388495 {A B : Type'} : (term32 A B) = (term37 A B).
Proof. exact (@lem4388494 (term33 A B)). Qed.
Lemma lem4388497 (t : Prop) : (term38 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem4388498 {A B : Type'} : (term37 A B) = (term30 A B).
Proof. exact (@lem4388497 (term30 A B)). Qed.
Lemma lem4388521 {A B : Type'} : (term32 A B) = (term30 A B).
Proof. exact (TRANS (@lem4388495 A B) (@lem4388498 A B)). Qed.
Lemma lem4388528 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term39 A B s f x) = (term39 A B s f x).
Proof. exact (eq_refl (term39 A B s f x)). Qed.
Lemma lem4388529 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term40 A B s f) = (term40 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388528 A B s f x)). Qed.
Lemma lem4388530 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4388531 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B s f) = (term14 A B s f).
Proof. exact (MK_COMB (@lem4388530 A) (@lem4388529 A B s f)). Qed.
Lemma lem4388535 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (@IN A x s) = False.
Proof. exact (h1). Qed.
Lemma lem4388536 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4388537 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term41 A B x s) = (@COND B False).
Proof. exact (MK_COMB (@lem4388536 B) (@lem4388535 A x s h1)). Qed.
Lemma lem4388538 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4388539 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term42 A B s f x) = (term43 A B f x).
Proof. exact (MK_COMB (@lem4388537 A B x s h1) (@lem4388538 A B f x)). Qed.
Lemma lem4388540 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4388541 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term5 A B s f x) = (term44 A B f x).
Proof. exact (MK_COMB (@lem4388539 A B f x s h1) (@lem4388540 B)). Qed.
Lemma lem4388543 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4388544 {B : Type'} (t1 : B) (t2 : B) : (@COND B False t1 t2) = t2.
Proof. exact (@lem4388543 B t1 t2). Qed.
Lemma lem4388545 {A B : Type'} (f : A -> B) (x : A) : (term44 A B f x) = (@ARB B).
Proof. exact (@lem4388544 B (f x) (@ARB B)). Qed.
Lemma lem4388546 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term5 A B s f x) = (@ARB B).
Proof. exact (TRANS (@lem4388541 A B f x s h1) (@lem4388545 A B f x)). Qed.
Lemma lem4388547 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4388548 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : (term17 A B s f x) = (@eq B (@ARB B)).
Proof. exact (MK_COMB (@lem4388547 B) (@lem4388546 A B f x s h1)). Qed.
Lemma lem4388549 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4388550 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = False) : ((term5 A B s f x) = (f x)) = ((@ARB B) = (f x)).
Proof. exact (MK_COMB (@lem4388548 A B f x s h1) (@lem4388549 A B f x)). Qed.
Lemma lem4388553 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term45 A B s f x.
Proof. exact (fun h0 : (@IN A x s) = False => @lem4388550 A B f x s h0). Qed.
Lemma lem4388555 {A : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (@IN A x s) = True.
Proof. exact (h1). Qed.
Lemma lem4388556 {B : Type'} : (@COND B) = (@COND B).
Proof. exact (eq_refl (@COND B)). Qed.
Lemma lem4388557 {A B : Type'} (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term41 A B x s) = (@COND B True).
Proof. exact (MK_COMB (@lem4388556 B) (@lem4388555 A x s h1)). Qed.
Lemma lem4388558 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4388559 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term42 A B s f x) = (term46 A B f x).
Proof. exact (MK_COMB (@lem4388557 A B x s h1) (@lem4388558 A B f x)). Qed.
Lemma lem4388560 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (eq_refl (@ARB B)). Qed.
Lemma lem4388561 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term5 A B s f x) = (term47 A B f x).
Proof. exact (MK_COMB (@lem4388559 A B f x s h1) (@lem4388560 B)). Qed.
Lemma lem4388563 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem4388564 {B : Type'} (t2 : B) (t1 : B) : (@COND B True t1 t2) = t1.
Proof. exact (@lem4388563 B t2 t1). Qed.
Lemma lem4388565 {A B : Type'} (f : A -> B) (x : A) : (term47 A B f x) = (f x).
Proof. exact (@lem4388564 B (@ARB B) (f x)). Qed.
Lemma lem4388566 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term5 A B s f x) = (f x).
Proof. exact (TRANS (@lem4388561 A B f x s h1) (@lem4388565 A B f x)). Qed.
Lemma lem4388567 {B : Type'} : (@eq B) = (@eq B).
Proof. exact (eq_refl (@eq B)). Qed.
Lemma lem4388568 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : (term17 A B s f x) = (term48 A B f x).
Proof. exact (MK_COMB (@lem4388567 B) (@lem4388566 A B f x s h1)). Qed.
Lemma lem4388569 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (eq_refl (f x)). Qed.
Lemma lem4388570 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term5 A B s f x) = (f x)) = ((f x) = (f x)).
Proof. exact (MK_COMB (@lem4388568 A B f x s h1) (@lem4388569 A B f x)). Qed.
Lemma lem4388572 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4388573 {B : Type'} (x : B) : (x = x) = True.
Proof. exact (@lem4388572 B x). Qed.
Lemma lem4388574 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (f x)) = True.
Proof. exact (@lem4388573 B (f x)). Qed.
Lemma lem4388575 {A B : Type'} (f : A -> B) (x : A) (s : A -> Prop) (h1 : (@IN A x s) = True) : ((term5 A B s f x) = (f x)) = True.
Proof. exact (TRANS (@lem4388570 A B f x s h1) (@lem4388574 A B f x)). Qed.
Lemma lem4388576 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term49 A B s f x.
Proof. exact (fun h0 : (@IN A x s) = True => @lem4388575 A B f x s h0). Qed.
Lemma lem4388577 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term50 A B s f x.
Proof. exact (conj (@lem4388553 A B s f x) (@lem4388576 A B s f x)). Qed.
Lemma lem4388579 (x : Prop) (x1 : Prop) (b : Prop) (x0 : Prop) : term51 x x1 b x0.
Proof. exact (or_elim (@lem20425 b) (fun h0 : b = True => @lem20612 x x1 x0 b h0) (fun h0 : b = False => @lem20611 x x1 x0 b h0)). Qed.
Lemma lem4388580 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : term52 A B s f x.
Proof. exact (@lem4388579 ((term5 A B s f x) = (f x)) True (@IN A x s) ((@ARB B) = (f x))). Qed.
Lemma lem4388581 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term5 A B s f x) = (f x)) = (term53 A B s f x).
Proof. exact (@lem4388580 A B s f x (@lem4388577 A B s f x)). Qed.
Lemma lem4388584 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term54 A B s f x) = (term54 A B s f x).
Proof. exact (eq_refl (term54 A B s f x)). Qed.
Lemma lem4388586 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem4388587 {A : Type'} (x : A) (s : A -> Prop) : (term55 A x s) = True.
Proof. exact (@lem4388586 (term56 A x s)). Qed.
Lemma lem4388588 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4388589 {A : Type'} (x : A) (s : A -> Prop) : (term57 A x s) = (and True).
Proof. exact (MK_COMB (@lem4388588) (@lem4388587 A x s)). Qed.
Lemma lem4388590 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term53 A B s f x) = (term58 A B s f x).
Proof. exact (MK_COMB (@lem4388589 A x s) (@lem4388584 A B s f x)). Qed.
Lemma lem4388592 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4388593 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term58 A B s f x) = (term54 A B s f x).
Proof. exact (@lem4388592 (term54 A B s f x)). Qed.
Lemma lem4388594 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term53 A B s f x) = (term54 A B s f x).
Proof. exact (TRANS (@lem4388590 A B s f x) (@lem4388593 A B s f x)). Qed.
Lemma lem4388603 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : ((term5 A B s f x) = (f x)) = (term54 A B s f x).
Proof. exact (TRANS (@lem4388581 A B s f x) (@lem4388594 A B s f x)). Qed.
Lemma lem4388604 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term19 A B s f) = (term59 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388603 A B s f x)). Qed.
Lemma lem4388605 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4388606 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term20 A B s f) = (term60 A B s f).
Proof. exact (MK_COMB (@lem4388605 A) (@lem4388604 A B s f)). Qed.
Lemma lem4388607 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4388608 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term22 A B s f) = (term61 A B s f).
Proof. exact (MK_COMB (@lem4388607) (@lem4388606 A B s f)). Qed.
Lemma lem4388609 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term20 A B s f) = (term14 A B s f)) = ((term60 A B s f) = (term14 A B s f)).
Proof. exact (MK_COMB (@lem4388608 A B s f) (@lem4388531 A B s f)). Qed.
Lemma lem4388610 {A B : Type'} (s : A -> Prop) : (term24 A B s) = (term62 A B s).
Proof. exact (fun_ext (fun f : A -> B => @lem4388609 A B s f)). Qed.
Lemma lem4388611 {A B : Type'} : (@all (A -> B)) = (@all (A -> B)).
Proof. exact (eq_refl (@all (A -> B))). Qed.
Lemma lem4388612 {A B : Type'} (s : A -> Prop) : (term26 A B s) = (term63 A B s).
Proof. exact (MK_COMB (@lem4388611 A B) (@lem4388610 A B s)). Qed.
Lemma lem4388613 {A B : Type'} : (term28 A B) = (term64 A B).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4388612 A B s)). Qed.
Lemma lem4388614 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4388615 {A B : Type'} : (term30 A B) = (term65 A B).
Proof. exact (MK_COMB (@lem4388614 A) (@lem4388613 A B)). Qed.
Lemma lem4388646 {A B : Type'} : (term32 A B) = (term65 A B).
Proof. exact (TRANS (@lem4388521 A B) (@lem4388615 A B)). Qed.
Lemma lem4388647 {A B : Type'} : (term65 A B) = (term32 A B).
Proof. exact (SYM (@lem4388646 A B)). Qed.
Lemma lem4388649 (p : Prop) : p = (term31 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem4388650 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term60 A B s f) = (term14 A B s f)) = (term66 A B s f).
Proof. exact (@lem4388649 ((term60 A B s f) = (term14 A B s f))). Qed.
Lemma lem4388651 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term66 A B s f) = ((term60 A B s f) = (term14 A B s f)).
Proof. exact (SYM (@lem4388650 A B s f)). Qed.
Lemma lem4388652 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term67 A B s f) : term67 A B s f.
Proof. exact (h1). Qed.
Lemma lem4388661 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term68 A B s f x) = (term69 A B s f x).
Proof. exact (@lem17160 (@IN A x s) ((@ARB B) = (f x))). Qed.
Lemma lem4388664 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term54 A B s f x) = (term54 A B s f x).
Proof. exact (eq_refl (term54 A B s f x)). Qed.
Lemma lem4388665 {A : Type'} (P : A -> Prop) : (term70 A P) = (term71 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4388666 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term72 A B s f) = (term73 A B s f).
Proof. exact (@lem4388665 A (term59 A B s f)). Qed.
Lemma lem4388667 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term74 A B s f x) = (term54 A B s f x).
Proof. exact (eq_refl (term74 A B s f x)). Qed.
Lemma lem4388668 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4388669 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term75 A B s f x) = (term68 A B s f x).
Proof. exact (MK_COMB (@lem4388668) (@lem4388667 A B s f x)). Qed.
Lemma lem4388670 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term75 A B s f x) = (term69 A B s f x).
Proof. exact (TRANS (@lem4388669 A B s f x) (@lem4388661 A B s f x)). Qed.
Lemma lem4388671 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term76 A B s f) = (term77 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388670 A B s f x)). Qed.
Lemma lem4388672 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388673 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term73 A B s f) = (term78 A B s f).
Proof. exact (MK_COMB (@lem4388672 A) (@lem4388671 A B s f)). Qed.
Lemma lem4388674 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term72 A B s f) = (term78 A B s f).
Proof. exact (TRANS (@lem4388666 A B s f) (@lem4388673 A B s f)). Qed.
Lemma lem4388675 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term59 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388664 A B s f x)). Qed.
Lemma lem4388676 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4388677 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term60 A B s f) = (term60 A B s f).
Proof. exact (MK_COMB (@lem4388676 A) (@lem4388675 A B s f)). Qed.
Lemma lem4388681 {A : Type'} (x : A) (s : A -> Prop) : (term79 A x s) = (@IN A x s).
Proof. exact (@lem16933 (@IN A x s)). Qed.
Lemma lem4388683 {A B : Type'} (f : A -> B) (x : A) : ((f x) = (@ARB B)) = ((f x) = (@ARB B)).
Proof. exact (eq_refl ((f x) = (@ARB B))). Qed.
Lemma lem4388688 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term80 A B s f x) = (term81 A B s f x).
Proof. exact (@lem17362 (term56 A x s) ((f x) = (@ARB B))). Qed.
Lemma lem4388689 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4388690 {A : Type'} (x : A) (s : A -> Prop) : (term82 A x s) = (term83 A x s).
Proof. exact (MK_COMB (@lem4388689) (@lem4388681 A x s)). Qed.
Lemma lem4388691 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term84 A B s f x) = (term85 A B s f x).
Proof. exact (MK_COMB (@lem4388690 A x s) (@lem4388683 A B f x)). Qed.
Lemma lem4388692 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term39 A B s f x) = (term84 A B s f x).
Proof. exact (@lem17265 (term56 A x s) ((f x) = (@ARB B))). Qed.
Lemma lem4388693 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term39 A B s f x) = (term85 A B s f x).
Proof. exact (TRANS (@lem4388692 A B s f x) (@lem4388691 A B s f x)). Qed.
Lemma lem4388694 {A : Type'} (P : A -> Prop) : (term70 A P) = (term71 A P).
Proof. exact (@lem18392 A P). Qed.
Lemma lem4388695 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term86 A B s f) = (term87 A B s f).
Proof. exact (@lem4388694 A (term40 A B s f)). Qed.
Lemma lem4388696 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term88 A B s f x) = (term39 A B s f x).
Proof. exact (eq_refl (term88 A B s f x)). Qed.
Lemma lem4388697 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem4388698 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term89 A B s f x) = (term80 A B s f x).
Proof. exact (MK_COMB (@lem4388697) (@lem4388696 A B s f x)). Qed.
Lemma lem4388699 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term89 A B s f x) = (term81 A B s f x).
Proof. exact (TRANS (@lem4388698 A B s f x) (@lem4388688 A B s f x)). Qed.
Lemma lem4388700 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term90 A B s f) = (term91 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388699 A B s f x)). Qed.
Lemma lem4388701 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388702 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term87 A B s f) = (term92 A B s f).
Proof. exact (MK_COMB (@lem4388701 A) (@lem4388700 A B s f)). Qed.
Lemma lem4388703 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term86 A B s f) = (term92 A B s f).
Proof. exact (TRANS (@lem4388695 A B s f) (@lem4388702 A B s f)). Qed.
Lemma lem4388704 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term40 A B s f) = (term93 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388693 A B s f x)). Qed.
Lemma lem4388705 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4388706 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term14 A B s f) = (term94 A B s f).
Proof. exact (MK_COMB (@lem4388705 A) (@lem4388704 A B s f)). Qed.
Lemma lem4388707 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4388708 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term95 A B s f) = (term96 A B s f).
Proof. exact (MK_COMB (@lem4388707) (@lem4388674 A B s f)). Qed.
Lemma lem4388709 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term97 A B s f) = (term98 A B s f).
Proof. exact (MK_COMB (@lem4388708 A B s f) (@lem4388706 A B s f)). Qed.
Lemma lem4388710 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4388711 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term99 A B s f) = (term99 A B s f).
Proof. exact (MK_COMB (@lem4388710) (@lem4388677 A B s f)). Qed.
Lemma lem4388712 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term100 A B s f) = (term101 A B s f).
Proof. exact (MK_COMB (@lem4388711 A B s f) (@lem4388703 A B s f)). Qed.
Lemma lem4388713 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4388714 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term102 A B s f) = (term103 A B s f).
Proof. exact (MK_COMB (@lem4388713) (@lem4388712 A B s f)). Qed.
Lemma lem4388715 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term104 A B s f) = (term105 A B s f).
Proof. exact (MK_COMB (@lem4388714 A B s f) (@lem4388709 A B s f)). Qed.
Lemma lem4388716 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term67 A B s f) = (term104 A B s f).
Proof. exact (@lem17646 (term60 A B s f) (term14 A B s f)). Qed.
Lemma lem4388717 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term67 A B s f) = (term105 A B s f).
Proof. exact (TRANS (@lem4388716 A B s f) (@lem4388715 A B s f)). Qed.
Lemma lem4388912 {A : Type'} (P : Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem4388913 {A : Type'} (P : Prop) (Q : A -> Prop) : (term106 A P Q) = (term107 A P Q).
Proof. exact (@lem4388912 A P Q). Qed.
Lemma lem4388914 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term108 A B s f) = (term109 A B s f).
Proof. exact (@lem4388913 A (term60 A B s f) (term91 A B s f)). Qed.
Lemma lem4388915 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term110 A B s f x) = (term81 A B s f x).
Proof. exact (eq_refl (term110 A B s f x)). Qed.
Lemma lem4388916 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term111 A B s f) = (term91 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388915 A B s f x)). Qed.
Lemma lem4388917 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388918 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term112 A B s f) = (term92 A B s f).
Proof. exact (MK_COMB (@lem4388917 A) (@lem4388916 A B s f)). Qed.
Lemma lem4388919 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term99 A B s f) = (term99 A B s f).
Proof. exact (eq_refl (term99 A B s f)). Qed.
Lemma lem4388920 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term108 A B s f) = (term101 A B s f).
Proof. exact (MK_COMB (@lem4388919 A B s f) (@lem4388918 A B s f)). Qed.
Lemma lem4388921 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4388922 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term113 A B s f) = (term114 A B s f).
Proof. exact (MK_COMB (@lem4388921) (@lem4388920 A B s f)). Qed.
Lemma lem4388923 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term110 A B s f x) = (term81 A B s f x).
Proof. exact (eq_refl (term110 A B s f x)). Qed.
Lemma lem4388924 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term99 A B s f) = (term99 A B s f).
Proof. exact (eq_refl (term99 A B s f)). Qed.
Lemma lem4388925 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term115 A B s f x) = (term116 A B s f x).
Proof. exact (MK_COMB (@lem4388924 A B s f) (@lem4388923 A B s f x)). Qed.
Lemma lem4388926 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term117 A B s f) = (term118 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388925 A B s f x)). Qed.
Lemma lem4388927 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388928 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term109 A B s f) = (term119 A B s f).
Proof. exact (MK_COMB (@lem4388927 A) (@lem4388926 A B s f)). Qed.
Lemma lem4388929 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term108 A B s f) = (term109 A B s f)) = ((term101 A B s f) = (term119 A B s f)).
Proof. exact (MK_COMB (@lem4388922 A B s f) (@lem4388928 A B s f)). Qed.
Lemma lem4388930 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term101 A B s f) = (term119 A B s f).
Proof. exact (EQ_MP (@lem4388929 A B s f) (@lem4388914 A B s f)). Qed.
Lemma lem4388931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4388932 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term103 A B s f) = (term120 A B s f).
Proof. exact (MK_COMB (@lem4388931) (@lem4388930 A B s f)). Qed.
Lemma lem4388934 {A : Type'} (P : A -> Prop) (Q : Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem4388935 {A : Type'} (P : A -> Prop) (Q : Prop) : (term121 A P Q) = (term122 A P Q).
Proof. exact (@lem4388934 A P Q). Qed.
Lemma lem4388936 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term123 A B s f) = (term124 A B s f).
Proof. exact (@lem4388935 A (term77 A B s f) (term94 A B s f)). Qed.
Lemma lem4388937 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term125 A B s f x) = (term69 A B s f x).
Proof. exact (eq_refl (term125 A B s f x)). Qed.
Lemma lem4388938 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term126 A B s f) = (term77 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388937 A B s f x)). Qed.
Lemma lem4388939 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388940 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term127 A B s f) = (term78 A B s f).
Proof. exact (MK_COMB (@lem4388939 A) (@lem4388938 A B s f)). Qed.
Lemma lem4388941 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4388942 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term128 A B s f) = (term96 A B s f).
Proof. exact (MK_COMB (@lem4388941) (@lem4388940 A B s f)). Qed.
Lemma lem4388943 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term94 A B s f) = (term94 A B s f).
Proof. exact (eq_refl (term94 A B s f)). Qed.
Lemma lem4388944 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term123 A B s f) = (term98 A B s f).
Proof. exact (MK_COMB (@lem4388942 A B s f) (@lem4388943 A B s f)). Qed.
Lemma lem4388945 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4388946 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term129 A B s f) = (term130 A B s f).
Proof. exact (MK_COMB (@lem4388945) (@lem4388944 A B s f)). Qed.
Lemma lem4388947 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term125 A B s f x) = (term69 A B s f x).
Proof. exact (eq_refl (term125 A B s f x)). Qed.
Lemma lem4388948 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4388949 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term131 A B s f x) = (term132 A B s f x).
Proof. exact (MK_COMB (@lem4388948) (@lem4388947 A B s f x)). Qed.
Lemma lem4388950 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term94 A B s f) = (term94 A B s f).
Proof. exact (eq_refl (term94 A B s f)). Qed.
Lemma lem4388951 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term133 A B x s f) = (term134 A B x s f).
Proof. exact (MK_COMB (@lem4388949 A B s f x) (@lem4388950 A B s f)). Qed.
Lemma lem4388952 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term135 A B s f) = (term136 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388951 A B x s f)). Qed.
Lemma lem4388953 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388954 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term124 A B s f) = (term137 A B s f).
Proof. exact (MK_COMB (@lem4388953 A) (@lem4388952 A B s f)). Qed.
Lemma lem4388955 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term123 A B s f) = (term124 A B s f)) = ((term98 A B s f) = (term137 A B s f)).
Proof. exact (MK_COMB (@lem4388946 A B s f) (@lem4388954 A B s f)). Qed.
Lemma lem4388956 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term98 A B s f) = (term137 A B s f).
Proof. exact (EQ_MP (@lem4388955 A B s f) (@lem4388936 A B s f)). Qed.
Lemma lem4388957 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term105 A B s f) = (term138 A B s f).
Proof. exact (MK_COMB (@lem4388932 A B s f) (@lem4388956 A B s f)). Qed.
Lemma lem4388959 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem4388960 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term139 A P Q) = (term140 A P Q).
Proof. exact (@lem4388959 A P Q). Qed.
Lemma lem4388961 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term141 A B s f) = (term142 A B s f).
Proof. exact (@lem4388960 A (term118 A B s f) (term136 A B s f)). Qed.
Lemma lem4388962 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term143 A B s f x) = (term116 A B s f x).
Proof. exact (eq_refl (term143 A B s f x)). Qed.
Lemma lem4388963 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term144 A B s f) = (term118 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388962 A B s f x)). Qed.
Lemma lem4388964 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388965 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term145 A B s f) = (term119 A B s f).
Proof. exact (MK_COMB (@lem4388964 A) (@lem4388963 A B s f)). Qed.
Lemma lem4388966 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4388967 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term146 A B s f) = (term120 A B s f).
Proof. exact (MK_COMB (@lem4388966) (@lem4388965 A B s f)). Qed.
Lemma lem4388968 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term147 A B s f x) = (term134 A B x s f).
Proof. exact (eq_refl (term147 A B s f x)). Qed.
Lemma lem4388969 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term148 A B s f) = (term136 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388968 A B x s f)). Qed.
Lemma lem4388970 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388971 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term149 A B s f) = (term137 A B s f).
Proof. exact (MK_COMB (@lem4388970 A) (@lem4388969 A B s f)). Qed.
Lemma lem4388972 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term141 A B s f) = (term138 A B s f).
Proof. exact (MK_COMB (@lem4388967 A B s f) (@lem4388971 A B s f)). Qed.
Lemma lem4388973 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4388974 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term150 A B s f) = (term151 A B s f).
Proof. exact (MK_COMB (@lem4388973) (@lem4388972 A B s f)). Qed.
Lemma lem4388975 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term143 A B s f x) = (term116 A B s f x).
Proof. exact (eq_refl (term143 A B s f x)). Qed.
Lemma lem4388976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4388977 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term152 A B s f x) = (term153 A B s f x).
Proof. exact (MK_COMB (@lem4388976) (@lem4388975 A B s f x)). Qed.
Lemma lem4388978 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term147 A B s f x) = (term134 A B x s f).
Proof. exact (eq_refl (term147 A B s f x)). Qed.
Lemma lem4388979 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term154 A B s f x) = (term155 A B x s f).
Proof. exact (MK_COMB (@lem4388977 A B s f x) (@lem4388978 A B x s f)). Qed.
Lemma lem4388980 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term156 A B s f) = (term157 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4388979 A B x s f)). Qed.
Lemma lem4388981 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem4388982 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term142 A B s f) = (term158 A B s f).
Proof. exact (MK_COMB (@lem4388981 A) (@lem4388980 A B s f)). Qed.
Lemma lem4388983 {A B : Type'} (s : A -> Prop) (f : A -> B) : ((term141 A B s f) = (term142 A B s f)) = ((term138 A B s f) = (term158 A B s f)).
Proof. exact (MK_COMB (@lem4388974 A B s f) (@lem4388982 A B s f)). Qed.
Lemma lem4388984 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term138 A B s f) = (term158 A B s f).
Proof. exact (EQ_MP (@lem4388983 A B s f) (@lem4388961 A B s f)). Qed.
Lemma lem4388986 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term105 A B s f) = (term158 A B s f).
Proof. exact (TRANS (@lem4388957 A B s f) (@lem4388984 A B s f)). Qed.
Lemma lem4388987 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term67 A B s f) = (term158 A B s f).
Proof. exact (TRANS (@lem4388717 A B s f) (@lem4388986 A B s f)). Qed.
Lemma lem4388988 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term67 A B s f) : term158 A B s f.
Proof. exact (EQ_MP (@lem4388987 A B s f) (@lem4388652 A B s f h1)). Qed.
Lemma lem4388989 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term155 A B x s f) : term155 A B x s f.
Proof. exact (h1). Qed.
Lemma lem4389004 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term85 A B s f x) = (term85 A B s f x).
Proof. exact (eq_refl (term85 A B s f x)). Qed.
Lemma lem4389005 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term93 A B s f) = (term93 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4389004 A B s f x)). Qed.
Lemma lem4389006 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4389007 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term94 A B s f) = (term94 A B s f).
Proof. exact (MK_COMB (@lem4389006 A) (@lem4389005 A B s f)). Qed.
Lemma lem4389028 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term132 A B s f x) = (term132 A B s f x).
Proof. exact (eq_refl (term132 A B s f x)). Qed.
Lemma lem4389029 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term134 A B x s f) = (term134 A B x s f).
Proof. exact (MK_COMB (@lem4389028 A B s f x) (@lem4389007 A B s f)). Qed.
Lemma lem4389048 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term81 A B s f x) = (term81 A B s f x).
Proof. exact (eq_refl (term81 A B s f x)). Qed.
Lemma lem4389063 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term54 A B s f x) = (term54 A B s f x).
Proof. exact (eq_refl (term54 A B s f x)). Qed.
Lemma lem4389064 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term59 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4389063 A B s f x)). Qed.
Lemma lem4389065 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4389066 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term60 A B s f) = (term60 A B s f).
Proof. exact (MK_COMB (@lem4389065 A) (@lem4389064 A B s f)). Qed.
Lemma lem4389067 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4389068 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term99 A B s f) = (term99 A B s f).
Proof. exact (MK_COMB (@lem4389067) (@lem4389066 A B s f)). Qed.
Lemma lem4389069 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term116 A B s f x) = (term116 A B s f x).
Proof. exact (MK_COMB (@lem4389068 A B s f) (@lem4389048 A B s f x)). Qed.
Lemma lem4389070 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem4389071 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term153 A B s f x) = (term153 A B s f x).
Proof. exact (MK_COMB (@lem4389070) (@lem4389069 A B s f x)). Qed.
Lemma lem4389072 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) : (term155 A B x s f) = (term155 A B x s f).
Proof. exact (MK_COMB (@lem4389071 A B s f x) (@lem4389029 A B x s f)). Qed.
Lemma lem4389073 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term155 A B x s f) : term155 A B x s f.
Proof. exact (EQ_MP (@lem4389072 A B x s f) (@lem4388989 A B x s f h1)). Qed.
Lemma lem4389074 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term116 A B s f x.
Proof. exact (h1). Qed.
Lemma lem4389075 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term134 A B x s f.
Proof. exact (h1). Qed.
Lemma lem4389076 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term81 A B s f x.
Proof. exact (proj2 (@lem4389074 A B s f x h1)). Qed.
Lemma lem4389077 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term60 A B s f.
Proof. exact (proj1 (@lem4389074 A B s f x h1)). Qed.
Lemma lem4389080 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term94 A B s f.
Proof. exact (proj2 (@lem4389075 A B x s f h1)). Qed.
Lemma lem4389081 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term69 A B s f x.
Proof. exact (proj1 (@lem4389075 A B x s f h1)). Qed.
Lemma lem4389091 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term54 A B s f x) = (term54 A B s f x).
Proof. exact (eq_refl (term54 A B s f x)). Qed.
Lemma lem4389092 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term59 A B s f) = (term59 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4389091 A B s f x)). Qed.
Lemma lem4389093 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4389095 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term60 A B s f) = (term60 A B s f).
Proof. exact (MK_COMB (@lem4389093 A) (@lem4389092 A B s f)). Qed.
Lemma lem4389096 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term60 A B s f.
Proof. exact (EQ_MP (@lem4389095 A B s f) (@lem4389077 A B s f x h1)). Qed.
Lemma lem4389112 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) : (term85 A B s f x) = (term85 A B s f x).
Proof. exact (eq_refl (term85 A B s f x)). Qed.
Lemma lem4389113 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term93 A B s f) = (term93 A B s f).
Proof. exact (fun_ext (fun x : A => @lem4389112 A B s f x)). Qed.
Lemma lem4389114 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4389116 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term94 A B s f) = (term94 A B s f).
Proof. exact (MK_COMB (@lem4389114 A) (@lem4389113 A B s f)). Qed.
Lemma lem4389117 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term94 A B s f.
Proof. exact (EQ_MP (@lem4389116 A B s f) (@lem4389080 A B x s f h1)). Qed.
Lemma lem4389126 {A B : Type'} (_50137 : A) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term74 A B s f _50137.
Proof. exact (@lem4389096 A B s f x h1 _50137). Qed.
Lemma lem4389127 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50137 : A) : (term74 A B s f _50137) = (term54 A B s f _50137).
Proof. exact (eq_refl (term74 A B s f _50137)). Qed.
Lemma lem4389129 {A B : Type'} (_50138 : A) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term159 A B s f _50138.
Proof. exact (@lem4389117 A B x s f h1 _50138). Qed.
Lemma lem4389130 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50138 : A) : (term159 A B s f _50138) = (term85 A B s f _50138).
Proof. exact (eq_refl (term159 A B s f _50138)). Qed.
Lemma lem4389137 {A B : Type'} (_50137 : A) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term54 A B s f _50137.
Proof. exact (EQ_MP (@lem4389127 A B s f _50137) (@lem4389126 A B _50137 s f x h1)). Qed.
Lemma lem4389141 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term160 A B f x.
Proof. exact (proj2 (@lem4389076 A B s f x h1)). Qed.
Lemma lem4389147 {A B : Type'} (_50138 : A) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term85 A B s f _50138.
Proof. exact (EQ_MP (@lem4389130 A B s f _50138) (@lem4389129 A B _50138 x s f h1)). Qed.
Lemma lem4389151 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term161 A B f x.
Proof. exact (proj2 (@lem4389081 A B x s f h1)). Qed.
Lemma lem4389180 {B : Type'} (x : B) (y : B) (z : B) : term162 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4389186 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term56 A x s.
Proof. exact (proj1 (@lem4389076 A B s f x h1)). Qed.
Lemma lem4389187 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term163 A x s.
Proof. exact (fun h0 : @IN A x s => @lem4389186 A B s f x h1). Qed.
Lemma lem4389189 (p : Prop) : (term164 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4389190 {A : Type'} (x : A) (s : A -> Prop) : (term163 A x s) = (term56 A x s).
Proof. exact (@lem4389189 (@IN A x s)). Qed.
Lemma lem4389191 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term56 A x s.
Proof. exact (EQ_MP (@lem4389190 A x s) (@lem4389187 A B s f x h1)). Qed.
Lemma lem4389197 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4389198 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : (term54 A B s f _50137) = (term165 A B f _50137 s).
Proof. exact (@lem4389197 ((@ARB B) = (f _50137)) (@IN A _50137 s)). Qed.
Lemma lem4389206 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4389207 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : (term166 A B s f _50137) = (term167 A B f _50137 s).
Proof. exact (MK_COMB (@lem4389206) (@lem4389198 A B f _50137 s)). Qed.
Lemma lem4389215 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : (term165 A B f _50137 s) = (term165 A B f _50137 s).
Proof. exact (eq_refl (term165 A B f _50137 s)). Qed.
Lemma lem4389216 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : ((term54 A B s f _50137) = (term165 A B f _50137 s)) = ((term165 A B f _50137 s) = (term165 A B f _50137 s)).
Proof. exact (MK_COMB (@lem4389207 A B f _50137 s) (@lem4389215 A B f _50137 s)). Qed.
Lemma lem4389218 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4389219 (x : Prop) : (x = x) = True.
Proof. exact (@lem4389218 Prop x). Qed.
Lemma lem4389220 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : ((term165 A B f _50137 s) = (term165 A B f _50137 s)) = True.
Proof. exact (@lem4389219 (term165 A B f _50137 s)). Qed.
Lemma lem4389221 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : ((term54 A B s f _50137) = (term165 A B f _50137 s)) = True.
Proof. exact (TRANS (@lem4389216 A B f _50137 s) (@lem4389220 A B f _50137 s)). Qed.
Lemma lem4389222 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : True = ((term54 A B s f _50137) = (term165 A B f _50137 s)).
Proof. exact (SYM (@lem4389221 A B f _50137 s)). Qed.
Lemma lem4389223 {A B : Type'} (f : A -> B) (_50137 : A) (s : A -> Prop) : (term54 A B s f _50137) = (term165 A B f _50137 s).
Proof. exact (EQ_MP (@lem4389222 A B f _50137 s) (@lem0)). Qed.
Lemma lem4389224 {A B : Type'} (_50137 : A) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term165 A B f _50137 s.
Proof. exact (EQ_MP (@lem4389223 A B f _50137 s) (@lem4389137 A B _50137 s f x h1)). Qed.
Lemma lem4389226 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4389229 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50137 : A) : (term165 A B f _50137 s) = (term169 A B s f _50137).
Proof. exact (@lem4389226 (@IN A _50137 s) ((@ARB B) = (f _50137))). Qed.
Lemma lem4389232 {A B : Type'} (_50137 : A) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term169 A B s f _50137.
Proof. exact (EQ_MP (@lem4389229 A B s f _50137) (@lem4389224 A B _50137 s f x h1)). Qed.
Lemma lem4389233 {A B : Type'} (_50137 : A) (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term169 A B s f _50137.
Proof. exact (@lem4389232 A B _50137 s f x h1). Qed.
Lemma lem4389234 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term169 A B s f x.
Proof. exact (@lem4389233 A B x s f x h1). Qed.
Lemma lem4389237 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : (@ARB B) = (f x).
Proof. exact (@lem4389234 A B s f x h1 (@lem4389191 A B s f x h1)). Qed.
Lemma lem4389238 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term170 A B f x.
Proof. exact (fun h0 : term161 A B f x => @lem4389237 A B s f x h1). Qed.
Lemma lem4389240 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389241 {A B : Type'} (f : A -> B) (x : A) : (term170 A B f x) = ((@ARB B) = (f x)).
Proof. exact (@lem4389240 ((@ARB B) = (f x))). Qed.
Lemma lem4389242 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : (@ARB B) = (f x).
Proof. exact (EQ_MP (@lem4389241 A B f x) (@lem4389238 A B s f x h1)). Qed.
Lemma lem4389244 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4389245 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4389244 B x). Qed.
Lemma lem4389246 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (@lem4389245 B (@ARB B)). Qed.
Lemma lem4389247 {B : Type'} : term172 B.
Proof. exact (fun h0 : term173 B => @lem4389246 B). Qed.
Lemma lem4389249 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389250 {B : Type'} : (term172 B) = ((@ARB B) = (@ARB B)).
Proof. exact (@lem4389249 ((@ARB B) = (@ARB B))). Qed.
Lemma lem4389251 {B : Type'} : (@ARB B) = (@ARB B).
Proof. exact (EQ_MP (@lem4389250 B) (@lem4389247 B)). Qed.
Lemma lem4389269 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4389270 {B : Type'} (y : B) (x : B) (z : B) : (term174 B x y z) = (term175 B y x z).
Proof. exact (@lem4389269 (y = z) (term176 B x z)). Qed.
Lemma lem4389280 {B : Type'} (x : B) (y : B) : (term177 B x y) = (term177 B x y).
Proof. exact (eq_refl (term177 B x y)). Qed.
Lemma lem4389281 {B : Type'} (y : B) (x : B) (z : B) : (term162 B x y z) = (term178 B y x z).
Proof. exact (MK_COMB (@lem4389280 B x y) (@lem4389270 B y x z)). Qed.
Lemma lem4389285 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4389286 {B : Type'} (y : B) (x : B) (z : B) : (term178 B y x z) = (term180 B y x z).
Proof. exact (@lem4389285 (y = z) (term176 B x y) (term176 B x z)). Qed.
Lemma lem4389308 {B : Type'} (y : B) (x : B) (z : B) : (term162 B x y z) = (term180 B y x z).
Proof. exact (TRANS (@lem4389281 B y x z) (@lem4389286 B y x z)). Qed.
Lemma lem4389309 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4389310 {B : Type'} (y : B) (x : B) (z : B) : (term181 B x y z) = (term182 B y x z).
Proof. exact (MK_COMB (@lem4389309) (@lem4389308 B y x z)). Qed.
Lemma lem4389332 {B : Type'} (y : B) (x : B) (z : B) : (term180 B y x z) = (term180 B y x z).
Proof. exact (eq_refl (term180 B y x z)). Qed.
Lemma lem4389333 {B : Type'} (y : B) (x : B) (z : B) : ((term162 B x y z) = (term180 B y x z)) = ((term180 B y x z) = (term180 B y x z)).
Proof. exact (MK_COMB (@lem4389310 B y x z) (@lem4389332 B y x z)). Qed.
Lemma lem4389335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4389336 (x : Prop) : (x = x) = True.
Proof. exact (@lem4389335 Prop x). Qed.
Lemma lem4389337 {B : Type'} (y : B) (x : B) (z : B) : ((term180 B y x z) = (term180 B y x z)) = True.
Proof. exact (@lem4389336 (term180 B y x z)). Qed.
Lemma lem4389338 {B : Type'} (y : B) (x : B) (z : B) : ((term162 B x y z) = (term180 B y x z)) = True.
Proof. exact (TRANS (@lem4389333 B y x z) (@lem4389337 B y x z)). Qed.
Lemma lem4389339 {B : Type'} (y : B) (x : B) (z : B) : True = ((term162 B x y z) = (term180 B y x z)).
Proof. exact (SYM (@lem4389338 B y x z)). Qed.
Lemma lem4389340 {B : Type'} (y : B) (x : B) (z : B) : (term162 B x y z) = (term180 B y x z).
Proof. exact (EQ_MP (@lem4389339 B y x z) (@lem0)). Qed.
Lemma lem4389341 {B : Type'} (y : B) (x : B) (z : B) : term180 B y x z.
Proof. exact (EQ_MP (@lem4389340 B y x z) (@lem4389180 B x y z)). Qed.
Lemma lem4389343 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4389344 {B : Type'} (x : B) (y : B) (z : B) : (term180 B y x z) = (term183 B x y z).
Proof. exact (@lem4389343 (term184 B y x z) (y = z)). Qed.
Lemma lem4389346 (a : Prop) (b : Prop) : (term185 a b) = (term186 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4389347 {B : Type'} (y : B) (x : B) (z : B) : (term187 B y x z) = (term188 B y x z).
Proof. exact (@lem4389346 (term176 B x y) (term176 B x z)). Qed.
Lemma lem4389349 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4389350 {B : Type'} (x : B) (y : B) : (term189 B x y) = (x = y).
Proof. exact (@lem4389349 (x = y)). Qed.
Lemma lem4389351 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4389352 {B : Type'} (x : B) (y : B) : (term190 B x y) = (term191 B x y).
Proof. exact (MK_COMB (@lem4389351) (@lem4389350 B x y)). Qed.
Lemma lem4389354 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4389355 {B : Type'} (x : B) (z : B) : (term189 B x z) = (x = z).
Proof. exact (@lem4389354 (x = z)). Qed.
Lemma lem4389356 {B : Type'} (y : B) (x : B) (z : B) : (term188 B y x z) = (term192 B y x z).
Proof. exact (MK_COMB (@lem4389352 B x y) (@lem4389355 B x z)). Qed.
Lemma lem4389357 {B : Type'} (y : B) (x : B) (z : B) : (term187 B y x z) = (term192 B y x z).
Proof. exact (TRANS (@lem4389347 B y x z) (@lem4389356 B y x z)). Qed.
Lemma lem4389358 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4389359 {B : Type'} (y : B) (x : B) (z : B) : (term193 B y x z) = (term194 B y x z).
Proof. exact (MK_COMB (@lem4389358) (@lem4389357 B y x z)). Qed.
Lemma lem4389360 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4389361 {B : Type'} (x : B) (y : B) (z : B) : (term183 B x y z) = (term195 B x y z).
Proof. exact (MK_COMB (@lem4389359 B y x z) (@lem4389360 B y z)). Qed.
Lemma lem4389362 {B : Type'} (x : B) (y : B) (z : B) : (term180 B y x z) = (term195 B x y z).
Proof. exact (TRANS (@lem4389344 B x y z) (@lem4389361 B x y z)). Qed.
Lemma lem4389364 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term196 A B f x.
Proof. exact (conj (@lem4389242 A B s f x h1) (@lem4389251 B)). Qed.
Lemma lem4389366 {B : Type'} (x : B) (y : B) (z : B) : term195 B x y z.
Proof. exact (EQ_MP (@lem4389362 B x y z) (@lem4389341 B y x z)). Qed.
Lemma lem4389367 {B : Type'} (x : B) (y : B) (z : B) : term195 B x y z.
Proof. exact (@lem4389366 B x y z). Qed.
Lemma lem4389368 {A B : Type'} (f : A -> B) (x : A) : term197 A B f x.
Proof. exact (@lem4389367 B (@ARB B) (f x) (@ARB B)). Qed.
Lemma lem4389371 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : (f x) = (@ARB B).
Proof. exact (@lem4389368 A B f x (@lem4389364 A B s f x h1)). Qed.
Lemma lem4389372 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term198 A B f x.
Proof. exact (fun h0 : term160 A B f x => @lem4389371 A B s f x h1). Qed.
Lemma lem4389374 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389375 {A B : Type'} (f : A -> B) (x : A) : (term198 A B f x) = ((f x) = (@ARB B)).
Proof. exact (@lem4389374 ((f x) = (@ARB B))). Qed.
Lemma lem4389376 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : (f x) = (@ARB B).
Proof. exact (EQ_MP (@lem4389375 A B f x) (@lem4389372 A B s f x h1)). Qed.
Lemma lem4389379 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4389381 {A B : Type'} (f : A -> B) (x : A) : (term160 A B f x) = (term199 A B f x).
Proof. exact (@lem4389379 ((f x) = (@ARB B))). Qed.
Lemma lem4389384 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term199 A B f x.
Proof. exact (EQ_MP (@lem4389381 A B f x) (@lem4389141 A B s f x h1)). Qed.
Lemma lem4389387 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : False.
Proof. exact (@lem4389384 A B s f x h1 (@lem4389376 A B s f x h1)). Qed.
Lemma lem4389388 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : term200.
Proof. exact (fun h0 : ~ False => @lem4389387 A B s f x h1). Qed.
Lemma lem4389390 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389391 : term200 = False.
Proof. exact (@lem4389390 False). Qed.
Lemma lem4389392 {A B : Type'} (s : A -> Prop) (f : A -> B) (x : A) (h1 : term116 A B s f x) : False.
Proof. exact (EQ_MP (@lem4389391) (@lem4389388 A B s f x h1)). Qed.
Lemma lem4389421 {B : Type'} (x : B) (y : B) (z : B) : term162 B x y z.
Proof. exact (@lem21385 B x y z). Qed.
Lemma lem4389427 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term56 A x s.
Proof. exact (proj1 (@lem4389081 A B x s f h1)). Qed.
Lemma lem4389428 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term163 A x s.
Proof. exact (fun h0 : @IN A x s => @lem4389427 A B x s f h1). Qed.
Lemma lem4389430 (p : Prop) : (term164 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem4389431 {A : Type'} (x : A) (s : A -> Prop) : (term163 A x s) = (term56 A x s).
Proof. exact (@lem4389430 (@IN A x s)). Qed.
Lemma lem4389432 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term56 A x s.
Proof. exact (EQ_MP (@lem4389431 A x s) (@lem4389428 A B x s f h1)). Qed.
Lemma lem4389438 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4389439 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : (term85 A B s f _50138) = (term201 A B f _50138 s).
Proof. exact (@lem4389438 ((f _50138) = (@ARB B)) (@IN A _50138 s)). Qed.
Lemma lem4389447 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4389448 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : (term202 A B s f _50138) = (term203 A B f _50138 s).
Proof. exact (MK_COMB (@lem4389447) (@lem4389439 A B f _50138 s)). Qed.
Lemma lem4389456 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : (term201 A B f _50138 s) = (term201 A B f _50138 s).
Proof. exact (eq_refl (term201 A B f _50138 s)). Qed.
Lemma lem4389457 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : ((term85 A B s f _50138) = (term201 A B f _50138 s)) = ((term201 A B f _50138 s) = (term201 A B f _50138 s)).
Proof. exact (MK_COMB (@lem4389448 A B f _50138 s) (@lem4389456 A B f _50138 s)). Qed.
Lemma lem4389459 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4389460 (x : Prop) : (x = x) = True.
Proof. exact (@lem4389459 Prop x). Qed.
Lemma lem4389461 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : ((term201 A B f _50138 s) = (term201 A B f _50138 s)) = True.
Proof. exact (@lem4389460 (term201 A B f _50138 s)). Qed.
Lemma lem4389462 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : ((term85 A B s f _50138) = (term201 A B f _50138 s)) = True.
Proof. exact (TRANS (@lem4389457 A B f _50138 s) (@lem4389461 A B f _50138 s)). Qed.
Lemma lem4389463 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : True = ((term85 A B s f _50138) = (term201 A B f _50138 s)).
Proof. exact (SYM (@lem4389462 A B f _50138 s)). Qed.
Lemma lem4389464 {A B : Type'} (f : A -> B) (_50138 : A) (s : A -> Prop) : (term85 A B s f _50138) = (term201 A B f _50138 s).
Proof. exact (EQ_MP (@lem4389463 A B f _50138 s) (@lem0)). Qed.
Lemma lem4389465 {A B : Type'} (_50138 : A) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term201 A B f _50138 s.
Proof. exact (EQ_MP (@lem4389464 A B f _50138 s) (@lem4389147 A B _50138 x s f h1)). Qed.
Lemma lem4389467 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4389470 {A B : Type'} (s : A -> Prop) (f : A -> B) (_50138 : A) : (term201 A B f _50138 s) = (term39 A B s f _50138).
Proof. exact (@lem4389467 (@IN A _50138 s) ((f _50138) = (@ARB B))). Qed.
Lemma lem4389473 {A B : Type'} (_50138 : A) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term39 A B s f _50138.
Proof. exact (EQ_MP (@lem4389470 A B s f _50138) (@lem4389465 A B _50138 x s f h1)). Qed.
Lemma lem4389474 {A B : Type'} (_50138 : A) (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term39 A B s f _50138.
Proof. exact (@lem4389473 A B _50138 x s f h1). Qed.
Lemma lem4389475 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term39 A B s f x.
Proof. exact (@lem4389474 A B x x s f h1). Qed.
Lemma lem4389478 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : (f x) = (@ARB B).
Proof. exact (@lem4389475 A B x s f h1 (@lem4389432 A B x s f h1)). Qed.
Lemma lem4389479 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term198 A B f x.
Proof. exact (fun h0 : term160 A B f x => @lem4389478 A B x s f h1). Qed.
Lemma lem4389481 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389482 {A B : Type'} (f : A -> B) (x : A) : (term198 A B f x) = ((f x) = (@ARB B)).
Proof. exact (@lem4389481 ((f x) = (@ARB B))). Qed.
Lemma lem4389483 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : (f x) = (@ARB B).
Proof. exact (EQ_MP (@lem4389482 A B f x) (@lem4389479 A B x s f h1)). Qed.
Lemma lem4389485 {B : Type'} (x : B) : x = x.
Proof. exact (@lem21386 B x). Qed.
Lemma lem4389486 {B : Type'} (x : B) : x = x.
Proof. exact (@lem4389485 B x). Qed.
Lemma lem4389487 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (@lem4389486 B (f x)). Qed.
Lemma lem4389488 {A B : Type'} (f : A -> B) (x : A) : term204 A B f x.
Proof. exact (fun h0 : term205 A B f x => @lem4389487 A B f x). Qed.
Lemma lem4389490 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389491 {A B : Type'} (f : A -> B) (x : A) : (term204 A B f x) = ((f x) = (f x)).
Proof. exact (@lem4389490 ((f x) = (f x))). Qed.
Lemma lem4389492 {A B : Type'} (f : A -> B) (x : A) : (f x) = (f x).
Proof. exact (EQ_MP (@lem4389491 A B f x) (@lem4389488 A B f x)). Qed.
Lemma lem4389510 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem4389511 {B : Type'} (y : B) (x : B) (z : B) : (term174 B x y z) = (term175 B y x z).
Proof. exact (@lem4389510 (y = z) (term176 B x z)). Qed.
Lemma lem4389521 {B : Type'} (x : B) (y : B) : (term177 B x y) = (term177 B x y).
Proof. exact (eq_refl (term177 B x y)). Qed.
Lemma lem4389522 {B : Type'} (y : B) (x : B) (z : B) : (term162 B x y z) = (term178 B y x z).
Proof. exact (MK_COMB (@lem4389521 B x y) (@lem4389511 B y x z)). Qed.
Lemma lem4389526 (q : Prop) (p : Prop) (r : Prop) : (term179 p q r) = (term179 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem4389527 {B : Type'} (y : B) (x : B) (z : B) : (term178 B y x z) = (term180 B y x z).
Proof. exact (@lem4389526 (y = z) (term176 B x y) (term176 B x z)). Qed.
Lemma lem4389549 {B : Type'} (y : B) (x : B) (z : B) : (term162 B x y z) = (term180 B y x z).
Proof. exact (TRANS (@lem4389522 B y x z) (@lem4389527 B y x z)). Qed.
Lemma lem4389550 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4389551 {B : Type'} (y : B) (x : B) (z : B) : (term181 B x y z) = (term182 B y x z).
Proof. exact (MK_COMB (@lem4389550) (@lem4389549 B y x z)). Qed.
Lemma lem4389573 {B : Type'} (y : B) (x : B) (z : B) : (term180 B y x z) = (term180 B y x z).
Proof. exact (eq_refl (term180 B y x z)). Qed.
Lemma lem4389574 {B : Type'} (y : B) (x : B) (z : B) : ((term162 B x y z) = (term180 B y x z)) = ((term180 B y x z) = (term180 B y x z)).
Proof. exact (MK_COMB (@lem4389551 B y x z) (@lem4389573 B y x z)). Qed.
Lemma lem4389576 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem4389577 (x : Prop) : (x = x) = True.
Proof. exact (@lem4389576 Prop x). Qed.
Lemma lem4389578 {B : Type'} (y : B) (x : B) (z : B) : ((term180 B y x z) = (term180 B y x z)) = True.
Proof. exact (@lem4389577 (term180 B y x z)). Qed.
Lemma lem4389579 {B : Type'} (y : B) (x : B) (z : B) : ((term162 B x y z) = (term180 B y x z)) = True.
Proof. exact (TRANS (@lem4389574 B y x z) (@lem4389578 B y x z)). Qed.
Lemma lem4389580 {B : Type'} (y : B) (x : B) (z : B) : True = ((term162 B x y z) = (term180 B y x z)).
Proof. exact (SYM (@lem4389579 B y x z)). Qed.
Lemma lem4389581 {B : Type'} (y : B) (x : B) (z : B) : (term162 B x y z) = (term180 B y x z).
Proof. exact (EQ_MP (@lem4389580 B y x z) (@lem0)). Qed.
Lemma lem4389582 {B : Type'} (y : B) (x : B) (z : B) : term180 B y x z.
Proof. exact (EQ_MP (@lem4389581 B y x z) (@lem4389421 B x y z)). Qed.
Lemma lem4389584 (b : Prop) (a : Prop) : (a \/ b) = (term168 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem4389585 {B : Type'} (x : B) (y : B) (z : B) : (term180 B y x z) = (term183 B x y z).
Proof. exact (@lem4389584 (term184 B y x z) (y = z)). Qed.
Lemma lem4389587 (a : Prop) (b : Prop) : (term185 a b) = (term186 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem4389588 {B : Type'} (y : B) (x : B) (z : B) : (term187 B y x z) = (term188 B y x z).
Proof. exact (@lem4389587 (term176 B x y) (term176 B x z)). Qed.
Lemma lem4389590 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4389591 {B : Type'} (x : B) (y : B) : (term189 B x y) = (x = y).
Proof. exact (@lem4389590 (x = y)). Qed.
Lemma lem4389592 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4389593 {B : Type'} (x : B) (y : B) : (term190 B x y) = (term191 B x y).
Proof. exact (MK_COMB (@lem4389592) (@lem4389591 B x y)). Qed.
Lemma lem4389595 (a : Prop) : (term38 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem4389596 {B : Type'} (x : B) (z : B) : (term189 B x z) = (x = z).
Proof. exact (@lem4389595 (x = z)). Qed.
Lemma lem4389597 {B : Type'} (y : B) (x : B) (z : B) : (term188 B y x z) = (term192 B y x z).
Proof. exact (MK_COMB (@lem4389593 B x y) (@lem4389596 B x z)). Qed.
Lemma lem4389598 {B : Type'} (y : B) (x : B) (z : B) : (term187 B y x z) = (term192 B y x z).
Proof. exact (TRANS (@lem4389588 B y x z) (@lem4389597 B y x z)). Qed.
Lemma lem4389599 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4389600 {B : Type'} (y : B) (x : B) (z : B) : (term193 B y x z) = (term194 B y x z).
Proof. exact (MK_COMB (@lem4389599) (@lem4389598 B y x z)). Qed.
Lemma lem4389601 {B : Type'} (y : B) (z : B) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem4389602 {B : Type'} (x : B) (y : B) (z : B) : (term183 B x y z) = (term195 B x y z).
Proof. exact (MK_COMB (@lem4389600 B y x z) (@lem4389601 B y z)). Qed.
Lemma lem4389603 {B : Type'} (x : B) (y : B) (z : B) : (term180 B y x z) = (term195 B x y z).
Proof. exact (TRANS (@lem4389585 B x y z) (@lem4389602 B x y z)). Qed.
Lemma lem4389605 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term206 A B f x.
Proof. exact (conj (@lem4389483 A B x s f h1) (@lem4389492 A B f x)). Qed.
Lemma lem4389607 {B : Type'} (x : B) (y : B) (z : B) : term195 B x y z.
Proof. exact (EQ_MP (@lem4389603 B x y z) (@lem4389582 B y x z)). Qed.
Lemma lem4389608 {B : Type'} (x : B) (y : B) (z : B) : term195 B x y z.
Proof. exact (@lem4389607 B x y z). Qed.
Lemma lem4389609 {A B : Type'} (f : A -> B) (x : A) : term207 A B f x.
Proof. exact (@lem4389608 B (f x) (@ARB B) (f x)). Qed.
Lemma lem4389612 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : (@ARB B) = (f x).
Proof. exact (@lem4389609 A B f x (@lem4389605 A B x s f h1)). Qed.
Lemma lem4389613 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term170 A B f x.
Proof. exact (fun h0 : term161 A B f x => @lem4389612 A B x s f h1). Qed.
Lemma lem4389615 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389616 {A B : Type'} (f : A -> B) (x : A) : (term170 A B f x) = ((@ARB B) = (f x)).
Proof. exact (@lem4389615 ((@ARB B) = (f x))). Qed.
Lemma lem4389617 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : (@ARB B) = (f x).
Proof. exact (EQ_MP (@lem4389616 A B f x) (@lem4389613 A B x s f h1)). Qed.
Lemma lem4389620 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem4389622 {A B : Type'} (f : A -> B) (x : A) : (term161 A B f x) = (term208 A B f x).
Proof. exact (@lem4389620 ((@ARB B) = (f x))). Qed.
Lemma lem4389625 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term208 A B f x.
Proof. exact (EQ_MP (@lem4389622 A B f x) (@lem4389151 A B x s f h1)). Qed.
Lemma lem4389628 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : False.
Proof. exact (@lem4389625 A B x s f h1 (@lem4389617 A B x s f h1)). Qed.
Lemma lem4389629 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : term200.
Proof. exact (fun h0 : ~ False => @lem4389628 A B x s f h1). Qed.
Lemma lem4389631 (p : Prop) : (term171 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem4389632 : term200 = False.
Proof. exact (@lem4389631 False). Qed.
Lemma lem4389633 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term134 A B x s f) : False.
Proof. exact (EQ_MP (@lem4389632) (@lem4389629 A B x s f h1)). Qed.
Lemma lem4389634 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term155 A B x s f) : False.
Proof. exact (or_elim (@lem4389073 A B x s f h1) (fun h0 : term116 A B s f x => @lem4389392 A B s f x h0) (fun h0 : term134 A B x s f => @lem4389633 A B x s f h0)). Qed.
Lemma lem4389635 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term155 A B x s f) : (term155 A B x s f) = False.
Proof. exact (prop_ext (fun h2 : term155 A B x s f => @lem4389634 A B x s f h1) (fun h2 : False => @lem4389073 A B x s f h1)). Qed.
Lemma lem4389636 {A B : Type'} (x : A) (s : A -> Prop) (f : A -> B) (h1 : term155 A B x s f) : False.
Proof. exact (EQ_MP (@lem4389635 A B x s f h1) (@lem4389073 A B x s f h1)). Qed.
Lemma lem4389637 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term67 A B s f) : False.
Proof. exact (ex_elim (@lem4388988 A B s f h1) (fun x : A => fun h0 : term157 A B s f x => @lem4389636 A B x s f h0)). Qed.
Lemma lem4389638 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term67 A B s f) : (term67 A B s f) = False.
Proof. exact (prop_ext (fun h2 : term67 A B s f => @lem4389637 A B s f h1) (fun h2 : False => @lem4388652 A B s f h1)). Qed.
Lemma lem4389639 {A B : Type'} (s : A -> Prop) (f : A -> B) (h1 : term67 A B s f) : False.
Proof. exact (EQ_MP (@lem4389638 A B s f h1) (@lem4388652 A B s f h1)). Qed.
Lemma lem4389640 {A B : Type'} (s : A -> Prop) (f : A -> B) : term66 A B s f.
Proof. exact (fun h0 : term67 A B s f => @lem4389639 A B s f h0). Qed.
Lemma lem4389641 {A B : Type'} (s : A -> Prop) (f : A -> B) : (term60 A B s f) = (term14 A B s f).
Proof. exact (EQ_MP (@lem4388651 A B s f) (@lem4389640 A B s f)). Qed.
Lemma lem4389646 {A B : Type'} (s : A -> Prop) : term63 A B s.
Proof. exact (fun f : A -> B => @lem4389641 A B s f). Qed.
Lemma lem4389651 {A B : Type'} : term65 A B.
Proof. exact (fun s : A -> Prop => @lem4389646 A B s). Qed.
Lemma lem4389652 {A B : Type'} : term32 A B.
Proof. exact (EQ_MP (@lem4388647 A B) (@lem4389651 A B)). Qed.
Lemma lem4389654 {A B : Type'} : term32 A B.
Proof. exact (@lem4388492 A B (@lem4389652 A B)). Qed.
Lemma lem4389655 {A B : Type'} (h1 : term33 A B) : False.
Proof. exact (@lem4389654 A B (@lem4388476 A B h1)). Qed.
Lemma lem4389656 {A B : Type'} (h1 : term33 A B) : (term33 A B) = False.
Proof. exact (prop_ext (fun h2 : term33 A B => @lem4389655 A B h1) (fun h2 : False => @lem4388476 A B h1)). Qed.
Lemma lem4389657 {A B : Type'} (h1 : term33 A B) : False.
Proof. exact (EQ_MP (@lem4389656 A B h1) (@lem4388476 A B h1)). Qed.
Lemma lem4389658 {A B : Type'} : term32 A B.
Proof. exact (fun h0 : term33 A B => @lem4389657 A B h0). Qed.
Lemma lem4389659 {A B : Type'} : term30 A B.
Proof. exact (EQ_MP (@lem4388475 A B) (@lem4389658 A B)). Qed.
Lemma lem4389660 {A B : Type'} : term29 A B.
Proof. exact (EQ_MP (@lem4388471 A B) (@lem4389659 A B)). Qed.
