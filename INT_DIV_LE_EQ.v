Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_DIV_LE_EQ_term_abbrevs.
Require Import INT_DIV_LT_EQ_spec.
Require Import INT_LE_DISCRETE_spec.
Require Import thm0_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem2611394 (a : int) : term0 a.
Proof. exact (@lem2611267 a). Qed.
Lemma lem2611395 (a : int) : (term0 a) = (term1 a).
Proof. exact (eq_refl (term0 a)). Qed.
Lemma lem2611396 (a : int) : term1 a.
Proof. exact (EQ_MP (@lem2611395 a) (@lem2611394 a)). Qed.
Lemma lem2611397 (a : int) (b : int) : term2 a b.
Proof. exact (@lem2611396 a b). Qed.
Lemma lem2611398 (b : int) (a : int) : (term2 a b) = (term3 b a).
Proof. exact (eq_refl (term2 a b)). Qed.
Lemma lem2611399 (b : int) (a : int) : term3 b a.
Proof. exact (EQ_MP (@lem2611398 b a) (@lem2611397 a b)). Qed.
Lemma lem2611400 (b : int) (a : int) (c : int) : term4 b a c.
Proof. exact (@lem2611399 b a c). Qed.
Lemma lem2611401 (b : int) (a : int) (c : int) : (term4 b a c) = (term5 b a c).
Proof. exact (eq_refl (term4 b a c)). Qed.
Lemma lem2611402 (b : int) (a : int) (c : int) : term5 b a c.
Proof. exact (EQ_MP (@lem2611401 b a c) (@lem2611400 b a c)). Qed.
Lemma lem2611403 (a : int) (h1 : term6 a) : term6 a.
Proof. exact (h1). Qed.
Lemma lem2611404 (b : int) (c : int) (a : int) (h1 : term6 a) : (term7 b a c) = (term8 b a c).
Proof. exact (@lem2611402 b a c (@lem2611403 a h1)). Qed.
Lemma lem2611410 (x : int) : term9 x.
Proof. exact (@lem2332494 x). Qed.
Lemma lem2611411 (x : int) : (term9 x) = (term10 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem2611412 (x : int) : term10 x.
Proof. exact (EQ_MP (@lem2611411 x) (@lem2611410 x)). Qed.
Lemma lem2611413 (x : int) (y : int) : term11 x y.
Proof. exact (@lem2611412 x y). Qed.
Lemma lem2611414 (x : int) (y : int) : (term11 x y) = ((int_le x y) = (term12 x y)).
Proof. exact (eq_refl (term11 x y)). Qed.
Lemma lem2611431 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term13 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem2611432 (p : Prop) (q : Prop) (p' : Prop) : term14 p q p'.
Proof. exact (fun q' : Prop => @lem2611431 p q p' q'). Qed.
Lemma lem2611433 (p : Prop) (q : Prop) : term15 p q.
Proof. exact (fun p' : Prop => @lem2611432 p q p'). Qed.
Lemma lem2611434 (b : int) (a : int) (c : int) : term16 b a c.
Proof. exact (@lem2611433 (term6 a) ((term17 b a c) = (term18 b a c))). Qed.
Lemma lem2611435 (b : int) (a : int) (c : int) (p' : Prop) : term19 b a c p'.
Proof. exact (@lem2611434 b a c p'). Qed.
Lemma lem2611436 (b : int) (a : int) (c : int) (p' : Prop) : (term19 b a c p') = (term20 b a c p').
Proof. exact (eq_refl (term19 b a c p')). Qed.
Lemma lem2611437 (b : int) (a : int) (c : int) (p' : Prop) : term20 b a c p'.
Proof. exact (EQ_MP (@lem2611436 b a c p') (@lem2611435 b a c p')). Qed.
Lemma lem2611438 (b : int) (a : int) (c : int) (p' : Prop) (q' : Prop) : term21 b a c p' q'.
Proof. exact (@lem2611437 b a c p' q'). Qed.
Lemma lem2611439 (b : int) (a : int) (c : int) (p' : Prop) (q' : Prop) : (term21 b a c p' q') = (term22 b a c p' q').
Proof. exact (eq_refl (term21 b a c p' q')). Qed.
Lemma lem2611440 (b : int) (a : int) (c : int) (p' : Prop) (q' : Prop) : term22 b a c p' q'.
Proof. exact (EQ_MP (@lem2611439 b a c p' q') (@lem2611438 b a c p' q')). Qed.
Lemma lem2611441 (a : int) : (term6 a) = (term6 a).
Proof. exact (eq_refl (term6 a)). Qed.
Lemma lem2611442 (b : int) (c : int) (a : int) (q' : Prop) : term23 b c a q'.
Proof. exact (@lem2611440 b a c (term6 a) q'). Qed.
Lemma lem2611443 (b : int) (c : int) (a : int) (q' : Prop) : term24 b c a q'.
Proof. exact (@lem2611442 b c a q' (@lem2611441 a)). Qed.
Lemma lem2611444 (a : int) (h1 : term6 a) : term6 a.
Proof. exact (h1). Qed.
Lemma lem2611445 (a : int) : (term6 a) = ((term6 a) = True).
Proof. exact (@lem7 (term6 a)). Qed.
Lemma lem2611450 (x : int) (y : int) : (int_le x y) = (term12 x y).
Proof. exact (EQ_MP (@lem2611414 x y) (@lem2611413 x y)). Qed.
Lemma lem2611451 (b : int) (a : int) (c : int) : (term17 b a c) = (term25 b a c).
Proof. exact (@lem2611450 (div b a) c). Qed.
Lemma lem2611453 (b : int) (a : int) (c : int) : term5 b a c.
Proof. exact (fun h0 : term6 a => @lem2611404 b c a h0). Qed.
Lemma lem2611454 (b : int) (a : int) (c : int) : term26 b a c.
Proof. exact (@lem2611453 b a (term27 c)). Qed.
Lemma lem2611456 (a : int) (h1 : term6 a) : (term6 a) = True.
Proof. exact (EQ_MP (@lem2611445 a) (@lem2611444 a h1)). Qed.
Lemma lem2611457 (a : int) (h1 : term6 a) : True = (term6 a).
Proof. exact (SYM (@lem2611456 a h1)). Qed.
Lemma lem2611458 (a : int) (h1 : term6 a) : term6 a.
Proof. exact (EQ_MP (@lem2611457 a h1) (@lem0)). Qed.
Lemma lem2611459 (b : int) (c : int) (a : int) (h1 : term6 a) : (term25 b a c) = (term18 b a c).
Proof. exact (@lem2611454 b a c (@lem2611458 a h1)). Qed.
Lemma lem2611460 (b : int) (c : int) (a : int) (h1 : term6 a) : (term17 b a c) = (term18 b a c).
Proof. exact (TRANS (@lem2611451 b a c) (@lem2611459 b c a h1)). Qed.
Lemma lem2611461 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2611462 (b : int) (c : int) (a : int) (h1 : term6 a) : (term28 b a c) = (term29 b a c).
Proof. exact (MK_COMB (@lem2611461) (@lem2611460 b c a h1)). Qed.
Lemma lem2611463 (b : int) (a : int) (c : int) : (term18 b a c) = (term18 b a c).
Proof. exact (eq_refl (term18 b a c)). Qed.
Lemma lem2611464 (b : int) (c : int) (a : int) (h1 : term6 a) : ((term17 b a c) = (term18 b a c)) = ((term18 b a c) = (term18 b a c)).
Proof. exact (MK_COMB (@lem2611462 b c a h1) (@lem2611463 b a c)). Qed.
Lemma lem2611466 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2611467 (x : Prop) : (x = x) = True.
Proof. exact (@lem2611466 Prop x). Qed.
Lemma lem2611468 (b : int) (a : int) (c : int) : ((term18 b a c) = (term18 b a c)) = True.
Proof. exact (@lem2611467 (term18 b a c)). Qed.
Lemma lem2611469 (b : int) (c : int) (a : int) (h1 : term6 a) : ((term17 b a c) = (term18 b a c)) = True.
Proof. exact (TRANS (@lem2611464 b c a h1) (@lem2611468 b a c)). Qed.
Lemma lem2611470 (b : int) (a : int) (c : int) : term30 b a c.
Proof. exact (fun h0 : term6 a => @lem2611469 b c a h0). Qed.
Lemma lem2611471 (b : int) (c : int) (a : int) : term31 b c a.
Proof. exact (@lem2611443 b c a True). Qed.
Lemma lem2611472 (b : int) (c : int) (a : int) : (term32 b a c) = (term33 a).
Proof. exact (@lem2611471 b c a (@lem2611470 b a c)). Qed.
Lemma lem2611474 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem2611475 (a : int) : (term33 a) = True.
Proof. exact (@lem2611474 (term6 a)). Qed.
Lemma lem2611476 (b : int) (a : int) (c : int) : (term32 b a c) = True.
Proof. exact (TRANS (@lem2611472 b c a) (@lem2611475 a)). Qed.
Lemma lem2611477 (b : int) (a : int) : (term34 b a) = term35.
Proof. exact (fun_ext (fun c : int => @lem2611476 b a c)). Qed.
Lemma lem2611478 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611479 (b : int) (a : int) : (term36 b a) = term37.
Proof. exact (MK_COMB (@lem2611478) (@lem2611477 b a)). Qed.
Lemma lem2611481 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611482 (t : Prop) : (term39 t) = t.
Proof. exact (@lem2611481 int t). Qed.
Lemma lem2611483 : term37 = True.
Proof. exact (@lem2611482 True). Qed.
Lemma lem2611484 (b : int) (a : int) : (term36 b a) = True.
Proof. exact (TRANS (@lem2611479 b a) (@lem2611483)). Qed.
Lemma lem2611485 (a : int) : (term40 a) = term35.
Proof. exact (fun_ext (fun b : int => @lem2611484 b a)). Qed.
Lemma lem2611486 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611487 (a : int) : (term41 a) = term37.
Proof. exact (MK_COMB (@lem2611486) (@lem2611485 a)). Qed.
Lemma lem2611489 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611490 (t : Prop) : (term39 t) = t.
Proof. exact (@lem2611489 int t). Qed.
Lemma lem2611491 : term37 = True.
Proof. exact (@lem2611490 True). Qed.
Lemma lem2611492 (a : int) : (term41 a) = True.
Proof. exact (TRANS (@lem2611487 a) (@lem2611491)). Qed.
Lemma lem2611493 : term42 = term35.
Proof. exact (fun_ext (fun a : int => @lem2611492 a)). Qed.
Lemma lem2611494 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2611495 : term43 = term37.
Proof. exact (MK_COMB (@lem2611494) (@lem2611493)). Qed.
Lemma lem2611497 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2611498 (t : Prop) : (term39 t) = t.
Proof. exact (@lem2611497 int t). Qed.
Lemma lem2611499 : term37 = True.
Proof. exact (@lem2611498 True). Qed.
Lemma lem2611500 : term43 = True.
Proof. exact (TRANS (@lem2611495) (@lem2611499)). Qed.
Lemma lem2611501 : True = term43.
Proof. exact (SYM (@lem2611500)). Qed.
Lemma lem2611502 : term43.
Proof. exact (EQ_MP (@lem2611501) (@lem0)). Qed.
