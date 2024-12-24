Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INTERSECTION_OF_INC_term_abbrevs.
Require Import INTERSECTION_OF_spec.
Require Import IN_SING_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm3354723_spec.
Require Import thm3355403_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem4842425 {A : Type'} (P : type180 A) : term0 A P.
Proof. exact (@lem4842239 A P). Qed.
Lemma lem4842426 {A : Type'} (P : type180 A) : (term0 A P) = (term1 A P).
Proof. exact (eq_refl (term0 A P)). Qed.
Lemma lem4842427 {A : Type'} (P : type180 A) : term1 A P.
Proof. exact (EQ_MP (@lem4842426 A P) (@lem4842425 A P)). Qed.
Lemma lem4842428 {A : Type'} (P : type180 A) (Q : type686 A) : term2 A P Q.
Proof. exact (@lem4842427 A P Q). Qed.
Lemma lem4842429 {A : Type'} (P : type180 A) (Q : type686 A) : (term2 A P Q) = ((@INTERSECTION_OF A P Q) = (term3 A P Q)).
Proof. exact (eq_refl (term2 A P Q)). Qed.
Lemma lem4842431 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : term4 A P Q s.
Proof. exact (h1). Qed.
Lemma lem4842432 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : Q s.
Proof. exact (h1). Qed.
Lemma lem4842433 {A : Type'} (P : type180 A) (s : A -> Prop) (h1 : term5 A P s) : term5 A P s.
Proof. exact (h1). Qed.
Lemma lem4842435 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (EQ_MP (@lem4842429 A P Q) (@lem4842428 A P Q)). Qed.
Lemma lem4842436 {A : Type'} (P : type180 A) (Q : type686 A) : (@INTERSECTION_OF A P Q) = (term3 A P Q).
Proof. exact (@lem4842435 A P Q). Qed.
Lemma lem4842453 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842454 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q s) = (term6 A P Q s).
Proof. exact (MK_COMB (@lem4842436 A P Q) (@lem4842453 A s)). Qed.
Lemma lem4842456 {A B : Type'} (f : A -> B) (y : A) : (term7 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem4842457 {A : Type'} (f : type686 A) (y : A -> Prop) : (term8 A f y) = (f y).
Proof. exact (@lem4842456 (A -> Prop) Prop f y). Qed.
Lemma lem4842458 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term9 A P Q s) = (term6 A P Q s).
Proof. exact (@lem4842457 A (term3 A P Q) s). Qed.
Lemma lem4842459 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term10 A P Q s).
Proof. exact (eq_refl (term6 A P Q s)). Qed.
Lemma lem4842460 {A : Type'} (P : type180 A) (Q : type686 A) : (term11 A P Q) = (term3 A P Q).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4842459 A P Q s)). Qed.
Lemma lem4842461 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842462 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term9 A P Q s) = (term6 A P Q s).
Proof. exact (MK_COMB (@lem4842460 A P Q) (@lem4842461 A s)). Qed.
Lemma lem4842463 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4842464 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term12 A P Q s) = (term13 A P Q s).
Proof. exact (MK_COMB (@lem4842463) (@lem4842462 A P Q s)). Qed.
Lemma lem4842465 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term10 A P Q s).
Proof. exact (eq_refl (term6 A P Q s)). Qed.
Lemma lem4842466 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : ((term9 A P Q s) = (term6 A P Q s)) = ((term6 A P Q s) = (term10 A P Q s)).
Proof. exact (MK_COMB (@lem4842464 A P Q s) (@lem4842465 A P Q s)). Qed.
Lemma lem4842467 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term6 A P Q s) = (term10 A P Q s).
Proof. exact (EQ_MP (@lem4842466 A P Q s) (@lem4842458 A P Q s)). Qed.
Lemma lem4842484 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (@INTERSECTION_OF A P Q s) = (term10 A P Q s).
Proof. exact (TRANS (@lem4842454 A P Q s) (@lem4842467 A P Q s)). Qed.
Lemma lem4842485 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : (term10 A P Q s) = (@INTERSECTION_OF A P Q s).
Proof. exact (SYM (@lem4842484 A P Q s)). Qed.
Lemma lem4842486 {A : Type'} (x : A) : term14 A x.
Proof. exact (@lem3205876 A x). Qed.
Lemma lem4842487 {A : Type'} (x : A) : (term14 A x) = (term15 A x).
Proof. exact (eq_refl (term14 A x)). Qed.
Lemma lem4842488 {A : Type'} (x : A) : term15 A x.
Proof. exact (EQ_MP (@lem4842487 A x) (@lem4842486 A x)). Qed.
Lemma lem4842489 {A : Type'} (x : A) (y : A) : term16 A x y.
Proof. exact (@lem4842488 A x y). Qed.
Lemma lem4842490 {A : Type'} (x : A) (y : A) : (term16 A x y) = ((term17 A x y) = (x = y)).
Proof. exact (eq_refl (term16 A x y)). Qed.
Lemma lem4842492 {A : Type'} (P : type180 A) (s : A -> Prop) : (term5 A P s) = ((term5 A P s) = True).
Proof. exact (@lem7 (term5 A P s)). Qed.
Lemma lem4842494 {A : Type'} (Q : type686 A) (s : A -> Prop) : (Q s) = ((Q s) = True).
Proof. exact (@lem7 (Q s)). Qed.
Lemma lem4842499 {A : Type'} (P : type180 A) (s : A -> Prop) (h1 : term5 A P s) : (term5 A P s) = True.
Proof. exact (EQ_MP (@lem4842492 A P s) (@lem4842433 A P s h1)). Qed.
Lemma lem4842500 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842501 {A : Type'} (P : type180 A) (s : A -> Prop) (h1 : term5 A P s) : (term18 A P s) = (and True).
Proof. exact (MK_COMB (@lem4842500) (@lem4842499 A P s h1)). Qed.
Lemma lem4842511 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term19 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem4842512 (p : Prop) (q : Prop) (p' : Prop) : term20 p q p'.
Proof. exact (fun q' : Prop => @lem4842511 p q p' q'). Qed.
Lemma lem4842513 (p : Prop) (q : Prop) : term21 p q.
Proof. exact (fun p' : Prop => @lem4842512 p q p'). Qed.
Lemma lem4842514 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) : term22 A s Q c.
Proof. exact (@lem4842513 (term23 A c s) (Q c)). Qed.
Lemma lem4842515 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) : term24 A s Q c p'.
Proof. exact (@lem4842514 A s Q c p'). Qed.
Lemma lem4842516 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) : (term24 A s Q c p') = (term25 A s Q c p').
Proof. exact (eq_refl (term24 A s Q c p')). Qed.
Lemma lem4842517 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) : term25 A s Q c p'.
Proof. exact (EQ_MP (@lem4842516 A s Q c p') (@lem4842515 A s Q c p')). Qed.
Lemma lem4842518 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) (q' : Prop) : term26 A s Q c p' q'.
Proof. exact (@lem4842517 A s Q c p' q'). Qed.
Lemma lem4842519 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) (q' : Prop) : (term26 A s Q c p' q') = (term27 A s Q c p' q').
Proof. exact (eq_refl (term26 A s Q c p' q')). Qed.
Lemma lem4842520 {A : Type'} (s : A -> Prop) (Q : type686 A) (c : A -> Prop) (p' : Prop) (q' : Prop) : term27 A s Q c p' q'.
Proof. exact (EQ_MP (@lem4842519 A s Q c p' q') (@lem4842518 A s Q c p' q')). Qed.
Lemma lem4842522 {A : Type'} (x : A) (y : A) : (term17 A x y) = (x = y).
Proof. exact (EQ_MP (@lem4842490 A x y) (@lem4842489 A x y)). Qed.
Lemma lem4842523 {A : Type'} (x : A -> Prop) (y : A -> Prop) : (term23 A x y) = (x = y).
Proof. exact (@lem4842522 (A -> Prop) x y). Qed.
Lemma lem4842524 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term23 A c s) = (c = s).
Proof. exact (@lem4842523 A c s). Qed.
Lemma lem4842527 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (q' : Prop) : term28 A Q c s q'.
Proof. exact (@lem4842520 A s Q c (c = s) q'). Qed.
Lemma lem4842528 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (q' : Prop) : term29 A Q c s q'.
Proof. exact (@lem4842527 A Q c s q' (@lem4842524 A c s)). Qed.
Lemma lem4842531 {A : Type'} (c : A -> Prop) (s : A -> Prop) (h1 : c = s) : c = s.
Proof. exact (h1). Qed.
Lemma lem4842532 {A : Type'} (Q : type686 A) : Q = Q.
Proof. exact (eq_refl Q). Qed.
Lemma lem4842533 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (h1 : c = s) : (Q c) = (Q s).
Proof. exact (MK_COMB (@lem4842532 A Q) (@lem4842531 A c s h1)). Qed.
Lemma lem4842535 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (Q s) = True.
Proof. exact (EQ_MP (@lem4842494 A Q s) (@lem4842432 A Q s h1)). Qed.
Lemma lem4842536 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) (h1 : Q s) (h2 : c = s) : (Q c) = True.
Proof. exact (TRANS (@lem4842533 A Q c s h2) (@lem4842535 A Q s h1)). Qed.
Lemma lem4842537 {A : Type'} (c : A -> Prop) (Q : type686 A) (s : A -> Prop) (h1 : Q s) : term30 A s Q c.
Proof. exact (fun h0 : c = s => @lem4842536 A Q c s h1 h0). Qed.
Lemma lem4842538 {A : Type'} (Q : type686 A) (c : A -> Prop) (s : A -> Prop) : term31 A Q c s.
Proof. exact (@lem4842528 A Q c s True). Qed.
Lemma lem4842539 {A : Type'} (c : A -> Prop) (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term32 A s Q c) = (term33 A c s).
Proof. exact (@lem4842538 A Q c s (@lem4842537 A c Q s h1)). Qed.
Lemma lem4842543 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem4842544 {A : Type'} (c : A -> Prop) (s : A -> Prop) : (term33 A c s) = True.
Proof. exact (@lem4842543 (c = s)). Qed.
Lemma lem4842545 {A : Type'} (c : A -> Prop) (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term32 A s Q c) = True.
Proof. exact (TRANS (@lem4842539 A c Q s h1) (@lem4842544 A c s)). Qed.
Lemma lem4842546 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term34 A s Q) = (term35 A).
Proof. exact (fun_ext (fun c : A -> Prop => @lem4842545 A c Q s h1)). Qed.
Lemma lem4842547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4842548 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term36 A s Q) = (term37 A).
Proof. exact (MK_COMB (@lem4842547 A) (@lem4842546 A Q s h1)). Qed.
Lemma lem4842550 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem4842551 {A : Type'} (t : Prop) : (term39 A t) = t.
Proof. exact (@lem4842550 (A -> Prop) t). Qed.
Lemma lem4842552 {A : Type'} : (term37 A) = True.
Proof. exact (@lem4842551 A True). Qed.
Lemma lem4842553 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term36 A s Q) = True.
Proof. exact (TRANS (@lem4842548 A Q s h1) (@lem4842552 A)). Qed.
Lemma lem4842554 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4842555 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term40 A s Q) = (and True).
Proof. exact (MK_COMB (@lem4842554) (@lem4842553 A Q s h1)). Qed.
Lemma lem4842559 {_87240 : Type'} (s : _87240 -> Prop) : (term41 _87240 s) = s.
Proof. exact (EQ_MP (@lem3354723 _87240 s) (@lem3355403 _87240 s)). Qed.
Lemma lem4842560 {A : Type'} (s : A -> Prop) : (term41 A s) = s.
Proof. exact (@lem4842559 A s). Qed.
Lemma lem4842561 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4842562 {A : Type'} (s : A -> Prop) : (term42 A s) = (@eq (A -> Prop) s).
Proof. exact (MK_COMB (@lem4842561 A) (@lem4842560 A s)). Qed.
Lemma lem4842563 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4842564 {A : Type'} (s : A -> Prop) : ((term41 A s) = s) = (s = s).
Proof. exact (MK_COMB (@lem4842562 A s) (@lem4842563 A s)). Qed.
Lemma lem4842566 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4842567 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4842566 (A -> Prop) x). Qed.
Lemma lem4842568 {A : Type'} (s : A -> Prop) : (s = s) = True.
Proof. exact (@lem4842567 A s). Qed.
Lemma lem4842569 {A : Type'} (s : A -> Prop) : ((term41 A s) = s) = True.
Proof. exact (TRANS (@lem4842564 A s) (@lem4842568 A s)). Qed.
Lemma lem4842570 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term43 A Q s) = (True /\ True).
Proof. exact (MK_COMB (@lem4842555 A Q s h1) (@lem4842569 A s)). Qed.
Lemma lem4842572 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4842573 : (True /\ True) = True.
Proof. exact (@lem4842572 True). Qed.
Lemma lem4842574 {A : Type'} (Q : type686 A) (s : A -> Prop) (h1 : Q s) : (term43 A Q s) = True.
Proof. exact (TRANS (@lem4842570 A Q s h1) (@lem4842573)). Qed.
Lemma lem4842575 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (term44 A P Q s) = (True /\ True).
Proof. exact (MK_COMB (@lem4842501 A P s h1) (@lem4842574 A Q s h2)). Qed.
Lemma lem4842577 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4842578 : (True /\ True) = True.
Proof. exact (@lem4842577 True). Qed.
Lemma lem4842579 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (term44 A P Q s) = True.
Proof. exact (TRANS (@lem4842575 A P Q s h1 h2) (@lem4842578)). Qed.
Lemma lem4842580 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : True = (term44 A P Q s).
Proof. exact (SYM (@lem4842579 A P Q s h1 h2)). Qed.
Lemma lem4842581 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : term44 A P Q s.
Proof. exact (EQ_MP (@lem4842580 A P Q s h1 h2) (@lem0)). Qed.
Lemma lem4842582 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : term10 A P Q s.
Proof. exact (ex_intro (term45 A P Q s) (@INSERT (A -> Prop) s (@EMPTY (A -> Prop))) (@lem4842581 A P Q s h1 h2)). Qed.
Lemma lem4842583 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : @INTERSECTION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842485 A P Q s) (@lem4842582 A P Q s h1 h2)). Qed.
Lemma lem4842584 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : Q s.
Proof. exact (proj2 (@lem4842431 A P Q s h1)). Qed.
Lemma lem4842585 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : term5 A P s.
Proof. exact (proj1 (@lem4842431 A P Q s h1)). Qed.
Lemma lem4842586 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (Q s) = (@INTERSECTION_OF A P Q s).
Proof. exact (prop_ext (fun h3 : Q s => @lem4842583 A P Q s h1 h2) (fun h3 : @INTERSECTION_OF A P Q s => @lem4842432 A Q s h2)). Qed.
Lemma lem4842587 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : @INTERSECTION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842586 A P Q s h1 h2) (@lem4842432 A Q s h2)). Qed.
Lemma lem4842588 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : (term5 A P s) = (@INTERSECTION_OF A P Q s).
Proof. exact (prop_ext (fun h3 : term5 A P s => @lem4842587 A P Q s h1 h2) (fun h3 : @INTERSECTION_OF A P Q s => @lem4842433 A P s h1)). Qed.
Lemma lem4842589 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : Q s) : @INTERSECTION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842588 A P Q s h1 h2) (@lem4842433 A P s h1)). Qed.
Lemma lem4842590 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : term4 A P Q s) : (Q s) = (@INTERSECTION_OF A P Q s).
Proof. exact (prop_ext (fun h3 : Q s => @lem4842589 A P Q s h1 h3) (fun h3 : @INTERSECTION_OF A P Q s => @lem4842584 A P Q s h2)). Qed.
Lemma lem4842591 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term5 A P s) (h2 : term4 A P Q s) : @INTERSECTION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842590 A P Q s h1 h2) (@lem4842584 A P Q s h2)). Qed.
Lemma lem4842592 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : (term5 A P s) = (@INTERSECTION_OF A P Q s).
Proof. exact (prop_ext (fun h2 : term5 A P s => @lem4842591 A P Q s h2 h1) (fun h2 : @INTERSECTION_OF A P Q s => @lem4842585 A P Q s h1)). Qed.
Lemma lem4842593 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) (h1 : term4 A P Q s) : @INTERSECTION_OF A P Q s.
Proof. exact (EQ_MP (@lem4842592 A P Q s h1) (@lem4842585 A P Q s h1)). Qed.
Lemma lem4842594 {A : Type'} (P : type180 A) (Q : type686 A) (s : A -> Prop) : term46 A P Q s.
Proof. exact (fun h0 : term4 A P Q s => @lem4842593 A P Q s h0). Qed.
Lemma lem4842599 {A : Type'} (P : type180 A) (Q : type686 A) : term47 A P Q.
Proof. exact (fun s : A -> Prop => @lem4842594 A P Q s). Qed.
Lemma lem4842604 {A : Type'} (P : type180 A) : term48 A P.
Proof. exact (fun Q : type686 A => @lem4842599 A P Q). Qed.
Lemma lem4842609 {A : Type'} : term49 A.
Proof. exact (fun P : type180 A => @lem4842604 A P). Qed.
