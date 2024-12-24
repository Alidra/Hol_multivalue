Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INJECTIVE_IMAGE_term_abbrevs.
Require Import INJECTIVE_ON_IMAGE_spec.
Require Import IN_UNIV_spec.
Require Import SUBSET_UNIV_spec.
Require Import thm0_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm7_spec.
Lemma lem5037471 {A : Type'} (s : A -> Prop) : term0 A s.
Proof. exact (@lem3220196 A s). Qed.
Lemma lem5037472 {A : Type'} (s : A -> Prop) : (term0 A s) = (@SUBSET A s (@UNIV A)).
Proof. exact (eq_refl (term0 A s)). Qed.
Lemma lem5037473 {A : Type'} (s : A -> Prop) : @SUBSET A s (@UNIV A).
Proof. exact (EQ_MP (@lem5037472 A s) (@lem5037471 A s)). Qed.
Lemma lem5037474 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = ((@SUBSET A s (@UNIV A)) = True).
Proof. exact (@lem7 (@SUBSET A s (@UNIV A))). Qed.
Lemma lem5037476 {A : Type'} (x : A) : term1 A x.
Proof. exact (@lem3204818 A x). Qed.
Lemma lem5037477 {A : Type'} (x : A) : (term1 A x) = (@IN A x (@UNIV A)).
Proof. exact (eq_refl (term1 A x)). Qed.
Lemma lem5037478 {A : Type'} (x : A) : @IN A x (@UNIV A).
Proof. exact (EQ_MP (@lem5037477 A x) (@lem5037476 A x)). Qed.
Lemma lem5037479 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = ((@IN A x (@UNIV A)) = True).
Proof. exact (@lem7 (@IN A x (@UNIV A))). Qed.
Lemma lem5037481 {A B : Type'} : term2 A B.
Proof. exact (@lem5037470 A B). Qed.
Lemma lem5037482 {A B : Type'} (f : A -> B) : term3 A B f.
Proof. exact (@lem5037481 A B f). Qed.
Lemma lem5037483 {A B : Type'} (f : A -> B) : (term3 A B f) = (term4 A B f).
Proof. exact (eq_refl (term3 A B f)). Qed.
Lemma lem5037484 {A B : Type'} (f : A -> B) : term4 A B f.
Proof. exact (EQ_MP (@lem5037483 A B f) (@lem5037482 A B f)). Qed.
Lemma lem5037485 {A B : Type'} (f : A -> B) : term5 A B f.
Proof. exact (@lem5037484 A B f (@UNIV A)). Qed.
Lemma lem5037486 {A B : Type'} (f : A -> B) : (term5 A B f) = ((term6 A B f) = (term7 A B f)).
Proof. exact (eq_refl (term5 A B f)). Qed.
Lemma lem5037487 {A B : Type'} (f : A -> B) : (term6 A B f) = (term7 A B f).
Proof. exact (EQ_MP (@lem5037486 A B f) (@lem5037485 A B f)). Qed.
Lemma lem5037507 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5037474 A s) (@lem5037473 A s)). Qed.
Lemma lem5037508 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (@lem5037507 A s). Qed.
Lemma lem5037509 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037510 {A : Type'} (s : A -> Prop) : (term8 A s) = (and True).
Proof. exact (MK_COMB (@lem5037509) (@lem5037508 A s)). Qed.
Lemma lem5037514 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5037474 A s) (@lem5037473 A s)). Qed.
Lemma lem5037515 {A : Type'} (s : A -> Prop) : (@SUBSET A s (@UNIV A)) = True.
Proof. exact (@lem5037514 A s). Qed.
Lemma lem5037516 {A : Type'} (t : A -> Prop) : (@SUBSET A t (@UNIV A)) = True.
Proof. exact (@lem5037515 A t). Qed.
Lemma lem5037517 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037518 {A : Type'} (t : A -> Prop) : (term8 A t) = (and True).
Proof. exact (MK_COMB (@lem5037517) (@lem5037516 A t)). Qed.
Lemma lem5037521 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : ((@IMAGE A B f s) = (@IMAGE A B f t)) = ((@IMAGE A B f s) = (@IMAGE A B f t)).
Proof. exact (eq_refl ((@IMAGE A B f s) = (@IMAGE A B f t))). Qed.
Lemma lem5037522 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term9 A B s f t) = (term10 A B s f t).
Proof. exact (MK_COMB (@lem5037518 A t) (@lem5037521 A B s f t)). Qed.
Lemma lem5037524 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5037525 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term10 A B s f t) = ((@IMAGE A B f s) = (@IMAGE A B f t)).
Proof. exact (@lem5037524 ((@IMAGE A B f s) = (@IMAGE A B f t))). Qed.
Lemma lem5037528 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term9 A B s f t) = ((@IMAGE A B f s) = (@IMAGE A B f t)).
Proof. exact (TRANS (@lem5037522 A B s f t) (@lem5037525 A B s f t)). Qed.
Lemma lem5037529 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term11 A B s f t) = (term10 A B s f t).
Proof. exact (MK_COMB (@lem5037510 A s) (@lem5037528 A B s f t)). Qed.
Lemma lem5037531 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5037532 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term10 A B s f t) = ((@IMAGE A B f s) = (@IMAGE A B f t)).
Proof. exact (@lem5037531 ((@IMAGE A B f s) = (@IMAGE A B f t))). Qed.
Lemma lem5037535 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term11 A B s f t) = ((@IMAGE A B f s) = (@IMAGE A B f t)).
Proof. exact (TRANS (@lem5037529 A B s f t) (@lem5037532 A B s f t)). Qed.
Lemma lem5037536 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037537 {A B : Type'} (s : A -> Prop) (f : A -> B) (t : A -> Prop) : (term12 A B s f t) = (term13 A B s f t).
Proof. exact (MK_COMB (@lem5037536) (@lem5037535 A B s f t)). Qed.
Lemma lem5037540 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (s = t).
Proof. exact (eq_refl (s = t)). Qed.
Lemma lem5037541 {A B : Type'} (f : A -> B) (s : A -> Prop) (t : A -> Prop) : (term14 A B f s t) = (term15 A B f s t).
Proof. exact (MK_COMB (@lem5037537 A B s f t) (@lem5037540 A s t)). Qed.
Lemma lem5037546 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term16 A B f s) = (term17 A B f s).
Proof. exact (fun_ext (fun t : A -> Prop => @lem5037541 A B f s t)). Qed.
Lemma lem5037547 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5037548 {A B : Type'} (f : A -> B) (s : A -> Prop) : (term18 A B f s) = (term19 A B f s).
Proof. exact (MK_COMB (@lem5037547 A) (@lem5037546 A B f s)). Qed.
Lemma lem5037553 {A B : Type'} (f : A -> B) : (term20 A B f) = (term21 A B f).
Proof. exact (fun_ext (fun s : A -> Prop => @lem5037548 A B f s)). Qed.
Lemma lem5037554 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem5037555 {A B : Type'} (f : A -> B) : (term6 A B f) = (term22 A B f).
Proof. exact (MK_COMB (@lem5037554 A) (@lem5037553 A B f)). Qed.
Lemma lem5037560 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem5037561 {A B : Type'} (f : A -> B) : (term23 A B f) = (term24 A B f).
Proof. exact (MK_COMB (@lem5037560) (@lem5037555 A B f)). Qed.
Lemma lem5037575 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5037479 A x) (@lem5037478 A x)). Qed.
Lemma lem5037576 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5037575 A x). Qed.
Lemma lem5037577 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037578 {A : Type'} (x : A) : (term25 A x) = (and True).
Proof. exact (MK_COMB (@lem5037577) (@lem5037576 A x)). Qed.
Lemma lem5037582 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (EQ_MP (@lem5037479 A x) (@lem5037478 A x)). Qed.
Lemma lem5037583 {A : Type'} (x : A) : (@IN A x (@UNIV A)) = True.
Proof. exact (@lem5037582 A x). Qed.
Lemma lem5037584 {A : Type'} (y : A) : (@IN A y (@UNIV A)) = True.
Proof. exact (@lem5037583 A y). Qed.
Lemma lem5037585 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem5037586 {A : Type'} (y : A) : (term25 A y) = (and True).
Proof. exact (MK_COMB (@lem5037585) (@lem5037584 A y)). Qed.
Lemma lem5037589 {A B : Type'} (x : A) (f : A -> B) (y : A) : ((f x) = (f y)) = ((f x) = (f y)).
Proof. exact (eq_refl ((f x) = (f y))). Qed.
Lemma lem5037590 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term26 A B x f y) = (term27 A B x f y).
Proof. exact (MK_COMB (@lem5037586 A y) (@lem5037589 A B x f y)). Qed.
Lemma lem5037592 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5037593 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term27 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem5037592 ((f x) = (f y))). Qed.
Lemma lem5037596 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term26 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem5037590 A B x f y) (@lem5037593 A B x f y)). Qed.
Lemma lem5037597 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term28 A B x f y) = (term27 A B x f y).
Proof. exact (MK_COMB (@lem5037578 A x) (@lem5037596 A B x f y)). Qed.
Lemma lem5037599 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem5037600 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term27 A B x f y) = ((f x) = (f y)).
Proof. exact (@lem5037599 ((f x) = (f y))). Qed.
Lemma lem5037603 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term28 A B x f y) = ((f x) = (f y)).
Proof. exact (TRANS (@lem5037597 A B x f y) (@lem5037600 A B x f y)). Qed.
Lemma lem5037604 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037605 {A B : Type'} (x : A) (f : A -> B) (y : A) : (term29 A B x f y) = (term30 A B x f y).
Proof. exact (MK_COMB (@lem5037604) (@lem5037603 A B x f y)). Qed.
Lemma lem5037608 {A : Type'} (x : A) (y : A) : (x = y) = (x = y).
Proof. exact (eq_refl (x = y)). Qed.
Lemma lem5037609 {A B : Type'} (f : A -> B) (x : A) (y : A) : (term31 A B f x y) = (term32 A B f x y).
Proof. exact (MK_COMB (@lem5037605 A B x f y) (@lem5037608 A x y)). Qed.
Lemma lem5037614 {A B : Type'} (f : A -> B) (x : A) : (term33 A B f x) = (term34 A B f x).
Proof. exact (fun_ext (fun y : A => @lem5037609 A B f x y)). Qed.
Lemma lem5037615 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037616 {A B : Type'} (f : A -> B) (x : A) : (term35 A B f x) = (term36 A B f x).
Proof. exact (MK_COMB (@lem5037615 A) (@lem5037614 A B f x)). Qed.
Lemma lem5037621 {A B : Type'} (f : A -> B) : (term37 A B f) = (term38 A B f).
Proof. exact (fun_ext (fun x : A => @lem5037616 A B f x)). Qed.
Lemma lem5037622 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem5037623 {A B : Type'} (f : A -> B) : (term7 A B f) = (term39 A B f).
Proof. exact (MK_COMB (@lem5037622 A) (@lem5037621 A B f)). Qed.
Lemma lem5037628 {A B : Type'} (f : A -> B) : ((term6 A B f) = (term7 A B f)) = ((term22 A B f) = (term39 A B f)).
Proof. exact (MK_COMB (@lem5037561 A B f) (@lem5037623 A B f)). Qed.
Lemma lem5037631 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem5037632 {A B : Type'} (f : A -> B) : (term40 A B f) = (term41 A B f).
Proof. exact (MK_COMB (@lem5037631) (@lem5037628 A B f)). Qed.
Lemma lem5037667 {A B : Type'} (f : A -> B) : ((term22 A B f) = (term39 A B f)) = ((term22 A B f) = (term39 A B f)).
Proof. exact (eq_refl ((term22 A B f) = (term39 A B f))). Qed.
Lemma lem5037668 {A B : Type'} (f : A -> B) : (term42 A B f) = (term43 A B f).
Proof. exact (MK_COMB (@lem5037632 A B f) (@lem5037667 A B f)). Qed.
Lemma lem5037672 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem5037673 {A B : Type'} (f : A -> B) : (term43 A B f) = True.
Proof. exact (@lem5037672 ((term22 A B f) = (term39 A B f))). Qed.
Lemma lem5037674 {A B : Type'} (f : A -> B) : (term42 A B f) = True.
Proof. exact (TRANS (@lem5037668 A B f) (@lem5037673 A B f)). Qed.
Lemma lem5037675 {A B : Type'} (f : A -> B) : True = (term42 A B f).
Proof. exact (SYM (@lem5037674 A B f)). Qed.
Lemma lem5037676 {A B : Type'} (f : A -> B) : term42 A B f.
Proof. exact (EQ_MP (@lem5037675 A B f) (@lem0)). Qed.
Lemma lem5037677 {A B : Type'} (f : A -> B) : (term22 A B f) = (term39 A B f).
Proof. exact (@lem5037676 A B f (@lem5037487 A B f)). Qed.
Lemma lem5037682 {A B : Type'} : term44 A B.
Proof. exact (fun f : A -> B => @lem5037677 A B f). Qed.
