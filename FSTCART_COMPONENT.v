Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import FSTCART_COMPONENT_term_abbrevs.
Require Import LAMBDA_BETA_spec.
Require Import fstcart_spec.
Require Import thm0_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1821_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4211_spec.
Require Import thm7_spec.
Lemma lem7664495 {A B : Type'} (g : nat -> A) (i : nat) : term0 A B g i.
Proof. exact (@lem7622314 A B g i). Qed.
Lemma lem7664496 {A B : Type'} (g : nat -> A) (i : nat) : (term0 A B g i) = (term1 A B g i).
Proof. exact (eq_refl (term0 A B g i)). Qed.
Lemma lem7664497 {A B : Type'} (g : nat -> A) (i : nat) : term1 A B g i.
Proof. exact (EQ_MP (@lem7664496 A B g i) (@lem7664495 A B g i)). Qed.
Lemma lem7664498 {B : Type'} (i : nat) (h1 : term2 B i) : term2 B i.
Proof. exact (h1). Qed.
Lemma lem7664499 {A B : Type'} (g : nat -> A) (i : nat) (h1 : term2 B i) : (term3 A B g i) = (g i).
Proof. exact (@lem7664497 A B g i (@lem7664498 B i h1)). Qed.
Lemma lem7664505 {A M N : Type'} (f : type2 A M N) : term4 A M N f.
Proof. exact (@lem7633949 A M N f). Qed.
Lemma lem7664506 {A M N : Type'} (f : type2 A M N) : (term4 A M N f) = ((@fstcart A M N f) = (term5 A M N f)).
Proof. exact (eq_refl (term4 A M N f)). Qed.
Lemma lem7664519 (p : Prop) (q : Prop) (p' : Prop) (q' : Prop) : term6 p q p' q'.
Proof. exact (fun h0 : p = p' => @lem4211 q q' p p' h0). Qed.
Lemma lem7664520 (p : Prop) (q : Prop) (p' : Prop) : term7 p q p'.
Proof. exact (fun q' : Prop => @lem7664519 p q p' q'). Qed.
Lemma lem7664521 (p : Prop) (q : Prop) : term8 p q.
Proof. exact (fun p' : Prop => @lem7664520 p q p'). Qed.
Lemma lem7664522 {A M N : Type'} (x : type2 A M N) (i : nat) : term9 A M N x i.
Proof. exact (@lem7664521 (term2 M i) ((term10 A M N x i) = (@dollar A (finite_sum M N) x i))). Qed.
Lemma lem7664523 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) : term11 A M N x i p'.
Proof. exact (@lem7664522 A M N x i p'). Qed.
Lemma lem7664524 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) : (term11 A M N x i p') = (term12 A M N x i p').
Proof. exact (eq_refl (term11 A M N x i p')). Qed.
Lemma lem7664525 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) : term12 A M N x i p'.
Proof. exact (EQ_MP (@lem7664524 A M N x i p') (@lem7664523 A M N x i p')). Qed.
Lemma lem7664526 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) (q' : Prop) : term13 A M N x i p' q'.
Proof. exact (@lem7664525 A M N x i p' q'). Qed.
Lemma lem7664527 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) (q' : Prop) : (term13 A M N x i p' q') = (term14 A M N x i p' q').
Proof. exact (eq_refl (term13 A M N x i p' q')). Qed.
Lemma lem7664528 {A M N : Type'} (x : type2 A M N) (i : nat) (p' : Prop) (q' : Prop) : term14 A M N x i p' q'.
Proof. exact (EQ_MP (@lem7664527 A M N x i p' q') (@lem7664526 A M N x i p' q')). Qed.
Lemma lem7664531 {M : Type'} (i : nat) : (term2 M i) = (term2 M i).
Proof. exact (eq_refl (term2 M i)). Qed.
Lemma lem7664532 {A M N : Type'} (x : type2 A M N) (i : nat) (q' : Prop) : term15 A M N x i q'.
Proof. exact (@lem7664528 A M N x i (term2 M i) q'). Qed.
Lemma lem7664533 {A M N : Type'} (x : type2 A M N) (i : nat) (q' : Prop) : term16 A M N x i q'.
Proof. exact (@lem7664532 A M N x i q' (@lem7664531 M i)). Qed.
Lemma lem7664534 {M : Type'} (i : nat) (h1 : term2 M i) : term2 M i.
Proof. exact (h1). Qed.
Lemma lem7664535 {M : Type'} (i : nat) (h1 : term2 M i) : term17 M i.
Proof. exact (proj2 (@lem7664534 M i h1)). Qed.
Lemma lem7664536 {M : Type'} (i : nat) : (term17 M i) = ((term17 M i) = True).
Proof. exact (@lem7 (term17 M i)). Qed.
Lemma lem7664538 {M : Type'} (i : nat) (h1 : term2 M i) : term18 i.
Proof. exact (proj1 (@lem7664534 M i h1)). Qed.
Lemma lem7664539 (i : nat) : (term18 i) = ((term18 i) = True).
Proof. exact (@lem7 (term18 i)). Qed.
Lemma lem7664544 {A M N : Type'} (f : type2 A M N) : (@fstcart A M N f) = (term5 A M N f).
Proof. exact (EQ_MP (@lem7664506 A M N f) (@lem7664505 A M N f)). Qed.
Lemma lem7664545 {A M N : Type'} (f : type2 A M N) : (@fstcart A M N f) = (term5 A M N f).
Proof. exact (@lem7664544 A M N f). Qed.
Lemma lem7664546 {A M N : Type'} (x : type2 A M N) : (@fstcart A M N x) = (term5 A M N x).
Proof. exact (@lem7664545 A M N x). Qed.
Lemma lem7664547 {A M : Type'} : (@dollar A M) = (@dollar A M).
Proof. exact (eq_refl (@dollar A M)). Qed.
Lemma lem7664548 {A M N : Type'} (x : type2 A M N) : (term19 A M N x) = (term20 A M N x).
Proof. exact (MK_COMB (@lem7664547 A M) (@lem7664546 A M N x)). Qed.
Lemma lem7664549 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7664550 {A M N : Type'} (x : type2 A M N) (i : nat) : (term10 A M N x i) = (term21 A M N x i).
Proof. exact (MK_COMB (@lem7664548 A M N x) (@lem7664549 i)). Qed.
Lemma lem7664552 {A B : Type'} (g : nat -> A) (i : nat) : term1 A B g i.
Proof. exact (fun h0 : term2 B i => @lem7664499 A B g i h0). Qed.
Lemma lem7664553 {A M : Type'} (g : nat -> A) (i : nat) : term1 A M g i.
Proof. exact (@lem7664552 A M g i). Qed.
Lemma lem7664554 {A M N : Type'} (x : type2 A M N) (i : nat) : term22 A M N x i.
Proof. exact (@lem7664553 A M (term23 A M N x) i). Qed.
Lemma lem7664558 {M : Type'} (i : nat) (h1 : term2 M i) : (term18 i) = True.
Proof. exact (EQ_MP (@lem7664539 i) (@lem7664538 M i h1)). Qed.
Lemma lem7664559 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem7664560 {M : Type'} (i : nat) (h1 : term2 M i) : (term24 i) = (and True).
Proof. exact (MK_COMB (@lem7664559) (@lem7664558 M i h1)). Qed.
Lemma lem7664562 {M : Type'} (i : nat) (h1 : term2 M i) : (term17 M i) = True.
Proof. exact (EQ_MP (@lem7664536 M i) (@lem7664535 M i h1)). Qed.
Lemma lem7664563 {M : Type'} (i : nat) (h1 : term2 M i) : (term2 M i) = (True /\ True).
Proof. exact (MK_COMB (@lem7664560 M i h1) (@lem7664562 M i h1)). Qed.
Lemma lem7664565 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem7664566 : (True /\ True) = True.
Proof. exact (@lem7664565 True). Qed.
Lemma lem7664567 {M : Type'} (i : nat) (h1 : term2 M i) : (term2 M i) = True.
Proof. exact (TRANS (@lem7664563 M i h1) (@lem7664566)). Qed.
Lemma lem7664568 {M : Type'} (i : nat) (h1 : term2 M i) : True = (term2 M i).
Proof. exact (SYM (@lem7664567 M i h1)). Qed.
Lemma lem7664569 {M : Type'} (i : nat) (h1 : term2 M i) : term2 M i.
Proof. exact (EQ_MP (@lem7664568 M i h1) (@lem0)). Qed.
Lemma lem7664570 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 M i) : (term21 A M N x i) = (term25 A M N x i).
Proof. exact (@lem7664554 A M N x i (@lem7664569 M i h1)). Qed.
Lemma lem7664572 {A B : Type'} (f : A -> B) (y : A) : (term26 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem7664573 {A : Type'} (f : nat -> A) (y : nat) : (term27 A f y) = (f y).
Proof. exact (@lem7664572 nat A f y). Qed.
Lemma lem7664574 {A M N : Type'} (x : type2 A M N) (i : nat) : (term28 A M N x i) = (term25 A M N x i).
Proof. exact (@lem7664573 A (term23 A M N x) i). Qed.
Lemma lem7664575 {A M N : Type'} (x : type2 A M N) (i : nat) : (term25 A M N x i) = (@dollar A (finite_sum M N) x i).
Proof. exact (eq_refl (term25 A M N x i)). Qed.
Lemma lem7664576 {A M N : Type'} (x : type2 A M N) : (term29 A M N x) = (term23 A M N x).
Proof. exact (fun_ext (fun i : nat => @lem7664575 A M N x i)). Qed.
Lemma lem7664577 (i : nat) : i = i.
Proof. exact (eq_refl i). Qed.
Lemma lem7664578 {A M N : Type'} (x : type2 A M N) (i : nat) : (term28 A M N x i) = (term25 A M N x i).
Proof. exact (MK_COMB (@lem7664576 A M N x) (@lem7664577 i)). Qed.
Lemma lem7664579 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7664580 {A M N : Type'} (x : type2 A M N) (i : nat) : (term30 A M N x i) = (term31 A M N x i).
Proof. exact (MK_COMB (@lem7664579 A) (@lem7664578 A M N x i)). Qed.
Lemma lem7664581 {A M N : Type'} (x : type2 A M N) (i : nat) : (term25 A M N x i) = (@dollar A (finite_sum M N) x i).
Proof. exact (eq_refl (term25 A M N x i)). Qed.
Lemma lem7664582 {A M N : Type'} (x : type2 A M N) (i : nat) : ((term28 A M N x i) = (term25 A M N x i)) = ((term25 A M N x i) = (@dollar A (finite_sum M N) x i)).
Proof. exact (MK_COMB (@lem7664580 A M N x i) (@lem7664581 A M N x i)). Qed.
Lemma lem7664583 {A M N : Type'} (x : type2 A M N) (i : nat) : (term25 A M N x i) = (@dollar A (finite_sum M N) x i).
Proof. exact (EQ_MP (@lem7664582 A M N x i) (@lem7664574 A M N x i)). Qed.
Lemma lem7664584 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 M i) : (term21 A M N x i) = (@dollar A (finite_sum M N) x i).
Proof. exact (TRANS (@lem7664570 A M N x i h1) (@lem7664583 A M N x i)). Qed.
Lemma lem7664585 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 M i) : (term10 A M N x i) = (@dollar A (finite_sum M N) x i).
Proof. exact (TRANS (@lem7664550 A M N x i) (@lem7664584 A M N x i h1)). Qed.
Lemma lem7664586 {A : Type'} : (@eq A) = (@eq A).
Proof. exact (eq_refl (@eq A)). Qed.
Lemma lem7664587 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 M i) : (term32 A M N x i) = (term33 A M N x i).
Proof. exact (MK_COMB (@lem7664586 A) (@lem7664585 A M N x i h1)). Qed.
Lemma lem7664588 {A M N : Type'} (x : type2 A M N) (i : nat) : (@dollar A (finite_sum M N) x i) = (@dollar A (finite_sum M N) x i).
Proof. exact (eq_refl (@dollar A (finite_sum M N) x i)). Qed.
Lemma lem7664589 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 M i) : ((term10 A M N x i) = (@dollar A (finite_sum M N) x i)) = ((@dollar A (finite_sum M N) x i) = (@dollar A (finite_sum M N) x i)).
Proof. exact (MK_COMB (@lem7664587 A M N x i h1) (@lem7664588 A M N x i)). Qed.
Lemma lem7664591 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem7664592 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (@lem7664591 A x). Qed.
Lemma lem7664593 {A M N : Type'} (x : type2 A M N) (i : nat) : ((@dollar A (finite_sum M N) x i) = (@dollar A (finite_sum M N) x i)) = True.
Proof. exact (@lem7664592 A (@dollar A (finite_sum M N) x i)). Qed.
Lemma lem7664594 {A M N : Type'} (x : type2 A M N) (i : nat) (h1 : term2 M i) : ((term10 A M N x i) = (@dollar A (finite_sum M N) x i)) = True.
Proof. exact (TRANS (@lem7664589 A M N x i h1) (@lem7664593 A M N x i)). Qed.
Lemma lem7664595 {A M N : Type'} (x : type2 A M N) (i : nat) : term34 A M N x i.
Proof. exact (fun h0 : term2 M i => @lem7664594 A M N x i h0). Qed.
Lemma lem7664596 {A M N : Type'} (x : type2 A M N) (i : nat) : term35 A M N x i.
Proof. exact (@lem7664533 A M N x i True). Qed.
Lemma lem7664597 {A M N : Type'} (x : type2 A M N) (i : nat) : (term36 A M N x i) = (term37 M i).
Proof. exact (@lem7664596 A M N x i (@lem7664595 A M N x i)). Qed.
Lemma lem7664599 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem7664600 {M : Type'} (i : nat) : (term37 M i) = True.
Proof. exact (@lem7664599 (term2 M i)). Qed.
Lemma lem7664601 {A M N : Type'} (x : type2 A M N) (i : nat) : (term36 A M N x i) = True.
Proof. exact (TRANS (@lem7664597 A M N x i) (@lem7664600 M i)). Qed.
Lemma lem7664602 {A M N : Type'} (x : type2 A M N) : (term38 A M N x) = term39.
Proof. exact (fun_ext (fun i : nat => @lem7664601 A M N x i)). Qed.
Lemma lem7664603 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem7664604 {A M N : Type'} (x : type2 A M N) : (term40 A M N x) = term41.
Proof. exact (MK_COMB (@lem7664603) (@lem7664602 A M N x)). Qed.
Lemma lem7664606 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664607 (t : Prop) : (term43 t) = t.
Proof. exact (@lem7664606 nat t). Qed.
Lemma lem7664608 : term41 = True.
Proof. exact (@lem7664607 True). Qed.
Lemma lem7664609 {A M N : Type'} (x : type2 A M N) : (term40 A M N x) = True.
Proof. exact (TRANS (@lem7664604 A M N x) (@lem7664608)). Qed.
Lemma lem7664610 {A M N : Type'} : (term44 A M N) = (term45 A M N).
Proof. exact (fun_ext (fun x : type2 A M N => @lem7664609 A M N x)). Qed.
Lemma lem7664611 {A M N : Type'} : (@all (cart A (finite_sum M N))) = (@all (cart A (finite_sum M N))).
Proof. exact (eq_refl (@all (cart A (finite_sum M N)))). Qed.
Lemma lem7664612 {A M N : Type'} : (term46 A M N) = (term47 A M N).
Proof. exact (MK_COMB (@lem7664611 A M N) (@lem7664610 A M N)). Qed.
Lemma lem7664614 {A : Type'} (t : Prop) : (term42 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem7664615 {A M N : Type'} (t : Prop) : (term48 A M N t) = t.
Proof. exact (@lem7664614 (type2 A M N) t). Qed.
Lemma lem7664616 {A M N : Type'} : (term47 A M N) = True.
Proof. exact (@lem7664615 A M N True). Qed.
Lemma lem7664617 {A M N : Type'} : (term46 A M N) = True.
Proof. exact (TRANS (@lem7664612 A M N) (@lem7664616 A M N)). Qed.
Lemma lem7664618 {A M N : Type'} : True = (term46 A M N).
Proof. exact (SYM (@lem7664617 A M N)). Qed.
Lemma lem7664619 {A M N : Type'} : term46 A M N.
Proof. exact (EQ_MP (@lem7664618 A M N) (@lem0)). Qed.
