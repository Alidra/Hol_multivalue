Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import REAL_POW2_ABS_term_abbrevs.
Require Import ARITH_EVEN_spec.
Require Import REAL_POW_NEG_spec.
Require Import real_abs_spec.
Require Import thm0_spec.
Require Import thm12653_spec.
Require Import thm13473_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Lemma lem1643458 (x : real) : term0 x.
Proof. exact (@lem1343359 x). Qed.
Lemma lem1643459 (x : real) : (term0 x) = ((real_abs x) = (term1 x)).
Proof. exact (eq_refl (term0 x)). Qed.
Lemma lem1643464 (x : real) : (real_abs x) = (term1 x).
Proof. exact (EQ_MP (@lem1643459 x) (@lem1643458 x)). Qed.
Lemma lem1643465 : real_pow = real_pow.
Proof. exact (eq_refl real_pow). Qed.
Lemma lem1643466 (x : real) : (term2 x) = (term3 x).
Proof. exact (MK_COMB (@lem1643465) (@lem1643464 x)). Qed.
Lemma lem1643467 : term4 = term4.
Proof. exact (eq_refl term4). Qed.
Lemma lem1643468 (x : real) : (term5 x) = (term6 x).
Proof. exact (MK_COMB (@lem1643466 x) (@lem1643467)). Qed.
Lemma lem1643469 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1643470 (x : real) : (term7 x) = (term8 x).
Proof. exact (MK_COMB (@lem1643469) (@lem1643468 x)). Qed.
Lemma lem1643471 (x : real) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1643472 (x : real) : ((term5 x) = (term9 x)) = ((term6 x) = (term9 x)).
Proof. exact (MK_COMB (@lem1643470 x) (@lem1643471 x)). Qed.
Lemma lem1643475 (x : real) : ((term6 x) = (term9 x)) = ((term5 x) = (term9 x)).
Proof. exact (SYM (@lem1643472 x)). Qed.
Lemma lem1643476 (_474 : real) (_475 : Prop) (_476 : real -> Prop) (_477 : real) : (term10 _476 _475 _474 _477) = (term11 _474 _475 _476 _477).
Proof. exact (@lem13473 real _474 _475 _476 _477). Qed.
Lemma lem1643477 (_474 : real) (_475 : Prop) (x : real) (_477 : real) : (term12 x _475 _474 _477) = (term13 _474 _475 x _477).
Proof. exact (@lem1643476 _474 _475 (term14 x) _477). Qed.
Lemma lem1643478 (x : real) : (term15 x) = (term16 x).
Proof. exact (@lem1643477 x (term17 x) x (real_neg x)). Qed.
Lemma lem1643479 (x : real) : (term18 x) = ((term19 x) = (term9 x)).
Proof. exact (eq_refl (term18 x)). Qed.
Lemma lem1643480 (x : real) : (term20 x) = (term20 x).
Proof. exact (eq_refl (term20 x)). Qed.
Lemma lem1643481 (x : real) : (term21 x) = (term22 x).
Proof. exact (MK_COMB (@lem1643480 x) (@lem1643479 x)). Qed.
Lemma lem1643482 (x : real) : (term23 x) = ((term9 x) = (term9 x)).
Proof. exact (eq_refl (term23 x)). Qed.
Lemma lem1643483 (x : real) : (term24 x) = (term24 x).
Proof. exact (eq_refl (term24 x)). Qed.
Lemma lem1643484 (x : real) : (term25 x) = (term26 x).
Proof. exact (MK_COMB (@lem1643483 x) (@lem1643482 x)). Qed.
Lemma lem1643485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1643486 (x : real) : (term27 x) = (term28 x).
Proof. exact (MK_COMB (@lem1643485) (@lem1643484 x)). Qed.
Lemma lem1643487 (x : real) : (term16 x) = (term29 x).
Proof. exact (MK_COMB (@lem1643486 x) (@lem1643481 x)). Qed.
Lemma lem1643488 (x : real) : (term15 x) = ((term6 x) = (term9 x)).
Proof. exact (eq_refl (term15 x)). Qed.
Lemma lem1643489 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1643490 (x : real) : (term30 x) = (term31 x).
Proof. exact (MK_COMB (@lem1643489) (@lem1643488 x)). Qed.
Lemma lem1643491 (x : real) : ((term15 x) = (term16 x)) = (((term6 x) = (term9 x)) = (term29 x)).
Proof. exact (MK_COMB (@lem1643490 x) (@lem1643487 x)). Qed.
Lemma lem1643492 (x : real) : ((term6 x) = (term9 x)) = (term29 x).
Proof. exact (EQ_MP (@lem1643491 x) (@lem1643478 x)). Qed.
Lemma lem1643493 (x : real) : (term29 x) = ((term6 x) = (term9 x)).
Proof. exact (SYM (@lem1643492 x)). Qed.
Lemma lem1643552 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1643553 (x : real) : (x = x) = True.
Proof. exact (@lem1643552 real x). Qed.
Lemma lem1643554 (x : real) : ((term9 x) = (term9 x)) = True.
Proof. exact (@lem1643553 (term9 x)). Qed.
Lemma lem1643555 (x : real) : True = ((term9 x) = (term9 x)).
Proof. exact (SYM (@lem1643554 x)). Qed.
Lemma lem1643557 : term32.
Proof. exact (proj2 (@lem516373)). Qed.
Lemma lem1643558 : term33.
Proof. exact (proj2 (@lem1643557)). Qed.
Lemma lem1643563 : term34.
Proof. exact (proj1 (@lem1643558)). Qed.
Lemma lem1643564 (n : nat) : term35 n.
Proof. exact (@lem1643563 n). Qed.
Lemma lem1643565 (n : nat) : (term35 n) = ((term36 n) = True).
Proof. exact (eq_refl (term35 n)). Qed.
Lemma lem1643568 : term37.
Proof. exact (proj1 (@lem516373)). Qed.
Lemma lem1643569 (n : nat) : term38 n.
Proof. exact (@lem1643568 n). Qed.
Lemma lem1643570 (n : nat) : (term38 n) = ((term39 n) = (Coq.Arith.PeanoNat.Nat.Even n)).
Proof. exact (eq_refl (term38 n)). Qed.
Lemma lem1643572 (x : real) : term40 x.
Proof. exact (@lem1362863 x). Qed.
Lemma lem1643573 (x : real) : (term40 x) = (term41 x).
Proof. exact (eq_refl (term40 x)). Qed.
Lemma lem1643574 (x : real) : term41 x.
Proof. exact (EQ_MP (@lem1643573 x) (@lem1643572 x)). Qed.
Lemma lem1643575 (x : real) (n : nat) : term42 x n.
Proof. exact (@lem1643574 x n). Qed.
Lemma lem1643576 (x : real) (n : nat) : (term42 x n) = ((term43 x n) = (term44 x n)).
Proof. exact (eq_refl (term42 x n)). Qed.
Lemma lem1643583 (x : real) (n : nat) : (term43 x n) = (term44 x n).
Proof. exact (EQ_MP (@lem1643576 x n) (@lem1643575 x n)). Qed.
Lemma lem1643584 (x : real) : (term19 x) = (term45 x).
Proof. exact (@lem1643583 x term4). Qed.
Lemma lem1643586 (n : nat) : (term39 n) = (Coq.Arith.PeanoNat.Nat.Even n).
Proof. exact (EQ_MP (@lem1643570 n) (@lem1643569 n)). Qed.
Lemma lem1643587 : term46 = term47.
Proof. exact (@lem1643586 term48). Qed.
Lemma lem1643589 (n : nat) : (term36 n) = True.
Proof. exact (EQ_MP (@lem1643565 n) (@lem1643564 n)). Qed.
Lemma lem1643590 : term47 = True.
Proof. exact (@lem1643589 (BIT1 0)). Qed.
Lemma lem1643591 : term46 = True.
Proof. exact (TRANS (@lem1643587) (@lem1643590)). Qed.
Lemma lem1643592 : (@COND real) = (@COND real).
Proof. exact (eq_refl (@COND real)). Qed.
Lemma lem1643593 : term49 = (@COND real True).
Proof. exact (MK_COMB (@lem1643592) (@lem1643591)). Qed.
Lemma lem1643594 (x : real) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1643595 (x : real) : (term50 x) = (term51 x).
Proof. exact (MK_COMB (@lem1643593) (@lem1643594 x)). Qed.
Lemma lem1643596 (x : real) : (term52 x) = (term52 x).
Proof. exact (eq_refl (term52 x)). Qed.
Lemma lem1643597 (x : real) : (term45 x) = (term53 x).
Proof. exact (MK_COMB (@lem1643595 x) (@lem1643596 x)). Qed.
Lemma lem1643599 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem1643600 (t2 : real) (t1 : real) : (@COND real True t1 t2) = t1.
Proof. exact (@lem1643599 real t2 t1). Qed.
Lemma lem1643601 (x : real) : (term53 x) = (term9 x).
Proof. exact (@lem1643600 (term52 x) (term9 x)). Qed.
Lemma lem1643602 (x : real) : (term45 x) = (term9 x).
Proof. exact (TRANS (@lem1643597 x) (@lem1643601 x)). Qed.
Lemma lem1643603 (x : real) : (term19 x) = (term9 x).
Proof. exact (TRANS (@lem1643584 x) (@lem1643602 x)). Qed.
Lemma lem1643604 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem1643605 (x : real) : (term54 x) = (term55 x).
Proof. exact (MK_COMB (@lem1643604) (@lem1643603 x)). Qed.
Lemma lem1643606 (x : real) : (term9 x) = (term9 x).
Proof. exact (eq_refl (term9 x)). Qed.
Lemma lem1643607 (x : real) : ((term19 x) = (term9 x)) = ((term9 x) = (term9 x)).
Proof. exact (MK_COMB (@lem1643605 x) (@lem1643606 x)). Qed.
Lemma lem1643609 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1643610 (x : real) : (x = x) = True.
Proof. exact (@lem1643609 real x). Qed.
Lemma lem1643611 (x : real) : ((term9 x) = (term9 x)) = True.
Proof. exact (@lem1643610 (term9 x)). Qed.
Lemma lem1643612 (x : real) : ((term19 x) = (term9 x)) = True.
Proof. exact (TRANS (@lem1643607 x) (@lem1643611 x)). Qed.
Lemma lem1643613 (x : real) : True = ((term19 x) = (term9 x)).
Proof. exact (SYM (@lem1643612 x)). Qed.
Lemma lem1643615 (x : real) : (term19 x) = (term9 x).
Proof. exact (EQ_MP (@lem1643613 x) (@lem0)). Qed.
Lemma lem1643616 (x : real) : term22 x.
Proof. exact (fun h0 : term56 x => @lem1643615 x). Qed.
Lemma lem1643617 (x : real) : (term9 x) = (term9 x).
Proof. exact (EQ_MP (@lem1643555 x) (@lem0)). Qed.
Lemma lem1643618 (x : real) : term26 x.
Proof. exact (fun h0 : term17 x => @lem1643617 x). Qed.
Lemma lem1643619 (x : real) : term29 x.
Proof. exact (conj (@lem1643618 x) (@lem1643616 x)). Qed.
Lemma lem1643620 (x : real) : (term6 x) = (term9 x).
Proof. exact (EQ_MP (@lem1643493 x) (@lem1643619 x)). Qed.
Lemma lem1643621 (x : real) : (term5 x) = (term9 x).
Proof. exact (EQ_MP (@lem1643475 x) (@lem1643620 x)). Qed.
Lemma lem1643626 : term57.
Proof. exact (fun x : real => @lem1643621 x). Qed.
