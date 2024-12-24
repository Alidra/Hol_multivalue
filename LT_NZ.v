Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_NZ_term_abbrevs.
Require Import BOOL_CASES_AX_spec.
Require Import EQ_SYM_EQ_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1833_spec.
Require Import thm1856_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89994_spec.
Lemma lem98473 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem98474 : term1.
Proof. exact (@lem98473 term2). Qed.
Lemma lem98475 : term3 = (term4 = term5).
Proof. exact (eq_refl term3). Qed.
Lemma lem98476 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem98477 : term6 = term7.
Proof. exact (MK_COMB (@lem98476) (@lem98475)). Qed.
Lemma lem98478 (n : nat) : (term8 n) = ((term9 n) = (term10 n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem98479 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98480 (n : nat) : (term11 n) = (term12 n).
Proof. exact (MK_COMB (@lem98479) (@lem98478 n)). Qed.
Lemma lem98481 (n : nat) : (term13 n) = ((term14 n) = (term15 n)).
Proof. exact (eq_refl (term13 n)). Qed.
Lemma lem98482 (n : nat) : (term16 n) = (term17 n).
Proof. exact (MK_COMB (@lem98480 n) (@lem98481 n)). Qed.
Lemma lem98483 : term18 = term19.
Proof. exact (fun_ext (fun n : nat => @lem98482 n)). Qed.
Lemma lem98484 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98485 : term20 = term21.
Proof. exact (MK_COMB (@lem98484) (@lem98483)). Qed.
Lemma lem98486 : term22 = term23.
Proof. exact (MK_COMB (@lem98477) (@lem98485)). Qed.
Lemma lem98487 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem98488 : term24 = term25.
Proof. exact (MK_COMB (@lem98487) (@lem98486)). Qed.
Lemma lem98489 (n : nat) : (term8 n) = ((term9 n) = (term10 n)).
Proof. exact (eq_refl (term8 n)). Qed.
Lemma lem98490 : term26 = term2.
Proof. exact (fun_ext (fun n : nat => @lem98489 n)). Qed.
Lemma lem98491 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem98492 : term27 = term28.
Proof. exact (MK_COMB (@lem98491) (@lem98490)). Qed.
Lemma lem98493 : term1 = term29.
Proof. exact (MK_COMB (@lem98488) (@lem98492)). Qed.
Lemma lem98494 : term29.
Proof. exact (EQ_MP (@lem98493) (@lem98474)). Qed.
Lemma lem98509 : term30.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem98510 (m : nat) : term31 m.
Proof. exact (@lem98509 m). Qed.
Lemma lem98511 (m : nat) : (term31 m) = ((term32 m) = False).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem98536 (m : nat) : (term32 m) = False.
Proof. exact (EQ_MP (@lem98511 m) (@lem98510 m)). Qed.
Lemma lem98537 : term4 = False.
Proof. exact (@lem98536 (NUMERAL 0)). Qed.
Lemma lem98538 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98539 : term33 = (@eq Prop False).
Proof. exact (MK_COMB (@lem98538) (@lem98537)). Qed.
Lemma lem98541 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem98542 (x : nat) : (x = x) = True.
Proof. exact (@lem98541 nat x). Qed.
Lemma lem98543 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem98542 (NUMERAL 0)). Qed.
Lemma lem98544 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98545 : term5 = (~ True).
Proof. exact (MK_COMB (@lem98544) (@lem98543)). Qed.
Lemma lem98547 : (~ True) = False.
Proof. exact (proj1 (@lem1504)). Qed.
Lemma lem98548 : term5 = False.
Proof. exact (TRANS (@lem98545) (@lem98547)). Qed.
Lemma lem98549 : (term4 = term5) = (False = False).
Proof. exact (MK_COMB (@lem98539) (@lem98548)). Qed.
Lemma lem98551 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem98552 : (False = False) = (~ False).
Proof. exact (@lem98551 False). Qed.
Lemma lem98554 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem98555 : (False = False) = True.
Proof. exact (TRANS (@lem98552) (@lem98554)). Qed.
Lemma lem98556 : (term4 = term5) = True.
Proof. exact (TRANS (@lem98549) (@lem98555)). Qed.
Lemma lem98557 : True = (term4 = term5).
Proof. exact (SYM (@lem98556)). Qed.
Lemma lem98558 : term4 = term5.
Proof. exact (EQ_MP (@lem98557) (@lem0)). Qed.
Lemma lem98559 {A : Type'} (x : A) : term34 A x.
Proof. exact (@lem362 A x). Qed.
Lemma lem98560 {A : Type'} (x : A) : (term34 A x) = (term35 A x).
Proof. exact (eq_refl (term34 A x)). Qed.
Lemma lem98561 {A : Type'} (x : A) : term35 A x.
Proof. exact (EQ_MP (@lem98560 A x) (@lem98559 A x)). Qed.
Lemma lem98562 {A : Type'} (x : A) (y : A) : term36 A x y.
Proof. exact (@lem98561 A x y). Qed.
Lemma lem98563 {A : Type'} (y : A) (x : A) : (term36 A x y) = ((x = y) = (y = x)).
Proof. exact (eq_refl (term36 A x y)). Qed.
Lemma lem98565 : term37.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem98566 (m : nat) : term38 m.
Proof. exact (@lem98565 m). Qed.
Lemma lem98567 (m : nat) : (term38 m) = (term39 m).
Proof. exact (eq_refl (term38 m)). Qed.
Lemma lem98568 (m : nat) : term39 m.
Proof. exact (EQ_MP (@lem98567 m) (@lem98566 m)). Qed.
Lemma lem98569 (m : nat) (n : nat) : term40 m n.
Proof. exact (@lem98568 m n). Qed.
Lemma lem98570 (m : nat) (n : nat) : (term40 m n) = ((term41 m n) = (term42 m n)).
Proof. exact (eq_refl (term40 m n)). Qed.
Lemma lem98576 (n : nat) : term43 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem98577 (n : nat) : (term43 n) = (term15 n).
Proof. exact (eq_refl (term43 n)). Qed.
Lemma lem98578 (n : nat) : term15 n.
Proof. exact (EQ_MP (@lem98577 n) (@lem98576 n)). Qed.
Lemma lem98579 (n : nat) : term44 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem98599 (m : nat) (n : nat) : (term41 m n) = (term42 m n).
Proof. exact (EQ_MP (@lem98570 m n) (@lem98569 m n)). Qed.
Lemma lem98600 (n : nat) : (term14 n) = (term45 n).
Proof. exact (@lem98599 (NUMERAL 0) n). Qed.
Lemma lem98606 {A : Type'} (y : A) (x : A) : (x = y) = (y = x).
Proof. exact (EQ_MP (@lem98563 A y x) (@lem98562 A x y)). Qed.
Lemma lem98607 (y : nat) (x : nat) : (x = y) = (y = x).
Proof. exact (@lem98606 nat y x). Qed.
Lemma lem98608 (n : nat) : ((NUMERAL 0) = n) = (n = (NUMERAL 0)).
Proof. exact (@lem98607 n (NUMERAL 0)). Qed.
Lemma lem98615 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem98616 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem98615) (@lem98608 n)). Qed.
Lemma lem98618 (n : nat) (h1 : (term9 n) = (term10 n)) : (term9 n) = (term10 n).
Proof. exact (h1). Qed.
Lemma lem98625 (n : nat) (h1 : (term9 n) = (term10 n)) : (term45 n) = (term48 n).
Proof. exact (MK_COMB (@lem98616 n) (@lem98618 n h1)). Qed.
Lemma lem98628 (n : nat) (h1 : (term9 n) = (term10 n)) : (term14 n) = (term48 n).
Proof. exact (TRANS (@lem98600 n) (@lem98625 n h1)). Qed.
Lemma lem98629 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98630 (n : nat) (h1 : (term9 n) = (term10 n)) : (term49 n) = (term50 n).
Proof. exact (MK_COMB (@lem98629) (@lem98628 n h1)). Qed.
Lemma lem98632 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem98579 n (@lem98578 n)). Qed.
Lemma lem98633 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem98634 (n : nat) : (term15 n) = (~ False).
Proof. exact (MK_COMB (@lem98633) (@lem98632 n)). Qed.
Lemma lem98636 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem98637 (n : nat) : (term15 n) = True.
Proof. exact (TRANS (@lem98634 n) (@lem98636)). Qed.
Lemma lem98638 (n : nat) (h1 : (term9 n) = (term10 n)) : ((term14 n) = (term15 n)) = ((term48 n) = True).
Proof. exact (MK_COMB (@lem98630 n h1) (@lem98637 n)). Qed.
Lemma lem98640 (t : Prop) : (t = True) = t.
Proof. exact (proj1 (@lem1856 t)). Qed.
Lemma lem98641 (n : nat) : ((term48 n) = True) = (term48 n).
Proof. exact (@lem98640 (term48 n)). Qed.
Lemma lem98656 (n : nat) (h1 : (term9 n) = (term10 n)) : ((term14 n) = (term15 n)) = (term48 n).
Proof. exact (TRANS (@lem98638 n h1) (@lem98641 n)). Qed.
Lemma lem98657 (n : nat) (h1 : (term9 n) = (term10 n)) : (term48 n) = ((term14 n) = (term15 n)).
Proof. exact (SYM (@lem98656 n h1)). Qed.
Lemma lem98666 (n : nat) : term51 n.
Proof. exact (@lem9851 (n = (NUMERAL 0))). Qed.
Lemma lem98667 (n : nat) : (term51 n) = (term52 n).
Proof. exact (eq_refl (term51 n)). Qed.
Lemma lem98668 (n : nat) : term52 n.
Proof. exact (EQ_MP (@lem98667 n) (@lem98666 n)). Qed.
Lemma lem98669 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (n = (NUMERAL 0)) = True.
Proof. exact (h1). Qed.
Lemma lem98670 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (n = (NUMERAL 0)) = False.
Proof. exact (h1). Qed.
Lemma lem98679 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem98680 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term54 n) = term55.
Proof. exact (MK_COMB (@lem98679) (@lem98669 n h1)). Qed.
Lemma lem98681 : term55 = term56.
Proof. exact (eq_refl term55). Qed.
Lemma lem98682 (n : nat) : (term57 n) = (term57 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem98683 (n : nat) : ((term54 n) = term55) = ((term54 n) = term56).
Proof. exact (MK_COMB (@lem98682 n) (@lem98681)). Qed.
Lemma lem98684 (n : nat) : (term54 n) = (term48 n).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem98685 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98686 (n : nat) : (term57 n) = (term50 n).
Proof. exact (MK_COMB (@lem98685) (@lem98684 n)). Qed.
Lemma lem98687 : term56 = term56.
Proof. exact (eq_refl term56). Qed.
Lemma lem98688 (n : nat) : ((term54 n) = term56) = ((term48 n) = term56).
Proof. exact (MK_COMB (@lem98686 n) (@lem98687)). Qed.
Lemma lem98689 (n : nat) : ((term54 n) = term55) = ((term48 n) = term56).
Proof. exact (TRANS (@lem98683 n) (@lem98688 n)). Qed.
Lemma lem98690 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : (term48 n) = term56.
Proof. exact (EQ_MP (@lem98689 n) (@lem98680 n h1)). Qed.
Lemma lem98691 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : term56 = (term48 n).
Proof. exact (SYM (@lem98690 n h1)). Qed.
Lemma lem98692 : term53 = term53.
Proof. exact (eq_refl term53). Qed.
Lemma lem98693 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term54 n) = term58.
Proof. exact (MK_COMB (@lem98692) (@lem98670 n h1)). Qed.
Lemma lem98694 : term58 = term59.
Proof. exact (eq_refl term58). Qed.
Lemma lem98695 (n : nat) : (term57 n) = (term57 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem98696 (n : nat) : ((term54 n) = term58) = ((term54 n) = term59).
Proof. exact (MK_COMB (@lem98695 n) (@lem98694)). Qed.
Lemma lem98697 (n : nat) : (term54 n) = (term48 n).
Proof. exact (eq_refl (term54 n)). Qed.
Lemma lem98698 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem98699 (n : nat) : (term57 n) = (term50 n).
Proof. exact (MK_COMB (@lem98698) (@lem98697 n)). Qed.
Lemma lem98700 : term59 = term59.
Proof. exact (eq_refl term59). Qed.
Lemma lem98701 (n : nat) : ((term54 n) = term59) = ((term48 n) = term59).
Proof. exact (MK_COMB (@lem98699 n) (@lem98700)). Qed.
Lemma lem98702 (n : nat) : ((term54 n) = term58) = ((term48 n) = term59).
Proof. exact (TRANS (@lem98696 n) (@lem98701 n)). Qed.
Lemma lem98703 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : (term48 n) = term59.
Proof. exact (EQ_MP (@lem98702 n) (@lem98693 n h1)). Qed.
Lemma lem98704 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : term59 = (term48 n).
Proof. exact (SYM (@lem98703 n h1)). Qed.
Lemma lem98706 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem98707 : term56 = True.
Proof. exact (@lem98706 (~ True)). Qed.
Lemma lem98708 : True = term56.
Proof. exact (SYM (@lem98707)). Qed.
Lemma lem98709 : term56.
Proof. exact (EQ_MP (@lem98708) (@lem0)). Qed.
Lemma lem98711 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem98712 : term59 = (~ False).
Proof. exact (@lem98711 (~ False)). Qed.
Lemma lem98714 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem98715 : term59 = True.
Proof. exact (TRANS (@lem98712) (@lem98714)). Qed.
Lemma lem98716 : True = term59.
Proof. exact (SYM (@lem98715)). Qed.
Lemma lem98717 : term59.
Proof. exact (EQ_MP (@lem98716) (@lem0)). Qed.
Lemma lem98718 (n : nat) (h1 : (n = (NUMERAL 0)) = False) : term48 n.
Proof. exact (EQ_MP (@lem98704 n h1) (@lem98717)). Qed.
Lemma lem98719 (n : nat) (h1 : (n = (NUMERAL 0)) = True) : term48 n.
Proof. exact (EQ_MP (@lem98691 n h1) (@lem98709)). Qed.
Lemma lem98722 (n : nat) : term48 n.
Proof. exact (or_elim (@lem98668 n) (fun h0 : (n = (NUMERAL 0)) = True => @lem98719 n h0) (fun h0 : (n = (NUMERAL 0)) = False => @lem98718 n h0)). Qed.
Lemma lem98723 (n : nat) (h1 : (term9 n) = (term10 n)) : (term14 n) = (term15 n).
Proof. exact (EQ_MP (@lem98657 n h1) (@lem98722 n)). Qed.
Lemma lem98724 (n : nat) : term17 n.
Proof. exact (fun h0 : (term9 n) = (term10 n) => @lem98723 n h0). Qed.
Lemma lem98729 : term21.
Proof. exact (fun n : nat => @lem98724 n). Qed.
Lemma lem98730 : term23.
Proof. exact (conj (@lem98558) (@lem98729)). Qed.
Lemma lem98731 : term28.
Proof. exact (@lem98494 (@lem98730)). Qed.
