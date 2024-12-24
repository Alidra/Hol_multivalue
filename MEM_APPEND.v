Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MEM_APPEND_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1095962_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1834_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm735_spec.
Require Import thm736_spec.
Require Import thm793_spec.
Require Import thm794_spec.
Lemma lem1145520 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1145521 {_26945 : Type'} (P : type1143 _26945) : term0 _26945 P.
Proof. exact (@lem1145520 _26945 P). Qed.
Lemma lem1145522 {_26945 : Type'} (x : _26945) : term1 _26945 x.
Proof. exact (@lem1145521 _26945 (term2 _26945 x)). Qed.
Lemma lem1145523 {_26945 : Type'} (x : _26945) : (term3 _26945 x) = (term4 _26945 x).
Proof. exact (eq_refl (term3 _26945 x)). Qed.
Lemma lem1145524 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1145525 {_26945 : Type'} (x : _26945) : (term5 _26945 x) = (term6 _26945 x).
Proof. exact (MK_COMB (@lem1145524) (@lem1145523 _26945 x)). Qed.
Lemma lem1145526 {_26945 : Type'} (t : list _26945) (x : _26945) : (term7 _26945 x t) = (term8 _26945 t x).
Proof. exact (eq_refl (term7 _26945 x t)). Qed.
Lemma lem1145527 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1145528 {_26945 : Type'} (t : list _26945) (x : _26945) : (term9 _26945 x t) = (term10 _26945 t x).
Proof. exact (MK_COMB (@lem1145527) (@lem1145526 _26945 t x)). Qed.
Lemma lem1145529 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) : (term11 _26945 x h t) = (term12 _26945 h t x).
Proof. exact (eq_refl (term11 _26945 x h t)). Qed.
Lemma lem1145530 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) : (term13 _26945 x h t) = (term14 _26945 h t x).
Proof. exact (MK_COMB (@lem1145528 _26945 t x) (@lem1145529 _26945 h t x)). Qed.
Lemma lem1145531 {_26945 : Type'} (h : _26945) (x : _26945) : (term15 _26945 x h) = (term16 _26945 h x).
Proof. exact (fun_ext (fun t : list _26945 => @lem1145530 _26945 h t x)). Qed.
Lemma lem1145532 {_26945 : Type'} : (@all (list _26945)) = (@all (list _26945)).
Proof. exact (eq_refl (@all (list _26945))). Qed.
Lemma lem1145533 {_26945 : Type'} (h : _26945) (x : _26945) : (term17 _26945 x h) = (term18 _26945 h x).
Proof. exact (MK_COMB (@lem1145532 _26945) (@lem1145531 _26945 h x)). Qed.
Lemma lem1145534 {_26945 : Type'} (x : _26945) : (term19 _26945 x) = (term20 _26945 x).
Proof. exact (fun_ext (fun h : _26945 => @lem1145533 _26945 h x)). Qed.
Lemma lem1145535 {_26945 : Type'} : (@all _26945) = (@all _26945).
Proof. exact (eq_refl (@all _26945)). Qed.
Lemma lem1145536 {_26945 : Type'} (x : _26945) : (term21 _26945 x) = (term22 _26945 x).
Proof. exact (MK_COMB (@lem1145535 _26945) (@lem1145534 _26945 x)). Qed.
Lemma lem1145537 {_26945 : Type'} (x : _26945) : (term23 _26945 x) = (term24 _26945 x).
Proof. exact (MK_COMB (@lem1145525 _26945 x) (@lem1145536 _26945 x)). Qed.
Lemma lem1145538 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1145539 {_26945 : Type'} (x : _26945) : (term25 _26945 x) = (term26 _26945 x).
Proof. exact (MK_COMB (@lem1145538) (@lem1145537 _26945 x)). Qed.
Lemma lem1145540 {_26945 : Type'} (l1 : list _26945) (x : _26945) : (term7 _26945 x l1) = (term8 _26945 l1 x).
Proof. exact (eq_refl (term7 _26945 x l1)). Qed.
Lemma lem1145541 {_26945 : Type'} (x : _26945) : (term27 _26945 x) = (term2 _26945 x).
Proof. exact (fun_ext (fun l1 : list _26945 => @lem1145540 _26945 l1 x)). Qed.
Lemma lem1145542 {_26945 : Type'} : (@all (list _26945)) = (@all (list _26945)).
Proof. exact (eq_refl (@all (list _26945))). Qed.
Lemma lem1145543 {_26945 : Type'} (x : _26945) : (term28 _26945 x) = (term29 _26945 x).
Proof. exact (MK_COMB (@lem1145542 _26945) (@lem1145541 _26945 x)). Qed.
Lemma lem1145544 {_26945 : Type'} (x : _26945) : (term1 _26945 x) = (term30 _26945 x).
Proof. exact (MK_COMB (@lem1145539 _26945 x) (@lem1145543 _26945 x)). Qed.
Lemma lem1145545 {_26945 : Type'} (x : _26945) : term30 _26945 x.
Proof. exact (EQ_MP (@lem1145544 _26945 x) (@lem1145522 _26945 x)). Qed.
Lemma lem1145546 {_26945 : Type'} (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : term8 _26945 t x.
Proof. exact (h1). Qed.
Lemma lem1145565 {A : Type'} : term31 A.
Proof. exact (proj1 (@lem1095962 A)). Qed.
Lemma lem1145566 {A : Type'} (l : list A) : term32 A l.
Proof. exact (@lem1145565 A l). Qed.
Lemma lem1145567 {A : Type'} (l : list A) : (term32 A l) = ((@List.app A (@nil A) l) = l).
Proof. exact (eq_refl (term32 A l)). Qed.
Lemma lem1145578 {A : Type'} (l : list A) : (@List.app A (@nil A) l) = l.
Proof. exact (EQ_MP (@lem1145567 A l) (@lem1145566 A l)). Qed.
Lemma lem1145579 {_26945 : Type'} (l : list _26945) : (@List.app _26945 (@nil _26945) l) = l.
Proof. exact (@lem1145578 _26945 l). Qed.
Lemma lem1145580 {_26945 : Type'} (l2 : list _26945) : (@List.app _26945 (@nil _26945) l2) = l2.
Proof. exact (@lem1145579 _26945 l2). Qed.
Lemma lem1145581 {_26945 : Type'} (x : _26945) : (@List.In _26945 x) = (@List.In _26945 x).
Proof. exact (eq_refl (@List.In _26945 x)). Qed.
Lemma lem1145582 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term33 _26945 x l2) = (@List.In _26945 x l2).
Proof. exact (MK_COMB (@lem1145581 _26945 x) (@lem1145580 _26945 l2)). Qed.
Lemma lem1145583 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1145584 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term34 _26945 x l2) = (term35 _26945 x l2).
Proof. exact (MK_COMB (@lem1145583) (@lem1145582 _26945 x l2)). Qed.
Lemma lem1145590 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem1145591 {_26945 : Type'} (l2 : list _26945) (x : _26945) : (term36 _26945 x l2) = (term37 _26945 l2 x).
Proof. exact (@lem1145590 (@List.In _26945 x l2) (@List.In _26945 x (@nil _26945))). Qed.
Lemma lem1145600 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1145601 {_26945 : Type'} (x : _26945) : (@List.In _26945 x (@nil _26945)) = False.
Proof. exact (@lem1145600 _26945 x). Qed.
Lemma lem1145602 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term38 _26945 x l2) = (term38 _26945 x l2).
Proof. exact (eq_refl (term38 _26945 x l2)). Qed.
Lemma lem1145603 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term37 _26945 l2 x) = (term39 _26945 x l2).
Proof. exact (MK_COMB (@lem1145602 _26945 x l2) (@lem1145601 _26945 x)). Qed.
Lemma lem1145605 (t : Prop) : (t \/ False) = t.
Proof. exact (proj1 (@lem1834 t)). Qed.
Lemma lem1145606 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term39 _26945 x l2) = (@List.In _26945 x l2).
Proof. exact (@lem1145605 (@List.In _26945 x l2)). Qed.
Lemma lem1145607 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term37 _26945 l2 x) = (@List.In _26945 x l2).
Proof. exact (TRANS (@lem1145603 _26945 x l2) (@lem1145606 _26945 x l2)). Qed.
Lemma lem1145608 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term36 _26945 x l2) = (@List.In _26945 x l2).
Proof. exact (TRANS (@lem1145591 _26945 l2 x) (@lem1145607 _26945 x l2)). Qed.
Lemma lem1145609 {_26945 : Type'} (x : _26945) (l2 : list _26945) : ((term33 _26945 x l2) = (term36 _26945 x l2)) = ((@List.In _26945 x l2) = (@List.In _26945 x l2)).
Proof. exact (MK_COMB (@lem1145584 _26945 x l2) (@lem1145608 _26945 x l2)). Qed.
Lemma lem1145611 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1145612 (x : Prop) : (x = x) = True.
Proof. exact (@lem1145611 Prop x). Qed.
Lemma lem1145613 {_26945 : Type'} (x : _26945) (l2 : list _26945) : ((@List.In _26945 x l2) = (@List.In _26945 x l2)) = True.
Proof. exact (@lem1145612 (@List.In _26945 x l2)). Qed.
Lemma lem1145614 {_26945 : Type'} (x : _26945) (l2 : list _26945) : ((term33 _26945 x l2) = (term36 _26945 x l2)) = True.
Proof. exact (TRANS (@lem1145609 _26945 x l2) (@lem1145613 _26945 x l2)). Qed.
Lemma lem1145615 {_26945 : Type'} (x : _26945) : (term40 _26945 x) = (term41 _26945).
Proof. exact (fun_ext (fun l2 : list _26945 => @lem1145614 _26945 x l2)). Qed.
Lemma lem1145616 {_26945 : Type'} : (@all (list _26945)) = (@all (list _26945)).
Proof. exact (eq_refl (@all (list _26945))). Qed.
Lemma lem1145617 {_26945 : Type'} (x : _26945) : (term4 _26945 x) = (term42 _26945).
Proof. exact (MK_COMB (@lem1145616 _26945) (@lem1145615 _26945 x)). Qed.
Lemma lem1145619 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1145620 {_26945 : Type'} (t : Prop) : (term44 _26945 t) = t.
Proof. exact (@lem1145619 (list _26945) t). Qed.
Lemma lem1145621 {_26945 : Type'} : (term42 _26945) = True.
Proof. exact (@lem1145620 _26945 True). Qed.
Lemma lem1145622 {_26945 : Type'} (x : _26945) : (term4 _26945 x) = True.
Proof. exact (TRANS (@lem1145617 _26945 x) (@lem1145621 _26945)). Qed.
Lemma lem1145623 {_26945 : Type'} (x : _26945) : True = (term4 _26945 x).
Proof. exact (SYM (@lem1145622 _26945 x)). Qed.
Lemma lem1145624 {_26945 : Type'} (x : _26945) : term4 _26945 x.
Proof. exact (EQ_MP (@lem1145623 _26945 x) (@lem0)). Qed.
Lemma lem1145633 {A : Type'} : term45 A.
Proof. exact (proj2 (@lem1095962 A)). Qed.
Lemma lem1145634 {A : Type'} (h : A) : term46 A h.
Proof. exact (@lem1145633 A h). Qed.
Lemma lem1145635 {A : Type'} (h : A) : (term46 A h) = (term47 A h).
Proof. exact (eq_refl (term46 A h)). Qed.
Lemma lem1145636 {A : Type'} (h : A) : term47 A h.
Proof. exact (EQ_MP (@lem1145635 A h) (@lem1145634 A h)). Qed.
Lemma lem1145637 {A : Type'} (h : A) (t : list A) : term48 A h t.
Proof. exact (@lem1145636 A h t). Qed.
Lemma lem1145638 {A : Type'} (h : A) (t : list A) : (term48 A h t) = (term49 A h t).
Proof. exact (eq_refl (term48 A h t)). Qed.
Lemma lem1145639 {A : Type'} (h : A) (t : list A) : term49 A h t.
Proof. exact (EQ_MP (@lem1145638 A h t) (@lem1145637 A h t)). Qed.
Lemma lem1145640 {A : Type'} (h : A) (t : list A) (l : list A) : term50 A h t l.
Proof. exact (@lem1145639 A h t l). Qed.
Lemma lem1145641 {A : Type'} (h : A) (t : list A) (l : list A) : (term50 A h t l) = ((term51 A h t l) = (term52 A h t l)).
Proof. exact (eq_refl (term50 A h t l)). Qed.
Lemma lem1145649 {_26945 : Type'} (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : term53 _26945 t x l2.
Proof. exact (@lem1145546 _26945 t x h1 l2). Qed.
Lemma lem1145650 {_26945 : Type'} (t : list _26945) (x : _26945) (l2 : list _26945) : (term53 _26945 t x l2) = ((term54 _26945 x t l2) = (term55 _26945 t x l2)).
Proof. exact (eq_refl (term53 _26945 t x l2)). Qed.
Lemma lem1145659 {A : Type'} (h : A) (t : list A) (l : list A) : (term51 A h t l) = (term52 A h t l).
Proof. exact (EQ_MP (@lem1145641 A h t l) (@lem1145640 A h t l)). Qed.
Lemma lem1145660 {_26945 : Type'} (h : _26945) (t : list _26945) (l : list _26945) : (term51 _26945 h t l) = (term52 _26945 h t l).
Proof. exact (@lem1145659 _26945 h t l). Qed.
Lemma lem1145661 {_26945 : Type'} (h : _26945) (t : list _26945) (l2 : list _26945) : (term51 _26945 h t l2) = (term52 _26945 h t l2).
Proof. exact (@lem1145660 _26945 h t l2). Qed.
Lemma lem1145662 {_26945 : Type'} (x : _26945) : (@List.In _26945 x) = (@List.In _26945 x).
Proof. exact (eq_refl (@List.In _26945 x)). Qed.
Lemma lem1145663 {_26945 : Type'} (x : _26945) (h : _26945) (t : list _26945) (l2 : list _26945) : (term56 _26945 x h t l2) = (term57 _26945 x h t l2).
Proof. exact (MK_COMB (@lem1145662 _26945 x) (@lem1145661 _26945 h t l2)). Qed.
Lemma lem1145665 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term58 _25376 x h t) = (term59 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1145666 {_26945 : Type'} (h : _26945) (x : _26945) (t : list _26945) : (term58 _26945 x h t) = (term59 _26945 h x t).
Proof. exact (@lem1145665 _26945 h x t). Qed.
Lemma lem1145667 {_26945 : Type'} (h : _26945) (x : _26945) (t : list _26945) (l2 : list _26945) : (term57 _26945 x h t l2) = (term60 _26945 h x t l2).
Proof. exact (@lem1145666 _26945 h x (@List.app _26945 t l2)). Qed.
Lemma lem1145678 {_26945 : Type'} (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term54 _26945 x t l2) = (term55 _26945 t x l2).
Proof. exact (EQ_MP (@lem1145650 _26945 t x l2) (@lem1145649 _26945 l2 t x h1)). Qed.
Lemma lem1145679 {_26945 : Type'} (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term54 _26945 x t l2) = (term55 _26945 t x l2).
Proof. exact (@lem1145678 _26945 l2 t x h1). Qed.
Lemma lem1145685 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem1145686 {_26945 : Type'} (l2 : list _26945) (x : _26945) (t : list _26945) : (term55 _26945 t x l2) = (term55 _26945 l2 x t).
Proof. exact (@lem1145685 (@List.In _26945 x l2) (@List.In _26945 x t)). Qed.
Lemma lem1145694 {_26945 : Type'} (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term54 _26945 x t l2) = (term55 _26945 l2 x t).
Proof. exact (TRANS (@lem1145679 _26945 l2 t x h1) (@lem1145686 _26945 l2 x t)). Qed.
Lemma lem1145695 {_26945 : Type'} (x : _26945) (h : _26945) : (term61 _26945 x h) = (term61 _26945 x h).
Proof. exact (eq_refl (term61 _26945 x h)). Qed.
Lemma lem1145696 {_26945 : Type'} (h : _26945) (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term60 _26945 h x t l2) = (term62 _26945 h l2 x t).
Proof. exact (MK_COMB (@lem1145695 _26945 x h) (@lem1145694 _26945 l2 t x h1)). Qed.
Lemma lem1145709 {_26945 : Type'} (h : _26945) (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term57 _26945 x h t l2) = (term62 _26945 h l2 x t).
Proof. exact (TRANS (@lem1145667 _26945 h x t l2) (@lem1145696 _26945 h l2 t x h1)). Qed.
Lemma lem1145710 {_26945 : Type'} (h : _26945) (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term56 _26945 x h t l2) = (term62 _26945 h l2 x t).
Proof. exact (TRANS (@lem1145663 _26945 x h t l2) (@lem1145709 _26945 h l2 t x h1)). Qed.
Lemma lem1145711 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1145712 {_26945 : Type'} (h : _26945) (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term63 _26945 x h t l2) = (term64 _26945 h l2 x t).
Proof. exact (MK_COMB (@lem1145711) (@lem1145710 _26945 h l2 t x h1)). Qed.
Lemma lem1145718 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (EQ_MP (@lem736 q p) (@lem735 p q)). Qed.
Lemma lem1145719 {_26945 : Type'} (l2 : list _26945) (x : _26945) (h : _26945) (t : list _26945) : (term65 _26945 h t x l2) = (term66 _26945 l2 x h t).
Proof. exact (@lem1145718 (@List.In _26945 x l2) (term58 _26945 x h t)). Qed.
Lemma lem1145728 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term58 _25376 x h t) = (term59 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1145729 {_26945 : Type'} (h : _26945) (x : _26945) (t : list _26945) : (term58 _26945 x h t) = (term59 _26945 h x t).
Proof. exact (@lem1145728 _26945 h x t). Qed.
Lemma lem1145739 {_26945 : Type'} (x : _26945) (l2 : list _26945) : (term38 _26945 x l2) = (term38 _26945 x l2).
Proof. exact (eq_refl (term38 _26945 x l2)). Qed.
Lemma lem1145740 {_26945 : Type'} (l2 : list _26945) (h : _26945) (x : _26945) (t : list _26945) : (term66 _26945 l2 x h t) = (term67 _26945 l2 h x t).
Proof. exact (MK_COMB (@lem1145739 _26945 x l2) (@lem1145729 _26945 h x t)). Qed.
Lemma lem1145744 (q : Prop) (p : Prop) (r : Prop) : (term68 p q r) = (term68 q p r).
Proof. exact (EQ_MP (@lem794 q p r) (@lem793 p q r)). Qed.
Lemma lem1145745 {_26945 : Type'} (h : _26945) (l2 : list _26945) (x : _26945) (t : list _26945) : (term67 _26945 l2 h x t) = (term62 _26945 h l2 x t).
Proof. exact (@lem1145744 (x = h) (@List.In _26945 x l2) (@List.In _26945 x t)). Qed.
Lemma lem1145767 {_26945 : Type'} (h : _26945) (l2 : list _26945) (x : _26945) (t : list _26945) : (term66 _26945 l2 x h t) = (term62 _26945 h l2 x t).
Proof. exact (TRANS (@lem1145740 _26945 l2 h x t) (@lem1145745 _26945 h l2 x t)). Qed.
Lemma lem1145768 {_26945 : Type'} (h : _26945) (l2 : list _26945) (x : _26945) (t : list _26945) : (term65 _26945 h t x l2) = (term62 _26945 h l2 x t).
Proof. exact (TRANS (@lem1145719 _26945 l2 x h t) (@lem1145767 _26945 h l2 x t)). Qed.
Lemma lem1145769 {_26945 : Type'} (h : _26945) (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : ((term56 _26945 x h t l2) = (term65 _26945 h t x l2)) = ((term62 _26945 h l2 x t) = (term62 _26945 h l2 x t)).
Proof. exact (MK_COMB (@lem1145712 _26945 h l2 t x h1) (@lem1145768 _26945 h l2 x t)). Qed.
Lemma lem1145771 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1145772 (x : Prop) : (x = x) = True.
Proof. exact (@lem1145771 Prop x). Qed.
Lemma lem1145773 {_26945 : Type'} (h : _26945) (l2 : list _26945) (x : _26945) (t : list _26945) : ((term62 _26945 h l2 x t) = (term62 _26945 h l2 x t)) = True.
Proof. exact (@lem1145772 (term62 _26945 h l2 x t)). Qed.
Lemma lem1145774 {_26945 : Type'} (h : _26945) (l2 : list _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : ((term56 _26945 x h t l2) = (term65 _26945 h t x l2)) = True.
Proof. exact (TRANS (@lem1145769 _26945 h l2 t x h1) (@lem1145773 _26945 h l2 x t)). Qed.
Lemma lem1145775 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term69 _26945 h t x) = (term41 _26945).
Proof. exact (fun_ext (fun l2 : list _26945 => @lem1145774 _26945 h l2 t x h1)). Qed.
Lemma lem1145776 {_26945 : Type'} : (@all (list _26945)) = (@all (list _26945)).
Proof. exact (eq_refl (@all (list _26945))). Qed.
Lemma lem1145777 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term12 _26945 h t x) = (term42 _26945).
Proof. exact (MK_COMB (@lem1145776 _26945) (@lem1145775 _26945 h t x h1)). Qed.
Lemma lem1145779 {A : Type'} (t : Prop) : (term43 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1145780 {_26945 : Type'} (t : Prop) : (term44 _26945 t) = t.
Proof. exact (@lem1145779 (list _26945) t). Qed.
Lemma lem1145781 {_26945 : Type'} : (term42 _26945) = True.
Proof. exact (@lem1145780 _26945 True). Qed.
Lemma lem1145782 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : (term12 _26945 h t x) = True.
Proof. exact (TRANS (@lem1145777 _26945 h t x h1) (@lem1145781 _26945)). Qed.
Lemma lem1145783 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : True = (term12 _26945 h t x).
Proof. exact (SYM (@lem1145782 _26945 h t x h1)). Qed.
Lemma lem1145784 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) (h1 : term8 _26945 t x) : term12 _26945 h t x.
Proof. exact (EQ_MP (@lem1145783 _26945 h t x h1) (@lem0)). Qed.
Lemma lem1145785 {_26945 : Type'} (h : _26945) (t : list _26945) (x : _26945) : term14 _26945 h t x.
Proof. exact (fun h0 : term8 _26945 t x => @lem1145784 _26945 h t x h0). Qed.
Lemma lem1145790 {_26945 : Type'} (h : _26945) (x : _26945) : term18 _26945 h x.
Proof. exact (fun t : list _26945 => @lem1145785 _26945 h t x). Qed.
Lemma lem1145795 {_26945 : Type'} (x : _26945) : term22 _26945 x.
Proof. exact (fun h : _26945 => @lem1145790 _26945 h x). Qed.
Lemma lem1145796 {_26945 : Type'} (x : _26945) : term24 _26945 x.
Proof. exact (conj (@lem1145624 _26945 x) (@lem1145795 _26945 x)). Qed.
Lemma lem1145797 {_26945 : Type'} (x : _26945) : term29 _26945 x.
Proof. exact (@lem1145545 _26945 x (@lem1145796 _26945 x)). Qed.
Lemma lem1145802 {_26945 : Type'} : term70 _26945.
Proof. exact (fun x : _26945 => @lem1145797 _26945 x). Qed.
