Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LIST_OF_SET_PROPERTIES_term_abbrevs.
Require Import CARD_CLAUSES_spec.
Require Import FINITE_INDUCT_STRONG_spec.
Require Import list_of_set_spec.
Require Import thm0_spec.
Require Import thm1097080_spec.
Require Import thm12653_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm4785464_spec.
Require Import thm4785470_spec.
Require Import thm4785471_spec.
Require Import thm82_spec.
Require Import thm9425_spec.
Lemma lem4786604 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4786605 {A : Type'} (P : type686 A) (h1 : term0 A) : term1 A P.
Proof. exact (@lem4786604 A h1 P). Qed.
Lemma lem4786606 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4786607 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (EQ_MP (@lem4786606 A P) (@lem4786605 A P h1)). Qed.
Lemma lem4786608 {A : Type'} (P : type686 A) (h1 : term3 A P) : term3 A P.
Proof. exact (h1). Qed.
Lemma lem4786609 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem4786607 A P h1 (@lem4786608 A P h2)). Qed.
Lemma lem4786610 {A : Type'} (P : type686 A) (h1 : term3 A P) : term5 A P.
Proof. exact (fun h0 : term0 A => @lem4786609 A P h0 h1). Qed.
Lemma lem4786611 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (h1). Qed.
Lemma lem4786612 {A : Type'} (P : type686 A) (h1 : term0 A) (h2 : term3 A P) : term4 A P.
Proof. exact (@lem4786610 A P h2 (@lem4786611 A h1)). Qed.
Lemma lem4786613 {A : Type'} (P : type686 A) (h1 : term0 A) : term2 A P.
Proof. exact (fun h0 : term3 A P => @lem4786612 A P h1 h0). Qed.
Lemma lem4786614 {A : Type'} (h1 : term0 A) : term0 A.
Proof. exact (fun P : type686 A => @lem4786613 A P h1). Qed.
Lemma lem4786615 {A : Type'} : term6 A.
Proof. exact (fun h0 : term0 A => @lem4786614 A h0). Qed.
Lemma lem4786616 {A : Type'} : term0 A.
Proof. exact (@lem4786615 A (@lem3558722 A)). Qed.
Lemma lem4786617 {A : Type'} (P : type686 A) : term1 A P.
Proof. exact (@lem4786616 A P). Qed.
Lemma lem4786618 {A : Type'} (P : type686 A) : (term1 A P) = (term2 A P).
Proof. exact (eq_refl (term1 A P)). Qed.
Lemma lem4786620 {_110256 : Type'} (s : _110256 -> Prop) : term7 _110256 s.
Proof. exact (@lem4786583 _110256 s). Qed.
Lemma lem4786621 {_110256 : Type'} (s : _110256 -> Prop) : (term7 _110256 s) = ((@list_of_set _110256 s) = (term8 _110256 s)).
Proof. exact (eq_refl (term7 _110256 s)). Qed.
Lemma lem4786634 {_110256 : Type'} (s : _110256 -> Prop) : (@list_of_set _110256 s) = (term8 _110256 s).
Proof. exact (EQ_MP (@lem4786621 _110256 s) (@lem4786620 _110256 s)). Qed.
Lemma lem4786635 {A : Type'} (s : A -> Prop) : (@list_of_set A s) = (term8 A s).
Proof. exact (@lem4786634 A s). Qed.
Lemma lem4786642 {A : Type'} : (@set_of_list A) = (@set_of_list A).
Proof. exact (eq_refl (@set_of_list A)). Qed.
Lemma lem4786643 {A : Type'} (s : A -> Prop) : (term9 A s) = (term10 A s).
Proof. exact (MK_COMB (@lem4786642 A) (@lem4786635 A s)). Qed.
Lemma lem4786644 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4786645 {A : Type'} (s : A -> Prop) : (term11 A s) = (term12 A s).
Proof. exact (MK_COMB (@lem4786644 A) (@lem4786643 A s)). Qed.
Lemma lem4786646 {A : Type'} (s : A -> Prop) : s = s.
Proof. exact (eq_refl s). Qed.
Lemma lem4786647 {A : Type'} (s : A -> Prop) : ((term9 A s) = s) = ((term10 A s) = s).
Proof. exact (MK_COMB (@lem4786645 A s) (@lem4786646 A s)). Qed.
Lemma lem4786650 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4786651 {A : Type'} (s : A -> Prop) : (term13 A s) = (term14 A s).
Proof. exact (MK_COMB (@lem4786650) (@lem4786647 A s)). Qed.
Lemma lem4786655 {_110256 : Type'} (s : _110256 -> Prop) : (@list_of_set _110256 s) = (term8 _110256 s).
Proof. exact (EQ_MP (@lem4786621 _110256 s) (@lem4786620 _110256 s)). Qed.
Lemma lem4786656 {A : Type'} (s : A -> Prop) : (@list_of_set A s) = (term8 A s).
Proof. exact (@lem4786655 A s). Qed.
Lemma lem4786663 {A : Type'} : (@List.length A) = (@List.length A).
Proof. exact (eq_refl (@List.length A)). Qed.
Lemma lem4786664 {A : Type'} (s : A -> Prop) : (term15 A s) = (term16 A s).
Proof. exact (MK_COMB (@lem4786663 A) (@lem4786656 A s)). Qed.
Lemma lem4786665 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4786666 {A : Type'} (s : A -> Prop) : (term17 A s) = (term18 A s).
Proof. exact (MK_COMB (@lem4786665) (@lem4786664 A s)). Qed.
Lemma lem4786667 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem4786668 {A : Type'} (s : A -> Prop) : ((term15 A s) = (@CARD A s)) = ((term16 A s) = (@CARD A s)).
Proof. exact (MK_COMB (@lem4786666 A s) (@lem4786667 A s)). Qed.
Lemma lem4786671 {A : Type'} (s : A -> Prop) : (term19 A s) = (term20 A s).
Proof. exact (MK_COMB (@lem4786651 A s) (@lem4786668 A s)). Qed.
Lemma lem4786674 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (eq_refl (term21 A s)). Qed.
Lemma lem4786675 {A : Type'} (s : A -> Prop) : (term22 A s) = (term23 A s).
Proof. exact (MK_COMB (@lem4786674 A s) (@lem4786671 A s)). Qed.
Lemma lem4786678 {A : Type'} : (term24 A) = (term25 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4786675 A s)). Qed.
Lemma lem4786679 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4786680 {A : Type'} : (term26 A) = (term27 A).
Proof. exact (MK_COMB (@lem4786679 A) (@lem4786678 A)). Qed.
Lemma lem4786685 {A : Type'} : (term27 A) = (term26 A).
Proof. exact (SYM (@lem4786680 A)). Qed.
Lemma lem4786686 {A : Type'} (P : type1143 A) : (term28 A P) = (ex P).
Proof. exact (@lem9425 (list A) P). Qed.
Lemma lem4786687 {A : Type'} (s : A -> Prop) : (term29 A s) = (term30 A s).
Proof. exact (@lem4786686 A (term31 A s)). Qed.
Lemma lem4786688 {A : Type'} (s : A -> Prop) : (term29 A s) = (term20 A s).
Proof. exact (eq_refl (term29 A s)). Qed.
Lemma lem4786689 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem4786690 {A : Type'} (s : A -> Prop) : (term32 A s) = (term33 A s).
Proof. exact (MK_COMB (@lem4786689) (@lem4786688 A s)). Qed.
Lemma lem4786691 {A : Type'} (s : A -> Prop) : (term30 A s) = (term30 A s).
Proof. exact (eq_refl (term30 A s)). Qed.
Lemma lem4786692 {A : Type'} (s : A -> Prop) : ((term29 A s) = (term30 A s)) = ((term20 A s) = (term30 A s)).
Proof. exact (MK_COMB (@lem4786690 A s) (@lem4786691 A s)). Qed.
Lemma lem4786693 {A : Type'} (s : A -> Prop) : (term20 A s) = (term30 A s).
Proof. exact (EQ_MP (@lem4786692 A s) (@lem4786687 A s)). Qed.
Lemma lem4786694 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (eq_refl (term21 A s)). Qed.
Lemma lem4786695 {A : Type'} (s : A -> Prop) : (term23 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem4786694 A s) (@lem4786693 A s)). Qed.
Lemma lem4786696 {A : Type'} : (term25 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4786695 A s)). Qed.
Lemma lem4786697 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4786698 {A : Type'} : (term27 A) = (term36 A).
Proof. exact (MK_COMB (@lem4786697 A) (@lem4786696 A)). Qed.
Lemma lem4786699 {A : Type'} : (term36 A) = (term27 A).
Proof. exact (SYM (@lem4786698 A)). Qed.
Lemma lem4786701 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (EQ_MP (@lem4786618 A P) (@lem4786617 A P)). Qed.
Lemma lem4786702 {A : Type'} (P : type686 A) : term2 A P.
Proof. exact (@lem4786701 A P). Qed.
Lemma lem4786703 {A : Type'} : term37 A.
Proof. exact (@lem4786702 A (term38 A)). Qed.
Lemma lem4786704 {A : Type'} : (term39 A) = (term40 A).
Proof. exact (eq_refl (term39 A)). Qed.
Lemma lem4786705 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4786706 {A : Type'} : (term41 A) = (term42 A).
Proof. exact (MK_COMB (@lem4786705) (@lem4786704 A)). Qed.
Lemma lem4786707 {A : Type'} (s : A -> Prop) : (term43 A s) = (term30 A s).
Proof. exact (eq_refl (term43 A s)). Qed.
Lemma lem4786708 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4786709 {A : Type'} (s : A -> Prop) : (term44 A s) = (term45 A s).
Proof. exact (MK_COMB (@lem4786708) (@lem4786707 A s)). Qed.
Lemma lem4786710 {A : Type'} (x : A) (s : A -> Prop) : (term46 A x s) = (term46 A x s).
Proof. exact (eq_refl (term46 A x s)). Qed.
Lemma lem4786711 {A : Type'} (x : A) (s : A -> Prop) : (term47 A x s) = (term48 A x s).
Proof. exact (MK_COMB (@lem4786709 A s) (@lem4786710 A x s)). Qed.
Lemma lem4786712 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4786713 {A : Type'} (x : A) (s : A -> Prop) : (term49 A x s) = (term50 A x s).
Proof. exact (MK_COMB (@lem4786712) (@lem4786711 A x s)). Qed.
Lemma lem4786714 {A : Type'} (x : A) (s : A -> Prop) : (term51 A x s) = (term52 A x s).
Proof. exact (eq_refl (term51 A x s)). Qed.
Lemma lem4786715 {A : Type'} (x : A) (s : A -> Prop) : (term53 A x s) = (term54 A x s).
Proof. exact (MK_COMB (@lem4786713 A x s) (@lem4786714 A x s)). Qed.
Lemma lem4786716 {A : Type'} (x : A) : (term55 A x) = (term56 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4786715 A x s)). Qed.
Lemma lem4786717 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4786718 {A : Type'} (x : A) : (term57 A x) = (term58 A x).
Proof. exact (MK_COMB (@lem4786717 A) (@lem4786716 A x)). Qed.
Lemma lem4786719 {A : Type'} : (term59 A) = (term60 A).
Proof. exact (fun_ext (fun x : A => @lem4786718 A x)). Qed.
Lemma lem4786720 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem4786721 {A : Type'} : (term61 A) = (term62 A).
Proof. exact (MK_COMB (@lem4786720 A) (@lem4786719 A)). Qed.
Lemma lem4786722 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (MK_COMB (@lem4786706 A) (@lem4786721 A)). Qed.
Lemma lem4786723 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem4786724 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (MK_COMB (@lem4786723) (@lem4786722 A)). Qed.
Lemma lem4786725 {A : Type'} (s : A -> Prop) : (term43 A s) = (term30 A s).
Proof. exact (eq_refl (term43 A s)). Qed.
Lemma lem4786726 {A : Type'} (s : A -> Prop) : (term21 A s) = (term21 A s).
Proof. exact (eq_refl (term21 A s)). Qed.
Lemma lem4786727 {A : Type'} (s : A -> Prop) : (term67 A s) = (term34 A s).
Proof. exact (MK_COMB (@lem4786726 A s) (@lem4786725 A s)). Qed.
Lemma lem4786728 {A : Type'} : (term68 A) = (term35 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem4786727 A s)). Qed.
Lemma lem4786729 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem4786730 {A : Type'} : (term69 A) = (term36 A).
Proof. exact (MK_COMB (@lem4786729 A) (@lem4786728 A)). Qed.
Lemma lem4786731 {A : Type'} : (term37 A) = (term70 A).
Proof. exact (MK_COMB (@lem4786724 A) (@lem4786730 A)). Qed.
Lemma lem4786732 {A : Type'} : term70 A.
Proof. exact (EQ_MP (@lem4786731 A) (@lem4786703 A)). Qed.
Lemma lem4786733 {A : Type'} (x : A) (s : A -> Prop) (h1 : term48 A x s) : term48 A x s.
Proof. exact (h1). Qed.
Lemma lem4786734 {A : Type'} (x : A) (s : A -> Prop) (h1 : term46 A x s) : term46 A x s.
Proof. exact (h1). Qed.
Lemma lem4786735 {A : Type'} (s : A -> Prop) (h1 : term30 A s) : term30 A s.
Proof. exact (h1). Qed.
Lemma lem4786736 {A : Type'} (l : list A) (s : A -> Prop) (h1 : term71 A l s) : term71 A l s.
Proof. exact (h1). Qed.
Lemma lem4786737 {A : Type'} (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : (@List.length A l) = (@CARD A s).
Proof. exact (h1). Qed.
Lemma lem4786738 {A : Type'} (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (@set_of_list A l) = s.
Proof. exact (h1). Qed.
Lemma lem4786739 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4786740 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : term72 A x s.
Proof. exact (h1). Qed.
Lemma lem4786746 {A : Type'} : (@set_of_list A (@nil A)) = (@EMPTY A).
Proof. exact (proj1 (@lem4785464 A)). Qed.
Lemma lem4786747 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4786748 {A : Type'} : (term73 A) = (@eq (A -> Prop) (@EMPTY A)).
Proof. exact (MK_COMB (@lem4786747 A) (@lem4786746 A)). Qed.
Lemma lem4786749 {A : Type'} : (@EMPTY A) = (@EMPTY A).
Proof. exact (eq_refl (@EMPTY A)). Qed.
Lemma lem4786750 {A : Type'} : ((@set_of_list A (@nil A)) = (@EMPTY A)) = ((@EMPTY A) = (@EMPTY A)).
Proof. exact (MK_COMB (@lem4786748 A) (@lem4786749 A)). Qed.
Lemma lem4786752 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4786753 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4786752 (A -> Prop) x). Qed.
Lemma lem4786754 {A : Type'} : ((@EMPTY A) = (@EMPTY A)) = True.
Proof. exact (@lem4786753 A (@EMPTY A)). Qed.
Lemma lem4786755 {A : Type'} : ((@set_of_list A (@nil A)) = (@EMPTY A)) = True.
Proof. exact (TRANS (@lem4786750 A) (@lem4786754 A)). Qed.
Lemma lem4786756 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4786757 {A : Type'} : (term74 A) = (and True).
Proof. exact (MK_COMB (@lem4786756) (@lem4786755 A)). Qed.
Lemma lem4786761 {A : Type'} : (@List.length A (@nil A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem1097080 A)). Qed.
Lemma lem4786762 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4786763 {A : Type'} : (term75 A) = term76.
Proof. exact (MK_COMB (@lem4786762) (@lem4786761 A)). Qed.
Lemma lem4786765 {A : Type'} : (@CARD A (@EMPTY A)) = (NUMERAL 0).
Proof. exact (proj1 (@lem3840691 A)). Qed.
Lemma lem4786766 {A : Type'} : ((@List.length A (@nil A)) = (@CARD A (@EMPTY A))) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem4786763 A) (@lem4786765 A)). Qed.
Lemma lem4786768 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4786769 (x : nat) : (x = x) = True.
Proof. exact (@lem4786768 nat x). Qed.
Lemma lem4786770 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem4786769 (NUMERAL 0)). Qed.
Lemma lem4786771 {A : Type'} : ((@List.length A (@nil A)) = (@CARD A (@EMPTY A))) = True.
Proof. exact (TRANS (@lem4786766 A) (@lem4786770)). Qed.
Lemma lem4786772 {A : Type'} : (term77 A) = (True /\ True).
Proof. exact (MK_COMB (@lem4786757 A) (@lem4786771 A)). Qed.
Lemma lem4786774 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4786775 : (True /\ True) = True.
Proof. exact (@lem4786774 True). Qed.
Lemma lem4786776 {A : Type'} : (term77 A) = True.
Proof. exact (TRANS (@lem4786772 A) (@lem4786775)). Qed.
Lemma lem4786777 {A : Type'} : True = (term77 A).
Proof. exact (SYM (@lem4786776 A)). Qed.
Lemma lem4786778 {A : Type'} : term77 A.
Proof. exact (EQ_MP (@lem4786777 A) (@lem0)). Qed.
Lemma lem4786779 {A : Type'} : term40 A.
Proof. exact (ex_intro (term78 A) (@nil A) (@lem4786778 A)). Qed.
Lemma lem4786780 {A : Type'} : term79 A.
Proof. exact (proj2 (@lem1097080 A)). Qed.
Lemma lem4786781 {A : Type'} (h : A) : term80 A h.
Proof. exact (@lem4786780 A h). Qed.
Lemma lem4786782 {A : Type'} (h : A) : (term80 A h) = (term81 A h).
Proof. exact (eq_refl (term80 A h)). Qed.
Lemma lem4786783 {A : Type'} (h : A) : term81 A h.
Proof. exact (EQ_MP (@lem4786782 A h) (@lem4786781 A h)). Qed.
Lemma lem4786784 {A : Type'} (h : A) (t : list A) : term82 A h t.
Proof. exact (@lem4786783 A h t). Qed.
Lemma lem4786785 {A : Type'} (h : A) (t : list A) : (term82 A h t) = ((term83 A h t) = (term84 A t)).
Proof. exact (eq_refl (term82 A h t)). Qed.
Lemma lem4786799 {A : Type'} (h : A) (t : list A) : (term83 A h t) = (term84 A t).
Proof. exact (EQ_MP (@lem4786785 A h t) (@lem4786784 A h t)). Qed.
Lemma lem4786800 {A : Type'} (h : A) (t : list A) : (term83 A h t) = (term84 A t).
Proof. exact (@lem4786799 A h t). Qed.
Lemma lem4786801 {A : Type'} (x : A) (l : list A) : (term83 A x l) = (term84 A l).
Proof. exact (@lem4786800 A x l). Qed.
Lemma lem4786803 {A : Type'} (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : (@List.length A l) = (@CARD A s).
Proof. exact (h1). Qed.
Lemma lem4786804 : S = S.
Proof. exact (eq_refl S). Qed.
Lemma lem4786805 {A : Type'} (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : (term84 A l) = (term85 A s).
Proof. exact (MK_COMB (@lem4786804) (@lem4786803 A l s h1)). Qed.
Lemma lem4786806 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : (term83 A x l) = (term85 A s).
Proof. exact (TRANS (@lem4786801 A x l) (@lem4786805 A l s h1)). Qed.
Lemma lem4786807 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem4786808 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : (term86 A x l) = (term87 A s).
Proof. exact (MK_COMB (@lem4786807) (@lem4786806 A x l s h1)). Qed.
Lemma lem4786809 {A : Type'} (x : A) (s : A -> Prop) : (term88 A x s) = (term88 A x s).
Proof. exact (eq_refl (term88 A x s)). Qed.
Lemma lem4786810 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : ((term83 A x l) = (term88 A x s)) = ((term85 A s) = (term88 A x s)).
Proof. exact (MK_COMB (@lem4786808 A x l s h1) (@lem4786809 A x s)). Qed.
Lemma lem4786813 {A : Type'} (l : list A) (x : A) (s : A -> Prop) : (term89 A l x s) = (term89 A l x s).
Proof. exact (eq_refl (term89 A l x s)). Qed.
Lemma lem4786814 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : (term90 A l x s) = (term91 A l x s).
Proof. exact (MK_COMB (@lem4786813 A l x s) (@lem4786810 A x l s h1)). Qed.
Lemma lem4786817 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@List.length A l) = (@CARD A s)) : (term91 A l x s) = (term90 A l x s).
Proof. exact (SYM (@lem4786814 A x l s h1)). Qed.
Lemma lem4786829 {A : Type'} (h : A) (t : list A) : (term92 A h t) = (term93 A h t).
Proof. exact (EQ_MP (@lem4785471 A h t) (@lem4785470 A h t)). Qed.
Lemma lem4786830 {A : Type'} (h : A) (t : list A) : (term92 A h t) = (term93 A h t).
Proof. exact (@lem4786829 A h t). Qed.
Lemma lem4786831 {A : Type'} (x : A) (l : list A) : (term92 A x l) = (term93 A x l).
Proof. exact (@lem4786830 A x l). Qed.
Lemma lem4786833 {A : Type'} (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (@set_of_list A l) = s.
Proof. exact (h1). Qed.
Lemma lem4786834 {A : Type'} (x : A) : (@INSERT A x) = (@INSERT A x).
Proof. exact (eq_refl (@INSERT A x)). Qed.
Lemma lem4786835 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (term93 A x l) = (@INSERT A x s).
Proof. exact (MK_COMB (@lem4786834 A x) (@lem4786833 A l s h1)). Qed.
Lemma lem4786836 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (term92 A x l) = (@INSERT A x s).
Proof. exact (TRANS (@lem4786831 A x l) (@lem4786835 A x l s h1)). Qed.
Lemma lem4786837 {A : Type'} : (@eq (A -> Prop)) = (@eq (A -> Prop)).
Proof. exact (eq_refl (@eq (A -> Prop))). Qed.
Lemma lem4786838 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (term94 A x l) = (term95 A x s).
Proof. exact (MK_COMB (@lem4786837 A) (@lem4786836 A x l s h1)). Qed.
Lemma lem4786839 {A : Type'} (x : A) (s : A -> Prop) : (@INSERT A x s) = (@INSERT A x s).
Proof. exact (eq_refl (@INSERT A x s)). Qed.
Lemma lem4786840 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : ((term92 A x l) = (@INSERT A x s)) = ((@INSERT A x s) = (@INSERT A x s)).
Proof. exact (MK_COMB (@lem4786838 A x l s h1) (@lem4786839 A x s)). Qed.
Lemma lem4786842 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4786843 {A : Type'} (x : A -> Prop) : (x = x) = True.
Proof. exact (@lem4786842 (A -> Prop) x). Qed.
Lemma lem4786844 {A : Type'} (x : A) (s : A -> Prop) : ((@INSERT A x s) = (@INSERT A x s)) = True.
Proof. exact (@lem4786843 A (@INSERT A x s)). Qed.
Lemma lem4786845 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : ((term92 A x l) = (@INSERT A x s)) = True.
Proof. exact (TRANS (@lem4786840 A x l s h1) (@lem4786844 A x s)). Qed.
Lemma lem4786846 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem4786847 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (term89 A l x s) = (and True).
Proof. exact (MK_COMB (@lem4786846) (@lem4786845 A x l s h1)). Qed.
Lemma lem4786850 {A : Type'} (x : A) (s : A -> Prop) : ((term85 A s) = (term88 A x s)) = ((term85 A s) = (term88 A x s)).
Proof. exact (eq_refl ((term85 A s) = (term88 A x s))). Qed.
Lemma lem4786851 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (term91 A l x s) = (term96 A x s).
Proof. exact (MK_COMB (@lem4786847 A x l s h1) (@lem4786850 A x s)). Qed.
Lemma lem4786853 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem4786854 {A : Type'} (x : A) (s : A -> Prop) : (term96 A x s) = ((term85 A s) = (term88 A x s)).
Proof. exact (@lem4786853 ((term85 A s) = (term88 A x s))). Qed.
Lemma lem4786857 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : (term91 A l x s) = ((term85 A s) = (term88 A x s)).
Proof. exact (TRANS (@lem4786851 A x l s h1) (@lem4786854 A x s)). Qed.
Lemma lem4786858 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : (@set_of_list A l) = s) : ((term85 A s) = (term88 A x s)) = (term91 A l x s).
Proof. exact (SYM (@lem4786857 A x l s h1)). Qed.
Lemma lem4786859 {A : Type'} : term97 A.
Proof. exact (proj2 (@lem3840691 A)). Qed.
Lemma lem4786860 {A : Type'} (h1 : term97 A) : term97 A.
Proof. exact (h1). Qed.
Lemma lem4786861 {A : Type'} (x : A) (h1 : term97 A) : term98 A x.
Proof. exact (@lem4786860 A h1 x). Qed.
Lemma lem4786862 {A : Type'} (x : A) : (term98 A x) = (term99 A x).
Proof. exact (eq_refl (term98 A x)). Qed.
Lemma lem4786863 {A : Type'} (x : A) (h1 : term97 A) : term99 A x.
Proof. exact (EQ_MP (@lem4786862 A x) (@lem4786861 A x h1)). Qed.
Lemma lem4786864 {A : Type'} (x : A) (s : A -> Prop) (h1 : term97 A) : term100 A x s.
Proof. exact (@lem4786863 A x h1 s). Qed.
Lemma lem4786865 {A : Type'} (x : A) (s : A -> Prop) : (term100 A x s) = (term101 A x s).
Proof. exact (eq_refl (term100 A x s)). Qed.
Lemma lem4786866 {A : Type'} (x : A) (s : A -> Prop) (h1 : term97 A) : term101 A x s.
Proof. exact (EQ_MP (@lem4786865 A x s) (@lem4786864 A x s h1)). Qed.
Lemma lem4786867 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem4786868 {A : Type'} (x : A) (s : A -> Prop) (h1 : term97 A) (h2 : @FINITE A s) : (term88 A x s) = (term102 A x s).
Proof. exact (@lem4786866 A x s h1 (@lem4786867 A s h2)). Qed.
Lemma lem4786869 {A : Type'} (s : A -> Prop) (h1 : term97 A) (h2 : @FINITE A s) : term103 A s.
Proof. exact (fun x : A => @lem4786868 A x s h1 h2). Qed.
Lemma lem4786870 {A : Type'} (s : A -> Prop) (h1 : term97 A) : term104 A s.
Proof. exact (fun h0 : @FINITE A s => @lem4786869 A s h1 h0). Qed.
Lemma lem4786871 {A : Type'} (h1 : term97 A) : term105 A.
Proof. exact (fun s : A -> Prop => @lem4786870 A s h1). Qed.
Lemma lem4786872 {A : Type'} : term106 A.
Proof. exact (fun h0 : term97 A => @lem4786871 A h0). Qed.
Lemma lem4786873 {A : Type'} : term105 A.
Proof. exact (@lem4786872 A (@lem4786859 A)). Qed.
Lemma lem4786874 {A : Type'} (s : A -> Prop) : term107 A s.
Proof. exact (@lem4786873 A s). Qed.
Lemma lem4786875 {A : Type'} (s : A -> Prop) : (term107 A s) = (term104 A s).
Proof. exact (eq_refl (term107 A s)). Qed.
Lemma lem4786878 {A : Type'} (s : A -> Prop) : term104 A s.
Proof. exact (EQ_MP (@lem4786875 A s) (@lem4786874 A s)). Qed.
Lemma lem4786879 {A : Type'} (s : A -> Prop) : term104 A s.
Proof. exact (@lem4786878 A s). Qed.
Lemma lem4786880 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : term103 A s.
Proof. exact (@lem4786879 A s (@lem4786739 A s h1)). Qed.
Lemma lem4786881 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : term108 A s x.
Proof. exact (@lem4786880 A s h1 x). Qed.
Lemma lem4786882 {A : Type'} (x : A) (s : A -> Prop) : (term108 A s x) = ((term88 A x s) = (term102 A x s)).
Proof. exact (eq_refl (term108 A s x)). Qed.
Lemma lem4786887 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term88 A x s) = (term102 A x s).
Proof. exact (EQ_MP (@lem4786882 A x s) (@lem4786881 A x s h1)). Qed.
Lemma lem4786888 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term88 A x s) = (term102 A x s).
Proof. exact (@lem4786887 A x s h1). Qed.
Lemma lem4786889 {A : Type'} (s : A -> Prop) : (term87 A s) = (term87 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem4786890 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : ((term85 A s) = (term88 A x s)) = ((term85 A s) = (term102 A x s)).
Proof. exact (MK_COMB (@lem4786889 A s) (@lem4786888 A x s h1)). Qed.
Lemma lem4786893 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : ((term85 A s) = (term102 A x s)) = ((term85 A s) = (term88 A x s)).
Proof. exact (SYM (@lem4786890 A x s h1)). Qed.
Lemma lem4786894 {A : Type'} (x : A) (s : A -> Prop) : term109 A x s.
Proof. exact (@lem82 (@IN A x s)). Qed.
Lemma lem4786901 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : (@IN A x s) = False.
Proof. exact (@lem4786894 A x s (@lem4786740 A x s h1)). Qed.
Lemma lem4786902 : (@COND nat) = (@COND nat).
Proof. exact (eq_refl (@COND nat)). Qed.
Lemma lem4786903 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : (term110 A x s) = (@COND nat False).
Proof. exact (MK_COMB (@lem4786902) (@lem4786901 A x s h1)). Qed.
Lemma lem4786904 {A : Type'} (s : A -> Prop) : (@CARD A s) = (@CARD A s).
Proof. exact (eq_refl (@CARD A s)). Qed.
Lemma lem4786905 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : (term111 A x s) = (term112 A s).
Proof. exact (MK_COMB (@lem4786903 A x s h1) (@lem4786904 A s)). Qed.
Lemma lem4786906 {A : Type'} (s : A -> Prop) : (term85 A s) = (term85 A s).
Proof. exact (eq_refl (term85 A s)). Qed.
Lemma lem4786907 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : (term102 A x s) = (term113 A s).
Proof. exact (MK_COMB (@lem4786905 A x s h1) (@lem4786906 A s)). Qed.
Lemma lem4786909 {A : Type'} (t1 : A) (t2 : A) : (@COND A False t1 t2) = t2.
Proof. exact (proj2 (@lem12653 A t1 t2)). Qed.
Lemma lem4786910 (t1 : nat) (t2 : nat) : (@COND nat False t1 t2) = t2.
Proof. exact (@lem4786909 nat t1 t2). Qed.
Lemma lem4786911 {A : Type'} (s : A -> Prop) : (term113 A s) = (term85 A s).
Proof. exact (@lem4786910 (@CARD A s) (term85 A s)). Qed.
Lemma lem4786912 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : (term102 A x s) = (term85 A s).
Proof. exact (TRANS (@lem4786907 A x s h1) (@lem4786911 A s)). Qed.
Lemma lem4786913 {A : Type'} (s : A -> Prop) : (term87 A s) = (term87 A s).
Proof. exact (eq_refl (term87 A s)). Qed.
Lemma lem4786914 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : ((term85 A s) = (term102 A x s)) = ((term85 A s) = (term85 A s)).
Proof. exact (MK_COMB (@lem4786913 A s) (@lem4786912 A x s h1)). Qed.
Lemma lem4786916 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem4786917 (x : nat) : (x = x) = True.
Proof. exact (@lem4786916 nat x). Qed.
Lemma lem4786918 {A : Type'} (s : A -> Prop) : ((term85 A s) = (term85 A s)) = True.
Proof. exact (@lem4786917 (term85 A s)). Qed.
Lemma lem4786919 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : ((term85 A s) = (term102 A x s)) = True.
Proof. exact (TRANS (@lem4786914 A x s h1) (@lem4786918 A s)). Qed.
Lemma lem4786920 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : True = ((term85 A s) = (term102 A x s)).
Proof. exact (SYM (@lem4786919 A x s h1)). Qed.
Lemma lem4786921 {A : Type'} (x : A) (s : A -> Prop) (h1 : term72 A x s) : (term85 A s) = (term102 A x s).
Proof. exact (EQ_MP (@lem4786920 A x s h1) (@lem0)). Qed.
Lemma lem4786922 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) : (term85 A s) = (term88 A x s).
Proof. exact (EQ_MP (@lem4786893 A x s h1) (@lem4786921 A x s h2)). Qed.
Lemma lem4786923 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) (h3 : (@set_of_list A l) = s) : term91 A l x s.
Proof. exact (EQ_MP (@lem4786858 A x l s h3) (@lem4786922 A x s h1 h2)). Qed.
Lemma lem4786924 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : term90 A l x s.
Proof. exact (EQ_MP (@lem4786817 A x l s h4) (@lem4786923 A x l s h1 h2 h3)). Qed.
Lemma lem4786925 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : term52 A x s.
Proof. exact (ex_intro (term114 A x s) (@cons A x l) (@lem4786924 A x l s h1 h2 h3 h4)). Qed.
Lemma lem4786926 {A : Type'} (x : A) (s : A -> Prop) (h1 : term48 A x s) : term46 A x s.
Proof. exact (proj2 (@lem4786733 A x s h1)). Qed.
Lemma lem4786927 {A : Type'} (x : A) (s : A -> Prop) (h1 : term48 A x s) : term30 A s.
Proof. exact (proj1 (@lem4786733 A x s h1)). Qed.
Lemma lem4786928 {A : Type'} (x : A) (s : A -> Prop) (h1 : term46 A x s) : @FINITE A s.
Proof. exact (proj2 (@lem4786734 A x s h1)). Qed.
Lemma lem4786929 {A : Type'} (x : A) (s : A -> Prop) (h1 : term46 A x s) : term72 A x s.
Proof. exact (proj1 (@lem4786734 A x s h1)). Qed.
Lemma lem4786930 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : (@FINITE A s) = (term52 A x s).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4786925 A x l s h1 h2 h3 h4) (fun h5 : term52 A x s => @lem4786739 A s h1)). Qed.
Lemma lem4786931 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : term52 A x s.
Proof. exact (EQ_MP (@lem4786930 A x l s h1 h2 h3 h4) (@lem4786739 A s h1)). Qed.
Lemma lem4786932 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : (term72 A x s) = (term52 A x s).
Proof. exact (prop_ext (fun h5 : term72 A x s => @lem4786931 A x l s h1 h2 h3 h4) (fun h5 : term52 A x s => @lem4786740 A x s h2)). Qed.
Lemma lem4786933 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : @FINITE A s) (h2 : term72 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : term52 A x s.
Proof. exact (EQ_MP (@lem4786932 A x l s h1 h2 h3 h4) (@lem4786740 A x s h2)). Qed.
Lemma lem4786934 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term72 A x s) (h2 : term46 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : (@FINITE A s) = (term52 A x s).
Proof. exact (prop_ext (fun h5 : @FINITE A s => @lem4786933 A x l s h5 h1 h3 h4) (fun h5 : term52 A x s => @lem4786928 A x s h2)). Qed.
Lemma lem4786935 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term72 A x s) (h2 : term46 A x s) (h3 : (@set_of_list A l) = s) (h4 : (@List.length A l) = (@CARD A s)) : term52 A x s.
Proof. exact (EQ_MP (@lem4786934 A x l s h1 h2 h3 h4) (@lem4786928 A x s h2)). Qed.
Lemma lem4786936 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : (@set_of_list A l) = s) (h3 : (@List.length A l) = (@CARD A s)) : (term72 A x s) = (term52 A x s).
Proof. exact (prop_ext (fun h4 : term72 A x s => @lem4786935 A x l s h4 h1 h2 h3) (fun h4 : term52 A x s => @lem4786929 A x s h1)). Qed.
Lemma lem4786937 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : (@set_of_list A l) = s) (h3 : (@List.length A l) = (@CARD A s)) : term52 A x s.
Proof. exact (EQ_MP (@lem4786936 A x l s h1 h2 h3) (@lem4786929 A x s h1)). Qed.
Lemma lem4786938 {A : Type'} (l : list A) (s : A -> Prop) (h1 : term71 A l s) : (@List.length A l) = (@CARD A s).
Proof. exact (proj2 (@lem4786736 A l s h1)). Qed.
Lemma lem4786939 {A : Type'} (l : list A) (s : A -> Prop) (h1 : term71 A l s) : (@set_of_list A l) = s.
Proof. exact (proj1 (@lem4786736 A l s h1)). Qed.
Lemma lem4786940 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : (@set_of_list A l) = s) (h3 : (@List.length A l) = (@CARD A s)) : ((@List.length A l) = (@CARD A s)) = (term52 A x s).
Proof. exact (prop_ext (fun h4 : (@List.length A l) = (@CARD A s) => @lem4786937 A x l s h1 h2 h3) (fun h4 : term52 A x s => @lem4786737 A l s h3)). Qed.
Lemma lem4786941 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : (@set_of_list A l) = s) (h3 : (@List.length A l) = (@CARD A s)) : term52 A x s.
Proof. exact (EQ_MP (@lem4786940 A x l s h1 h2 h3) (@lem4786737 A l s h3)). Qed.
Lemma lem4786942 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : (@set_of_list A l) = s) (h3 : (@List.length A l) = (@CARD A s)) : ((@set_of_list A l) = s) = (term52 A x s).
Proof. exact (prop_ext (fun h4 : (@set_of_list A l) = s => @lem4786941 A x l s h1 h2 h3) (fun h4 : term52 A x s => @lem4786738 A l s h2)). Qed.
Lemma lem4786943 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : (@set_of_list A l) = s) (h3 : (@List.length A l) = (@CARD A s)) : term52 A x s.
Proof. exact (EQ_MP (@lem4786942 A x l s h1 h2 h3) (@lem4786738 A l s h2)). Qed.
Lemma lem4786944 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : term71 A l s) (h3 : (@set_of_list A l) = s) : ((@List.length A l) = (@CARD A s)) = (term52 A x s).
Proof. exact (prop_ext (fun h4 : (@List.length A l) = (@CARD A s) => @lem4786943 A x l s h1 h3 h4) (fun h4 : term52 A x s => @lem4786938 A l s h2)). Qed.
Lemma lem4786945 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : term71 A l s) (h3 : (@set_of_list A l) = s) : term52 A x s.
Proof. exact (EQ_MP (@lem4786944 A x l s h1 h2 h3) (@lem4786938 A l s h2)). Qed.
Lemma lem4786946 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : term71 A l s) : ((@set_of_list A l) = s) = (term52 A x s).
Proof. exact (prop_ext (fun h3 : (@set_of_list A l) = s => @lem4786945 A x l s h1 h2 h3) (fun h3 : term52 A x s => @lem4786939 A l s h2)). Qed.
Lemma lem4786947 {A : Type'} (x : A) (l : list A) (s : A -> Prop) (h1 : term46 A x s) (h2 : term71 A l s) : term52 A x s.
Proof. exact (EQ_MP (@lem4786946 A x l s h1 h2) (@lem4786939 A l s h2)). Qed.
Lemma lem4786948 {A : Type'} (x : A) (s : A -> Prop) (h1 : term30 A s) (h2 : term46 A x s) : term52 A x s.
Proof. exact (ex_elim (@lem4786735 A s h1) (fun l : list A => fun h0 : term31 A s l => @lem4786947 A x l s h2 h0)). Qed.
Lemma lem4786949 {A : Type'} (x : A) (s : A -> Prop) (h1 : term30 A s) (h2 : term48 A x s) : (term46 A x s) = (term52 A x s).
Proof. exact (prop_ext (fun h3 : term46 A x s => @lem4786948 A x s h1 h3) (fun h3 : term52 A x s => @lem4786926 A x s h2)). Qed.
Lemma lem4786950 {A : Type'} (x : A) (s : A -> Prop) (h1 : term30 A s) (h2 : term48 A x s) : term52 A x s.
Proof. exact (EQ_MP (@lem4786949 A x s h1 h2) (@lem4786926 A x s h2)). Qed.
Lemma lem4786951 {A : Type'} (x : A) (s : A -> Prop) (h1 : term48 A x s) : (term30 A s) = (term52 A x s).
Proof. exact (prop_ext (fun h2 : term30 A s => @lem4786950 A x s h2 h1) (fun h2 : term52 A x s => @lem4786927 A x s h1)). Qed.
Lemma lem4786952 {A : Type'} (x : A) (s : A -> Prop) (h1 : term48 A x s) : term52 A x s.
Proof. exact (EQ_MP (@lem4786951 A x s h1) (@lem4786927 A x s h1)). Qed.
Lemma lem4786953 {A : Type'} (x : A) (s : A -> Prop) : term54 A x s.
Proof. exact (fun h0 : term48 A x s => @lem4786952 A x s h0). Qed.
Lemma lem4786958 {A : Type'} (x : A) : term58 A x.
Proof. exact (fun s : A -> Prop => @lem4786953 A x s). Qed.
Lemma lem4786963 {A : Type'} : term62 A.
Proof. exact (fun x : A => @lem4786958 A x). Qed.
Lemma lem4786964 {A : Type'} : term64 A.
Proof. exact (conj (@lem4786779 A) (@lem4786963 A)). Qed.
Lemma lem4786965 {A : Type'} : term36 A.
Proof. exact (@lem4786732 A (@lem4786964 A)). Qed.
Lemma lem4786966 {A : Type'} : term27 A.
Proof. exact (EQ_MP (@lem4786699 A) (@lem4786965 A)). Qed.
Lemma lem4786967 {A : Type'} : term26 A.
Proof. exact (EQ_MP (@lem4786685 A) (@lem4786966 A)). Qed.
