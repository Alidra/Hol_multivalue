Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL_FILTER_term_abbrevs.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1106562_spec.
Require Import thm1106563_spec.
Require Import thm1106571_spec.
Require Import thm1106572_spec.
Require Import thm13473_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1820_spec.
Require Import thm1822_spec.
Require Import thm1842_spec.
Require Import thm1855_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem1207677 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1207678 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (@lem1207677 A P). Qed.
Lemma lem1207679 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : term1 A Q P.
Proof. exact (@lem1207678 A (term2 A Q P)). Qed.
Lemma lem1207680 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term3 A Q P) = ((term4 A P Q) = (term5 A Q P)).
Proof. exact (eq_refl (term3 A Q P)). Qed.
Lemma lem1207681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207682 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term6 A Q P) = (term7 A Q P).
Proof. exact (MK_COMB (@lem1207681) (@lem1207680 A Q P)). Qed.
Lemma lem1207683 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term8 A Q P t) = ((term9 A P Q t) = (term10 A Q P t)).
Proof. exact (eq_refl (term8 A Q P t)). Qed.
Lemma lem1207684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207685 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term11 A Q P t) = (term12 A Q P t).
Proof. exact (MK_COMB (@lem1207684) (@lem1207683 A Q P t)). Qed.
Lemma lem1207686 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) (t : list A) : (term13 A Q P h t) = ((term14 A P Q h t) = (term15 A Q P h t)).
Proof. exact (eq_refl (term13 A Q P h t)). Qed.
Lemma lem1207687 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) (t : list A) : (term16 A Q P h t) = (term17 A Q P h t).
Proof. exact (MK_COMB (@lem1207685 A Q P t) (@lem1207686 A Q P h t)). Qed.
Lemma lem1207688 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term18 A Q P h) = (term19 A Q P h).
Proof. exact (fun_ext (fun t : list A => @lem1207687 A Q P h t)). Qed.
Lemma lem1207689 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1207690 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term20 A Q P h) = (term21 A Q P h).
Proof. exact (MK_COMB (@lem1207689 A) (@lem1207688 A Q P h)). Qed.
Lemma lem1207691 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term22 A Q P) = (term23 A Q P).
Proof. exact (fun_ext (fun h : A => @lem1207690 A Q P h)). Qed.
Lemma lem1207692 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1207693 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term24 A Q P) = (term25 A Q P).
Proof. exact (MK_COMB (@lem1207692 A) (@lem1207691 A Q P)). Qed.
Lemma lem1207694 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term26 A Q P) = (term27 A Q P).
Proof. exact (MK_COMB (@lem1207682 A Q P) (@lem1207693 A Q P)). Qed.
Lemma lem1207695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1207696 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term28 A Q P) = (term29 A Q P).
Proof. exact (MK_COMB (@lem1207695) (@lem1207694 A Q P)). Qed.
Lemma lem1207697 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (l : list A) : (term8 A Q P l) = ((term9 A P Q l) = (term10 A Q P l)).
Proof. exact (eq_refl (term8 A Q P l)). Qed.
Lemma lem1207698 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term30 A Q P) = (term2 A Q P).
Proof. exact (fun_ext (fun l : list A => @lem1207697 A Q P l)). Qed.
Lemma lem1207699 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1207700 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term31 A Q P) = (term32 A Q P).
Proof. exact (MK_COMB (@lem1207699 A) (@lem1207698 A Q P)). Qed.
Lemma lem1207701 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term1 A Q P) = (term33 A Q P).
Proof. exact (MK_COMB (@lem1207696 A Q P) (@lem1207700 A Q P)). Qed.
Lemma lem1207702 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : term33 A Q P.
Proof. exact (EQ_MP (@lem1207701 A Q P) (@lem1207679 A Q P)). Qed.
Lemma lem1207707 {_25594 : Type'} (P : _25594 -> Prop) : (@FILTER _25594 P (@nil _25594)) = (@nil _25594).
Proof. exact (EQ_MP (@lem1106563 _25594 P) (@lem1106562 _25594 P)). Qed.
Lemma lem1207708 {A : Type'} (P : A -> Prop) : (@FILTER A P (@nil A)) = (@nil A).
Proof. exact (@lem1207707 A P). Qed.
Lemma lem1207709 {A : Type'} (Q : A -> Prop) : (@FILTER A Q (@nil A)) = (@nil A).
Proof. exact (@lem1207708 A Q). Qed.
Lemma lem1207710 {A : Type'} (P : A -> Prop) : (@List.Forall A P) = (@List.Forall A P).
Proof. exact (eq_refl (@List.Forall A P)). Qed.
Lemma lem1207711 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term4 A P Q) = (@List.Forall A P (@nil A)).
Proof. exact (MK_COMB (@lem1207710 A P) (@lem1207709 A Q)). Qed.
Lemma lem1207713 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1207714 {A : Type'} (P : A -> Prop) : (@List.Forall A P (@nil A)) = True.
Proof. exact (@lem1207713 A P). Qed.
Lemma lem1207715 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term4 A P Q) = True.
Proof. exact (TRANS (@lem1207711 A Q P) (@lem1207714 A P)). Qed.
Lemma lem1207716 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207717 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term34 A P Q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1207716) (@lem1207715 A P Q)). Qed.
Lemma lem1207719 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1207720 {A : Type'} (P : A -> Prop) : (@List.Forall A P (@nil A)) = True.
Proof. exact (@lem1207719 A P). Qed.
Lemma lem1207721 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term5 A Q P) = True.
Proof. exact (@lem1207720 A (term35 A Q P)). Qed.
Lemma lem1207722 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : ((term4 A P Q) = (term5 A Q P)) = (True = True).
Proof. exact (MK_COMB (@lem1207717 A P Q) (@lem1207721 A Q P)). Qed.
Lemma lem1207724 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1207725 : (True = True) = True.
Proof. exact (@lem1207724 True). Qed.
Lemma lem1207726 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : ((term4 A P Q) = (term5 A Q P)) = True.
Proof. exact (TRANS (@lem1207722 A Q P) (@lem1207725)). Qed.
Lemma lem1207727 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : True = ((term4 A P Q) = (term5 A Q P)).
Proof. exact (SYM (@lem1207726 A Q P)). Qed.
Lemma lem1207728 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term4 A P Q) = (term5 A Q P).
Proof. exact (EQ_MP (@lem1207727 A Q P) (@lem0)). Qed.
Lemma lem1207732 {_25594 : Type'} (h : _25594) (P : _25594 -> Prop) (t : list _25594) : (term36 _25594 P h t) = (term37 _25594 h P t).
Proof. exact (EQ_MP (@lem1106572 _25594 h P t) (@lem1106571 _25594 h P t)). Qed.
Lemma lem1207733 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term36 A P h t) = (term37 A h P t).
Proof. exact (@lem1207732 A h P t). Qed.
Lemma lem1207734 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term36 A Q h t) = (term37 A h Q t).
Proof. exact (@lem1207733 A h Q t). Qed.
Lemma lem1207735 {A : Type'} (P : A -> Prop) : (@List.Forall A P) = (@List.Forall A P).
Proof. exact (eq_refl (@List.Forall A P)). Qed.
Lemma lem1207736 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term14 A P Q h t) = (term38 A P h Q t).
Proof. exact (MK_COMB (@lem1207735 A P) (@lem1207734 A h Q t)). Qed.
Lemma lem1207737 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207738 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term39 A P Q h t) = (term40 A P h Q t).
Proof. exact (MK_COMB (@lem1207737) (@lem1207736 A P h Q t)). Qed.
Lemma lem1207740 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term41 _25307 P h t) = (term42 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1207741 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term41 A P h t) = (term42 A h P t).
Proof. exact (@lem1207740 A h P t). Qed.
Lemma lem1207742 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term15 A Q P h t) = (term43 A h Q P t).
Proof. exact (@lem1207741 A h (term35 A Q P) t). Qed.
Lemma lem1207746 {A B : Type'} (f : A -> B) (y : A) : (term44 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1207747 {A : Type'} (f : A -> Prop) (y : A) : (term45 A f y) = (f y).
Proof. exact (@lem1207746 A Prop f y). Qed.
Lemma lem1207748 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term46 A Q P h) = (term47 A Q P h).
Proof. exact (@lem1207747 A (term35 A Q P) h). Qed.
Lemma lem1207749 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (x : A) : (term47 A Q P x) = (term48 A Q P x).
Proof. exact (eq_refl (term47 A Q P x)). Qed.
Lemma lem1207750 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : (term49 A Q P) = (term35 A Q P).
Proof. exact (fun_ext (fun x : A => @lem1207749 A Q P x)). Qed.
Lemma lem1207751 {A : Type'} (h : A) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1207752 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term46 A Q P h) = (term47 A Q P h).
Proof. exact (MK_COMB (@lem1207750 A Q P) (@lem1207751 A h)). Qed.
Lemma lem1207753 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207754 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term50 A Q P h) = (term51 A Q P h).
Proof. exact (MK_COMB (@lem1207753) (@lem1207752 A Q P h)). Qed.
Lemma lem1207755 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term47 A Q P h) = (term48 A Q P h).
Proof. exact (eq_refl (term47 A Q P h)). Qed.
Lemma lem1207756 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : ((term46 A Q P h) = (term47 A Q P h)) = ((term47 A Q P h) = (term48 A Q P h)).
Proof. exact (MK_COMB (@lem1207754 A Q P h) (@lem1207755 A Q P h)). Qed.
Lemma lem1207757 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term47 A Q P h) = (term48 A Q P h).
Proof. exact (EQ_MP (@lem1207756 A Q P h) (@lem1207748 A Q P h)). Qed.
Lemma lem1207760 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207761 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : (term52 A Q P h) = (term53 A Q P h).
Proof. exact (MK_COMB (@lem1207760) (@lem1207757 A Q P h)). Qed.
Lemma lem1207764 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term10 A Q P t) = (term10 A Q P t).
Proof. exact (eq_refl (term10 A Q P t)). Qed.
Lemma lem1207765 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term43 A h Q P t) = (term54 A h Q P t).
Proof. exact (MK_COMB (@lem1207761 A Q P h) (@lem1207764 A Q P t)). Qed.
Lemma lem1207768 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term15 A Q P h t) = (term54 A h Q P t).
Proof. exact (TRANS (@lem1207742 A h Q P t) (@lem1207765 A h Q P t)). Qed.
Lemma lem1207769 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term14 A P Q h t) = (term15 A Q P h t)) = ((term38 A P h Q t) = (term54 A h Q P t)).
Proof. exact (MK_COMB (@lem1207738 A P h Q t) (@lem1207768 A h Q P t)). Qed.
Lemma lem1207772 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) (t : list A) : ((term38 A P h Q t) = (term54 A h Q P t)) = ((term14 A P Q h t) = (term15 A Q P h t)).
Proof. exact (SYM (@lem1207769 A h Q P t)). Qed.
Lemma lem1207773 {A : Type'} (_474 : list A) (_475 : Prop) (_476 : type1143 A) (_477 : list A) : (term55 A _476 _475 _474 _477) = (term56 A _474 _475 _476 _477).
Proof. exact (@lem13473 (list A) _474 _475 _476 _477). Qed.
Lemma lem1207774 {A : Type'} (_474 : list A) (_475 : Prop) (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (_477 : list A) : (term57 A h Q P t _475 _474 _477) = (term58 A _474 _475 h Q P t _477).
Proof. exact (@lem1207773 A _474 _475 (term59 A h Q P t) _477). Qed.
Lemma lem1207775 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) : (term60 A P h Q t) = (term61 A h P Q t).
Proof. exact (@lem1207774 A (term62 A h Q t) (Q h) h Q P t (@FILTER A Q t)). Qed.
Lemma lem1207776 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term63 A h P Q t) = ((term9 A P Q t) = (term54 A h Q P t)).
Proof. exact (eq_refl (term63 A h P Q t)). Qed.
Lemma lem1207777 {A : Type'} (Q : A -> Prop) (h : A) : (term64 A Q h) = (term64 A Q h).
Proof. exact (eq_refl (term64 A Q h)). Qed.
Lemma lem1207778 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term65 A h P Q t) = (term66 A h Q P t).
Proof. exact (MK_COMB (@lem1207777 A Q h) (@lem1207776 A h Q P t)). Qed.
Lemma lem1207779 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term67 A P h Q t) = ((term68 A P h Q t) = (term54 A h Q P t)).
Proof. exact (eq_refl (term67 A P h Q t)). Qed.
Lemma lem1207780 {A : Type'} (Q : A -> Prop) (h : A) : (term69 A Q h) = (term69 A Q h).
Proof. exact (eq_refl (term69 A Q h)). Qed.
Lemma lem1207781 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term70 A P h Q t) = (term71 A h Q P t).
Proof. exact (MK_COMB (@lem1207780 A Q h) (@lem1207779 A h Q P t)). Qed.
Lemma lem1207782 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207783 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term72 A P h Q t) = (term73 A h Q P t).
Proof. exact (MK_COMB (@lem1207782) (@lem1207781 A h Q P t)). Qed.
Lemma lem1207784 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term61 A h P Q t) = (term74 A h Q P t).
Proof. exact (MK_COMB (@lem1207783 A h Q P t) (@lem1207778 A h Q P t)). Qed.
Lemma lem1207785 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term60 A P h Q t) = ((term38 A P h Q t) = (term54 A h Q P t)).
Proof. exact (eq_refl (term60 A P h Q t)). Qed.
Lemma lem1207786 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207787 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term75 A P h Q t) = (term76 A h Q P t).
Proof. exact (MK_COMB (@lem1207786) (@lem1207785 A h Q P t)). Qed.
Lemma lem1207788 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term60 A P h Q t) = (term61 A h P Q t)) = (((term38 A P h Q t) = (term54 A h Q P t)) = (term74 A h Q P t)).
Proof. exact (MK_COMB (@lem1207787 A h Q P t) (@lem1207784 A h Q P t)). Qed.
Lemma lem1207789 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term38 A P h Q t) = (term54 A h Q P t)) = (term74 A h Q P t).
Proof. exact (EQ_MP (@lem1207788 A h Q P t) (@lem1207775 A h P Q t)). Qed.
Lemma lem1207790 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term74 A h Q P t) = ((term38 A P h Q t) = (term54 A h Q P t)).
Proof. exact (SYM (@lem1207789 A h Q P t)). Qed.
Lemma lem1207791 {A : Type'} (Q : A -> Prop) (h : A) (h1 : Q h) : Q h.
Proof. exact (h1). Qed.
Lemma lem1207792 {A : Type'} (Q : A -> Prop) (h : A) : (Q h) = ((Q h) = True).
Proof. exact (@lem7 (Q h)). Qed.
Lemma lem1207793 {A : Type'} (Q : A -> Prop) (h : A) (h1 : Q h) : (Q h) = True.
Proof. exact (EQ_MP (@lem1207792 A Q h) (@lem1207791 A Q h h1)). Qed.
Lemma lem1207794 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term77 A h Q P t) = (term77 A h Q P t).
Proof. exact (eq_refl (term77 A h Q P t)). Qed.
Lemma lem1207795 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) (h1 : Q h) : (term78 A P t Q h) = (term79 A h Q P t).
Proof. exact (MK_COMB (@lem1207794 A h Q P t) (@lem1207793 A Q h h1)). Qed.
Lemma lem1207796 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term79 A h Q P t) = ((term68 A P h Q t) = (term80 A h Q P t)).
Proof. exact (eq_refl (term79 A h Q P t)). Qed.
Lemma lem1207797 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) : (term81 A P t Q h) = (term81 A P t Q h).
Proof. exact (eq_refl (term81 A P t Q h)). Qed.
Lemma lem1207798 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term78 A P t Q h) = (term79 A h Q P t)) = ((term78 A P t Q h) = ((term68 A P h Q t) = (term80 A h Q P t))).
Proof. exact (MK_COMB (@lem1207797 A P t Q h) (@lem1207796 A h Q P t)). Qed.
Lemma lem1207799 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term78 A P t Q h) = ((term68 A P h Q t) = (term54 A h Q P t)).
Proof. exact (eq_refl (term78 A P t Q h)). Qed.
Lemma lem1207800 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207801 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term81 A P t Q h) = (term82 A h Q P t).
Proof. exact (MK_COMB (@lem1207800) (@lem1207799 A h Q P t)). Qed.
Lemma lem1207802 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term68 A P h Q t) = (term80 A h Q P t)) = ((term68 A P h Q t) = (term80 A h Q P t)).
Proof. exact (eq_refl ((term68 A P h Q t) = (term80 A h Q P t))). Qed.
Lemma lem1207803 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term78 A P t Q h) = ((term68 A P h Q t) = (term80 A h Q P t))) = (((term68 A P h Q t) = (term54 A h Q P t)) = ((term68 A P h Q t) = (term80 A h Q P t))).
Proof. exact (MK_COMB (@lem1207801 A h Q P t) (@lem1207802 A h Q P t)). Qed.
Lemma lem1207804 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term78 A P t Q h) = (term79 A h Q P t)) = (((term68 A P h Q t) = (term54 A h Q P t)) = ((term68 A P h Q t) = (term80 A h Q P t))).
Proof. exact (TRANS (@lem1207798 A h Q P t) (@lem1207803 A h Q P t)). Qed.
Lemma lem1207805 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) (h1 : Q h) : ((term68 A P h Q t) = (term54 A h Q P t)) = ((term68 A P h Q t) = (term80 A h Q P t)).
Proof. exact (EQ_MP (@lem1207804 A h Q P t) (@lem1207795 A P t Q h h1)). Qed.
Lemma lem1207806 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) (h1 : Q h) : ((term68 A P h Q t) = (term80 A h Q P t)) = ((term68 A P h Q t) = (term54 A h Q P t)).
Proof. exact (SYM (@lem1207805 A P t Q h h1)). Qed.
Lemma lem1207807 {A : Type'} (Q : A -> Prop) (h : A) (h1 : term83 A Q h) : term83 A Q h.
Proof. exact (h1). Qed.
Lemma lem1207808 {A : Type'} (Q : A -> Prop) (h : A) : term84 A Q h.
Proof. exact (@lem82 (Q h)). Qed.
Lemma lem1207809 {A : Type'} (Q : A -> Prop) (h : A) (h1 : term83 A Q h) : (Q h) = False.
Proof. exact (@lem1207808 A Q h (@lem1207807 A Q h h1)). Qed.
Lemma lem1207810 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term85 A h Q P t) = (term85 A h Q P t).
Proof. exact (eq_refl (term85 A h Q P t)). Qed.
Lemma lem1207811 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) (h1 : term83 A Q h) : (term86 A P t Q h) = (term87 A h Q P t).
Proof. exact (MK_COMB (@lem1207810 A h Q P t) (@lem1207809 A Q h h1)). Qed.
Lemma lem1207812 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term87 A h Q P t) = ((term9 A P Q t) = (term88 A h Q P t)).
Proof. exact (eq_refl (term87 A h Q P t)). Qed.
Lemma lem1207813 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) : (term89 A P t Q h) = (term89 A P t Q h).
Proof. exact (eq_refl (term89 A P t Q h)). Qed.
Lemma lem1207814 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term86 A P t Q h) = (term87 A h Q P t)) = ((term86 A P t Q h) = ((term9 A P Q t) = (term88 A h Q P t))).
Proof. exact (MK_COMB (@lem1207813 A P t Q h) (@lem1207812 A h Q P t)). Qed.
Lemma lem1207815 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term86 A P t Q h) = ((term9 A P Q t) = (term54 A h Q P t)).
Proof. exact (eq_refl (term86 A P t Q h)). Qed.
Lemma lem1207816 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207817 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term89 A P t Q h) = (term90 A h Q P t).
Proof. exact (MK_COMB (@lem1207816) (@lem1207815 A h Q P t)). Qed.
Lemma lem1207818 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term9 A P Q t) = (term88 A h Q P t)) = ((term9 A P Q t) = (term88 A h Q P t)).
Proof. exact (eq_refl ((term9 A P Q t) = (term88 A h Q P t))). Qed.
Lemma lem1207819 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term86 A P t Q h) = ((term9 A P Q t) = (term88 A h Q P t))) = (((term9 A P Q t) = (term54 A h Q P t)) = ((term9 A P Q t) = (term88 A h Q P t))).
Proof. exact (MK_COMB (@lem1207817 A h Q P t) (@lem1207818 A h Q P t)). Qed.
Lemma lem1207820 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term86 A P t Q h) = (term87 A h Q P t)) = (((term9 A P Q t) = (term54 A h Q P t)) = ((term9 A P Q t) = (term88 A h Q P t))).
Proof. exact (TRANS (@lem1207814 A h Q P t) (@lem1207819 A h Q P t)). Qed.
Lemma lem1207821 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) (h1 : term83 A Q h) : ((term9 A P Q t) = (term54 A h Q P t)) = ((term9 A P Q t) = (term88 A h Q P t)).
Proof. exact (EQ_MP (@lem1207820 A h Q P t) (@lem1207811 A P t Q h h1)). Qed.
Lemma lem1207822 {A : Type'} (P : A -> Prop) (t : list A) (Q : A -> Prop) (h : A) (h1 : term83 A Q h) : ((term9 A P Q t) = (term88 A h Q P t)) = ((term9 A P Q t) = (term54 A h Q P t)).
Proof. exact (SYM (@lem1207821 A P t Q h h1)). Qed.
Lemma lem1207830 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term41 _25307 P h t) = (term42 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1207831 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term41 A P h t) = (term42 A h P t).
Proof. exact (@lem1207830 A h P t). Qed.
Lemma lem1207832 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) : (term68 A P h Q t) = (term91 A h P Q t).
Proof. exact (@lem1207831 A h P (@FILTER A Q t)). Qed.
Lemma lem1207836 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term9 A P Q t) = (term10 A Q P t).
Proof. exact (h1). Qed.
Lemma lem1207839 {A : Type'} (P : A -> Prop) (h : A) : (term92 A P h) = (term92 A P h).
Proof. exact (eq_refl (term92 A P h)). Qed.
Lemma lem1207840 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term91 A h P Q t) = (term93 A h Q P t).
Proof. exact (MK_COMB (@lem1207839 A P h) (@lem1207836 A Q P t h1)). Qed.
Lemma lem1207843 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term68 A P h Q t) = (term93 A h Q P t).
Proof. exact (TRANS (@lem1207832 A h P Q t) (@lem1207840 A h Q P t h1)). Qed.
Lemma lem1207844 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207845 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term94 A P h Q t) = (term95 A h Q P t).
Proof. exact (MK_COMB (@lem1207844) (@lem1207843 A h Q P t h1)). Qed.
Lemma lem1207849 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1207850 {A : Type'} (P : A -> Prop) (h : A) : (term96 A P h) = (P h).
Proof. exact (@lem1207849 (P h)). Qed.
Lemma lem1207851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207852 {A : Type'} (P : A -> Prop) (h : A) : (term97 A P h) = (term92 A P h).
Proof. exact (MK_COMB (@lem1207851) (@lem1207850 A P h)). Qed.
Lemma lem1207855 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term10 A Q P t) = (term10 A Q P t).
Proof. exact (eq_refl (term10 A Q P t)). Qed.
Lemma lem1207856 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term80 A h Q P t) = (term93 A h Q P t).
Proof. exact (MK_COMB (@lem1207852 A P h) (@lem1207855 A Q P t)). Qed.
Lemma lem1207859 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : ((term68 A P h Q t) = (term80 A h Q P t)) = ((term93 A h Q P t) = (term93 A h Q P t)).
Proof. exact (MK_COMB (@lem1207845 A h Q P t h1) (@lem1207856 A h Q P t)). Qed.
Lemma lem1207861 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1207862 (x : Prop) : (x = x) = True.
Proof. exact (@lem1207861 Prop x). Qed.
Lemma lem1207863 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term93 A h Q P t) = (term93 A h Q P t)) = True.
Proof. exact (@lem1207862 (term93 A h Q P t)). Qed.
Lemma lem1207864 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : ((term68 A P h Q t) = (term80 A h Q P t)) = True.
Proof. exact (TRANS (@lem1207859 A h Q P t h1) (@lem1207863 A h Q P t)). Qed.
Lemma lem1207865 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : True = ((term68 A P h Q t) = (term80 A h Q P t)).
Proof. exact (SYM (@lem1207864 A h Q P t h1)). Qed.
Lemma lem1207866 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term68 A P h Q t) = (term80 A h Q P t).
Proof. exact (EQ_MP (@lem1207865 A h Q P t h1) (@lem0)). Qed.
Lemma lem1207874 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term9 A P Q t) = (term10 A Q P t).
Proof. exact (h1). Qed.
Lemma lem1207877 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1207878 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term98 A P Q t) = (term99 A Q P t).
Proof. exact (MK_COMB (@lem1207877) (@lem1207874 A Q P t h1)). Qed.
Lemma lem1207882 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem1207883 {A : Type'} (P : A -> Prop) (h : A) : (term100 A P h) = True.
Proof. exact (@lem1207882 (P h)). Qed.
Lemma lem1207884 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1207885 {A : Type'} (P : A -> Prop) (h : A) : (term101 A P h) = (and True).
Proof. exact (MK_COMB (@lem1207884) (@lem1207883 A P h)). Qed.
Lemma lem1207888 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term10 A Q P t) = (term10 A Q P t).
Proof. exact (eq_refl (term10 A Q P t)). Qed.
Lemma lem1207889 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term88 A h Q P t) = (term102 A Q P t).
Proof. exact (MK_COMB (@lem1207885 A P h) (@lem1207888 A Q P t)). Qed.
Lemma lem1207891 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1207892 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term102 A Q P t) = (term10 A Q P t).
Proof. exact (@lem1207891 (term10 A Q P t)). Qed.
Lemma lem1207895 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) : (term88 A h Q P t) = (term10 A Q P t).
Proof. exact (TRANS (@lem1207889 A h Q P t) (@lem1207892 A Q P t)). Qed.
Lemma lem1207896 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : ((term9 A P Q t) = (term88 A h Q P t)) = ((term10 A Q P t) = (term10 A Q P t)).
Proof. exact (MK_COMB (@lem1207878 A Q P t h1) (@lem1207895 A h Q P t)). Qed.
Lemma lem1207898 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1207899 (x : Prop) : (x = x) = True.
Proof. exact (@lem1207898 Prop x). Qed.
Lemma lem1207900 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (t : list A) : ((term10 A Q P t) = (term10 A Q P t)) = True.
Proof. exact (@lem1207899 (term10 A Q P t)). Qed.
Lemma lem1207901 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : ((term9 A P Q t) = (term88 A h Q P t)) = True.
Proof. exact (TRANS (@lem1207896 A h Q P t h1) (@lem1207900 A Q P t)). Qed.
Lemma lem1207902 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : True = ((term9 A P Q t) = (term88 A h Q P t)).
Proof. exact (SYM (@lem1207901 A h Q P t h1)). Qed.
Lemma lem1207903 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term9 A P Q t) = (term88 A h Q P t).
Proof. exact (EQ_MP (@lem1207902 A h Q P t h1) (@lem0)). Qed.
Lemma lem1207904 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : term83 A Q h) (h2 : (term9 A P Q t) = (term10 A Q P t)) : (term9 A P Q t) = (term54 A h Q P t).
Proof. exact (EQ_MP (@lem1207822 A P t Q h h1) (@lem1207903 A h Q P t h2)). Qed.
Lemma lem1207905 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : term83 A Q h) (h2 : (term9 A P Q t) = (term10 A Q P t)) : (term83 A Q h) = ((term9 A P Q t) = (term54 A h Q P t)).
Proof. exact (prop_ext (fun h3 : term83 A Q h => @lem1207904 A h Q P t h1 h2) (fun h3 : (term9 A P Q t) = (term54 A h Q P t) => @lem1207807 A Q h h1)). Qed.
Lemma lem1207906 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : term83 A Q h) (h2 : (term9 A P Q t) = (term10 A Q P t)) : (term9 A P Q t) = (term54 A h Q P t).
Proof. exact (EQ_MP (@lem1207905 A h Q P t h1 h2) (@lem1207807 A Q h h1)). Qed.
Lemma lem1207907 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : term66 A h Q P t.
Proof. exact (fun h0 : term83 A Q h => @lem1207906 A h Q P t h0 h1). Qed.
Lemma lem1207908 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : Q h) (h2 : (term9 A P Q t) = (term10 A Q P t)) : (term68 A P h Q t) = (term54 A h Q P t).
Proof. exact (EQ_MP (@lem1207806 A P t Q h h1) (@lem1207866 A h Q P t h2)). Qed.
Lemma lem1207909 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : Q h) (h2 : (term9 A P Q t) = (term10 A Q P t)) : (Q h) = ((term68 A P h Q t) = (term54 A h Q P t)).
Proof. exact (prop_ext (fun h3 : Q h => @lem1207908 A h Q P t h1 h2) (fun h3 : (term68 A P h Q t) = (term54 A h Q P t) => @lem1207791 A Q h h1)). Qed.
Lemma lem1207910 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : Q h) (h2 : (term9 A P Q t) = (term10 A Q P t)) : (term68 A P h Q t) = (term54 A h Q P t).
Proof. exact (EQ_MP (@lem1207909 A h Q P t h1 h2) (@lem1207791 A Q h h1)). Qed.
Lemma lem1207911 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : term71 A h Q P t.
Proof. exact (fun h0 : Q h => @lem1207910 A h Q P t h0 h1). Qed.
Lemma lem1207912 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : term74 A h Q P t.
Proof. exact (conj (@lem1207911 A h Q P t h1) (@lem1207907 A h Q P t h1)). Qed.
Lemma lem1207913 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term38 A P h Q t) = (term54 A h Q P t).
Proof. exact (EQ_MP (@lem1207790 A h Q P t) (@lem1207912 A h Q P t h1)). Qed.
Lemma lem1207914 {A : Type'} (h : A) (Q : A -> Prop) (P : A -> Prop) (t : list A) (h1 : (term9 A P Q t) = (term10 A Q P t)) : (term14 A P Q h t) = (term15 A Q P h t).
Proof. exact (EQ_MP (@lem1207772 A Q P h t) (@lem1207913 A h Q P t h1)). Qed.
Lemma lem1207915 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) (t : list A) : term17 A Q P h t.
Proof. exact (fun h0 : (term9 A P Q t) = (term10 A Q P t) => @lem1207914 A h Q P t h0). Qed.
Lemma lem1207920 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (h : A) : term21 A Q P h.
Proof. exact (fun t : list A => @lem1207915 A Q P h t). Qed.
Lemma lem1207925 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : term25 A Q P.
Proof. exact (fun h : A => @lem1207920 A Q P h). Qed.
Lemma lem1207926 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : term27 A Q P.
Proof. exact (conj (@lem1207728 A Q P) (@lem1207925 A Q P)). Qed.
Lemma lem1207927 {A : Type'} (Q : A -> Prop) (P : A -> Prop) : term32 A Q P.
Proof. exact (@lem1207702 A Q P (@lem1207926 A Q P)). Qed.
Lemma lem1207932 {A : Type'} (P : A -> Prop) : term103 A P.
Proof. exact (fun Q : A -> Prop => @lem1207927 A Q P). Qed.
Lemma lem1207937 {A : Type'} : term104 A.
Proof. exact (fun P : A -> Prop => @lem1207932 A P). Qed.
