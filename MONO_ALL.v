Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MONO_ALL_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17265_spec.
Require Import thm1820_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Lemma lem1237625 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem1237627 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1237628 {A : Type'} (P : type1143 A) : term1 A P.
Proof. exact (@lem1237627 A P). Qed.
Lemma lem1237629 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term2 A P Q.
Proof. exact (@lem1237628 A (term3 A P Q)). Qed.
Lemma lem1237630 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term4 A P Q) = (term5 A P Q).
Proof. exact (eq_refl (term4 A P Q)). Qed.
Lemma lem1237631 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1237632 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term6 A P Q) = (term7 A P Q).
Proof. exact (MK_COMB (@lem1237631) (@lem1237630 A P Q)). Qed.
Lemma lem1237633 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (t : list A) : (term8 A P Q t) = (term9 A P Q t).
Proof. exact (eq_refl (term8 A P Q t)). Qed.
Lemma lem1237634 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237635 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (t : list A) : (term10 A P Q t) = (term11 A P Q t).
Proof. exact (MK_COMB (@lem1237634) (@lem1237633 A P Q t)). Qed.
Lemma lem1237636 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h : A) (t : list A) : (term12 A P Q h t) = (term13 A P Q h t).
Proof. exact (eq_refl (term12 A P Q h t)). Qed.
Lemma lem1237637 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h : A) (t : list A) : (term14 A P Q h t) = (term15 A P Q h t).
Proof. exact (MK_COMB (@lem1237635 A P Q t) (@lem1237636 A P Q h t)). Qed.
Lemma lem1237638 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h : A) : (term16 A P Q h) = (term17 A P Q h).
Proof. exact (fun_ext (fun t : list A => @lem1237637 A P Q h t)). Qed.
Lemma lem1237639 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1237640 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h : A) : (term18 A P Q h) = (term19 A P Q h).
Proof. exact (MK_COMB (@lem1237639 A) (@lem1237638 A P Q h)). Qed.
Lemma lem1237641 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term20 A P Q) = (term21 A P Q).
Proof. exact (fun_ext (fun h : A => @lem1237640 A P Q h)). Qed.
Lemma lem1237642 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1237643 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term22 A P Q) = (term23 A P Q).
Proof. exact (MK_COMB (@lem1237642 A) (@lem1237641 A P Q)). Qed.
Lemma lem1237644 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term24 A P Q) = (term25 A P Q).
Proof. exact (MK_COMB (@lem1237632 A P Q) (@lem1237643 A P Q)). Qed.
Lemma lem1237645 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237646 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term26 A P Q) = (term27 A P Q).
Proof. exact (MK_COMB (@lem1237645) (@lem1237644 A P Q)). Qed.
Lemma lem1237647 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (l : list A) : (term8 A P Q l) = (term9 A P Q l).
Proof. exact (eq_refl (term8 A P Q l)). Qed.
Lemma lem1237648 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term28 A P Q) = (term3 A P Q).
Proof. exact (fun_ext (fun l : list A => @lem1237647 A P Q l)). Qed.
Lemma lem1237649 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1237650 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term29 A P Q) = (term30 A P Q).
Proof. exact (MK_COMB (@lem1237649 A) (@lem1237648 A P Q)). Qed.
Lemma lem1237651 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term2 A P Q) = (term31 A P Q).
Proof. exact (MK_COMB (@lem1237646 A P Q) (@lem1237650 A P Q)). Qed.
Lemma lem1237652 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term31 A P Q.
Proof. exact (EQ_MP (@lem1237651 A P Q) (@lem1237629 A P Q)). Qed.
Lemma lem1237653 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term9 A P Q t) : term9 A P Q t.
Proof. exact (h1). Qed.
Lemma lem1237664 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1237665 {A : Type'} (P : A -> Prop) : (@List.Forall A P (@nil A)) = True.
Proof. exact (@lem1237664 A P). Qed.
Lemma lem1237666 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237667 {A : Type'} (P : A -> Prop) : (term32 A P) = (imp True).
Proof. exact (MK_COMB (@lem1237666) (@lem1237665 A P)). Qed.
Lemma lem1237669 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1237670 {A : Type'} (P : A -> Prop) : (@List.Forall A P (@nil A)) = True.
Proof. exact (@lem1237669 A P). Qed.
Lemma lem1237671 {A : Type'} (Q : A -> Prop) : (@List.Forall A Q (@nil A)) = True.
Proof. exact (@lem1237670 A Q). Qed.
Lemma lem1237672 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term5 A P Q) = (True -> True).
Proof. exact (MK_COMB (@lem1237667 A P) (@lem1237671 A Q)). Qed.
Lemma lem1237674 (t : Prop) : (True -> t) = t.
Proof. exact (proj1 (@lem1820 t)). Qed.
Lemma lem1237675 : (True -> True) = True.
Proof. exact (@lem1237674 True). Qed.
Lemma lem1237676 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term5 A P Q) = True.
Proof. exact (TRANS (@lem1237672 A P Q) (@lem1237675)). Qed.
Lemma lem1237677 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : True = (term5 A P Q).
Proof. exact (SYM (@lem1237676 A P Q)). Qed.
Lemma lem1237678 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term5 A P Q.
Proof. exact (EQ_MP (@lem1237677 A P Q) (@lem0)). Qed.
Lemma lem1237691 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term33 _25307 P h t) = (term34 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1237692 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term33 A P h t) = (term34 A h P t).
Proof. exact (@lem1237691 A h P t). Qed.
Lemma lem1237695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237696 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term35 A P h t) = (term36 A h P t).
Proof. exact (MK_COMB (@lem1237695) (@lem1237692 A h P t)). Qed.
Lemma lem1237698 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term33 _25307 P h t) = (term34 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1237699 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term33 A P h t) = (term34 A h P t).
Proof. exact (@lem1237698 A h P t). Qed.
Lemma lem1237700 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term33 A Q h t) = (term34 A h Q t).
Proof. exact (@lem1237699 A h Q t). Qed.
Lemma lem1237703 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term13 A P Q h t) = (term37 A P h Q t).
Proof. exact (MK_COMB (@lem1237696 A h P t) (@lem1237700 A h Q t)). Qed.
Lemma lem1237706 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h : A) (t : list A) : (term37 A P h Q t) = (term13 A P Q h t).
Proof. exact (SYM (@lem1237703 A P h Q t)). Qed.
Lemma lem1237708 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1237709 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term37 A P h Q t) = (term39 A P h Q t).
Proof. exact (@lem1237708 (term37 A P h Q t)). Qed.
Lemma lem1237710 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term39 A P h Q t) = (term37 A P h Q t).
Proof. exact (SYM (@lem1237709 A P h Q t)). Qed.
Lemma lem1237711 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term40 A P h Q t) : term40 A P h Q t.
Proof. exact (h1). Qed.
Lemma lem1237714 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term41 A P h Q t) : term41 A P h Q t.
Proof. exact (h1). Qed.
Lemma lem1237715 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : term42 A P h Q t.
Proof. exact (fun h0 : term41 A P h Q t => @lem1237714 A P h Q t h0). Qed.
Lemma lem1237716 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term42 A P h Q t) : term42 A P h Q t.
Proof. exact (h1). Qed.
Lemma lem1237717 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term41 A P h Q t) : term41 A P h Q t.
Proof. exact (h1). Qed.
Lemma lem1237718 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term41 A P h Q t) (h2 : term42 A P h Q t) : term41 A P h Q t.
Proof. exact (@lem1237716 A P h Q t h2 (@lem1237717 A P h Q t h1)). Qed.
Lemma lem1237719 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term41 A P h Q t) : term43 A P h Q t.
Proof. exact (fun h0 : term42 A P h Q t => @lem1237718 A P h Q t h1 h0). Qed.
Lemma lem1237720 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term42 A P h Q t) : term42 A P h Q t.
Proof. exact (h1). Qed.
Lemma lem1237721 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term41 A P h Q t) (h2 : term42 A P h Q t) : term41 A P h Q t.
Proof. exact (@lem1237719 A P h Q t h1 (@lem1237720 A P h Q t h2)). Qed.
Lemma lem1237722 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) (h1 : term42 A P h Q t) : term42 A P h Q t.
Proof. exact (fun h0 : term41 A P h Q t => @lem1237721 A P h Q t h0 h1). Qed.
Lemma lem1237723 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : term44 A P h Q t.
Proof. exact (fun h0 : term42 A P h Q t => @lem1237722 A P h Q t h0). Qed.
Lemma lem1237726 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : term42 A P h Q t.
Proof. exact (@lem1237723 A P h Q t (@lem1237715 A P h Q t)). Qed.
Lemma lem1237727 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : term42 A P h Q t.
Proof. exact (@lem1237726 A P h Q t). Qed.
Lemma lem1237757 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1237758 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term39 A P h Q t) = (term45 A P h Q t).
Proof. exact (@lem1237757 (term40 A P h Q t)). Qed.
Lemma lem1237760 (t : Prop) : (term46 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1237761 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term45 A P h Q t) = (term37 A P h Q t).
Proof. exact (@lem1237760 (term37 A P h Q t)). Qed.
Lemma lem1237764 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term39 A P h Q t) = (term37 A P h Q t).
Proof. exact (TRANS (@lem1237758 A P h Q t) (@lem1237761 A P h Q t)). Qed.
Lemma lem1237769 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (t : list A) : (term11 A P Q t) = (term11 A P Q t).
Proof. exact (eq_refl (term11 A P Q t)). Qed.
Lemma lem1237770 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term47 A P h Q t) = (term48 A P h Q t).
Proof. exact (MK_COMB (@lem1237769 A P Q t) (@lem1237764 A P h Q t)). Qed.
Lemma lem1237773 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = (term49 A P Q).
Proof. exact (eq_refl (term49 A P Q)). Qed.
Lemma lem1237774 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term41 A P h Q t) = (term50 A P h Q t).
Proof. exact (MK_COMB (@lem1237773 A P Q) (@lem1237770 A P h Q t)). Qed.
Lemma lem1237777 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term51 A h Q t) = (term52 A h Q t).
Proof. exact (fun_ext (fun P : A -> Prop => @lem1237774 A P h Q t)). Qed.
Lemma lem1237778 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem1237779 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term53 A h Q t) = (term54 A h Q t).
Proof. exact (MK_COMB (@lem1237778 A) (@lem1237777 A h Q t)). Qed.
Lemma lem1237784 {A : Type'} (Q : A -> Prop) (t : list A) : (term55 A Q t) = (term56 A Q t).
Proof. exact (fun_ext (fun h : A => @lem1237779 A h Q t)). Qed.
Lemma lem1237785 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1237786 {A : Type'} (Q : A -> Prop) (t : list A) : (term57 A Q t) = (term58 A Q t).
Proof. exact (MK_COMB (@lem1237785 A) (@lem1237784 A Q t)). Qed.
Lemma lem1237791 {A : Type'} (t : list A) : (term59 A t) = (term60 A t).
Proof. exact (fun_ext (fun Q : A -> Prop => @lem1237786 A Q t)). Qed.
Lemma lem1237792 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem1237793 {A : Type'} (t : list A) : (term61 A t) = (term62 A t).
Proof. exact (MK_COMB (@lem1237792 A) (@lem1237791 A t)). Qed.
Lemma lem1237798 {A : Type'} : (term63 A) = (term64 A).
Proof. exact (fun_ext (fun t : list A => @lem1237793 A t)). Qed.
Lemma lem1237799 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1237808 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (MK_COMB (@lem1237799 A) (@lem1237798 A)). Qed.
Lemma lem1237829 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term48 A P h Q t) = (term48 A P h Q t).
Proof. exact (eq_refl (term48 A P h Q t)). Qed.
Lemma lem1237834 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term67 A P Q x) = (term67 A P Q x).
Proof. exact (eq_refl (term67 A P Q x)). Qed.
Lemma lem1237835 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term68 A P Q) = (term68 A P Q).
Proof. exact (fun_ext (fun x : A => @lem1237834 A P Q x)). Qed.
Lemma lem1237836 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1237837 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term0 A P Q).
Proof. exact (MK_COMB (@lem1237836 A) (@lem1237835 A P Q)). Qed.
Lemma lem1237838 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1237839 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term49 A P Q) = (term49 A P Q).
Proof. exact (MK_COMB (@lem1237838) (@lem1237837 A P Q)). Qed.
Lemma lem1237840 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term50 A P h Q t) = (term50 A P h Q t).
Proof. exact (MK_COMB (@lem1237839 A P Q) (@lem1237829 A P h Q t)). Qed.
Lemma lem1237841 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term52 A h Q t) = (term52 A h Q t).
Proof. exact (fun_ext (fun P : A -> Prop => @lem1237840 A P h Q t)). Qed.
Lemma lem1237842 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem1237843 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term54 A h Q t) = (term54 A h Q t).
Proof. exact (MK_COMB (@lem1237842 A) (@lem1237841 A h Q t)). Qed.
Lemma lem1237844 {A : Type'} (Q : A -> Prop) (t : list A) : (term56 A Q t) = (term56 A Q t).
Proof. exact (fun_ext (fun h : A => @lem1237843 A h Q t)). Qed.
Lemma lem1237845 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1237846 {A : Type'} (Q : A -> Prop) (t : list A) : (term58 A Q t) = (term58 A Q t).
Proof. exact (MK_COMB (@lem1237845 A) (@lem1237844 A Q t)). Qed.
Lemma lem1237847 {A : Type'} (t : list A) : (term60 A t) = (term60 A t).
Proof. exact (fun_ext (fun Q : A -> Prop => @lem1237846 A Q t)). Qed.
Lemma lem1237848 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem1237849 {A : Type'} (t : list A) : (term62 A t) = (term62 A t).
Proof. exact (MK_COMB (@lem1237848 A) (@lem1237847 A t)). Qed.
Lemma lem1237850 {A : Type'} : (term64 A) = (term64 A).
Proof. exact (fun_ext (fun t : list A => @lem1237849 A t)). Qed.
Lemma lem1237851 {A : Type'} : (@all (list A)) = (@all (list A)).
Proof. exact (eq_refl (@all (list A))). Qed.
Lemma lem1237852 {A : Type'} : (term66 A) = (term66 A).
Proof. exact (MK_COMB (@lem1237851 A) (@lem1237850 A)). Qed.
Lemma lem1237899 {A : Type'} : (term65 A) = (term66 A).
Proof. exact (TRANS (@lem1237808 A) (@lem1237852 A)). Qed.
Lemma lem1237900 {A : Type'} : (term66 A) = (term65 A).
Proof. exact (SYM (@lem1237899 A)). Qed.
Lemma lem1237901 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term0 A P Q.
Proof. exact (h1). Qed.
Lemma lem1237902 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term9 A P Q t) : term9 A P Q t.
Proof. exact (h1). Qed.
Lemma lem1237905 (p : Prop) : p = (term38 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1237906 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term34 A h Q t) = (term69 A h Q t).
Proof. exact (@lem1237905 (term34 A h Q t)). Qed.
Lemma lem1237907 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term69 A h Q t) = (term34 A h Q t).
Proof. exact (SYM (@lem1237906 A h Q t)). Qed.
Lemma lem1237908 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) (h1 : term70 A h Q t) : term70 A h Q t.
Proof. exact (h1). Qed.
Lemma lem1237915 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term67 A P Q x) = (term71 A P Q x).
Proof. exact (@lem17265 (P x) (Q x)). Qed.
Lemma lem1237916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term68 A P Q) = (term72 A P Q).
Proof. exact (fun_ext (fun x : A => @lem1237915 A P Q x)). Qed.
Lemma lem1237917 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1237954 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term0 A P Q) = (term73 A P Q).
Proof. exact (MK_COMB (@lem1237917 A) (@lem1237916 A P Q)). Qed.
Lemma lem1237955 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term73 A P Q.
Proof. exact (EQ_MP (@lem1237954 A P Q) (@lem1237901 A P Q h1)). Qed.
Lemma lem1237966 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (t : list A) : (term9 A P Q t) = (term74 A P Q t).
Proof. exact (@lem17265 (@List.Forall A P t) (@List.Forall A Q t)). Qed.
Lemma lem1237977 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : term34 A h P t.
Proof. exact (h1). Qed.
Lemma lem1237988 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term70 A h Q t) = (term75 A h Q t).
Proof. exact (@lem17045 (Q h) (@List.Forall A Q t)). Qed.
Lemma lem1237989 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) (h1 : term70 A h Q t) : term75 A h Q t.
Proof. exact (EQ_MP (@lem1237988 A h Q t) (@lem1237908 A h Q t h1)). Qed.
Lemma lem1237994 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1237995 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1237994 A Prop f x). Qed.
Lemma lem1237997 {A : Type'} (Q : A -> Prop) (x : A) : (Q x) = (@I (A -> Prop) Q x).
Proof. exact (@lem1237995 A Q x). Qed.
Lemma lem1237998 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1238003 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1238004 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1238003 A Prop f x). Qed.
Lemma lem1238006 {A : Type'} (P : A -> Prop) (x : A) : (P x) = (@I (A -> Prop) P x).
Proof. exact (@lem1238004 A P x). Qed.
Lemma lem1238007 {A : Type'} (P : A -> Prop) (x : A) : (term76 A P x) = (term77 A P x).
Proof. exact (MK_COMB (@lem1237998) (@lem1238006 A P x)). Qed.
Lemma lem1238008 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1238009 {A : Type'} (P : A -> Prop) (x : A) : (term78 A P x) = (term79 A P x).
Proof. exact (MK_COMB (@lem1238008) (@lem1238007 A P x)). Qed.
Lemma lem1238010 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term71 A P Q x) = (term80 A P Q x).
Proof. exact (MK_COMB (@lem1238009 A P x) (@lem1237997 A Q x)). Qed.
Lemma lem1238011 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term72 A P Q) = (term81 A P Q).
Proof. exact (fun_ext (fun x : A => @lem1238010 A P Q x)). Qed.
Lemma lem1238012 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1238013 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term73 A P Q) = (term82 A P Q).
Proof. exact (MK_COMB (@lem1238012 A) (@lem1238011 A P Q)). Qed.
Lemma lem1238014 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term82 A P Q.
Proof. exact (EQ_MP (@lem1238013 A P Q) (@lem1237955 A P Q h1)). Qed.
Lemma lem1238030 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term9 A P Q t) : term74 A P Q t.
Proof. exact (EQ_MP (@lem1237966 A P Q t) (@lem1237902 A P Q t h1)). Qed.
Lemma lem1238035 {A : Type'} (P : A -> Prop) (t : list A) : (@List.Forall A P t) = (@List.Forall A P t).
Proof. exact (eq_refl (@List.Forall A P t)). Qed.
Lemma lem1238040 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1238041 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1238040 A Prop f x). Qed.
Lemma lem1238043 {A : Type'} (P : A -> Prop) (h : A) : (P h) = (@I (A -> Prop) P h).
Proof. exact (@lem1238041 A P h). Qed.
Lemma lem1238044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1238045 {A : Type'} (P : A -> Prop) (h : A) : (term83 A P h) = (term84 A P h).
Proof. exact (MK_COMB (@lem1238044) (@lem1238043 A P h)). Qed.
Lemma lem1238046 {A : Type'} (h : A) (P : A -> Prop) (t : list A) : (term34 A h P t) = (term85 A h P t).
Proof. exact (MK_COMB (@lem1238045 A P h) (@lem1238035 A P t)). Qed.
Lemma lem1238047 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : term85 A h P t.
Proof. exact (EQ_MP (@lem1238046 A h P t) (@lem1237977 A h P t h1)). Qed.
Lemma lem1238054 {A : Type'} (Q : A -> Prop) (t : list A) : (term86 A Q t) = (term86 A Q t).
Proof. exact (eq_refl (term86 A Q t)). Qed.
Lemma lem1238055 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1238060 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1238061 {A : Type'} (f : A -> Prop) (x : A) : (f x) = (@I (A -> Prop) f x).
Proof. exact (@lem1238060 A Prop f x). Qed.
Lemma lem1238063 {A : Type'} (Q : A -> Prop) (h : A) : (Q h) = (@I (A -> Prop) Q h).
Proof. exact (@lem1238061 A Q h). Qed.
Lemma lem1238064 {A : Type'} (Q : A -> Prop) (h : A) : (term76 A Q h) = (term77 A Q h).
Proof. exact (MK_COMB (@lem1238055) (@lem1238063 A Q h)). Qed.
Lemma lem1238065 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1238066 {A : Type'} (Q : A -> Prop) (h : A) : (term78 A Q h) = (term79 A Q h).
Proof. exact (MK_COMB (@lem1238065) (@lem1238064 A Q h)). Qed.
Lemma lem1238067 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term75 A h Q t) = (term87 A h Q t).
Proof. exact (MK_COMB (@lem1238066 A Q h) (@lem1238054 A Q t)). Qed.
Lemma lem1238068 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) (h1 : term70 A h Q t) : term87 A h Q t.
Proof. exact (EQ_MP (@lem1238067 A h Q t) (@lem1237989 A h Q t h1)). Qed.
Lemma lem1238105 {A : Type'} (P : A -> Prop) (t : list A) (h1 : term86 A P t) : term86 A P t.
Proof. exact (h1). Qed.
Lemma lem1238113 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (x : A) : (term80 A P Q x) = (term80 A P Q x).
Proof. exact (eq_refl (term80 A P Q x)). Qed.
Lemma lem1238114 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term81 A P Q) = (term81 A P Q).
Proof. exact (fun_ext (fun x : A => @lem1238113 A P Q x)). Qed.
Lemma lem1238115 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem1238117 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term82 A P Q) = (term82 A P Q).
Proof. exact (MK_COMB (@lem1238115 A) (@lem1238114 A P Q)). Qed.
Lemma lem1238118 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term82 A P Q.
Proof. exact (EQ_MP (@lem1238117 A P Q) (@lem1238014 A P Q h1)). Qed.
Lemma lem1238130 {A : Type'} (Q : A -> Prop) (h : A) (h1 : term77 A Q h) : term77 A Q h.
Proof. exact (h1). Qed.
Lemma lem1238163 {A : Type'} (P : A -> Prop) (t : list A) (h1 : term86 A P t) : term86 A P t.
Proof. exact (h1). Qed.
Lemma lem1238188 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) : term86 A Q t.
Proof. exact (h1). Qed.
Lemma lem1238192 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : @List.Forall A Q t) : @List.Forall A Q t.
Proof. exact (h1). Qed.
Lemma lem1238196 {A : Type'} (_22679 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term88 A P Q _22679.
Proof. exact (@lem1238118 A P Q h1 _22679). Qed.
Lemma lem1238197 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_22679 : A) : (term88 A P Q _22679) = (term80 A P Q _22679).
Proof. exact (eq_refl (term88 A P Q _22679)). Qed.
Lemma lem1238218 {A : Type'} (P : A -> Prop) (t : list A) (h1 : term86 A P t) : term86 A P t.
Proof. exact (h1). Qed.
Lemma lem1238224 {A : Type'} (_22679 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term80 A P Q _22679.
Proof. exact (EQ_MP (@lem1238197 A P Q _22679) (@lem1238196 A _22679 P Q h1)). Qed.
Lemma lem1238230 {A : Type'} (Q : A -> Prop) (h : A) (h1 : term77 A Q h) : term77 A Q h.
Proof. exact (h1). Qed.
Lemma lem1238246 {A : Type'} (P : A -> Prop) (t : list A) (h1 : term86 A P t) : term86 A P t.
Proof. exact (h1). Qed.
Lemma lem1238258 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) : term86 A Q t.
Proof. exact (h1). Qed.
Lemma lem1238260 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : @List.Forall A Q t) : @List.Forall A Q t.
Proof. exact (h1). Qed.
Lemma lem1238262 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : @List.Forall A P t.
Proof. exact (proj2 (@lem1238047 A h P t h1)). Qed.
Lemma lem1238263 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : term89 A P t.
Proof. exact (fun h0 : term86 A P t => @lem1238262 A h P t h1). Qed.
Lemma lem1238265 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238266 {A : Type'} (P : A -> Prop) (t : list A) : (term89 A P t) = (@List.Forall A P t).
Proof. exact (@lem1238265 (@List.Forall A P t)). Qed.
Lemma lem1238267 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : @List.Forall A P t.
Proof. exact (EQ_MP (@lem1238266 A P t) (@lem1238263 A h P t h1)). Qed.
Lemma lem1238270 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1238272 {A : Type'} (P : A -> Prop) (t : list A) : (term86 A P t) = (term91 A P t).
Proof. exact (@lem1238270 (@List.Forall A P t)). Qed.
Lemma lem1238275 {A : Type'} (P : A -> Prop) (t : list A) (h1 : term86 A P t) : term91 A P t.
Proof. exact (EQ_MP (@lem1238272 A P t) (@lem1238218 A P t h1)). Qed.
Lemma lem1238278 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (@lem1238275 A P t h1 (@lem1238267 A h P t h2)). Qed.
Lemma lem1238279 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : term92.
Proof. exact (fun h0 : ~ False => @lem1238278 A h P t h1 h2). Qed.
Lemma lem1238281 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238282 : term92 = False.
Proof. exact (@lem1238281 False). Qed.
Lemma lem1238283 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238282) (@lem1238279 A h P t h1 h2)). Qed.
Lemma lem1238285 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : @I (A -> Prop) P h.
Proof. exact (proj1 (@lem1238047 A h P t h1)). Qed.
Lemma lem1238286 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : term93 A P h.
Proof. exact (fun h0 : term77 A P h => @lem1238285 A h P t h1). Qed.
Lemma lem1238288 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238289 {A : Type'} (P : A -> Prop) (h : A) : (term93 A P h) = (@I (A -> Prop) P h).
Proof. exact (@lem1238288 (@I (A -> Prop) P h)). Qed.
Lemma lem1238290 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : @I (A -> Prop) P h.
Proof. exact (EQ_MP (@lem1238289 A P h) (@lem1238286 A h P t h1)). Qed.
Lemma lem1238296 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem1238297 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : (term80 A P Q _22679) = (term94 A Q P _22679).
Proof. exact (@lem1238296 (@I (A -> Prop) Q _22679) (term77 A P _22679)). Qed.
Lemma lem1238303 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1238304 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : (term95 A P Q _22679) = (term96 A Q P _22679).
Proof. exact (MK_COMB (@lem1238303) (@lem1238297 A Q P _22679)). Qed.
Lemma lem1238310 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : (term94 A Q P _22679) = (term94 A Q P _22679).
Proof. exact (eq_refl (term94 A Q P _22679)). Qed.
Lemma lem1238311 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : ((term80 A P Q _22679) = (term94 A Q P _22679)) = ((term94 A Q P _22679) = (term94 A Q P _22679)).
Proof. exact (MK_COMB (@lem1238304 A Q P _22679) (@lem1238310 A Q P _22679)). Qed.
Lemma lem1238313 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem1238314 (x : Prop) : (x = x) = True.
Proof. exact (@lem1238313 Prop x). Qed.
Lemma lem1238315 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : ((term94 A Q P _22679) = (term94 A Q P _22679)) = True.
Proof. exact (@lem1238314 (term94 A Q P _22679)). Qed.
Lemma lem1238316 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : ((term80 A P Q _22679) = (term94 A Q P _22679)) = True.
Proof. exact (TRANS (@lem1238311 A Q P _22679) (@lem1238315 A Q P _22679)). Qed.
Lemma lem1238317 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : True = ((term80 A P Q _22679) = (term94 A Q P _22679)).
Proof. exact (SYM (@lem1238316 A Q P _22679)). Qed.
Lemma lem1238318 {A : Type'} (Q : A -> Prop) (P : A -> Prop) (_22679 : A) : (term80 A P Q _22679) = (term94 A Q P _22679).
Proof. exact (EQ_MP (@lem1238317 A Q P _22679) (@lem0)). Qed.
Lemma lem1238319 {A : Type'} (_22679 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term94 A Q P _22679.
Proof. exact (EQ_MP (@lem1238318 A Q P _22679) (@lem1238224 A _22679 P Q h1)). Qed.
Lemma lem1238321 (b : Prop) (a : Prop) : (a \/ b) = (term97 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem1238322 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_22679 : A) : (term94 A Q P _22679) = (term98 A P Q _22679).
Proof. exact (@lem1238321 (term77 A P _22679) (@I (A -> Prop) Q _22679)). Qed.
Lemma lem1238324 (a : Prop) : (term46 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem1238325 {A : Type'} (P : A -> Prop) (_22679 : A) : (term99 A P _22679) = (@I (A -> Prop) P _22679).
Proof. exact (@lem1238324 (@I (A -> Prop) P _22679)). Qed.
Lemma lem1238326 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1238327 {A : Type'} (P : A -> Prop) (_22679 : A) : (term100 A P _22679) = (term101 A P _22679).
Proof. exact (MK_COMB (@lem1238326) (@lem1238325 A P _22679)). Qed.
Lemma lem1238328 {A : Type'} (Q : A -> Prop) (_22679 : A) : (@I (A -> Prop) Q _22679) = (@I (A -> Prop) Q _22679).
Proof. exact (eq_refl (@I (A -> Prop) Q _22679)). Qed.
Lemma lem1238329 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_22679 : A) : (term98 A P Q _22679) = (term102 A P Q _22679).
Proof. exact (MK_COMB (@lem1238327 A P _22679) (@lem1238328 A Q _22679)). Qed.
Lemma lem1238330 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (_22679 : A) : (term94 A Q P _22679) = (term102 A P Q _22679).
Proof. exact (TRANS (@lem1238322 A P Q _22679) (@lem1238329 A P Q _22679)). Qed.
Lemma lem1238333 {A : Type'} (_22679 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term102 A P Q _22679.
Proof. exact (EQ_MP (@lem1238330 A P Q _22679) (@lem1238319 A _22679 P Q h1)). Qed.
Lemma lem1238334 {A : Type'} (_22679 : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term102 A P Q _22679.
Proof. exact (@lem1238333 A _22679 P Q h1). Qed.
Lemma lem1238335 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term102 A P Q h.
Proof. exact (@lem1238334 A h P Q h1). Qed.
Lemma lem1238338 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term34 A h P t) : @I (A -> Prop) Q h.
Proof. exact (@lem1238335 A h P Q h1 (@lem1238290 A h P t h2)). Qed.
Lemma lem1238339 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term34 A h P t) : term93 A Q h.
Proof. exact (fun h0 : term77 A Q h => @lem1238338 A Q h P t h1 h2). Qed.
Lemma lem1238341 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238342 {A : Type'} (Q : A -> Prop) (h : A) : (term93 A Q h) = (@I (A -> Prop) Q h).
Proof. exact (@lem1238341 (@I (A -> Prop) Q h)). Qed.
Lemma lem1238343 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term34 A h P t) : @I (A -> Prop) Q h.
Proof. exact (EQ_MP (@lem1238342 A Q h) (@lem1238339 A Q h P t h1 h2)). Qed.
Lemma lem1238346 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1238348 {A : Type'} (Q : A -> Prop) (h : A) : (term77 A Q h) = (term103 A Q h).
Proof. exact (@lem1238346 (@I (A -> Prop) Q h)). Qed.
Lemma lem1238351 {A : Type'} (Q : A -> Prop) (h : A) (h1 : term77 A Q h) : term103 A Q h.
Proof. exact (EQ_MP (@lem1238348 A Q h) (@lem1238230 A Q h h1)). Qed.
Lemma lem1238354 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : False.
Proof. exact (@lem1238351 A Q h h2 (@lem1238343 A Q h P t h1 h3)). Qed.
Lemma lem1238355 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : term92.
Proof. exact (fun h0 : ~ False => @lem1238354 A Q h P t h1 h2 h3). Qed.
Lemma lem1238357 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238358 : term92 = False.
Proof. exact (@lem1238357 False). Qed.
Lemma lem1238359 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238358) (@lem1238355 A Q h P t h1 h2 h3)). Qed.
Lemma lem1238361 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : @List.Forall A P t.
Proof. exact (proj2 (@lem1238047 A h P t h1)). Qed.
Lemma lem1238362 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : term89 A P t.
Proof. exact (fun h0 : term86 A P t => @lem1238361 A h P t h1). Qed.
Lemma lem1238364 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238365 {A : Type'} (P : A -> Prop) (t : list A) : (term89 A P t) = (@List.Forall A P t).
Proof. exact (@lem1238364 (@List.Forall A P t)). Qed.
Lemma lem1238366 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term34 A h P t) : @List.Forall A P t.
Proof. exact (EQ_MP (@lem1238365 A P t) (@lem1238362 A h P t h1)). Qed.
Lemma lem1238369 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1238371 {A : Type'} (P : A -> Prop) (t : list A) : (term86 A P t) = (term91 A P t).
Proof. exact (@lem1238369 (@List.Forall A P t)). Qed.
Lemma lem1238374 {A : Type'} (P : A -> Prop) (t : list A) (h1 : term86 A P t) : term91 A P t.
Proof. exact (EQ_MP (@lem1238371 A P t) (@lem1238246 A P t h1)). Qed.
Lemma lem1238377 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (@lem1238374 A P t h1 (@lem1238366 A h P t h2)). Qed.
Lemma lem1238378 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : term92.
Proof. exact (fun h0 : ~ False => @lem1238377 A h P t h1 h2). Qed.
Lemma lem1238380 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238381 : term92 = False.
Proof. exact (@lem1238380 False). Qed.
Lemma lem1238382 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238381) (@lem1238378 A h P t h1 h2)). Qed.
Lemma lem1238384 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : @List.Forall A Q t) : @List.Forall A Q t.
Proof. exact (h1). Qed.
Lemma lem1238385 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : @List.Forall A Q t) : term89 A Q t.
Proof. exact (fun h0 : term86 A Q t => @lem1238384 A Q t h1). Qed.
Lemma lem1238387 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238388 {A : Type'} (Q : A -> Prop) (t : list A) : (term89 A Q t) = (@List.Forall A Q t).
Proof. exact (@lem1238387 (@List.Forall A Q t)). Qed.
Lemma lem1238389 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : @List.Forall A Q t) : @List.Forall A Q t.
Proof. exact (EQ_MP (@lem1238388 A Q t) (@lem1238385 A Q t h1)). Qed.
Lemma lem1238392 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1238394 {A : Type'} (Q : A -> Prop) (t : list A) : (term86 A Q t) = (term91 A Q t).
Proof. exact (@lem1238392 (@List.Forall A Q t)). Qed.
Lemma lem1238397 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) : term91 A Q t.
Proof. exact (EQ_MP (@lem1238394 A Q t) (@lem1238258 A Q t h1)). Qed.
Lemma lem1238400 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (@lem1238397 A Q t h1 (@lem1238389 A Q t h2)). Qed.
Lemma lem1238401 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : term92.
Proof. exact (fun h0 : ~ False => @lem1238400 A Q t h1 h2). Qed.
Lemma lem1238403 (p : Prop) : (term90 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1238404 : term92 = False.
Proof. exact (@lem1238403 False). Qed.
Lemma lem1238405 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (EQ_MP (@lem1238404) (@lem1238401 A Q t h1 h2)). Qed.
Lemma lem1238406 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : (@List.Forall A Q t) = False.
Proof. exact (prop_ext (fun h3 : @List.Forall A Q t => @lem1238405 A Q t h1 h2) (fun h3 : False => @lem1238260 A Q t h2)). Qed.
Lemma lem1238407 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (EQ_MP (@lem1238406 A Q t h1 h2) (@lem1238260 A Q t h2)). Qed.
Lemma lem1238408 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : (term86 A Q t) = False.
Proof. exact (prop_ext (fun h3 : term86 A Q t => @lem1238407 A Q t h1 h2) (fun h3 : False => @lem1238258 A Q t h1)). Qed.
Lemma lem1238409 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (EQ_MP (@lem1238408 A Q t h1 h2) (@lem1238258 A Q t h1)). Qed.
Lemma lem1238410 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : (term86 A P t) = False.
Proof. exact (prop_ext (fun h3 : term86 A P t => @lem1238382 A h P t h1 h2) (fun h3 : False => @lem1238246 A P t h1)). Qed.
Lemma lem1238411 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238410 A h P t h1 h2) (@lem1238246 A P t h1)). Qed.
Lemma lem1238412 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : (term77 A Q h) = False.
Proof. exact (prop_ext (fun h4 : term77 A Q h => @lem1238359 A Q h P t h1 h2 h3) (fun h4 : False => @lem1238230 A Q h h2)). Qed.
Lemma lem1238413 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238412 A Q h P t h1 h2 h3) (@lem1238230 A Q h h2)). Qed.
Lemma lem1238414 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : (term86 A P t) = False.
Proof. exact (prop_ext (fun h3 : term86 A P t => @lem1238283 A h P t h1 h2) (fun h3 : False => @lem1238218 A P t h1)). Qed.
Lemma lem1238415 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238414 A h P t h1 h2) (@lem1238218 A P t h1)). Qed.
Lemma lem1238416 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : (@List.Forall A Q t) = False.
Proof. exact (prop_ext (fun h3 : @List.Forall A Q t => @lem1238409 A Q t h1 h2) (fun h3 : False => @lem1238192 A Q t h2)). Qed.
Lemma lem1238417 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (EQ_MP (@lem1238416 A Q t h1 h2) (@lem1238192 A Q t h2)). Qed.
Lemma lem1238418 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : (term86 A Q t) = False.
Proof. exact (prop_ext (fun h3 : term86 A Q t => @lem1238417 A Q t h1 h2) (fun h3 : False => @lem1238188 A Q t h1)). Qed.
Lemma lem1238419 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (EQ_MP (@lem1238418 A Q t h1 h2) (@lem1238188 A Q t h1)). Qed.
Lemma lem1238420 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : (term86 A P t) = False.
Proof. exact (prop_ext (fun h3 : term86 A P t => @lem1238411 A h P t h1 h2) (fun h3 : False => @lem1238163 A P t h1)). Qed.
Lemma lem1238421 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238420 A h P t h1 h2) (@lem1238163 A P t h1)). Qed.
Lemma lem1238422 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : (term77 A Q h) = False.
Proof. exact (prop_ext (fun h4 : term77 A Q h => @lem1238413 A Q h P t h1 h2 h3) (fun h4 : False => @lem1238130 A Q h h2)). Qed.
Lemma lem1238423 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238422 A Q h P t h1 h2 h3) (@lem1238130 A Q h h2)). Qed.
Lemma lem1238424 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : (term86 A P t) = False.
Proof. exact (prop_ext (fun h3 : term86 A P t => @lem1238415 A h P t h1 h2) (fun h3 : False => @lem1238105 A P t h1)). Qed.
Lemma lem1238425 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238424 A h P t h1 h2) (@lem1238105 A P t h1)). Qed.
Lemma lem1238426 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : (@List.Forall A Q t) = False.
Proof. exact (prop_ext (fun h3 : @List.Forall A Q t => @lem1238419 A Q t h1 h2) (fun h3 : False => @lem1238192 A Q t h2)). Qed.
Lemma lem1238427 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (EQ_MP (@lem1238426 A Q t h1 h2) (@lem1238192 A Q t h2)). Qed.
Lemma lem1238428 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : (term86 A Q t) = False.
Proof. exact (prop_ext (fun h3 : term86 A Q t => @lem1238427 A Q t h1 h2) (fun h3 : False => @lem1238188 A Q t h1)). Qed.
Lemma lem1238429 {A : Type'} (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : @List.Forall A Q t) : False.
Proof. exact (EQ_MP (@lem1238428 A Q t h1 h2) (@lem1238188 A Q t h1)). Qed.
Lemma lem1238430 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : (term86 A P t) = False.
Proof. exact (prop_ext (fun h3 : term86 A P t => @lem1238421 A h P t h1 h2) (fun h3 : False => @lem1238163 A P t h1)). Qed.
Lemma lem1238431 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238430 A h P t h1 h2) (@lem1238163 A P t h1)). Qed.
Lemma lem1238432 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : (term77 A Q h) = False.
Proof. exact (prop_ext (fun h4 : term77 A Q h => @lem1238423 A Q h P t h1 h2 h3) (fun h4 : False => @lem1238130 A Q h h2)). Qed.
Lemma lem1238433 {A : Type'} (Q : A -> Prop) (h : A) (P : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238432 A Q h P t h1 h2 h3) (@lem1238130 A Q h h2)). Qed.
Lemma lem1238434 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : (term86 A P t) = False.
Proof. exact (prop_ext (fun h3 : term86 A P t => @lem1238425 A h P t h1 h2) (fun h3 : False => @lem1238105 A P t h1)). Qed.
Lemma lem1238435 {A : Type'} (h : A) (P : A -> Prop) (t : list A) (h1 : term86 A P t) (h2 : term34 A h P t) : False.
Proof. exact (EQ_MP (@lem1238434 A h P t h1 h2) (@lem1238105 A P t h1)). Qed.
Lemma lem1238436 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term86 A Q t) (h2 : term34 A h P t) (h3 : term9 A P Q t) : False.
Proof. exact (or_elim (@lem1238030 A P Q t h3) (fun h0 : term86 A P t => @lem1238431 A h P t h0 h2) (fun h0 : @List.Forall A Q t => @lem1238429 A Q t h1 h0)). Qed.
Lemma lem1238437 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term77 A Q h) (h3 : term34 A h P t) (h4 : term9 A P Q t) : False.
Proof. exact (or_elim (@lem1238030 A P Q t h4) (fun h0 : term86 A P t => @lem1238435 A h P t h0 h3) (fun h0 : @List.Forall A Q t => @lem1238433 A Q h P t h1 h2 h3)). Qed.
Lemma lem1238438 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term70 A h Q t) (h3 : term34 A h P t) (h4 : term9 A P Q t) : False.
Proof. exact (or_elim (@lem1238068 A h Q t h2) (fun h0 : term77 A Q h => @lem1238437 A h P Q t h1 h0 h3 h4) (fun h0 : term86 A Q t => @lem1238436 A h P Q t h0 h3 h4)). Qed.
Lemma lem1238439 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term70 A h Q t) (h3 : term34 A h P t) (h4 : term9 A P Q t) : (term34 A h P t) = False.
Proof. exact (prop_ext (fun h5 : term34 A h P t => @lem1238438 A h P Q t h1 h2 h3 h4) (fun h5 : False => @lem1237977 A h P t h3)). Qed.
Lemma lem1238440 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term70 A h Q t) (h3 : term34 A h P t) (h4 : term9 A P Q t) : False.
Proof. exact (EQ_MP (@lem1238439 A h P Q t h1 h2 h3 h4) (@lem1237977 A h P t h3)). Qed.
Lemma lem1238441 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term70 A h Q t) (h3 : term34 A h P t) (h4 : term9 A P Q t) : (term70 A h Q t) = False.
Proof. exact (prop_ext (fun h5 : term70 A h Q t => @lem1238440 A h P Q t h1 h2 h3 h4) (fun h5 : False => @lem1237908 A h Q t h2)). Qed.
Lemma lem1238442 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term70 A h Q t) (h3 : term34 A h P t) (h4 : term9 A P Q t) : False.
Proof. exact (EQ_MP (@lem1238441 A h P Q t h1 h2 h3 h4) (@lem1237908 A h Q t h2)). Qed.
Lemma lem1238443 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term34 A h P t) (h3 : term9 A P Q t) : term69 A h Q t.
Proof. exact (fun h0 : term70 A h Q t => @lem1238442 A h P Q t h1 h0 h2 h3). Qed.
Lemma lem1238444 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term34 A h P t) (h3 : term9 A P Q t) : term34 A h Q t.
Proof. exact (EQ_MP (@lem1237907 A h Q t) (@lem1238443 A h P Q t h1 h2 h3)). Qed.
Lemma lem1238445 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term9 A P Q t) : term37 A P h Q t.
Proof. exact (fun h0 : term34 A h P t => @lem1238444 A h P Q t h1 h0 h2). Qed.
Lemma lem1238446 {A : Type'} (h : A) (t : list A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term48 A P h Q t.
Proof. exact (fun h0 : term9 A P Q t => @lem1238445 A h P Q t h1 h0). Qed.
Lemma lem1238447 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : term50 A P h Q t.
Proof. exact (fun h0 : term0 A P Q => @lem1238446 A h t P Q h0). Qed.
Lemma lem1238452 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : term54 A h Q t.
Proof. exact (fun P : A -> Prop => @lem1238447 A P h Q t). Qed.
Lemma lem1238457 {A : Type'} (Q : A -> Prop) (t : list A) : term58 A Q t.
Proof. exact (fun h : A => @lem1238452 A h Q t). Qed.
Lemma lem1238462 {A : Type'} (t : list A) : term62 A t.
Proof. exact (fun Q : A -> Prop => @lem1238457 A Q t). Qed.
Lemma lem1238467 {A : Type'} : term66 A.
Proof. exact (fun t : list A => @lem1238462 A t). Qed.
Lemma lem1238468 {A : Type'} : term65 A.
Proof. exact (EQ_MP (@lem1237900 A) (@lem1238467 A)). Qed.
Lemma lem1238469 {A : Type'} (t : list A) : term104 A t.
Proof. exact (@lem1238468 A t). Qed.
Lemma lem1238470 {A : Type'} (t : list A) : (term104 A t) = (term61 A t).
Proof. exact (eq_refl (term104 A t)). Qed.
Lemma lem1238471 {A : Type'} (t : list A) : term61 A t.
Proof. exact (EQ_MP (@lem1238470 A t) (@lem1238469 A t)). Qed.
Lemma lem1238472 {A : Type'} (t : list A) (Q : A -> Prop) : term105 A t Q.
Proof. exact (@lem1238471 A t Q). Qed.
Lemma lem1238473 {A : Type'} (Q : A -> Prop) (t : list A) : (term105 A t Q) = (term57 A Q t).
Proof. exact (eq_refl (term105 A t Q)). Qed.
Lemma lem1238474 {A : Type'} (Q : A -> Prop) (t : list A) : term57 A Q t.
Proof. exact (EQ_MP (@lem1238473 A Q t) (@lem1238472 A t Q)). Qed.
Lemma lem1238475 {A : Type'} (Q : A -> Prop) (t : list A) (h : A) : term106 A Q t h.
Proof. exact (@lem1238474 A Q t h). Qed.
Lemma lem1238476 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : (term106 A Q t h) = (term53 A h Q t).
Proof. exact (eq_refl (term106 A Q t h)). Qed.
Lemma lem1238477 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) : term53 A h Q t.
Proof. exact (EQ_MP (@lem1238476 A h Q t) (@lem1238475 A Q t h)). Qed.
Lemma lem1238478 {A : Type'} (h : A) (Q : A -> Prop) (t : list A) (P : A -> Prop) : term107 A h Q t P.
Proof. exact (@lem1238477 A h Q t P). Qed.
Lemma lem1238479 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : (term107 A h Q t P) = (term41 A P h Q t).
Proof. exact (eq_refl (term107 A h Q t P)). Qed.
Lemma lem1238480 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : term41 A P h Q t.
Proof. exact (EQ_MP (@lem1238479 A P h Q t) (@lem1238478 A h Q t P)). Qed.
Lemma lem1238482 {A : Type'} (P : A -> Prop) (h : A) (Q : A -> Prop) (t : list A) : term41 A P h Q t.
Proof. exact (@lem1237727 A P h Q t (@lem1238480 A P h Q t)). Qed.
Lemma lem1238483 {A : Type'} (h : A) (t : list A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term47 A P h Q t.
Proof. exact (@lem1238482 A P h Q t (@lem1237625 A P Q h1)). Qed.
Lemma lem1238484 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term9 A P Q t) : term39 A P h Q t.
Proof. exact (@lem1238483 A h t P Q h1 (@lem1237653 A P Q t h2)). Qed.
Lemma lem1238485 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term40 A P h Q t) (h3 : term9 A P Q t) : False.
Proof. exact (@lem1238484 A h P Q t h1 h3 (@lem1237711 A P h Q t h2)). Qed.
Lemma lem1238486 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term40 A P h Q t) (h3 : term9 A P Q t) : (term40 A P h Q t) = False.
Proof. exact (prop_ext (fun h4 : term40 A P h Q t => @lem1238485 A h P Q t h1 h2 h3) (fun h4 : False => @lem1237711 A P h Q t h2)). Qed.
Lemma lem1238487 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term40 A P h Q t) (h3 : term9 A P Q t) : False.
Proof. exact (EQ_MP (@lem1238486 A h P Q t h1 h2 h3) (@lem1237711 A P h Q t h2)). Qed.
Lemma lem1238488 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term9 A P Q t) : term39 A P h Q t.
Proof. exact (fun h0 : term40 A P h Q t => @lem1238487 A h P Q t h1 h0 h2). Qed.
Lemma lem1238489 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term9 A P Q t) : term37 A P h Q t.
Proof. exact (EQ_MP (@lem1237710 A P h Q t) (@lem1238488 A h P Q t h1 h2)). Qed.
Lemma lem1238490 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (t : list A) (h1 : term0 A P Q) (h2 : term9 A P Q t) : term13 A P Q h t.
Proof. exact (EQ_MP (@lem1237706 A P Q h t) (@lem1238489 A h P Q t h1 h2)). Qed.
Lemma lem1238491 {A : Type'} (h : A) (t : list A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term15 A P Q h t.
Proof. exact (fun h0 : term9 A P Q t => @lem1238490 A h P Q t h1 h0). Qed.
Lemma lem1238496 {A : Type'} (h : A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term19 A P Q h.
Proof. exact (fun t : list A => @lem1238491 A h t P Q h1). Qed.
Lemma lem1238501 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term23 A P Q.
Proof. exact (fun h : A => @lem1238496 A h P Q h1). Qed.
Lemma lem1238502 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term25 A P Q.
Proof. exact (conj (@lem1237678 A P Q) (@lem1238501 A P Q h1)). Qed.
Lemma lem1238503 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term30 A P Q.
Proof. exact (@lem1237652 A P Q (@lem1238502 A P Q h1)). Qed.
Lemma lem1238504 {A : Type'} (l : list A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term8 A P Q l.
Proof. exact (@lem1238503 A P Q h1 l). Qed.
Lemma lem1238505 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (l : list A) : (term8 A P Q l) = (term9 A P Q l).
Proof. exact (eq_refl (term8 A P Q l)). Qed.
Lemma lem1238506 {A : Type'} (l : list A) (P : A -> Prop) (Q : A -> Prop) (h1 : term0 A P Q) : term9 A P Q l.
Proof. exact (EQ_MP (@lem1238505 A P Q l) (@lem1238504 A l P Q h1)). Qed.
Lemma lem1238507 {A : Type'} (P : A -> Prop) (Q : A -> Prop) (l : list A) : term108 A P Q l.
Proof. exact (fun h0 : term0 A P Q => @lem1238506 A l P Q h0). Qed.
