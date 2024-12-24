Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import EX_MEM_term_abbrevs.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1101587_spec.
Require Import thm1101588_spec.
Require Import thm1101596_spec.
Require Import thm1101597_spec.
Require Import thm1103191_spec.
Require Import thm1103192_spec.
Require Import thm1103200_spec.
Require Import thm1103201_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm1812_spec.
Require Import thm1813_spec.
Require Import thm18394_spec.
Require Import thm1845_spec.
Require Import thm1857_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm19490_spec.
Require Import thm20661_spec.
Require Import thm20662_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Lemma lem1152677 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1152678 {_27094 : Type'} (P : type1143 _27094) : term0 _27094 P.
Proof. exact (@lem1152677 _27094 P). Qed.
Lemma lem1152679 {_27094 : Type'} (P : _27094 -> Prop) : term1 _27094 P.
Proof. exact (@lem1152678 _27094 (term2 _27094 P)). Qed.
Lemma lem1152680 {_27094 : Type'} (P : _27094 -> Prop) : (term3 _27094 P) = ((term4 _27094 P) = (@EX _27094 P (@nil _27094))).
Proof. exact (eq_refl (term3 _27094 P)). Qed.
Lemma lem1152681 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1152682 {_27094 : Type'} (P : _27094 -> Prop) : (term5 _27094 P) = (term6 _27094 P).
Proof. exact (MK_COMB (@lem1152681) (@lem1152680 _27094 P)). Qed.
Lemma lem1152683 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term7 _27094 P t) = ((term8 _27094 P t) = (@EX _27094 P t)).
Proof. exact (eq_refl (term7 _27094 P t)). Qed.
Lemma lem1152684 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1152685 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term9 _27094 P t) = (term10 _27094 P t).
Proof. exact (MK_COMB (@lem1152684) (@lem1152683 _27094 P t)). Qed.
Lemma lem1152686 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term11 _27094 P h t) = ((term12 _27094 P h t) = (term13 _27094 P h t)).
Proof. exact (eq_refl (term11 _27094 P h t)). Qed.
Lemma lem1152687 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term14 _27094 P h t) = (term15 _27094 P h t).
Proof. exact (MK_COMB (@lem1152685 _27094 P t) (@lem1152686 _27094 P h t)). Qed.
Lemma lem1152688 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term16 _27094 P h) = (term17 _27094 P h).
Proof. exact (fun_ext (fun t : list _27094 => @lem1152687 _27094 P h t)). Qed.
Lemma lem1152689 {_27094 : Type'} : (@all (list _27094)) = (@all (list _27094)).
Proof. exact (eq_refl (@all (list _27094))). Qed.
Lemma lem1152690 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term18 _27094 P h) = (term19 _27094 P h).
Proof. exact (MK_COMB (@lem1152689 _27094) (@lem1152688 _27094 P h)). Qed.
Lemma lem1152691 {_27094 : Type'} (P : _27094 -> Prop) : (term20 _27094 P) = (term21 _27094 P).
Proof. exact (fun_ext (fun h : _27094 => @lem1152690 _27094 P h)). Qed.
Lemma lem1152692 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1152693 {_27094 : Type'} (P : _27094 -> Prop) : (term22 _27094 P) = (term23 _27094 P).
Proof. exact (MK_COMB (@lem1152692 _27094) (@lem1152691 _27094 P)). Qed.
Lemma lem1152694 {_27094 : Type'} (P : _27094 -> Prop) : (term24 _27094 P) = (term25 _27094 P).
Proof. exact (MK_COMB (@lem1152682 _27094 P) (@lem1152693 _27094 P)). Qed.
Lemma lem1152695 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1152696 {_27094 : Type'} (P : _27094 -> Prop) : (term26 _27094 P) = (term27 _27094 P).
Proof. exact (MK_COMB (@lem1152695) (@lem1152694 _27094 P)). Qed.
Lemma lem1152697 {_27094 : Type'} (P : _27094 -> Prop) (l : list _27094) : (term7 _27094 P l) = ((term8 _27094 P l) = (@EX _27094 P l)).
Proof. exact (eq_refl (term7 _27094 P l)). Qed.
Lemma lem1152698 {_27094 : Type'} (P : _27094 -> Prop) : (term28 _27094 P) = (term2 _27094 P).
Proof. exact (fun_ext (fun l : list _27094 => @lem1152697 _27094 P l)). Qed.
Lemma lem1152699 {_27094 : Type'} : (@all (list _27094)) = (@all (list _27094)).
Proof. exact (eq_refl (@all (list _27094))). Qed.
Lemma lem1152700 {_27094 : Type'} (P : _27094 -> Prop) : (term29 _27094 P) = (term30 _27094 P).
Proof. exact (MK_COMB (@lem1152699 _27094) (@lem1152698 _27094 P)). Qed.
Lemma lem1152701 {_27094 : Type'} (P : _27094 -> Prop) : (term1 _27094 P) = (term31 _27094 P).
Proof. exact (MK_COMB (@lem1152696 _27094 P) (@lem1152700 _27094 P)). Qed.
Lemma lem1152702 {_27094 : Type'} (P : _27094 -> Prop) : term31 _27094 P.
Proof. exact (EQ_MP (@lem1152701 _27094 P) (@lem1152679 _27094 P)). Qed.
Lemma lem1152703 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : (term8 _27094 P t) = (@EX _27094 P t).
Proof. exact (h1). Qed.
Lemma lem1152717 {_25376 : Type'} (x : _25376) : (@List.In _25376 x (@nil _25376)) = False.
Proof. exact (EQ_MP (@lem1103192 _25376 x) (@lem1103191 _25376 x)). Qed.
Lemma lem1152718 {_27094 : Type'} (x : _27094) : (@List.In _27094 x (@nil _27094)) = False.
Proof. exact (@lem1152717 _27094 x). Qed.
Lemma lem1152719 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term32 _27094 P x) = (term32 _27094 P x).
Proof. exact (eq_refl (term32 _27094 P x)). Qed.
Lemma lem1152720 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term33 _27094 P x) = (term34 _27094 P x).
Proof. exact (MK_COMB (@lem1152719 _27094 P x) (@lem1152718 _27094 x)). Qed.
Lemma lem1152722 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1152723 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term34 _27094 P x) = False.
Proof. exact (@lem1152722 (P x)). Qed.
Lemma lem1152724 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term33 _27094 P x) = False.
Proof. exact (TRANS (@lem1152720 _27094 P x) (@lem1152723 _27094 P x)). Qed.
Lemma lem1152725 {_27094 : Type'} (P : _27094 -> Prop) : (term35 _27094 P) = (term36 _27094).
Proof. exact (fun_ext (fun x : _27094 => @lem1152724 _27094 P x)). Qed.
Lemma lem1152726 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1152727 {_27094 : Type'} (P : _27094 -> Prop) : (term4 _27094 P) = (term37 _27094).
Proof. exact (MK_COMB (@lem1152726 _27094) (@lem1152725 _27094 P)). Qed.
Lemma lem1152729 {A : Type'} (t : Prop) : (term38 A t) = t.
Proof. exact (EQ_MP (@lem1813 A t) (@lem1812 A t)). Qed.
Lemma lem1152730 {_27094 : Type'} (t : Prop) : (term38 _27094 t) = t.
Proof. exact (@lem1152729 _27094 t). Qed.
Lemma lem1152731 {_27094 : Type'} : (term37 _27094) = False.
Proof. exact (@lem1152730 _27094 False). Qed.
Lemma lem1152732 {_27094 : Type'} (P : _27094 -> Prop) : (term4 _27094 P) = False.
Proof. exact (TRANS (@lem1152727 _27094 P) (@lem1152731 _27094)). Qed.
Lemma lem1152733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1152734 {_27094 : Type'} (P : _27094 -> Prop) : (term39 _27094 P) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1152733) (@lem1152732 _27094 P)). Qed.
Lemma lem1152736 {_25328 : Type'} (P : _25328 -> Prop) : (@EX _25328 P (@nil _25328)) = False.
Proof. exact (EQ_MP (@lem1101588 _25328 P) (@lem1101587 _25328 P)). Qed.
Lemma lem1152737 {_27094 : Type'} (P : _27094 -> Prop) : (@EX _27094 P (@nil _27094)) = False.
Proof. exact (@lem1152736 _27094 P). Qed.
Lemma lem1152738 {_27094 : Type'} (P : _27094 -> Prop) : ((term4 _27094 P) = (@EX _27094 P (@nil _27094))) = (False = False).
Proof. exact (MK_COMB (@lem1152734 _27094 P) (@lem1152737 _27094 P)). Qed.
Lemma lem1152740 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1152741 : (False = False) = (~ False).
Proof. exact (@lem1152740 False). Qed.
Lemma lem1152743 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1152744 : (False = False) = True.
Proof. exact (TRANS (@lem1152741) (@lem1152743)). Qed.
Lemma lem1152745 {_27094 : Type'} (P : _27094 -> Prop) : ((term4 _27094 P) = (@EX _27094 P (@nil _27094))) = True.
Proof. exact (TRANS (@lem1152738 _27094 P) (@lem1152744)). Qed.
Lemma lem1152746 {_27094 : Type'} (P : _27094 -> Prop) : True = ((term4 _27094 P) = (@EX _27094 P (@nil _27094))).
Proof. exact (SYM (@lem1152745 _27094 P)). Qed.
Lemma lem1152747 {_27094 : Type'} (P : _27094 -> Prop) : (term4 _27094 P) = (@EX _27094 P (@nil _27094)).
Proof. exact (EQ_MP (@lem1152746 _27094 P) (@lem0)). Qed.
Lemma lem1152761 {_25376 : Type'} (h : _25376) (x : _25376) (t : list _25376) : (term40 _25376 x h t) = (term41 _25376 h x t).
Proof. exact (EQ_MP (@lem1103201 _25376 h x t) (@lem1103200 _25376 h x t)). Qed.
Lemma lem1152762 {_27094 : Type'} (h : _27094) (x : _27094) (t : list _27094) : (term40 _27094 x h t) = (term41 _27094 h x t).
Proof. exact (@lem1152761 _27094 h x t). Qed.
Lemma lem1152767 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term32 _27094 P x) = (term32 _27094 P x).
Proof. exact (eq_refl (term32 _27094 P x)). Qed.
Lemma lem1152768 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term42 _27094 P x h t) = (term43 _27094 P h x t).
Proof. exact (MK_COMB (@lem1152767 _27094 P x) (@lem1152762 _27094 h x t)). Qed.
Lemma lem1152771 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term44 _27094 P h t) = (term45 _27094 P h t).
Proof. exact (fun_ext (fun x : _27094 => @lem1152768 _27094 P h x t)). Qed.
Lemma lem1152772 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1152773 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term12 _27094 P h t) = (term46 _27094 P h t).
Proof. exact (MK_COMB (@lem1152772 _27094) (@lem1152771 _27094 P h t)). Qed.
Lemma lem1152778 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1152779 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term47 _27094 P h t) = (term48 _27094 P h t).
Proof. exact (MK_COMB (@lem1152778) (@lem1152773 _27094 P h t)). Qed.
Lemma lem1152781 {_25328 : Type'} (h : _25328) (P : _25328 -> Prop) (t : list _25328) : (term13 _25328 P h t) = (term49 _25328 h P t).
Proof. exact (EQ_MP (@lem1101597 _25328 h P t) (@lem1101596 _25328 h P t)). Qed.
Lemma lem1152782 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term13 _27094 P h t) = (term49 _27094 h P t).
Proof. exact (@lem1152781 _27094 h P t). Qed.
Lemma lem1152785 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : ((term12 _27094 P h t) = (term13 _27094 P h t)) = ((term46 _27094 P h t) = (term49 _27094 h P t)).
Proof. exact (MK_COMB (@lem1152779 _27094 P h t) (@lem1152782 _27094 h P t)). Qed.
Lemma lem1152788 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : ((term46 _27094 P h t) = (term49 _27094 h P t)) = ((term12 _27094 P h t) = (term13 _27094 P h t)).
Proof. exact (SYM (@lem1152785 _27094 h P t)). Qed.
Lemma lem1152790 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1152791 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : ((term46 _27094 P h t) = (term49 _27094 h P t)) = (term51 _27094 h P t).
Proof. exact (@lem1152790 ((term46 _27094 P h t) = (term49 _27094 h P t))). Qed.
Lemma lem1152792 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term51 _27094 h P t) = ((term46 _27094 P h t) = (term49 _27094 h P t)).
Proof. exact (SYM (@lem1152791 _27094 h P t)). Qed.
Lemma lem1152793 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) : term52 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1152796 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term53 _27094 h P t) : term53 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1152797 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : term54 _27094 h P t.
Proof. exact (fun h0 : term53 _27094 h P t => @lem1152796 _27094 h P t h0). Qed.
Lemma lem1152798 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term54 _27094 h P t) : term54 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1152799 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term53 _27094 h P t) : term53 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1152800 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term53 _27094 h P t) (h2 : term54 _27094 h P t) : term53 _27094 h P t.
Proof. exact (@lem1152798 _27094 h P t h2 (@lem1152799 _27094 h P t h1)). Qed.
Lemma lem1152801 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term53 _27094 h P t) : term55 _27094 h P t.
Proof. exact (fun h0 : term54 _27094 h P t => @lem1152800 _27094 h P t h1 h0). Qed.
Lemma lem1152802 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term54 _27094 h P t) : term54 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1152803 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term53 _27094 h P t) (h2 : term54 _27094 h P t) : term53 _27094 h P t.
Proof. exact (@lem1152801 _27094 h P t h1 (@lem1152802 _27094 h P t h2)). Qed.
Lemma lem1152804 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term54 _27094 h P t) : term54 _27094 h P t.
Proof. exact (fun h0 : term53 _27094 h P t => @lem1152803 _27094 h P t h0 h1). Qed.
Lemma lem1152805 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : term56 _27094 h P t.
Proof. exact (fun h0 : term54 _27094 h P t => @lem1152804 _27094 h P t h0). Qed.
Lemma lem1152808 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : term54 _27094 h P t.
Proof. exact (@lem1152805 _27094 h P t (@lem1152797 _27094 h P t)). Qed.
Lemma lem1152809 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : term54 _27094 h P t.
Proof. exact (@lem1152808 _27094 h P t). Qed.
Lemma lem1152855 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem1152856 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term51 _27094 h P t) = (term57 _27094 h P t).
Proof. exact (@lem1152855 (term52 _27094 h P t)). Qed.
Lemma lem1152858 (t : Prop) : (term58 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem1152859 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term57 _27094 h P t) = ((term46 _27094 P h t) = (term49 _27094 h P t)).
Proof. exact (@lem1152858 ((term46 _27094 P h t) = (term49 _27094 h P t))). Qed.
Lemma lem1152860 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term51 _27094 h P t) = ((term46 _27094 P h t) = (term49 _27094 h P t)).
Proof. exact (TRANS (@lem1152856 _27094 h P t) (@lem1152859 _27094 h P t)). Qed.
Lemma lem1152895 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term10 _27094 P t) = (term10 _27094 P t).
Proof. exact (eq_refl (term10 _27094 P t)). Qed.
Lemma lem1152896 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term53 _27094 h P t) = (term59 _27094 h P t).
Proof. exact (MK_COMB (@lem1152895 _27094 P t) (@lem1152860 _27094 h P t)). Qed.
Lemma lem1152899 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term60 _27094 P t) = (term61 _27094 P t).
Proof. exact (fun_ext (fun h : _27094 => @lem1152896 _27094 h P t)). Qed.
Lemma lem1152900 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1152901 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term62 _27094 P t) = (term63 _27094 P t).
Proof. exact (MK_COMB (@lem1152900 _27094) (@lem1152899 _27094 P t)). Qed.
Lemma lem1152906 {_27094 : Type'} (t : list _27094) : (term64 _27094 t) = (term65 _27094 t).
Proof. exact (fun_ext (fun P : _27094 -> Prop => @lem1152901 _27094 P t)). Qed.
Lemma lem1152907 {_27094 : Type'} : (@all (_27094 -> Prop)) = (@all (_27094 -> Prop)).
Proof. exact (eq_refl (@all (_27094 -> Prop))). Qed.
Lemma lem1152908 {_27094 : Type'} (t : list _27094) : (term66 _27094 t) = (term67 _27094 t).
Proof. exact (MK_COMB (@lem1152907 _27094) (@lem1152906 _27094 t)). Qed.
Lemma lem1152913 {_27094 : Type'} : (term68 _27094) = (term69 _27094).
Proof. exact (fun_ext (fun t : list _27094 => @lem1152908 _27094 t)). Qed.
Lemma lem1152914 {_27094 : Type'} : (@all (list _27094)) = (@all (list _27094)).
Proof. exact (eq_refl (@all (list _27094))). Qed.
Lemma lem1152923 {_27094 : Type'} : (term70 _27094) = (term71 _27094).
Proof. exact (MK_COMB (@lem1152914 _27094) (@lem1152913 _27094)). Qed.
Lemma lem1152928 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term49 _27094 h P t) = (term49 _27094 h P t).
Proof. exact (eq_refl (term49 _27094 h P t)). Qed.
Lemma lem1152937 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term43 _27094 P h x t) = (term43 _27094 P h x t).
Proof. exact (eq_refl (term43 _27094 P h x t)). Qed.
Lemma lem1152938 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term45 _27094 P h t) = (term45 _27094 P h t).
Proof. exact (fun_ext (fun x : _27094 => @lem1152937 _27094 P h x t)). Qed.
Lemma lem1152939 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1152940 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term46 _27094 P h t) = (term46 _27094 P h t).
Proof. exact (MK_COMB (@lem1152939 _27094) (@lem1152938 _27094 P h t)). Qed.
Lemma lem1152941 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1152942 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term48 _27094 P h t) = (term48 _27094 P h t).
Proof. exact (MK_COMB (@lem1152941) (@lem1152940 _27094 P h t)). Qed.
Lemma lem1152943 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : ((term46 _27094 P h t) = (term49 _27094 h P t)) = ((term46 _27094 P h t) = (term49 _27094 h P t)).
Proof. exact (MK_COMB (@lem1152942 _27094 P h t) (@lem1152928 _27094 h P t)). Qed.
Lemma lem1152944 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (@EX _27094 P t) = (@EX _27094 P t).
Proof. exact (eq_refl (@EX _27094 P t)). Qed.
Lemma lem1152949 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term72 _27094 P x t) = (term72 _27094 P x t).
Proof. exact (eq_refl (term72 _27094 P x t)). Qed.
Lemma lem1152950 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term73 _27094 P t) = (term73 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1152949 _27094 P x t)). Qed.
Lemma lem1152951 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1152952 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term8 _27094 P t) = (term8 _27094 P t).
Proof. exact (MK_COMB (@lem1152951 _27094) (@lem1152950 _27094 P t)). Qed.
Lemma lem1152953 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1152954 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term74 _27094 P t) = (term74 _27094 P t).
Proof. exact (MK_COMB (@lem1152953) (@lem1152952 _27094 P t)). Qed.
Lemma lem1152955 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : ((term8 _27094 P t) = (@EX _27094 P t)) = ((term8 _27094 P t) = (@EX _27094 P t)).
Proof. exact (MK_COMB (@lem1152954 _27094 P t) (@lem1152944 _27094 P t)). Qed.
Lemma lem1152956 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1152957 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term10 _27094 P t) = (term10 _27094 P t).
Proof. exact (MK_COMB (@lem1152956) (@lem1152955 _27094 P t)). Qed.
Lemma lem1152958 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term59 _27094 h P t) = (term59 _27094 h P t).
Proof. exact (MK_COMB (@lem1152957 _27094 P t) (@lem1152943 _27094 h P t)). Qed.
Lemma lem1152959 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term61 _27094 P t) = (term61 _27094 P t).
Proof. exact (fun_ext (fun h : _27094 => @lem1152958 _27094 h P t)). Qed.
Lemma lem1152960 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1152961 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term63 _27094 P t) = (term63 _27094 P t).
Proof. exact (MK_COMB (@lem1152960 _27094) (@lem1152959 _27094 P t)). Qed.
Lemma lem1152962 {_27094 : Type'} (t : list _27094) : (term65 _27094 t) = (term65 _27094 t).
Proof. exact (fun_ext (fun P : _27094 -> Prop => @lem1152961 _27094 P t)). Qed.
Lemma lem1152963 {_27094 : Type'} : (@all (_27094 -> Prop)) = (@all (_27094 -> Prop)).
Proof. exact (eq_refl (@all (_27094 -> Prop))). Qed.
Lemma lem1152964 {_27094 : Type'} (t : list _27094) : (term67 _27094 t) = (term67 _27094 t).
Proof. exact (MK_COMB (@lem1152963 _27094) (@lem1152962 _27094 t)). Qed.
Lemma lem1152965 {_27094 : Type'} : (term69 _27094) = (term69 _27094).
Proof. exact (fun_ext (fun t : list _27094 => @lem1152964 _27094 t)). Qed.
Lemma lem1152966 {_27094 : Type'} : (@all (list _27094)) = (@all (list _27094)).
Proof. exact (eq_refl (@all (list _27094))). Qed.
Lemma lem1152967 {_27094 : Type'} : (term71 _27094) = (term71 _27094).
Proof. exact (MK_COMB (@lem1152966 _27094) (@lem1152965 _27094)). Qed.
Lemma lem1153010 {_27094 : Type'} : (term70 _27094) = (term71 _27094).
Proof. exact (TRANS (@lem1152923 _27094) (@lem1152967 _27094)). Qed.
Lemma lem1153011 {_27094 : Type'} : (term71 _27094) = (term70 _27094).
Proof. exact (SYM (@lem1153010 _27094)). Qed.
Lemma lem1153012 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : (term8 _27094 P t) = (@EX _27094 P t).
Proof. exact (h1). Qed.
Lemma lem1153014 (p : Prop) : p = (term50 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem1153015 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : ((term46 _27094 P h t) = (term49 _27094 h P t)) = (term51 _27094 h P t).
Proof. exact (@lem1153014 ((term46 _27094 P h t) = (term49 _27094 h P t))). Qed.
Lemma lem1153016 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term51 _27094 h P t) = ((term46 _27094 P h t) = (term49 _27094 h P t)).
Proof. exact (SYM (@lem1153015 _27094 h P t)). Qed.
Lemma lem1153017 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) : term52 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1153026 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term75 _27094 P x t) = (term76 _27094 P x t).
Proof. exact (@lem17045 (P x) (@List.In _27094 x t)). Qed.
Lemma lem1153029 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term72 _27094 P x t) = (term72 _27094 P x t).
Proof. exact (eq_refl (term72 _27094 P x t)). Qed.
Lemma lem1153030 {_27094 : Type'} (P : _27094 -> Prop) : (term77 _27094 P) = (term78 _27094 P).
Proof. exact (@lem18394 _27094 P). Qed.
Lemma lem1153031 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term79 _27094 P t) = (term80 _27094 P t).
Proof. exact (@lem1153030 _27094 (term73 _27094 P t)). Qed.
Lemma lem1153032 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term81 _27094 P t x) = (term72 _27094 P x t).
Proof. exact (eq_refl (term81 _27094 P t x)). Qed.
Lemma lem1153033 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1153034 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term82 _27094 P t x) = (term75 _27094 P x t).
Proof. exact (MK_COMB (@lem1153033) (@lem1153032 _27094 P x t)). Qed.
Lemma lem1153035 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term82 _27094 P t x) = (term76 _27094 P x t).
Proof. exact (TRANS (@lem1153034 _27094 P x t) (@lem1153026 _27094 P x t)). Qed.
Lemma lem1153036 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term83 _27094 P t) = (term84 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153035 _27094 P x t)). Qed.
Lemma lem1153037 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153038 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term80 _27094 P t) = (term85 _27094 P t).
Proof. exact (MK_COMB (@lem1153037 _27094) (@lem1153036 _27094 P t)). Qed.
Lemma lem1153039 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term79 _27094 P t) = (term85 _27094 P t).
Proof. exact (TRANS (@lem1153031 _27094 P t) (@lem1153038 _27094 P t)). Qed.
Lemma lem1153040 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term73 _27094 P t) = (term73 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153029 _27094 P x t)). Qed.
Lemma lem1153041 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153042 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term8 _27094 P t) = (term8 _27094 P t).
Proof. exact (MK_COMB (@lem1153041 _27094) (@lem1153040 _27094 P t)). Qed.
Lemma lem1153043 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term86 _27094 P t) = (term86 _27094 P t).
Proof. exact (eq_refl (term86 _27094 P t)). Qed.
Lemma lem1153044 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (@EX _27094 P t) = (@EX _27094 P t).
Proof. exact (eq_refl (@EX _27094 P t)). Qed.
Lemma lem1153045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153046 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term87 _27094 P t) = (term88 _27094 P t).
Proof. exact (MK_COMB (@lem1153045) (@lem1153039 _27094 P t)). Qed.
Lemma lem1153047 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term89 _27094 P t) = (term90 _27094 P t).
Proof. exact (MK_COMB (@lem1153046 _27094 P t) (@lem1153043 _27094 P t)). Qed.
Lemma lem1153048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153049 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term91 _27094 P t) = (term91 _27094 P t).
Proof. exact (MK_COMB (@lem1153048) (@lem1153042 _27094 P t)). Qed.
Lemma lem1153050 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term92 _27094 P t) = (term92 _27094 P t).
Proof. exact (MK_COMB (@lem1153049 _27094 P t) (@lem1153044 _27094 P t)). Qed.
Lemma lem1153051 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153052 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term93 _27094 P t) = (term93 _27094 P t).
Proof. exact (MK_COMB (@lem1153051) (@lem1153050 _27094 P t)). Qed.
Lemma lem1153053 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term94 _27094 P t) = (term95 _27094 P t).
Proof. exact (MK_COMB (@lem1153052 _27094 P t) (@lem1153047 _27094 P t)). Qed.
Lemma lem1153054 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : ((term8 _27094 P t) = (@EX _27094 P t)) = (term94 _27094 P t).
Proof. exact (@lem17500 (term8 _27094 P t) (@EX _27094 P t)). Qed.
Lemma lem1153055 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : ((term8 _27094 P t) = (@EX _27094 P t)) = (term95 _27094 P t).
Proof. exact (TRANS (@lem1153054 _27094 P t) (@lem1153053 _27094 P t)). Qed.
Lemma lem1153134 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1153135 {_27094 : Type'} (P : _27094 -> Prop) (Q : Prop) : (term96 _27094 P Q) = (term97 _27094 P Q).
Proof. exact (@lem1153134 _27094 P Q). Qed.
Lemma lem1153136 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term98 _27094 P t) = (term99 _27094 P t).
Proof. exact (@lem1153135 _27094 (term73 _27094 P t) (@EX _27094 P t)). Qed.
Lemma lem1153137 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term81 _27094 P t x) = (term72 _27094 P x t).
Proof. exact (eq_refl (term81 _27094 P t x)). Qed.
Lemma lem1153138 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term100 _27094 P t) = (term73 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153137 _27094 P x t)). Qed.
Lemma lem1153139 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153140 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term101 _27094 P t) = (term8 _27094 P t).
Proof. exact (MK_COMB (@lem1153139 _27094) (@lem1153138 _27094 P t)). Qed.
Lemma lem1153141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153142 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term102 _27094 P t) = (term91 _27094 P t).
Proof. exact (MK_COMB (@lem1153141) (@lem1153140 _27094 P t)). Qed.
Lemma lem1153143 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (@EX _27094 P t) = (@EX _27094 P t).
Proof. exact (eq_refl (@EX _27094 P t)). Qed.
Lemma lem1153144 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term98 _27094 P t) = (term92 _27094 P t).
Proof. exact (MK_COMB (@lem1153142 _27094 P t) (@lem1153143 _27094 P t)). Qed.
Lemma lem1153145 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1153146 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term103 _27094 P t) = (term104 _27094 P t).
Proof. exact (MK_COMB (@lem1153145) (@lem1153144 _27094 P t)). Qed.
Lemma lem1153147 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term81 _27094 P t x) = (term72 _27094 P x t).
Proof. exact (eq_refl (term81 _27094 P t x)). Qed.
Lemma lem1153148 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153149 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term105 _27094 P t x) = (term106 _27094 P x t).
Proof. exact (MK_COMB (@lem1153148) (@lem1153147 _27094 P x t)). Qed.
Lemma lem1153150 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (@EX _27094 P t) = (@EX _27094 P t).
Proof. exact (eq_refl (@EX _27094 P t)). Qed.
Lemma lem1153151 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (t : list _27094) : (term107 _27094 x P t) = (term108 _27094 x P t).
Proof. exact (MK_COMB (@lem1153149 _27094 P x t) (@lem1153150 _27094 P t)). Qed.
Lemma lem1153152 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term109 _27094 P t) = (term110 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153151 _27094 x P t)). Qed.
Lemma lem1153153 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153154 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term99 _27094 P t) = (term111 _27094 P t).
Proof. exact (MK_COMB (@lem1153153 _27094) (@lem1153152 _27094 P t)). Qed.
Lemma lem1153155 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : ((term98 _27094 P t) = (term99 _27094 P t)) = ((term92 _27094 P t) = (term111 _27094 P t)).
Proof. exact (MK_COMB (@lem1153146 _27094 P t) (@lem1153154 _27094 P t)). Qed.
Lemma lem1153156 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term92 _27094 P t) = (term111 _27094 P t).
Proof. exact (EQ_MP (@lem1153155 _27094 P t) (@lem1153136 _27094 P t)). Qed.
Lemma lem1153157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153158 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term93 _27094 P t) = (term112 _27094 P t).
Proof. exact (MK_COMB (@lem1153157) (@lem1153156 _27094 P t)). Qed.
Lemma lem1153159 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term90 _27094 P t) = (term90 _27094 P t).
Proof. exact (eq_refl (term90 _27094 P t)). Qed.
Lemma lem1153160 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term95 _27094 P t) = (term113 _27094 P t).
Proof. exact (MK_COMB (@lem1153158 _27094 P t) (@lem1153159 _27094 P t)). Qed.
Lemma lem1153162 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1153163 {_27094 : Type'} (P : _27094 -> Prop) (Q : Prop) : (term114 _27094 P Q) = (term115 _27094 P Q).
Proof. exact (@lem1153162 _27094 P Q). Qed.
Lemma lem1153164 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term116 _27094 P t) = (term117 _27094 P t).
Proof. exact (@lem1153163 _27094 (term110 _27094 P t) (term90 _27094 P t)). Qed.
Lemma lem1153165 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (t : list _27094) : (term118 _27094 P t x) = (term108 _27094 x P t).
Proof. exact (eq_refl (term118 _27094 P t x)). Qed.
Lemma lem1153166 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term119 _27094 P t) = (term110 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153165 _27094 x P t)). Qed.
Lemma lem1153167 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153168 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term120 _27094 P t) = (term111 _27094 P t).
Proof. exact (MK_COMB (@lem1153167 _27094) (@lem1153166 _27094 P t)). Qed.
Lemma lem1153169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153170 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term121 _27094 P t) = (term112 _27094 P t).
Proof. exact (MK_COMB (@lem1153169) (@lem1153168 _27094 P t)). Qed.
Lemma lem1153171 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term90 _27094 P t) = (term90 _27094 P t).
Proof. exact (eq_refl (term90 _27094 P t)). Qed.
Lemma lem1153172 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term116 _27094 P t) = (term113 _27094 P t).
Proof. exact (MK_COMB (@lem1153170 _27094 P t) (@lem1153171 _27094 P t)). Qed.
Lemma lem1153173 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1153174 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term122 _27094 P t) = (term123 _27094 P t).
Proof. exact (MK_COMB (@lem1153173) (@lem1153172 _27094 P t)). Qed.
Lemma lem1153175 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (t : list _27094) : (term118 _27094 P t x) = (term108 _27094 x P t).
Proof. exact (eq_refl (term118 _27094 P t x)). Qed.
Lemma lem1153176 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153177 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (t : list _27094) : (term124 _27094 P t x) = (term125 _27094 x P t).
Proof. exact (MK_COMB (@lem1153176) (@lem1153175 _27094 x P t)). Qed.
Lemma lem1153178 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term90 _27094 P t) = (term90 _27094 P t).
Proof. exact (eq_refl (term90 _27094 P t)). Qed.
Lemma lem1153179 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (t : list _27094) : (term126 _27094 x P t) = (term127 _27094 x P t).
Proof. exact (MK_COMB (@lem1153177 _27094 x P t) (@lem1153178 _27094 P t)). Qed.
Lemma lem1153180 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term128 _27094 P t) = (term129 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153179 _27094 x P t)). Qed.
Lemma lem1153181 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153182 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term117 _27094 P t) = (term130 _27094 P t).
Proof. exact (MK_COMB (@lem1153181 _27094) (@lem1153180 _27094 P t)). Qed.
Lemma lem1153183 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : ((term116 _27094 P t) = (term117 _27094 P t)) = ((term113 _27094 P t) = (term130 _27094 P t)).
Proof. exact (MK_COMB (@lem1153174 _27094 P t) (@lem1153182 _27094 P t)). Qed.
Lemma lem1153184 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term113 _27094 P t) = (term130 _27094 P t).
Proof. exact (EQ_MP (@lem1153183 _27094 P t) (@lem1153164 _27094 P t)). Qed.
Lemma lem1153186 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term95 _27094 P t) = (term130 _27094 P t).
Proof. exact (TRANS (@lem1153160 _27094 P t) (@lem1153184 _27094 P t)). Qed.
Lemma lem1153187 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : ((term8 _27094 P t) = (@EX _27094 P t)) = (term130 _27094 P t).
Proof. exact (TRANS (@lem1153055 _27094 P t) (@lem1153186 _27094 P t)). Qed.
Lemma lem1153188 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : term130 _27094 P t.
Proof. exact (EQ_MP (@lem1153187 _27094 P t) (@lem1153012 _27094 P t h1)). Qed.
Lemma lem1153199 {_27094 : Type'} (h : _27094) (x : _27094) (t : list _27094) : (term131 _27094 h x t) = (term132 _27094 h x t).
Proof. exact (@lem17160 (x = h) (@List.In _27094 x t)). Qed.
Lemma lem1153204 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term133 _27094 P x) = (term133 _27094 P x).
Proof. exact (eq_refl (term133 _27094 P x)). Qed.
Lemma lem1153205 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term134 _27094 P h x t) = (term135 _27094 P h x t).
Proof. exact (MK_COMB (@lem1153204 _27094 P x) (@lem1153199 _27094 h x t)). Qed.
Lemma lem1153206 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term136 _27094 P h x t) = (term134 _27094 P h x t).
Proof. exact (@lem17045 (P x) (term41 _27094 h x t)). Qed.
Lemma lem1153207 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term136 _27094 P h x t) = (term135 _27094 P h x t).
Proof. exact (TRANS (@lem1153206 _27094 P h x t) (@lem1153205 _27094 P h x t)). Qed.
Lemma lem1153210 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term43 _27094 P h x t) = (term43 _27094 P h x t).
Proof. exact (eq_refl (term43 _27094 P h x t)). Qed.
Lemma lem1153211 {_27094 : Type'} (P : _27094 -> Prop) : (term77 _27094 P) = (term78 _27094 P).
Proof. exact (@lem18394 _27094 P). Qed.
Lemma lem1153212 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term137 _27094 P h t) = (term138 _27094 P h t).
Proof. exact (@lem1153211 _27094 (term45 _27094 P h t)). Qed.
Lemma lem1153213 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term139 _27094 P h t x) = (term43 _27094 P h x t).
Proof. exact (eq_refl (term139 _27094 P h t x)). Qed.
Lemma lem1153214 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1153215 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term140 _27094 P h t x) = (term136 _27094 P h x t).
Proof. exact (MK_COMB (@lem1153214) (@lem1153213 _27094 P h x t)). Qed.
Lemma lem1153216 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term140 _27094 P h t x) = (term135 _27094 P h x t).
Proof. exact (TRANS (@lem1153215 _27094 P h x t) (@lem1153207 _27094 P h x t)). Qed.
Lemma lem1153217 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term141 _27094 P h t) = (term142 _27094 P h t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153216 _27094 P h x t)). Qed.
Lemma lem1153218 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153219 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term138 _27094 P h t) = (term143 _27094 P h t).
Proof. exact (MK_COMB (@lem1153218 _27094) (@lem1153217 _27094 P h t)). Qed.
Lemma lem1153220 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term137 _27094 P h t) = (term143 _27094 P h t).
Proof. exact (TRANS (@lem1153212 _27094 P h t) (@lem1153219 _27094 P h t)). Qed.
Lemma lem1153221 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term45 _27094 P h t) = (term45 _27094 P h t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153210 _27094 P h x t)). Qed.
Lemma lem1153222 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153223 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term46 _27094 P h t) = (term46 _27094 P h t).
Proof. exact (MK_COMB (@lem1153222 _27094) (@lem1153221 _27094 P h t)). Qed.
Lemma lem1153232 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term144 _27094 h P t) = (term145 _27094 h P t).
Proof. exact (@lem17160 (P h) (@EX _27094 P t)). Qed.
Lemma lem1153235 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term49 _27094 h P t) = (term49 _27094 h P t).
Proof. exact (eq_refl (term49 _27094 h P t)). Qed.
Lemma lem1153236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153237 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term146 _27094 P h t) = (term147 _27094 P h t).
Proof. exact (MK_COMB (@lem1153236) (@lem1153220 _27094 P h t)). Qed.
Lemma lem1153238 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term148 _27094 h P t) = (term149 _27094 h P t).
Proof. exact (MK_COMB (@lem1153237 _27094 P h t) (@lem1153235 _27094 h P t)). Qed.
Lemma lem1153239 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153240 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term150 _27094 P h t) = (term150 _27094 P h t).
Proof. exact (MK_COMB (@lem1153239) (@lem1153223 _27094 P h t)). Qed.
Lemma lem1153241 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term151 _27094 h P t) = (term152 _27094 h P t).
Proof. exact (MK_COMB (@lem1153240 _27094 P h t) (@lem1153232 _27094 h P t)). Qed.
Lemma lem1153242 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153243 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term153 _27094 h P t) = (term154 _27094 h P t).
Proof. exact (MK_COMB (@lem1153242) (@lem1153241 _27094 h P t)). Qed.
Lemma lem1153244 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term155 _27094 h P t) = (term156 _27094 h P t).
Proof. exact (MK_COMB (@lem1153243 _27094 h P t) (@lem1153238 _27094 h P t)). Qed.
Lemma lem1153245 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term52 _27094 h P t) = (term155 _27094 h P t).
Proof. exact (@lem17646 (term46 _27094 P h t) (term49 _27094 h P t)). Qed.
Lemma lem1153246 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term52 _27094 h P t) = (term156 _27094 h P t).
Proof. exact (TRANS (@lem1153245 _27094 h P t) (@lem1153244 _27094 h P t)). Qed.
Lemma lem1153325 {A : Type'} (P : A -> Prop) (Q : Prop) : (term96 A P Q) = (term97 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem1153326 {_27094 : Type'} (P : _27094 -> Prop) (Q : Prop) : (term96 _27094 P Q) = (term97 _27094 P Q).
Proof. exact (@lem1153325 _27094 P Q). Qed.
Lemma lem1153327 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term157 _27094 h P t) = (term158 _27094 h P t).
Proof. exact (@lem1153326 _27094 (term45 _27094 P h t) (term145 _27094 h P t)). Qed.
Lemma lem1153328 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term139 _27094 P h t x) = (term43 _27094 P h x t).
Proof. exact (eq_refl (term139 _27094 P h t x)). Qed.
Lemma lem1153329 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term159 _27094 P h t) = (term45 _27094 P h t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153328 _27094 P h x t)). Qed.
Lemma lem1153330 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153331 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term160 _27094 P h t) = (term46 _27094 P h t).
Proof. exact (MK_COMB (@lem1153330 _27094) (@lem1153329 _27094 P h t)). Qed.
Lemma lem1153332 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153333 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term161 _27094 P h t) = (term150 _27094 P h t).
Proof. exact (MK_COMB (@lem1153332) (@lem1153331 _27094 P h t)). Qed.
Lemma lem1153334 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term145 _27094 h P t) = (term145 _27094 h P t).
Proof. exact (eq_refl (term145 _27094 h P t)). Qed.
Lemma lem1153335 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term157 _27094 h P t) = (term152 _27094 h P t).
Proof. exact (MK_COMB (@lem1153333 _27094 P h t) (@lem1153334 _27094 h P t)). Qed.
Lemma lem1153336 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1153337 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term162 _27094 h P t) = (term163 _27094 h P t).
Proof. exact (MK_COMB (@lem1153336) (@lem1153335 _27094 h P t)). Qed.
Lemma lem1153338 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term139 _27094 P h t x) = (term43 _27094 P h x t).
Proof. exact (eq_refl (term139 _27094 P h t x)). Qed.
Lemma lem1153339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153340 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term164 _27094 P h t x) = (term165 _27094 P h x t).
Proof. exact (MK_COMB (@lem1153339) (@lem1153338 _27094 P h x t)). Qed.
Lemma lem1153341 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term145 _27094 h P t) = (term145 _27094 h P t).
Proof. exact (eq_refl (term145 _27094 h P t)). Qed.
Lemma lem1153342 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term166 _27094 x h P t) = (term167 _27094 x h P t).
Proof. exact (MK_COMB (@lem1153340 _27094 P h x t) (@lem1153341 _27094 h P t)). Qed.
Lemma lem1153343 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term168 _27094 h P t) = (term169 _27094 h P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153342 _27094 x h P t)). Qed.
Lemma lem1153344 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153345 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term158 _27094 h P t) = (term170 _27094 h P t).
Proof. exact (MK_COMB (@lem1153344 _27094) (@lem1153343 _27094 h P t)). Qed.
Lemma lem1153346 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : ((term157 _27094 h P t) = (term158 _27094 h P t)) = ((term152 _27094 h P t) = (term170 _27094 h P t)).
Proof. exact (MK_COMB (@lem1153337 _27094 h P t) (@lem1153345 _27094 h P t)). Qed.
Lemma lem1153347 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term152 _27094 h P t) = (term170 _27094 h P t).
Proof. exact (EQ_MP (@lem1153346 _27094 h P t) (@lem1153327 _27094 h P t)). Qed.
Lemma lem1153348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153349 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term154 _27094 h P t) = (term171 _27094 h P t).
Proof. exact (MK_COMB (@lem1153348) (@lem1153347 _27094 h P t)). Qed.
Lemma lem1153350 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term149 _27094 h P t) = (term149 _27094 h P t).
Proof. exact (eq_refl (term149 _27094 h P t)). Qed.
Lemma lem1153351 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term156 _27094 h P t) = (term172 _27094 h P t).
Proof. exact (MK_COMB (@lem1153349 _27094 h P t) (@lem1153350 _27094 h P t)). Qed.
Lemma lem1153353 {A : Type'} (P : A -> Prop) (Q : Prop) : (term114 A P Q) = (term115 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem1153354 {_27094 : Type'} (P : _27094 -> Prop) (Q : Prop) : (term114 _27094 P Q) = (term115 _27094 P Q).
Proof. exact (@lem1153353 _27094 P Q). Qed.
Lemma lem1153355 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term173 _27094 h P t) = (term174 _27094 h P t).
Proof. exact (@lem1153354 _27094 (term169 _27094 h P t) (term149 _27094 h P t)). Qed.
Lemma lem1153356 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term175 _27094 h P t x) = (term167 _27094 x h P t).
Proof. exact (eq_refl (term175 _27094 h P t x)). Qed.
Lemma lem1153357 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term176 _27094 h P t) = (term169 _27094 h P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153356 _27094 x h P t)). Qed.
Lemma lem1153358 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153359 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term177 _27094 h P t) = (term170 _27094 h P t).
Proof. exact (MK_COMB (@lem1153358 _27094) (@lem1153357 _27094 h P t)). Qed.
Lemma lem1153360 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153361 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term178 _27094 h P t) = (term171 _27094 h P t).
Proof. exact (MK_COMB (@lem1153360) (@lem1153359 _27094 h P t)). Qed.
Lemma lem1153362 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term149 _27094 h P t) = (term149 _27094 h P t).
Proof. exact (eq_refl (term149 _27094 h P t)). Qed.
Lemma lem1153363 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term173 _27094 h P t) = (term172 _27094 h P t).
Proof. exact (MK_COMB (@lem1153361 _27094 h P t) (@lem1153362 _27094 h P t)). Qed.
Lemma lem1153364 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1153365 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term179 _27094 h P t) = (term180 _27094 h P t).
Proof. exact (MK_COMB (@lem1153364) (@lem1153363 _27094 h P t)). Qed.
Lemma lem1153366 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term175 _27094 h P t x) = (term167 _27094 x h P t).
Proof. exact (eq_refl (term175 _27094 h P t x)). Qed.
Lemma lem1153367 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153368 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term181 _27094 h P t x) = (term182 _27094 x h P t).
Proof. exact (MK_COMB (@lem1153367) (@lem1153366 _27094 x h P t)). Qed.
Lemma lem1153369 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term149 _27094 h P t) = (term149 _27094 h P t).
Proof. exact (eq_refl (term149 _27094 h P t)). Qed.
Lemma lem1153370 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term183 _27094 x h P t) = (term184 _27094 x h P t).
Proof. exact (MK_COMB (@lem1153368 _27094 x h P t) (@lem1153369 _27094 h P t)). Qed.
Lemma lem1153371 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term185 _27094 h P t) = (term186 _27094 h P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153370 _27094 x h P t)). Qed.
Lemma lem1153372 {_27094 : Type'} : (@ex _27094) = (@ex _27094).
Proof. exact (eq_refl (@ex _27094)). Qed.
Lemma lem1153373 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term174 _27094 h P t) = (term187 _27094 h P t).
Proof. exact (MK_COMB (@lem1153372 _27094) (@lem1153371 _27094 h P t)). Qed.
Lemma lem1153374 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : ((term173 _27094 h P t) = (term174 _27094 h P t)) = ((term172 _27094 h P t) = (term187 _27094 h P t)).
Proof. exact (MK_COMB (@lem1153365 _27094 h P t) (@lem1153373 _27094 h P t)). Qed.
Lemma lem1153375 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term172 _27094 h P t) = (term187 _27094 h P t).
Proof. exact (EQ_MP (@lem1153374 _27094 h P t) (@lem1153355 _27094 h P t)). Qed.
Lemma lem1153377 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term156 _27094 h P t) = (term187 _27094 h P t).
Proof. exact (TRANS (@lem1153351 _27094 h P t) (@lem1153375 _27094 h P t)). Qed.
Lemma lem1153378 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term52 _27094 h P t) = (term187 _27094 h P t).
Proof. exact (TRANS (@lem1153246 _27094 h P t) (@lem1153377 _27094 h P t)). Qed.
Lemma lem1153379 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) : term187 _27094 h P t.
Proof. exact (EQ_MP (@lem1153378 _27094 h P t) (@lem1153017 _27094 h P t h1)). Qed.
Lemma lem1153380 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term184 _27094 x h P t) : term184 _27094 x h P t.
Proof. exact (h1). Qed.
Lemma lem1153381 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term127 _27094 x' P t) : term127 _27094 x' P t.
Proof. exact (h1). Qed.
Lemma lem1153386 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (@EX _27094 P t) = (@EX _27094 P t).
Proof. exact (eq_refl (@EX _27094 P t)). Qed.
Lemma lem1153391 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1153392 {_27094 : Type'} (f : _27094 -> Prop) (x : _27094) : (f x) = (@I (_27094 -> Prop) f x).
Proof. exact (@lem1153391 _27094 Prop f x). Qed.
Lemma lem1153394 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (P h) = (@I (_27094 -> Prop) P h).
Proof. exact (@lem1153392 _27094 P h). Qed.
Lemma lem1153395 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153396 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term188 _27094 P h) = (term189 _27094 P h).
Proof. exact (MK_COMB (@lem1153395) (@lem1153394 _27094 P h)). Qed.
Lemma lem1153397 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term49 _27094 h P t) = (term190 _27094 h P t).
Proof. exact (MK_COMB (@lem1153396 _27094 P h) (@lem1153386 _27094 P t)). Qed.
Lemma lem1153414 {_27094 : Type'} (h : _27094) (x : _27094) (t : list _27094) : (term132 _27094 h x t) = (term132 _27094 h x t).
Proof. exact (eq_refl (term132 _27094 h x t)). Qed.
Lemma lem1153415 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1153420 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1153421 {_27094 : Type'} (f : _27094 -> Prop) (x : _27094) : (f x) = (@I (_27094 -> Prop) f x).
Proof. exact (@lem1153420 _27094 Prop f x). Qed.
Lemma lem1153423 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (P x) = (@I (_27094 -> Prop) P x).
Proof. exact (@lem1153421 _27094 P x). Qed.
Lemma lem1153424 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term191 _27094 P x) = (term192 _27094 P x).
Proof. exact (MK_COMB (@lem1153415) (@lem1153423 _27094 P x)). Qed.
Lemma lem1153425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153426 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term133 _27094 P x) = (term193 _27094 P x).
Proof. exact (MK_COMB (@lem1153425) (@lem1153424 _27094 P x)). Qed.
Lemma lem1153427 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term135 _27094 P h x t) = (term194 _27094 P h x t).
Proof. exact (MK_COMB (@lem1153426 _27094 P x) (@lem1153414 _27094 h x t)). Qed.
Lemma lem1153428 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term142 _27094 P h t) = (term195 _27094 P h t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153427 _27094 P h x t)). Qed.
Lemma lem1153429 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153430 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term143 _27094 P h t) = (term196 _27094 P h t).
Proof. exact (MK_COMB (@lem1153429 _27094) (@lem1153428 _27094 P h t)). Qed.
Lemma lem1153431 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153432 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : (term147 _27094 P h t) = (term197 _27094 P h t).
Proof. exact (MK_COMB (@lem1153431) (@lem1153430 _27094 P h t)). Qed.
Lemma lem1153433 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term149 _27094 h P t) = (term198 _27094 h P t).
Proof. exact (MK_COMB (@lem1153432 _27094 P h t) (@lem1153397 _27094 h P t)). Qed.
Lemma lem1153440 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term86 _27094 P t) = (term86 _27094 P t).
Proof. exact (eq_refl (term86 _27094 P t)). Qed.
Lemma lem1153441 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1153446 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1153447 {_27094 : Type'} (f : _27094 -> Prop) (x : _27094) : (f x) = (@I (_27094 -> Prop) f x).
Proof. exact (@lem1153446 _27094 Prop f x). Qed.
Lemma lem1153449 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (P h) = (@I (_27094 -> Prop) P h).
Proof. exact (@lem1153447 _27094 P h). Qed.
Lemma lem1153450 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term191 _27094 P h) = (term192 _27094 P h).
Proof. exact (MK_COMB (@lem1153441) (@lem1153449 _27094 P h)). Qed.
Lemma lem1153451 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153452 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term199 _27094 P h) = (term200 _27094 P h).
Proof. exact (MK_COMB (@lem1153451) (@lem1153450 _27094 P h)). Qed.
Lemma lem1153453 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term145 _27094 h P t) = (term201 _27094 h P t).
Proof. exact (MK_COMB (@lem1153452 _27094 P h) (@lem1153440 _27094 P t)). Qed.
Lemma lem1153466 {_27094 : Type'} (h : _27094) (x : _27094) (t : list _27094) : (term41 _27094 h x t) = (term41 _27094 h x t).
Proof. exact (eq_refl (term41 _27094 h x t)). Qed.
Lemma lem1153471 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1153472 {_27094 : Type'} (f : _27094 -> Prop) (x : _27094) : (f x) = (@I (_27094 -> Prop) f x).
Proof. exact (@lem1153471 _27094 Prop f x). Qed.
Lemma lem1153474 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (P x) = (@I (_27094 -> Prop) P x).
Proof. exact (@lem1153472 _27094 P x). Qed.
Lemma lem1153475 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153476 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term32 _27094 P x) = (term202 _27094 P x).
Proof. exact (MK_COMB (@lem1153475) (@lem1153474 _27094 P x)). Qed.
Lemma lem1153477 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term43 _27094 P h x t) = (term203 _27094 P h x t).
Proof. exact (MK_COMB (@lem1153476 _27094 P x) (@lem1153466 _27094 h x t)). Qed.
Lemma lem1153478 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153479 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (x : _27094) (t : list _27094) : (term165 _27094 P h x t) = (term204 _27094 P h x t).
Proof. exact (MK_COMB (@lem1153478) (@lem1153477 _27094 P h x t)). Qed.
Lemma lem1153480 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term167 _27094 x h P t) = (term205 _27094 x h P t).
Proof. exact (MK_COMB (@lem1153479 _27094 P h x t) (@lem1153453 _27094 h P t)). Qed.
Lemma lem1153481 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153482 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term182 _27094 x h P t) = (term206 _27094 x h P t).
Proof. exact (MK_COMB (@lem1153481) (@lem1153480 _27094 x h P t)). Qed.
Lemma lem1153483 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term184 _27094 x h P t) = (term207 _27094 x h P t).
Proof. exact (MK_COMB (@lem1153482 _27094 x h P t) (@lem1153433 _27094 h P t)). Qed.
Lemma lem1153484 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term184 _27094 x h P t) : term207 _27094 x h P t.
Proof. exact (EQ_MP (@lem1153483 _27094 x h P t) (@lem1153380 _27094 x h P t h1)). Qed.
Lemma lem1153491 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term86 _27094 P t) = (term86 _27094 P t).
Proof. exact (eq_refl (term86 _27094 P t)). Qed.
Lemma lem1153498 {_27094 : Type'} (x : _27094) (t : list _27094) : (term208 _27094 x t) = (term208 _27094 x t).
Proof. exact (eq_refl (term208 _27094 x t)). Qed.
Lemma lem1153499 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem1153504 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1153505 {_27094 : Type'} (f : _27094 -> Prop) (x : _27094) : (f x) = (@I (_27094 -> Prop) f x).
Proof. exact (@lem1153504 _27094 Prop f x). Qed.
Lemma lem1153507 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (P x) = (@I (_27094 -> Prop) P x).
Proof. exact (@lem1153505 _27094 P x). Qed.
Lemma lem1153508 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term191 _27094 P x) = (term192 _27094 P x).
Proof. exact (MK_COMB (@lem1153499) (@lem1153507 _27094 P x)). Qed.
Lemma lem1153509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153510 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term133 _27094 P x) = (term193 _27094 P x).
Proof. exact (MK_COMB (@lem1153509) (@lem1153508 _27094 P x)). Qed.
Lemma lem1153511 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term76 _27094 P x t) = (term209 _27094 P x t).
Proof. exact (MK_COMB (@lem1153510 _27094 P x) (@lem1153498 _27094 x t)). Qed.
Lemma lem1153512 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term84 _27094 P t) = (term210 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153511 _27094 P x t)). Qed.
Lemma lem1153513 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153514 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term85 _27094 P t) = (term211 _27094 P t).
Proof. exact (MK_COMB (@lem1153513 _27094) (@lem1153512 _27094 P t)). Qed.
Lemma lem1153515 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153516 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term88 _27094 P t) = (term212 _27094 P t).
Proof. exact (MK_COMB (@lem1153515) (@lem1153514 _27094 P t)). Qed.
Lemma lem1153517 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term90 _27094 P t) = (term213 _27094 P t).
Proof. exact (MK_COMB (@lem1153516 _27094 P t) (@lem1153491 _27094 P t)). Qed.
Lemma lem1153522 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (@EX _27094 P t) = (@EX _27094 P t).
Proof. exact (eq_refl (@EX _27094 P t)). Qed.
Lemma lem1153527 {_27094 : Type'} (x' : _27094) (t : list _27094) : (@List.In _27094 x' t) = (@List.In _27094 x' t).
Proof. exact (eq_refl (@List.In _27094 x' t)). Qed.
Lemma lem1153532 {A B : Type'} (f : A -> B) (x : A) : (f x) = (@I (A -> B) f x).
Proof. exact (EQ_MP (@lem20662 A B f x) (@lem20661 A B f x)). Qed.
Lemma lem1153533 {_27094 : Type'} (f : _27094 -> Prop) (x : _27094) : (f x) = (@I (_27094 -> Prop) f x).
Proof. exact (@lem1153532 _27094 Prop f x). Qed.
Lemma lem1153535 {_27094 : Type'} (P : _27094 -> Prop) (x' : _27094) : (P x') = (@I (_27094 -> Prop) P x').
Proof. exact (@lem1153533 _27094 P x'). Qed.
Lemma lem1153536 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153537 {_27094 : Type'} (P : _27094 -> Prop) (x' : _27094) : (term32 _27094 P x') = (term202 _27094 P x').
Proof. exact (MK_COMB (@lem1153536) (@lem1153535 _27094 P x')). Qed.
Lemma lem1153538 {_27094 : Type'} (P : _27094 -> Prop) (x' : _27094) (t : list _27094) : (term72 _27094 P x' t) = (term214 _27094 P x' t).
Proof. exact (MK_COMB (@lem1153537 _27094 P x') (@lem1153527 _27094 x' t)). Qed.
Lemma lem1153539 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1153540 {_27094 : Type'} (P : _27094 -> Prop) (x' : _27094) (t : list _27094) : (term106 _27094 P x' t) = (term215 _27094 P x' t).
Proof. exact (MK_COMB (@lem1153539) (@lem1153538 _27094 P x' t)). Qed.
Lemma lem1153541 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) : (term108 _27094 x' P t) = (term216 _27094 x' P t).
Proof. exact (MK_COMB (@lem1153540 _27094 P x' t) (@lem1153522 _27094 P t)). Qed.
Lemma lem1153542 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem1153543 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) : (term125 _27094 x' P t) = (term217 _27094 x' P t).
Proof. exact (MK_COMB (@lem1153542) (@lem1153541 _27094 x' P t)). Qed.
Lemma lem1153544 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) : (term127 _27094 x' P t) = (term218 _27094 x' P t).
Proof. exact (MK_COMB (@lem1153543 _27094 x' P t) (@lem1153517 _27094 P t)). Qed.
Lemma lem1153545 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term127 _27094 x' P t) : term218 _27094 x' P t.
Proof. exact (EQ_MP (@lem1153544 _27094 x' P t) (@lem1153381 _27094 x' P t h1)). Qed.
Lemma lem1153546 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term216 _27094 x' P t.
Proof. exact (h1). Qed.
Lemma lem1153547 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term213 _27094 P t.
Proof. exact (h1). Qed.
Lemma lem1153549 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term214 _27094 P x' t.
Proof. exact (proj1 (@lem1153546 _27094 x' P t h1)). Qed.
Lemma lem1153552 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term205 _27094 x h P t.
Proof. exact (h1). Qed.
Lemma lem1153553 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term198 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1153554 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term201 _27094 h P t.
Proof. exact (proj2 (@lem1153552 _27094 x h P t h1)). Qed.
Lemma lem1153555 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term203 _27094 P h x t.
Proof. exact (proj1 (@lem1153552 _27094 x h P t h1)). Qed.
Lemma lem1153558 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term41 _27094 h x t.
Proof. exact (proj2 (@lem1153555 _27094 x h P t h1)). Qed.
Lemma lem1153562 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term190 _27094 h P t.
Proof. exact (proj2 (@lem1153553 _27094 h P t h1)). Qed.
Lemma lem1153563 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term196 _27094 P h t.
Proof. exact (proj1 (@lem1153553 _27094 h P t h1)). Qed.
Lemma lem1153567 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term211 _27094 P t.
Proof. exact (proj1 (@lem1153547 _27094 P t h1)). Qed.
Lemma lem1153568 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term205 _27094 x h P t.
Proof. exact (h1). Qed.
Lemma lem1153569 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term198 _27094 h P t.
Proof. exact (h1). Qed.
Lemma lem1153570 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term201 _27094 h P t.
Proof. exact (proj2 (@lem1153568 _27094 x h P t h1)). Qed.
Lemma lem1153571 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term203 _27094 P h x t.
Proof. exact (proj1 (@lem1153568 _27094 x h P t h1)). Qed.
Lemma lem1153574 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term41 _27094 h x t.
Proof. exact (proj2 (@lem1153571 _27094 x h P t h1)). Qed.
Lemma lem1153578 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term190 _27094 h P t.
Proof. exact (proj2 (@lem1153569 _27094 h P t h1)). Qed.
Lemma lem1153579 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term196 _27094 P h t.
Proof. exact (proj1 (@lem1153569 _27094 h P t h1)). Qed.
Lemma lem1153667 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term194 _27094 P h x t) = (term219 _27094 h P x t).
Proof. exact (@lem19490 (term220 _27094 x h) (term192 _27094 P x) (term208 _27094 x t)). Qed.
Lemma lem1153668 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term195 _27094 P h t) = (term221 _27094 h P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153667 _27094 h P x t)). Qed.
Lemma lem1153669 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153671 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term196 _27094 P h t) = (term222 _27094 h P t).
Proof. exact (MK_COMB (@lem1153669 _27094) (@lem1153668 _27094 h P t)). Qed.
Lemma lem1153672 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term222 _27094 h P t.
Proof. exact (EQ_MP (@lem1153671 _27094 h P t) (@lem1153563 _27094 h P t h1)). Qed.
Lemma lem1153706 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term194 _27094 P h x t) = (term219 _27094 h P x t).
Proof. exact (@lem19490 (term220 _27094 x h) (term192 _27094 P x) (term208 _27094 x t)). Qed.
Lemma lem1153707 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term195 _27094 P h t) = (term221 _27094 h P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153706 _27094 h P x t)). Qed.
Lemma lem1153708 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153710 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term196 _27094 P h t) = (term222 _27094 h P t).
Proof. exact (MK_COMB (@lem1153708 _27094) (@lem1153707 _27094 h P t)). Qed.
Lemma lem1153711 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term222 _27094 h P t.
Proof. exact (EQ_MP (@lem1153710 _27094 h P t) (@lem1153563 _27094 h P t h1)). Qed.
Lemma lem1153748 {_27094 : Type'} (x : _27094) (h : _27094) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1153756 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term209 _27094 P x t) = (term209 _27094 P x t).
Proof. exact (eq_refl (term209 _27094 P x t)). Qed.
Lemma lem1153757 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term210 _27094 P t) = (term210 _27094 P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153756 _27094 P x t)). Qed.
Lemma lem1153758 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153760 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term211 _27094 P t) = (term211 _27094 P t).
Proof. exact (MK_COMB (@lem1153758 _27094) (@lem1153757 _27094 P t)). Qed.
Lemma lem1153761 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term211 _27094 P t.
Proof. exact (EQ_MP (@lem1153760 _27094 P t) (@lem1153567 _27094 P t h1)). Qed.
Lemma lem1153781 {_27094 : Type'} (x : _27094) (t : list _27094) (h1 : @List.In _27094 x t) : @List.In _27094 x t.
Proof. exact (h1). Qed.
Lemma lem1153816 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) : (term194 _27094 P h x t) = (term219 _27094 h P x t).
Proof. exact (@lem19490 (term220 _27094 x h) (term192 _27094 P x) (term208 _27094 x t)). Qed.
Lemma lem1153817 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term195 _27094 P h t) = (term221 _27094 h P t).
Proof. exact (fun_ext (fun x : _27094 => @lem1153816 _27094 h P x t)). Qed.
Lemma lem1153818 {_27094 : Type'} : (@all _27094) = (@all _27094).
Proof. exact (eq_refl (@all _27094)). Qed.
Lemma lem1153820 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term196 _27094 P h t) = (term222 _27094 h P t).
Proof. exact (MK_COMB (@lem1153818 _27094) (@lem1153817 _27094 h P t)). Qed.
Lemma lem1153821 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term222 _27094 h P t.
Proof. exact (EQ_MP (@lem1153820 _27094 h P t) (@lem1153579 _27094 h P t h1)). Qed.
Lemma lem1153825 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (h1 : @I (_27094 -> Prop) P h) : @I (_27094 -> Prop) P h.
Proof. exact (h1). Qed.
Lemma lem1153869 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : @EX _27094 P t) : @EX _27094 P t.
Proof. exact (h1). Qed.
Lemma lem1153870 {_27094 : Type'} (_19243 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term223 _27094 h P t _19243.
Proof. exact (@lem1153672 _27094 h P t h1 _19243). Qed.
Lemma lem1153871 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (_19243 : _27094) (t : list _27094) : (term223 _27094 h P t _19243) = (term219 _27094 h P _19243 t).
Proof. exact (eq_refl (term223 _27094 h P t _19243)). Qed.
Lemma lem1153872 {_27094 : Type'} (_19243 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term219 _27094 h P _19243 t.
Proof. exact (EQ_MP (@lem1153871 _27094 h P _19243 t) (@lem1153870 _27094 _19243 h P t h1)). Qed.
Lemma lem1153873 {_27094 : Type'} (_19244 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term223 _27094 h P t _19244.
Proof. exact (@lem1153711 _27094 h P t h1 _19244). Qed.
Lemma lem1153874 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (_19244 : _27094) (t : list _27094) : (term223 _27094 h P t _19244) = (term219 _27094 h P _19244 t).
Proof. exact (eq_refl (term223 _27094 h P t _19244)). Qed.
Lemma lem1153875 {_27094 : Type'} (_19244 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term219 _27094 h P _19244 t.
Proof. exact (EQ_MP (@lem1153874 _27094 h P _19244 t) (@lem1153873 _27094 _19244 h P t h1)). Qed.
Lemma lem1153879 {_27094 : Type'} (_19246 : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term224 _27094 P t _19246.
Proof. exact (@lem1153761 _27094 P t h1 _19246). Qed.
Lemma lem1153880 {_27094 : Type'} (P : _27094 -> Prop) (_19246 : _27094) (t : list _27094) : (term224 _27094 P t _19246) = (term209 _27094 P _19246 t).
Proof. exact (eq_refl (term224 _27094 P t _19246)). Qed.
Lemma lem1153885 {_27094 : Type'} (_19248 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term223 _27094 h P t _19248.
Proof. exact (@lem1153821 _27094 h P t h1 _19248). Qed.
Lemma lem1153886 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (_19248 : _27094) (t : list _27094) : (term223 _27094 h P t _19248) = (term219 _27094 h P _19248 t).
Proof. exact (eq_refl (term223 _27094 h P t _19248)). Qed.
Lemma lem1153887 {_27094 : Type'} (_19248 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term219 _27094 h P _19248 t.
Proof. exact (EQ_MP (@lem1153886 _27094 h P _19248 t) (@lem1153885 _27094 _19248 h P t h1)). Qed.
Lemma lem1153925 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term86 _27094 P t.
Proof. exact (proj2 (@lem1153554 _27094 x h P t h1)). Qed.
Lemma lem1153949 {_27094 : Type'} (_19243 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term209 _27094 P _19243 t.
Proof. exact (proj2 (@lem1153872 _27094 _19243 h P t h1)). Qed.
Lemma lem1153969 {_27094 : Type'} (_19244 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term209 _27094 P _19244 t.
Proof. exact (proj2 (@lem1153875 _27094 _19244 h P t h1)). Qed.
Lemma lem1153983 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : @I (_27094 -> Prop) P x.
Proof. exact (proj1 (@lem1153571 _27094 x h P t h1)). Qed.
Lemma lem1153985 {_27094 : Type'} (x : _27094) (h : _27094) (h1 : x = h) : x = h.
Proof. exact (h1). Qed.
Lemma lem1153991 {_27094 : Type'} (_19246 : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term209 _27094 P _19246 t.
Proof. exact (EQ_MP (@lem1153880 _27094 P _19246 t) (@lem1153879 _27094 _19246 P t h1)). Qed.
Lemma lem1154001 {_27094 : Type'} (x : _27094) (t : list _27094) (h1 : @List.In _27094 x t) : @List.In _27094 x t.
Proof. exact (h1). Qed.
Lemma lem1154011 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (h1 : @I (_27094 -> Prop) P h) : @I (_27094 -> Prop) P h.
Proof. exact (h1). Qed.
Lemma lem1154017 {_27094 : Type'} (_19248 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term225 _27094 P _19248 h.
Proof. exact (proj1 (@lem1153887 _27094 _19248 h P t h1)). Qed.
Lemma lem1154031 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term86 _27094 P t.
Proof. exact (proj2 (@lem1153547 _27094 P t h1)). Qed.
Lemma lem1154033 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : @EX _27094 P t) : @EX _27094 P t.
Proof. exact (h1). Qed.
Lemma lem1154129 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term86 _27094 P t.
Proof. exact (proj2 (@lem1153554 _27094 x h P t h1)). Qed.
Lemma lem1154198 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term192 _27094 P h.
Proof. exact (proj1 (@lem1153570 _27094 x h P t h1)). Qed.
Lemma lem1154213 {_27094 : Type'} (P : _27094 -> Prop) : (term226 _27094 P) = (term226 _27094 P).
Proof. exact (eq_refl (term226 _27094 P)). Qed.
Lemma lem1154214 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (h : _27094) (h1 : x = h) : (term227 _27094 P x) = (term227 _27094 P h).
Proof. exact (MK_COMB (@lem1154213 _27094 P) (@lem1153985 _27094 x h h1)). Qed.
Lemma lem1154215 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term227 _27094 P h) = (@I (_27094 -> Prop) P h).
Proof. exact (eq_refl (term227 _27094 P h)). Qed.
Lemma lem1154216 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term228 _27094 P x) = (term228 _27094 P x).
Proof. exact (eq_refl (term228 _27094 P x)). Qed.
Lemma lem1154217 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (h : _27094) : ((term227 _27094 P x) = (term227 _27094 P h)) = ((term227 _27094 P x) = (@I (_27094 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1154216 _27094 P x) (@lem1154215 _27094 P h)). Qed.
Lemma lem1154218 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term227 _27094 P x) = (@I (_27094 -> Prop) P x).
Proof. exact (eq_refl (term227 _27094 P x)). Qed.
Lemma lem1154219 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1154220 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term228 _27094 P x) = (term229 _27094 P x).
Proof. exact (MK_COMB (@lem1154219) (@lem1154218 _27094 P x)). Qed.
Lemma lem1154221 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (@I (_27094 -> Prop) P h) = (@I (_27094 -> Prop) P h).
Proof. exact (eq_refl (@I (_27094 -> Prop) P h)). Qed.
Lemma lem1154222 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (h : _27094) : ((term227 _27094 P x) = (@I (_27094 -> Prop) P h)) = ((@I (_27094 -> Prop) P x) = (@I (_27094 -> Prop) P h)).
Proof. exact (MK_COMB (@lem1154220 _27094 P x) (@lem1154221 _27094 P h)). Qed.
Lemma lem1154223 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (h : _27094) : ((term227 _27094 P x) = (term227 _27094 P h)) = ((@I (_27094 -> Prop) P x) = (@I (_27094 -> Prop) P h)).
Proof. exact (TRANS (@lem1154217 _27094 x P h) (@lem1154222 _27094 x P h)). Qed.
Lemma lem1154224 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) (h : _27094) (h1 : x = h) : (@I (_27094 -> Prop) P x) = (@I (_27094 -> Prop) P h).
Proof. exact (EQ_MP (@lem1154223 _27094 x P h) (@lem1154214 _27094 P x h h1)). Qed.
Lemma lem1154227 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @EX _27094 P t.
Proof. exact (proj2 (@lem1153546 _27094 x' P t h1)). Qed.
Lemma lem1154228 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term230 _27094 P t.
Proof. exact (fun h0 : term86 _27094 P t => @lem1154227 _27094 x' P t h1). Qed.
Lemma lem1154230 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154231 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term230 _27094 P t) = (@EX _27094 P t).
Proof. exact (@lem1154230 (@EX _27094 P t)). Qed.
Lemma lem1154232 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @EX _27094 P t.
Proof. exact (EQ_MP (@lem1154231 _27094 P t) (@lem1154228 _27094 x' P t h1)). Qed.
Lemma lem1154235 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154237 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term86 _27094 P t) = (term232 _27094 P t).
Proof. exact (@lem1154235 (@EX _27094 P t)). Qed.
Lemma lem1154240 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term232 _27094 P t.
Proof. exact (EQ_MP (@lem1154237 _27094 P t) (@lem1154129 _27094 x h P t h1)). Qed.
Lemma lem1154243 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (@lem1154240 _27094 x h P t h1 (@lem1154232 _27094 x' P t h2)). Qed.
Lemma lem1154244 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : term216 _27094 x' P t) : term233.
Proof. exact (fun h0 : ~ False => @lem1154243 _27094 x h x' P t h1 h2). Qed.
Lemma lem1154246 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154247 : term233 = False.
Proof. exact (@lem1154246 False). Qed.
Lemma lem1154250 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @EX _27094 P t.
Proof. exact (proj2 (@lem1153546 _27094 x' P t h1)). Qed.
Lemma lem1154251 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term230 _27094 P t.
Proof. exact (fun h0 : term86 _27094 P t => @lem1154250 _27094 x' P t h1). Qed.
Lemma lem1154253 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154254 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term230 _27094 P t) = (@EX _27094 P t).
Proof. exact (@lem1154253 (@EX _27094 P t)). Qed.
Lemma lem1154255 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @EX _27094 P t.
Proof. exact (EQ_MP (@lem1154254 _27094 P t) (@lem1154251 _27094 x' P t h1)). Qed.
Lemma lem1154258 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154260 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term86 _27094 P t) = (term232 _27094 P t).
Proof. exact (@lem1154258 (@EX _27094 P t)). Qed.
Lemma lem1154263 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term232 _27094 P t.
Proof. exact (EQ_MP (@lem1154260 _27094 P t) (@lem1153925 _27094 x h P t h1)). Qed.
Lemma lem1154266 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (@lem1154263 _27094 x h P t h1 (@lem1154255 _27094 x' P t h2)). Qed.
Lemma lem1154267 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : term216 _27094 x' P t) : term233.
Proof. exact (fun h0 : ~ False => @lem1154266 _27094 x h x' P t h1 h2). Qed.
Lemma lem1154269 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154270 : term233 = False.
Proof. exact (@lem1154269 False). Qed.
Lemma lem1154271 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (EQ_MP (@lem1154270) (@lem1154267 _27094 x h x' P t h1 h2)). Qed.
Lemma lem1154336 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @I (_27094 -> Prop) P x'.
Proof. exact (proj1 (@lem1153549 _27094 x' P t h1)). Qed.
Lemma lem1154337 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term234 _27094 P x'.
Proof. exact (fun h0 : term192 _27094 P x' => @lem1154336 _27094 x' P t h1). Qed.
Lemma lem1154339 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154340 {_27094 : Type'} (P : _27094 -> Prop) (x' : _27094) : (term234 _27094 P x') = (@I (_27094 -> Prop) P x').
Proof. exact (@lem1154339 (@I (_27094 -> Prop) P x')). Qed.
Lemma lem1154341 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @I (_27094 -> Prop) P x'.
Proof. exact (EQ_MP (@lem1154340 _27094 P x') (@lem1154337 _27094 x' P t h1)). Qed.
Lemma lem1154343 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @List.In _27094 x' t.
Proof. exact (proj2 (@lem1153549 _27094 x' P t h1)). Qed.
Lemma lem1154344 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term235 _27094 x' t.
Proof. exact (fun h0 : term208 _27094 x' t => @lem1154343 _27094 x' P t h1). Qed.
Lemma lem1154346 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154347 {_27094 : Type'} (x' : _27094) (t : list _27094) : (term235 _27094 x' t) = (@List.In _27094 x' t).
Proof. exact (@lem1154346 (@List.In _27094 x' t)). Qed.
Lemma lem1154348 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @List.In _27094 x' t.
Proof. exact (EQ_MP (@lem1154347 _27094 x' t) (@lem1154344 _27094 x' P t h1)). Qed.
Lemma lem1154350 (a : Prop) (b : Prop) : (term236 a b) = (term237 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1154351 {_27094 : Type'} (P : _27094 -> Prop) (_19243 : _27094) (t : list _27094) : (term209 _27094 P _19243 t) = (term238 _27094 P _19243 t).
Proof. exact (@lem1154350 (@I (_27094 -> Prop) P _19243) (@List.In _27094 _19243 t)). Qed.
Lemma lem1154353 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154354 {_27094 : Type'} (P : _27094 -> Prop) (_19243 : _27094) (t : list _27094) : (term238 _27094 P _19243 t) = (term239 _27094 P _19243 t).
Proof. exact (@lem1154353 (term214 _27094 P _19243 t)). Qed.
Lemma lem1154355 {_27094 : Type'} (P : _27094 -> Prop) (_19243 : _27094) (t : list _27094) : (term209 _27094 P _19243 t) = (term239 _27094 P _19243 t).
Proof. exact (TRANS (@lem1154351 _27094 P _19243 t) (@lem1154354 _27094 P _19243 t)). Qed.
Lemma lem1154357 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term214 _27094 P x' t.
Proof. exact (conj (@lem1154341 _27094 x' P t h1) (@lem1154348 _27094 x' P t h1)). Qed.
Lemma lem1154359 {_27094 : Type'} (_19243 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term239 _27094 P _19243 t.
Proof. exact (EQ_MP (@lem1154355 _27094 P _19243 t) (@lem1153949 _27094 _19243 h P t h1)). Qed.
Lemma lem1154360 {_27094 : Type'} (_19243 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term239 _27094 P _19243 t.
Proof. exact (@lem1154359 _27094 _19243 h P t h1). Qed.
Lemma lem1154361 {_27094 : Type'} (x' : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term239 _27094 P x' t.
Proof. exact (@lem1154360 _27094 x' h P t h1). Qed.
Lemma lem1154364 {_27094 : Type'} (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (@lem1154361 _27094 x' h P t h1 (@lem1154357 _27094 x' P t h2)). Qed.
Lemma lem1154365 {_27094 : Type'} (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) (h2 : term216 _27094 x' P t) : term233.
Proof. exact (fun h0 : ~ False => @lem1154364 _27094 h x' P t h1 h2). Qed.
Lemma lem1154367 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154368 : term233 = False.
Proof. exact (@lem1154367 False). Qed.
Lemma lem1154369 {_27094 : Type'} (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (EQ_MP (@lem1154368) (@lem1154365 _27094 h x' P t h1 h2)). Qed.
Lemma lem1154434 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @I (_27094 -> Prop) P x'.
Proof. exact (proj1 (@lem1153549 _27094 x' P t h1)). Qed.
Lemma lem1154435 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term234 _27094 P x'.
Proof. exact (fun h0 : term192 _27094 P x' => @lem1154434 _27094 x' P t h1). Qed.
Lemma lem1154437 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154438 {_27094 : Type'} (P : _27094 -> Prop) (x' : _27094) : (term234 _27094 P x') = (@I (_27094 -> Prop) P x').
Proof. exact (@lem1154437 (@I (_27094 -> Prop) P x')). Qed.
Lemma lem1154439 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @I (_27094 -> Prop) P x'.
Proof. exact (EQ_MP (@lem1154438 _27094 P x') (@lem1154435 _27094 x' P t h1)). Qed.
Lemma lem1154441 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @List.In _27094 x' t.
Proof. exact (proj2 (@lem1153549 _27094 x' P t h1)). Qed.
Lemma lem1154442 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term235 _27094 x' t.
Proof. exact (fun h0 : term208 _27094 x' t => @lem1154441 _27094 x' P t h1). Qed.
Lemma lem1154444 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154445 {_27094 : Type'} (x' : _27094) (t : list _27094) : (term235 _27094 x' t) = (@List.In _27094 x' t).
Proof. exact (@lem1154444 (@List.In _27094 x' t)). Qed.
Lemma lem1154446 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : @List.In _27094 x' t.
Proof. exact (EQ_MP (@lem1154445 _27094 x' t) (@lem1154442 _27094 x' P t h1)). Qed.
Lemma lem1154448 (a : Prop) (b : Prop) : (term236 a b) = (term237 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1154449 {_27094 : Type'} (P : _27094 -> Prop) (_19244 : _27094) (t : list _27094) : (term209 _27094 P _19244 t) = (term238 _27094 P _19244 t).
Proof. exact (@lem1154448 (@I (_27094 -> Prop) P _19244) (@List.In _27094 _19244 t)). Qed.
Lemma lem1154451 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154452 {_27094 : Type'} (P : _27094 -> Prop) (_19244 : _27094) (t : list _27094) : (term238 _27094 P _19244 t) = (term239 _27094 P _19244 t).
Proof. exact (@lem1154451 (term214 _27094 P _19244 t)). Qed.
Lemma lem1154453 {_27094 : Type'} (P : _27094 -> Prop) (_19244 : _27094) (t : list _27094) : (term209 _27094 P _19244 t) = (term239 _27094 P _19244 t).
Proof. exact (TRANS (@lem1154449 _27094 P _19244 t) (@lem1154452 _27094 P _19244 t)). Qed.
Lemma lem1154455 {_27094 : Type'} (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) : term214 _27094 P x' t.
Proof. exact (conj (@lem1154439 _27094 x' P t h1) (@lem1154446 _27094 x' P t h1)). Qed.
Lemma lem1154457 {_27094 : Type'} (_19244 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term239 _27094 P _19244 t.
Proof. exact (EQ_MP (@lem1154453 _27094 P _19244 t) (@lem1153969 _27094 _19244 h P t h1)). Qed.
Lemma lem1154458 {_27094 : Type'} (_19244 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term239 _27094 P _19244 t.
Proof. exact (@lem1154457 _27094 _19244 h P t h1). Qed.
Lemma lem1154459 {_27094 : Type'} (x' : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term239 _27094 P x' t.
Proof. exact (@lem1154458 _27094 x' h P t h1). Qed.
Lemma lem1154462 {_27094 : Type'} (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (@lem1154459 _27094 x' h P t h1 (@lem1154455 _27094 x' P t h2)). Qed.
Lemma lem1154463 {_27094 : Type'} (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) (h2 : term216 _27094 x' P t) : term233.
Proof. exact (fun h0 : ~ False => @lem1154462 _27094 h x' P t h1 h2). Qed.
Lemma lem1154465 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154466 : term233 = False.
Proof. exact (@lem1154465 False). Qed.
Lemma lem1154467 {_27094 : Type'} (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (EQ_MP (@lem1154466) (@lem1154463 _27094 h x' P t h1 h2)). Qed.
Lemma lem1154469 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : @I (_27094 -> Prop) P h.
Proof. exact (EQ_MP (@lem1154224 _27094 P x h h2) (@lem1153983 _27094 x h P t h1)). Qed.
Lemma lem1154470 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : term234 _27094 P h.
Proof. exact (fun h0 : term192 _27094 P h => @lem1154469 _27094 P t x h h1 h2). Qed.
Lemma lem1154472 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154473 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term234 _27094 P h) = (@I (_27094 -> Prop) P h).
Proof. exact (@lem1154472 (@I (_27094 -> Prop) P h)). Qed.
Lemma lem1154474 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : @I (_27094 -> Prop) P h.
Proof. exact (EQ_MP (@lem1154473 _27094 P h) (@lem1154470 _27094 P t x h h1 h2)). Qed.
Lemma lem1154477 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154479 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term192 _27094 P h) = (term240 _27094 P h).
Proof. exact (@lem1154477 (@I (_27094 -> Prop) P h)). Qed.
Lemma lem1154482 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term240 _27094 P h.
Proof. exact (EQ_MP (@lem1154479 _27094 P h) (@lem1154198 _27094 x h P t h1)). Qed.
Lemma lem1154485 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : False.
Proof. exact (@lem1154482 _27094 x h P t h1 (@lem1154474 _27094 P t x h h1 h2)). Qed.
Lemma lem1154486 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : term233.
Proof. exact (fun h0 : ~ False => @lem1154485 _27094 P t x h h1 h2). Qed.
Lemma lem1154488 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154489 : term233 = False.
Proof. exact (@lem1154488 False). Qed.
Lemma lem1154492 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : @I (_27094 -> Prop) P x.
Proof. exact (proj1 (@lem1153571 _27094 x h P t h1)). Qed.
Lemma lem1154493 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : term234 _27094 P x.
Proof. exact (fun h0 : term192 _27094 P x => @lem1154492 _27094 x h P t h1). Qed.
Lemma lem1154495 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154496 {_27094 : Type'} (P : _27094 -> Prop) (x : _27094) : (term234 _27094 P x) = (@I (_27094 -> Prop) P x).
Proof. exact (@lem1154495 (@I (_27094 -> Prop) P x)). Qed.
Lemma lem1154497 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) : @I (_27094 -> Prop) P x.
Proof. exact (EQ_MP (@lem1154496 _27094 P x) (@lem1154493 _27094 x h P t h1)). Qed.
Lemma lem1154499 {_27094 : Type'} (x : _27094) (t : list _27094) (h1 : @List.In _27094 x t) : @List.In _27094 x t.
Proof. exact (h1). Qed.
Lemma lem1154500 {_27094 : Type'} (x : _27094) (t : list _27094) (h1 : @List.In _27094 x t) : term235 _27094 x t.
Proof. exact (fun h0 : term208 _27094 x t => @lem1154499 _27094 x t h1). Qed.
Lemma lem1154502 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154503 {_27094 : Type'} (x : _27094) (t : list _27094) : (term235 _27094 x t) = (@List.In _27094 x t).
Proof. exact (@lem1154502 (@List.In _27094 x t)). Qed.
Lemma lem1154504 {_27094 : Type'} (x : _27094) (t : list _27094) (h1 : @List.In _27094 x t) : @List.In _27094 x t.
Proof. exact (EQ_MP (@lem1154503 _27094 x t) (@lem1154500 _27094 x t h1)). Qed.
Lemma lem1154506 (a : Prop) (b : Prop) : (term236 a b) = (term237 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1154507 {_27094 : Type'} (P : _27094 -> Prop) (_19246 : _27094) (t : list _27094) : (term209 _27094 P _19246 t) = (term238 _27094 P _19246 t).
Proof. exact (@lem1154506 (@I (_27094 -> Prop) P _19246) (@List.In _27094 _19246 t)). Qed.
Lemma lem1154509 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154510 {_27094 : Type'} (P : _27094 -> Prop) (_19246 : _27094) (t : list _27094) : (term238 _27094 P _19246 t) = (term239 _27094 P _19246 t).
Proof. exact (@lem1154509 (term214 _27094 P _19246 t)). Qed.
Lemma lem1154511 {_27094 : Type'} (P : _27094 -> Prop) (_19246 : _27094) (t : list _27094) : (term209 _27094 P _19246 t) = (term239 _27094 P _19246 t).
Proof. exact (TRANS (@lem1154507 _27094 P _19246 t) (@lem1154510 _27094 P _19246 t)). Qed.
Lemma lem1154513 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : @List.In _27094 x t) : term214 _27094 P x t.
Proof. exact (conj (@lem1154497 _27094 x h P t h1) (@lem1154504 _27094 x t h2)). Qed.
Lemma lem1154515 {_27094 : Type'} (_19246 : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term239 _27094 P _19246 t.
Proof. exact (EQ_MP (@lem1154511 _27094 P _19246 t) (@lem1153991 _27094 _19246 P t h1)). Qed.
Lemma lem1154516 {_27094 : Type'} (_19246 : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term239 _27094 P _19246 t.
Proof. exact (@lem1154515 _27094 _19246 P t h1). Qed.
Lemma lem1154517 {_27094 : Type'} (x : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term239 _27094 P x t.
Proof. exact (@lem1154516 _27094 x P t h1). Qed.
Lemma lem1154520 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : False.
Proof. exact (@lem1154517 _27094 x P t h1 (@lem1154513 _27094 h P x t h2 h3)). Qed.
Lemma lem1154521 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : term233.
Proof. exact (fun h0 : ~ False => @lem1154520 _27094 h P x t h1 h2 h3). Qed.
Lemma lem1154523 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154524 : term233 = False.
Proof. exact (@lem1154523 False). Qed.
Lemma lem1154525 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : False.
Proof. exact (EQ_MP (@lem1154524) (@lem1154521 _27094 h P x t h1 h2 h3)). Qed.
Lemma lem1154590 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (h1 : @I (_27094 -> Prop) P h) : @I (_27094 -> Prop) P h.
Proof. exact (h1). Qed.
Lemma lem1154591 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (h1 : @I (_27094 -> Prop) P h) : term234 _27094 P h.
Proof. exact (fun h0 : term192 _27094 P h => @lem1154590 _27094 P h h1). Qed.
Lemma lem1154593 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154594 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : (term234 _27094 P h) = (@I (_27094 -> Prop) P h).
Proof. exact (@lem1154593 (@I (_27094 -> Prop) P h)). Qed.
Lemma lem1154595 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (h1 : @I (_27094 -> Prop) P h) : @I (_27094 -> Prop) P h.
Proof. exact (EQ_MP (@lem1154594 _27094 P h) (@lem1154591 _27094 P h h1)). Qed.
Lemma lem1154597 {_27094 : Type'} (x : _27094) : x = x.
Proof. exact (@lem21386 _27094 x). Qed.
Lemma lem1154598 {_27094 : Type'} (x : _27094) : x = x.
Proof. exact (@lem1154597 _27094 x). Qed.
Lemma lem1154599 {_27094 : Type'} (h : _27094) : h = h.
Proof. exact (@lem1154598 _27094 h). Qed.
Lemma lem1154600 {_27094 : Type'} (h : _27094) : term241 _27094 h.
Proof. exact (fun h0 : term242 _27094 h => @lem1154599 _27094 h). Qed.
Lemma lem1154602 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154603 {_27094 : Type'} (h : _27094) : (term241 _27094 h) = (h = h).
Proof. exact (@lem1154602 (h = h)). Qed.
Lemma lem1154604 {_27094 : Type'} (h : _27094) : h = h.
Proof. exact (EQ_MP (@lem1154603 _27094 h) (@lem1154600 _27094 h)). Qed.
Lemma lem1154606 (a : Prop) (b : Prop) : (term236 a b) = (term237 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem1154607 {_27094 : Type'} (P : _27094 -> Prop) (_19248 : _27094) (h : _27094) : (term225 _27094 P _19248 h) = (term243 _27094 P _19248 h).
Proof. exact (@lem1154606 (@I (_27094 -> Prop) P _19248) (_19248 = h)). Qed.
Lemma lem1154609 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154610 {_27094 : Type'} (P : _27094 -> Prop) (_19248 : _27094) (h : _27094) : (term243 _27094 P _19248 h) = (term244 _27094 P _19248 h).
Proof. exact (@lem1154609 (term245 _27094 P _19248 h)). Qed.
Lemma lem1154611 {_27094 : Type'} (P : _27094 -> Prop) (_19248 : _27094) (h : _27094) : (term225 _27094 P _19248 h) = (term244 _27094 P _19248 h).
Proof. exact (TRANS (@lem1154607 _27094 P _19248 h) (@lem1154610 _27094 P _19248 h)). Qed.
Lemma lem1154613 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (h1 : @I (_27094 -> Prop) P h) : term246 _27094 P h.
Proof. exact (conj (@lem1154595 _27094 P h h1) (@lem1154604 _27094 h)). Qed.
Lemma lem1154615 {_27094 : Type'} (_19248 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term244 _27094 P _19248 h.
Proof. exact (EQ_MP (@lem1154611 _27094 P _19248 h) (@lem1154017 _27094 _19248 h P t h1)). Qed.
Lemma lem1154616 {_27094 : Type'} (_19248 : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term244 _27094 P _19248 h.
Proof. exact (@lem1154615 _27094 _19248 h P t h1). Qed.
Lemma lem1154617 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) : term247 _27094 P h.
Proof. exact (@lem1154616 _27094 h h P t h1). Qed.
Lemma lem1154620 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : False.
Proof. exact (@lem1154617 _27094 h P t h1 (@lem1154613 _27094 P h h2)). Qed.
Lemma lem1154621 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : term233.
Proof. exact (fun h0 : ~ False => @lem1154620 _27094 t P h h1 h2). Qed.
Lemma lem1154623 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154624 : term233 = False.
Proof. exact (@lem1154623 False). Qed.
Lemma lem1154625 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1154624) (@lem1154621 _27094 t P h h1 h2)). Qed.
Lemma lem1154690 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : @EX _27094 P t) : @EX _27094 P t.
Proof. exact (h1). Qed.
Lemma lem1154691 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : @EX _27094 P t) : term230 _27094 P t.
Proof. exact (fun h0 : term86 _27094 P t => @lem1154690 _27094 P t h1). Qed.
Lemma lem1154693 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154694 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term230 _27094 P t) = (@EX _27094 P t).
Proof. exact (@lem1154693 (@EX _27094 P t)). Qed.
Lemma lem1154695 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : @EX _27094 P t) : @EX _27094 P t.
Proof. exact (EQ_MP (@lem1154694 _27094 P t) (@lem1154691 _27094 P t h1)). Qed.
Lemma lem1154698 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem1154700 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term86 _27094 P t) = (term232 _27094 P t).
Proof. exact (@lem1154698 (@EX _27094 P t)). Qed.
Lemma lem1154703 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) : term232 _27094 P t.
Proof. exact (EQ_MP (@lem1154700 _27094 P t) (@lem1154031 _27094 P t h1)). Qed.
Lemma lem1154706 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : False.
Proof. exact (@lem1154703 _27094 P t h1 (@lem1154695 _27094 P t h2)). Qed.
Lemma lem1154707 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : term233.
Proof. exact (fun h0 : ~ False => @lem1154706 _27094 P t h1 h2). Qed.
Lemma lem1154709 (p : Prop) : (term231 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem1154710 : term233 = False.
Proof. exact (@lem1154709 False). Qed.
Lemma lem1154711 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : False.
Proof. exact (EQ_MP (@lem1154710) (@lem1154707 _27094 P t h1 h2)). Qed.
Lemma lem1154712 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1154489) (@lem1154486 _27094 P t x h h1 h2)). Qed.
Lemma lem1154713 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (EQ_MP (@lem1154247) (@lem1154244 _27094 x h x' P t h1 h2)). Qed.
Lemma lem1154714 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : (@EX _27094 P t) = False.
Proof. exact (prop_ext (fun h3 : @EX _27094 P t => @lem1154711 _27094 P t h1 h2) (fun h3 : False => @lem1154033 _27094 P t h2)). Qed.
Lemma lem1154715 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : False.
Proof. exact (EQ_MP (@lem1154714 _27094 P t h1 h2) (@lem1154033 _27094 P t h2)). Qed.
Lemma lem1154716 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : (@I (_27094 -> Prop) P h) = False.
Proof. exact (prop_ext (fun h3 : @I (_27094 -> Prop) P h => @lem1154625 _27094 t P h h1 h2) (fun h3 : False => @lem1154011 _27094 P h h2)). Qed.
Lemma lem1154717 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1154716 _27094 t P h h1 h2) (@lem1154011 _27094 P h h2)). Qed.
Lemma lem1154718 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : (@List.In _27094 x t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _27094 x t => @lem1154525 _27094 h P x t h1 h2 h3) (fun h4 : False => @lem1154001 _27094 x t h3)). Qed.
Lemma lem1154719 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : False.
Proof. exact (EQ_MP (@lem1154718 _27094 h P x t h1 h2 h3) (@lem1154001 _27094 x t h3)). Qed.
Lemma lem1154720 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1154712 _27094 P t x h h1 h2) (fun h3 : False => @lem1153985 _27094 x h h2)). Qed.
Lemma lem1154721 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1154720 _27094 P t x h h1 h2) (@lem1153985 _27094 x h h2)). Qed.
Lemma lem1154722 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : (@EX _27094 P t) = False.
Proof. exact (prop_ext (fun h3 : @EX _27094 P t => @lem1154715 _27094 P t h1 h2) (fun h3 : False => @lem1153869 _27094 P t h2)). Qed.
Lemma lem1154723 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : False.
Proof. exact (EQ_MP (@lem1154722 _27094 P t h1 h2) (@lem1153869 _27094 P t h2)). Qed.
Lemma lem1154724 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : (@I (_27094 -> Prop) P h) = False.
Proof. exact (prop_ext (fun h3 : @I (_27094 -> Prop) P h => @lem1154717 _27094 t P h h1 h2) (fun h3 : False => @lem1153825 _27094 P h h2)). Qed.
Lemma lem1154725 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1154724 _27094 t P h h1 h2) (@lem1153825 _27094 P h h2)). Qed.
Lemma lem1154726 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : (@List.In _27094 x t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _27094 x t => @lem1154719 _27094 h P x t h1 h2 h3) (fun h4 : False => @lem1153781 _27094 x t h3)). Qed.
Lemma lem1154727 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : False.
Proof. exact (EQ_MP (@lem1154726 _27094 h P x t h1 h2 h3) (@lem1153781 _27094 x t h3)). Qed.
Lemma lem1154728 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1154721 _27094 P t x h h1 h2) (fun h3 : False => @lem1153748 _27094 x h h2)). Qed.
Lemma lem1154729 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1154728 _27094 P t x h h1 h2) (@lem1153748 _27094 x h h2)). Qed.
Lemma lem1154730 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : (@EX _27094 P t) = False.
Proof. exact (prop_ext (fun h3 : @EX _27094 P t => @lem1154723 _27094 P t h1 h2) (fun h3 : False => @lem1153869 _27094 P t h2)). Qed.
Lemma lem1154731 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : @EX _27094 P t) : False.
Proof. exact (EQ_MP (@lem1154730 _27094 P t h1 h2) (@lem1153869 _27094 P t h2)). Qed.
Lemma lem1154732 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : (@I (_27094 -> Prop) P h) = False.
Proof. exact (prop_ext (fun h3 : @I (_27094 -> Prop) P h => @lem1154725 _27094 t P h h1 h2) (fun h3 : False => @lem1153825 _27094 P h h2)). Qed.
Lemma lem1154733 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) (h : _27094) (h1 : term198 _27094 h P t) (h2 : @I (_27094 -> Prop) P h) : False.
Proof. exact (EQ_MP (@lem1154732 _27094 t P h h1 h2) (@lem1153825 _27094 P h h2)). Qed.
Lemma lem1154734 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : (@List.In _27094 x t) = False.
Proof. exact (prop_ext (fun h4 : @List.In _27094 x t => @lem1154727 _27094 h P x t h1 h2 h3) (fun h4 : False => @lem1153781 _27094 x t h3)). Qed.
Lemma lem1154735 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (x : _27094) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) (h3 : @List.In _27094 x t) : False.
Proof. exact (EQ_MP (@lem1154734 _27094 h P x t h1 h2 h3) (@lem1153781 _27094 x t h3)). Qed.
Lemma lem1154736 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : (x = h) = False.
Proof. exact (prop_ext (fun h3 : x = h => @lem1154729 _27094 P t x h h1 h2) (fun h3 : False => @lem1153748 _27094 x h h2)). Qed.
Lemma lem1154737 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (x : _27094) (h : _27094) (h1 : term205 _27094 x h P t) (h2 : x = h) : False.
Proof. exact (EQ_MP (@lem1154736 _27094 P t x h h1 h2) (@lem1153748 _27094 x h h2)). Qed.
Lemma lem1154738 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term198 _27094 h P t) : False.
Proof. exact (or_elim (@lem1153578 _27094 h P t h2) (fun h0 : @I (_27094 -> Prop) P h => @lem1154733 _27094 t P h h2 h0) (fun h0 : @EX _27094 P t => @lem1154731 _27094 P t h1 h0)). Qed.
Lemma lem1154739 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term205 _27094 x h P t) : False.
Proof. exact (or_elim (@lem1153574 _27094 x h P t h2) (fun h0 : x = h => @lem1154737 _27094 P t x h h2 h0) (fun h0 : @List.In _27094 x t => @lem1154735 _27094 h P x t h1 h2 h0)). Qed.
Lemma lem1154740 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term213 _27094 P t) (h2 : term184 _27094 x h P t) : False.
Proof. exact (or_elim (@lem1153484 _27094 x h P t h2) (fun h0 : term205 _27094 x h P t => @lem1154739 _27094 x h P t h1 h0) (fun h0 : term198 _27094 h P t => @lem1154738 _27094 h P t h1 h0)). Qed.
Lemma lem1154741 {_27094 : Type'} (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term198 _27094 h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (or_elim (@lem1153562 _27094 h P t h1) (fun h0 : @I (_27094 -> Prop) P h => @lem1154369 _27094 h x' P t h1 h2) (fun h0 : @EX _27094 P t => @lem1154467 _27094 h x' P t h1 h2)). Qed.
Lemma lem1154742 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term205 _27094 x h P t) (h2 : term216 _27094 x' P t) : False.
Proof. exact (or_elim (@lem1153558 _27094 x h P t h1) (fun h0 : x = h => @lem1154713 _27094 x h x' P t h1 h2) (fun h0 : @List.In _27094 x t => @lem1154271 _27094 x h x' P t h1 h2)). Qed.
Lemma lem1154743 {_27094 : Type'} (x' : _27094) (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term216 _27094 x' P t) (h2 : term184 _27094 x h P t) : False.
Proof. exact (or_elim (@lem1153484 _27094 x h P t h2) (fun h0 : term205 _27094 x h P t => @lem1154742 _27094 x h x' P t h0 h1) (fun h0 : term198 _27094 h P t => @lem1154741 _27094 h x' P t h0 h1)). Qed.
Lemma lem1154744 {_27094 : Type'} (x : _27094) (h : _27094) (x' : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term184 _27094 x h P t) (h2 : term127 _27094 x' P t) : False.
Proof. exact (or_elim (@lem1153545 _27094 x' P t h2) (fun h0 : term216 _27094 x' P t => @lem1154743 _27094 x' x h P t h0 h1) (fun h0 : term213 _27094 P t => @lem1154740 _27094 x h P t h0 h1)). Qed.
Lemma lem1154745 {_27094 : Type'} (x : _27094) (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) (h2 : term184 _27094 x h P t) : False.
Proof. exact (ex_elim (@lem1153188 _27094 P t h1) (fun x' : _27094 => fun h0 : term129 _27094 P t x' => @lem1154744 _27094 x h x' P t h2 h0)). Qed.
Lemma lem1154746 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) (h2 : (term8 _27094 P t) = (@EX _27094 P t)) : False.
Proof. exact (ex_elim (@lem1153379 _27094 h P t h1) (fun x : _27094 => fun h0 : term186 _27094 h P t x => @lem1154745 _27094 x h P t h2 h0)). Qed.
Lemma lem1154747 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) (h2 : (term8 _27094 P t) = (@EX _27094 P t)) : (term52 _27094 h P t) = False.
Proof. exact (prop_ext (fun h3 : term52 _27094 h P t => @lem1154746 _27094 h P t h1 h2) (fun h3 : False => @lem1153017 _27094 h P t h1)). Qed.
Lemma lem1154748 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) (h2 : (term8 _27094 P t) = (@EX _27094 P t)) : False.
Proof. exact (EQ_MP (@lem1154747 _27094 h P t h1 h2) (@lem1153017 _27094 h P t h1)). Qed.
Lemma lem1154749 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : term51 _27094 h P t.
Proof. exact (fun h0 : term52 _27094 h P t => @lem1154748 _27094 h P t h0 h1). Qed.
Lemma lem1154750 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : (term46 _27094 P h t) = (term49 _27094 h P t).
Proof. exact (EQ_MP (@lem1153016 _27094 h P t) (@lem1154749 _27094 h P t h1)). Qed.
Lemma lem1154751 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : term59 _27094 h P t.
Proof. exact (fun h0 : (term8 _27094 P t) = (@EX _27094 P t) => @lem1154750 _27094 h P t h0). Qed.
Lemma lem1154756 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : term63 _27094 P t.
Proof. exact (fun h : _27094 => @lem1154751 _27094 h P t). Qed.
Lemma lem1154761 {_27094 : Type'} (t : list _27094) : term67 _27094 t.
Proof. exact (fun P : _27094 -> Prop => @lem1154756 _27094 P t). Qed.
Lemma lem1154766 {_27094 : Type'} : term71 _27094.
Proof. exact (fun t : list _27094 => @lem1154761 _27094 t). Qed.
Lemma lem1154767 {_27094 : Type'} : term70 _27094.
Proof. exact (EQ_MP (@lem1153011 _27094) (@lem1154766 _27094)). Qed.
Lemma lem1154768 {_27094 : Type'} (t : list _27094) : term248 _27094 t.
Proof. exact (@lem1154767 _27094 t). Qed.
Lemma lem1154769 {_27094 : Type'} (t : list _27094) : (term248 _27094 t) = (term66 _27094 t).
Proof. exact (eq_refl (term248 _27094 t)). Qed.
Lemma lem1154770 {_27094 : Type'} (t : list _27094) : term66 _27094 t.
Proof. exact (EQ_MP (@lem1154769 _27094 t) (@lem1154768 _27094 t)). Qed.
Lemma lem1154771 {_27094 : Type'} (t : list _27094) (P : _27094 -> Prop) : term249 _27094 t P.
Proof. exact (@lem1154770 _27094 t P). Qed.
Lemma lem1154772 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : (term249 _27094 t P) = (term62 _27094 P t).
Proof. exact (eq_refl (term249 _27094 t P)). Qed.
Lemma lem1154773 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) : term62 _27094 P t.
Proof. exact (EQ_MP (@lem1154772 _27094 P t) (@lem1154771 _27094 t P)). Qed.
Lemma lem1154774 {_27094 : Type'} (P : _27094 -> Prop) (t : list _27094) (h : _27094) : term250 _27094 P t h.
Proof. exact (@lem1154773 _27094 P t h). Qed.
Lemma lem1154775 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : (term250 _27094 P t h) = (term53 _27094 h P t).
Proof. exact (eq_refl (term250 _27094 P t h)). Qed.
Lemma lem1154776 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : term53 _27094 h P t.
Proof. exact (EQ_MP (@lem1154775 _27094 h P t) (@lem1154774 _27094 P t h)). Qed.
Lemma lem1154778 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) : term53 _27094 h P t.
Proof. exact (@lem1152809 _27094 h P t (@lem1154776 _27094 h P t)). Qed.
Lemma lem1154779 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : term51 _27094 h P t.
Proof. exact (@lem1154778 _27094 h P t (@lem1152703 _27094 P t h1)). Qed.
Lemma lem1154780 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) (h2 : (term8 _27094 P t) = (@EX _27094 P t)) : False.
Proof. exact (@lem1154779 _27094 h P t h2 (@lem1152793 _27094 h P t h1)). Qed.
Lemma lem1154781 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) (h2 : (term8 _27094 P t) = (@EX _27094 P t)) : (term52 _27094 h P t) = False.
Proof. exact (prop_ext (fun h3 : term52 _27094 h P t => @lem1154780 _27094 h P t h1 h2) (fun h3 : False => @lem1152793 _27094 h P t h1)). Qed.
Lemma lem1154782 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : term52 _27094 h P t) (h2 : (term8 _27094 P t) = (@EX _27094 P t)) : False.
Proof. exact (EQ_MP (@lem1154781 _27094 h P t h1 h2) (@lem1152793 _27094 h P t h1)). Qed.
Lemma lem1154783 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : term51 _27094 h P t.
Proof. exact (fun h0 : term52 _27094 h P t => @lem1154782 _27094 h P t h0 h1). Qed.
Lemma lem1154784 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : (term46 _27094 P h t) = (term49 _27094 h P t).
Proof. exact (EQ_MP (@lem1152792 _27094 h P t) (@lem1154783 _27094 h P t h1)). Qed.
Lemma lem1154785 {_27094 : Type'} (h : _27094) (P : _27094 -> Prop) (t : list _27094) (h1 : (term8 _27094 P t) = (@EX _27094 P t)) : (term12 _27094 P h t) = (term13 _27094 P h t).
Proof. exact (EQ_MP (@lem1152788 _27094 P h t) (@lem1154784 _27094 h P t h1)). Qed.
Lemma lem1154786 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) (t : list _27094) : term15 _27094 P h t.
Proof. exact (fun h0 : (term8 _27094 P t) = (@EX _27094 P t) => @lem1154785 _27094 h P t h0). Qed.
Lemma lem1154791 {_27094 : Type'} (P : _27094 -> Prop) (h : _27094) : term19 _27094 P h.
Proof. exact (fun t : list _27094 => @lem1154786 _27094 P h t). Qed.
Lemma lem1154796 {_27094 : Type'} (P : _27094 -> Prop) : term23 _27094 P.
Proof. exact (fun h : _27094 => @lem1154791 _27094 P h). Qed.
Lemma lem1154797 {_27094 : Type'} (P : _27094 -> Prop) : term25 _27094 P.
Proof. exact (conj (@lem1152747 _27094 P) (@lem1154796 _27094 P)). Qed.
Lemma lem1154798 {_27094 : Type'} (P : _27094 -> Prop) : term30 _27094 P.
Proof. exact (@lem1152702 _27094 P (@lem1154797 _27094 P)). Qed.
Lemma lem1154803 {_27094 : Type'} : term251 _27094.
Proof. exact (fun P : _27094 -> Prop => @lem1154798 _27094 P). Qed.
