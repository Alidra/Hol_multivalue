Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import ALL2_AND_RIGHT_term_abbrevs.
Require Import ALL2_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1094346_spec.
Require Import thm1094347_spec.
Require Import thm1100834_spec.
Require Import thm1100835_spec.
Require Import thm1100843_spec.
Require Import thm1100844_spec.
Require Import thm1809_spec.
Require Import thm1810_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm1842_spec.
Require Import thm1845_spec.
Require Import thm1855_spec.
Require Import thm1857_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm585_spec.
Require Import thm586_spec.
Require Import thm616_spec.
Require Import thm617_spec.
Lemma lem1128667 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1128668 {_26589 : Type'} (P : type1143 _26589) : term0 _26589 P.
Proof. exact (@lem1128667 _26589 P). Qed.
Lemma lem1128669 {_26588 _26589 : Type'} : term1 _26588 _26589.
Proof. exact (@lem1128668 _26589 (term2 _26588 _26589)). Qed.
Lemma lem1128670 {_26588 _26589 : Type'} : (term3 _26588 _26589) = (term4 _26588 _26589).
Proof. exact (eq_refl (term3 _26588 _26589)). Qed.
Lemma lem1128671 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128672 {_26588 _26589 : Type'} : (term5 _26588 _26589) = (term6 _26588 _26589).
Proof. exact (MK_COMB (@lem1128671) (@lem1128670 _26588 _26589)). Qed.
Lemma lem1128673 {_26588 _26589 : Type'} (t : list _26589) : (term7 _26588 _26589 t) = (term8 _26588 _26589 t).
Proof. exact (eq_refl (term7 _26588 _26589 t)). Qed.
Lemma lem1128674 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128675 {_26588 _26589 : Type'} (t : list _26589) : (term9 _26588 _26589 t) = (term10 _26588 _26589 t).
Proof. exact (MK_COMB (@lem1128674) (@lem1128673 _26588 _26589 t)). Qed.
Lemma lem1128676 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term11 _26588 _26589 h t) = (term12 _26588 _26589 h t).
Proof. exact (eq_refl (term11 _26588 _26589 h t)). Qed.
Lemma lem1128677 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term13 _26588 _26589 h t) = (term14 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128675 _26588 _26589 t) (@lem1128676 _26588 _26589 h t)). Qed.
Lemma lem1128678 {_26588 _26589 : Type'} (h : _26589) : (term15 _26588 _26589 h) = (term16 _26588 _26589 h).
Proof. exact (fun_ext (fun t : list _26589 => @lem1128677 _26588 _26589 h t)). Qed.
Lemma lem1128679 {_26589 : Type'} : (@all (list _26589)) = (@all (list _26589)).
Proof. exact (eq_refl (@all (list _26589))). Qed.
Lemma lem1128680 {_26588 _26589 : Type'} (h : _26589) : (term17 _26588 _26589 h) = (term18 _26588 _26589 h).
Proof. exact (MK_COMB (@lem1128679 _26589) (@lem1128678 _26588 _26589 h)). Qed.
Lemma lem1128681 {_26588 _26589 : Type'} : (term19 _26588 _26589) = (term20 _26588 _26589).
Proof. exact (fun_ext (fun h : _26589 => @lem1128680 _26588 _26589 h)). Qed.
Lemma lem1128682 {_26589 : Type'} : (@all _26589) = (@all _26589).
Proof. exact (eq_refl (@all _26589)). Qed.
Lemma lem1128683 {_26588 _26589 : Type'} : (term21 _26588 _26589) = (term22 _26588 _26589).
Proof. exact (MK_COMB (@lem1128682 _26589) (@lem1128681 _26588 _26589)). Qed.
Lemma lem1128684 {_26588 _26589 : Type'} : (term23 _26588 _26589) = (term24 _26588 _26589).
Proof. exact (MK_COMB (@lem1128672 _26588 _26589) (@lem1128683 _26588 _26589)). Qed.
Lemma lem1128685 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128686 {_26588 _26589 : Type'} : (term25 _26588 _26589) = (term26 _26588 _26589).
Proof. exact (MK_COMB (@lem1128685) (@lem1128684 _26588 _26589)). Qed.
Lemma lem1128687 {_26588 _26589 : Type'} (l : list _26589) : (term7 _26588 _26589 l) = (term8 _26588 _26589 l).
Proof. exact (eq_refl (term7 _26588 _26589 l)). Qed.
Lemma lem1128688 {_26588 _26589 : Type'} : (term27 _26588 _26589) = (term2 _26588 _26589).
Proof. exact (fun_ext (fun l : list _26589 => @lem1128687 _26588 _26589 l)). Qed.
Lemma lem1128689 {_26589 : Type'} : (@all (list _26589)) = (@all (list _26589)).
Proof. exact (eq_refl (@all (list _26589))). Qed.
Lemma lem1128690 {_26588 _26589 : Type'} : (term28 _26588 _26589) = (term29 _26588 _26589).
Proof. exact (MK_COMB (@lem1128689 _26589) (@lem1128688 _26588 _26589)). Qed.
Lemma lem1128691 {_26588 _26589 : Type'} : (term1 _26588 _26589) = (term30 _26588 _26589).
Proof. exact (MK_COMB (@lem1128686 _26588 _26589) (@lem1128690 _26588 _26589)). Qed.
Lemma lem1128692 {_26588 _26589 : Type'} : term30 _26588 _26589.
Proof. exact (EQ_MP (@lem1128691 _26588 _26589) (@lem1128669 _26588 _26589)). Qed.
Lemma lem1128693 {_26588 _26589 : Type'} (t : list _26589) (h1 : term8 _26588 _26589 t) : term8 _26588 _26589 t.
Proof. exact (h1). Qed.
Lemma lem1128721 {_25307 : Type'} (P : _25307 -> Prop) : (@List.Forall _25307 P (@nil _25307)) = True.
Proof. exact (EQ_MP (@lem1100835 _25307 P) (@lem1100834 _25307 P)). Qed.
Lemma lem1128722 {_26589 : Type'} (P : _26589 -> Prop) : (@List.Forall _26589 P (@nil _26589)) = True.
Proof. exact (@lem1128721 _26589 P). Qed.
Lemma lem1128723 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128724 {_26589 : Type'} (P : _26589 -> Prop) : (term31 _26589 P) = (and True).
Proof. exact (MK_COMB (@lem1128723) (@lem1128722 _26589 P)). Qed.
Lemma lem1128725 {_26588 _26589 : Type'} (Q : type1470 _26588 _26589) (m : list _26588) : (@ALL2 _26589 _26588 Q (@nil _26589) m) = (@ALL2 _26589 _26588 Q (@nil _26589) m).
Proof. exact (eq_refl (@ALL2 _26589 _26588 Q (@nil _26589) m)). Qed.
Lemma lem1128726 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (m : list _26588) : (term32 _26588 _26589 P Q m) = (term33 _26588 _26589 Q m).
Proof. exact (MK_COMB (@lem1128724 _26589 P) (@lem1128725 _26588 _26589 Q m)). Qed.
Lemma lem1128728 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1128729 {_26588 _26589 : Type'} (Q : type1470 _26588 _26589) (m : list _26588) : (term33 _26588 _26589 Q m) = (@ALL2 _26589 _26588 Q (@nil _26589) m).
Proof. exact (@lem1128728 (@ALL2 _26589 _26588 Q (@nil _26589) m)). Qed.
Lemma lem1128730 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (m : list _26588) : (term32 _26588 _26589 P Q m) = (@ALL2 _26589 _26588 Q (@nil _26589) m).
Proof. exact (TRANS (@lem1128726 _26588 _26589 P Q m) (@lem1128729 _26588 _26589 Q m)). Qed.
Lemma lem1128731 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (m : list _26588) : (term34 _26588 _26589 P Q m) = (term34 _26588 _26589 P Q m).
Proof. exact (eq_refl (term34 _26588 _26589 P Q m)). Qed.
Lemma lem1128732 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (m : list _26588) : ((term35 _26588 _26589 P Q m) = (term32 _26588 _26589 P Q m)) = ((term35 _26588 _26589 P Q m) = (@ALL2 _26589 _26588 Q (@nil _26589) m)).
Proof. exact (MK_COMB (@lem1128731 _26588 _26589 P Q m) (@lem1128730 _26588 _26589 P Q m)). Qed.
Lemma lem1128735 {_26588 _26589 : Type'} (P : _26589 -> Prop) (m : list _26588) : (term36 _26588 _26589 P m) = (term37 _26588 _26589 P m).
Proof. exact (fun_ext (fun Q : type1470 _26588 _26589 => @lem1128732 _26588 _26589 P Q m)). Qed.
Lemma lem1128736 {_26588 _26589 : Type'} : (@all (_26589 -> _26588 -> Prop)) = (@all (_26589 -> _26588 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> _26588 -> Prop))). Qed.
Lemma lem1128737 {_26588 _26589 : Type'} (P : _26589 -> Prop) (m : list _26588) : (term38 _26588 _26589 P m) = (term39 _26588 _26589 P m).
Proof. exact (MK_COMB (@lem1128736 _26588 _26589) (@lem1128735 _26588 _26589 P m)). Qed.
Lemma lem1128742 {_26588 _26589 : Type'} (m : list _26588) : (term40 _26588 _26589 m) = (term41 _26588 _26589 m).
Proof. exact (fun_ext (fun P : _26589 -> Prop => @lem1128737 _26588 _26589 P m)). Qed.
Lemma lem1128743 {_26589 : Type'} : (@all (_26589 -> Prop)) = (@all (_26589 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> Prop))). Qed.
Lemma lem1128744 {_26588 _26589 : Type'} (m : list _26588) : (term42 _26588 _26589 m) = (term43 _26588 _26589 m).
Proof. exact (MK_COMB (@lem1128743 _26589) (@lem1128742 _26588 _26589 m)). Qed.
Lemma lem1128749 {_26588 _26589 : Type'} : (term44 _26588 _26589) = (term45 _26588 _26589).
Proof. exact (fun_ext (fun m : list _26588 => @lem1128744 _26588 _26589 m)). Qed.
Lemma lem1128750 {_26588 : Type'} : (@all (list _26588)) = (@all (list _26588)).
Proof. exact (eq_refl (@all (list _26588))). Qed.
Lemma lem1128751 {_26588 _26589 : Type'} : (term4 _26588 _26589) = (term46 _26588 _26589).
Proof. exact (MK_COMB (@lem1128750 _26588) (@lem1128749 _26588 _26589)). Qed.
Lemma lem1128756 {_26588 _26589 : Type'} : (term46 _26588 _26589) = (term4 _26588 _26589).
Proof. exact (SYM (@lem1128751 _26588 _26589)). Qed.
Lemma lem1128793 {_25307 : Type'} (h : _25307) (P : _25307 -> Prop) (t : list _25307) : (term47 _25307 P h t) = (term48 _25307 h P t).
Proof. exact (EQ_MP (@lem1100844 _25307 h P t) (@lem1100843 _25307 h P t)). Qed.
Lemma lem1128794 {_26589 : Type'} (h : _26589) (P : _26589 -> Prop) (t : list _26589) : (term47 _26589 P h t) = (term48 _26589 h P t).
Proof. exact (@lem1128793 _26589 h P t). Qed.
Lemma lem1128797 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128798 {_26589 : Type'} (h : _26589) (P : _26589 -> Prop) (t : list _26589) : (term49 _26589 P h t) = (term50 _26589 h P t).
Proof. exact (MK_COMB (@lem1128797) (@lem1128794 _26589 h P t)). Qed.
Lemma lem1128799 {_26588 _26589 : Type'} (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) (m : list _26588) : (term51 _26588 _26589 Q h t m) = (term51 _26588 _26589 Q h t m).
Proof. exact (eq_refl (term51 _26588 _26589 Q h t m)). Qed.
Lemma lem1128800 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) (m : list _26588) : (term52 _26588 _26589 P Q h t m) = (term53 _26588 _26589 P Q h t m).
Proof. exact (MK_COMB (@lem1128798 _26589 h P t) (@lem1128799 _26588 _26589 Q h t m)). Qed.
Lemma lem1128803 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) (m : list _26588) : (term54 _26588 _26589 P Q h t m) = (term54 _26588 _26589 P Q h t m).
Proof. exact (eq_refl (term54 _26588 _26589 P Q h t m)). Qed.
Lemma lem1128804 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) (m : list _26588) : ((term55 _26588 _26589 P Q h t m) = (term52 _26588 _26589 P Q h t m)) = ((term55 _26588 _26589 P Q h t m) = (term53 _26588 _26589 P Q h t m)).
Proof. exact (MK_COMB (@lem1128803 _26588 _26589 P Q h t m) (@lem1128800 _26588 _26589 P Q h t m)). Qed.
Lemma lem1128807 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (t : list _26589) (m : list _26588) : (term56 _26588 _26589 P h t m) = (term57 _26588 _26589 P h t m).
Proof. exact (fun_ext (fun Q : type1470 _26588 _26589 => @lem1128804 _26588 _26589 P Q h t m)). Qed.
Lemma lem1128808 {_26588 _26589 : Type'} : (@all (_26589 -> _26588 -> Prop)) = (@all (_26589 -> _26588 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> _26588 -> Prop))). Qed.
Lemma lem1128809 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (t : list _26589) (m : list _26588) : (term58 _26588 _26589 P h t m) = (term59 _26588 _26589 P h t m).
Proof. exact (MK_COMB (@lem1128808 _26588 _26589) (@lem1128807 _26588 _26589 P h t m)). Qed.
Lemma lem1128814 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (m : list _26588) : (term60 _26588 _26589 h t m) = (term61 _26588 _26589 h t m).
Proof. exact (fun_ext (fun P : _26589 -> Prop => @lem1128809 _26588 _26589 P h t m)). Qed.
Lemma lem1128815 {_26589 : Type'} : (@all (_26589 -> Prop)) = (@all (_26589 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> Prop))). Qed.
Lemma lem1128816 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (m : list _26588) : (term62 _26588 _26589 h t m) = (term63 _26588 _26589 h t m).
Proof. exact (MK_COMB (@lem1128815 _26589) (@lem1128814 _26588 _26589 h t m)). Qed.
Lemma lem1128821 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term64 _26588 _26589 h t) = (term65 _26588 _26589 h t).
Proof. exact (fun_ext (fun m : list _26588 => @lem1128816 _26588 _26589 h t m)). Qed.
Lemma lem1128822 {_26588 : Type'} : (@all (list _26588)) = (@all (list _26588)).
Proof. exact (eq_refl (@all (list _26588))). Qed.
Lemma lem1128823 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term12 _26588 _26589 h t) = (term66 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128822 _26588) (@lem1128821 _26588 _26589 h t)). Qed.
Lemma lem1128828 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term66 _26588 _26589 h t) = (term12 _26588 _26589 h t).
Proof. exact (SYM (@lem1128823 _26588 _26589 h t)). Qed.
Lemma lem1128830 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1128831 {_26588 : Type'} (P : type1143 _26588) : term0 _26588 P.
Proof. exact (@lem1128830 _26588 P). Qed.
Lemma lem1128832 {_26588 _26589 : Type'} : term67 _26588 _26589.
Proof. exact (@lem1128831 _26588 (term45 _26588 _26589)). Qed.
Lemma lem1128833 {_26588 _26589 : Type'} : (term68 _26588 _26589) = (term69 _26588 _26589).
Proof. exact (eq_refl (term68 _26588 _26589)). Qed.
Lemma lem1128834 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128835 {_26588 _26589 : Type'} : (term70 _26588 _26589) = (term71 _26588 _26589).
Proof. exact (MK_COMB (@lem1128834) (@lem1128833 _26588 _26589)). Qed.
Lemma lem1128836 {_26588 _26589 : Type'} (t : list _26588) : (term72 _26588 _26589 t) = (term43 _26588 _26589 t).
Proof. exact (eq_refl (term72 _26588 _26589 t)). Qed.
Lemma lem1128837 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128838 {_26588 _26589 : Type'} (t : list _26588) : (term73 _26588 _26589 t) = (term74 _26588 _26589 t).
Proof. exact (MK_COMB (@lem1128837) (@lem1128836 _26588 _26589 t)). Qed.
Lemma lem1128839 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : (term75 _26588 _26589 h t) = (term76 _26588 _26589 h t).
Proof. exact (eq_refl (term75 _26588 _26589 h t)). Qed.
Lemma lem1128840 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : (term77 _26588 _26589 h t) = (term78 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128838 _26588 _26589 t) (@lem1128839 _26588 _26589 h t)). Qed.
Lemma lem1128841 {_26588 _26589 : Type'} (h : _26588) : (term79 _26588 _26589 h) = (term80 _26588 _26589 h).
Proof. exact (fun_ext (fun t : list _26588 => @lem1128840 _26588 _26589 h t)). Qed.
Lemma lem1128842 {_26588 : Type'} : (@all (list _26588)) = (@all (list _26588)).
Proof. exact (eq_refl (@all (list _26588))). Qed.
Lemma lem1128843 {_26588 _26589 : Type'} (h : _26588) : (term81 _26588 _26589 h) = (term82 _26588 _26589 h).
Proof. exact (MK_COMB (@lem1128842 _26588) (@lem1128841 _26588 _26589 h)). Qed.
Lemma lem1128844 {_26588 _26589 : Type'} : (term83 _26588 _26589) = (term84 _26588 _26589).
Proof. exact (fun_ext (fun h : _26588 => @lem1128843 _26588 _26589 h)). Qed.
Lemma lem1128845 {_26588 : Type'} : (@all _26588) = (@all _26588).
Proof. exact (eq_refl (@all _26588)). Qed.
Lemma lem1128846 {_26588 _26589 : Type'} : (term85 _26588 _26589) = (term86 _26588 _26589).
Proof. exact (MK_COMB (@lem1128845 _26588) (@lem1128844 _26588 _26589)). Qed.
Lemma lem1128847 {_26588 _26589 : Type'} : (term87 _26588 _26589) = (term88 _26588 _26589).
Proof. exact (MK_COMB (@lem1128835 _26588 _26589) (@lem1128846 _26588 _26589)). Qed.
Lemma lem1128848 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128849 {_26588 _26589 : Type'} : (term89 _26588 _26589) = (term90 _26588 _26589).
Proof. exact (MK_COMB (@lem1128848) (@lem1128847 _26588 _26589)). Qed.
Lemma lem1128850 {_26588 _26589 : Type'} (m : list _26588) : (term72 _26588 _26589 m) = (term43 _26588 _26589 m).
Proof. exact (eq_refl (term72 _26588 _26589 m)). Qed.
Lemma lem1128851 {_26588 _26589 : Type'} : (term91 _26588 _26589) = (term45 _26588 _26589).
Proof. exact (fun_ext (fun m : list _26588 => @lem1128850 _26588 _26589 m)). Qed.
Lemma lem1128852 {_26588 : Type'} : (@all (list _26588)) = (@all (list _26588)).
Proof. exact (eq_refl (@all (list _26588))). Qed.
Lemma lem1128853 {_26588 _26589 : Type'} : (term92 _26588 _26589) = (term46 _26588 _26589).
Proof. exact (MK_COMB (@lem1128852 _26588) (@lem1128851 _26588 _26589)). Qed.
Lemma lem1128854 {_26588 _26589 : Type'} : (term67 _26588 _26589) = (term93 _26588 _26589).
Proof. exact (MK_COMB (@lem1128849 _26588 _26589) (@lem1128853 _26588 _26589)). Qed.
Lemma lem1128855 {_26588 _26589 : Type'} : term93 _26588 _26589.
Proof. exact (EQ_MP (@lem1128854 _26588 _26589) (@lem1128832 _26588 _26589)). Qed.
Lemma lem1128858 {A : Type'} (P : type1143 A) : term0 A P.
Proof. exact (EQ_MP (@lem1094347 A P) (@lem1094346 A P)). Qed.
Lemma lem1128859 {_26588 : Type'} (P : type1143 _26588) : term0 _26588 P.
Proof. exact (@lem1128858 _26588 P). Qed.
Lemma lem1128860 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : term94 _26588 _26589 h t.
Proof. exact (@lem1128859 _26588 (term65 _26588 _26589 h t)). Qed.
Lemma lem1128861 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term95 _26588 _26589 h t) = (term96 _26588 _26589 h t).
Proof. exact (eq_refl (term95 _26588 _26589 h t)). Qed.
Lemma lem1128862 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1128863 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term97 _26588 _26589 h t) = (term98 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128862) (@lem1128861 _26588 _26589 h t)). Qed.
Lemma lem1128864 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (t' : list _26588) : (term99 _26588 _26589 h t t') = (term63 _26588 _26589 h t t').
Proof. exact (eq_refl (term99 _26588 _26589 h t t')). Qed.
Lemma lem1128865 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128866 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (t' : list _26588) : (term100 _26588 _26589 h t t') = (term101 _26588 _26589 h t t').
Proof. exact (MK_COMB (@lem1128865) (@lem1128864 _26588 _26589 h t t')). Qed.
Lemma lem1128867 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h' : _26588) (t' : list _26588) : (term102 _26588 _26589 h t h' t') = (term103 _26588 _26589 h t h' t').
Proof. exact (eq_refl (term102 _26588 _26589 h t h' t')). Qed.
Lemma lem1128868 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h' : _26588) (t' : list _26588) : (term104 _26588 _26589 h t h' t') = (term105 _26588 _26589 h t h' t').
Proof. exact (MK_COMB (@lem1128866 _26588 _26589 h t t') (@lem1128867 _26588 _26589 h t h' t')). Qed.
Lemma lem1128869 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h' : _26588) : (term106 _26588 _26589 h t h') = (term107 _26588 _26589 h t h').
Proof. exact (fun_ext (fun t' : list _26588 => @lem1128868 _26588 _26589 h t h' t')). Qed.
Lemma lem1128870 {_26588 : Type'} : (@all (list _26588)) = (@all (list _26588)).
Proof. exact (eq_refl (@all (list _26588))). Qed.
Lemma lem1128871 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h' : _26588) : (term108 _26588 _26589 h t h') = (term109 _26588 _26589 h t h').
Proof. exact (MK_COMB (@lem1128870 _26588) (@lem1128869 _26588 _26589 h t h')). Qed.
Lemma lem1128872 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term110 _26588 _26589 h t) = (term111 _26588 _26589 h t).
Proof. exact (fun_ext (fun h' : _26588 => @lem1128871 _26588 _26589 h t h')). Qed.
Lemma lem1128873 {_26588 : Type'} : (@all _26588) = (@all _26588).
Proof. exact (eq_refl (@all _26588)). Qed.
Lemma lem1128874 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term112 _26588 _26589 h t) = (term113 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128873 _26588) (@lem1128872 _26588 _26589 h t)). Qed.
Lemma lem1128875 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term114 _26588 _26589 h t) = (term115 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128863 _26588 _26589 h t) (@lem1128874 _26588 _26589 h t)). Qed.
Lemma lem1128876 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1128877 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term116 _26588 _26589 h t) = (term117 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128876) (@lem1128875 _26588 _26589 h t)). Qed.
Lemma lem1128878 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (m : list _26588) : (term99 _26588 _26589 h t m) = (term63 _26588 _26589 h t m).
Proof. exact (eq_refl (term99 _26588 _26589 h t m)). Qed.
Lemma lem1128879 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term118 _26588 _26589 h t) = (term65 _26588 _26589 h t).
Proof. exact (fun_ext (fun m : list _26588 => @lem1128878 _26588 _26589 h t m)). Qed.
Lemma lem1128880 {_26588 : Type'} : (@all (list _26588)) = (@all (list _26588)).
Proof. exact (eq_refl (@all (list _26588))). Qed.
Lemma lem1128881 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term119 _26588 _26589 h t) = (term66 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128880 _26588) (@lem1128879 _26588 _26589 h t)). Qed.
Lemma lem1128882 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term94 _26588 _26589 h t) = (term120 _26588 _26589 h t).
Proof. exact (MK_COMB (@lem1128877 _26588 _26589 h t) (@lem1128881 _26588 _26589 h t)). Qed.
Lemma lem1128883 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : term120 _26588 _26589 h t.
Proof. exact (EQ_MP (@lem1128882 _26588 _26589 h t) (@lem1128860 _26588 _26589 h t)). Qed.
Lemma lem1128904 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1128905 {_26588 _26589 : Type'} (P : type1470 _26588 _26589) : (@ALL2 _26589 _26588 P (@nil _26589) (@nil _26588)) = True.
Proof. exact (@lem1128904 _26588 _26589 P). Qed.
Lemma lem1128906 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) : (term121 _26588 _26589 P Q) = True.
Proof. exact (@lem1128905 _26588 _26589 (term122 _26588 _26589 P Q)). Qed.
Lemma lem1128907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1128908 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) : (term123 _26588 _26589 P Q) = (@eq Prop True).
Proof. exact (MK_COMB (@lem1128907) (@lem1128906 _26588 _26589 P Q)). Qed.
Lemma lem1128910 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) : (@ALL2 _25471 _25470 P (@nil _25471) (@nil _25470)) = True.
Proof. exact (proj1 (@lem1104212 _25470 _25471 (@el _25471) (@el _25470) P (@el (list _25471)) (@el (list _25470)))). Qed.
Lemma lem1128911 {_26588 _26589 : Type'} (P : type1470 _26588 _26589) : (@ALL2 _26589 _26588 P (@nil _26589) (@nil _26588)) = True.
Proof. exact (@lem1128910 _26588 _26589 P). Qed.
Lemma lem1128912 {_26588 _26589 : Type'} (Q : type1470 _26588 _26589) : (@ALL2 _26589 _26588 Q (@nil _26589) (@nil _26588)) = True.
Proof. exact (@lem1128911 _26588 _26589 Q). Qed.
Lemma lem1128913 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) : ((term121 _26588 _26589 P Q) = (@ALL2 _26589 _26588 Q (@nil _26589) (@nil _26588))) = (True = True).
Proof. exact (MK_COMB (@lem1128908 _26588 _26589 P Q) (@lem1128912 _26588 _26589 Q)). Qed.
Lemma lem1128915 (t : Prop) : (True = t) = t.
Proof. exact (proj1 (@lem1855 t)). Qed.
Lemma lem1128916 : (True = True) = True.
Proof. exact (@lem1128915 True). Qed.
Lemma lem1128917 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) : ((term121 _26588 _26589 P Q) = (@ALL2 _26589 _26588 Q (@nil _26589) (@nil _26588))) = True.
Proof. exact (TRANS (@lem1128913 _26588 _26589 P Q) (@lem1128916)). Qed.
Lemma lem1128918 {_26588 _26589 : Type'} (P : _26589 -> Prop) : (term124 _26588 _26589 P) = (term125 _26588 _26589).
Proof. exact (fun_ext (fun Q : type1470 _26588 _26589 => @lem1128917 _26588 _26589 P Q)). Qed.
Lemma lem1128919 {_26588 _26589 : Type'} : (@all (_26589 -> _26588 -> Prop)) = (@all (_26589 -> _26588 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> _26588 -> Prop))). Qed.
Lemma lem1128920 {_26588 _26589 : Type'} (P : _26589 -> Prop) : (term126 _26588 _26589 P) = (term127 _26588 _26589).
Proof. exact (MK_COMB (@lem1128919 _26588 _26589) (@lem1128918 _26588 _26589 P)). Qed.
Lemma lem1128922 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1128923 {_26588 _26589 : Type'} (t : Prop) : (term129 _26588 _26589 t) = t.
Proof. exact (@lem1128922 (type1470 _26588 _26589) t). Qed.
Lemma lem1128924 {_26588 _26589 : Type'} : (term127 _26588 _26589) = True.
Proof. exact (@lem1128923 _26588 _26589 True). Qed.
Lemma lem1128925 {_26588 _26589 : Type'} (P : _26589 -> Prop) : (term126 _26588 _26589 P) = True.
Proof. exact (TRANS (@lem1128920 _26588 _26589 P) (@lem1128924 _26588 _26589)). Qed.
Lemma lem1128926 {_26588 _26589 : Type'} : (term130 _26588 _26589) = (term131 _26589).
Proof. exact (fun_ext (fun P : _26589 -> Prop => @lem1128925 _26588 _26589 P)). Qed.
Lemma lem1128927 {_26589 : Type'} : (@all (_26589 -> Prop)) = (@all (_26589 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> Prop))). Qed.
Lemma lem1128928 {_26588 _26589 : Type'} : (term69 _26588 _26589) = (term132 _26589).
Proof. exact (MK_COMB (@lem1128927 _26589) (@lem1128926 _26588 _26589)). Qed.
Lemma lem1128930 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1128931 {_26589 : Type'} (t : Prop) : (term133 _26589 t) = t.
Proof. exact (@lem1128930 (_26589 -> Prop) t). Qed.
Lemma lem1128932 {_26589 : Type'} : (term132 _26589) = True.
Proof. exact (@lem1128931 _26589 True). Qed.
Lemma lem1128933 {_26588 _26589 : Type'} : (term69 _26588 _26589) = True.
Proof. exact (TRANS (@lem1128928 _26588 _26589) (@lem1128932 _26589)). Qed.
Lemma lem1128934 {_26588 _26589 : Type'} : True = (term69 _26588 _26589).
Proof. exact (SYM (@lem1128933 _26588 _26589)). Qed.
Lemma lem1128935 {_26588 _26589 : Type'} : term69 _26588 _26589.
Proof. exact (EQ_MP (@lem1128934 _26588 _26589) (@lem0)). Qed.
Lemma lem1128936 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term134 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1128937 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term135 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1128936 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1128961 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term136 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1128937 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1128962 {_26588 _26589 : Type'} (P : type1470 _26588 _26589) (h2' : _26588) (t2 : list _26588) : (term136 _26588 _26589 P h2' t2) = False.
Proof. exact (@lem1128961 _26588 _26589 P h2' t2). Qed.
Lemma lem1128963 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26588) (t : list _26588) : (term137 _26588 _26589 P Q h t) = False.
Proof. exact (@lem1128962 _26588 _26589 (term122 _26588 _26589 P Q) h t). Qed.
Lemma lem1128964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1128965 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26588) (t : list _26588) : (term138 _26588 _26589 P Q h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1128964) (@lem1128963 _26588 _26589 P Q h t)). Qed.
Lemma lem1128967 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h2' : _25470) (t2 : list _25470) : (term136 _25470 _25471 P h2' t2) = False.
Proof. exact (proj1 (@lem1128937 _25470 _25471 (@el _25471) h2' P (@el (list _25471)) t2)). Qed.
Lemma lem1128968 {_26588 _26589 : Type'} (P : type1470 _26588 _26589) (h2' : _26588) (t2 : list _26588) : (term136 _26588 _26589 P h2' t2) = False.
Proof. exact (@lem1128967 _26588 _26589 P h2' t2). Qed.
Lemma lem1128969 {_26588 _26589 : Type'} (Q : type1470 _26588 _26589) (h : _26588) (t : list _26588) : (term136 _26588 _26589 Q h t) = False.
Proof. exact (@lem1128968 _26588 _26589 Q h t). Qed.
Lemma lem1128970 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26588) (t : list _26588) : ((term137 _26588 _26589 P Q h t) = (term136 _26588 _26589 Q h t)) = (False = False).
Proof. exact (MK_COMB (@lem1128965 _26588 _26589 P Q h t) (@lem1128969 _26588 _26589 Q h t)). Qed.
Lemma lem1128972 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1128973 : (False = False) = (~ False).
Proof. exact (@lem1128972 False). Qed.
Lemma lem1128975 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1128976 : (False = False) = True.
Proof. exact (TRANS (@lem1128973) (@lem1128975)). Qed.
Lemma lem1128977 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26588) (t : list _26588) : ((term137 _26588 _26589 P Q h t) = (term136 _26588 _26589 Q h t)) = True.
Proof. exact (TRANS (@lem1128970 _26588 _26589 P Q h t) (@lem1128976)). Qed.
Lemma lem1128978 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26588) (t : list _26588) : (term139 _26588 _26589 P h t) = (term125 _26588 _26589).
Proof. exact (fun_ext (fun Q : type1470 _26588 _26589 => @lem1128977 _26588 _26589 P Q h t)). Qed.
Lemma lem1128979 {_26588 _26589 : Type'} : (@all (_26589 -> _26588 -> Prop)) = (@all (_26589 -> _26588 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> _26588 -> Prop))). Qed.
Lemma lem1128980 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26588) (t : list _26588) : (term140 _26588 _26589 P h t) = (term127 _26588 _26589).
Proof. exact (MK_COMB (@lem1128979 _26588 _26589) (@lem1128978 _26588 _26589 P h t)). Qed.
Lemma lem1128982 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1128983 {_26588 _26589 : Type'} (t : Prop) : (term129 _26588 _26589 t) = t.
Proof. exact (@lem1128982 (type1470 _26588 _26589) t). Qed.
Lemma lem1128984 {_26588 _26589 : Type'} : (term127 _26588 _26589) = True.
Proof. exact (@lem1128983 _26588 _26589 True). Qed.
Lemma lem1128985 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26588) (t : list _26588) : (term140 _26588 _26589 P h t) = True.
Proof. exact (TRANS (@lem1128980 _26588 _26589 P h t) (@lem1128984 _26588 _26589)). Qed.
Lemma lem1128986 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : (term141 _26588 _26589 h t) = (term131 _26589).
Proof. exact (fun_ext (fun P : _26589 -> Prop => @lem1128985 _26588 _26589 P h t)). Qed.
Lemma lem1128987 {_26589 : Type'} : (@all (_26589 -> Prop)) = (@all (_26589 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> Prop))). Qed.
Lemma lem1128988 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : (term76 _26588 _26589 h t) = (term132 _26589).
Proof. exact (MK_COMB (@lem1128987 _26589) (@lem1128986 _26588 _26589 h t)). Qed.
Lemma lem1128990 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1128991 {_26589 : Type'} (t : Prop) : (term133 _26589 t) = t.
Proof. exact (@lem1128990 (_26589 -> Prop) t). Qed.
Lemma lem1128992 {_26589 : Type'} : (term132 _26589) = True.
Proof. exact (@lem1128991 _26589 True). Qed.
Lemma lem1128993 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : (term76 _26588 _26589 h t) = True.
Proof. exact (TRANS (@lem1128988 _26588 _26589 h t) (@lem1128992 _26589)). Qed.
Lemma lem1128994 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : True = (term76 _26588 _26589 h t).
Proof. exact (SYM (@lem1128993 _26588 _26589 h t)). Qed.
Lemma lem1128995 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : term76 _26588 _26589 h t.
Proof. exact (EQ_MP (@lem1128994 _26588 _26589 h t) (@lem0)). Qed.
Lemma lem1128996 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term134 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1129024 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term142 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1128996 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1129025 {_26588 _26589 : Type'} (P : type1470 _26588 _26589) (h1' : _26589) (t1 : list _26589) : (term142 _26588 _26589 P h1' t1) = False.
Proof. exact (@lem1129024 _26588 _26589 P h1' t1). Qed.
Lemma lem1129026 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) : (term143 _26588 _26589 P Q h t) = False.
Proof. exact (@lem1129025 _26588 _26589 (term122 _26588 _26589 P Q) h t). Qed.
Lemma lem1129027 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129028 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) : (term144 _26588 _26589 P Q h t) = (@eq Prop False).
Proof. exact (MK_COMB (@lem1129027) (@lem1129026 _26588 _26589 P Q h t)). Qed.
Lemma lem1129034 {_25470 _25471 : Type'} (P : type1470 _25470 _25471) (h1' : _25471) (t1 : list _25471) : (term142 _25470 _25471 P h1' t1) = False.
Proof. exact (proj1 (@lem1128996 _25470 _25471 h1' (@el _25470) P t1 (@el (list _25470)))). Qed.
Lemma lem1129035 {_26588 _26589 : Type'} (P : type1470 _26588 _26589) (h1' : _26589) (t1 : list _26589) : (term142 _26588 _26589 P h1' t1) = False.
Proof. exact (@lem1129034 _26588 _26589 P h1' t1). Qed.
Lemma lem1129036 {_26588 _26589 : Type'} (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) : (term142 _26588 _26589 Q h t) = False.
Proof. exact (@lem1129035 _26588 _26589 Q h t). Qed.
Lemma lem1129037 {_26589 : Type'} (h : _26589) (P : _26589 -> Prop) (t : list _26589) : (term50 _26589 h P t) = (term50 _26589 h P t).
Proof. exact (eq_refl (term50 _26589 h P t)). Qed.
Lemma lem1129038 {_26588 _26589 : Type'} (Q : type1470 _26588 _26589) (h : _26589) (P : _26589 -> Prop) (t : list _26589) : (term145 _26588 _26589 P Q h t) = (term146 _26589 h P t).
Proof. exact (MK_COMB (@lem1129037 _26589 h P t) (@lem1129036 _26588 _26589 Q h t)). Qed.
Lemma lem1129040 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem1129041 {_26589 : Type'} (h : _26589) (P : _26589 -> Prop) (t : list _26589) : (term146 _26589 h P t) = False.
Proof. exact (@lem1129040 (term48 _26589 h P t)). Qed.
Lemma lem1129042 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) : (term145 _26588 _26589 P Q h t) = False.
Proof. exact (TRANS (@lem1129038 _26588 _26589 Q h P t) (@lem1129041 _26589 h P t)). Qed.
Lemma lem1129043 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) : ((term143 _26588 _26589 P Q h t) = (term145 _26588 _26589 P Q h t)) = (False = False).
Proof. exact (MK_COMB (@lem1129028 _26588 _26589 P Q h t) (@lem1129042 _26588 _26589 P Q h t)). Qed.
Lemma lem1129045 (t : Prop) : (False = t) = (~ t).
Proof. exact (proj1 (@lem1857 t)). Qed.
Lemma lem1129046 : (False = False) = (~ False).
Proof. exact (@lem1129045 False). Qed.
Lemma lem1129048 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem1129049 : (False = False) = True.
Proof. exact (TRANS (@lem1129046) (@lem1129048)). Qed.
Lemma lem1129050 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (t : list _26589) : ((term143 _26588 _26589 P Q h t) = (term145 _26588 _26589 P Q h t)) = True.
Proof. exact (TRANS (@lem1129043 _26588 _26589 P Q h t) (@lem1129049)). Qed.
Lemma lem1129051 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (t : list _26589) : (term147 _26588 _26589 P h t) = (term125 _26588 _26589).
Proof. exact (fun_ext (fun Q : type1470 _26588 _26589 => @lem1129050 _26588 _26589 P Q h t)). Qed.
Lemma lem1129052 {_26588 _26589 : Type'} : (@all (_26589 -> _26588 -> Prop)) = (@all (_26589 -> _26588 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> _26588 -> Prop))). Qed.
Lemma lem1129053 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (t : list _26589) : (term148 _26588 _26589 P h t) = (term127 _26588 _26589).
Proof. exact (MK_COMB (@lem1129052 _26588 _26589) (@lem1129051 _26588 _26589 P h t)). Qed.
Lemma lem1129055 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1129056 {_26588 _26589 : Type'} (t : Prop) : (term129 _26588 _26589 t) = t.
Proof. exact (@lem1129055 (type1470 _26588 _26589) t). Qed.
Lemma lem1129057 {_26588 _26589 : Type'} : (term127 _26588 _26589) = True.
Proof. exact (@lem1129056 _26588 _26589 True). Qed.
Lemma lem1129058 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (t : list _26589) : (term148 _26588 _26589 P h t) = True.
Proof. exact (TRANS (@lem1129053 _26588 _26589 P h t) (@lem1129057 _26588 _26589)). Qed.
Lemma lem1129059 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term149 _26588 _26589 h t) = (term131 _26589).
Proof. exact (fun_ext (fun P : _26589 -> Prop => @lem1129058 _26588 _26589 P h t)). Qed.
Lemma lem1129060 {_26589 : Type'} : (@all (_26589 -> Prop)) = (@all (_26589 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> Prop))). Qed.
Lemma lem1129061 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term96 _26588 _26589 h t) = (term132 _26589).
Proof. exact (MK_COMB (@lem1129060 _26589) (@lem1129059 _26588 _26589 h t)). Qed.
Lemma lem1129063 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1129064 {_26589 : Type'} (t : Prop) : (term133 _26589 t) = t.
Proof. exact (@lem1129063 (_26589 -> Prop) t). Qed.
Lemma lem1129065 {_26589 : Type'} : (term132 _26589) = True.
Proof. exact (@lem1129064 _26589 True). Qed.
Lemma lem1129066 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : (term96 _26588 _26589 h t) = True.
Proof. exact (TRANS (@lem1129061 _26588 _26589 h t) (@lem1129065 _26589)). Qed.
Lemma lem1129067 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : True = (term96 _26588 _26589 h t).
Proof. exact (SYM (@lem1129066 _26588 _26589 h t)). Qed.
Lemma lem1129068 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : term96 _26588 _26589 h t.
Proof. exact (EQ_MP (@lem1129067 _26588 _26589 h t) (@lem0)). Qed.
Lemma lem1129069 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term134 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1104212 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1129070 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : term135 _25470 _25471 h1' h2' P t1 t2.
Proof. exact (proj2 (@lem1129069 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1129077 {_26588 _26589 : Type'} (m : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : term150 _26588 _26589 t m.
Proof. exact (@lem1128693 _26588 _26589 t h1 m). Qed.
Lemma lem1129078 {_26588 _26589 : Type'} (t : list _26589) (m : list _26588) : (term150 _26588 _26589 t m) = (term151 _26588 _26589 t m).
Proof. exact (eq_refl (term150 _26588 _26589 t m)). Qed.
Lemma lem1129079 {_26588 _26589 : Type'} (m : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : term151 _26588 _26589 t m.
Proof. exact (EQ_MP (@lem1129078 _26588 _26589 t m) (@lem1129077 _26588 _26589 m t h1)). Qed.
Lemma lem1129080 {_26588 _26589 : Type'} (m : list _26588) (P : _26589 -> Prop) (t : list _26589) (h1 : term8 _26588 _26589 t) : term152 _26588 _26589 t m P.
Proof. exact (@lem1129079 _26588 _26589 m t h1 P). Qed.
Lemma lem1129081 {_26588 _26589 : Type'} (P : _26589 -> Prop) (t : list _26589) (m : list _26588) : (term152 _26588 _26589 t m P) = (term153 _26588 _26589 P t m).
Proof. exact (eq_refl (term152 _26588 _26589 t m P)). Qed.
Lemma lem1129082 {_26588 _26589 : Type'} (P : _26589 -> Prop) (m : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : term153 _26588 _26589 P t m.
Proof. exact (EQ_MP (@lem1129081 _26588 _26589 P t m) (@lem1129080 _26588 _26589 m P t h1)). Qed.
Lemma lem1129083 {_26588 _26589 : Type'} (P : _26589 -> Prop) (m : list _26588) (Q : type1470 _26588 _26589) (t : list _26589) (h1 : term8 _26588 _26589 t) : term154 _26588 _26589 P t m Q.
Proof. exact (@lem1129082 _26588 _26589 P m t h1 Q). Qed.
Lemma lem1129084 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (m : list _26588) : (term154 _26588 _26589 P t m Q) = ((term155 _26588 _26589 P Q t m) = (term156 _26588 _26589 P Q t m)).
Proof. exact (eq_refl (term154 _26588 _26589 P t m Q)). Qed.
Lemma lem1129103 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term157 _25470 _25471 P h1' t1 h2' t2) = (term158 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1129070 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1129104 {_26588 _26589 : Type'} (h1' : _26589) (h2' : _26588) (P : type1470 _26588 _26589) (t1 : list _26589) (t2 : list _26588) : (term157 _26588 _26589 P h1' t1 h2' t2) = (term158 _26588 _26589 h1' h2' P t1 t2).
Proof. exact (@lem1129103 _26588 _26589 h1' h2' P t1 t2). Qed.
Lemma lem1129105 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term159 _26588 _26589 P Q h t h' t') = (term160 _26588 _26589 h h' P Q t t').
Proof. exact (@lem1129104 _26588 _26589 h h' (term122 _26588 _26589 P Q) t t'). Qed.
Lemma lem1129109 {A B : Type'} (f : A -> B) (y : A) : (term161 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1129110 {_26588 _26589 : Type'} (f : type1470 _26588 _26589) (y : _26589) : (term162 _26588 _26589 f y) = (f y).
Proof. exact (@lem1129109 _26589 (_26588 -> Prop) f y). Qed.
Lemma lem1129111 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) : (term163 _26588 _26589 P Q h) = (term164 _26588 _26589 P Q h).
Proof. exact (@lem1129110 _26588 _26589 (term122 _26588 _26589 P Q) h). Qed.
Lemma lem1129112 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (x : _26589) : (term164 _26588 _26589 P Q x) = (term165 _26588 _26589 P Q x).
Proof. exact (eq_refl (term164 _26588 _26589 P Q x)). Qed.
Lemma lem1129113 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) : (term166 _26588 _26589 P Q) = (term122 _26588 _26589 P Q).
Proof. exact (fun_ext (fun x : _26589 => @lem1129112 _26588 _26589 P Q x)). Qed.
Lemma lem1129114 {_26589 : Type'} (h : _26589) : h = h.
Proof. exact (eq_refl h). Qed.
Lemma lem1129115 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) : (term163 _26588 _26589 P Q h) = (term164 _26588 _26589 P Q h).
Proof. exact (MK_COMB (@lem1129113 _26588 _26589 P Q) (@lem1129114 _26589 h)). Qed.
Lemma lem1129116 {_26588 : Type'} : (@eq (_26588 -> Prop)) = (@eq (_26588 -> Prop)).
Proof. exact (eq_refl (@eq (_26588 -> Prop))). Qed.
Lemma lem1129117 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) : (term167 _26588 _26589 P Q h) = (term168 _26588 _26589 P Q h).
Proof. exact (MK_COMB (@lem1129116 _26588) (@lem1129115 _26588 _26589 P Q h)). Qed.
Lemma lem1129118 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) : (term164 _26588 _26589 P Q h) = (term165 _26588 _26589 P Q h).
Proof. exact (eq_refl (term164 _26588 _26589 P Q h)). Qed.
Lemma lem1129119 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) : ((term163 _26588 _26589 P Q h) = (term164 _26588 _26589 P Q h)) = ((term164 _26588 _26589 P Q h) = (term165 _26588 _26589 P Q h)).
Proof. exact (MK_COMB (@lem1129117 _26588 _26589 P Q h) (@lem1129118 _26588 _26589 P Q h)). Qed.
Lemma lem1129120 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) : (term164 _26588 _26589 P Q h) = (term165 _26588 _26589 P Q h).
Proof. exact (EQ_MP (@lem1129119 _26588 _26589 P Q h) (@lem1129111 _26588 _26589 P Q h)). Qed.
Lemma lem1129123 {_26588 : Type'} (h' : _26588) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1129124 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term169 _26588 _26589 P Q h h') = (term170 _26588 _26589 P Q h h').
Proof. exact (MK_COMB (@lem1129120 _26588 _26589 P Q h) (@lem1129123 _26588 h')). Qed.
Lemma lem1129126 {A B : Type'} (f : A -> B) (y : A) : (term161 A B f y) = (f y).
Proof. exact (EQ_MP (@lem1810 A B f y) (@lem1809 A B f y)). Qed.
Lemma lem1129127 {_26588 : Type'} (f : _26588 -> Prop) (y : _26588) : (term171 _26588 f y) = (f y).
Proof. exact (@lem1129126 _26588 Prop f y). Qed.
Lemma lem1129128 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term172 _26588 _26589 P Q h h') = (term170 _26588 _26589 P Q h h').
Proof. exact (@lem1129127 _26588 (term165 _26588 _26589 P Q h) h'). Qed.
Lemma lem1129129 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (y : _26588) : (term170 _26588 _26589 P Q h y) = (term173 _26588 _26589 P Q h y).
Proof. exact (eq_refl (term170 _26588 _26589 P Q h y)). Qed.
Lemma lem1129130 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) : (term174 _26588 _26589 P Q h) = (term165 _26588 _26589 P Q h).
Proof. exact (fun_ext (fun y : _26588 => @lem1129129 _26588 _26589 P Q h y)). Qed.
Lemma lem1129131 {_26588 : Type'} (h' : _26588) : h' = h'.
Proof. exact (eq_refl h'). Qed.
Lemma lem1129132 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term172 _26588 _26589 P Q h h') = (term170 _26588 _26589 P Q h h').
Proof. exact (MK_COMB (@lem1129130 _26588 _26589 P Q h) (@lem1129131 _26588 h')). Qed.
Lemma lem1129133 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129134 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term175 _26588 _26589 P Q h h') = (term176 _26588 _26589 P Q h h').
Proof. exact (MK_COMB (@lem1129133) (@lem1129132 _26588 _26589 P Q h h')). Qed.
Lemma lem1129135 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term170 _26588 _26589 P Q h h') = (term173 _26588 _26589 P Q h h').
Proof. exact (eq_refl (term170 _26588 _26589 P Q h h')). Qed.
Lemma lem1129136 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : ((term172 _26588 _26589 P Q h h') = (term170 _26588 _26589 P Q h h')) = ((term170 _26588 _26589 P Q h h') = (term173 _26588 _26589 P Q h h')).
Proof. exact (MK_COMB (@lem1129134 _26588 _26589 P Q h h') (@lem1129135 _26588 _26589 P Q h h')). Qed.
Lemma lem1129137 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term170 _26588 _26589 P Q h h') = (term173 _26588 _26589 P Q h h').
Proof. exact (EQ_MP (@lem1129136 _26588 _26589 P Q h h') (@lem1129128 _26588 _26589 P Q h h')). Qed.
Lemma lem1129140 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term169 _26588 _26589 P Q h h') = (term173 _26588 _26589 P Q h h').
Proof. exact (TRANS (@lem1129124 _26588 _26589 P Q h h') (@lem1129137 _26588 _26589 P Q h h')). Qed.
Lemma lem1129141 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1129142 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (h : _26589) (h' : _26588) : (term177 _26588 _26589 P Q h h') = (term178 _26588 _26589 P Q h h').
Proof. exact (MK_COMB (@lem1129141) (@lem1129140 _26588 _26589 P Q h h')). Qed.
Lemma lem1129144 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (m : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term155 _26588 _26589 P Q t m) = (term156 _26588 _26589 P Q t m).
Proof. exact (EQ_MP (@lem1129084 _26588 _26589 P Q t m) (@lem1129083 _26588 _26589 P m Q t h1)). Qed.
Lemma lem1129145 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (m : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term155 _26588 _26589 P Q t m) = (term156 _26588 _26589 P Q t m).
Proof. exact (@lem1129144 _26588 _26589 P Q m t h1). Qed.
Lemma lem1129146 {_26588 _26589 : Type'} (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term155 _26588 _26589 P Q t t') = (term156 _26588 _26589 P Q t t').
Proof. exact (@lem1129145 _26588 _26589 P Q t' t h1). Qed.
Lemma lem1129149 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term160 _26588 _26589 h h' P Q t t') = (term179 _26588 _26589 h h' P Q t t').
Proof. exact (MK_COMB (@lem1129142 _26588 _26589 P Q h h') (@lem1129146 _26588 _26589 P Q t' t h1)). Qed.
Lemma lem1129152 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term159 _26588 _26589 P Q h t h' t') = (term179 _26588 _26589 h h' P Q t t').
Proof. exact (TRANS (@lem1129105 _26588 _26589 h h' P Q t t') (@lem1129149 _26588 _26589 h h' P Q t' t h1)). Qed.
Lemma lem1129153 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129154 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term180 _26588 _26589 P Q h t h' t') = (term181 _26588 _26589 h h' P Q t t').
Proof. exact (MK_COMB (@lem1129153) (@lem1129152 _26588 _26589 h h' P Q t' t h1)). Qed.
Lemma lem1129160 {_25470 _25471 : Type'} (h1' : _25471) (h2' : _25470) (P : type1470 _25470 _25471) (t1 : list _25471) (t2 : list _25470) : (term157 _25470 _25471 P h1' t1 h2' t2) = (term158 _25470 _25471 h1' h2' P t1 t2).
Proof. exact (proj2 (@lem1129070 _25470 _25471 h1' h2' P t1 t2)). Qed.
Lemma lem1129161 {_26588 _26589 : Type'} (h1' : _26589) (h2' : _26588) (P : type1470 _26588 _26589) (t1 : list _26589) (t2 : list _26588) : (term157 _26588 _26589 P h1' t1 h2' t2) = (term158 _26588 _26589 h1' h2' P t1 t2).
Proof. exact (@lem1129160 _26588 _26589 h1' h2' P t1 t2). Qed.
Lemma lem1129162 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term157 _26588 _26589 Q h t h' t') = (term158 _26588 _26589 h h' Q t t').
Proof. exact (@lem1129161 _26588 _26589 h h' Q t t'). Qed.
Lemma lem1129165 {_26589 : Type'} (h : _26589) (P : _26589 -> Prop) (t : list _26589) : (term50 _26589 h P t) = (term50 _26589 h P t).
Proof. exact (eq_refl (term50 _26589 h P t)). Qed.
Lemma lem1129166 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term182 _26588 _26589 P Q h t h' t') = (term183 _26588 _26589 P h h' Q t t').
Proof. exact (MK_COMB (@lem1129165 _26589 h P t) (@lem1129162 _26588 _26589 h h' Q t t')). Qed.
Lemma lem1129169 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (Q : type1470 _26588 _26589) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : ((term159 _26588 _26589 P Q h t h' t') = (term182 _26588 _26589 P Q h t h' t')) = ((term179 _26588 _26589 h h' P Q t t') = (term183 _26588 _26589 P h h' Q t t')).
Proof. exact (MK_COMB (@lem1129154 _26588 _26589 h h' P Q t' t h1) (@lem1129166 _26588 _26589 P h h' Q t t')). Qed.
Lemma lem1129172 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term184 _26588 _26589 P h t h' t') = (term185 _26588 _26589 P h h' t t').
Proof. exact (fun_ext (fun Q : type1470 _26588 _26589 => @lem1129169 _26588 _26589 P h h' Q t' t h1)). Qed.
Lemma lem1129173 {_26588 _26589 : Type'} : (@all (_26589 -> _26588 -> Prop)) = (@all (_26589 -> _26588 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> _26588 -> Prop))). Qed.
Lemma lem1129174 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term186 _26588 _26589 P h t h' t') = (term187 _26588 _26589 P h h' t t').
Proof. exact (MK_COMB (@lem1129173 _26588 _26589) (@lem1129172 _26588 _26589 P h h' t' t h1)). Qed.
Lemma lem1129179 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term188 _26588 _26589 h t h' t') = (term189 _26588 _26589 h h' t t').
Proof. exact (fun_ext (fun P : _26589 -> Prop => @lem1129174 _26588 _26589 P h h' t' t h1)). Qed.
Lemma lem1129180 {_26589 : Type'} : (@all (_26589 -> Prop)) = (@all (_26589 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> Prop))). Qed.
Lemma lem1129181 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term103 _26588 _26589 h t h' t') = (term190 _26588 _26589 h h' t t').
Proof. exact (MK_COMB (@lem1129180 _26589) (@lem1129179 _26588 _26589 h h' t' t h1)). Qed.
Lemma lem1129186 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : (term190 _26588 _26589 h h' t t') = (term103 _26588 _26589 h t h' t').
Proof. exact (SYM (@lem1129181 _26588 _26589 h h' t' t h1)). Qed.
Lemma lem1129198 (p : Prop) (q : Prop) (r : Prop) : (term191 p q r) = (term192 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
Lemma lem1129199 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term179 _26588 _26589 h h' P Q t t') = (term193 _26588 _26589 h h' P Q t t').
Proof. exact (@lem1129198 (P h) (Q h h') (term156 _26588 _26589 P Q t t')). Qed.
Lemma lem1129231 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem1129232 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term181 _26588 _26589 h h' P Q t t') = (term194 _26588 _26589 h h' P Q t t').
Proof. exact (MK_COMB (@lem1129231) (@lem1129199 _26588 _26589 h h' P Q t t')). Qed.
Lemma lem1129234 (p : Prop) (q : Prop) (r : Prop) : (term191 p q r) = (term192 p q r).
Proof. exact (EQ_MP (@lem586 p q r) (@lem585 p q r)). Qed.
Lemma lem1129235 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term183 _26588 _26589 P h h' Q t t') = (term195 _26588 _26589 P h h' Q t t').
Proof. exact (@lem1129234 (P h) (@List.Forall _26589 P t) (term158 _26588 _26589 h h' Q t t')). Qed.
Lemma lem1129251 (q : Prop) (p : Prop) (r : Prop) : (term192 p q r) = (term192 q p r).
Proof. exact (EQ_MP (@lem617 q p r) (@lem616 p q r)). Qed.
Lemma lem1129252 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term196 _26588 _26589 P h h' Q t t') = (term197 _26588 _26589 h h' P Q t t').
Proof. exact (@lem1129251 (Q h h') (@List.Forall _26589 P t) (@ALL2 _26589 _26588 Q t t')). Qed.
Lemma lem1129272 {_26589 : Type'} (P : _26589 -> Prop) (h : _26589) : (term198 _26589 P h) = (term198 _26589 P h).
Proof. exact (eq_refl (term198 _26589 P h)). Qed.
Lemma lem1129273 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term195 _26588 _26589 P h h' Q t t') = (term193 _26588 _26589 h h' P Q t t').
Proof. exact (MK_COMB (@lem1129272 _26589 P h) (@lem1129252 _26588 _26589 h h' P Q t t')). Qed.
Lemma lem1129286 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : (term183 _26588 _26589 P h h' Q t t') = (term193 _26588 _26589 h h' P Q t t').
Proof. exact (TRANS (@lem1129235 _26588 _26589 P h h' Q t t') (@lem1129273 _26588 _26589 h h' P Q t t')). Qed.
Lemma lem1129287 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : ((term179 _26588 _26589 h h' P Q t t') = (term183 _26588 _26589 P h h' Q t t')) = ((term193 _26588 _26589 h h' P Q t t') = (term193 _26588 _26589 h h' P Q t t')).
Proof. exact (MK_COMB (@lem1129232 _26588 _26589 h h' P Q t t') (@lem1129286 _26588 _26589 h h' P Q t t')). Qed.
Lemma lem1129289 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1129290 (x : Prop) : (x = x) = True.
Proof. exact (@lem1129289 Prop x). Qed.
Lemma lem1129291 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (P : _26589 -> Prop) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : ((term193 _26588 _26589 h h' P Q t t') = (term193 _26588 _26589 h h' P Q t t')) = True.
Proof. exact (@lem1129290 (term193 _26588 _26589 h h' P Q t t')). Qed.
Lemma lem1129292 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (Q : type1470 _26588 _26589) (t : list _26589) (t' : list _26588) : ((term179 _26588 _26589 h h' P Q t t') = (term183 _26588 _26589 P h h' Q t t')) = True.
Proof. exact (TRANS (@lem1129287 _26588 _26589 h h' P Q t t') (@lem1129291 _26588 _26589 h h' P Q t t')). Qed.
Lemma lem1129293 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : (term185 _26588 _26589 P h h' t t') = (term125 _26588 _26589).
Proof. exact (fun_ext (fun Q : type1470 _26588 _26589 => @lem1129292 _26588 _26589 P h h' Q t t')). Qed.
Lemma lem1129294 {_26588 _26589 : Type'} : (@all (_26589 -> _26588 -> Prop)) = (@all (_26589 -> _26588 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> _26588 -> Prop))). Qed.
Lemma lem1129295 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : (term187 _26588 _26589 P h h' t t') = (term127 _26588 _26589).
Proof. exact (MK_COMB (@lem1129294 _26588 _26589) (@lem1129293 _26588 _26589 P h h' t t')). Qed.
Lemma lem1129297 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1129298 {_26588 _26589 : Type'} (t : Prop) : (term129 _26588 _26589 t) = t.
Proof. exact (@lem1129297 (type1470 _26588 _26589) t). Qed.
Lemma lem1129299 {_26588 _26589 : Type'} : (term127 _26588 _26589) = True.
Proof. exact (@lem1129298 _26588 _26589 True). Qed.
Lemma lem1129300 {_26588 _26589 : Type'} (P : _26589 -> Prop) (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : (term187 _26588 _26589 P h h' t t') = True.
Proof. exact (TRANS (@lem1129295 _26588 _26589 P h h' t t') (@lem1129299 _26588 _26589)). Qed.
Lemma lem1129301 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : (term189 _26588 _26589 h h' t t') = (term131 _26589).
Proof. exact (fun_ext (fun P : _26589 -> Prop => @lem1129300 _26588 _26589 P h h' t t')). Qed.
Lemma lem1129302 {_26589 : Type'} : (@all (_26589 -> Prop)) = (@all (_26589 -> Prop)).
Proof. exact (eq_refl (@all (_26589 -> Prop))). Qed.
Lemma lem1129303 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : (term190 _26588 _26589 h h' t t') = (term132 _26589).
Proof. exact (MK_COMB (@lem1129302 _26589) (@lem1129301 _26588 _26589 h h' t t')). Qed.
Lemma lem1129305 {A : Type'} (t : Prop) : (term128 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem1129306 {_26589 : Type'} (t : Prop) : (term133 _26589 t) = t.
Proof. exact (@lem1129305 (_26589 -> Prop) t). Qed.
Lemma lem1129307 {_26589 : Type'} : (term132 _26589) = True.
Proof. exact (@lem1129306 _26589 True). Qed.
Lemma lem1129308 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : (term190 _26588 _26589 h h' t t') = True.
Proof. exact (TRANS (@lem1129303 _26588 _26589 h h' t t') (@lem1129307 _26589)). Qed.
Lemma lem1129309 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : True = (term190 _26588 _26589 h h' t t').
Proof. exact (SYM (@lem1129308 _26588 _26589 h h' t t')). Qed.
Lemma lem1129310 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t : list _26589) (t' : list _26588) : term190 _26588 _26589 h h' t t'.
Proof. exact (EQ_MP (@lem1129309 _26588 _26589 h h' t t') (@lem0)). Qed.
Lemma lem1129311 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : term103 _26588 _26589 h t h' t'.
Proof. exact (EQ_MP (@lem1129186 _26588 _26589 h h' t' t h1) (@lem1129310 _26588 _26589 h h' t t')). Qed.
Lemma lem1129312 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t' : list _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : term105 _26588 _26589 h t h' t'.
Proof. exact (fun h0 : term63 _26588 _26589 h t t' => @lem1129311 _26588 _26589 h h' t' t h1). Qed.
Lemma lem1129317 {_26588 _26589 : Type'} (h : _26589) (h' : _26588) (t : list _26589) (h1 : term8 _26588 _26589 t) : term109 _26588 _26589 h t h'.
Proof. exact (fun t' : list _26588 => @lem1129312 _26588 _26589 h h' t' t h1). Qed.
Lemma lem1129322 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h1 : term8 _26588 _26589 t) : term113 _26588 _26589 h t.
Proof. exact (fun h' : _26588 => @lem1129317 _26588 _26589 h h' t h1). Qed.
Lemma lem1129323 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h1 : term8 _26588 _26589 t) : term115 _26588 _26589 h t.
Proof. exact (conj (@lem1129068 _26588 _26589 h t) (@lem1129322 _26588 _26589 h t h1)). Qed.
Lemma lem1129324 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h1 : term8 _26588 _26589 t) : term66 _26588 _26589 h t.
Proof. exact (@lem1128883 _26588 _26589 h t (@lem1129323 _26588 _26589 h t h1)). Qed.
Lemma lem1129325 {_26588 _26589 : Type'} (h : _26588) (t : list _26588) : term78 _26588 _26589 h t.
Proof. exact (fun h0 : term43 _26588 _26589 t => @lem1128995 _26588 _26589 h t). Qed.
Lemma lem1129330 {_26588 _26589 : Type'} (h : _26588) : term82 _26588 _26589 h.
Proof. exact (fun t : list _26588 => @lem1129325 _26588 _26589 h t). Qed.
Lemma lem1129335 {_26588 _26589 : Type'} : term86 _26588 _26589.
Proof. exact (fun h : _26588 => @lem1129330 _26588 _26589 h). Qed.
Lemma lem1129336 {_26588 _26589 : Type'} : term88 _26588 _26589.
Proof. exact (conj (@lem1128935 _26588 _26589) (@lem1129335 _26588 _26589)). Qed.
Lemma lem1129337 {_26588 _26589 : Type'} : term46 _26588 _26589.
Proof. exact (@lem1128855 _26588 _26589 (@lem1129336 _26588 _26589)). Qed.
Lemma lem1129338 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) (h1 : term8 _26588 _26589 t) : term12 _26588 _26589 h t.
Proof. exact (EQ_MP (@lem1128828 _26588 _26589 h t) (@lem1129324 _26588 _26589 h t h1)). Qed.
Lemma lem1129339 {_26588 _26589 : Type'} : term4 _26588 _26589.
Proof. exact (EQ_MP (@lem1128756 _26588 _26589) (@lem1129337 _26588 _26589)). Qed.
Lemma lem1129340 {_26588 _26589 : Type'} (h : _26589) (t : list _26589) : term14 _26588 _26589 h t.
Proof. exact (fun h0 : term8 _26588 _26589 t => @lem1129338 _26588 _26589 h t h0). Qed.
Lemma lem1129345 {_26588 _26589 : Type'} (h : _26589) : term18 _26588 _26589 h.
Proof. exact (fun t : list _26589 => @lem1129340 _26588 _26589 h t). Qed.
Lemma lem1129350 {_26588 _26589 : Type'} : term22 _26588 _26589.
Proof. exact (fun h : _26589 => @lem1129345 _26588 _26589 h). Qed.
Lemma lem1129351 {_26588 _26589 : Type'} : term24 _26588 _26589.
Proof. exact (conj (@lem1129339 _26588 _26589) (@lem1129350 _26588 _26589)). Qed.
Lemma lem1129352 {_26588 _26589 : Type'} : term29 _26588 _26589.
Proof. exact (@lem1128692 _26588 _26589 (@lem1129351 _26588 _26589)). Qed.
