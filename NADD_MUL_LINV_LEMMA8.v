Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import NADD_MUL_LINV_LEMMA8_term_abbrevs.
Require Import ADD_ASSOC_spec.
Require Import ADD_SYM_spec.
Require Import BOUNDS_NOTZERO_spec.
Require Import DIST_REFL_spec.
Require Import DIST_SYM_spec.
Require Import LEFT_ADD_DISTRIB_spec.
Require Import LE_ADD_spec.
Require Import LE_ADD_RCANCEL_spec.
Require Import LE_CASES_spec.
Require Import LE_TRANS_spec.
Require Import NADD_MUL_LINV_LEMMA7_spec.
Require Import NADD_MUL_LINV_LEMMA7a_spec.
Require Import RIGHT_ADD_DISTRIB_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Lemma lem1306680 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1306681 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1306680 m n p h1)). Qed.
Lemma lem1306682 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1306683 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1306682 m n p h1)). Qed.
Lemma lem1306684 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1306681 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1306683 m n p h1)). Qed.
Lemma lem1306685 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1306684 m n p)). Qed.
Lemma lem1306686 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306687 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1306686) (@lem1306685 m n)). Qed.
Lemma lem1306688 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1306687 m n)). Qed.
Lemma lem1306689 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306690 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1306689) (@lem1306688 m)). Qed.
Lemma lem1306691 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1306690 m)). Qed.
Lemma lem1306692 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306693 : term12 = term13.
Proof. exact (MK_COMB (@lem1306692) (@lem1306691)). Qed.
Lemma lem1306694 : term13.
Proof. exact (EQ_MP (@lem1306693) (@lem77960)). Qed.
Lemma lem1306695 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1306696 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1306697 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1306696 m) (@lem1306695 m)). Qed.
Lemma lem1306698 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1306697 m n). Qed.
Lemma lem1306699 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1306700 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1306699 m n) (@lem1306698 m n)). Qed.
Lemma lem1306701 (m : nat) (n : nat) : (term17 m n) = ((term17 m n) = True).
Proof. exact (@lem7 (term17 m n)). Qed.
Lemma lem1306703 (m : nat) : term18 m.
Proof. exact (@lem1306694 m). Qed.
Lemma lem1306704 (m : nat) : (term18 m) = (term9 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1306705 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1306704 m) (@lem1306703 m)). Qed.
Lemma lem1306706 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1306705 m n). Qed.
Lemma lem1306707 (m : nat) (n : nat) : (term19 m n) = (term5 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1306708 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1306707 m n) (@lem1306706 m n)). Qed.
Lemma lem1306709 (m : nat) (n : nat) (p : nat) : term20 m n p.
Proof. exact (@lem1306708 m n p). Qed.
Lemma lem1306710 (m : nat) (n : nat) (p : nat) : (term20 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem1306712 (m : nat) : term21 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1306713 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1306714 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1306713 m) (@lem1306712 m)). Qed.
Lemma lem1306715 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1306714 m n). Qed.
Lemma lem1306716 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1306717 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1306716 m n) (@lem1306715 m n)). Qed.
Lemma lem1306718 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1306717 m n p). Qed.
Lemma lem1306719 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1306721 (m : nat) : term28 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1306722 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1306723 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1306722 m) (@lem1306721 m)). Qed.
Lemma lem1306724 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1306723 m n). Qed.
Lemma lem1306725 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1306726 (n : nat) (m : nat) : term31 n m.
Proof. exact (EQ_MP (@lem1306725 n m) (@lem1306724 m n)). Qed.
Lemma lem1306727 (n : nat) (m : nat) (p : nat) : term32 n m p.
Proof. exact (@lem1306726 n m p). Qed.
Lemma lem1306728 (n : nat) (m : nat) (p : nat) : (term32 n m p) = ((term33 m n p) = (term34 n m p)).
Proof. exact (eq_refl (term32 n m p)). Qed.
Lemma lem1306730 (m : nat) : term35 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1306731 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1306732 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1306731 m) (@lem1306730 m)). Qed.
Lemma lem1306733 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem1306732 m n). Qed.
Lemma lem1306734 (n : nat) (m : nat) : (term37 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1306736 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1306737 (m : nat) (h1 : term38) : term39 m.
Proof. exact (@lem1306736 h1 m). Qed.
Lemma lem1306738 (m : nat) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem1306739 (m : nat) (h1 : term38) : term40 m.
Proof. exact (EQ_MP (@lem1306738 m) (@lem1306737 m h1)). Qed.
Lemma lem1306740 (m : nat) (n : nat) (h1 : term38) : term41 m n.
Proof. exact (@lem1306739 m h1 n). Qed.
Lemma lem1306741 (n : nat) (m : nat) : (term41 m n) = (term42 n m).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem1306742 (n : nat) (m : nat) (h1 : term38) : term42 n m.
Proof. exact (EQ_MP (@lem1306741 n m) (@lem1306740 m n h1)). Qed.
Lemma lem1306743 (n : nat) (m : nat) (p : nat) (h1 : term38) : term43 n m p.
Proof. exact (@lem1306742 n m h1 p). Qed.
Lemma lem1306744 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term44 n m p).
Proof. exact (eq_refl (term43 n m p)). Qed.
Lemma lem1306745 (n : nat) (m : nat) (p : nat) (h1 : term38) : term44 n m p.
Proof. exact (EQ_MP (@lem1306744 n m p) (@lem1306743 n m p h1)). Qed.
Lemma lem1306746 (m : nat) (n : nat) (p : nat) (h1 : term45 m n p) : term45 m n p.
Proof. exact (h1). Qed.
Lemma lem1306747 (m : nat) (n : nat) (p : nat) (h1 : term38) (h2 : term45 m n p) : Peano.le m p.
Proof. exact (@lem1306745 n m p h1 (@lem1306746 m n p h2)). Qed.
Lemma lem1306748 (m : nat) (n : nat) (p : nat) (h1 : term45 m n p) : term46 m p.
Proof. exact (fun h0 : term38 => @lem1306747 m n p h0 h1). Qed.
Lemma lem1306749 (m : nat) (p : nat) (h1 : term47 m p) : term47 m p.
Proof. exact (h1). Qed.
Lemma lem1306750 (m : nat) (p : nat) (h1 : term47 m p) : term46 m p.
Proof. exact (ex_elim (@lem1306749 m p h1) (fun n : nat => fun h0 : term48 m p n => @lem1306748 m n p h0)). Qed.
Lemma lem1306751 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1306752 (m : nat) (p : nat) (h1 : term38) (h2 : term47 m p) : Peano.le m p.
Proof. exact (@lem1306750 m p h2 (@lem1306751 h1)). Qed.
Lemma lem1306753 (m : nat) (p : nat) (h1 : term38) : term49 m p.
Proof. exact (fun h0 : term47 m p => @lem1306752 m p h1 h0). Qed.
Lemma lem1306754 (m : nat) (h1 : term38) : term50 m.
Proof. exact (fun p : nat => @lem1306753 m p h1). Qed.
Lemma lem1306755 (h1 : term38) : term51.
Proof. exact (fun m : nat => @lem1306754 m h1). Qed.
Lemma lem1306756 : term52.
Proof. exact (fun h0 : term38 => @lem1306755 h0). Qed.
Lemma lem1306757 : term51.
Proof. exact (@lem1306756 (@lem93743)). Qed.
Lemma lem1306758 (m : nat) : term53 m.
Proof. exact (@lem1306757 m). Qed.
Lemma lem1306759 (m : nat) : (term53 m) = (term50 m).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem1306760 (m : nat) : term50 m.
Proof. exact (EQ_MP (@lem1306759 m) (@lem1306758 m)). Qed.
Lemma lem1306761 (m : nat) (p : nat) : term54 m p.
Proof. exact (@lem1306760 m p). Qed.
Lemma lem1306762 (m : nat) (p : nat) : (term54 m p) = (term49 m p).
Proof. exact (eq_refl (term54 m p)). Qed.
Lemma lem1306767 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1306768 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1306767 m n p h1)). Qed.
Lemma lem1306769 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1306770 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1306769 m n p h1)). Qed.
Lemma lem1306771 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1306768 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1306770 m n p h1)). Qed.
Lemma lem1306772 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1306771 m n p)). Qed.
Lemma lem1306773 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306774 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1306773) (@lem1306772 m n)). Qed.
Lemma lem1306775 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1306774 m n)). Qed.
Lemma lem1306776 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306777 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1306776) (@lem1306775 m)). Qed.
Lemma lem1306778 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1306777 m)). Qed.
Lemma lem1306779 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306780 : term12 = term13.
Proof. exact (MK_COMB (@lem1306779) (@lem1306778)). Qed.
Lemma lem1306781 : term13.
Proof. exact (EQ_MP (@lem1306780) (@lem77960)). Qed.
Lemma lem1306782 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1306783 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1306784 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1306783 m) (@lem1306782 m)). Qed.
Lemma lem1306785 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1306784 m n). Qed.
Lemma lem1306786 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1306787 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1306786 m n) (@lem1306785 m n)). Qed.
Lemma lem1306788 (m : nat) (n : nat) : (term17 m n) = ((term17 m n) = True).
Proof. exact (@lem7 (term17 m n)). Qed.
Lemma lem1306790 (m : nat) : term18 m.
Proof. exact (@lem1306781 m). Qed.
Lemma lem1306791 (m : nat) : (term18 m) = (term9 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1306792 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1306791 m) (@lem1306790 m)). Qed.
Lemma lem1306793 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1306792 m n). Qed.
Lemma lem1306794 (m : nat) (n : nat) : (term19 m n) = (term5 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1306795 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1306794 m n) (@lem1306793 m n)). Qed.
Lemma lem1306796 (m : nat) (n : nat) (p : nat) : term20 m n p.
Proof. exact (@lem1306795 m n p). Qed.
Lemma lem1306797 (m : nat) (n : nat) (p : nat) : (term20 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem1306799 (m : nat) : term21 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1306800 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1306801 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1306800 m) (@lem1306799 m)). Qed.
Lemma lem1306802 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1306801 m n). Qed.
Lemma lem1306803 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1306804 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1306803 m n) (@lem1306802 m n)). Qed.
Lemma lem1306805 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1306804 m n p). Qed.
Lemma lem1306806 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1306808 (m : nat) : term28 m.
Proof. exact (@lem82055 m). Qed.
Lemma lem1306809 (m : nat) : (term28 m) = (term29 m).
Proof. exact (eq_refl (term28 m)). Qed.
Lemma lem1306810 (m : nat) : term29 m.
Proof. exact (EQ_MP (@lem1306809 m) (@lem1306808 m)). Qed.
Lemma lem1306811 (m : nat) (n : nat) : term30 m n.
Proof. exact (@lem1306810 m n). Qed.
Lemma lem1306812 (n : nat) (m : nat) : (term30 m n) = (term31 n m).
Proof. exact (eq_refl (term30 m n)). Qed.
Lemma lem1306813 (n : nat) (m : nat) : term31 n m.
Proof. exact (EQ_MP (@lem1306812 n m) (@lem1306811 m n)). Qed.
Lemma lem1306814 (n : nat) (m : nat) (p : nat) : term32 n m p.
Proof. exact (@lem1306813 n m p). Qed.
Lemma lem1306815 (n : nat) (m : nat) (p : nat) : (term32 n m p) = ((term33 m n p) = (term34 n m p)).
Proof. exact (eq_refl (term32 n m p)). Qed.
Lemma lem1306817 (m : nat) : term55 m.
Proof. exact (@lem1244997 m). Qed.
Lemma lem1306818 (m : nat) : (term55 m) = (term56 m).
Proof. exact (eq_refl (term55 m)). Qed.
Lemma lem1306819 (m : nat) : term56 m.
Proof. exact (EQ_MP (@lem1306818 m) (@lem1306817 m)). Qed.
Lemma lem1306820 (m : nat) (n : nat) : term57 m n.
Proof. exact (@lem1306819 m n). Qed.
Lemma lem1306821 (n : nat) (m : nat) : (term57 m n) = ((term58 m n) = (term58 n m)).
Proof. exact (eq_refl (term57 m n)). Qed.
Lemma lem1306823 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1306824 (m : nat) (h1 : term38) : term39 m.
Proof. exact (@lem1306823 h1 m). Qed.
Lemma lem1306825 (m : nat) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem1306826 (m : nat) (h1 : term38) : term40 m.
Proof. exact (EQ_MP (@lem1306825 m) (@lem1306824 m h1)). Qed.
Lemma lem1306827 (m : nat) (n : nat) (h1 : term38) : term41 m n.
Proof. exact (@lem1306826 m h1 n). Qed.
Lemma lem1306828 (n : nat) (m : nat) : (term41 m n) = (term42 n m).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem1306829 (n : nat) (m : nat) (h1 : term38) : term42 n m.
Proof. exact (EQ_MP (@lem1306828 n m) (@lem1306827 m n h1)). Qed.
Lemma lem1306830 (n : nat) (m : nat) (p : nat) (h1 : term38) : term43 n m p.
Proof. exact (@lem1306829 n m h1 p). Qed.
Lemma lem1306831 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term44 n m p).
Proof. exact (eq_refl (term43 n m p)). Qed.
Lemma lem1306832 (n : nat) (m : nat) (p : nat) (h1 : term38) : term44 n m p.
Proof. exact (EQ_MP (@lem1306831 n m p) (@lem1306830 n m p h1)). Qed.
Lemma lem1306833 (m : nat) (n : nat) (p : nat) (h1 : term45 m n p) : term45 m n p.
Proof. exact (h1). Qed.
Lemma lem1306834 (m : nat) (n : nat) (p : nat) (h1 : term38) (h2 : term45 m n p) : Peano.le m p.
Proof. exact (@lem1306832 n m p h1 (@lem1306833 m n p h2)). Qed.
Lemma lem1306835 (m : nat) (n : nat) (p : nat) (h1 : term45 m n p) : term46 m p.
Proof. exact (fun h0 : term38 => @lem1306834 m n p h0 h1). Qed.
Lemma lem1306836 (m : nat) (p : nat) (h1 : term47 m p) : term47 m p.
Proof. exact (h1). Qed.
Lemma lem1306837 (m : nat) (p : nat) (h1 : term47 m p) : term46 m p.
Proof. exact (ex_elim (@lem1306836 m p h1) (fun n : nat => fun h0 : term48 m p n => @lem1306835 m n p h0)). Qed.
Lemma lem1306838 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1306839 (m : nat) (p : nat) (h1 : term38) (h2 : term47 m p) : Peano.le m p.
Proof. exact (@lem1306837 m p h2 (@lem1306838 h1)). Qed.
Lemma lem1306840 (m : nat) (p : nat) (h1 : term38) : term49 m p.
Proof. exact (fun h0 : term47 m p => @lem1306839 m p h1 h0). Qed.
Lemma lem1306841 (m : nat) (h1 : term38) : term50 m.
Proof. exact (fun p : nat => @lem1306840 m p h1). Qed.
Lemma lem1306842 (h1 : term38) : term51.
Proof. exact (fun m : nat => @lem1306841 m h1). Qed.
Lemma lem1306843 : term52.
Proof. exact (fun h0 : term38 => @lem1306842 h0). Qed.
Lemma lem1306844 : term51.
Proof. exact (@lem1306843 (@lem93743)). Qed.
Lemma lem1306845 (m : nat) : term53 m.
Proof. exact (@lem1306844 m). Qed.
Lemma lem1306846 (m : nat) : (term53 m) = (term50 m).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem1306847 (m : nat) : term50 m.
Proof. exact (EQ_MP (@lem1306846 m) (@lem1306845 m)). Qed.
Lemma lem1306848 (m : nat) (p : nat) : term54 m p.
Proof. exact (@lem1306847 m p). Qed.
Lemma lem1306849 (m : nat) (p : nat) : (term54 m p) = (term49 m p).
Proof. exact (eq_refl (term54 m p)). Qed.
Lemma lem1306854 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (h1). Qed.
Lemma lem1306855 (m : nat) (n : nat) (p : nat) (h1 : (term0 m n p) = (term1 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (SYM (@lem1306854 m n p h1)). Qed.
Lemma lem1306856 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term1 m n p) = (term0 m n p).
Proof. exact (h1). Qed.
Lemma lem1306857 (m : nat) (n : nat) (p : nat) (h1 : (term1 m n p) = (term0 m n p)) : (term0 m n p) = (term1 m n p).
Proof. exact (SYM (@lem1306856 m n p h1)). Qed.
Lemma lem1306858 (m : nat) (n : nat) (p : nat) : ((term0 m n p) = (term1 m n p)) = ((term1 m n p) = (term0 m n p)).
Proof. exact (prop_ext (fun h1 : (term0 m n p) = (term1 m n p) => @lem1306855 m n p h1) (fun h1 : (term1 m n p) = (term0 m n p) => @lem1306857 m n p h1)). Qed.
Lemma lem1306859 (m : nat) (n : nat) : (term2 m n) = (term3 m n).
Proof. exact (fun_ext (fun p : nat => @lem1306858 m n p)). Qed.
Lemma lem1306860 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306861 (m : nat) (n : nat) : (term4 m n) = (term5 m n).
Proof. exact (MK_COMB (@lem1306860) (@lem1306859 m n)). Qed.
Lemma lem1306862 (m : nat) : (term6 m) = (term7 m).
Proof. exact (fun_ext (fun n : nat => @lem1306861 m n)). Qed.
Lemma lem1306863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306864 (m : nat) : (term8 m) = (term9 m).
Proof. exact (MK_COMB (@lem1306863) (@lem1306862 m)). Qed.
Lemma lem1306865 : term10 = term11.
Proof. exact (fun_ext (fun m : nat => @lem1306864 m)). Qed.
Lemma lem1306866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1306867 : term12 = term13.
Proof. exact (MK_COMB (@lem1306866) (@lem1306865)). Qed.
Lemma lem1306868 : term13.
Proof. exact (EQ_MP (@lem1306867) (@lem77960)). Qed.
Lemma lem1306869 (m : nat) : term14 m.
Proof. exact (@lem100517 m). Qed.
Lemma lem1306870 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem1306871 (m : nat) : term15 m.
Proof. exact (EQ_MP (@lem1306870 m) (@lem1306869 m)). Qed.
Lemma lem1306872 (m : nat) (n : nat) : term16 m n.
Proof. exact (@lem1306871 m n). Qed.
Lemma lem1306873 (m : nat) (n : nat) : (term16 m n) = (term17 m n).
Proof. exact (eq_refl (term16 m n)). Qed.
Lemma lem1306874 (m : nat) (n : nat) : term17 m n.
Proof. exact (EQ_MP (@lem1306873 m n) (@lem1306872 m n)). Qed.
Lemma lem1306875 (m : nat) (n : nat) : (term17 m n) = ((term17 m n) = True).
Proof. exact (@lem7 (term17 m n)). Qed.
Lemma lem1306877 (m : nat) : term18 m.
Proof. exact (@lem1306868 m). Qed.
Lemma lem1306878 (m : nat) : (term18 m) = (term9 m).
Proof. exact (eq_refl (term18 m)). Qed.
Lemma lem1306879 (m : nat) : term9 m.
Proof. exact (EQ_MP (@lem1306878 m) (@lem1306877 m)). Qed.
Lemma lem1306880 (m : nat) (n : nat) : term19 m n.
Proof. exact (@lem1306879 m n). Qed.
Lemma lem1306881 (m : nat) (n : nat) : (term19 m n) = (term5 m n).
Proof. exact (eq_refl (term19 m n)). Qed.
Lemma lem1306882 (m : nat) (n : nat) : term5 m n.
Proof. exact (EQ_MP (@lem1306881 m n) (@lem1306880 m n)). Qed.
Lemma lem1306883 (m : nat) (n : nat) (p : nat) : term20 m n p.
Proof. exact (@lem1306882 m n p). Qed.
Lemma lem1306884 (m : nat) (n : nat) (p : nat) : (term20 m n p) = ((term1 m n p) = (term0 m n p)).
Proof. exact (eq_refl (term20 m n p)). Qed.
Lemma lem1306886 (m : nat) : term21 m.
Proof. exact (@lem82128 m). Qed.
Lemma lem1306887 (m : nat) : (term21 m) = (term22 m).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem1306888 (m : nat) : term22 m.
Proof. exact (EQ_MP (@lem1306887 m) (@lem1306886 m)). Qed.
Lemma lem1306889 (m : nat) (n : nat) : term23 m n.
Proof. exact (@lem1306888 m n). Qed.
Lemma lem1306890 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (eq_refl (term23 m n)). Qed.
Lemma lem1306891 (m : nat) (n : nat) : term24 m n.
Proof. exact (EQ_MP (@lem1306890 m n) (@lem1306889 m n)). Qed.
Lemma lem1306892 (m : nat) (n : nat) (p : nat) : term25 m n p.
Proof. exact (@lem1306891 m n p). Qed.
Lemma lem1306893 (m : nat) (n : nat) (p : nat) : (term25 m n p) = ((term26 m n p) = (term27 m n p)).
Proof. exact (eq_refl (term25 m n p)). Qed.
Lemma lem1306895 (m : nat) : term35 m.
Proof. exact (@lem77775 m). Qed.
Lemma lem1306896 (m : nat) : (term35 m) = (term36 m).
Proof. exact (eq_refl (term35 m)). Qed.
Lemma lem1306897 (m : nat) : term36 m.
Proof. exact (EQ_MP (@lem1306896 m) (@lem1306895 m)). Qed.
Lemma lem1306898 (m : nat) (n : nat) : term37 m n.
Proof. exact (@lem1306897 m n). Qed.
Lemma lem1306899 (n : nat) (m : nat) : (term37 m n) = ((Nat.add m n) = (Nat.add n m)).
Proof. exact (eq_refl (term37 m n)). Qed.
Lemma lem1306901 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1306902 (m : nat) (h1 : term38) : term39 m.
Proof. exact (@lem1306901 h1 m). Qed.
Lemma lem1306903 (m : nat) : (term39 m) = (term40 m).
Proof. exact (eq_refl (term39 m)). Qed.
Lemma lem1306904 (m : nat) (h1 : term38) : term40 m.
Proof. exact (EQ_MP (@lem1306903 m) (@lem1306902 m h1)). Qed.
Lemma lem1306905 (m : nat) (n : nat) (h1 : term38) : term41 m n.
Proof. exact (@lem1306904 m h1 n). Qed.
Lemma lem1306906 (n : nat) (m : nat) : (term41 m n) = (term42 n m).
Proof. exact (eq_refl (term41 m n)). Qed.
Lemma lem1306907 (n : nat) (m : nat) (h1 : term38) : term42 n m.
Proof. exact (EQ_MP (@lem1306906 n m) (@lem1306905 m n h1)). Qed.
Lemma lem1306908 (n : nat) (m : nat) (p : nat) (h1 : term38) : term43 n m p.
Proof. exact (@lem1306907 n m h1 p). Qed.
Lemma lem1306909 (n : nat) (m : nat) (p : nat) : (term43 n m p) = (term44 n m p).
Proof. exact (eq_refl (term43 n m p)). Qed.
Lemma lem1306910 (n : nat) (m : nat) (p : nat) (h1 : term38) : term44 n m p.
Proof. exact (EQ_MP (@lem1306909 n m p) (@lem1306908 n m p h1)). Qed.
Lemma lem1306911 (m : nat) (n : nat) (p : nat) (h1 : term45 m n p) : term45 m n p.
Proof. exact (h1). Qed.
Lemma lem1306912 (m : nat) (n : nat) (p : nat) (h1 : term38) (h2 : term45 m n p) : Peano.le m p.
Proof. exact (@lem1306910 n m p h1 (@lem1306911 m n p h2)). Qed.
Lemma lem1306913 (m : nat) (n : nat) (p : nat) (h1 : term45 m n p) : term46 m p.
Proof. exact (fun h0 : term38 => @lem1306912 m n p h0 h1). Qed.
Lemma lem1306914 (m : nat) (p : nat) (h1 : term47 m p) : term47 m p.
Proof. exact (h1). Qed.
Lemma lem1306915 (m : nat) (p : nat) (h1 : term47 m p) : term46 m p.
Proof. exact (ex_elim (@lem1306914 m p h1) (fun n : nat => fun h0 : term48 m p n => @lem1306913 m n p h0)). Qed.
Lemma lem1306916 (h1 : term38) : term38.
Proof. exact (h1). Qed.
Lemma lem1306917 (m : nat) (p : nat) (h1 : term38) (h2 : term47 m p) : Peano.le m p.
Proof. exact (@lem1306915 m p h2 (@lem1306916 h1)). Qed.
Lemma lem1306918 (m : nat) (p : nat) (h1 : term38) : term49 m p.
Proof. exact (fun h0 : term47 m p => @lem1306917 m p h1 h0). Qed.
Lemma lem1306919 (m : nat) (h1 : term38) : term50 m.
Proof. exact (fun p : nat => @lem1306918 m p h1). Qed.
Lemma lem1306920 (h1 : term38) : term51.
Proof. exact (fun m : nat => @lem1306919 m h1). Qed.
Lemma lem1306921 : term52.
Proof. exact (fun h0 : term38 => @lem1306920 h0). Qed.
Lemma lem1306922 : term51.
Proof. exact (@lem1306921 (@lem93743)). Qed.
Lemma lem1306923 (m : nat) : term53 m.
Proof. exact (@lem1306922 m). Qed.
Lemma lem1306924 (m : nat) : (term53 m) = (term50 m).
Proof. exact (eq_refl (term53 m)). Qed.
Lemma lem1306925 (m : nat) : term50 m.
Proof. exact (EQ_MP (@lem1306924 m) (@lem1306923 m)). Qed.
Lemma lem1306926 (m : nat) (p : nat) : term54 m p.
Proof. exact (@lem1306925 m p). Qed.
Lemma lem1306927 (m : nat) (p : nat) : (term54 m p) = (term49 m p).
Proof. exact (eq_refl (term54 m p)). Qed.
Lemma lem1306929 (N : nat) : term59 N.
Proof. exact (@lem96155 N). Qed.
Lemma lem1306930 (N : nat) : (term59 N) = (term60 N).
Proof. exact (eq_refl (term59 N)). Qed.
Lemma lem1306931 (N : nat) : term60 N.
Proof. exact (EQ_MP (@lem1306930 N) (@lem1306929 N)). Qed.
Lemma lem1306932 (N : nat) (n : nat) : term61 N n.
Proof. exact (@lem1306931 N n). Qed.
Lemma lem1306933 (n : nat) (N : nat) : (term61 N n) = (term62 n N).
Proof. exact (eq_refl (term61 N n)). Qed.
Lemma lem1306934 (n : nat) (N : nat) : term62 n N.
Proof. exact (EQ_MP (@lem1306933 n N) (@lem1306932 N n)). Qed.
Lemma lem1306935 (N : nat) (n : nat) (h1 : Peano.le N n) : Peano.le N n.
Proof. exact (h1). Qed.
Lemma lem1306936 (n : nat) (N : nat) (h1 : Peano.le n N) : Peano.le n N.
Proof. exact (h1). Qed.
Lemma lem1306937 (N : nat) : term59 N.
Proof. exact (@lem96155 N). Qed.
Lemma lem1306938 (N : nat) : (term59 N) = (term60 N).
Proof. exact (eq_refl (term59 N)). Qed.
Lemma lem1306939 (N : nat) : term60 N.
Proof. exact (EQ_MP (@lem1306938 N) (@lem1306937 N)). Qed.
Lemma lem1306940 (N : nat) (m : nat) : term61 N m.
Proof. exact (@lem1306939 N m). Qed.
Lemma lem1306941 (m : nat) (N : nat) : (term61 N m) = (term62 m N).
Proof. exact (eq_refl (term61 N m)). Qed.
Lemma lem1306942 (m : nat) (N : nat) : term62 m N.
Proof. exact (EQ_MP (@lem1306941 m N) (@lem1306940 N m)). Qed.
Lemma lem1306943 (N : nat) (m : nat) (h1 : Peano.le N m) : Peano.le N m.
Proof. exact (h1). Qed.
Lemma lem1306944 (m : nat) (N : nat) (h1 : Peano.le m N) : Peano.le m N.
Proof. exact (h1). Qed.
Lemma lem1306945 (n : nat) : term63 n.
Proof. exact (@lem1244783 n). Qed.
Lemma lem1306946 (n : nat) : (term63 n) = ((term64 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term63 n)). Qed.
Lemma lem1306948 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem1306949 (P : type1606) (h1 : term65) : term66 P.
Proof. exact (@lem1306948 h1 P). Qed.
Lemma lem1306950 (P : type1606) : (term66 P) = (term67 P).
Proof. exact (eq_refl (term66 P)). Qed.
Lemma lem1306951 (P : type1606) (h1 : term65) : term67 P.
Proof. exact (EQ_MP (@lem1306950 P) (@lem1306949 P h1)). Qed.
Lemma lem1306952 (P : type1606) (A : nat) (h1 : term65) : term68 P A.
Proof. exact (@lem1306951 P h1 A). Qed.
Lemma lem1306953 (A : nat) (P : type1606) : (term68 P A) = (term69 A P).
Proof. exact (eq_refl (term68 P A)). Qed.
Lemma lem1306954 (A : nat) (P : type1606) (h1 : term65) : term69 A P.
Proof. exact (EQ_MP (@lem1306953 A P) (@lem1306952 P A h1)). Qed.
Lemma lem1306955 (A : nat) (P : type1606) (B : nat) (h1 : term65) : term70 A P B.
Proof. exact (@lem1306954 A P h1 B). Qed.
Lemma lem1306956 (A : nat) (B : nat) (P : type1606) : (term70 A P B) = (term71 A B P).
Proof. exact (eq_refl (term70 A P B)). Qed.
Lemma lem1306957 (A : nat) (B : nat) (P : type1606) (h1 : term65) : term71 A B P.
Proof. exact (EQ_MP (@lem1306956 A B P) (@lem1306955 A P B h1)). Qed.
Lemma lem1306958 (P : type1606) (A : nat) (B : nat) (h1 : term72 P A B) : term72 P A B.
Proof. exact (h1). Qed.
Lemma lem1306959 (P : type1606) (A : nat) (B : nat) (h1 : term65) (h2 : term72 P A B) : term73 P.
Proof. exact (@lem1306957 A B P h1 (@lem1306958 P A B h2)). Qed.
Lemma lem1306960 (P : type1606) (A : nat) (B : nat) (h1 : term72 P A B) : term74 P.
Proof. exact (fun h0 : term65 => @lem1306959 P A B h0 h1). Qed.
Lemma lem1306961 (P : type1606) (A : nat) (h1 : term75 P A) : term75 P A.
Proof. exact (h1). Qed.
Lemma lem1306962 (P : type1606) (A : nat) (h1 : term75 P A) : term74 P.
Proof. exact (ex_elim (@lem1306961 P A h1) (fun B : nat => fun h0 : term76 P A B => @lem1306960 P A B h0)). Qed.
Lemma lem1306963 (P : type1606) (h1 : term77 P) : term77 P.
Proof. exact (h1). Qed.
Lemma lem1306964 (P : type1606) (h1 : term77 P) : term74 P.
Proof. exact (ex_elim (@lem1306963 P h1) (fun A : nat => fun h0 : term78 P A => @lem1306962 P A h0)). Qed.
Lemma lem1306965 (h1 : term65) : term65.
Proof. exact (h1). Qed.
Lemma lem1306966 (P : type1606) (h1 : term65) (h2 : term77 P) : term73 P.
Proof. exact (@lem1306964 P h2 (@lem1306965 h1)). Qed.
Lemma lem1306967 (P : type1606) (h1 : term65) : term79 P.
Proof. exact (fun h0 : term77 P => @lem1306966 P h1 h0). Qed.
Lemma lem1306968 (h1 : term65) : term80.
Proof. exact (fun P : type1606 => @lem1306967 P h1). Qed.
Lemma lem1306969 : term81.
Proof. exact (fun h0 : term65 => @lem1306968 h0). Qed.
Lemma lem1306970 : term80.
Proof. exact (@lem1306969 (@lem1261658)). Qed.
Lemma lem1306971 (P : type1606) : term82 P.
Proof. exact (@lem1306970 P). Qed.
Lemma lem1306972 (P : type1606) : (term82 P) = (term79 P).
Proof. exact (eq_refl (term82 P)). Qed.
Lemma lem1306974 (x : nadd) : term83 x.
Proof. exact (@lem1306676 x). Qed.
Lemma lem1306975 (x : nadd) : (term83 x) = (term84 x).
Proof. exact (eq_refl (term83 x)). Qed.
Lemma lem1306977 (x : nadd) : term85 x.
Proof. exact (@lem1305777 x). Qed.
Lemma lem1306978 (x : nadd) : (term85 x) = (term86 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem1306980 (x : nadd) (h1 : term87 x) : term87 x.
Proof. exact (h1). Qed.
Lemma lem1306982 (x : nadd) : term86 x.
Proof. exact (EQ_MP (@lem1306978 x) (@lem1306977 x)). Qed.
Lemma lem1306983 (x : nadd) (h1 : term87 x) : term88 x.
Proof. exact (@lem1306982 x (@lem1306980 x h1)). Qed.
Lemma lem1306984 (x : nadd) (h1 : term88 x) : term88 x.
Proof. exact (h1). Qed.
Lemma lem1306985 (x : nadd) (B0 : nat) (h1 : term89 x B0) : term89 x B0.
Proof. exact (h1). Qed.
Lemma lem1306986 (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term90 N x B0.
Proof. exact (h1). Qed.
Lemma lem1306990 (x : nadd) : term84 x.
Proof. exact (EQ_MP (@lem1306975 x) (@lem1306974 x)). Qed.
Lemma lem1306991 (x : nadd) (h1 : term87 x) : term91 x.
Proof. exact (@lem1306990 x (@lem1306980 x h1)). Qed.
Lemma lem1306992 (N : nat) (x : nadd) (h1 : term87 x) : term92 x N.
Proof. exact (@lem1306991 x h1 N). Qed.
Lemma lem1306993 (N : nat) (x : nadd) : (term92 x N) = (term93 N x).
Proof. exact (eq_refl (term92 x N)). Qed.
Lemma lem1306994 (N : nat) (x : nadd) (h1 : term87 x) : term93 N x.
Proof. exact (EQ_MP (@lem1306993 N x) (@lem1306992 N x h1)). Qed.
Lemma lem1306995 (N : nat) (x : nadd) (h1 : term93 N x) : term93 N x.
Proof. exact (h1). Qed.
Lemma lem1306996 (N : nat) (x : nadd) (A : nat) (h1 : term94 N x A) : term94 N x A.
Proof. exact (h1). Qed.
Lemma lem1306997 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term95 N x A B.
Proof. exact (h1). Qed.
Lemma lem1306999 (P : type1606) : term79 P.
Proof. exact (EQ_MP (@lem1306972 P) (@lem1306971 P)). Qed.
Lemma lem1307000 (x : nadd) : term96 x.
Proof. exact (@lem1306999 (term97 x)). Qed.
Lemma lem1307001 (x : nadd) : (term98 x) = (term99 x).
Proof. exact (eq_refl (term98 x)). Qed.
Lemma lem1307002 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1307003 (x : nadd) : (term100 x) = (term101 x).
Proof. exact (MK_COMB (@lem1307001 x) (@lem1307002)). Qed.
Lemma lem1307004 (x : nadd) : (term101 x) = (term102 x).
Proof. exact (eq_refl (term101 x)). Qed.
Lemma lem1307005 (x : nadd) : (term100 x) = (term102 x).
Proof. exact (TRANS (@lem1307003 x) (@lem1307004 x)). Qed.
Lemma lem1307006 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1307007 (x : nadd) : (term103 x) = (term104 x).
Proof. exact (MK_COMB (@lem1307006) (@lem1307005 x)). Qed.
Lemma lem1307008 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1307009 (x : nadd) : ((term100 x) = (NUMERAL 0)) = ((term102 x) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1307007 x) (@lem1307008)). Qed.
Lemma lem1307010 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1307011 (x : nadd) : (term105 x) = (term106 x).
Proof. exact (MK_COMB (@lem1307010) (@lem1307009 x)). Qed.
Lemma lem1307012 (x : nadd) (m : nat) : (term107 x m) = (term108 x m).
Proof. exact (eq_refl (term107 x m)). Qed.
Lemma lem1307013 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1307014 (x : nadd) (m : nat) (n : nat) : (term109 x m n) = (term110 x m n).
Proof. exact (MK_COMB (@lem1307012 x m) (@lem1307013 n)). Qed.
Lemma lem1307015 (n : nat) (x : nadd) (m : nat) : (term110 x m n) = (term111 n x m).
Proof. exact (eq_refl (term110 x m n)). Qed.
Lemma lem1307016 (n : nat) (x : nadd) (m : nat) : (term109 x m n) = (term111 n x m).
Proof. exact (TRANS (@lem1307014 x m n) (@lem1307015 n x m)). Qed.
Lemma lem1307017 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1307018 (n : nat) (x : nadd) (m : nat) : (term112 x m n) = (term113 n x m).
Proof. exact (MK_COMB (@lem1307017) (@lem1307016 n x m)). Qed.
Lemma lem1307019 (A : nat) (m : nat) (n : nat) (B : nat) : (term114 A m n B) = (term114 A m n B).
Proof. exact (eq_refl (term114 A m n B)). Qed.
Lemma lem1307020 (x : nadd) (A : nat) (m : nat) (n : nat) (B : nat) : (term115 x A m n B) = (term116 x A m n B).
Proof. exact (MK_COMB (@lem1307018 n x m) (@lem1307019 A m n B)). Qed.
Lemma lem1307021 (x : nadd) (A : nat) (m : nat) (B : nat) : (term117 x A m B) = (term118 x A m B).
Proof. exact (fun_ext (fun n : nat => @lem1307020 x A m n B)). Qed.
Lemma lem1307022 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1307023 (x : nadd) (A : nat) (m : nat) (B : nat) : (term119 x A m B) = (term120 x A m B).
Proof. exact (MK_COMB (@lem1307022) (@lem1307021 x A m B)). Qed.
Lemma lem1307024 (x : nadd) (A : nat) (B : nat) : (term121 x A B) = (term122 x A B).
Proof. exact (fun_ext (fun m : nat => @lem1307023 x A m B)). Qed.
Lemma lem1307025 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1307026 (x : nadd) (A : nat) (B : nat) : (term123 x A B) = (term124 x A B).
Proof. exact (MK_COMB (@lem1307025) (@lem1307024 x A B)). Qed.
Lemma lem1307027 (x : nadd) (A : nat) (B : nat) : (term125 x A B) = (term126 x A B).
Proof. exact (MK_COMB (@lem1307011 x) (@lem1307026 x A B)). Qed.
Lemma lem1307028 (x : nadd) (A : nat) : (term127 x A) = (term128 x A).
Proof. exact (fun_ext (fun B : nat => @lem1307027 x A B)). Qed.
Lemma lem1307029 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1307030 (x : nadd) (A : nat) : (term129 x A) = (term130 x A).
Proof. exact (MK_COMB (@lem1307029) (@lem1307028 x A)). Qed.
Lemma lem1307031 (x : nadd) : (term131 x) = (term132 x).
Proof. exact (fun_ext (fun A : nat => @lem1307030 x A)). Qed.
Lemma lem1307032 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1307033 (x : nadd) : (term133 x) = (term134 x).
Proof. exact (MK_COMB (@lem1307032) (@lem1307031 x)). Qed.
Lemma lem1307034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem1307035 (x : nadd) : (term135 x) = (term136 x).
Proof. exact (MK_COMB (@lem1307034) (@lem1307033 x)). Qed.
Lemma lem1307036 (x : nadd) (m : nat) : (term107 x m) = (term108 x m).
Proof. exact (eq_refl (term107 x m)). Qed.
Lemma lem1307037 (n : nat) : n = n.
Proof. exact (eq_refl n). Qed.
Lemma lem1307038 (x : nadd) (m : nat) (n : nat) : (term109 x m n) = (term110 x m n).
Proof. exact (MK_COMB (@lem1307036 x m) (@lem1307037 n)). Qed.
Lemma lem1307039 (n : nat) (x : nadd) (m : nat) : (term110 x m n) = (term111 n x m).
Proof. exact (eq_refl (term110 x m n)). Qed.
Lemma lem1307040 (n : nat) (x : nadd) (m : nat) : (term109 x m n) = (term111 n x m).
Proof. exact (TRANS (@lem1307038 x m n) (@lem1307039 n x m)). Qed.
Lemma lem1307041 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1307042 (n : nat) (x : nadd) (m : nat) : (term112 x m n) = (term113 n x m).
Proof. exact (MK_COMB (@lem1307041) (@lem1307040 n x m)). Qed.
Lemma lem1307043 (B : nat) (m : nat) (n : nat) : (term33 B m n) = (term33 B m n).
Proof. exact (eq_refl (term33 B m n)). Qed.
Lemma lem1307044 (x : nadd) (B : nat) (m : nat) (n : nat) : (term137 x B m n) = (term138 x B m n).
Proof. exact (MK_COMB (@lem1307042 n x m) (@lem1307043 B m n)). Qed.
Lemma lem1307045 (x : nadd) (B : nat) (m : nat) : (term139 x B m) = (term140 x B m).
Proof. exact (fun_ext (fun n : nat => @lem1307044 x B m n)). Qed.
Lemma lem1307046 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1307047 (x : nadd) (B : nat) (m : nat) : (term141 x B m) = (term142 x B m).
Proof. exact (MK_COMB (@lem1307046) (@lem1307045 x B m)). Qed.
Lemma lem1307048 (x : nadd) (B : nat) : (term143 x B) = (term144 x B).
Proof. exact (fun_ext (fun m : nat => @lem1307047 x B m)). Qed.
Lemma lem1307049 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem1307050 (x : nadd) (B : nat) : (term145 x B) = (term146 x B).
Proof. exact (MK_COMB (@lem1307049) (@lem1307048 x B)). Qed.
Lemma lem1307051 (x : nadd) : (term147 x) = (term148 x).
Proof. exact (fun_ext (fun B : nat => @lem1307050 x B)). Qed.
Lemma lem1307052 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1307053 (x : nadd) : (term149 x) = (term150 x).
Proof. exact (MK_COMB (@lem1307052) (@lem1307051 x)). Qed.
Lemma lem1307054 (x : nadd) : (term96 x) = (term151 x).
Proof. exact (MK_COMB (@lem1307035 x) (@lem1307053 x)). Qed.
Lemma lem1307055 (x : nadd) : term151 x.
Proof. exact (EQ_MP (@lem1307054 x) (@lem1307000 x)). Qed.
Lemma lem1307069 (n : nat) : (term64 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem1306946 n) (@lem1306945 n)). Qed.
Lemma lem1307070 (x : nadd) : (term102 x) = (NUMERAL 0).
Proof. exact (@lem1307069 (term152 x)). Qed.
Lemma lem1307071 : (@eq nat) = (@eq nat).
Proof. exact (eq_refl (@eq nat)). Qed.
Lemma lem1307072 (x : nadd) : (term104 x) = term153.
Proof. exact (MK_COMB (@lem1307071) (@lem1307070 x)). Qed.
Lemma lem1307073 : (NUMERAL 0) = (NUMERAL 0).
Proof. exact (eq_refl (NUMERAL 0)). Qed.
Lemma lem1307074 (x : nadd) : ((term102 x) = (NUMERAL 0)) = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (MK_COMB (@lem1307072 x) (@lem1307073)). Qed.
Lemma lem1307076 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem1307077 (x : nat) : (x = x) = True.
Proof. exact (@lem1307076 nat x). Qed.
Lemma lem1307078 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1307077 (NUMERAL 0)). Qed.
Lemma lem1307079 (x : nadd) : ((term102 x) = (NUMERAL 0)) = True.
Proof. exact (TRANS (@lem1307074 x) (@lem1307078)). Qed.
Lemma lem1307080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1307081 (x : nadd) : (term106 x) = (and True).
Proof. exact (MK_COMB (@lem1307080) (@lem1307079 x)). Qed.
Lemma lem1307092 (x : nadd) (A : nat) (B : nat) : (term124 x A B) = (term124 x A B).
Proof. exact (eq_refl (term124 x A B)). Qed.
Lemma lem1307093 (x : nadd) (A : nat) (B : nat) : (term126 x A B) = (term154 x A B).
Proof. exact (MK_COMB (@lem1307081 x) (@lem1307092 x A B)). Qed.
Lemma lem1307095 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1307096 (x : nadd) (A : nat) (B : nat) : (term154 x A B) = (term124 x A B).
Proof. exact (@lem1307095 (term124 x A B)). Qed.
Lemma lem1307107 (x : nadd) (A : nat) (B : nat) : (term126 x A B) = (term124 x A B).
Proof. exact (TRANS (@lem1307093 x A B) (@lem1307096 x A B)). Qed.
Lemma lem1307108 (x : nadd) (A : nat) : (term128 x A) = (term155 x A).
Proof. exact (fun_ext (fun B : nat => @lem1307107 x A B)). Qed.
Lemma lem1307109 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1307110 (x : nadd) (A : nat) : (term130 x A) = (term156 x A).
Proof. exact (MK_COMB (@lem1307109) (@lem1307108 x A)). Qed.
Lemma lem1307115 (x : nadd) : (term132 x) = (term157 x).
Proof. exact (fun_ext (fun A : nat => @lem1307110 x A)). Qed.
Lemma lem1307116 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem1307117 (x : nadd) : (term134 x) = (term158 x).
Proof. exact (MK_COMB (@lem1307116) (@lem1307115 x)). Qed.
Lemma lem1307122 (x : nadd) : (term158 x) = (term134 x).
Proof. exact (SYM (@lem1307117 x)). Qed.
Lemma lem1307124 (m : nat) (p : nat) : term49 m p.
Proof. exact (EQ_MP (@lem1306927 m p) (@lem1306926 m p)). Qed.
Lemma lem1307125 (x : nadd) (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : term159 x A B0 m n B.
Proof. exact (@lem1307124 (term111 n x m) (term160 A B0 m n B)). Qed.
Lemma lem1307151 (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term90 N x B0.
Proof. exact (h1). Qed.
Lemma lem1307152 (m : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term161 N x B0 m.
Proof. exact (@lem1307151 N x B0 h1 m). Qed.
Lemma lem1307153 (N : nat) (x : nadd) (B0 : nat) (m : nat) : (term161 N x B0 m) = (term162 N x B0 m).
Proof. exact (eq_refl (term161 N x B0 m)). Qed.
Lemma lem1307154 (m : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term162 N x B0 m.
Proof. exact (EQ_MP (@lem1307153 N x B0 m) (@lem1307152 m N x B0 h1)). Qed.
Lemma lem1307155 (m : nat) (n : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term163 N x B0 m n.
Proof. exact (@lem1307154 m N x B0 h1 n). Qed.
Lemma lem1307156 (N : nat) (x : nadd) (B0 : nat) (m : nat) (n : nat) : (term163 N x B0 m n) = (term164 N x B0 m n).
Proof. exact (eq_refl (term163 N x B0 m n)). Qed.
Lemma lem1307157 (m : nat) (n : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term164 N x B0 m n.
Proof. exact (EQ_MP (@lem1307156 N x B0 m n) (@lem1307155 m n N x B0 h1)). Qed.
Lemma lem1307158 (m : nat) (N : nat) (n : nat) (h1 : term165 m N n) : term165 m N n.
Proof. exact (h1). Qed.
Lemma lem1307159 (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : term165 m N n) : term138 x B0 m n.
Proof. exact (@lem1307157 m n N x B0 h1 (@lem1307158 m N n h2)). Qed.
Lemma lem1307160 (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term165 m N n) : term166 N x B0 m n.
Proof. exact (fun h0 : term90 N x B0 => @lem1307159 x B0 m N n h0 h1). Qed.
Lemma lem1307161 (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term90 N x B0.
Proof. exact (h1). Qed.
Lemma lem1307162 (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : term165 m N n) : term138 x B0 m n.
Proof. exact (@lem1307160 x B0 m N n h2 (@lem1307161 N x B0 h1)). Qed.
Lemma lem1307163 (m : nat) (n : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term164 N x B0 m n.
Proof. exact (fun h0 : term165 m N n => @lem1307162 x B0 m N n h1 h0). Qed.
Lemma lem1307164 (m : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term162 N x B0 m.
Proof. exact (fun n : nat => @lem1307163 m n N x B0 h1). Qed.
Lemma lem1307165 (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term90 N x B0.
Proof. exact (fun m : nat => @lem1307164 m N x B0 h1). Qed.
Lemma lem1307166 (N : nat) (x : nadd) (B0 : nat) : term167 N x B0.
Proof. exact (fun h0 : term90 N x B0 => @lem1307165 N x B0 h0). Qed.
Lemma lem1307167 (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term90 N x B0.
Proof. exact (@lem1307166 N x B0 (@lem1306986 N x B0 h1)). Qed.
Lemma lem1307168 (m : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term161 N x B0 m.
Proof. exact (@lem1307167 N x B0 h1 m). Qed.
Lemma lem1307169 (N : nat) (x : nadd) (B0 : nat) (m : nat) : (term161 N x B0 m) = (term162 N x B0 m).
Proof. exact (eq_refl (term161 N x B0 m)). Qed.
Lemma lem1307170 (m : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term162 N x B0 m.
Proof. exact (EQ_MP (@lem1307169 N x B0 m) (@lem1307168 m N x B0 h1)). Qed.
Lemma lem1307171 (m : nat) (n : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term163 N x B0 m n.
Proof. exact (@lem1307170 m N x B0 h1 n). Qed.
Lemma lem1307172 (N : nat) (x : nadd) (B0 : nat) (m : nat) (n : nat) : (term163 N x B0 m n) = (term164 N x B0 m n).
Proof. exact (eq_refl (term163 N x B0 m n)). Qed.
Lemma lem1307175 (m : nat) (n : nat) (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term164 N x B0 m n.
Proof. exact (EQ_MP (@lem1307172 N x B0 m n) (@lem1307171 m n N x B0 h1)). Qed.
Lemma lem1307194 (N : nat) (m : nat) : (Peano.le N m) = ((Peano.le N m) = True).
Proof. exact (@lem7 (Peano.le N m)). Qed.
Lemma lem1307196 (N : nat) (n : nat) : (Peano.le N n) = ((Peano.le N n) = True).
Proof. exact (@lem7 (Peano.le N n)). Qed.
Lemma lem1307201 (N : nat) (m : nat) (h1 : Peano.le N m) : (Peano.le N m) = True.
Proof. exact (EQ_MP (@lem1307194 N m) (@lem1306943 N m h1)). Qed.
Lemma lem1307202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1307203 (N : nat) (m : nat) (h1 : Peano.le N m) : (term168 N m) = (and True).
Proof. exact (MK_COMB (@lem1307202) (@lem1307201 N m h1)). Qed.
Lemma lem1307205 (N : nat) (n : nat) (h1 : Peano.le N n) : (Peano.le N n) = True.
Proof. exact (EQ_MP (@lem1307196 N n) (@lem1306935 N n h1)). Qed.
Lemma lem1307206 (m : nat) (N : nat) (n : nat) (h1 : Peano.le N m) (h2 : Peano.le N n) : (term165 m N n) = (True /\ True).
Proof. exact (MK_COMB (@lem1307203 N m h1) (@lem1307205 N n h2)). Qed.
Lemma lem1307208 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1307209 : (True /\ True) = True.
Proof. exact (@lem1307208 True). Qed.
Lemma lem1307210 (m : nat) (N : nat) (n : nat) (h1 : Peano.le N m) (h2 : Peano.le N n) : (term165 m N n) = True.
Proof. exact (TRANS (@lem1307206 m N n h1 h2) (@lem1307209)). Qed.
Lemma lem1307211 (m : nat) (N : nat) (n : nat) (h1 : Peano.le N m) (h2 : Peano.le N n) : True = (term165 m N n).
Proof. exact (SYM (@lem1307210 m N n h1 h2)). Qed.
Lemma lem1307212 (m : nat) (N : nat) (n : nat) (h1 : Peano.le N m) (h2 : Peano.le N n) : term165 m N n.
Proof. exact (EQ_MP (@lem1307211 m N n h1 h2) (@lem0)). Qed.
Lemma lem1307213 (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : Peano.le N m) (h3 : Peano.le N n) : term138 x B0 m n.
Proof. exact (@lem1307175 m n N x B0 h1 (@lem1307212 m N n h2 h3)). Qed.
Lemma lem1307215 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1306899 n m) (@lem1306898 m n)). Qed.
Lemma lem1307216 (B0 : nat) (A : nat) : (Nat.add A B0) = (Nat.add B0 A).
Proof. exact (@lem1307215 B0 A). Qed.
Lemma lem1307217 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem1307218 (B0 : nat) (A : nat) : (term169 A B0) = (term169 B0 A).
Proof. exact (MK_COMB (@lem1307217) (@lem1307216 B0 A)). Qed.
Lemma lem1307219 (m : nat) (n : nat) : (Nat.add m n) = (Nat.add m n).
Proof. exact (eq_refl (Nat.add m n)). Qed.
Lemma lem1307220 (B0 : nat) (A : nat) (m : nat) (n : nat) : (term170 A B0 m n) = (term170 B0 A m n).
Proof. exact (MK_COMB (@lem1307218 B0 A) (@lem1307219 m n)). Qed.
Lemma lem1307221 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1307222 (B0 : nat) (A : nat) (m : nat) (n : nat) : (term171 A B0 m n) = (term171 B0 A m n).
Proof. exact (MK_COMB (@lem1307221) (@lem1307220 B0 A m n)). Qed.
Lemma lem1307223 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1307224 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term160 A B0 m n B) = (term160 B0 A m n B).
Proof. exact (MK_COMB (@lem1307222 B0 A m n) (@lem1307223 B)). Qed.
Lemma lem1307225 (B0 : nat) (m : nat) (n : nat) : (term172 B0 m n) = (term172 B0 m n).
Proof. exact (eq_refl (term172 B0 m n)). Qed.
Lemma lem1307226 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term173 A B0 m n B) = (term174 B0 A m n B).
Proof. exact (MK_COMB (@lem1307225 B0 m n) (@lem1307224 B0 A m n B)). Qed.
Lemma lem1307227 (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : (term174 B0 A m n B) = (term173 A B0 m n B).
Proof. exact (SYM (@lem1307226 B0 A m n B)). Qed.
Lemma lem1307231 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1306893 m n p) (@lem1306892 m n p)). Qed.
Lemma lem1307232 (B0 : nat) (A : nat) (m : nat) (n : nat) : (term170 B0 A m n) = (term175 B0 A m n).
Proof. exact (@lem1307231 B0 A (Nat.add m n)). Qed.
Lemma lem1307233 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1307234 (B0 : nat) (A : nat) (m : nat) (n : nat) : (term171 B0 A m n) = (term176 B0 A m n).
Proof. exact (MK_COMB (@lem1307233) (@lem1307232 B0 A m n)). Qed.
Lemma lem1307235 (B : nat) : B = B.
Proof. exact (eq_refl B). Qed.
Lemma lem1307236 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term160 B0 A m n B) = (term177 B0 A m n B).
Proof. exact (MK_COMB (@lem1307234 B0 A m n) (@lem1307235 B)). Qed.
Lemma lem1307238 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1306884 m n p) (@lem1306883 m n p)). Qed.
Lemma lem1307239 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term177 B0 A m n B) = (term178 B0 A m n B).
Proof. exact (@lem1307238 (term33 B0 m n) (term33 A m n) B). Qed.
Lemma lem1307240 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term160 B0 A m n B) = (term178 B0 A m n B).
Proof. exact (TRANS (@lem1307236 B0 A m n B) (@lem1307239 B0 A m n B)). Qed.
Lemma lem1307241 (B0 : nat) (m : nat) (n : nat) : (term172 B0 m n) = (term172 B0 m n).
Proof. exact (eq_refl (term172 B0 m n)). Qed.
Lemma lem1307242 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term174 B0 A m n B) = (term179 B0 A m n B).
Proof. exact (MK_COMB (@lem1307241 B0 m n) (@lem1307240 B0 A m n B)). Qed.
Lemma lem1307244 (m : nat) (n : nat) : (term17 m n) = True.
Proof. exact (EQ_MP (@lem1306875 m n) (@lem1306874 m n)). Qed.
Lemma lem1307245 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term179 B0 A m n B) = True.
Proof. exact (@lem1307244 (term33 B0 m n) (term114 A m n B)). Qed.
Lemma lem1307246 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : (term174 B0 A m n B) = True.
Proof. exact (TRANS (@lem1307242 B0 A m n B) (@lem1307245 B0 A m n B)). Qed.
Lemma lem1307247 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : True = (term174 B0 A m n B).
Proof. exact (SYM (@lem1307246 B0 A m n B)). Qed.
Lemma lem1307248 (B0 : nat) (A : nat) (m : nat) (n : nat) (B : nat) : term174 B0 A m n B.
Proof. exact (EQ_MP (@lem1307247 B0 A m n B) (@lem0)). Qed.
Lemma lem1307249 (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : term173 A B0 m n B.
Proof. exact (EQ_MP (@lem1307227 A B0 m n B) (@lem1307248 B0 A m n B)). Qed.
Lemma lem1307250 (A : nat) (B : nat) (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : Peano.le N m) (h3 : Peano.le N n) : term180 x A B0 m n B.
Proof. exact (conj (@lem1307213 x B0 m N n h1 h2 h3) (@lem1307249 A B0 m n B)). Qed.
Lemma lem1307251 (A : nat) (B : nat) (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : Peano.le N m) (h3 : Peano.le N n) : term181 x A B0 m n B.
Proof. exact (ex_intro (term182 x A B0 m n B) (term33 B0 m n) (@lem1307250 A B x B0 m N n h1 h2 h3)). Qed.
Lemma lem1307252 (A : nat) (B : nat) (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : Peano.le N m) (h3 : Peano.le N n) : term183 x A B0 m n B.
Proof. exact (@lem1307125 x A B0 m n B (@lem1307251 A B x B0 m N n h1 h2 h3)). Qed.
Lemma lem1307253 (n : nat) (N : nat) (h1 : Peano.le n N) : Peano.le n N.
Proof. exact (h1). Qed.
Lemma lem1307262 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term95 N x A B.
Proof. exact (h1). Qed.
Lemma lem1307263 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term184 N x A B m.
Proof. exact (@lem1307262 N x A B h1 m). Qed.
Lemma lem1307264 (N : nat) (x : nadd) (m : nat) (A : nat) (B : nat) : (term184 N x A B m) = (term185 N x m A B).
Proof. exact (eq_refl (term184 N x A B m)). Qed.
Lemma lem1307265 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term185 N x m A B.
Proof. exact (EQ_MP (@lem1307264 N x m A B) (@lem1307263 m N x A B h1)). Qed.
Lemma lem1307266 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term186 N x m A B n.
Proof. exact (@lem1307265 m N x A B h1 n). Qed.
Lemma lem1307267 (N : nat) (x : nadd) (m : nat) (A : nat) (n : nat) (B : nat) : (term186 N x m A B n) = (term187 N x m A n B).
Proof. exact (eq_refl (term186 N x m A B n)). Qed.
Lemma lem1307268 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term187 N x m A n B.
Proof. exact (EQ_MP (@lem1307267 N x m A n B) (@lem1307266 m n N x A B h1)). Qed.
Lemma lem1307269 (m : nat) (N : nat) (h1 : Peano.le m N) : Peano.le m N.
Proof. exact (h1). Qed.
Lemma lem1307270 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term188 x m A n B.
Proof. exact (@lem1307268 m n N x A B h1 (@lem1307269 m N h2)). Qed.
Lemma lem1307271 (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term189 x m A B.
Proof. exact (fun n : nat => @lem1307270 n x A B m N h1 h2). Qed.
Lemma lem1307272 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term190 N x m A B.
Proof. exact (fun h0 : Peano.le m N => @lem1307271 x A B m N h1 h0). Qed.
Lemma lem1307273 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term191 N x A B.
Proof. exact (fun m : nat => @lem1307272 m N x A B h1). Qed.
Lemma lem1307274 (N : nat) (x : nadd) (A : nat) (B : nat) : term192 N x A B.
Proof. exact (fun h0 : term95 N x A B => @lem1307273 N x A B h0). Qed.
Lemma lem1307275 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term191 N x A B.
Proof. exact (@lem1307274 N x A B (@lem1306997 N x A B h1)). Qed.
Lemma lem1307276 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term193 N x A B m.
Proof. exact (@lem1307275 N x A B h1 m). Qed.
Lemma lem1307277 (N : nat) (x : nadd) (m : nat) (A : nat) (B : nat) : (term193 N x A B m) = (term190 N x m A B).
Proof. exact (eq_refl (term193 N x A B m)). Qed.
Lemma lem1307280 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term190 N x m A B.
Proof. exact (EQ_MP (@lem1307277 N x m A B) (@lem1307276 m N x A B h1)). Qed.
Lemma lem1307281 (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term190 N x n A B.
Proof. exact (@lem1307280 n N x A B h1). Qed.
Lemma lem1307282 (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term189 x n A B.
Proof. exact (@lem1307281 n N x A B h1 (@lem1307253 n N h2)). Qed.
Lemma lem1307284 (m : nat) (p : nat) : term49 m p.
Proof. exact (EQ_MP (@lem1306849 m p) (@lem1306848 m p)). Qed.
Lemma lem1307285 (x : nadd) (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : term159 x A B0 m n B.
Proof. exact (@lem1307284 (term111 n x m) (term160 A B0 m n B)). Qed.
Lemma lem1307289 (n : nat) (m : nat) : (term58 m n) = (term58 n m).
Proof. exact (EQ_MP (@lem1306821 n m) (@lem1306820 m n)). Qed.
Lemma lem1307290 (m : nat) (x : nadd) (n : nat) : (term111 n x m) = (term111 m x n).
Proof. exact (@lem1307289 (term194 n x m) (term194 m x n)). Qed.
Lemma lem1307291 : Peano.le = Peano.le.
Proof. exact (eq_refl Peano.le). Qed.
Lemma lem1307292 (m : nat) (x : nadd) (n : nat) : (term113 n x m) = (term113 m x n).
Proof. exact (MK_COMB (@lem1307291) (@lem1307290 m x n)). Qed.
Lemma lem1307293 (A : nat) (m : nat) (B : nat) : (term195 A m B) = (term195 A m B).
Proof. exact (eq_refl (term195 A m B)). Qed.
Lemma lem1307294 (x : nadd) (n : nat) (A : nat) (m : nat) (B : nat) : (term196 n x A m B) = (term188 x n A m B).
Proof. exact (MK_COMB (@lem1307292 m x n) (@lem1307293 A m B)). Qed.
Lemma lem1307295 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1307296 (x : nadd) (n : nat) (A : nat) (m : nat) (B : nat) : (term197 n x A m B) = (term198 x n A m B).
Proof. exact (MK_COMB (@lem1307295) (@lem1307294 x n A m B)). Qed.
Lemma lem1307297 (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : (term199 A B0 m n B) = (term199 A B0 m n B).
Proof. exact (eq_refl (term199 A B0 m n B)). Qed.
Lemma lem1307298 (x : nadd) (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : (term200 x A B0 m n B) = (term201 x A B0 m n B).
Proof. exact (MK_COMB (@lem1307296 x n A m B) (@lem1307297 A B0 m n B)). Qed.
Lemma lem1307299 (x : nadd) (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : (term201 x A B0 m n B) = (term200 x A B0 m n B).
Proof. exact (SYM (@lem1307298 x A B0 m n B)). Qed.
Lemma lem1307300 (m : nat) : term202 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1307301 (m : nat) : (term202 m) = (term203 m).
Proof. exact (eq_refl (term202 m)). Qed.
Lemma lem1307302 (m : nat) : term203 m.
Proof. exact (EQ_MP (@lem1307301 m) (@lem1307300 m)). Qed.
Lemma lem1307303 (m : nat) (n : nat) : term204 m n.
Proof. exact (@lem1307302 m n). Qed.
Lemma lem1307304 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (eq_refl (term204 m n)). Qed.
Lemma lem1307305 (m : nat) (n : nat) : term205 m n.
Proof. exact (EQ_MP (@lem1307304 m n) (@lem1307303 m n)). Qed.
Lemma lem1307306 (m : nat) (n : nat) (p : nat) : term206 m n p.
Proof. exact (@lem1307305 m n p). Qed.
Lemma lem1307307 (p : nat) (m : nat) (n : nat) : (term206 m n p) = ((term207 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term206 m n p)). Qed.
Lemma lem1307329 (n' : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term208 x n A B n'.
Proof. exact (@lem1307282 x A B n N h1 h2 n'). Qed.
Lemma lem1307330 (x : nadd) (n : nat) (A : nat) (n' : nat) (B : nat) : (term208 x n A B n') = (term188 x n A n' B).
Proof. exact (eq_refl (term208 x n A B n')). Qed.
Lemma lem1307331 (n' : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term188 x n A n' B.
Proof. exact (EQ_MP (@lem1307330 x n A n' B) (@lem1307329 n' x A B n N h1 h2)). Qed.
Lemma lem1307332 (x : nadd) (n : nat) (A : nat) (n' : nat) (B : nat) : (term188 x n A n' B) = ((term188 x n A n' B) = True).
Proof. exact (@lem7 (term188 x n A n' B)). Qed.
Lemma lem1307337 (n' : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : (term188 x n A n' B) = True.
Proof. exact (EQ_MP (@lem1307332 x n A n' B) (@lem1307331 n' x A B n N h1 h2)). Qed.
Lemma lem1307338 (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : (term188 x n A m B) = True.
Proof. exact (@lem1307337 m x A B n N h1 h2). Qed.
Lemma lem1307339 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1307340 (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : (term198 x n A m B) = (and True).
Proof. exact (MK_COMB (@lem1307339) (@lem1307338 m x A B n N h1 h2)). Qed.
Lemma lem1307342 (p : nat) (m : nat) (n : nat) : (term207 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1307307 p m n) (@lem1307306 m n p)). Qed.
Lemma lem1307343 (B : nat) (A : nat) (B0 : nat) (m : nat) (n : nat) : (term199 A B0 m n B) = (term209 A B0 m n).
Proof. exact (@lem1307342 B (Nat.mul A m) (term170 A B0 m n)). Qed.
Lemma lem1307344 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : (term201 x A B0 m n B) = (term210 A B0 m n).
Proof. exact (MK_COMB (@lem1307340 m x A B n N h1 h2) (@lem1307343 B A B0 m n)). Qed.
Lemma lem1307346 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1307347 (A : nat) (B0 : nat) (m : nat) (n : nat) : (term210 A B0 m n) = (term209 A B0 m n).
Proof. exact (@lem1307346 (term209 A B0 m n)). Qed.
Lemma lem1307348 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : (term201 x A B0 m n B) = (term209 A B0 m n).
Proof. exact (TRANS (@lem1307344 B0 m x A B n N h1 h2) (@lem1307347 A B0 m n)). Qed.
Lemma lem1307349 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : (term209 A B0 m n) = (term201 x A B0 m n B).
Proof. exact (SYM (@lem1307348 B0 m x A B n N h1 h2)). Qed.
Lemma lem1307351 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1306806 m n p) (@lem1306805 m n p)). Qed.
Lemma lem1307352 (A : nat) (B0 : nat) (m : nat) (n : nat) : (term170 A B0 m n) = (term175 A B0 m n).
Proof. exact (@lem1307351 A B0 (Nat.add m n)). Qed.
Lemma lem1307354 (n : nat) (m : nat) (p : nat) : (term33 m n p) = (term34 n m p).
Proof. exact (EQ_MP (@lem1306815 n m p) (@lem1306814 n m p)). Qed.
Lemma lem1307355 (m : nat) (A : nat) (n : nat) : (term33 A m n) = (term34 m A n).
Proof. exact (@lem1307354 m A n). Qed.
Lemma lem1307356 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1307357 (m : nat) (A : nat) (n : nat) : (term211 A m n) = (term212 m A n).
Proof. exact (MK_COMB (@lem1307356) (@lem1307355 m A n)). Qed.
Lemma lem1307359 (n : nat) (m : nat) (p : nat) : (term33 m n p) = (term34 n m p).
Proof. exact (EQ_MP (@lem1306815 n m p) (@lem1306814 n m p)). Qed.
Lemma lem1307360 (m : nat) (B0 : nat) (n : nat) : (term33 B0 m n) = (term34 m B0 n).
Proof. exact (@lem1307359 m B0 n). Qed.
Lemma lem1307361 (A : nat) (m : nat) (B0 : nat) (n : nat) : (term175 A B0 m n) = (term213 A m B0 n).
Proof. exact (MK_COMB (@lem1307357 m A n) (@lem1307360 m B0 n)). Qed.
Lemma lem1307363 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1306797 m n p) (@lem1306796 m n p)). Qed.
Lemma lem1307364 (A : nat) (m : nat) (B0 : nat) (n : nat) : (term213 A m B0 n) = (term214 A m B0 n).
Proof. exact (@lem1307363 (Nat.mul A m) (Nat.mul A n) (term34 m B0 n)). Qed.
Lemma lem1307365 (A : nat) (m : nat) (B0 : nat) (n : nat) : (term175 A B0 m n) = (term214 A m B0 n).
Proof. exact (TRANS (@lem1307361 A m B0 n) (@lem1307364 A m B0 n)). Qed.
Lemma lem1307366 (A : nat) (m : nat) (B0 : nat) (n : nat) : (term170 A B0 m n) = (term214 A m B0 n).
Proof. exact (TRANS (@lem1307352 A B0 m n) (@lem1307365 A m B0 n)). Qed.
Lemma lem1307367 (A : nat) (m : nat) : (term215 A m) = (term215 A m).
Proof. exact (eq_refl (term215 A m)). Qed.
Lemma lem1307368 (A : nat) (m : nat) (B0 : nat) (n : nat) : (term209 A B0 m n) = (term216 A m B0 n).
Proof. exact (MK_COMB (@lem1307367 A m) (@lem1307366 A m B0 n)). Qed.
Lemma lem1307370 (m : nat) (n : nat) : (term17 m n) = True.
Proof. exact (EQ_MP (@lem1306788 m n) (@lem1306787 m n)). Qed.
Lemma lem1307371 (A : nat) (m : nat) (B0 : nat) (n : nat) : (term216 A m B0 n) = True.
Proof. exact (@lem1307370 (Nat.mul A m) (term217 A m B0 n)). Qed.
Lemma lem1307372 (A : nat) (B0 : nat) (m : nat) (n : nat) : (term209 A B0 m n) = True.
Proof. exact (TRANS (@lem1307368 A m B0 n) (@lem1307371 A m B0 n)). Qed.
Lemma lem1307373 (A : nat) (B0 : nat) (m : nat) (n : nat) : True = (term209 A B0 m n).
Proof. exact (SYM (@lem1307372 A B0 m n)). Qed.
Lemma lem1307374 (A : nat) (B0 : nat) (m : nat) (n : nat) : term209 A B0 m n.
Proof. exact (EQ_MP (@lem1307373 A B0 m n) (@lem0)). Qed.
Lemma lem1307375 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term201 x A B0 m n B.
Proof. exact (EQ_MP (@lem1307349 B0 m x A B n N h1 h2) (@lem1307374 A B0 m n)). Qed.
Lemma lem1307376 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term200 x A B0 m n B.
Proof. exact (EQ_MP (@lem1307299 x A B0 m n B) (@lem1307375 B0 m x A B n N h1 h2)). Qed.
Lemma lem1307377 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term181 x A B0 m n B.
Proof. exact (ex_intro (term182 x A B0 m n B) (term195 A m B) (@lem1307376 B0 m x A B n N h1 h2)). Qed.
Lemma lem1307378 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term183 x A B0 m n B.
Proof. exact (@lem1307285 x A B0 m n B (@lem1307377 B0 m x A B n N h1 h2)). Qed.
Lemma lem1307379 (B0 : nat) (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term218 N x A B0 m n B.
Proof. exact (fun h0 : Peano.le n N => @lem1307378 B0 m x A B n N h1 h0). Qed.
Lemma lem1307380 (B0 : nat) (m : nat) (x : nadd) (A : nat) (B : nat) (n : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le n N) : term183 x A B0 m n B.
Proof. exact (@lem1307379 B0 m n N x A B h1 (@lem1306936 n N h2)). Qed.
Lemma lem1307381 (A : nat) (B : nat) (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : Peano.le N m) (h3 : Peano.le N n) : (Peano.le N n) = (term183 x A B0 m n B).
Proof. exact (prop_ext (fun h4 : Peano.le N n => @lem1307252 A B x B0 m N n h1 h2 h3) (fun h4 : term183 x A B0 m n B => @lem1306935 N n h3)). Qed.
Lemma lem1307382 (A : nat) (B : nat) (x : nadd) (B0 : nat) (m : nat) (N : nat) (n : nat) (h1 : term90 N x B0) (h2 : Peano.le N m) (h3 : Peano.le N n) : term183 x A B0 m n B.
Proof. exact (EQ_MP (@lem1307381 A B x B0 m N n h1 h2 h3) (@lem1306935 N n h3)). Qed.
Lemma lem1307383 (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (N : nat) (m : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) (h3 : Peano.le N m) : term183 x A B0 m n B.
Proof. exact (or_elim (@lem1306934 n N) (fun h0 : Peano.le N n => @lem1307382 A B x B0 m N n h1 h3 h0) (fun h0 : Peano.le n N => @lem1307380 B0 m x A B n N h2 h0)). Qed.
Lemma lem1307384 (m : nat) (N : nat) (h1 : Peano.le m N) : Peano.le m N.
Proof. exact (h1). Qed.
Lemma lem1307393 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term95 N x A B.
Proof. exact (h1). Qed.
Lemma lem1307394 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term184 N x A B m.
Proof. exact (@lem1307393 N x A B h1 m). Qed.
Lemma lem1307395 (N : nat) (x : nadd) (m : nat) (A : nat) (B : nat) : (term184 N x A B m) = (term185 N x m A B).
Proof. exact (eq_refl (term184 N x A B m)). Qed.
Lemma lem1307396 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term185 N x m A B.
Proof. exact (EQ_MP (@lem1307395 N x m A B) (@lem1307394 m N x A B h1)). Qed.
Lemma lem1307397 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term186 N x m A B n.
Proof. exact (@lem1307396 m N x A B h1 n). Qed.
Lemma lem1307398 (N : nat) (x : nadd) (m : nat) (A : nat) (n : nat) (B : nat) : (term186 N x m A B n) = (term187 N x m A n B).
Proof. exact (eq_refl (term186 N x m A B n)). Qed.
Lemma lem1307399 (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term187 N x m A n B.
Proof. exact (EQ_MP (@lem1307398 N x m A n B) (@lem1307397 m n N x A B h1)). Qed.
Lemma lem1307400 (m : nat) (N : nat) (h1 : Peano.le m N) : Peano.le m N.
Proof. exact (h1). Qed.
Lemma lem1307401 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term188 x m A n B.
Proof. exact (@lem1307399 m n N x A B h1 (@lem1307400 m N h2)). Qed.
Lemma lem1307402 (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term189 x m A B.
Proof. exact (fun n : nat => @lem1307401 n x A B m N h1 h2). Qed.
Lemma lem1307403 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term190 N x m A B.
Proof. exact (fun h0 : Peano.le m N => @lem1307402 x A B m N h1 h0). Qed.
Lemma lem1307404 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term191 N x A B.
Proof. exact (fun m : nat => @lem1307403 m N x A B h1). Qed.
Lemma lem1307405 (N : nat) (x : nadd) (A : nat) (B : nat) : term192 N x A B.
Proof. exact (fun h0 : term95 N x A B => @lem1307404 N x A B h0). Qed.
Lemma lem1307406 (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term191 N x A B.
Proof. exact (@lem1307405 N x A B (@lem1306997 N x A B h1)). Qed.
Lemma lem1307407 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term193 N x A B m.
Proof. exact (@lem1307406 N x A B h1 m). Qed.
Lemma lem1307408 (N : nat) (x : nadd) (m : nat) (A : nat) (B : nat) : (term193 N x A B m) = (term190 N x m A B).
Proof. exact (eq_refl (term193 N x A B m)). Qed.
Lemma lem1307411 (m : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term190 N x m A B.
Proof. exact (EQ_MP (@lem1307408 N x m A B) (@lem1307407 m N x A B h1)). Qed.
Lemma lem1307412 (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term189 x m A B.
Proof. exact (@lem1307411 m N x A B h1 (@lem1307384 m N h2)). Qed.
Lemma lem1307414 (m : nat) (p : nat) : term49 m p.
Proof. exact (EQ_MP (@lem1306762 m p) (@lem1306761 m p)). Qed.
Lemma lem1307415 (x : nadd) (A : nat) (B0 : nat) (m : nat) (n : nat) (B : nat) : term159 x A B0 m n B.
Proof. exact (@lem1307414 (term111 n x m) (term160 A B0 m n B)). Qed.
Lemma lem1307416 (m : nat) : term202 m.
Proof. exact (@lem100973 m). Qed.
Lemma lem1307417 (m : nat) : (term202 m) = (term203 m).
Proof. exact (eq_refl (term202 m)). Qed.
Lemma lem1307418 (m : nat) : term203 m.
Proof. exact (EQ_MP (@lem1307417 m) (@lem1307416 m)). Qed.
Lemma lem1307419 (m : nat) (n : nat) : term204 m n.
Proof. exact (@lem1307418 m n). Qed.
Lemma lem1307420 (m : nat) (n : nat) : (term204 m n) = (term205 m n).
Proof. exact (eq_refl (term204 m n)). Qed.
Lemma lem1307421 (m : nat) (n : nat) : term205 m n.
Proof. exact (EQ_MP (@lem1307420 m n) (@lem1307419 m n)). Qed.
Lemma lem1307422 (m : nat) (n : nat) (p : nat) : term206 m n p.
Proof. exact (@lem1307421 m n p). Qed.
Lemma lem1307423 (p : nat) (m : nat) (n : nat) : (term206 m n p) = ((term207 m n p) = (Peano.le m n)).
Proof. exact (eq_refl (term206 m n p)). Qed.
Lemma lem1307443 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term208 x m A B n.
Proof. exact (@lem1307412 x A B m N h1 h2 n). Qed.
Lemma lem1307444 (x : nadd) (m : nat) (A : nat) (n : nat) (B : nat) : (term208 x m A B n) = (term188 x m A n B).
Proof. exact (eq_refl (term208 x m A B n)). Qed.
Lemma lem1307445 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term188 x m A n B.
Proof. exact (EQ_MP (@lem1307444 x m A n B) (@lem1307443 n x A B m N h1 h2)). Qed.
Lemma lem1307446 (x : nadd) (m : nat) (A : nat) (n : nat) (B : nat) : (term188 x m A n B) = ((term188 x m A n B) = True).
Proof. exact (@lem7 (term188 x m A n B)). Qed.
Lemma lem1307451 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : (term188 x m A n B) = True.
Proof. exact (EQ_MP (@lem1307446 x m A n B) (@lem1307445 n x A B m N h1 h2)). Qed.
Lemma lem1307452 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem1307453 (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : (term198 x m A n B) = (and True).
Proof. exact (MK_COMB (@lem1307452) (@lem1307451 n x A B m N h1 h2)). Qed.
Lemma lem1307455 (p : nat) (m : nat) (n : nat) : (term207 m n p) = (Peano.le m n).
Proof. exact (EQ_MP (@lem1307423 p m n) (@lem1307422 m n p)). Qed.
Lemma lem1307456 (B : nat) (A : nat) (B0 : nat) (m : nat) (n : nat) : (term219 A B0 m n B) = (term220 A B0 m n).
Proof. exact (@lem1307455 B (Nat.mul A n) (term170 A B0 m n)). Qed.
Lemma lem1307457 (B0 : nat) (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : (term221 x A B0 m n B) = (term222 A B0 m n).
Proof. exact (MK_COMB (@lem1307453 n x A B m N h1 h2) (@lem1307456 B A B0 m n)). Qed.
Lemma lem1307459 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem1307460 (A : nat) (B0 : nat) (m : nat) (n : nat) : (term222 A B0 m n) = (term220 A B0 m n).
Proof. exact (@lem1307459 (term220 A B0 m n)). Qed.
Lemma lem1307461 (B0 : nat) (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : (term221 x A B0 m n B) = (term220 A B0 m n).
Proof. exact (TRANS (@lem1307457 B0 n x A B m N h1 h2) (@lem1307460 A B0 m n)). Qed.
Lemma lem1307462 (B0 : nat) (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : (term220 A B0 m n) = (term221 x A B0 m n B).
Proof. exact (SYM (@lem1307461 B0 n x A B m N h1 h2)). Qed.
Lemma lem1307464 (n : nat) (m : nat) : (Nat.add m n) = (Nat.add n m).
Proof. exact (EQ_MP (@lem1306734 n m) (@lem1306733 m n)). Qed.
Lemma lem1307465 (A : nat) (B0 : nat) : (term169 A B0) = (term169 A B0).
Proof. exact (eq_refl (term169 A B0)). Qed.
Lemma lem1307466 (A : nat) (B0 : nat) (n : nat) (m : nat) : (term170 A B0 m n) = (term170 A B0 n m).
Proof. exact (MK_COMB (@lem1307465 A B0) (@lem1307464 n m)). Qed.
Lemma lem1307467 (A : nat) (n : nat) : (term215 A n) = (term215 A n).
Proof. exact (eq_refl (term215 A n)). Qed.
Lemma lem1307468 (A : nat) (B0 : nat) (n : nat) (m : nat) : (term220 A B0 m n) = (term209 A B0 n m).
Proof. exact (MK_COMB (@lem1307467 A n) (@lem1307466 A B0 n m)). Qed.
Lemma lem1307469 (A : nat) (B0 : nat) (m : nat) (n : nat) : (term209 A B0 n m) = (term220 A B0 m n).
Proof. exact (SYM (@lem1307468 A B0 n m)). Qed.
Lemma lem1307471 (m : nat) (n : nat) (p : nat) : (term26 m n p) = (term27 m n p).
Proof. exact (EQ_MP (@lem1306719 m n p) (@lem1306718 m n p)). Qed.
Lemma lem1307472 (A : nat) (B0 : nat) (n : nat) (m : nat) : (term170 A B0 n m) = (term175 A B0 n m).
Proof. exact (@lem1307471 A B0 (Nat.add n m)). Qed.
Lemma lem1307474 (n : nat) (m : nat) (p : nat) : (term33 m n p) = (term34 n m p).
Proof. exact (EQ_MP (@lem1306728 n m p) (@lem1306727 n m p)). Qed.
Lemma lem1307475 (n : nat) (A : nat) (m : nat) : (term33 A n m) = (term34 n A m).
Proof. exact (@lem1307474 n A m). Qed.
Lemma lem1307476 : Nat.add = Nat.add.
Proof. exact (eq_refl Nat.add). Qed.
Lemma lem1307477 (n : nat) (A : nat) (m : nat) : (term211 A n m) = (term212 n A m).
Proof. exact (MK_COMB (@lem1307476) (@lem1307475 n A m)). Qed.
Lemma lem1307479 (n : nat) (m : nat) (p : nat) : (term33 m n p) = (term34 n m p).
Proof. exact (EQ_MP (@lem1306728 n m p) (@lem1306727 n m p)). Qed.
Lemma lem1307480 (n : nat) (B0 : nat) (m : nat) : (term33 B0 n m) = (term34 n B0 m).
Proof. exact (@lem1307479 n B0 m). Qed.
Lemma lem1307481 (A : nat) (n : nat) (B0 : nat) (m : nat) : (term175 A B0 n m) = (term213 A n B0 m).
Proof. exact (MK_COMB (@lem1307477 n A m) (@lem1307480 n B0 m)). Qed.
Lemma lem1307483 (m : nat) (n : nat) (p : nat) : (term1 m n p) = (term0 m n p).
Proof. exact (EQ_MP (@lem1306710 m n p) (@lem1306709 m n p)). Qed.
Lemma lem1307484 (A : nat) (n : nat) (B0 : nat) (m : nat) : (term213 A n B0 m) = (term214 A n B0 m).
Proof. exact (@lem1307483 (Nat.mul A n) (Nat.mul A m) (term34 n B0 m)). Qed.
Lemma lem1307485 (A : nat) (n : nat) (B0 : nat) (m : nat) : (term175 A B0 n m) = (term214 A n B0 m).
Proof. exact (TRANS (@lem1307481 A n B0 m) (@lem1307484 A n B0 m)). Qed.
Lemma lem1307486 (A : nat) (n : nat) (B0 : nat) (m : nat) : (term170 A B0 n m) = (term214 A n B0 m).
Proof. exact (TRANS (@lem1307472 A B0 n m) (@lem1307485 A n B0 m)). Qed.
Lemma lem1307487 (A : nat) (n : nat) : (term215 A n) = (term215 A n).
Proof. exact (eq_refl (term215 A n)). Qed.
Lemma lem1307488 (A : nat) (n : nat) (B0 : nat) (m : nat) : (term209 A B0 n m) = (term216 A n B0 m).
Proof. exact (MK_COMB (@lem1307487 A n) (@lem1307486 A n B0 m)). Qed.
Lemma lem1307490 (m : nat) (n : nat) : (term17 m n) = True.
Proof. exact (EQ_MP (@lem1306701 m n) (@lem1306700 m n)). Qed.
Lemma lem1307491 (A : nat) (n : nat) (B0 : nat) (m : nat) : (term216 A n B0 m) = True.
Proof. exact (@lem1307490 (Nat.mul A n) (term217 A n B0 m)). Qed.
Lemma lem1307492 (A : nat) (B0 : nat) (n : nat) (m : nat) : (term209 A B0 n m) = True.
Proof. exact (TRANS (@lem1307488 A n B0 m) (@lem1307491 A n B0 m)). Qed.
Lemma lem1307493 (A : nat) (B0 : nat) (n : nat) (m : nat) : True = (term209 A B0 n m).
Proof. exact (SYM (@lem1307492 A B0 n m)). Qed.
Lemma lem1307494 (A : nat) (B0 : nat) (n : nat) (m : nat) : term209 A B0 n m.
Proof. exact (EQ_MP (@lem1307493 A B0 n m) (@lem0)). Qed.
Lemma lem1307495 (A : nat) (B0 : nat) (m : nat) (n : nat) : term220 A B0 m n.
Proof. exact (EQ_MP (@lem1307469 A B0 m n) (@lem1307494 A B0 n m)). Qed.
Lemma lem1307496 (B0 : nat) (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term221 x A B0 m n B.
Proof. exact (EQ_MP (@lem1307462 B0 n x A B m N h1 h2) (@lem1307495 A B0 m n)). Qed.
Lemma lem1307497 (B0 : nat) (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term181 x A B0 m n B.
Proof. exact (ex_intro (term182 x A B0 m n B) (term195 A n B) (@lem1307496 B0 n x A B m N h1 h2)). Qed.
Lemma lem1307498 (B0 : nat) (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term183 x A B0 m n B.
Proof. exact (@lem1307415 x A B0 m n B (@lem1307497 B0 n x A B m N h1 h2)). Qed.
Lemma lem1307499 (B0 : nat) (m : nat) (n : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term95 N x A B) : term223 N x A B0 m n B.
Proof. exact (fun h0 : Peano.le m N => @lem1307498 B0 n x A B m N h1 h0). Qed.
Lemma lem1307500 (B0 : nat) (n : nat) (x : nadd) (A : nat) (B : nat) (m : nat) (N : nat) (h1 : term95 N x A B) (h2 : Peano.le m N) : term183 x A B0 m n B.
Proof. exact (@lem1307499 B0 m n N x A B h1 (@lem1306944 m N h2)). Qed.
Lemma lem1307501 (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (N : nat) (m : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) (h3 : Peano.le N m) : (Peano.le N m) = (term183 x A B0 m n B).
Proof. exact (prop_ext (fun h4 : Peano.le N m => @lem1307383 n B0 x A B N m h1 h2 h3) (fun h4 : term183 x A B0 m n B => @lem1306943 N m h3)). Qed.
Lemma lem1307502 (n : nat) (B0 : nat) (x : nadd) (A : nat) (B : nat) (N : nat) (m : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) (h3 : Peano.le N m) : term183 x A B0 m n B.
Proof. exact (EQ_MP (@lem1307501 n B0 x A B N m h1 h2 h3) (@lem1306943 N m h3)). Qed.
Lemma lem1307503 (m : nat) (n : nat) (B0 : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) : term183 x A B0 m n B.
Proof. exact (or_elim (@lem1306942 m N) (fun h0 : Peano.le N m => @lem1307502 n B0 x A B N m h1 h2 h0) (fun h0 : Peano.le m N => @lem1307500 B0 n x A B m N h2 h0)). Qed.
Lemma lem1307508 (m : nat) (B0 : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) : term224 x A B0 m B.
Proof. exact (fun n : nat => @lem1307503 m n B0 N x A B h1 h2). Qed.
Lemma lem1307513 (B0 : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) : term225 x A B0 B.
Proof. exact (fun m : nat => @lem1307508 m B0 N x A B h1 h2). Qed.
Lemma lem1307514 (B0 : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) : term226 x A B0.
Proof. exact (ex_intro (term227 x A B0) B (@lem1307513 B0 N x A B h1 h2)). Qed.
Lemma lem1307515 (B0 : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) : term158 x.
Proof. exact (ex_intro (term157 x) (Nat.add A B0) (@lem1307514 B0 N x A B h1 h2)). Qed.
Lemma lem1307516 (B0 : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) : term134 x.
Proof. exact (EQ_MP (@lem1307122 x) (@lem1307515 B0 N x A B h1 h2)). Qed.
Lemma lem1307517 (B0 : nat) (N : nat) (x : nadd) (A : nat) (B : nat) (h1 : term90 N x B0) (h2 : term95 N x A B) : term150 x.
Proof. exact (@lem1307055 x (@lem1307516 B0 N x A B h1 h2)). Qed.
Lemma lem1307518 (B0 : nat) (N : nat) (x : nadd) (A : nat) (h1 : term90 N x B0) (h2 : term94 N x A) : term150 x.
Proof. exact (ex_elim (@lem1306996 N x A h2) (fun B : nat => fun h0 : term228 N x A B => @lem1307517 B0 N x A B h1 h0)). Qed.
Lemma lem1307519 (B0 : nat) (N : nat) (x : nadd) (h1 : term90 N x B0) (h2 : term93 N x) : term150 x.
Proof. exact (ex_elim (@lem1306995 N x h2) (fun A : nat => fun h0 : term229 N x A => @lem1307518 B0 N x A h1 h0)). Qed.
Lemma lem1307520 (N : nat) (x : nadd) (B0 : nat) (h1 : term90 N x B0) : term230 N x.
Proof. exact (fun h0 : term93 N x => @lem1307519 B0 N x h1 h0). Qed.
Lemma lem1307521 (N : nat) (B0 : nat) (x : nadd) (h1 : term90 N x B0) (h2 : term87 x) : term150 x.
Proof. exact (@lem1307520 N x B0 h1 (@lem1306994 N x h2)). Qed.
Lemma lem1307522 (B0 : nat) (x : nadd) (h1 : term89 x B0) (h2 : term87 x) : term150 x.
Proof. exact (ex_elim (@lem1306985 x B0 h1) (fun N : nat => fun h0 : term231 x B0 N => @lem1307521 N B0 x h0 h2)). Qed.
Lemma lem1307523 (x : nadd) (h1 : term88 x) (h2 : term87 x) : term150 x.
Proof. exact (ex_elim (@lem1306984 x h1) (fun B0 : nat => fun h0 : term232 x B0 => @lem1307522 B0 x h0 h2)). Qed.
Lemma lem1307524 (x : nadd) (h1 : term87 x) : term233 x.
Proof. exact (fun h0 : term88 x => @lem1307523 x h0 h1). Qed.
Lemma lem1307525 (x : nadd) (h1 : term87 x) : term150 x.
Proof. exact (@lem1307524 x h1 (@lem1306983 x h1)). Qed.
Lemma lem1307526 (x : nadd) : term234 x.
Proof. exact (fun h0 : term87 x => @lem1307525 x h0). Qed.
Lemma lem1307531 : term235.
Proof. exact (fun x : nadd => @lem1307526 x). Qed.
