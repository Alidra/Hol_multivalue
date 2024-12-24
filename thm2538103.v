Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2538103_term_abbrevs.
Require Import AND_FORALL_THM_spec.
Require Import DIVISION_spec.
Require Import DIV_ZERO_spec.
Require Import EXCLUDED_MIDDLE_spec.
Require Import INT_ABS_NUM_spec.
Require Import INT_DIVMOD_UNIQ_spec.
Require Import INT_DIV_0_spec.
Require Import INT_OF_NUM_ADD_spec.
Require Import INT_OF_NUM_EQ_spec.
Require Import INT_OF_NUM_LT_spec.
Require Import INT_OF_NUM_MUL_spec.
Require Import INT_POS_spec.
Require Import INT_REM_0_spec.
Require Import MOD_ZERO_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import thm0_spec.
Require Import thm1842_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm7_spec.
Require Import thm82_spec.
Lemma lem2537701 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2537702 (m : nat) (h1 : term0) : term1 m.
Proof. exact (@lem2537701 h1 m). Qed.
Lemma lem2537703 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2537704 (m : nat) (h1 : term0) : term2 m.
Proof. exact (EQ_MP (@lem2537703 m) (@lem2537702 m h1)). Qed.
Lemma lem2537705 (m : nat) (n : nat) (h1 : term0) : term3 m n.
Proof. exact (@lem2537704 m h1 n). Qed.
Lemma lem2537706 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2537707 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (EQ_MP (@lem2537706 m n) (@lem2537705 m n h1)). Qed.
Lemma lem2537708 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (h1). Qed.
Lemma lem2537709 (m : nat) (n : nat) (h1 : term0) (h2 : term5 n) : term6 m n.
Proof. exact (@lem2537707 m n h1 (@lem2537708 n h2)). Qed.
Lemma lem2537710 (m : nat) (n : nat) (h1 : term5 n) : term7 m n.
Proof. exact (fun h0 : term0 => @lem2537709 m n h0 h1). Qed.
Lemma lem2537711 (h1 : term0) : term0.
Proof. exact (h1). Qed.
Lemma lem2537712 (m : nat) (n : nat) (h1 : term0) (h2 : term5 n) : term6 m n.
Proof. exact (@lem2537710 m n h2 (@lem2537711 h1)). Qed.
Lemma lem2537713 (m : nat) (n : nat) (h1 : term0) : term4 m n.
Proof. exact (fun h0 : term5 n => @lem2537712 m n h1 h0). Qed.
Lemma lem2537714 (m : nat) (h1 : term0) : term2 m.
Proof. exact (fun n : nat => @lem2537713 m n h1). Qed.
Lemma lem2537715 (h1 : term0) : term0.
Proof. exact (fun m : nat => @lem2537714 m h1). Qed.
Lemma lem2537716 : term8.
Proof. exact (fun h0 : term0 => @lem2537715 h0). Qed.
Lemma lem2537717 : term0.
Proof. exact (@lem2537716 (@lem157261)). Qed.
Lemma lem2537718 (m : nat) : term1 m.
Proof. exact (@lem2537717 m). Qed.
Lemma lem2537719 (m : nat) : (term1 m) = (term2 m).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem2537720 (m : nat) : term2 m.
Proof. exact (EQ_MP (@lem2537719 m) (@lem2537718 m)). Qed.
Lemma lem2537721 (m : nat) (n : nat) : term3 m n.
Proof. exact (@lem2537720 m n). Qed.
Lemma lem2537722 (m : nat) (n : nat) : (term3 m n) = (term4 m n).
Proof. exact (eq_refl (term3 m n)). Qed.
Lemma lem2537724 (m : nat) : term9 m.
Proof. exact (@lem2307247 m). Qed.
Lemma lem2537725 (m : nat) : (term9 m) = (term10 m).
Proof. exact (eq_refl (term9 m)). Qed.
Lemma lem2537726 (m : nat) : term10 m.
Proof. exact (EQ_MP (@lem2537725 m) (@lem2537724 m)). Qed.
Lemma lem2537727 (m : nat) (n : nat) : term11 m n.
Proof. exact (@lem2537726 m n). Qed.
Lemma lem2537728 (m : nat) (n : nat) : (term11 m n) = ((term12 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term11 m n)). Qed.
Lemma lem2537730 (m : nat) : term13 m.
Proof. exact (@lem2307147 m). Qed.
Lemma lem2537731 (m : nat) : (term13 m) = (term14 m).
Proof. exact (eq_refl (term13 m)). Qed.
Lemma lem2537732 (m : nat) : term14 m.
Proof. exact (EQ_MP (@lem2537731 m) (@lem2537730 m)). Qed.
Lemma lem2537733 (m : nat) (n : nat) : term15 m n.
Proof. exact (@lem2537732 m n). Qed.
Lemma lem2537734 (m : nat) (n : nat) : (term15 m n) = (((int_of_num m) = (int_of_num n)) = (m = n)).
Proof. exact (eq_refl (term15 m n)). Qed.
Lemma lem2537736 (n : nat) : term16 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem2537737 (n : nat) : (term16 n) = (term17 n).
Proof. exact (eq_refl (term16 n)). Qed.
Lemma lem2537738 (n : nat) : term17 n.
Proof. exact (EQ_MP (@lem2537737 n) (@lem2537736 n)). Qed.
Lemma lem2537739 (n : nat) : (term17 n) = ((term17 n) = True).
Proof. exact (@lem7 (term17 n)). Qed.
Lemma lem2537741 (n : nat) : term18 n.
Proof. exact (@lem2300474 n). Qed.
Lemma lem2537742 (n : nat) : (term18 n) = ((term19 n) = (int_of_num n)).
Proof. exact (eq_refl (term18 n)). Qed.
Lemma lem2537744 (m : nat) : term20 m.
Proof. exact (@lem2306816 m). Qed.
Lemma lem2537745 (m : nat) : (term20 m) = (term21 m).
Proof. exact (eq_refl (term20 m)). Qed.
Lemma lem2537746 (m : nat) : term21 m.
Proof. exact (EQ_MP (@lem2537745 m) (@lem2537744 m)). Qed.
Lemma lem2537747 (m : nat) (n : nat) : term22 m n.
Proof. exact (@lem2537746 m n). Qed.
Lemma lem2537748 (m : nat) (n : nat) : (term22 m n) = ((term23 m n) = (term24 m n)).
Proof. exact (eq_refl (term22 m n)). Qed.
Lemma lem2537750 (m : nat) : term25 m.
Proof. exact (@lem2307381 m). Qed.
Lemma lem2537751 (m : nat) : (term25 m) = (term26 m).
Proof. exact (eq_refl (term25 m)). Qed.
Lemma lem2537752 (m : nat) : term26 m.
Proof. exact (EQ_MP (@lem2537751 m) (@lem2537750 m)). Qed.
Lemma lem2537753 (m : nat) (n : nat) : term27 m n.
Proof. exact (@lem2537752 m n). Qed.
Lemma lem2537754 (m : nat) (n : nat) : (term27 m n) = ((term28 m n) = (term29 m n)).
Proof. exact (eq_refl (term27 m n)). Qed.
Lemma lem2537756 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem2537757 (m : int) (h1 : term30) : term31 m.
Proof. exact (@lem2537756 h1 m). Qed.
Lemma lem2537758 (m : int) : (term31 m) = (term32 m).
Proof. exact (eq_refl (term31 m)). Qed.
Lemma lem2537759 (m : int) (h1 : term30) : term32 m.
Proof. exact (EQ_MP (@lem2537758 m) (@lem2537757 m h1)). Qed.
Lemma lem2537760 (m : int) (n : int) (h1 : term30) : term33 m n.
Proof. exact (@lem2537759 m h1 n). Qed.
Lemma lem2537761 (m : int) (n : int) : (term33 m n) = (term34 m n).
Proof. exact (eq_refl (term33 m n)). Qed.
Lemma lem2537762 (m : int) (n : int) (h1 : term30) : term34 m n.
Proof. exact (EQ_MP (@lem2537761 m n) (@lem2537760 m n h1)). Qed.
Lemma lem2537763 (m : int) (n : int) (q : int) (h1 : term30) : term35 m n q.
Proof. exact (@lem2537762 m n h1 q). Qed.
Lemma lem2537764 (q : int) (m : int) (n : int) : (term35 m n q) = (term36 q m n).
Proof. exact (eq_refl (term35 m n q)). Qed.
Lemma lem2537765 (q : int) (m : int) (n : int) (h1 : term30) : term36 q m n.
Proof. exact (EQ_MP (@lem2537764 q m n) (@lem2537763 m n q h1)). Qed.
Lemma lem2537766 (q : int) (m : int) (n : int) (r : int) (h1 : term30) : term37 q m n r.
Proof. exact (@lem2537765 q m n h1 r). Qed.
Lemma lem2537767 (q : int) (m : int) (n : int) (r : int) : (term37 q m n r) = (term38 q m n r).
Proof. exact (eq_refl (term37 q m n r)). Qed.
Lemma lem2537768 (q : int) (m : int) (n : int) (r : int) (h1 : term30) : term38 q m n r.
Proof. exact (EQ_MP (@lem2537767 q m n r) (@lem2537766 q m n r h1)). Qed.
Lemma lem2537769 (m : int) (q : int) (r : int) (n : int) (h1 : term39 m q r n) : term39 m q r n.
Proof. exact (h1). Qed.
Lemma lem2537770 (m : int) (q : int) (r : int) (n : int) (h1 : term30) (h2 : term39 m q r n) : term40 q m n r.
Proof. exact (@lem2537768 q m n r h1 (@lem2537769 m q r n h2)). Qed.
Lemma lem2537771 (m : int) (q : int) (r : int) (n : int) (h1 : term39 m q r n) : term41 q m n r.
Proof. exact (fun h0 : term30 => @lem2537770 m q r n h0 h1). Qed.
Lemma lem2537772 (h1 : term30) : term30.
Proof. exact (h1). Qed.
Lemma lem2537773 (m : int) (q : int) (r : int) (n : int) (h1 : term30) (h2 : term39 m q r n) : term40 q m n r.
Proof. exact (@lem2537771 m q r n h2 (@lem2537772 h1)). Qed.
Lemma lem2537774 (q : int) (m : int) (n : int) (r : int) (h1 : term30) : term38 q m n r.
Proof. exact (fun h0 : term39 m q r n => @lem2537773 m q r n h1 h0). Qed.
Lemma lem2537775 (q : int) (m : int) (n : int) (h1 : term30) : term36 q m n.
Proof. exact (fun r : int => @lem2537774 q m n r h1). Qed.
Lemma lem2537776 (q : int) (m : int) (h1 : term30) : term42 q m.
Proof. exact (fun n : int => @lem2537775 q m n h1). Qed.
Lemma lem2537777 (q : int) (h1 : term30) : term43 q.
Proof. exact (fun m : int => @lem2537776 q m h1). Qed.
Lemma lem2537778 (h1 : term30) : term44.
Proof. exact (fun q : int => @lem2537777 q h1). Qed.
Lemma lem2537779 : term45.
Proof. exact (fun h0 : term30 => @lem2537778 h0). Qed.
Lemma lem2537780 : term44.
Proof. exact (@lem2537779 (@lem2495588)). Qed.
Lemma lem2537781 (q : int) : term46 q.
Proof. exact (@lem2537780 q). Qed.
Lemma lem2537782 (q : int) : (term46 q) = (term43 q).
Proof. exact (eq_refl (term46 q)). Qed.
Lemma lem2537783 (q : int) : term43 q.
Proof. exact (EQ_MP (@lem2537782 q) (@lem2537781 q)). Qed.
Lemma lem2537784 (q : int) (m : int) : term47 q m.
Proof. exact (@lem2537783 q m). Qed.
Lemma lem2537785 (q : int) (m : int) : (term47 q m) = (term42 q m).
Proof. exact (eq_refl (term47 q m)). Qed.
Lemma lem2537786 (q : int) (m : int) : term42 q m.
Proof. exact (EQ_MP (@lem2537785 q m) (@lem2537784 q m)). Qed.
Lemma lem2537787 (q : int) (m : int) (n : int) : term48 q m n.
Proof. exact (@lem2537786 q m n). Qed.
Lemma lem2537788 (q : int) (m : int) (n : int) : (term48 q m n) = (term36 q m n).
Proof. exact (eq_refl (term48 q m n)). Qed.
Lemma lem2537789 (q : int) (m : int) (n : int) : term36 q m n.
Proof. exact (EQ_MP (@lem2537788 q m n) (@lem2537787 q m n)). Qed.
Lemma lem2537790 (q : int) (m : int) (n : int) (r : int) : term37 q m n r.
Proof. exact (@lem2537789 q m n r). Qed.
Lemma lem2537791 (q : int) (m : int) (n : int) (r : int) : (term37 q m n r) = (term38 q m n r).
Proof. exact (eq_refl (term37 q m n r)). Qed.
Lemma lem2537793 (n : nat) : term49 n.
Proof. exact (@lem9784 (n = (NUMERAL 0))). Qed.
Lemma lem2537794 (n : nat) : (term49 n) = (term50 n).
Proof. exact (eq_refl (term49 n)). Qed.
Lemma lem2537795 (n : nat) : term50 n.
Proof. exact (EQ_MP (@lem2537794 n) (@lem2537793 n)). Qed.
Lemma lem2537797 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (h1). Qed.
Lemma lem2537798 {A : Type'} (P : A -> Prop) : term51 A P.
Proof. exact (@lem5146 A P). Qed.
Lemma lem2537799 {A : Type'} (P : A -> Prop) : (term51 A P) = (term52 A P).
Proof. exact (eq_refl (term51 A P)). Qed.
Lemma lem2537800 {A : Type'} (P : A -> Prop) : term52 A P.
Proof. exact (EQ_MP (@lem2537799 A P) (@lem2537798 A P)). Qed.
Lemma lem2537801 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : term53 A P Q.
Proof. exact (@lem2537800 A P Q). Qed.
Lemma lem2537802 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term53 A P Q) = ((term54 A P Q) = (term55 A P Q)).
Proof. exact (eq_refl (term53 A P Q)). Qed.
Lemma lem2537805 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem2537802 A P Q) (@lem2537801 A P Q)). Qed.
Lemma lem2537806 (P : nat -> Prop) (Q : nat -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem2537805 nat P Q). Qed.
Lemma lem2537807 : term58 = term59.
Proof. exact (@lem2537806 term60 term61). Qed.
Lemma lem2537808 (m : nat) : (term62 m) = (term63 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem2537809 : term64 = term60.
Proof. exact (fun_ext (fun m : nat => @lem2537808 m)). Qed.
Lemma lem2537810 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537811 : term65 = term66.
Proof. exact (MK_COMB (@lem2537810) (@lem2537809)). Qed.
Lemma lem2537812 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2537813 : term67 = term68.
Proof. exact (MK_COMB (@lem2537812) (@lem2537811)). Qed.
Lemma lem2537814 (m : nat) : (term69 m) = (term70 m).
Proof. exact (eq_refl (term69 m)). Qed.
Lemma lem2537815 : term71 = term61.
Proof. exact (fun_ext (fun m : nat => @lem2537814 m)). Qed.
Lemma lem2537816 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537817 : term72 = term73.
Proof. exact (MK_COMB (@lem2537816) (@lem2537815)). Qed.
Lemma lem2537818 : term58 = term74.
Proof. exact (MK_COMB (@lem2537813) (@lem2537817)). Qed.
Lemma lem2537819 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2537820 : term75 = term76.
Proof. exact (MK_COMB (@lem2537819) (@lem2537818)). Qed.
Lemma lem2537821 (m : nat) : (term62 m) = (term63 m).
Proof. exact (eq_refl (term62 m)). Qed.
Lemma lem2537822 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2537823 (m : nat) : (term77 m) = (term78 m).
Proof. exact (MK_COMB (@lem2537822) (@lem2537821 m)). Qed.
Lemma lem2537824 (m : nat) : (term69 m) = (term70 m).
Proof. exact (eq_refl (term69 m)). Qed.
Lemma lem2537825 (m : nat) : (term79 m) = (term80 m).
Proof. exact (MK_COMB (@lem2537823 m) (@lem2537824 m)). Qed.
Lemma lem2537826 : term81 = term82.
Proof. exact (fun_ext (fun m : nat => @lem2537825 m)). Qed.
Lemma lem2537827 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537828 : term59 = term83.
Proof. exact (MK_COMB (@lem2537827) (@lem2537826)). Qed.
Lemma lem2537829 : (term58 = term59) = (term74 = term83).
Proof. exact (MK_COMB (@lem2537820) (@lem2537828)). Qed.
Lemma lem2537830 : term74 = term83.
Proof. exact (EQ_MP (@lem2537829) (@lem2537807)). Qed.
Lemma lem2537836 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term54 A P Q) = (term55 A P Q).
Proof. exact (EQ_MP (@lem2537802 A P Q) (@lem2537801 A P Q)). Qed.
Lemma lem2537837 (P : nat -> Prop) (Q : nat -> Prop) : (term56 P Q) = (term57 P Q).
Proof. exact (@lem2537836 nat P Q). Qed.
Lemma lem2537838 (m : nat) : (term84 m) = (term85 m).
Proof. exact (@lem2537837 (term86 m) (term87 m)). Qed.
Lemma lem2537839 (m : nat) (n : nat) : (term88 m n) = ((term89 m n) = (term90 m n)).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem2537840 (m : nat) : (term91 m) = (term86 m).
Proof. exact (fun_ext (fun n : nat => @lem2537839 m n)). Qed.
Lemma lem2537841 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537842 (m : nat) : (term92 m) = (term63 m).
Proof. exact (MK_COMB (@lem2537841) (@lem2537840 m)). Qed.
Lemma lem2537843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2537844 (m : nat) : (term93 m) = (term78 m).
Proof. exact (MK_COMB (@lem2537843) (@lem2537842 m)). Qed.
Lemma lem2537845 (m : nat) (n : nat) : (term94 m n) = ((term95 m n) = (term96 m n)).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem2537846 (m : nat) : (term97 m) = (term87 m).
Proof. exact (fun_ext (fun n : nat => @lem2537845 m n)). Qed.
Lemma lem2537847 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537848 (m : nat) : (term98 m) = (term70 m).
Proof. exact (MK_COMB (@lem2537847) (@lem2537846 m)). Qed.
Lemma lem2537849 (m : nat) : (term84 m) = (term80 m).
Proof. exact (MK_COMB (@lem2537844 m) (@lem2537848 m)). Qed.
Lemma lem2537850 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2537851 (m : nat) : (term99 m) = (term100 m).
Proof. exact (MK_COMB (@lem2537850) (@lem2537849 m)). Qed.
Lemma lem2537852 (m : nat) (n : nat) : (term88 m n) = ((term89 m n) = (term90 m n)).
Proof. exact (eq_refl (term88 m n)). Qed.
Lemma lem2537853 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2537854 (m : nat) (n : nat) : (term101 m n) = (term102 m n).
Proof. exact (MK_COMB (@lem2537853) (@lem2537852 m n)). Qed.
Lemma lem2537855 (m : nat) (n : nat) : (term94 m n) = ((term95 m n) = (term96 m n)).
Proof. exact (eq_refl (term94 m n)). Qed.
Lemma lem2537856 (m : nat) (n : nat) : (term103 m n) = (term104 m n).
Proof. exact (MK_COMB (@lem2537854 m n) (@lem2537855 m n)). Qed.
Lemma lem2537857 (m : nat) : (term105 m) = (term106 m).
Proof. exact (fun_ext (fun n : nat => @lem2537856 m n)). Qed.
Lemma lem2537858 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537859 (m : nat) : (term85 m) = (term107 m).
Proof. exact (MK_COMB (@lem2537858) (@lem2537857 m)). Qed.
Lemma lem2537860 (m : nat) : ((term84 m) = (term85 m)) = ((term80 m) = (term107 m)).
Proof. exact (MK_COMB (@lem2537851 m) (@lem2537859 m)). Qed.
Lemma lem2537861 (m : nat) : (term80 m) = (term107 m).
Proof. exact (EQ_MP (@lem2537860 m) (@lem2537838 m)). Qed.
Lemma lem2537872 : term82 = term108.
Proof. exact (fun_ext (fun m : nat => @lem2537861 m)). Qed.
Lemma lem2537873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2537874 : term83 = term109.
Proof. exact (MK_COMB (@lem2537873) (@lem2537872)). Qed.
Lemma lem2537879 : term74 = term109.
Proof. exact (TRANS (@lem2537830) (@lem2537874)). Qed.
Lemma lem2537880 : term109 = term74.
Proof. exact (SYM (@lem2537879)). Qed.
Lemma lem2537881 (n : nat) : term110 n.
Proof. exact (@lem159121 n). Qed.
Lemma lem2537882 (n : nat) : (term110 n) = ((term111 n) = n).
Proof. exact (eq_refl (term110 n)). Qed.
Lemma lem2537884 (n : nat) : term112 n.
Proof. exact (@lem158192 n). Qed.
Lemma lem2537885 (n : nat) : (term112 n) = ((term113 n) = (NUMERAL 0)).
Proof. exact (eq_refl (term112 n)). Qed.
Lemma lem2537887 (m : int) : term114 m.
Proof. exact (@lem2396893 m). Qed.
Lemma lem2537888 (m : int) : (term114 m) = ((term115 m) = m).
Proof. exact (eq_refl (term114 m)). Qed.
Lemma lem2537890 (m : int) : term116 m.
Proof. exact (@lem2395867 m). Qed.
Lemma lem2537891 (m : int) : (term116 m) = ((term117 m) = term118).
Proof. exact (eq_refl (term116 m)). Qed.
Lemma lem2537898 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2537899 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2537900 (n : nat) (h1 : n = (NUMERAL 0)) : (int_of_num n) = term118.
Proof. exact (MK_COMB (@lem2537899) (@lem2537898 n h1)). Qed.
Lemma lem2537901 (m : nat) : (term119 m) = (term119 m).
Proof. exact (eq_refl (term119 m)). Qed.
Lemma lem2537902 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term89 m n) = (term120 m).
Proof. exact (MK_COMB (@lem2537901 m) (@lem2537900 n h1)). Qed.
Lemma lem2537904 (m : int) : (term117 m) = term118.
Proof. exact (EQ_MP (@lem2537891 m) (@lem2537890 m)). Qed.
Lemma lem2537905 (m : nat) : (term120 m) = term118.
Proof. exact (@lem2537904 (int_of_num m)). Qed.
Lemma lem2537906 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term89 m n) = term118.
Proof. exact (TRANS (@lem2537902 m n h1) (@lem2537905 m)). Qed.
Lemma lem2537907 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537908 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term121 m n) = term122.
Proof. exact (MK_COMB (@lem2537907) (@lem2537906 m n h1)). Qed.
Lemma lem2537910 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2537911 (m : nat) : (Nat.div m) = (Nat.div m).
Proof. exact (eq_refl (Nat.div m)). Qed.
Lemma lem2537912 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (term113 m).
Proof. exact (MK_COMB (@lem2537911 m) (@lem2537910 n h1)). Qed.
Lemma lem2537914 (n : nat) : (term113 n) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem2537885 n) (@lem2537884 n)). Qed.
Lemma lem2537915 (m : nat) : (term113 m) = (NUMERAL 0).
Proof. exact (@lem2537914 m). Qed.
Lemma lem2537916 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.div m n) = (NUMERAL 0).
Proof. exact (TRANS (@lem2537912 m n h1) (@lem2537915 m)). Qed.
Lemma lem2537917 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2537918 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term90 m n) = term118.
Proof. exact (MK_COMB (@lem2537917) (@lem2537916 m n h1)). Qed.
Lemma lem2537919 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term89 m n) = (term90 m n)) = (term118 = term118).
Proof. exact (MK_COMB (@lem2537908 m n h1) (@lem2537918 m n h1)). Qed.
Lemma lem2537921 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2537922 (x : int) : (x = x) = True.
Proof. exact (@lem2537921 int x). Qed.
Lemma lem2537923 : (term118 = term118) = True.
Proof. exact (@lem2537922 term118). Qed.
Lemma lem2537924 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term89 m n) = (term90 m n)) = True.
Proof. exact (TRANS (@lem2537919 m n h1) (@lem2537923)). Qed.
Lemma lem2537925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2537926 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term102 m n) = (and True).
Proof. exact (MK_COMB (@lem2537925) (@lem2537924 m n h1)). Qed.
Lemma lem2537930 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2537931 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2537932 (n : nat) (h1 : n = (NUMERAL 0)) : (int_of_num n) = term118.
Proof. exact (MK_COMB (@lem2537931) (@lem2537930 n h1)). Qed.
Lemma lem2537933 (m : nat) : (term123 m) = (term123 m).
Proof. exact (eq_refl (term123 m)). Qed.
Lemma lem2537934 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term95 m n) = (term124 m).
Proof. exact (MK_COMB (@lem2537933 m) (@lem2537932 n h1)). Qed.
Lemma lem2537936 (m : int) : (term115 m) = m.
Proof. exact (EQ_MP (@lem2537888 m) (@lem2537887 m)). Qed.
Lemma lem2537937 (m : nat) : (term124 m) = (int_of_num m).
Proof. exact (@lem2537936 (int_of_num m)). Qed.
Lemma lem2537938 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term95 m n) = (int_of_num m).
Proof. exact (TRANS (@lem2537934 m n h1) (@lem2537937 m)). Qed.
Lemma lem2537939 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2537940 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term125 m n) = (term126 m).
Proof. exact (MK_COMB (@lem2537939) (@lem2537938 m n h1)). Qed.
Lemma lem2537942 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem2537943 (m : nat) : (Nat.modulo m) = (Nat.modulo m).
Proof. exact (eq_refl (Nat.modulo m)). Qed.
Lemma lem2537944 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = (term111 m).
Proof. exact (MK_COMB (@lem2537943 m) (@lem2537942 n h1)). Qed.
Lemma lem2537946 (n : nat) : (term111 n) = n.
Proof. exact (EQ_MP (@lem2537882 n) (@lem2537881 n)). Qed.
Lemma lem2537947 (m : nat) : (term111 m) = m.
Proof. exact (@lem2537946 m). Qed.
Lemma lem2537948 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (Nat.modulo m n) = m.
Proof. exact (TRANS (@lem2537944 m n h1) (@lem2537947 m)). Qed.
Lemma lem2537949 : int_of_num = int_of_num.
Proof. exact (eq_refl int_of_num). Qed.
Lemma lem2537950 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term96 m n) = (int_of_num m).
Proof. exact (MK_COMB (@lem2537949) (@lem2537948 m n h1)). Qed.
Lemma lem2537951 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term95 m n) = (term96 m n)) = ((int_of_num m) = (int_of_num m)).
Proof. exact (MK_COMB (@lem2537940 m n h1) (@lem2537950 m n h1)). Qed.
Lemma lem2537953 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2537954 (x : int) : (x = x) = True.
Proof. exact (@lem2537953 int x). Qed.
Lemma lem2537955 (m : nat) : ((int_of_num m) = (int_of_num m)) = True.
Proof. exact (@lem2537954 (int_of_num m)). Qed.
Lemma lem2537956 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : ((term95 m n) = (term96 m n)) = True.
Proof. exact (TRANS (@lem2537951 m n h1) (@lem2537955 m)). Qed.
Lemma lem2537957 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term104 m n) = (True /\ True).
Proof. exact (MK_COMB (@lem2537926 m n h1) (@lem2537956 m n h1)). Qed.
Lemma lem2537959 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2537960 : (True /\ True) = True.
Proof. exact (@lem2537959 True). Qed.
Lemma lem2537961 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term104 m n) = True.
Proof. exact (TRANS (@lem2537957 m n h1) (@lem2537960)). Qed.
Lemma lem2537962 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : True = (term104 m n).
Proof. exact (SYM (@lem2537961 m n h1)). Qed.
Lemma lem2537963 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : term104 m n.
Proof. exact (EQ_MP (@lem2537962 m n h1) (@lem0)). Qed.
Lemma lem2537998 (q : int) (m : int) (n : int) (r : int) : term38 q m n r.
Proof. exact (EQ_MP (@lem2537791 q m n r) (@lem2537790 q m n r)). Qed.
Lemma lem2537999 (m : nat) (n : nat) : term127 m n.
Proof. exact (@lem2537998 (term90 m n) (int_of_num m) (int_of_num n) (term96 m n)). Qed.
Lemma lem2538005 (m : nat) (n : nat) : (term28 m n) = (term29 m n).
Proof. exact (EQ_MP (@lem2537754 m n) (@lem2537753 m n)). Qed.
Lemma lem2538006 (m : nat) (n : nat) : (term128 m n) = (term129 m n).
Proof. exact (@lem2538005 (Nat.div m n) n). Qed.
Lemma lem2538007 : int_add = int_add.
Proof. exact (eq_refl int_add). Qed.
Lemma lem2538008 (m : nat) (n : nat) : (term130 m n) = (term131 m n).
Proof. exact (MK_COMB (@lem2538007) (@lem2538006 m n)). Qed.
Lemma lem2538009 (m : nat) (n : nat) : (term96 m n) = (term96 m n).
Proof. exact (eq_refl (term96 m n)). Qed.
Lemma lem2538010 (m : nat) (n : nat) : (term132 m n) = (term133 m n).
Proof. exact (MK_COMB (@lem2538008 m n) (@lem2538009 m n)). Qed.
Lemma lem2538012 (m : nat) (n : nat) : (term23 m n) = (term24 m n).
Proof. exact (EQ_MP (@lem2537748 m n) (@lem2537747 m n)). Qed.
Lemma lem2538013 (m : nat) (n : nat) : (term133 m n) = (term134 m n).
Proof. exact (@lem2538012 (term135 m n) (Nat.modulo m n)). Qed.
Lemma lem2538014 (m : nat) (n : nat) : (term132 m n) = (term134 m n).
Proof. exact (TRANS (@lem2538010 m n) (@lem2538013 m n)). Qed.
Lemma lem2538015 (m : nat) : (term126 m) = (term126 m).
Proof. exact (eq_refl (term126 m)). Qed.
Lemma lem2538016 (m : nat) (n : nat) : ((int_of_num m) = (term132 m n)) = ((int_of_num m) = (term134 m n)).
Proof. exact (MK_COMB (@lem2538015 m) (@lem2538014 m n)). Qed.
Lemma lem2538019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2538020 (m : nat) (n : nat) : (term136 m n) = (term137 m n).
Proof. exact (MK_COMB (@lem2538019) (@lem2538016 m n)). Qed.
Lemma lem2538024 (n : nat) : (term19 n) = (int_of_num n).
Proof. exact (EQ_MP (@lem2537742 n) (@lem2537741 n)). Qed.
Lemma lem2538025 (m : nat) (n : nat) : (term138 m n) = (term138 m n).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem2538026 (m : nat) (n : nat) : (term139 m n) = (term140 m n).
Proof. exact (MK_COMB (@lem2538025 m n) (@lem2538024 n)). Qed.
Lemma lem2538027 (m : nat) (n : nat) : (term141 m n) = (term141 m n).
Proof. exact (eq_refl (term141 m n)). Qed.
Lemma lem2538028 (m : nat) (n : nat) : (term142 m n) = (term143 m n).
Proof. exact (MK_COMB (@lem2538027 m n) (@lem2538026 m n)). Qed.
Lemma lem2538031 (m : nat) (n : nat) : (term144 m n) = (term145 m n).
Proof. exact (MK_COMB (@lem2538020 m n) (@lem2538028 m n)). Qed.
Lemma lem2538034 (m : nat) (n : nat) : (term145 m n) = (term144 m n).
Proof. exact (SYM (@lem2538031 m n)). Qed.
Lemma lem2538038 (m : nat) (n : nat) : ((int_of_num m) = (int_of_num n)) = (m = n).
Proof. exact (EQ_MP (@lem2537734 m n) (@lem2537733 m n)). Qed.
Lemma lem2538039 (m : nat) (n : nat) : ((int_of_num m) = (term134 m n)) = (m = (term146 m n)).
Proof. exact (@lem2538038 m (term146 m n)). Qed.
Lemma lem2538042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2538043 (m : nat) (n : nat) : (term137 m n) = (term147 m n).
Proof. exact (MK_COMB (@lem2538042) (@lem2538039 m n)). Qed.
Lemma lem2538047 (n : nat) : (term17 n) = True.
Proof. exact (EQ_MP (@lem2537739 n) (@lem2537738 n)). Qed.
Lemma lem2538048 (m : nat) (n : nat) : (term148 m n) = True.
Proof. exact (@lem2538047 (Nat.modulo m n)). Qed.
Lemma lem2538049 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2538050 (m : nat) (n : nat) : (term141 m n) = (and True).
Proof. exact (MK_COMB (@lem2538049) (@lem2538048 m n)). Qed.
Lemma lem2538052 (m : nat) (n : nat) : (term12 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem2537728 m n) (@lem2537727 m n)). Qed.
Lemma lem2538053 (m : nat) (n : nat) : (term140 m n) = (term149 m n).
Proof. exact (@lem2538052 (Nat.modulo m n) n). Qed.
Lemma lem2538054 (m : nat) (n : nat) : (term143 m n) = (term150 m n).
Proof. exact (MK_COMB (@lem2538050 m n) (@lem2538053 m n)). Qed.
Lemma lem2538056 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2538057 (m : nat) (n : nat) : (term150 m n) = (term149 m n).
Proof. exact (@lem2538056 (term149 m n)). Qed.
Lemma lem2538058 (m : nat) (n : nat) : (term143 m n) = (term149 m n).
Proof. exact (TRANS (@lem2538054 m n) (@lem2538057 m n)). Qed.
Lemma lem2538059 (m : nat) (n : nat) : (term145 m n) = (term6 m n).
Proof. exact (MK_COMB (@lem2538043 m n) (@lem2538058 m n)). Qed.
Lemma lem2538062 (m : nat) (n : nat) : (term6 m n) = (term145 m n).
Proof. exact (SYM (@lem2538059 m n)). Qed.
Lemma lem2538064 (m : nat) (n : nat) : term4 m n.
Proof. exact (EQ_MP (@lem2537722 m n) (@lem2537721 m n)). Qed.
Lemma lem2538065 (n : nat) : term151 n.
Proof. exact (@lem82 (n = (NUMERAL 0))). Qed.
Lemma lem2538079 (n : nat) (h1 : term5 n) : (n = (NUMERAL 0)) = False.
Proof. exact (@lem2538065 n (@lem2537797 n h1)). Qed.
Lemma lem2538080 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2538081 (n : nat) (h1 : term5 n) : (term5 n) = (~ False).
Proof. exact (MK_COMB (@lem2538080) (@lem2538079 n h1)). Qed.
Lemma lem2538083 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem2538084 (n : nat) (h1 : term5 n) : (term5 n) = True.
Proof. exact (TRANS (@lem2538081 n h1) (@lem2538083)). Qed.
Lemma lem2538085 (n : nat) (h1 : term5 n) : True = (term5 n).
Proof. exact (SYM (@lem2538084 n h1)). Qed.
Lemma lem2538086 (n : nat) (h1 : term5 n) : term5 n.
Proof. exact (EQ_MP (@lem2538085 n h1) (@lem0)). Qed.
Lemma lem2538087 (m : nat) (n : nat) (h1 : term5 n) : term6 m n.
Proof. exact (@lem2538064 m n (@lem2538086 n h1)). Qed.
Lemma lem2538088 (m : nat) (n : nat) (h1 : term5 n) : term145 m n.
Proof. exact (EQ_MP (@lem2538062 m n) (@lem2538087 m n h1)). Qed.
Lemma lem2538089 (m : nat) (n : nat) (h1 : term5 n) : term144 m n.
Proof. exact (EQ_MP (@lem2538034 m n) (@lem2538088 m n h1)). Qed.
Lemma lem2538091 (m : nat) (n : nat) (h1 : term5 n) : term104 m n.
Proof. exact (@lem2537999 m n (@lem2538089 m n h1)). Qed.
Lemma lem2538092 (m : nat) (n : nat) : term104 m n.
Proof. exact (or_elim (@lem2537795 n) (fun h0 : n = (NUMERAL 0) => @lem2537963 m n h0) (fun h0 : term5 n => @lem2538091 m n h0)). Qed.
Lemma lem2538097 (m : nat) : term107 m.
Proof. exact (fun n : nat => @lem2538092 m n). Qed.
Lemma lem2538102 : term109.
Proof. exact (fun m : nat => @lem2538097 m). Qed.
Lemma lem2538103 : term74.
Proof. exact (EQ_MP (@lem2537880) (@lem2538102)). Qed.
