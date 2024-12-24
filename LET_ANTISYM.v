Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LET_ANTISYM_term_abbrevs.
Require Import LE_SUC_spec.
Require Import LT_SUC_spec.
Require Import NOT_CLAUSES_WEAK_spec.
Require Import NOT_SUC_spec.
Require Import thm0_spec.
Require Import thm1833_spec.
Require Import thm1842_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm82_spec.
Require Import thm89498_spec.
Require Import thm89994_spec.
Lemma lem92679 (n : nat) : term0 n.
Proof. exact (@lem75570 n). Qed.
Lemma lem92680 (n : nat) : (term0 n) = (term1 n).
Proof. exact (eq_refl (term0 n)). Qed.
Lemma lem92681 (n : nat) : term1 n.
Proof. exact (EQ_MP (@lem92680 n) (@lem92679 n)). Qed.
Lemma lem92682 (n : nat) : term2 n.
Proof. exact (@lem82 ((S n) = (NUMERAL 0))). Qed.
Lemma lem92685 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (S n) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem92686 (n : nat) (h1 : (S n) = (NUMERAL 0)) : (NUMERAL 0) = (S n).
Proof. exact (SYM (@lem92685 n h1)). Qed.
Lemma lem92687 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (NUMERAL 0) = (S n).
Proof. exact (h1). Qed.
Lemma lem92688 (n : nat) (h1 : (NUMERAL 0) = (S n)) : (S n) = (NUMERAL 0).
Proof. exact (SYM (@lem92687 n h1)). Qed.
Lemma lem92689 (n : nat) : ((S n) = (NUMERAL 0)) = ((NUMERAL 0) = (S n)).
Proof. exact (prop_ext (fun h1 : (S n) = (NUMERAL 0) => @lem92686 n h1) (fun h1 : (NUMERAL 0) = (S n) => @lem92688 n h1)). Qed.
Lemma lem92690 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92691 (n : nat) : (term1 n) = (term3 n).
Proof. exact (MK_COMB (@lem92690) (@lem92689 n)). Qed.
Lemma lem92692 (n : nat) : term3 n.
Proof. exact (EQ_MP (@lem92691 n) (@lem92681 n)). Qed.
Lemma lem92693 (n : nat) : term4 n.
Proof. exact (@lem82 ((NUMERAL 0) = (S n))). Qed.
Lemma lem92695 : term5.
Proof. exact (proj2 (@lem89994)). Qed.
Lemma lem92696 (m : nat) : term6 m.
Proof. exact (@lem92695 m). Qed.
Lemma lem92697 (m : nat) : (term6 m) = (term7 m).
Proof. exact (eq_refl (term6 m)). Qed.
Lemma lem92698 (m : nat) : term7 m.
Proof. exact (EQ_MP (@lem92697 m) (@lem92696 m)). Qed.
Lemma lem92699 (m : nat) (n : nat) : term8 m n.
Proof. exact (@lem92698 m n). Qed.
Lemma lem92700 (m : nat) (n : nat) : (term8 m n) = ((term9 m n) = (term10 m n)).
Proof. exact (eq_refl (term8 m n)). Qed.
Lemma lem92702 : term11.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem92703 (m : nat) : term12 m.
Proof. exact (@lem92702 m). Qed.
Lemma lem92704 (m : nat) : (term12 m) = ((term13 m) = False).
Proof. exact (eq_refl (term12 m)). Qed.
Lemma lem92706 : term14.
Proof. exact (proj2 (@lem89498)). Qed.
Lemma lem92707 (m : nat) : term15 m.
Proof. exact (@lem92706 m). Qed.
Lemma lem92708 (m : nat) : (term15 m) = (term16 m).
Proof. exact (eq_refl (term15 m)). Qed.
Lemma lem92709 (m : nat) : term16 m.
Proof. exact (EQ_MP (@lem92708 m) (@lem92707 m)). Qed.
Lemma lem92710 (m : nat) (n : nat) : term17 m n.
Proof. exact (@lem92709 m n). Qed.
Lemma lem92711 (m : nat) (n : nat) : (term17 m n) = ((term18 m n) = (term19 m n)).
Proof. exact (eq_refl (term17 m n)). Qed.
Lemma lem92713 : term20.
Proof. exact (proj1 (@lem89498)). Qed.
Lemma lem92714 (m : nat) : term21 m.
Proof. exact (@lem92713 m). Qed.
Lemma lem92715 (m : nat) : (term21 m) = ((term22 m) = (m = (NUMERAL 0))).
Proof. exact (eq_refl (term21 m)). Qed.
Lemma lem92718 (P : nat -> Prop) : term23 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92719 : term24.
Proof. exact (@lem92718 term25). Qed.
Lemma lem92720 : term26 = term27.
Proof. exact (eq_refl term26). Qed.
Lemma lem92721 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92722 : term28 = term29.
Proof. exact (MK_COMB (@lem92721) (@lem92720)). Qed.
Lemma lem92723 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem92724 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92725 (m : nat) : (term32 m) = (term33 m).
Proof. exact (MK_COMB (@lem92724) (@lem92723 m)). Qed.
Lemma lem92726 (m : nat) : (term34 m) = (term35 m).
Proof. exact (eq_refl (term34 m)). Qed.
Lemma lem92727 (m : nat) : (term36 m) = (term37 m).
Proof. exact (MK_COMB (@lem92725 m) (@lem92726 m)). Qed.
Lemma lem92728 : term38 = term39.
Proof. exact (fun_ext (fun m : nat => @lem92727 m)). Qed.
Lemma lem92729 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92730 : term40 = term41.
Proof. exact (MK_COMB (@lem92729) (@lem92728)). Qed.
Lemma lem92731 : term42 = term43.
Proof. exact (MK_COMB (@lem92722) (@lem92730)). Qed.
Lemma lem92732 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92733 : term44 = term45.
Proof. exact (MK_COMB (@lem92732) (@lem92731)). Qed.
Lemma lem92734 (m : nat) : (term30 m) = (term31 m).
Proof. exact (eq_refl (term30 m)). Qed.
Lemma lem92735 : term46 = term25.
Proof. exact (fun_ext (fun m : nat => @lem92734 m)). Qed.
Lemma lem92736 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92737 : term47 = term48.
Proof. exact (MK_COMB (@lem92736) (@lem92735)). Qed.
Lemma lem92738 : term24 = term49.
Proof. exact (MK_COMB (@lem92733) (@lem92737)). Qed.
Lemma lem92739 : term49.
Proof. exact (EQ_MP (@lem92738) (@lem92719)). Qed.
Lemma lem92740 (m : nat) (h1 : term31 m) : term31 m.
Proof. exact (h1). Qed.
Lemma lem92742 (P : nat -> Prop) : term23 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92743 : term50.
Proof. exact (@lem92742 term51). Qed.
Lemma lem92744 : term52 = term53.
Proof. exact (eq_refl term52). Qed.
Lemma lem92745 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92746 : term54 = term55.
Proof. exact (MK_COMB (@lem92745) (@lem92744)). Qed.
Lemma lem92747 (n : nat) : (term56 n) = (term57 n).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem92748 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92749 (n : nat) : (term58 n) = (term59 n).
Proof. exact (MK_COMB (@lem92748) (@lem92747 n)). Qed.
Lemma lem92750 (n : nat) : (term60 n) = (term61 n).
Proof. exact (eq_refl (term60 n)). Qed.
Lemma lem92751 (n : nat) : (term62 n) = (term63 n).
Proof. exact (MK_COMB (@lem92749 n) (@lem92750 n)). Qed.
Lemma lem92752 : term64 = term65.
Proof. exact (fun_ext (fun n : nat => @lem92751 n)). Qed.
Lemma lem92753 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92754 : term66 = term67.
Proof. exact (MK_COMB (@lem92753) (@lem92752)). Qed.
Lemma lem92755 : term68 = term69.
Proof. exact (MK_COMB (@lem92746) (@lem92754)). Qed.
Lemma lem92756 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92757 : term70 = term71.
Proof. exact (MK_COMB (@lem92756) (@lem92755)). Qed.
Lemma lem92758 (n : nat) : (term56 n) = (term57 n).
Proof. exact (eq_refl (term56 n)). Qed.
Lemma lem92759 : term72 = term51.
Proof. exact (fun_ext (fun n : nat => @lem92758 n)). Qed.
Lemma lem92760 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92761 : term73 = term27.
Proof. exact (MK_COMB (@lem92760) (@lem92759)). Qed.
Lemma lem92762 : term50 = term74.
Proof. exact (MK_COMB (@lem92757) (@lem92761)). Qed.
Lemma lem92763 : term74.
Proof. exact (EQ_MP (@lem92762) (@lem92743)). Qed.
Lemma lem92770 (P : nat -> Prop) : term23 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem92771 (m : nat) : term75 m.
Proof. exact (@lem92770 (term76 m)). Qed.
Lemma lem92772 (m : nat) : (term77 m) = (term78 m).
Proof. exact (eq_refl (term77 m)). Qed.
Lemma lem92773 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92774 (m : nat) : (term79 m) = (term80 m).
Proof. exact (MK_COMB (@lem92773) (@lem92772 m)). Qed.
Lemma lem92775 (n : nat) (m : nat) : (term81 m n) = (term82 n m).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem92776 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92777 (n : nat) (m : nat) : (term83 m n) = (term84 n m).
Proof. exact (MK_COMB (@lem92776) (@lem92775 n m)). Qed.
Lemma lem92778 (n : nat) (m : nat) : (term85 m n) = (term86 n m).
Proof. exact (eq_refl (term85 m n)). Qed.
Lemma lem92779 (n : nat) (m : nat) : (term87 m n) = (term88 n m).
Proof. exact (MK_COMB (@lem92777 n m) (@lem92778 n m)). Qed.
Lemma lem92780 (m : nat) : (term89 m) = (term90 m).
Proof. exact (fun_ext (fun n : nat => @lem92779 n m)). Qed.
Lemma lem92781 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92782 (m : nat) : (term91 m) = (term92 m).
Proof. exact (MK_COMB (@lem92781) (@lem92780 m)). Qed.
Lemma lem92783 (m : nat) : (term93 m) = (term94 m).
Proof. exact (MK_COMB (@lem92774 m) (@lem92782 m)). Qed.
Lemma lem92784 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem92785 (m : nat) : (term95 m) = (term96 m).
Proof. exact (MK_COMB (@lem92784) (@lem92783 m)). Qed.
Lemma lem92786 (n : nat) (m : nat) : (term81 m n) = (term82 n m).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem92787 (m : nat) : (term97 m) = (term76 m).
Proof. exact (fun_ext (fun n : nat => @lem92786 n m)). Qed.
Lemma lem92788 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem92789 (m : nat) : (term98 m) = (term35 m).
Proof. exact (MK_COMB (@lem92788) (@lem92787 m)). Qed.
Lemma lem92790 (m : nat) : (term75 m) = (term99 m).
Proof. exact (MK_COMB (@lem92785 m) (@lem92789 m)). Qed.
Lemma lem92791 (m : nat) : term99 m.
Proof. exact (EQ_MP (@lem92790 m) (@lem92771 m)). Qed.
Lemma lem92852 (m : nat) : term100 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem92853 (m : nat) : (term100 m) = (term101 m).
Proof. exact (eq_refl (term100 m)). Qed.
Lemma lem92854 (m : nat) : term101 m.
Proof. exact (EQ_MP (@lem92853 m) (@lem92852 m)). Qed.
Lemma lem92855 (m : nat) (n : nat) : term102 m n.
Proof. exact (@lem92854 m n). Qed.
Lemma lem92856 (m : nat) (n : nat) : (term102 m n) = ((term103 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem92858 (m : nat) : term104 m.
Proof. exact (@lem91360 m). Qed.
Lemma lem92859 (m : nat) : (term104 m) = (term105 m).
Proof. exact (eq_refl (term104 m)). Qed.
Lemma lem92860 (m : nat) : term105 m.
Proof. exact (EQ_MP (@lem92859 m) (@lem92858 m)). Qed.
Lemma lem92861 (m : nat) (n : nat) : term106 m n.
Proof. exact (@lem92860 m n). Qed.
Lemma lem92862 (m : nat) (n : nat) : (term106 m n) = ((term107 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term106 m n)). Qed.
Lemma lem92864 (n : nat) (m : nat) (h1 : term31 m) : term108 m n.
Proof. exact (@lem92740 m h1 n). Qed.
Lemma lem92865 (n : nat) (m : nat) : (term108 m n) = (term109 n m).
Proof. exact (eq_refl (term108 m n)). Qed.
Lemma lem92866 (n : nat) (m : nat) (h1 : term31 m) : term109 n m.
Proof. exact (EQ_MP (@lem92865 n m) (@lem92864 n m h1)). Qed.
Lemma lem92867 (n : nat) (m : nat) : term110 n m.
Proof. exact (@lem82 (term111 n m)). Qed.
Lemma lem92874 (m : nat) (n : nat) : (term107 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem92862 m n) (@lem92861 m n)). Qed.
Lemma lem92875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92876 (m : nat) (n : nat) : (term112 m n) = (term113 m n).
Proof. exact (MK_COMB (@lem92875) (@lem92874 m n)). Qed.
Lemma lem92878 (m : nat) (n : nat) : (term103 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem92856 m n) (@lem92855 m n)). Qed.
Lemma lem92879 (n : nat) (m : nat) : (term103 n m) = (Peano.lt n m).
Proof. exact (@lem92878 n m). Qed.
Lemma lem92880 (n : nat) (m : nat) : (term114 n m) = (term111 n m).
Proof. exact (MK_COMB (@lem92876 m n) (@lem92879 n m)). Qed.
Lemma lem92882 (n : nat) (m : nat) (h1 : term31 m) : (term111 n m) = False.
Proof. exact (@lem92867 n m (@lem92866 n m h1)). Qed.
Lemma lem92883 (n : nat) (m : nat) (h1 : term31 m) : (term114 n m) = False.
Proof. exact (TRANS (@lem92880 n m) (@lem92882 n m h1)). Qed.
Lemma lem92884 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92885 (n : nat) (m : nat) (h1 : term31 m) : (term86 n m) = (~ False).
Proof. exact (MK_COMB (@lem92884) (@lem92883 n m h1)). Qed.
Lemma lem92887 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92888 (n : nat) (m : nat) (h1 : term31 m) : (term86 n m) = True.
Proof. exact (TRANS (@lem92885 n m h1) (@lem92887)). Qed.
Lemma lem92889 (n : nat) (m : nat) (h1 : term31 m) : True = (term86 n m).
Proof. exact (SYM (@lem92888 n m h1)). Qed.
Lemma lem92890 (n : nat) (m : nat) (h1 : term31 m) : term86 n m.
Proof. exact (EQ_MP (@lem92889 n m h1) (@lem0)). Qed.
Lemma lem92894 (m : nat) : (term22 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem92715 m) (@lem92714 m)). Qed.
Lemma lem92895 : term115 = ((NUMERAL 0) = (NUMERAL 0)).
Proof. exact (@lem92894 (NUMERAL 0)). Qed.
Lemma lem92897 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem92898 (x : nat) : (x = x) = True.
Proof. exact (@lem92897 nat x). Qed.
Lemma lem92899 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem92898 (NUMERAL 0)). Qed.
Lemma lem92900 : term115 = True.
Proof. exact (TRANS (@lem92895) (@lem92899)). Qed.
Lemma lem92901 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92902 : term116 = (and True).
Proof. exact (MK_COMB (@lem92901) (@lem92900)). Qed.
Lemma lem92904 (m : nat) : (term13 m) = False.
Proof. exact (EQ_MP (@lem92704 m) (@lem92703 m)). Qed.
Lemma lem92905 : term117 = False.
Proof. exact (@lem92904 (NUMERAL 0)). Qed.
Lemma lem92906 : term118 = (True /\ False).
Proof. exact (MK_COMB (@lem92902) (@lem92905)). Qed.
Lemma lem92908 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem92909 : (True /\ False) = False.
Proof. exact (@lem92908 False). Qed.
Lemma lem92910 : term118 = False.
Proof. exact (TRANS (@lem92906) (@lem92909)). Qed.
Lemma lem92911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92912 : term53 = (~ False).
Proof. exact (MK_COMB (@lem92911) (@lem92910)). Qed.
Lemma lem92914 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92915 : term53 = True.
Proof. exact (TRANS (@lem92912) (@lem92914)). Qed.
Lemma lem92916 : True = term53.
Proof. exact (SYM (@lem92915)). Qed.
Lemma lem92921 (m : nat) (n : nat) : (term18 m n) = (term19 m n).
Proof. exact (EQ_MP (@lem92711 m n) (@lem92710 m n)). Qed.
Lemma lem92922 (n : nat) : (term119 n) = (term120 n).
Proof. exact (@lem92921 (NUMERAL 0) n). Qed.
Lemma lem92926 (n : nat) : ((NUMERAL 0) = (S n)) = False.
Proof. exact (@lem92693 n (@lem92692 n)). Qed.
Lemma lem92927 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem92928 (n : nat) : (term121 n) = (or False).
Proof. exact (MK_COMB (@lem92927) (@lem92926 n)). Qed.
Lemma lem92929 (n : nat) : (term122 n) = (term122 n).
Proof. exact (eq_refl (term122 n)). Qed.
Lemma lem92930 (n : nat) : (term120 n) = (term123 n).
Proof. exact (MK_COMB (@lem92928 n) (@lem92929 n)). Qed.
Lemma lem92932 (t : Prop) : (False \/ t) = t.
Proof. exact (proj1 (@lem1833 t)). Qed.
Lemma lem92933 (n : nat) : (term123 n) = (term122 n).
Proof. exact (@lem92932 (term122 n)). Qed.
Lemma lem92934 (n : nat) : (term120 n) = (term122 n).
Proof. exact (TRANS (@lem92930 n) (@lem92933 n)). Qed.
Lemma lem92935 (n : nat) : (term119 n) = (term122 n).
Proof. exact (TRANS (@lem92922 n) (@lem92934 n)). Qed.
Lemma lem92936 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92937 (n : nat) : (term124 n) = (term125 n).
Proof. exact (MK_COMB (@lem92936) (@lem92935 n)). Qed.
Lemma lem92939 (m : nat) : (term13 m) = False.
Proof. exact (EQ_MP (@lem92704 m) (@lem92703 m)). Qed.
Lemma lem92940 (n : nat) : (term126 n) = False.
Proof. exact (@lem92939 (S n)). Qed.
Lemma lem92941 (n : nat) : (term127 n) = (term128 n).
Proof. exact (MK_COMB (@lem92937 n) (@lem92940 n)). Qed.
Lemma lem92943 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem92944 (n : nat) : (term128 n) = False.
Proof. exact (@lem92943 (term122 n)). Qed.
Lemma lem92945 (n : nat) : (term127 n) = False.
Proof. exact (TRANS (@lem92941 n) (@lem92944 n)). Qed.
Lemma lem92946 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92947 (n : nat) : (term61 n) = (~ False).
Proof. exact (MK_COMB (@lem92946) (@lem92945 n)). Qed.
Lemma lem92949 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92950 (n : nat) : (term61 n) = True.
Proof. exact (TRANS (@lem92947 n) (@lem92949)). Qed.
Lemma lem92951 (n : nat) : True = (term61 n).
Proof. exact (SYM (@lem92950 n)). Qed.
Lemma lem92956 (m : nat) : (term22 m) = (m = (NUMERAL 0)).
Proof. exact (EQ_MP (@lem92715 m) (@lem92714 m)). Qed.
Lemma lem92957 (m : nat) : (term129 m) = ((S m) = (NUMERAL 0)).
Proof. exact (@lem92956 (S m)). Qed.
Lemma lem92959 (n : nat) : ((S n) = (NUMERAL 0)) = False.
Proof. exact (@lem92682 n (@lem92681 n)). Qed.
Lemma lem92960 (m : nat) : ((S m) = (NUMERAL 0)) = False.
Proof. exact (@lem92959 m). Qed.
Lemma lem92961 (m : nat) : (term129 m) = False.
Proof. exact (TRANS (@lem92957 m) (@lem92960 m)). Qed.
Lemma lem92962 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem92963 (m : nat) : (term130 m) = (and False).
Proof. exact (MK_COMB (@lem92962) (@lem92961 m)). Qed.
Lemma lem92965 (m : nat) (n : nat) : (term9 m n) = (term10 m n).
Proof. exact (EQ_MP (@lem92700 m n) (@lem92699 m n)). Qed.
Lemma lem92966 (m : nat) : (term131 m) = (term132 m).
Proof. exact (@lem92965 (NUMERAL 0) m). Qed.
Lemma lem92971 (m : nat) : (term133 m) = (term134 m).
Proof. exact (MK_COMB (@lem92963 m) (@lem92966 m)). Qed.
Lemma lem92973 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem92974 (m : nat) : (term134 m) = False.
Proof. exact (@lem92973 (term132 m)). Qed.
Lemma lem92975 (m : nat) : (term133 m) = False.
Proof. exact (TRANS (@lem92971 m) (@lem92974 m)). Qed.
Lemma lem92976 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem92977 (m : nat) : (term78 m) = (~ False).
Proof. exact (MK_COMB (@lem92976) (@lem92975 m)). Qed.
Lemma lem92979 : (~ False) = True.
Proof. exact (proj2 (@lem1504)). Qed.
Lemma lem92980 (m : nat) : (term78 m) = True.
Proof. exact (TRANS (@lem92977 m) (@lem92979)). Qed.
Lemma lem92981 (m : nat) : True = (term78 m).
Proof. exact (SYM (@lem92980 m)). Qed.
Lemma lem92983 (m : nat) : term78 m.
Proof. exact (EQ_MP (@lem92981 m) (@lem0)). Qed.
Lemma lem92984 (n : nat) : term61 n.
Proof. exact (EQ_MP (@lem92951 n) (@lem0)). Qed.
Lemma lem92985 : term53.
Proof. exact (EQ_MP (@lem92916) (@lem0)). Qed.
Lemma lem92986 (n : nat) (m : nat) (h1 : term31 m) : term88 n m.
Proof. exact (fun h0 : term82 n m => @lem92890 n m h1). Qed.
Lemma lem92991 (m : nat) (h1 : term31 m) : term92 m.
Proof. exact (fun n : nat => @lem92986 n m h1). Qed.
Lemma lem92992 (m : nat) (h1 : term31 m) : term94 m.
Proof. exact (conj (@lem92983 m) (@lem92991 m h1)). Qed.
Lemma lem92993 (m : nat) (h1 : term31 m) : term35 m.
Proof. exact (@lem92791 m (@lem92992 m h1)). Qed.
Lemma lem92994 (n : nat) : term63 n.
Proof. exact (fun h0 : term57 n => @lem92984 n). Qed.
Lemma lem92999 : term67.
Proof. exact (fun n : nat => @lem92994 n). Qed.
Lemma lem93000 : term69.
Proof. exact (conj (@lem92985) (@lem92999)). Qed.
Lemma lem93001 : term27.
Proof. exact (@lem92763 (@lem93000)). Qed.
Lemma lem93002 (m : nat) : term37 m.
Proof. exact (fun h0 : term31 m => @lem92993 m h0). Qed.
Lemma lem93007 : term41.
Proof. exact (fun m : nat => @lem93002 m). Qed.
Lemma lem93008 : term43.
Proof. exact (conj (@lem93001) (@lem93007)). Qed.
Lemma lem93009 : term48.
Proof. exact (@lem92739 (@lem93008)). Qed.
