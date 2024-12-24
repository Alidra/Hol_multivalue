Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LET_CASES_term_abbrevs.
Require Import LE_0_spec.
Require Import LE_SUC_LT_spec.
Require Import LT_SUC_LE_spec.
Require Import thm0_spec.
Require Import thm1831_spec.
Require Import thm1832_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Lemma lem96659 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96660 : term1.
Proof. exact (@lem96659 term2). Qed.
Lemma lem96661 : term3 = term4.
Proof. exact (eq_refl term3). Qed.
Lemma lem96662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96663 : term5 = term6.
Proof. exact (MK_COMB (@lem96662) (@lem96661)). Qed.
Lemma lem96664 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem96665 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96666 (m : nat) : (term9 m) = (term10 m).
Proof. exact (MK_COMB (@lem96665) (@lem96664 m)). Qed.
Lemma lem96667 (m : nat) : (term11 m) = (term12 m).
Proof. exact (eq_refl (term11 m)). Qed.
Lemma lem96668 (m : nat) : (term13 m) = (term14 m).
Proof. exact (MK_COMB (@lem96666 m) (@lem96667 m)). Qed.
Lemma lem96669 : term15 = term16.
Proof. exact (fun_ext (fun m : nat => @lem96668 m)). Qed.
Lemma lem96670 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96671 : term17 = term18.
Proof. exact (MK_COMB (@lem96670) (@lem96669)). Qed.
Lemma lem96672 : term19 = term20.
Proof. exact (MK_COMB (@lem96663) (@lem96671)). Qed.
Lemma lem96673 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96674 : term21 = term22.
Proof. exact (MK_COMB (@lem96673) (@lem96672)). Qed.
Lemma lem96675 (m : nat) : (term7 m) = (term8 m).
Proof. exact (eq_refl (term7 m)). Qed.
Lemma lem96676 : term23 = term2.
Proof. exact (fun_ext (fun m : nat => @lem96675 m)). Qed.
Lemma lem96677 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96678 : term24 = term25.
Proof. exact (MK_COMB (@lem96677) (@lem96676)). Qed.
Lemma lem96679 : term1 = term26.
Proof. exact (MK_COMB (@lem96674) (@lem96678)). Qed.
Lemma lem96680 : term26.
Proof. exact (EQ_MP (@lem96679) (@lem96660)). Qed.
Lemma lem96681 (m : nat) (h1 : term8 m) : term8 m.
Proof. exact (h1). Qed.
Lemma lem96683 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96684 : term27.
Proof. exact (@lem96683 term28). Qed.
Lemma lem96685 : term29 = term30.
Proof. exact (eq_refl term29). Qed.
Lemma lem96686 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96687 : term31 = term32.
Proof. exact (MK_COMB (@lem96686) (@lem96685)). Qed.
Lemma lem96688 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem96689 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96690 (n : nat) : (term35 n) = (term36 n).
Proof. exact (MK_COMB (@lem96689) (@lem96688 n)). Qed.
Lemma lem96691 (n : nat) : (term37 n) = (term38 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem96692 (n : nat) : (term39 n) = (term40 n).
Proof. exact (MK_COMB (@lem96690 n) (@lem96691 n)). Qed.
Lemma lem96693 : term41 = term42.
Proof. exact (fun_ext (fun n : nat => @lem96692 n)). Qed.
Lemma lem96694 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96695 : term43 = term44.
Proof. exact (MK_COMB (@lem96694) (@lem96693)). Qed.
Lemma lem96696 : term45 = term46.
Proof. exact (MK_COMB (@lem96687) (@lem96695)). Qed.
Lemma lem96697 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96698 : term47 = term48.
Proof. exact (MK_COMB (@lem96697) (@lem96696)). Qed.
Lemma lem96699 (n : nat) : (term33 n) = (term34 n).
Proof. exact (eq_refl (term33 n)). Qed.
Lemma lem96700 : term49 = term28.
Proof. exact (fun_ext (fun n : nat => @lem96699 n)). Qed.
Lemma lem96701 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96702 : term50 = term4.
Proof. exact (MK_COMB (@lem96701) (@lem96700)). Qed.
Lemma lem96703 : term27 = term51.
Proof. exact (MK_COMB (@lem96698) (@lem96702)). Qed.
Lemma lem96704 : term51.
Proof. exact (EQ_MP (@lem96703) (@lem96684)). Qed.
Lemma lem96711 (P : nat -> Prop) : term0 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem96712 (m : nat) : term52 m.
Proof. exact (@lem96711 (term53 m)). Qed.
Lemma lem96713 (m : nat) : (term54 m) = (term55 m).
Proof. exact (eq_refl (term54 m)). Qed.
Lemma lem96714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem96715 (m : nat) : (term56 m) = (term57 m).
Proof. exact (MK_COMB (@lem96714) (@lem96713 m)). Qed.
Lemma lem96716 (n : nat) (m : nat) : (term58 m n) = (term59 n m).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem96717 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96718 (n : nat) (m : nat) : (term60 m n) = (term61 n m).
Proof. exact (MK_COMB (@lem96717) (@lem96716 n m)). Qed.
Lemma lem96719 (n : nat) (m : nat) : (term62 m n) = (term63 n m).
Proof. exact (eq_refl (term62 m n)). Qed.
Lemma lem96720 (n : nat) (m : nat) : (term64 m n) = (term65 n m).
Proof. exact (MK_COMB (@lem96718 n m) (@lem96719 n m)). Qed.
Lemma lem96721 (m : nat) : (term66 m) = (term67 m).
Proof. exact (fun_ext (fun n : nat => @lem96720 n m)). Qed.
Lemma lem96722 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96723 (m : nat) : (term68 m) = (term69 m).
Proof. exact (MK_COMB (@lem96722) (@lem96721 m)). Qed.
Lemma lem96724 (m : nat) : (term70 m) = (term71 m).
Proof. exact (MK_COMB (@lem96715 m) (@lem96723 m)). Qed.
Lemma lem96725 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem96726 (m : nat) : (term72 m) = (term73 m).
Proof. exact (MK_COMB (@lem96725) (@lem96724 m)). Qed.
Lemma lem96727 (n : nat) (m : nat) : (term58 m n) = (term59 n m).
Proof. exact (eq_refl (term58 m n)). Qed.
Lemma lem96728 (m : nat) : (term74 m) = (term53 m).
Proof. exact (fun_ext (fun n : nat => @lem96727 n m)). Qed.
Lemma lem96729 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem96730 (m : nat) : (term75 m) = (term12 m).
Proof. exact (MK_COMB (@lem96729) (@lem96728 m)). Qed.
Lemma lem96731 (m : nat) : (term52 m) = (term76 m).
Proof. exact (MK_COMB (@lem96726 m) (@lem96730 m)). Qed.
Lemma lem96732 (m : nat) : term76 m.
Proof. exact (EQ_MP (@lem96731 m) (@lem96712 m)). Qed.
Lemma lem96738 (n : nat) : term77 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem96739 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem96740 (n : nat) : term78 n.
Proof. exact (EQ_MP (@lem96739 n) (@lem96738 n)). Qed.
Lemma lem96741 (n : nat) : (term78 n) = ((term78 n) = True).
Proof. exact (@lem7 (term78 n)). Qed.
Lemma lem96758 (n : nat) : (term78 n) = True.
Proof. exact (EQ_MP (@lem96741 n) (@lem96740 n)). Qed.
Lemma lem96759 : term79 = True.
Proof. exact (@lem96758 (NUMERAL 0)). Qed.
Lemma lem96760 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96761 : term80 = (or True).
Proof. exact (MK_COMB (@lem96760) (@lem96759)). Qed.
Lemma lem96762 : term81 = term81.
Proof. exact (eq_refl term81). Qed.
Lemma lem96763 : term30 = term82.
Proof. exact (MK_COMB (@lem96761) (@lem96762)). Qed.
Lemma lem96765 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem96766 : term82 = True.
Proof. exact (@lem96765 term81). Qed.
Lemma lem96767 : term30 = True.
Proof. exact (TRANS (@lem96763) (@lem96766)). Qed.
Lemma lem96768 : True = term30.
Proof. exact (SYM (@lem96767)). Qed.
Lemma lem96769 : term30.
Proof. exact (EQ_MP (@lem96768) (@lem0)). Qed.
Lemma lem96770 (n : nat) : term77 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem96771 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem96772 (n : nat) : term78 n.
Proof. exact (EQ_MP (@lem96771 n) (@lem96770 n)). Qed.
Lemma lem96773 (n : nat) : (term78 n) = ((term78 n) = True).
Proof. exact (@lem7 (term78 n)). Qed.
Lemma lem96792 (n : nat) : (term78 n) = True.
Proof. exact (EQ_MP (@lem96773 n) (@lem96772 n)). Qed.
Lemma lem96793 (n : nat) : (term83 n) = True.
Proof. exact (@lem96792 (S n)). Qed.
Lemma lem96794 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96795 (n : nat) : (term84 n) = (or True).
Proof. exact (MK_COMB (@lem96794) (@lem96793 n)). Qed.
Lemma lem96796 (n : nat) : (term85 n) = (term85 n).
Proof. exact (eq_refl (term85 n)). Qed.
Lemma lem96797 (n : nat) : (term38 n) = (term86 n).
Proof. exact (MK_COMB (@lem96795 n) (@lem96796 n)). Qed.
Lemma lem96799 (t : Prop) : (True \/ t) = True.
Proof. exact (proj1 (@lem1831 t)). Qed.
Lemma lem96800 (n : nat) : (term86 n) = True.
Proof. exact (@lem96799 (term85 n)). Qed.
Lemma lem96801 (n : nat) : (term38 n) = True.
Proof. exact (TRANS (@lem96797 n) (@lem96800 n)). Qed.
Lemma lem96802 (n : nat) : True = (term38 n).
Proof. exact (SYM (@lem96801 n)). Qed.
Lemma lem96803 (n : nat) : term38 n.
Proof. exact (EQ_MP (@lem96802 n) (@lem0)). Qed.
Lemma lem96804 (n : nat) : term77 n.
Proof. exact (@lem91499 n). Qed.
Lemma lem96805 (n : nat) : (term77 n) = (term78 n).
Proof. exact (eq_refl (term77 n)). Qed.
Lemma lem96806 (n : nat) : term78 n.
Proof. exact (EQ_MP (@lem96805 n) (@lem96804 n)). Qed.
Lemma lem96807 (n : nat) : (term78 n) = ((term78 n) = True).
Proof. exact (@lem7 (term78 n)). Qed.
Lemma lem96809 (m : nat) : term87 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem96810 (m : nat) : (term87 m) = (term88 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem96811 (m : nat) : term88 m.
Proof. exact (EQ_MP (@lem96810 m) (@lem96809 m)). Qed.
Lemma lem96812 (m : nat) (n : nat) : term89 m n.
Proof. exact (@lem96811 m n). Qed.
Lemma lem96813 (m : nat) (n : nat) : (term89 m n) = ((term90 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem96815 (m : nat) : term91 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem96816 (m : nat) : (term91 m) = (term92 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem96817 (m : nat) : term92 m.
Proof. exact (EQ_MP (@lem96816 m) (@lem96815 m)). Qed.
Lemma lem96818 (m : nat) (n : nat) : term93 m n.
Proof. exact (@lem96817 m n). Qed.
Lemma lem96819 (m : nat) (n : nat) : (term93 m n) = ((term94 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem96829 (m : nat) (n : nat) : (term94 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem96819 m n) (@lem96818 m n)). Qed.
Lemma lem96830 (m : nat) : (term95 m) = (term96 m).
Proof. exact (@lem96829 m (NUMERAL 0)). Qed.
Lemma lem96831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96832 (m : nat) : (term97 m) = (term98 m).
Proof. exact (MK_COMB (@lem96831) (@lem96830 m)). Qed.
Lemma lem96834 (m : nat) (n : nat) : (term90 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem96813 m n) (@lem96812 m n)). Qed.
Lemma lem96835 (m : nat) : (term99 m) = (term78 m).
Proof. exact (@lem96834 (NUMERAL 0) m). Qed.
Lemma lem96837 (n : nat) : (term78 n) = True.
Proof. exact (EQ_MP (@lem96807 n) (@lem96806 n)). Qed.
Lemma lem96838 (m : nat) : (term78 m) = True.
Proof. exact (@lem96837 m). Qed.
Lemma lem96839 (m : nat) : (term99 m) = True.
Proof. exact (TRANS (@lem96835 m) (@lem96838 m)). Qed.
Lemma lem96840 (m : nat) : (term55 m) = (term100 m).
Proof. exact (MK_COMB (@lem96832 m) (@lem96839 m)). Qed.
Lemma lem96842 (t : Prop) : (t \/ True) = True.
Proof. exact (proj1 (@lem1832 t)). Qed.
Lemma lem96843 (m : nat) : (term100 m) = True.
Proof. exact (@lem96842 (term96 m)). Qed.
Lemma lem96844 (m : nat) : (term55 m) = True.
Proof. exact (TRANS (@lem96840 m) (@lem96843 m)). Qed.
Lemma lem96845 (m : nat) : True = (term55 m).
Proof. exact (SYM (@lem96844 m)). Qed.
Lemma lem96846 (m : nat) : term55 m.
Proof. exact (EQ_MP (@lem96845 m) (@lem0)). Qed.
Lemma lem96852 (m : nat) : term87 m.
Proof. exact (@lem91305 m). Qed.
Lemma lem96853 (m : nat) : (term87 m) = (term88 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem96854 (m : nat) : term88 m.
Proof. exact (EQ_MP (@lem96853 m) (@lem96852 m)). Qed.
Lemma lem96855 (m : nat) (n : nat) : term89 m n.
Proof. exact (@lem96854 m n). Qed.
Lemma lem96856 (m : nat) (n : nat) : (term89 m n) = ((term90 m n) = (Peano.le m n)).
Proof. exact (eq_refl (term89 m n)). Qed.
Lemma lem96858 (m : nat) : term91 m.
Proof. exact (@lem91144 m). Qed.
Lemma lem96859 (m : nat) : (term91 m) = (term92 m).
Proof. exact (eq_refl (term91 m)). Qed.
Lemma lem96860 (m : nat) : term92 m.
Proof. exact (EQ_MP (@lem96859 m) (@lem96858 m)). Qed.
Lemma lem96861 (m : nat) (n : nat) : term93 m n.
Proof. exact (@lem96860 m n). Qed.
Lemma lem96862 (m : nat) (n : nat) : (term93 m n) = ((term94 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term93 m n)). Qed.
Lemma lem96864 (n : nat) (m : nat) (h1 : term8 m) : term101 m n.
Proof. exact (@lem96681 m h1 n). Qed.
Lemma lem96865 (n : nat) (m : nat) : (term101 m n) = (term102 n m).
Proof. exact (eq_refl (term101 m n)). Qed.
Lemma lem96866 (n : nat) (m : nat) (h1 : term8 m) : term102 n m.
Proof. exact (EQ_MP (@lem96865 n m) (@lem96864 n m h1)). Qed.
Lemma lem96867 (n : nat) (m : nat) : (term102 n m) = ((term102 n m) = True).
Proof. exact (@lem7 (term102 n m)). Qed.
Lemma lem96874 (m : nat) (n : nat) : (term94 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem96862 m n) (@lem96861 m n)). Qed.
Lemma lem96875 (m : nat) (n : nat) : (term103 m n) = (term90 m n).
Proof. exact (@lem96874 m (S n)). Qed.
Lemma lem96877 (m : nat) (n : nat) : (term90 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem96856 m n) (@lem96855 m n)). Qed.
Lemma lem96878 (m : nat) (n : nat) : (term103 m n) = (Peano.le m n).
Proof. exact (TRANS (@lem96875 m n) (@lem96877 m n)). Qed.
Lemma lem96879 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem96880 (m : nat) (n : nat) : (term104 m n) = (term105 m n).
Proof. exact (MK_COMB (@lem96879) (@lem96878 m n)). Qed.
Lemma lem96882 (m : nat) (n : nat) : (term90 m n) = (Peano.le m n).
Proof. exact (EQ_MP (@lem96856 m n) (@lem96855 m n)). Qed.
Lemma lem96883 (n : nat) (m : nat) : (term106 n m) = (term94 n m).
Proof. exact (@lem96882 (S n) m). Qed.
Lemma lem96885 (m : nat) (n : nat) : (term94 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem96862 m n) (@lem96861 m n)). Qed.
Lemma lem96886 (n : nat) (m : nat) : (term94 n m) = (Peano.lt n m).
Proof. exact (@lem96885 n m). Qed.
Lemma lem96887 (n : nat) (m : nat) : (term106 n m) = (Peano.lt n m).
Proof. exact (TRANS (@lem96883 n m) (@lem96886 n m)). Qed.
Lemma lem96888 (n : nat) (m : nat) : (term63 n m) = (term102 n m).
Proof. exact (MK_COMB (@lem96880 m n) (@lem96887 n m)). Qed.
Lemma lem96890 (n : nat) (m : nat) (h1 : term8 m) : (term102 n m) = True.
Proof. exact (EQ_MP (@lem96867 n m) (@lem96866 n m h1)). Qed.
Lemma lem96891 (n : nat) (m : nat) (h1 : term8 m) : (term63 n m) = True.
Proof. exact (TRANS (@lem96888 n m) (@lem96890 n m h1)). Qed.
Lemma lem96892 (n : nat) (m : nat) (h1 : term8 m) : True = (term63 n m).
Proof. exact (SYM (@lem96891 n m h1)). Qed.
Lemma lem96893 (n : nat) (m : nat) (h1 : term8 m) : term63 n m.
Proof. exact (EQ_MP (@lem96892 n m h1) (@lem0)). Qed.
Lemma lem96894 (n : nat) (m : nat) (h1 : term8 m) : term65 n m.
Proof. exact (fun h0 : term59 n m => @lem96893 n m h1). Qed.
Lemma lem96899 (m : nat) (h1 : term8 m) : term69 m.
Proof. exact (fun n : nat => @lem96894 n m h1). Qed.
Lemma lem96900 (m : nat) (h1 : term8 m) : term71 m.
Proof. exact (conj (@lem96846 m) (@lem96899 m h1)). Qed.
Lemma lem96901 (m : nat) (h1 : term8 m) : term12 m.
Proof. exact (@lem96732 m (@lem96900 m h1)). Qed.
Lemma lem96902 (n : nat) : term40 n.
Proof. exact (fun h0 : term34 n => @lem96803 n). Qed.
Lemma lem96907 : term44.
Proof. exact (fun n : nat => @lem96902 n). Qed.
Lemma lem96908 : term46.
Proof. exact (conj (@lem96769) (@lem96907)). Qed.
Lemma lem96909 : term4.
Proof. exact (@lem96704 (@lem96908)). Qed.
Lemma lem96910 (m : nat) : term14 m.
Proof. exact (fun h0 : term8 m => @lem96901 m h0). Qed.
Lemma lem96915 : term18.
Proof. exact (fun m : nat => @lem96910 m). Qed.
Lemma lem96916 : term20.
Proof. exact (conj (@lem96909) (@lem96915)). Qed.
Lemma lem96917 : term25.
Proof. exact (@lem96680 (@lem96916)). Qed.
