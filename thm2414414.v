Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm2414414_term_abbrevs.
Require Import INT_POW_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm16451_spec.
Require Import thm16452_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17045_spec.
Require Import thm1815_spec.
Require Import thm1816_spec.
Require Import thm18392_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1862_spec.
Require Import thm1863_spec.
Require Import thm18931_spec.
Require Import thm18932_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982729_spec.
Require Import thm1982733_spec.
Require Import thm1982745_spec.
Require Import thm1982747_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm2318497_spec.
Require Import thm2318532_spec.
Require Import thm2318533_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2406498 (x : int) : term0 x.
Proof. exact (proj2 (@lem2318057 x)). Qed.
Lemma lem2406499 (x : int) (n : nat) : term1 x n.
Proof. exact (@lem2406498 x n). Qed.
Lemma lem2406500 (x : int) (n : nat) : (term1 x n) = ((term2 x n) = (term3 x n)).
Proof. exact (eq_refl (term1 x n)). Qed.
Lemma lem2406608 (x : int) : (term4 x) = term5.
Proof. exact (proj1 (@lem2318057 x)). Qed.
Lemma lem2406609 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406610 (x : int) : (term6 x) = term7.
Proof. exact (MK_COMB (@lem2406609) (@lem2406608 x)). Qed.
Lemma lem2406611 : term5 = term5.
Proof. exact (eq_refl term5). Qed.
Lemma lem2406612 (x : int) : ((term4 x) = term5) = (term5 = term5).
Proof. exact (MK_COMB (@lem2406610 x) (@lem2406611)). Qed.
Lemma lem2406614 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406615 (x : int) : (x = x) = True.
Proof. exact (@lem2406614 int x). Qed.
Lemma lem2406616 : (term5 = term5) = True.
Proof. exact (@lem2406615 term5). Qed.
Lemma lem2406617 (x : int) : ((term4 x) = term5) = True.
Proof. exact (TRANS (@lem2406612 x) (@lem2406616)). Qed.
Lemma lem2406618 : term8 = term9.
Proof. exact (fun_ext (fun x : int => @lem2406617 x)). Qed.
Lemma lem2406619 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2406620 : term10 = term11.
Proof. exact (MK_COMB (@lem2406619) (@lem2406618)). Qed.
Lemma lem2406622 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2406623 (t : Prop) : (term13 t) = t.
Proof. exact (@lem2406622 int t). Qed.
Lemma lem2406624 : term11 = True.
Proof. exact (@lem2406623 True). Qed.
Lemma lem2406625 : term10 = True.
Proof. exact (TRANS (@lem2406620) (@lem2406624)). Qed.
Lemma lem2406626 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2406627 : term14 = (and True).
Proof. exact (MK_COMB (@lem2406626) (@lem2406625)). Qed.
Lemma lem2406639 (x : int) (n : nat) : (term2 x n) = (term3 x n).
Proof. exact (EQ_MP (@lem2406500 x n) (@lem2406499 x n)). Qed.
Lemma lem2406640 : (@eq int) = (@eq int).
Proof. exact (eq_refl (@eq int)). Qed.
Lemma lem2406641 (x : int) (n : nat) : (term15 x n) = (term16 x n).
Proof. exact (MK_COMB (@lem2406640) (@lem2406639 x n)). Qed.
Lemma lem2406642 (x : int) (n : nat) : (term3 x n) = (term3 x n).
Proof. exact (eq_refl (term3 x n)). Qed.
Lemma lem2406643 (x : int) (n : nat) : ((term2 x n) = (term3 x n)) = ((term3 x n) = (term3 x n)).
Proof. exact (MK_COMB (@lem2406641 x n) (@lem2406642 x n)). Qed.
Lemma lem2406645 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem1863 A x) (@lem1862 A x)). Qed.
Lemma lem2406646 (x : int) : (x = x) = True.
Proof. exact (@lem2406645 int x). Qed.
Lemma lem2406647 (x : int) (n : nat) : ((term3 x n) = (term3 x n)) = True.
Proof. exact (@lem2406646 (term3 x n)). Qed.
Lemma lem2406648 (x : int) (n : nat) : ((term2 x n) = (term3 x n)) = True.
Proof. exact (TRANS (@lem2406643 x n) (@lem2406647 x n)). Qed.
Lemma lem2406649 (x : int) : (term17 x) = term18.
Proof. exact (fun_ext (fun n : nat => @lem2406648 x n)). Qed.
Lemma lem2406650 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem2406651 (x : int) : (term0 x) = term19.
Proof. exact (MK_COMB (@lem2406650) (@lem2406649 x)). Qed.
Lemma lem2406653 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2406654 (t : Prop) : (term20 t) = t.
Proof. exact (@lem2406653 nat t). Qed.
Lemma lem2406655 : term19 = True.
Proof. exact (@lem2406654 True). Qed.
Lemma lem2406656 (x : int) : (term0 x) = True.
Proof. exact (TRANS (@lem2406651 x) (@lem2406655)). Qed.
Lemma lem2406657 : term21 = term9.
Proof. exact (fun_ext (fun x : int => @lem2406656 x)). Qed.
Lemma lem2406658 : (@all int) = (@all int).
Proof. exact (eq_refl (@all int)). Qed.
Lemma lem2406659 : term22 = term11.
Proof. exact (MK_COMB (@lem2406658) (@lem2406657)). Qed.
Lemma lem2406661 {A : Type'} (t : Prop) : (term12 A t) = t.
Proof. exact (EQ_MP (@lem1816 A t) (@lem1815 A t)). Qed.
Lemma lem2406662 (t : Prop) : (term13 t) = t.
Proof. exact (@lem2406661 int t). Qed.
Lemma lem2406663 : term11 = True.
Proof. exact (@lem2406662 True). Qed.
Lemma lem2406664 : term22 = True.
Proof. exact (TRANS (@lem2406659) (@lem2406663)). Qed.
Lemma lem2406665 : term23 = (True /\ True).
Proof. exact (MK_COMB (@lem2406627) (@lem2406664)). Qed.
Lemma lem2406667 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem2406668 : (True /\ True) = True.
Proof. exact (@lem2406667 True). Qed.
Lemma lem2406669 : term23 = True.
Proof. exact (TRANS (@lem2406665) (@lem2406668)). Qed.
Lemma lem2406670 : term24 = term24.
Proof. exact (eq_refl term24). Qed.
Lemma lem2406671 : term25 = term26.
Proof. exact (MK_COMB (@lem2406670) (@lem2406669)). Qed.
Lemma lem2406673 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem2406674 : term26 = term27.
Proof. exact (@lem2406673 term27). Qed.
Lemma lem2406689 : term25 = term27.
Proof. exact (TRANS (@lem2406671) (@lem2406674)). Qed.
Lemma lem2406690 : term28 = term28.
Proof. exact (eq_refl term28). Qed.
Lemma lem2406691 : term29 = term30.
Proof. exact (MK_COMB (@lem2406690) (@lem2406689)). Qed.
Lemma lem2406694 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2406695 : term32 = term33.
Proof. exact (MK_COMB (@lem2406694) (@lem2406691)). Qed.
Lemma lem2406698 : term34 = term34.
Proof. exact (eq_refl term34). Qed.
Lemma lem2406699 : term35 = term36.
Proof. exact (MK_COMB (@lem2406698) (@lem2406695)). Qed.
Lemma lem2406702 : term37 = term37.
Proof. exact (eq_refl term37). Qed.
Lemma lem2406703 : term38 = term39.
Proof. exact (MK_COMB (@lem2406702) (@lem2406699)). Qed.
Lemma lem2406706 : term40 = term40.
Proof. exact (eq_refl term40). Qed.
Lemma lem2406707 : term41 = term42.
Proof. exact (MK_COMB (@lem2406706) (@lem2406703)). Qed.
Lemma lem2406710 : term43 = term43.
Proof. exact (eq_refl term43). Qed.
Lemma lem2406711 : term44 = term45.
Proof. exact (MK_COMB (@lem2406710) (@lem2406707)). Qed.
Lemma lem2406714 : term46 = term46.
Proof. exact (eq_refl term46). Qed.
Lemma lem2406715 : term47 = term48.
Proof. exact (MK_COMB (@lem2406714) (@lem2406711)). Qed.
Lemma lem2406718 : term48 = term47.
Proof. exact (SYM (@lem2406715)). Qed.
Lemma lem2406719 : term49 = term48.
Proof. exact (@lem2318604 term48). Qed.
Lemma lem2406804 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406805 (x : int) (y : int) : (term52 x y) = (term53 x y).
Proof. exact (@lem2406804 (term54 x y)). Qed.
Lemma lem2406806 (x : int) (y : int) (z : int) : (term55 x y z) = ((term56 x y z) = (term57 x y z)).
Proof. exact (eq_refl (term55 x y z)). Qed.
Lemma lem2406807 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406809 (x : int) (y : int) (z : int) : (term58 x y z) = (term59 x y z).
Proof. exact (MK_COMB (@lem2406807) (@lem2406806 x y z)). Qed.
Lemma lem2406810 (x : int) (y : int) : (term60 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : int => @lem2406809 x y z)). Qed.
Lemma lem2406811 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406812 (x : int) (y : int) : (term53 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem2406811) (@lem2406810 x y)). Qed.
Lemma lem2406813 (x : int) (y : int) : (term52 x y) = (term62 x y).
Proof. exact (TRANS (@lem2406805 x y) (@lem2406812 x y)). Qed.
Lemma lem2406814 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406815 (x : int) : (term63 x) = (term64 x).
Proof. exact (@lem2406814 (term65 x)). Qed.
Lemma lem2406816 (x : int) (y : int) : (term66 x y) = (term67 x y).
Proof. exact (eq_refl (term66 x y)). Qed.
Lemma lem2406817 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406818 (x : int) (y : int) : (term68 x y) = (term52 x y).
Proof. exact (MK_COMB (@lem2406817) (@lem2406816 x y)). Qed.
Lemma lem2406819 (x : int) (y : int) : (term68 x y) = (term62 x y).
Proof. exact (TRANS (@lem2406818 x y) (@lem2406813 x y)). Qed.
Lemma lem2406820 (x : int) : (term69 x) = (term70 x).
Proof. exact (fun_ext (fun y : int => @lem2406819 x y)). Qed.
Lemma lem2406821 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406822 (x : int) : (term64 x) = (term71 x).
Proof. exact (MK_COMB (@lem2406821) (@lem2406820 x)). Qed.
Lemma lem2406823 (x : int) : (term63 x) = (term71 x).
Proof. exact (TRANS (@lem2406815 x) (@lem2406822 x)). Qed.
Lemma lem2406824 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406825 : term72 = term73.
Proof. exact (@lem2406824 term74). Qed.
Lemma lem2406826 (x : int) : (term75 x) = (term76 x).
Proof. exact (eq_refl (term75 x)). Qed.
Lemma lem2406827 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406828 (x : int) : (term77 x) = (term63 x).
Proof. exact (MK_COMB (@lem2406827) (@lem2406826 x)). Qed.
Lemma lem2406829 (x : int) : (term77 x) = (term71 x).
Proof. exact (TRANS (@lem2406828 x) (@lem2406823 x)). Qed.
Lemma lem2406830 : term78 = term79.
Proof. exact (fun_ext (fun x : int => @lem2406829 x)). Qed.
Lemma lem2406831 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406832 : term73 = term80.
Proof. exact (MK_COMB (@lem2406831) (@lem2406830)). Qed.
Lemma lem2406833 : term72 = term80.
Proof. exact (TRANS (@lem2406825) (@lem2406832)). Qed.
Lemma lem2406835 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406836 (x : int) : (term81 x) = (term82 x).
Proof. exact (@lem2406835 (term83 x)). Qed.
Lemma lem2406837 (y : int) (x : int) : (term84 x y) = ((int_add x y) = (int_add y x)).
Proof. exact (eq_refl (term84 x y)). Qed.
Lemma lem2406838 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406840 (y : int) (x : int) : (term85 x y) = (term86 y x).
Proof. exact (MK_COMB (@lem2406838) (@lem2406837 y x)). Qed.
Lemma lem2406841 (x : int) : (term87 x) = (term88 x).
Proof. exact (fun_ext (fun y : int => @lem2406840 y x)). Qed.
Lemma lem2406842 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406843 (x : int) : (term82 x) = (term89 x).
Proof. exact (MK_COMB (@lem2406842) (@lem2406841 x)). Qed.
Lemma lem2406844 (x : int) : (term81 x) = (term89 x).
Proof. exact (TRANS (@lem2406836 x) (@lem2406843 x)). Qed.
Lemma lem2406845 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406846 : term90 = term91.
Proof. exact (@lem2406845 term92). Qed.
Lemma lem2406847 (x : int) : (term93 x) = (term94 x).
Proof. exact (eq_refl (term93 x)). Qed.
Lemma lem2406848 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406849 (x : int) : (term95 x) = (term81 x).
Proof. exact (MK_COMB (@lem2406848) (@lem2406847 x)). Qed.
Lemma lem2406850 (x : int) : (term95 x) = (term89 x).
Proof. exact (TRANS (@lem2406849 x) (@lem2406844 x)). Qed.
Lemma lem2406851 : term96 = term97.
Proof. exact (fun_ext (fun x : int => @lem2406850 x)). Qed.
Lemma lem2406852 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406853 : term91 = term98.
Proof. exact (MK_COMB (@lem2406852) (@lem2406851)). Qed.
Lemma lem2406854 : term90 = term98.
Proof. exact (TRANS (@lem2406846) (@lem2406853)). Qed.
Lemma lem2406856 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406857 : term99 = term100.
Proof. exact (@lem2406856 term101). Qed.
Lemma lem2406858 (x : int) : (term102 x) = ((term103 x) = x).
Proof. exact (eq_refl (term102 x)). Qed.
Lemma lem2406859 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406861 (x : int) : (term104 x) = (term105 x).
Proof. exact (MK_COMB (@lem2406859) (@lem2406858 x)). Qed.
Lemma lem2406862 : term106 = term107.
Proof. exact (fun_ext (fun x : int => @lem2406861 x)). Qed.
Lemma lem2406863 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406864 : term100 = term108.
Proof. exact (MK_COMB (@lem2406863) (@lem2406862)). Qed.
Lemma lem2406865 : term99 = term108.
Proof. exact (TRANS (@lem2406857) (@lem2406864)). Qed.
Lemma lem2406867 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406868 (x : int) (y : int) : (term109 x y) = (term110 x y).
Proof. exact (@lem2406867 (term111 x y)). Qed.
Lemma lem2406869 (x : int) (y : int) (z : int) : (term112 x y z) = ((term113 x y z) = (term114 x y z)).
Proof. exact (eq_refl (term112 x y z)). Qed.
Lemma lem2406870 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406872 (x : int) (y : int) (z : int) : (term115 x y z) = (term116 x y z).
Proof. exact (MK_COMB (@lem2406870) (@lem2406869 x y z)). Qed.
Lemma lem2406873 (x : int) (y : int) : (term117 x y) = (term118 x y).
Proof. exact (fun_ext (fun z : int => @lem2406872 x y z)). Qed.
Lemma lem2406874 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406875 (x : int) (y : int) : (term110 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem2406874) (@lem2406873 x y)). Qed.
Lemma lem2406876 (x : int) (y : int) : (term109 x y) = (term119 x y).
Proof. exact (TRANS (@lem2406868 x y) (@lem2406875 x y)). Qed.
Lemma lem2406877 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406878 (x : int) : (term120 x) = (term121 x).
Proof. exact (@lem2406877 (term122 x)). Qed.
Lemma lem2406879 (x : int) (y : int) : (term123 x y) = (term124 x y).
Proof. exact (eq_refl (term123 x y)). Qed.
Lemma lem2406880 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406881 (x : int) (y : int) : (term125 x y) = (term109 x y).
Proof. exact (MK_COMB (@lem2406880) (@lem2406879 x y)). Qed.
Lemma lem2406882 (x : int) (y : int) : (term125 x y) = (term119 x y).
Proof. exact (TRANS (@lem2406881 x y) (@lem2406876 x y)). Qed.
Lemma lem2406883 (x : int) : (term126 x) = (term127 x).
Proof. exact (fun_ext (fun y : int => @lem2406882 x y)). Qed.
Lemma lem2406884 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406885 (x : int) : (term121 x) = (term128 x).
Proof. exact (MK_COMB (@lem2406884) (@lem2406883 x)). Qed.
Lemma lem2406886 (x : int) : (term120 x) = (term128 x).
Proof. exact (TRANS (@lem2406878 x) (@lem2406885 x)). Qed.
Lemma lem2406887 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406888 : term129 = term130.
Proof. exact (@lem2406887 term131). Qed.
Lemma lem2406889 (x : int) : (term132 x) = (term133 x).
Proof. exact (eq_refl (term132 x)). Qed.
Lemma lem2406890 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406891 (x : int) : (term134 x) = (term120 x).
Proof. exact (MK_COMB (@lem2406890) (@lem2406889 x)). Qed.
Lemma lem2406892 (x : int) : (term134 x) = (term128 x).
Proof. exact (TRANS (@lem2406891 x) (@lem2406886 x)). Qed.
Lemma lem2406893 : term135 = term136.
Proof. exact (fun_ext (fun x : int => @lem2406892 x)). Qed.
Lemma lem2406894 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406895 : term130 = term137.
Proof. exact (MK_COMB (@lem2406894) (@lem2406893)). Qed.
Lemma lem2406896 : term129 = term137.
Proof. exact (TRANS (@lem2406888) (@lem2406895)). Qed.
Lemma lem2406898 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406899 (x : int) : (term138 x) = (term139 x).
Proof. exact (@lem2406898 (term140 x)). Qed.
Lemma lem2406900 (y : int) (x : int) : (term141 x y) = ((int_mul x y) = (int_mul y x)).
Proof. exact (eq_refl (term141 x y)). Qed.
Lemma lem2406901 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406903 (y : int) (x : int) : (term142 x y) = (term143 y x).
Proof. exact (MK_COMB (@lem2406901) (@lem2406900 y x)). Qed.
Lemma lem2406904 (x : int) : (term144 x) = (term145 x).
Proof. exact (fun_ext (fun y : int => @lem2406903 y x)). Qed.
Lemma lem2406905 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406906 (x : int) : (term139 x) = (term146 x).
Proof. exact (MK_COMB (@lem2406905) (@lem2406904 x)). Qed.
Lemma lem2406907 (x : int) : (term138 x) = (term146 x).
Proof. exact (TRANS (@lem2406899 x) (@lem2406906 x)). Qed.
Lemma lem2406908 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406909 : term147 = term148.
Proof. exact (@lem2406908 term149). Qed.
Lemma lem2406910 (x : int) : (term150 x) = (term151 x).
Proof. exact (eq_refl (term150 x)). Qed.
Lemma lem2406911 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406912 (x : int) : (term152 x) = (term138 x).
Proof. exact (MK_COMB (@lem2406911) (@lem2406910 x)). Qed.
Lemma lem2406913 (x : int) : (term152 x) = (term146 x).
Proof. exact (TRANS (@lem2406912 x) (@lem2406907 x)). Qed.
Lemma lem2406914 : term153 = term154.
Proof. exact (fun_ext (fun x : int => @lem2406913 x)). Qed.
Lemma lem2406915 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406916 : term148 = term155.
Proof. exact (MK_COMB (@lem2406915) (@lem2406914)). Qed.
Lemma lem2406917 : term147 = term155.
Proof. exact (TRANS (@lem2406909) (@lem2406916)). Qed.
Lemma lem2406919 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406920 : term156 = term157.
Proof. exact (@lem2406919 term158). Qed.
Lemma lem2406921 (x : int) : (term159 x) = ((term160 x) = x).
Proof. exact (eq_refl (term159 x)). Qed.
Lemma lem2406922 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406924 (x : int) : (term161 x) = (term162 x).
Proof. exact (MK_COMB (@lem2406922) (@lem2406921 x)). Qed.
Lemma lem2406925 : term163 = term164.
Proof. exact (fun_ext (fun x : int => @lem2406924 x)). Qed.
Lemma lem2406926 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406927 : term157 = term165.
Proof. exact (MK_COMB (@lem2406926) (@lem2406925)). Qed.
Lemma lem2406928 : term156 = term165.
Proof. exact (TRANS (@lem2406920) (@lem2406927)). Qed.
Lemma lem2406930 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406931 : term166 = term167.
Proof. exact (@lem2406930 term168). Qed.
Lemma lem2406932 (x : int) : (term169 x) = ((term170 x) = term171).
Proof. exact (eq_refl (term169 x)). Qed.
Lemma lem2406933 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406935 (x : int) : (term172 x) = (term173 x).
Proof. exact (MK_COMB (@lem2406933) (@lem2406932 x)). Qed.
Lemma lem2406936 : term174 = term175.
Proof. exact (fun_ext (fun x : int => @lem2406935 x)). Qed.
Lemma lem2406937 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406938 : term167 = term176.
Proof. exact (MK_COMB (@lem2406937) (@lem2406936)). Qed.
Lemma lem2406939 : term166 = term176.
Proof. exact (TRANS (@lem2406931) (@lem2406938)). Qed.
Lemma lem2406941 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406942 (y : int) (x : int) : (term177 y x) = (term178 y x).
Proof. exact (@lem2406941 (term179 y x)). Qed.
Lemma lem2406943 (y : int) (x : int) (z : int) : (term180 y x z) = ((term181 x y z) = (term182 y x z)).
Proof. exact (eq_refl (term180 y x z)). Qed.
Lemma lem2406944 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406946 (y : int) (x : int) (z : int) : (term183 y x z) = (term184 y x z).
Proof. exact (MK_COMB (@lem2406944) (@lem2406943 y x z)). Qed.
Lemma lem2406947 (y : int) (x : int) : (term185 y x) = (term186 y x).
Proof. exact (fun_ext (fun z : int => @lem2406946 y x z)). Qed.
Lemma lem2406948 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406949 (y : int) (x : int) : (term178 y x) = (term187 y x).
Proof. exact (MK_COMB (@lem2406948) (@lem2406947 y x)). Qed.
Lemma lem2406950 (y : int) (x : int) : (term177 y x) = (term187 y x).
Proof. exact (TRANS (@lem2406942 y x) (@lem2406949 y x)). Qed.
Lemma lem2406951 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406952 (x : int) : (term188 x) = (term189 x).
Proof. exact (@lem2406951 (term190 x)). Qed.
Lemma lem2406953 (y : int) (x : int) : (term191 x y) = (term192 y x).
Proof. exact (eq_refl (term191 x y)). Qed.
Lemma lem2406954 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406955 (y : int) (x : int) : (term193 x y) = (term177 y x).
Proof. exact (MK_COMB (@lem2406954) (@lem2406953 y x)). Qed.
Lemma lem2406956 (y : int) (x : int) : (term193 x y) = (term187 y x).
Proof. exact (TRANS (@lem2406955 y x) (@lem2406950 y x)). Qed.
Lemma lem2406957 (x : int) : (term194 x) = (term195 x).
Proof. exact (fun_ext (fun y : int => @lem2406956 y x)). Qed.
Lemma lem2406958 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406959 (x : int) : (term189 x) = (term196 x).
Proof. exact (MK_COMB (@lem2406958) (@lem2406957 x)). Qed.
Lemma lem2406960 (x : int) : (term188 x) = (term196 x).
Proof. exact (TRANS (@lem2406952 x) (@lem2406959 x)). Qed.
Lemma lem2406961 (P : int -> Prop) : (term50 P) = (term51 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2406962 : term197 = term198.
Proof. exact (@lem2406961 term199). Qed.
Lemma lem2406963 (x : int) : (term200 x) = (term201 x).
Proof. exact (eq_refl (term200 x)). Qed.
Lemma lem2406964 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2406965 (x : int) : (term202 x) = (term188 x).
Proof. exact (MK_COMB (@lem2406964) (@lem2406963 x)). Qed.
Lemma lem2406966 (x : int) : (term202 x) = (term196 x).
Proof. exact (TRANS (@lem2406965 x) (@lem2406960 x)). Qed.
Lemma lem2406967 : term203 = term204.
Proof. exact (fun_ext (fun x : int => @lem2406966 x)). Qed.
Lemma lem2406968 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2406969 : term198 = term205.
Proof. exact (MK_COMB (@lem2406968) (@lem2406967)). Qed.
Lemma lem2406970 : term197 = term205.
Proof. exact (TRANS (@lem2406962) (@lem2406969)). Qed.
Lemma lem2406971 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2406972 : term206 = term207.
Proof. exact (MK_COMB (@lem2406971) (@lem2406939)). Qed.
Lemma lem2406973 : term208 = term209.
Proof. exact (MK_COMB (@lem2406972) (@lem2406970)). Qed.
Lemma lem2406974 : term210 = term208.
Proof. exact (@lem17045 term211 term27). Qed.
Lemma lem2406975 : term210 = term209.
Proof. exact (TRANS (@lem2406974) (@lem2406973)). Qed.
Lemma lem2406976 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2406977 : term212 = term213.
Proof. exact (MK_COMB (@lem2406976) (@lem2406928)). Qed.
Lemma lem2406978 : term214 = term215.
Proof. exact (MK_COMB (@lem2406977) (@lem2406975)). Qed.
Lemma lem2406979 : term216 = term214.
Proof. exact (@lem17045 term217 term30). Qed.
Lemma lem2406980 : term216 = term215.
Proof. exact (TRANS (@lem2406979) (@lem2406978)). Qed.
Lemma lem2406981 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2406982 : term218 = term219.
Proof. exact (MK_COMB (@lem2406981) (@lem2406917)). Qed.
Lemma lem2406983 : term220 = term221.
Proof. exact (MK_COMB (@lem2406982) (@lem2406980)). Qed.
Lemma lem2406984 : term222 = term220.
Proof. exact (@lem17045 term223 term33). Qed.
Lemma lem2406985 : term222 = term221.
Proof. exact (TRANS (@lem2406984) (@lem2406983)). Qed.
Lemma lem2406986 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2406987 : term224 = term225.
Proof. exact (MK_COMB (@lem2406986) (@lem2406896)). Qed.
Lemma lem2406988 : term226 = term227.
Proof. exact (MK_COMB (@lem2406987) (@lem2406985)). Qed.
Lemma lem2406989 : term228 = term226.
Proof. exact (@lem17045 term229 term36). Qed.
Lemma lem2406990 : term228 = term227.
Proof. exact (TRANS (@lem2406989) (@lem2406988)). Qed.
Lemma lem2406991 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2406992 : term230 = term231.
Proof. exact (MK_COMB (@lem2406991) (@lem2406865)). Qed.
Lemma lem2406993 : term232 = term233.
Proof. exact (MK_COMB (@lem2406992) (@lem2406990)). Qed.
Lemma lem2406994 : term234 = term232.
Proof. exact (@lem17045 term235 term39). Qed.
Lemma lem2406995 : term234 = term233.
Proof. exact (TRANS (@lem2406994) (@lem2406993)). Qed.
Lemma lem2406996 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2406997 : term236 = term237.
Proof. exact (MK_COMB (@lem2406996) (@lem2406854)). Qed.
Lemma lem2406998 : term238 = term239.
Proof. exact (MK_COMB (@lem2406997) (@lem2406995)). Qed.
Lemma lem2406999 : term240 = term238.
Proof. exact (@lem17045 term241 term42). Qed.
Lemma lem2407000 : term240 = term239.
Proof. exact (TRANS (@lem2406999) (@lem2406998)). Qed.
Lemma lem2407001 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407002 : term242 = term243.
Proof. exact (MK_COMB (@lem2407001) (@lem2406833)). Qed.
Lemma lem2407003 : term244 = term245.
Proof. exact (MK_COMB (@lem2407002) (@lem2407000)). Qed.
Lemma lem2407004 : term246 = term244.
Proof. exact (@lem17045 term247 term45). Qed.
Lemma lem2407006 : term246 = term245.
Proof. exact (TRANS (@lem2407004) (@lem2407003)). Qed.
Lemma lem2407009 (x : int) (y : int) (z : int) : (term59 x y z) = (term59 x y z).
Proof. exact (eq_refl (term59 x y z)). Qed.
Lemma lem2407010 (x : int) (y : int) : (term61 x y) = (term61 x y).
Proof. exact (fun_ext (fun z : int => @lem2407009 x y z)). Qed.
Lemma lem2407011 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407012 (x : int) (y : int) : (term62 x y) = (term62 x y).
Proof. exact (MK_COMB (@lem2407011) (@lem2407010 x y)). Qed.
Lemma lem2407013 (x : int) : (term70 x) = (term70 x).
Proof. exact (fun_ext (fun y : int => @lem2407012 x y)). Qed.
Lemma lem2407014 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407015 (x : int) : (term71 x) = (term71 x).
Proof. exact (MK_COMB (@lem2407014) (@lem2407013 x)). Qed.
Lemma lem2407016 : term79 = term79.
Proof. exact (fun_ext (fun x : int => @lem2407015 x)). Qed.
Lemma lem2407017 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407018 : term80 = term80.
Proof. exact (MK_COMB (@lem2407017) (@lem2407016)). Qed.
Lemma lem2407021 (y : int) (x : int) : (term86 y x) = (term86 y x).
Proof. exact (eq_refl (term86 y x)). Qed.
Lemma lem2407022 (x : int) : (term88 x) = (term88 x).
Proof. exact (fun_ext (fun y : int => @lem2407021 y x)). Qed.
Lemma lem2407023 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407024 (x : int) : (term89 x) = (term89 x).
Proof. exact (MK_COMB (@lem2407023) (@lem2407022 x)). Qed.
Lemma lem2407025 : term97 = term97.
Proof. exact (fun_ext (fun x : int => @lem2407024 x)). Qed.
Lemma lem2407026 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407027 : term98 = term98.
Proof. exact (MK_COMB (@lem2407026) (@lem2407025)). Qed.
Lemma lem2407030 (x : int) : (term105 x) = (term105 x).
Proof. exact (eq_refl (term105 x)). Qed.
Lemma lem2407031 : term107 = term107.
Proof. exact (fun_ext (fun x : int => @lem2407030 x)). Qed.
Lemma lem2407032 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407033 : term108 = term108.
Proof. exact (MK_COMB (@lem2407032) (@lem2407031)). Qed.
Lemma lem2407036 (x : int) (y : int) (z : int) : (term116 x y z) = (term116 x y z).
Proof. exact (eq_refl (term116 x y z)). Qed.
Lemma lem2407037 (x : int) (y : int) : (term118 x y) = (term118 x y).
Proof. exact (fun_ext (fun z : int => @lem2407036 x y z)). Qed.
Lemma lem2407038 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407039 (x : int) (y : int) : (term119 x y) = (term119 x y).
Proof. exact (MK_COMB (@lem2407038) (@lem2407037 x y)). Qed.
Lemma lem2407040 (x : int) : (term127 x) = (term127 x).
Proof. exact (fun_ext (fun y : int => @lem2407039 x y)). Qed.
Lemma lem2407041 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407042 (x : int) : (term128 x) = (term128 x).
Proof. exact (MK_COMB (@lem2407041) (@lem2407040 x)). Qed.
Lemma lem2407043 : term136 = term136.
Proof. exact (fun_ext (fun x : int => @lem2407042 x)). Qed.
Lemma lem2407044 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407045 : term137 = term137.
Proof. exact (MK_COMB (@lem2407044) (@lem2407043)). Qed.
Lemma lem2407048 (y : int) (x : int) : (term143 y x) = (term143 y x).
Proof. exact (eq_refl (term143 y x)). Qed.
Lemma lem2407049 (x : int) : (term145 x) = (term145 x).
Proof. exact (fun_ext (fun y : int => @lem2407048 y x)). Qed.
Lemma lem2407050 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407051 (x : int) : (term146 x) = (term146 x).
Proof. exact (MK_COMB (@lem2407050) (@lem2407049 x)). Qed.
Lemma lem2407052 : term154 = term154.
Proof. exact (fun_ext (fun x : int => @lem2407051 x)). Qed.
Lemma lem2407053 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407054 : term155 = term155.
Proof. exact (MK_COMB (@lem2407053) (@lem2407052)). Qed.
Lemma lem2407057 (x : int) : (term162 x) = (term162 x).
Proof. exact (eq_refl (term162 x)). Qed.
Lemma lem2407058 : term164 = term164.
Proof. exact (fun_ext (fun x : int => @lem2407057 x)). Qed.
Lemma lem2407059 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407060 : term165 = term165.
Proof. exact (MK_COMB (@lem2407059) (@lem2407058)). Qed.
Lemma lem2407063 (x : int) : (term173 x) = (term173 x).
Proof. exact (eq_refl (term173 x)). Qed.
Lemma lem2407064 : term175 = term175.
Proof. exact (fun_ext (fun x : int => @lem2407063 x)). Qed.
Lemma lem2407065 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407066 : term176 = term176.
Proof. exact (MK_COMB (@lem2407065) (@lem2407064)). Qed.
Lemma lem2407069 (y : int) (x : int) (z : int) : (term184 y x z) = (term184 y x z).
Proof. exact (eq_refl (term184 y x z)). Qed.
Lemma lem2407070 (y : int) (x : int) : (term186 y x) = (term186 y x).
Proof. exact (fun_ext (fun z : int => @lem2407069 y x z)). Qed.
Lemma lem2407071 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407072 (y : int) (x : int) : (term187 y x) = (term187 y x).
Proof. exact (MK_COMB (@lem2407071) (@lem2407070 y x)). Qed.
Lemma lem2407073 (x : int) : (term195 x) = (term195 x).
Proof. exact (fun_ext (fun y : int => @lem2407072 y x)). Qed.
Lemma lem2407074 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407075 (x : int) : (term196 x) = (term196 x).
Proof. exact (MK_COMB (@lem2407074) (@lem2407073 x)). Qed.
Lemma lem2407076 : term204 = term204.
Proof. exact (fun_ext (fun x : int => @lem2407075 x)). Qed.
Lemma lem2407077 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407078 : term205 = term205.
Proof. exact (MK_COMB (@lem2407077) (@lem2407076)). Qed.
Lemma lem2407079 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407080 : term207 = term207.
Proof. exact (MK_COMB (@lem2407079) (@lem2407066)). Qed.
Lemma lem2407081 : term209 = term209.
Proof. exact (MK_COMB (@lem2407080) (@lem2407078)). Qed.
Lemma lem2407082 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407083 : term213 = term213.
Proof. exact (MK_COMB (@lem2407082) (@lem2407060)). Qed.
Lemma lem2407084 : term215 = term215.
Proof. exact (MK_COMB (@lem2407083) (@lem2407081)). Qed.
Lemma lem2407085 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407086 : term219 = term219.
Proof. exact (MK_COMB (@lem2407085) (@lem2407054)). Qed.
Lemma lem2407087 : term221 = term221.
Proof. exact (MK_COMB (@lem2407086) (@lem2407084)). Qed.
Lemma lem2407088 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407089 : term225 = term225.
Proof. exact (MK_COMB (@lem2407088) (@lem2407045)). Qed.
Lemma lem2407090 : term227 = term227.
Proof. exact (MK_COMB (@lem2407089) (@lem2407087)). Qed.
Lemma lem2407091 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407092 : term231 = term231.
Proof. exact (MK_COMB (@lem2407091) (@lem2407033)). Qed.
Lemma lem2407093 : term233 = term233.
Proof. exact (MK_COMB (@lem2407092) (@lem2407090)). Qed.
Lemma lem2407094 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407095 : term237 = term237.
Proof. exact (MK_COMB (@lem2407094) (@lem2407027)). Qed.
Lemma lem2407096 : term239 = term239.
Proof. exact (MK_COMB (@lem2407095) (@lem2407093)). Qed.
Lemma lem2407097 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407098 : term243 = term243.
Proof. exact (MK_COMB (@lem2407097) (@lem2407018)). Qed.
Lemma lem2407099 : term245 = term245.
Proof. exact (MK_COMB (@lem2407098) (@lem2407096)). Qed.
Lemma lem2407100 : term246 = term245.
Proof. exact (TRANS (@lem2407006) (@lem2407099)). Qed.
Lemma lem2407102 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407103 (x : int) (y : int) (z : int) : (term59 x y z) = (term250 x y z).
Proof. exact (@lem2407102 (term57 x y z) (term56 x y z)). Qed.
Lemma lem2407105 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407106 (x : int) (y : int) (z : int) : (term252 x y z) = (term253 x y z).
Proof. exact (@lem2407105 (term254 x y z) (term57 x y z)). Qed.
Lemma lem2407108 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407109 (x : int) (y : int) (z : int) : (term257 x y z) = (term258 x y z).
Proof. exact (@lem2407108 (term56 x y z) term5). Qed.
Lemma lem2407111 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407112 (x : int) (y : int) (z : int) : (term259 x y z) = (term260 x y z).
Proof. exact (@lem2407111 x (int_add y z)). Qed.
Lemma lem2407114 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407115 (y : int) (z : int) : (term255 y z) = (term256 y z).
Proof. exact (@lem2407114 y z). Qed.
Lemma lem2407116 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2407117 (x : int) (y : int) (z : int) : (term260 x y z) = (term262 x y z).
Proof. exact (MK_COMB (@lem2407116 x) (@lem2407115 y z)). Qed.
Lemma lem2407118 (x : int) (y : int) (z : int) : (term259 x y z) = (term262 x y z).
Proof. exact (TRANS (@lem2407112 x y z) (@lem2407117 x y z)). Qed.
Lemma lem2407119 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407120 (x : int) (y : int) (z : int) : (term263 x y z) = (term264 x y z).
Proof. exact (MK_COMB (@lem2407119) (@lem2407118 x y z)). Qed.
Lemma lem2407122 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407123 : term266 = term267.
Proof. exact (@lem2407122 term268). Qed.
Lemma lem2407124 (x : int) (y : int) (z : int) : (term258 x y z) = (term269 x y z).
Proof. exact (MK_COMB (@lem2407120 x y z) (@lem2407123)). Qed.
Lemma lem2407125 (x : int) (y : int) (z : int) : (term257 x y z) = (term269 x y z).
Proof. exact (TRANS (@lem2407109 x y z) (@lem2407124 x y z)). Qed.
Lemma lem2407126 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407127 (x : int) (y : int) (z : int) : (term270 x y z) = (term271 x y z).
Proof. exact (MK_COMB (@lem2407126) (@lem2407125 x y z)). Qed.
Lemma lem2407129 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407130 (x : int) (y : int) (z : int) : (term272 x y z) = (term273 x y z).
Proof. exact (@lem2407129 (int_add x y) z). Qed.
Lemma lem2407132 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407133 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407134 (x : int) (y : int) : (term274 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem2407133) (@lem2407132 x y)). Qed.
Lemma lem2407135 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2407136 (x : int) (y : int) (z : int) : (term273 x y z) = (term276 x y z).
Proof. exact (MK_COMB (@lem2407134 x y) (@lem2407135 z)). Qed.
Lemma lem2407137 (x : int) (y : int) (z : int) : (term272 x y z) = (term276 x y z).
Proof. exact (TRANS (@lem2407130 x y z) (@lem2407136 x y z)). Qed.
Lemma lem2407138 (x : int) (y : int) (z : int) : (term253 x y z) = (term277 x y z).
Proof. exact (MK_COMB (@lem2407127 x y z) (@lem2407137 x y z)). Qed.
Lemma lem2407139 (x : int) (y : int) (z : int) : (term252 x y z) = (term277 x y z).
Proof. exact (TRANS (@lem2407106 x y z) (@lem2407138 x y z)). Qed.
Lemma lem2407140 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407141 (x : int) (y : int) (z : int) : (term278 x y z) = (term279 x y z).
Proof. exact (MK_COMB (@lem2407140) (@lem2407139 x y z)). Qed.
Lemma lem2407143 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407144 (x : int) (y : int) (z : int) : (term280 x y z) = (term281 x y z).
Proof. exact (@lem2407143 (term282 x y z) (term56 x y z)). Qed.
Lemma lem2407146 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407147 (x : int) (y : int) (z : int) : (term283 x y z) = (term284 x y z).
Proof. exact (@lem2407146 (term57 x y z) term5). Qed.
Lemma lem2407149 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407150 (x : int) (y : int) (z : int) : (term272 x y z) = (term273 x y z).
Proof. exact (@lem2407149 (int_add x y) z). Qed.
Lemma lem2407152 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407153 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407154 (x : int) (y : int) : (term274 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem2407153) (@lem2407152 x y)). Qed.
Lemma lem2407155 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2407156 (x : int) (y : int) (z : int) : (term273 x y z) = (term276 x y z).
Proof. exact (MK_COMB (@lem2407154 x y) (@lem2407155 z)). Qed.
Lemma lem2407157 (x : int) (y : int) (z : int) : (term272 x y z) = (term276 x y z).
Proof. exact (TRANS (@lem2407150 x y z) (@lem2407156 x y z)). Qed.
Lemma lem2407158 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407159 (x : int) (y : int) (z : int) : (term285 x y z) = (term286 x y z).
Proof. exact (MK_COMB (@lem2407158) (@lem2407157 x y z)). Qed.
Lemma lem2407161 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407162 : term266 = term267.
Proof. exact (@lem2407161 term268). Qed.
Lemma lem2407163 (x : int) (y : int) (z : int) : (term284 x y z) = (term287 x y z).
Proof. exact (MK_COMB (@lem2407159 x y z) (@lem2407162)). Qed.
Lemma lem2407164 (x : int) (y : int) (z : int) : (term283 x y z) = (term287 x y z).
Proof. exact (TRANS (@lem2407147 x y z) (@lem2407163 x y z)). Qed.
Lemma lem2407165 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407166 (x : int) (y : int) (z : int) : (term288 x y z) = (term289 x y z).
Proof. exact (MK_COMB (@lem2407165) (@lem2407164 x y z)). Qed.
Lemma lem2407168 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407169 (x : int) (y : int) (z : int) : (term259 x y z) = (term260 x y z).
Proof. exact (@lem2407168 x (int_add y z)). Qed.
Lemma lem2407171 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407172 (y : int) (z : int) : (term255 y z) = (term256 y z).
Proof. exact (@lem2407171 y z). Qed.
Lemma lem2407173 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2407174 (x : int) (y : int) (z : int) : (term260 x y z) = (term262 x y z).
Proof. exact (MK_COMB (@lem2407173 x) (@lem2407172 y z)). Qed.
Lemma lem2407175 (x : int) (y : int) (z : int) : (term259 x y z) = (term262 x y z).
Proof. exact (TRANS (@lem2407169 x y z) (@lem2407174 x y z)). Qed.
Lemma lem2407176 (x : int) (y : int) (z : int) : (term281 x y z) = (term290 x y z).
Proof. exact (MK_COMB (@lem2407166 x y z) (@lem2407175 x y z)). Qed.
Lemma lem2407177 (x : int) (y : int) (z : int) : (term280 x y z) = (term290 x y z).
Proof. exact (TRANS (@lem2407144 x y z) (@lem2407176 x y z)). Qed.
Lemma lem2407178 (x : int) (y : int) (z : int) : (term250 x y z) = (term291 x y z).
Proof. exact (MK_COMB (@lem2407141 x y z) (@lem2407177 x y z)). Qed.
Lemma lem2407179 (x : int) (y : int) (z : int) : (term59 x y z) = (term291 x y z).
Proof. exact (TRANS (@lem2407103 x y z) (@lem2407178 x y z)). Qed.
Lemma lem2407180 (x : int) (y : int) : (term61 x y) = (term292 x y).
Proof. exact (fun_ext (fun z : int => @lem2407179 x y z)). Qed.
Lemma lem2407181 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407182 (x : int) (y : int) : (term62 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem2407181) (@lem2407180 x y)). Qed.
Lemma lem2407183 (x : int) : (term70 x) = (term294 x).
Proof. exact (fun_ext (fun y : int => @lem2407182 x y)). Qed.
Lemma lem2407184 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407185 (x : int) : (term71 x) = (term295 x).
Proof. exact (MK_COMB (@lem2407184) (@lem2407183 x)). Qed.
Lemma lem2407186 : term79 = term296.
Proof. exact (fun_ext (fun x : int => @lem2407185 x)). Qed.
Lemma lem2407187 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407188 : term80 = term297.
Proof. exact (MK_COMB (@lem2407187) (@lem2407186)). Qed.
Lemma lem2407190 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407191 (x : int) (y : int) : (term86 y x) = (term298 x y).
Proof. exact (@lem2407190 (int_add y x) (int_add x y)). Qed.
Lemma lem2407193 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407194 (y : int) (x : int) : (term299 y x) = (term300 y x).
Proof. exact (@lem2407193 (term301 x y) (int_add y x)). Qed.
Lemma lem2407196 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407197 (x : int) (y : int) : (term302 x y) = (term303 x y).
Proof. exact (@lem2407196 (int_add x y) term5). Qed.
Lemma lem2407199 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407200 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407201 (x : int) (y : int) : (term274 x y) = (term275 x y).
Proof. exact (MK_COMB (@lem2407200) (@lem2407199 x y)). Qed.
Lemma lem2407203 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407204 : term266 = term267.
Proof. exact (@lem2407203 term268). Qed.
Lemma lem2407205 (x : int) (y : int) : (term303 x y) = (term304 x y).
Proof. exact (MK_COMB (@lem2407201 x y) (@lem2407204)). Qed.
Lemma lem2407206 (x : int) (y : int) : (term302 x y) = (term304 x y).
Proof. exact (TRANS (@lem2407197 x y) (@lem2407205 x y)). Qed.
Lemma lem2407207 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407208 (x : int) (y : int) : (term305 x y) = (term306 x y).
Proof. exact (MK_COMB (@lem2407207) (@lem2407206 x y)). Qed.
Lemma lem2407210 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407211 (y : int) (x : int) : (term255 y x) = (term256 y x).
Proof. exact (@lem2407210 y x). Qed.
Lemma lem2407212 (y : int) (x : int) : (term300 y x) = (term307 y x).
Proof. exact (MK_COMB (@lem2407208 x y) (@lem2407211 y x)). Qed.
Lemma lem2407213 (y : int) (x : int) : (term299 y x) = (term307 y x).
Proof. exact (TRANS (@lem2407194 y x) (@lem2407212 y x)). Qed.
Lemma lem2407214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407215 (y : int) (x : int) : (term308 y x) = (term309 y x).
Proof. exact (MK_COMB (@lem2407214) (@lem2407213 y x)). Qed.
Lemma lem2407217 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407218 (x : int) (y : int) : (term299 x y) = (term300 x y).
Proof. exact (@lem2407217 (term301 y x) (int_add x y)). Qed.
Lemma lem2407220 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407221 (y : int) (x : int) : (term302 y x) = (term303 y x).
Proof. exact (@lem2407220 (int_add y x) term5). Qed.
Lemma lem2407223 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407224 (y : int) (x : int) : (term255 y x) = (term256 y x).
Proof. exact (@lem2407223 y x). Qed.
Lemma lem2407225 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407226 (y : int) (x : int) : (term274 y x) = (term275 y x).
Proof. exact (MK_COMB (@lem2407225) (@lem2407224 y x)). Qed.
Lemma lem2407228 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407229 : term266 = term267.
Proof. exact (@lem2407228 term268). Qed.
Lemma lem2407230 (y : int) (x : int) : (term303 y x) = (term304 y x).
Proof. exact (MK_COMB (@lem2407226 y x) (@lem2407229)). Qed.
Lemma lem2407231 (y : int) (x : int) : (term302 y x) = (term304 y x).
Proof. exact (TRANS (@lem2407221 y x) (@lem2407230 y x)). Qed.
Lemma lem2407232 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407233 (y : int) (x : int) : (term305 y x) = (term306 y x).
Proof. exact (MK_COMB (@lem2407232) (@lem2407231 y x)). Qed.
Lemma lem2407235 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407236 (x : int) (y : int) : (term300 x y) = (term307 x y).
Proof. exact (MK_COMB (@lem2407233 y x) (@lem2407235 x y)). Qed.
Lemma lem2407237 (x : int) (y : int) : (term299 x y) = (term307 x y).
Proof. exact (TRANS (@lem2407218 x y) (@lem2407236 x y)). Qed.
Lemma lem2407238 (x : int) (y : int) : (term298 x y) = (term310 x y).
Proof. exact (MK_COMB (@lem2407215 y x) (@lem2407237 x y)). Qed.
Lemma lem2407239 (x : int) (y : int) : (term86 y x) = (term310 x y).
Proof. exact (TRANS (@lem2407191 x y) (@lem2407238 x y)). Qed.
Lemma lem2407240 (x : int) : (term88 x) = (term311 x).
Proof. exact (fun_ext (fun y : int => @lem2407239 x y)). Qed.
Lemma lem2407241 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407242 (x : int) : (term89 x) = (term312 x).
Proof. exact (MK_COMB (@lem2407241) (@lem2407240 x)). Qed.
Lemma lem2407243 : term97 = term313.
Proof. exact (fun_ext (fun x : int => @lem2407242 x)). Qed.
Lemma lem2407244 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407245 : term98 = term314.
Proof. exact (MK_COMB (@lem2407244) (@lem2407243)). Qed.
Lemma lem2407247 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407248 (x : int) : (term105 x) = (term315 x).
Proof. exact (@lem2407247 x (term103 x)). Qed.
Lemma lem2407250 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407251 (x : int) : (term316 x) = (term317 x).
Proof. exact (@lem2407250 (term318 x) x). Qed.
Lemma lem2407253 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407254 (x : int) : (term319 x) = (term320 x).
Proof. exact (@lem2407253 (term103 x) term5). Qed.
Lemma lem2407256 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407257 (x : int) : (term321 x) = (term322 x).
Proof. exact (@lem2407256 term171 x). Qed.
Lemma lem2407259 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407260 : term323 = term324.
Proof. exact (@lem2407259 (NUMERAL 0)). Qed.
Lemma lem2407261 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407262 : term325 = term326.
Proof. exact (MK_COMB (@lem2407261) (@lem2407260)). Qed.
Lemma lem2407263 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407264 (x : int) : (term322 x) = (term327 x).
Proof. exact (MK_COMB (@lem2407262) (@lem2407263 x)). Qed.
Lemma lem2407265 (x : int) : (term321 x) = (term327 x).
Proof. exact (TRANS (@lem2407257 x) (@lem2407264 x)). Qed.
Lemma lem2407266 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407267 (x : int) : (term328 x) = (term329 x).
Proof. exact (MK_COMB (@lem2407266) (@lem2407265 x)). Qed.
Lemma lem2407269 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407270 : term266 = term267.
Proof. exact (@lem2407269 term268). Qed.
Lemma lem2407271 (x : int) : (term320 x) = (term330 x).
Proof. exact (MK_COMB (@lem2407267 x) (@lem2407270)). Qed.
Lemma lem2407272 (x : int) : (term319 x) = (term330 x).
Proof. exact (TRANS (@lem2407254 x) (@lem2407271 x)). Qed.
Lemma lem2407273 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407274 (x : int) : (term331 x) = (term332 x).
Proof. exact (MK_COMB (@lem2407273) (@lem2407272 x)). Qed.
Lemma lem2407275 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407276 (x : int) : (term317 x) = (term333 x).
Proof. exact (MK_COMB (@lem2407274 x) (@lem2407275 x)). Qed.
Lemma lem2407277 (x : int) : (term316 x) = (term333 x).
Proof. exact (TRANS (@lem2407251 x) (@lem2407276 x)). Qed.
Lemma lem2407278 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407279 (x : int) : (term334 x) = (term335 x).
Proof. exact (MK_COMB (@lem2407278) (@lem2407277 x)). Qed.
Lemma lem2407281 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407282 (x : int) : (term336 x) = (term337 x).
Proof. exact (@lem2407281 (term338 x) (term103 x)). Qed.
Lemma lem2407284 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407285 (x : int) : (term339 x) = (term340 x).
Proof. exact (@lem2407284 x term5). Qed.
Lemma lem2407287 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407288 : term266 = term267.
Proof. exact (@lem2407287 term268). Qed.
Lemma lem2407289 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2407290 (x : int) : (term340 x) = (term341 x).
Proof. exact (MK_COMB (@lem2407289 x) (@lem2407288)). Qed.
Lemma lem2407291 (x : int) : (term339 x) = (term341 x).
Proof. exact (TRANS (@lem2407285 x) (@lem2407290 x)). Qed.
Lemma lem2407292 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407293 (x : int) : (term342 x) = (term343 x).
Proof. exact (MK_COMB (@lem2407292) (@lem2407291 x)). Qed.
Lemma lem2407295 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407296 (x : int) : (term321 x) = (term322 x).
Proof. exact (@lem2407295 term171 x). Qed.
Lemma lem2407298 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407299 : term323 = term324.
Proof. exact (@lem2407298 (NUMERAL 0)). Qed.
Lemma lem2407300 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407301 : term325 = term326.
Proof. exact (MK_COMB (@lem2407300) (@lem2407299)). Qed.
Lemma lem2407302 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407303 (x : int) : (term322 x) = (term327 x).
Proof. exact (MK_COMB (@lem2407301) (@lem2407302 x)). Qed.
Lemma lem2407304 (x : int) : (term321 x) = (term327 x).
Proof. exact (TRANS (@lem2407296 x) (@lem2407303 x)). Qed.
Lemma lem2407305 (x : int) : (term337 x) = (term344 x).
Proof. exact (MK_COMB (@lem2407293 x) (@lem2407304 x)). Qed.
Lemma lem2407306 (x : int) : (term336 x) = (term344 x).
Proof. exact (TRANS (@lem2407282 x) (@lem2407305 x)). Qed.
Lemma lem2407307 (x : int) : (term315 x) = (term345 x).
Proof. exact (MK_COMB (@lem2407279 x) (@lem2407306 x)). Qed.
Lemma lem2407308 (x : int) : (term105 x) = (term345 x).
Proof. exact (TRANS (@lem2407248 x) (@lem2407307 x)). Qed.
Lemma lem2407309 : term107 = term346.
Proof. exact (fun_ext (fun x : int => @lem2407308 x)). Qed.
Lemma lem2407310 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407311 : term108 = term347.
Proof. exact (MK_COMB (@lem2407310) (@lem2407309)). Qed.
Lemma lem2407313 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407314 (x : int) (y : int) (z : int) : (term116 x y z) = (term348 x y z).
Proof. exact (@lem2407313 (term114 x y z) (term113 x y z)). Qed.
Lemma lem2407316 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407317 (x : int) (y : int) (z : int) : (term349 x y z) = (term350 x y z).
Proof. exact (@lem2407316 (term351 x y z) (term114 x y z)). Qed.
Lemma lem2407319 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407320 (x : int) (y : int) (z : int) : (term352 x y z) = (term353 x y z).
Proof. exact (@lem2407319 (term113 x y z) term5). Qed.
Lemma lem2407322 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407323 (x : int) (y : int) (z : int) : (term356 x y z) = (term357 x y z).
Proof. exact (@lem2407322 x (int_mul y z)). Qed.
Lemma lem2407325 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407326 (y : int) (z : int) : (term354 y z) = (term355 y z).
Proof. exact (@lem2407325 y z). Qed.
Lemma lem2407327 (x : int) : (term358 x) = (term358 x).
Proof. exact (eq_refl (term358 x)). Qed.
Lemma lem2407328 (x : int) (y : int) (z : int) : (term357 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem2407327 x) (@lem2407326 y z)). Qed.
Lemma lem2407329 (x : int) (y : int) (z : int) : (term356 x y z) = (term359 x y z).
Proof. exact (TRANS (@lem2407323 x y z) (@lem2407328 x y z)). Qed.
Lemma lem2407330 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407331 (x : int) (y : int) (z : int) : (term360 x y z) = (term361 x y z).
Proof. exact (MK_COMB (@lem2407330) (@lem2407329 x y z)). Qed.
Lemma lem2407333 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407334 : term266 = term267.
Proof. exact (@lem2407333 term268). Qed.
Lemma lem2407335 (x : int) (y : int) (z : int) : (term353 x y z) = (term362 x y z).
Proof. exact (MK_COMB (@lem2407331 x y z) (@lem2407334)). Qed.
Lemma lem2407336 (x : int) (y : int) (z : int) : (term352 x y z) = (term362 x y z).
Proof. exact (TRANS (@lem2407320 x y z) (@lem2407335 x y z)). Qed.
Lemma lem2407337 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407338 (x : int) (y : int) (z : int) : (term363 x y z) = (term364 x y z).
Proof. exact (MK_COMB (@lem2407337) (@lem2407336 x y z)). Qed.
Lemma lem2407340 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407341 (x : int) (y : int) (z : int) : (term365 x y z) = (term366 x y z).
Proof. exact (@lem2407340 (int_mul x y) z). Qed.
Lemma lem2407343 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407344 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2407345 (x : int) (y : int) : (term367 x y) = (term368 x y).
Proof. exact (MK_COMB (@lem2407344) (@lem2407343 x y)). Qed.
Lemma lem2407346 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2407347 (x : int) (y : int) (z : int) : (term366 x y z) = (term369 x y z).
Proof. exact (MK_COMB (@lem2407345 x y) (@lem2407346 z)). Qed.
Lemma lem2407348 (x : int) (y : int) (z : int) : (term365 x y z) = (term369 x y z).
Proof. exact (TRANS (@lem2407341 x y z) (@lem2407347 x y z)). Qed.
Lemma lem2407349 (x : int) (y : int) (z : int) : (term350 x y z) = (term370 x y z).
Proof. exact (MK_COMB (@lem2407338 x y z) (@lem2407348 x y z)). Qed.
Lemma lem2407350 (x : int) (y : int) (z : int) : (term349 x y z) = (term370 x y z).
Proof. exact (TRANS (@lem2407317 x y z) (@lem2407349 x y z)). Qed.
Lemma lem2407351 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407352 (x : int) (y : int) (z : int) : (term371 x y z) = (term372 x y z).
Proof. exact (MK_COMB (@lem2407351) (@lem2407350 x y z)). Qed.
Lemma lem2407354 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407355 (x : int) (y : int) (z : int) : (term373 x y z) = (term374 x y z).
Proof. exact (@lem2407354 (term375 x y z) (term113 x y z)). Qed.
Lemma lem2407357 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407358 (x : int) (y : int) (z : int) : (term376 x y z) = (term377 x y z).
Proof. exact (@lem2407357 (term114 x y z) term5). Qed.
Lemma lem2407360 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407361 (x : int) (y : int) (z : int) : (term365 x y z) = (term366 x y z).
Proof. exact (@lem2407360 (int_mul x y) z). Qed.
Lemma lem2407363 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2407365 (x : int) (y : int) : (term367 x y) = (term368 x y).
Proof. exact (MK_COMB (@lem2407364) (@lem2407363 x y)). Qed.
Lemma lem2407366 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2407367 (x : int) (y : int) (z : int) : (term366 x y z) = (term369 x y z).
Proof. exact (MK_COMB (@lem2407365 x y) (@lem2407366 z)). Qed.
Lemma lem2407368 (x : int) (y : int) (z : int) : (term365 x y z) = (term369 x y z).
Proof. exact (TRANS (@lem2407361 x y z) (@lem2407367 x y z)). Qed.
Lemma lem2407369 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407370 (x : int) (y : int) (z : int) : (term378 x y z) = (term379 x y z).
Proof. exact (MK_COMB (@lem2407369) (@lem2407368 x y z)). Qed.
Lemma lem2407372 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407373 : term266 = term267.
Proof. exact (@lem2407372 term268). Qed.
Lemma lem2407374 (x : int) (y : int) (z : int) : (term377 x y z) = (term380 x y z).
Proof. exact (MK_COMB (@lem2407370 x y z) (@lem2407373)). Qed.
Lemma lem2407375 (x : int) (y : int) (z : int) : (term376 x y z) = (term380 x y z).
Proof. exact (TRANS (@lem2407358 x y z) (@lem2407374 x y z)). Qed.
Lemma lem2407376 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407377 (x : int) (y : int) (z : int) : (term381 x y z) = (term382 x y z).
Proof. exact (MK_COMB (@lem2407376) (@lem2407375 x y z)). Qed.
Lemma lem2407379 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407380 (x : int) (y : int) (z : int) : (term356 x y z) = (term357 x y z).
Proof. exact (@lem2407379 x (int_mul y z)). Qed.
Lemma lem2407382 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407383 (y : int) (z : int) : (term354 y z) = (term355 y z).
Proof. exact (@lem2407382 y z). Qed.
Lemma lem2407384 (x : int) : (term358 x) = (term358 x).
Proof. exact (eq_refl (term358 x)). Qed.
Lemma lem2407385 (x : int) (y : int) (z : int) : (term357 x y z) = (term359 x y z).
Proof. exact (MK_COMB (@lem2407384 x) (@lem2407383 y z)). Qed.
Lemma lem2407386 (x : int) (y : int) (z : int) : (term356 x y z) = (term359 x y z).
Proof. exact (TRANS (@lem2407380 x y z) (@lem2407385 x y z)). Qed.
Lemma lem2407387 (x : int) (y : int) (z : int) : (term374 x y z) = (term383 x y z).
Proof. exact (MK_COMB (@lem2407377 x y z) (@lem2407386 x y z)). Qed.
Lemma lem2407388 (x : int) (y : int) (z : int) : (term373 x y z) = (term383 x y z).
Proof. exact (TRANS (@lem2407355 x y z) (@lem2407387 x y z)). Qed.
Lemma lem2407389 (x : int) (y : int) (z : int) : (term348 x y z) = (term384 x y z).
Proof. exact (MK_COMB (@lem2407352 x y z) (@lem2407388 x y z)). Qed.
Lemma lem2407390 (x : int) (y : int) (z : int) : (term116 x y z) = (term384 x y z).
Proof. exact (TRANS (@lem2407314 x y z) (@lem2407389 x y z)). Qed.
Lemma lem2407391 (x : int) (y : int) : (term118 x y) = (term385 x y).
Proof. exact (fun_ext (fun z : int => @lem2407390 x y z)). Qed.
Lemma lem2407392 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407393 (x : int) (y : int) : (term119 x y) = (term386 x y).
Proof. exact (MK_COMB (@lem2407392) (@lem2407391 x y)). Qed.
Lemma lem2407394 (x : int) : (term127 x) = (term387 x).
Proof. exact (fun_ext (fun y : int => @lem2407393 x y)). Qed.
Lemma lem2407395 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407396 (x : int) : (term128 x) = (term388 x).
Proof. exact (MK_COMB (@lem2407395) (@lem2407394 x)). Qed.
Lemma lem2407397 : term136 = term389.
Proof. exact (fun_ext (fun x : int => @lem2407396 x)). Qed.
Lemma lem2407398 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407399 : term137 = term390.
Proof. exact (MK_COMB (@lem2407398) (@lem2407397)). Qed.
Lemma lem2407401 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407402 (x : int) (y : int) : (term143 y x) = (term391 x y).
Proof. exact (@lem2407401 (int_mul y x) (int_mul x y)). Qed.
Lemma lem2407404 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407405 (y : int) (x : int) : (term392 y x) = (term393 y x).
Proof. exact (@lem2407404 (term394 x y) (int_mul y x)). Qed.
Lemma lem2407407 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407408 (x : int) (y : int) : (term395 x y) = (term396 x y).
Proof. exact (@lem2407407 (int_mul x y) term5). Qed.
Lemma lem2407410 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407411 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407412 (x : int) (y : int) : (term397 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem2407411) (@lem2407410 x y)). Qed.
Lemma lem2407414 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407415 : term266 = term267.
Proof. exact (@lem2407414 term268). Qed.
Lemma lem2407416 (x : int) (y : int) : (term396 x y) = (term399 x y).
Proof. exact (MK_COMB (@lem2407412 x y) (@lem2407415)). Qed.
Lemma lem2407417 (x : int) (y : int) : (term395 x y) = (term399 x y).
Proof. exact (TRANS (@lem2407408 x y) (@lem2407416 x y)). Qed.
Lemma lem2407418 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407419 (x : int) (y : int) : (term400 x y) = (term401 x y).
Proof. exact (MK_COMB (@lem2407418) (@lem2407417 x y)). Qed.
Lemma lem2407421 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407422 (y : int) (x : int) : (term354 y x) = (term355 y x).
Proof. exact (@lem2407421 y x). Qed.
Lemma lem2407423 (y : int) (x : int) : (term393 y x) = (term402 y x).
Proof. exact (MK_COMB (@lem2407419 x y) (@lem2407422 y x)). Qed.
Lemma lem2407424 (y : int) (x : int) : (term392 y x) = (term402 y x).
Proof. exact (TRANS (@lem2407405 y x) (@lem2407423 y x)). Qed.
Lemma lem2407425 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407426 (y : int) (x : int) : (term403 y x) = (term404 y x).
Proof. exact (MK_COMB (@lem2407425) (@lem2407424 y x)). Qed.
Lemma lem2407428 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407429 (x : int) (y : int) : (term392 x y) = (term393 x y).
Proof. exact (@lem2407428 (term394 y x) (int_mul x y)). Qed.
Lemma lem2407431 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407432 (y : int) (x : int) : (term395 y x) = (term396 y x).
Proof. exact (@lem2407431 (int_mul y x) term5). Qed.
Lemma lem2407434 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407435 (y : int) (x : int) : (term354 y x) = (term355 y x).
Proof. exact (@lem2407434 y x). Qed.
Lemma lem2407436 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407437 (y : int) (x : int) : (term397 y x) = (term398 y x).
Proof. exact (MK_COMB (@lem2407436) (@lem2407435 y x)). Qed.
Lemma lem2407439 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407440 : term266 = term267.
Proof. exact (@lem2407439 term268). Qed.
Lemma lem2407441 (y : int) (x : int) : (term396 y x) = (term399 y x).
Proof. exact (MK_COMB (@lem2407437 y x) (@lem2407440)). Qed.
Lemma lem2407442 (y : int) (x : int) : (term395 y x) = (term399 y x).
Proof. exact (TRANS (@lem2407432 y x) (@lem2407441 y x)). Qed.
Lemma lem2407443 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407444 (y : int) (x : int) : (term400 y x) = (term401 y x).
Proof. exact (MK_COMB (@lem2407443) (@lem2407442 y x)). Qed.
Lemma lem2407446 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407447 (x : int) (y : int) : (term393 x y) = (term402 x y).
Proof. exact (MK_COMB (@lem2407444 y x) (@lem2407446 x y)). Qed.
Lemma lem2407448 (x : int) (y : int) : (term392 x y) = (term402 x y).
Proof. exact (TRANS (@lem2407429 x y) (@lem2407447 x y)). Qed.
Lemma lem2407449 (x : int) (y : int) : (term391 x y) = (term405 x y).
Proof. exact (MK_COMB (@lem2407426 y x) (@lem2407448 x y)). Qed.
Lemma lem2407450 (x : int) (y : int) : (term143 y x) = (term405 x y).
Proof. exact (TRANS (@lem2407402 x y) (@lem2407449 x y)). Qed.
Lemma lem2407451 (x : int) : (term145 x) = (term406 x).
Proof. exact (fun_ext (fun y : int => @lem2407450 x y)). Qed.
Lemma lem2407452 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407453 (x : int) : (term146 x) = (term407 x).
Proof. exact (MK_COMB (@lem2407452) (@lem2407451 x)). Qed.
Lemma lem2407454 : term154 = term408.
Proof. exact (fun_ext (fun x : int => @lem2407453 x)). Qed.
Lemma lem2407455 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407456 : term155 = term409.
Proof. exact (MK_COMB (@lem2407455) (@lem2407454)). Qed.
Lemma lem2407458 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407459 (x : int) : (term162 x) = (term410 x).
Proof. exact (@lem2407458 x (term160 x)). Qed.
Lemma lem2407461 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407462 (x : int) : (term411 x) = (term412 x).
Proof. exact (@lem2407461 (term413 x) x). Qed.
Lemma lem2407464 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407465 (x : int) : (term414 x) = (term415 x).
Proof. exact (@lem2407464 (term160 x) term5). Qed.
Lemma lem2407467 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407468 (x : int) : (term416 x) = (term417 x).
Proof. exact (@lem2407467 term5 x). Qed.
Lemma lem2407470 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407471 : term266 = term267.
Proof. exact (@lem2407470 term268). Qed.
Lemma lem2407472 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2407473 : term418 = term419.
Proof. exact (MK_COMB (@lem2407472) (@lem2407471)). Qed.
Lemma lem2407474 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407475 (x : int) : (term417 x) = (term420 x).
Proof. exact (MK_COMB (@lem2407473) (@lem2407474 x)). Qed.
Lemma lem2407476 (x : int) : (term416 x) = (term420 x).
Proof. exact (TRANS (@lem2407468 x) (@lem2407475 x)). Qed.
Lemma lem2407477 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407478 (x : int) : (term421 x) = (term422 x).
Proof. exact (MK_COMB (@lem2407477) (@lem2407476 x)). Qed.
Lemma lem2407480 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407481 : term266 = term267.
Proof. exact (@lem2407480 term268). Qed.
Lemma lem2407482 (x : int) : (term415 x) = (term423 x).
Proof. exact (MK_COMB (@lem2407478 x) (@lem2407481)). Qed.
Lemma lem2407483 (x : int) : (term414 x) = (term423 x).
Proof. exact (TRANS (@lem2407465 x) (@lem2407482 x)). Qed.
Lemma lem2407484 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407485 (x : int) : (term424 x) = (term425 x).
Proof. exact (MK_COMB (@lem2407484) (@lem2407483 x)). Qed.
Lemma lem2407486 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407487 (x : int) : (term412 x) = (term426 x).
Proof. exact (MK_COMB (@lem2407485 x) (@lem2407486 x)). Qed.
Lemma lem2407488 (x : int) : (term411 x) = (term426 x).
Proof. exact (TRANS (@lem2407462 x) (@lem2407487 x)). Qed.
Lemma lem2407489 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407490 (x : int) : (term427 x) = (term428 x).
Proof. exact (MK_COMB (@lem2407489) (@lem2407488 x)). Qed.
Lemma lem2407492 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407493 (x : int) : (term429 x) = (term430 x).
Proof. exact (@lem2407492 (term338 x) (term160 x)). Qed.
Lemma lem2407495 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407496 (x : int) : (term339 x) = (term340 x).
Proof. exact (@lem2407495 x term5). Qed.
Lemma lem2407498 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407499 : term266 = term267.
Proof. exact (@lem2407498 term268). Qed.
Lemma lem2407500 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2407501 (x : int) : (term340 x) = (term341 x).
Proof. exact (MK_COMB (@lem2407500 x) (@lem2407499)). Qed.
Lemma lem2407502 (x : int) : (term339 x) = (term341 x).
Proof. exact (TRANS (@lem2407496 x) (@lem2407501 x)). Qed.
Lemma lem2407503 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407504 (x : int) : (term342 x) = (term343 x).
Proof. exact (MK_COMB (@lem2407503) (@lem2407502 x)). Qed.
Lemma lem2407506 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407507 (x : int) : (term416 x) = (term417 x).
Proof. exact (@lem2407506 term5 x). Qed.
Lemma lem2407509 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407510 : term266 = term267.
Proof. exact (@lem2407509 term268). Qed.
Lemma lem2407511 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2407512 : term418 = term419.
Proof. exact (MK_COMB (@lem2407511) (@lem2407510)). Qed.
Lemma lem2407513 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407514 (x : int) : (term417 x) = (term420 x).
Proof. exact (MK_COMB (@lem2407512) (@lem2407513 x)). Qed.
Lemma lem2407515 (x : int) : (term416 x) = (term420 x).
Proof. exact (TRANS (@lem2407507 x) (@lem2407514 x)). Qed.
Lemma lem2407516 (x : int) : (term430 x) = (term431 x).
Proof. exact (MK_COMB (@lem2407504 x) (@lem2407515 x)). Qed.
Lemma lem2407517 (x : int) : (term429 x) = (term431 x).
Proof. exact (TRANS (@lem2407493 x) (@lem2407516 x)). Qed.
Lemma lem2407518 (x : int) : (term410 x) = (term432 x).
Proof. exact (MK_COMB (@lem2407490 x) (@lem2407517 x)). Qed.
Lemma lem2407519 (x : int) : (term162 x) = (term432 x).
Proof. exact (TRANS (@lem2407459 x) (@lem2407518 x)). Qed.
Lemma lem2407520 : term164 = term433.
Proof. exact (fun_ext (fun x : int => @lem2407519 x)). Qed.
Lemma lem2407521 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407522 : term165 = term434.
Proof. exact (MK_COMB (@lem2407521) (@lem2407520)). Qed.
Lemma lem2407524 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407525 (x : int) : (term173 x) = (term435 x).
Proof. exact (@lem2407524 term171 (term170 x)). Qed.
Lemma lem2407527 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407528 (x : int) : (term436 x) = (term437 x).
Proof. exact (@lem2407527 (term438 x) term171). Qed.
Lemma lem2407530 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407531 (x : int) : (term439 x) = (term440 x).
Proof. exact (@lem2407530 (term170 x) term5). Qed.
Lemma lem2407533 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407534 (x : int) : (term441 x) = (term442 x).
Proof. exact (@lem2407533 term171 x). Qed.
Lemma lem2407536 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407537 : term323 = term324.
Proof. exact (@lem2407536 (NUMERAL 0)). Qed.
Lemma lem2407538 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2407539 : term443 = term444.
Proof. exact (MK_COMB (@lem2407538) (@lem2407537)). Qed.
Lemma lem2407540 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407541 (x : int) : (term442 x) = (term445 x).
Proof. exact (MK_COMB (@lem2407539) (@lem2407540 x)). Qed.
Lemma lem2407542 (x : int) : (term441 x) = (term445 x).
Proof. exact (TRANS (@lem2407534 x) (@lem2407541 x)). Qed.
Lemma lem2407543 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407544 (x : int) : (term446 x) = (term447 x).
Proof. exact (MK_COMB (@lem2407543) (@lem2407542 x)). Qed.
Lemma lem2407546 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407547 : term266 = term267.
Proof. exact (@lem2407546 term268). Qed.
Lemma lem2407548 (x : int) : (term440 x) = (term448 x).
Proof. exact (MK_COMB (@lem2407544 x) (@lem2407547)). Qed.
Lemma lem2407549 (x : int) : (term439 x) = (term448 x).
Proof. exact (TRANS (@lem2407531 x) (@lem2407548 x)). Qed.
Lemma lem2407550 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407551 (x : int) : (term449 x) = (term450 x).
Proof. exact (MK_COMB (@lem2407550) (@lem2407549 x)). Qed.
Lemma lem2407553 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407554 : term323 = term324.
Proof. exact (@lem2407553 (NUMERAL 0)). Qed.
Lemma lem2407555 (x : int) : (term437 x) = (term451 x).
Proof. exact (MK_COMB (@lem2407551 x) (@lem2407554)). Qed.
Lemma lem2407556 (x : int) : (term436 x) = (term451 x).
Proof. exact (TRANS (@lem2407528 x) (@lem2407555 x)). Qed.
Lemma lem2407557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407558 (x : int) : (term452 x) = (term453 x).
Proof. exact (MK_COMB (@lem2407557) (@lem2407556 x)). Qed.
Lemma lem2407560 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407561 (x : int) : (term454 x) = (term455 x).
Proof. exact (@lem2407560 term456 (term170 x)). Qed.
Lemma lem2407563 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407564 : term457 = term458.
Proof. exact (@lem2407563 term171 term5). Qed.
Lemma lem2407566 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407567 : term323 = term324.
Proof. exact (@lem2407566 (NUMERAL 0)). Qed.
Lemma lem2407568 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407569 : term325 = term326.
Proof. exact (MK_COMB (@lem2407568) (@lem2407567)). Qed.
Lemma lem2407571 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407572 : term266 = term267.
Proof. exact (@lem2407571 term268). Qed.
Lemma lem2407573 : term458 = term459.
Proof. exact (MK_COMB (@lem2407569) (@lem2407572)). Qed.
Lemma lem2407574 : term457 = term459.
Proof. exact (TRANS (@lem2407564) (@lem2407573)). Qed.
Lemma lem2407575 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407576 : term460 = term461.
Proof. exact (MK_COMB (@lem2407575) (@lem2407574)). Qed.
Lemma lem2407578 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407579 (x : int) : (term441 x) = (term442 x).
Proof. exact (@lem2407578 term171 x). Qed.
Lemma lem2407581 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407582 : term323 = term324.
Proof. exact (@lem2407581 (NUMERAL 0)). Qed.
Lemma lem2407583 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2407584 : term443 = term444.
Proof. exact (MK_COMB (@lem2407583) (@lem2407582)). Qed.
Lemma lem2407585 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2407586 (x : int) : (term442 x) = (term445 x).
Proof. exact (MK_COMB (@lem2407584) (@lem2407585 x)). Qed.
Lemma lem2407587 (x : int) : (term441 x) = (term445 x).
Proof. exact (TRANS (@lem2407579 x) (@lem2407586 x)). Qed.
Lemma lem2407588 (x : int) : (term455 x) = (term462 x).
Proof. exact (MK_COMB (@lem2407576) (@lem2407587 x)). Qed.
Lemma lem2407589 (x : int) : (term454 x) = (term462 x).
Proof. exact (TRANS (@lem2407561 x) (@lem2407588 x)). Qed.
Lemma lem2407590 (x : int) : (term435 x) = (term463 x).
Proof. exact (MK_COMB (@lem2407558 x) (@lem2407589 x)). Qed.
Lemma lem2407591 (x : int) : (term173 x) = (term463 x).
Proof. exact (TRANS (@lem2407525 x) (@lem2407590 x)). Qed.
Lemma lem2407592 : term175 = term464.
Proof. exact (fun_ext (fun x : int => @lem2407591 x)). Qed.
Lemma lem2407593 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407594 : term176 = term465.
Proof. exact (MK_COMB (@lem2407593) (@lem2407592)). Qed.
Lemma lem2407596 (y : int) (x : int) : (term248 x y) = (term249 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem2407597 (x : int) (y : int) (z : int) : (term184 y x z) = (term466 x y z).
Proof. exact (@lem2407596 (term182 y x z) (term181 x y z)). Qed.
Lemma lem2407599 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407600 (y : int) (x : int) (z : int) : (term467 y x z) = (term468 y x z).
Proof. exact (@lem2407599 (term469 x y z) (term182 y x z)). Qed.
Lemma lem2407602 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407603 (x : int) (y : int) (z : int) : (term470 x y z) = (term471 x y z).
Proof. exact (@lem2407602 (term181 x y z) term5). Qed.
Lemma lem2407605 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407606 (x : int) (y : int) (z : int) : (term472 x y z) = (term473 x y z).
Proof. exact (@lem2407605 x (int_add y z)). Qed.
Lemma lem2407608 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407609 (y : int) (z : int) : (term255 y z) = (term256 y z).
Proof. exact (@lem2407608 y z). Qed.
Lemma lem2407610 (x : int) : (term358 x) = (term358 x).
Proof. exact (eq_refl (term358 x)). Qed.
Lemma lem2407611 (x : int) (y : int) (z : int) : (term473 x y z) = (term474 x y z).
Proof. exact (MK_COMB (@lem2407610 x) (@lem2407609 y z)). Qed.
Lemma lem2407612 (x : int) (y : int) (z : int) : (term472 x y z) = (term474 x y z).
Proof. exact (TRANS (@lem2407606 x y z) (@lem2407611 x y z)). Qed.
Lemma lem2407613 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407614 (x : int) (y : int) (z : int) : (term475 x y z) = (term476 x y z).
Proof. exact (MK_COMB (@lem2407613) (@lem2407612 x y z)). Qed.
Lemma lem2407616 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407617 : term266 = term267.
Proof. exact (@lem2407616 term268). Qed.
Lemma lem2407618 (x : int) (y : int) (z : int) : (term471 x y z) = (term477 x y z).
Proof. exact (MK_COMB (@lem2407614 x y z) (@lem2407617)). Qed.
Lemma lem2407619 (x : int) (y : int) (z : int) : (term470 x y z) = (term477 x y z).
Proof. exact (TRANS (@lem2407603 x y z) (@lem2407618 x y z)). Qed.
Lemma lem2407620 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407621 (x : int) (y : int) (z : int) : (term478 x y z) = (term479 x y z).
Proof. exact (MK_COMB (@lem2407620) (@lem2407619 x y z)). Qed.
Lemma lem2407623 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407624 (y : int) (x : int) (z : int) : (term480 y x z) = (term481 y x z).
Proof. exact (@lem2407623 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2407626 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407627 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407628 (x : int) (y : int) : (term397 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem2407627) (@lem2407626 x y)). Qed.
Lemma lem2407630 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407631 (x : int) (z : int) : (term354 x z) = (term355 x z).
Proof. exact (@lem2407630 x z). Qed.
Lemma lem2407632 (y : int) (x : int) (z : int) : (term481 y x z) = (term482 y x z).
Proof. exact (MK_COMB (@lem2407628 x y) (@lem2407631 x z)). Qed.
Lemma lem2407633 (y : int) (x : int) (z : int) : (term480 y x z) = (term482 y x z).
Proof. exact (TRANS (@lem2407624 y x z) (@lem2407632 y x z)). Qed.
Lemma lem2407634 (y : int) (x : int) (z : int) : (term468 y x z) = (term483 y x z).
Proof. exact (MK_COMB (@lem2407621 x y z) (@lem2407633 y x z)). Qed.
Lemma lem2407635 (y : int) (x : int) (z : int) : (term467 y x z) = (term483 y x z).
Proof. exact (TRANS (@lem2407600 y x z) (@lem2407634 y x z)). Qed.
Lemma lem2407636 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407637 (y : int) (x : int) (z : int) : (term484 y x z) = (term485 y x z).
Proof. exact (MK_COMB (@lem2407636) (@lem2407635 y x z)). Qed.
Lemma lem2407639 (x : int) (y : int) : (int_le x y) = (term251 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2407640 (x : int) (y : int) (z : int) : (term486 x y z) = (term487 x y z).
Proof. exact (@lem2407639 (term488 y x z) (term181 x y z)). Qed.
Lemma lem2407642 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407643 (y : int) (x : int) (z : int) : (term489 y x z) = (term490 y x z).
Proof. exact (@lem2407642 (term182 y x z) term5). Qed.
Lemma lem2407645 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407646 (y : int) (x : int) (z : int) : (term480 y x z) = (term481 y x z).
Proof. exact (@lem2407645 (int_mul x y) (int_mul x z)). Qed.
Lemma lem2407648 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407649 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407650 (x : int) (y : int) : (term397 x y) = (term398 x y).
Proof. exact (MK_COMB (@lem2407649) (@lem2407648 x y)). Qed.
Lemma lem2407652 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407653 (x : int) (z : int) : (term354 x z) = (term355 x z).
Proof. exact (@lem2407652 x z). Qed.
Lemma lem2407654 (y : int) (x : int) (z : int) : (term481 y x z) = (term482 y x z).
Proof. exact (MK_COMB (@lem2407650 x y) (@lem2407653 x z)). Qed.
Lemma lem2407655 (y : int) (x : int) (z : int) : (term480 y x z) = (term482 y x z).
Proof. exact (TRANS (@lem2407646 y x z) (@lem2407654 y x z)). Qed.
Lemma lem2407656 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2407657 (y : int) (x : int) (z : int) : (term491 y x z) = (term492 y x z).
Proof. exact (MK_COMB (@lem2407656) (@lem2407655 y x z)). Qed.
Lemma lem2407659 (n : nat) : (term265 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2407660 : term266 = term267.
Proof. exact (@lem2407659 term268). Qed.
Lemma lem2407661 (y : int) (x : int) (z : int) : (term490 y x z) = (term493 y x z).
Proof. exact (MK_COMB (@lem2407657 y x z) (@lem2407660)). Qed.
Lemma lem2407662 (y : int) (x : int) (z : int) : (term489 y x z) = (term493 y x z).
Proof. exact (TRANS (@lem2407643 y x z) (@lem2407661 y x z)). Qed.
Lemma lem2407663 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2407664 (y : int) (x : int) (z : int) : (term494 y x z) = (term495 y x z).
Proof. exact (MK_COMB (@lem2407663) (@lem2407662 y x z)). Qed.
Lemma lem2407666 (x : int) (y : int) : (term354 x y) = (term355 x y).
Proof. exact (EQ_MP (@lem2318533 x y) (@lem2318532 x y)). Qed.
Lemma lem2407667 (x : int) (y : int) (z : int) : (term472 x y z) = (term473 x y z).
Proof. exact (@lem2407666 x (int_add y z)). Qed.
Lemma lem2407669 (x : int) (y : int) : (term255 x y) = (term256 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2407670 (y : int) (z : int) : (term255 y z) = (term256 y z).
Proof. exact (@lem2407669 y z). Qed.
Lemma lem2407671 (x : int) : (term358 x) = (term358 x).
Proof. exact (eq_refl (term358 x)). Qed.
Lemma lem2407672 (x : int) (y : int) (z : int) : (term473 x y z) = (term474 x y z).
Proof. exact (MK_COMB (@lem2407671 x) (@lem2407670 y z)). Qed.
Lemma lem2407673 (x : int) (y : int) (z : int) : (term472 x y z) = (term474 x y z).
Proof. exact (TRANS (@lem2407667 x y z) (@lem2407672 x y z)). Qed.
Lemma lem2407674 (x : int) (y : int) (z : int) : (term487 x y z) = (term496 x y z).
Proof. exact (MK_COMB (@lem2407664 y x z) (@lem2407673 x y z)). Qed.
Lemma lem2407675 (x : int) (y : int) (z : int) : (term486 x y z) = (term496 x y z).
Proof. exact (TRANS (@lem2407640 x y z) (@lem2407674 x y z)). Qed.
Lemma lem2407676 (x : int) (y : int) (z : int) : (term466 x y z) = (term497 x y z).
Proof. exact (MK_COMB (@lem2407637 y x z) (@lem2407675 x y z)). Qed.
Lemma lem2407677 (x : int) (y : int) (z : int) : (term184 y x z) = (term497 x y z).
Proof. exact (TRANS (@lem2407597 x y z) (@lem2407676 x y z)). Qed.
Lemma lem2407678 (x : int) (y : int) : (term186 y x) = (term498 x y).
Proof. exact (fun_ext (fun z : int => @lem2407677 x y z)). Qed.
Lemma lem2407679 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407680 (x : int) (y : int) : (term187 y x) = (term499 x y).
Proof. exact (MK_COMB (@lem2407679) (@lem2407678 x y)). Qed.
Lemma lem2407681 (x : int) : (term195 x) = (term500 x).
Proof. exact (fun_ext (fun y : int => @lem2407680 x y)). Qed.
Lemma lem2407682 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407683 (x : int) : (term196 x) = (term501 x).
Proof. exact (MK_COMB (@lem2407682) (@lem2407681 x)). Qed.
Lemma lem2407684 : term204 = term502.
Proof. exact (fun_ext (fun x : int => @lem2407683 x)). Qed.
Lemma lem2407685 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407686 : term205 = term503.
Proof. exact (MK_COMB (@lem2407685) (@lem2407684)). Qed.
Lemma lem2407687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407688 : term207 = term504.
Proof. exact (MK_COMB (@lem2407687) (@lem2407594)). Qed.
Lemma lem2407689 : term209 = term505.
Proof. exact (MK_COMB (@lem2407688) (@lem2407686)). Qed.
Lemma lem2407690 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407691 : term213 = term506.
Proof. exact (MK_COMB (@lem2407690) (@lem2407522)). Qed.
Lemma lem2407692 : term215 = term507.
Proof. exact (MK_COMB (@lem2407691) (@lem2407689)). Qed.
Lemma lem2407693 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407694 : term219 = term508.
Proof. exact (MK_COMB (@lem2407693) (@lem2407456)). Qed.
Lemma lem2407695 : term221 = term509.
Proof. exact (MK_COMB (@lem2407694) (@lem2407692)). Qed.
Lemma lem2407696 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407697 : term225 = term510.
Proof. exact (MK_COMB (@lem2407696) (@lem2407399)). Qed.
Lemma lem2407698 : term227 = term511.
Proof. exact (MK_COMB (@lem2407697) (@lem2407695)). Qed.
Lemma lem2407699 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407700 : term231 = term512.
Proof. exact (MK_COMB (@lem2407699) (@lem2407311)). Qed.
Lemma lem2407701 : term233 = term513.
Proof. exact (MK_COMB (@lem2407700) (@lem2407698)). Qed.
Lemma lem2407702 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407703 : term237 = term514.
Proof. exact (MK_COMB (@lem2407702) (@lem2407245)). Qed.
Lemma lem2407704 : term239 = term515.
Proof. exact (MK_COMB (@lem2407703) (@lem2407701)). Qed.
Lemma lem2407705 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407706 : term243 = term516.
Proof. exact (MK_COMB (@lem2407705) (@lem2407188)). Qed.
Lemma lem2407707 : term245 = term517.
Proof. exact (MK_COMB (@lem2407706) (@lem2407704)). Qed.
Lemma lem2407708 : term246 = term517.
Proof. exact (TRANS (@lem2407100) (@lem2407707)). Qed.
Lemma lem2407712 (t : Prop) : (term518 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2407713 : term519 = term517.
Proof. exact (@lem2407712 term517). Qed.
Lemma lem2407725 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2407726 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2407725 int P Q). Qed.
Lemma lem2407727 (x : int) (y : int) : (term524 x y) = (term525 x y).
Proof. exact (@lem2407726 (term526 x y) (term527 x y)). Qed.
Lemma lem2407728 (x : int) (y : int) (z : int) : (term528 x y z) = (term277 x y z).
Proof. exact (eq_refl (term528 x y z)). Qed.
Lemma lem2407729 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407730 (x : int) (y : int) (z : int) : (term529 x y z) = (term279 x y z).
Proof. exact (MK_COMB (@lem2407729) (@lem2407728 x y z)). Qed.
Lemma lem2407731 (x : int) (y : int) (z : int) : (term530 x y z) = (term290 x y z).
Proof. exact (eq_refl (term530 x y z)). Qed.
Lemma lem2407732 (x : int) (y : int) (z : int) : (term531 x y z) = (term291 x y z).
Proof. exact (MK_COMB (@lem2407730 x y z) (@lem2407731 x y z)). Qed.
Lemma lem2407733 (x : int) (y : int) : (term532 x y) = (term292 x y).
Proof. exact (fun_ext (fun z : int => @lem2407732 x y z)). Qed.
Lemma lem2407734 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407735 (x : int) (y : int) : (term524 x y) = (term293 x y).
Proof. exact (MK_COMB (@lem2407734) (@lem2407733 x y)). Qed.
Lemma lem2407736 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2407737 (x : int) (y : int) : (term533 x y) = (term534 x y).
Proof. exact (MK_COMB (@lem2407736) (@lem2407735 x y)). Qed.
Lemma lem2407738 (x : int) (y : int) (z : int) : (term528 x y z) = (term277 x y z).
Proof. exact (eq_refl (term528 x y z)). Qed.
Lemma lem2407739 (x : int) (y : int) : (term535 x y) = (term526 x y).
Proof. exact (fun_ext (fun z : int => @lem2407738 x y z)). Qed.
Lemma lem2407740 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407741 (x : int) (y : int) : (term536 x y) = (term537 x y).
Proof. exact (MK_COMB (@lem2407740) (@lem2407739 x y)). Qed.
Lemma lem2407742 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407743 (x : int) (y : int) : (term538 x y) = (term539 x y).
Proof. exact (MK_COMB (@lem2407742) (@lem2407741 x y)). Qed.
Lemma lem2407744 (x : int) (y : int) (z : int) : (term530 x y z) = (term290 x y z).
Proof. exact (eq_refl (term530 x y z)). Qed.
Lemma lem2407745 (x : int) (y : int) : (term540 x y) = (term527 x y).
Proof. exact (fun_ext (fun z : int => @lem2407744 x y z)). Qed.
Lemma lem2407746 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407747 (x : int) (y : int) : (term541 x y) = (term542 x y).
Proof. exact (MK_COMB (@lem2407746) (@lem2407745 x y)). Qed.
Lemma lem2407748 (x : int) (y : int) : (term525 x y) = (term543 x y).
Proof. exact (MK_COMB (@lem2407743 x y) (@lem2407747 x y)). Qed.
Lemma lem2407749 (x : int) (y : int) : ((term524 x y) = (term525 x y)) = ((term293 x y) = (term543 x y)).
Proof. exact (MK_COMB (@lem2407737 x y) (@lem2407748 x y)). Qed.
Lemma lem2407750 (x : int) (y : int) : (term293 x y) = (term543 x y).
Proof. exact (EQ_MP (@lem2407749 x y) (@lem2407727 x y)). Qed.
Lemma lem2407761 (x : int) : (term294 x) = (term544 x).
Proof. exact (fun_ext (fun y : int => @lem2407750 x y)). Qed.
Lemma lem2407762 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407763 (x : int) : (term295 x) = (term545 x).
Proof. exact (MK_COMB (@lem2407762) (@lem2407761 x)). Qed.
Lemma lem2407765 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2407766 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2407765 int P Q). Qed.
Lemma lem2407767 (x : int) : (term546 x) = (term547 x).
Proof. exact (@lem2407766 (term548 x) (term549 x)). Qed.
Lemma lem2407768 (x : int) (y : int) : (term550 x y) = (term537 x y).
Proof. exact (eq_refl (term550 x y)). Qed.
Lemma lem2407769 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407770 (x : int) (y : int) : (term551 x y) = (term539 x y).
Proof. exact (MK_COMB (@lem2407769) (@lem2407768 x y)). Qed.
Lemma lem2407771 (x : int) (y : int) : (term552 x y) = (term542 x y).
Proof. exact (eq_refl (term552 x y)). Qed.
Lemma lem2407772 (x : int) (y : int) : (term553 x y) = (term543 x y).
Proof. exact (MK_COMB (@lem2407770 x y) (@lem2407771 x y)). Qed.
Lemma lem2407773 (x : int) : (term554 x) = (term544 x).
Proof. exact (fun_ext (fun y : int => @lem2407772 x y)). Qed.
Lemma lem2407774 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407775 (x : int) : (term546 x) = (term545 x).
Proof. exact (MK_COMB (@lem2407774) (@lem2407773 x)). Qed.
Lemma lem2407776 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2407777 (x : int) : (term555 x) = (term556 x).
Proof. exact (MK_COMB (@lem2407776) (@lem2407775 x)). Qed.
Lemma lem2407778 (x : int) (y : int) : (term550 x y) = (term537 x y).
Proof. exact (eq_refl (term550 x y)). Qed.
Lemma lem2407779 (x : int) : (term557 x) = (term548 x).
Proof. exact (fun_ext (fun y : int => @lem2407778 x y)). Qed.
Lemma lem2407780 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407781 (x : int) : (term558 x) = (term559 x).
Proof. exact (MK_COMB (@lem2407780) (@lem2407779 x)). Qed.
Lemma lem2407782 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407783 (x : int) : (term560 x) = (term561 x).
Proof. exact (MK_COMB (@lem2407782) (@lem2407781 x)). Qed.
Lemma lem2407784 (x : int) (y : int) : (term552 x y) = (term542 x y).
Proof. exact (eq_refl (term552 x y)). Qed.
Lemma lem2407785 (x : int) : (term562 x) = (term549 x).
Proof. exact (fun_ext (fun y : int => @lem2407784 x y)). Qed.
Lemma lem2407786 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407787 (x : int) : (term563 x) = (term564 x).
Proof. exact (MK_COMB (@lem2407786) (@lem2407785 x)). Qed.
Lemma lem2407788 (x : int) : (term547 x) = (term565 x).
Proof. exact (MK_COMB (@lem2407783 x) (@lem2407787 x)). Qed.
Lemma lem2407789 (x : int) : ((term546 x) = (term547 x)) = ((term545 x) = (term565 x)).
Proof. exact (MK_COMB (@lem2407777 x) (@lem2407788 x)). Qed.
Lemma lem2407790 (x : int) : (term545 x) = (term565 x).
Proof. exact (EQ_MP (@lem2407789 x) (@lem2407767 x)). Qed.
Lemma lem2407809 (x : int) : (term295 x) = (term565 x).
Proof. exact (TRANS (@lem2407763 x) (@lem2407790 x)). Qed.
Lemma lem2407810 : term296 = term566.
Proof. exact (fun_ext (fun x : int => @lem2407809 x)). Qed.
Lemma lem2407811 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407812 : term297 = term567.
Proof. exact (MK_COMB (@lem2407811) (@lem2407810)). Qed.
Lemma lem2407814 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2407815 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2407814 int P Q). Qed.
Lemma lem2407816 : term568 = term569.
Proof. exact (@lem2407815 term570 term571). Qed.
Lemma lem2407817 (x : int) : (term572 x) = (term559 x).
Proof. exact (eq_refl (term572 x)). Qed.
Lemma lem2407818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407819 (x : int) : (term573 x) = (term561 x).
Proof. exact (MK_COMB (@lem2407818) (@lem2407817 x)). Qed.
Lemma lem2407820 (x : int) : (term574 x) = (term564 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem2407821 (x : int) : (term575 x) = (term565 x).
Proof. exact (MK_COMB (@lem2407819 x) (@lem2407820 x)). Qed.
Lemma lem2407822 : term576 = term566.
Proof. exact (fun_ext (fun x : int => @lem2407821 x)). Qed.
Lemma lem2407823 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407824 : term568 = term567.
Proof. exact (MK_COMB (@lem2407823) (@lem2407822)). Qed.
Lemma lem2407825 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2407826 : term577 = term578.
Proof. exact (MK_COMB (@lem2407825) (@lem2407824)). Qed.
Lemma lem2407827 (x : int) : (term572 x) = (term559 x).
Proof. exact (eq_refl (term572 x)). Qed.
Lemma lem2407828 : term579 = term570.
Proof. exact (fun_ext (fun x : int => @lem2407827 x)). Qed.
Lemma lem2407829 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407830 : term580 = term581.
Proof. exact (MK_COMB (@lem2407829) (@lem2407828)). Qed.
Lemma lem2407831 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407832 : term582 = term583.
Proof. exact (MK_COMB (@lem2407831) (@lem2407830)). Qed.
Lemma lem2407833 (x : int) : (term574 x) = (term564 x).
Proof. exact (eq_refl (term574 x)). Qed.
Lemma lem2407834 : term584 = term571.
Proof. exact (fun_ext (fun x : int => @lem2407833 x)). Qed.
Lemma lem2407835 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407836 : term585 = term586.
Proof. exact (MK_COMB (@lem2407835) (@lem2407834)). Qed.
Lemma lem2407837 : term569 = term587.
Proof. exact (MK_COMB (@lem2407832) (@lem2407836)). Qed.
Lemma lem2407838 : (term568 = term569) = (term567 = term587).
Proof. exact (MK_COMB (@lem2407826) (@lem2407837)). Qed.
Lemma lem2407839 : term567 = term587.
Proof. exact (EQ_MP (@lem2407838) (@lem2407816)). Qed.
Lemma lem2407866 : term297 = term587.
Proof. exact (TRANS (@lem2407812) (@lem2407839)). Qed.
Lemma lem2407867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407868 : term516 = term588.
Proof. exact (MK_COMB (@lem2407867) (@lem2407866)). Qed.
Lemma lem2407876 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2407877 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2407876 int P Q). Qed.
Lemma lem2407878 (x : int) : (term589 x) = (term590 x).
Proof. exact (@lem2407877 (term591 x) (term592 x)). Qed.
Lemma lem2407879 (y : int) (x : int) : (term593 x y) = (term307 y x).
Proof. exact (eq_refl (term593 x y)). Qed.
Lemma lem2407880 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407881 (y : int) (x : int) : (term594 x y) = (term309 y x).
Proof. exact (MK_COMB (@lem2407880) (@lem2407879 y x)). Qed.
Lemma lem2407882 (x : int) (y : int) : (term595 x y) = (term307 x y).
Proof. exact (eq_refl (term595 x y)). Qed.
Lemma lem2407883 (x : int) (y : int) : (term596 x y) = (term310 x y).
Proof. exact (MK_COMB (@lem2407881 y x) (@lem2407882 x y)). Qed.
Lemma lem2407884 (x : int) : (term597 x) = (term311 x).
Proof. exact (fun_ext (fun y : int => @lem2407883 x y)). Qed.
Lemma lem2407885 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407886 (x : int) : (term589 x) = (term312 x).
Proof. exact (MK_COMB (@lem2407885) (@lem2407884 x)). Qed.
Lemma lem2407887 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2407888 (x : int) : (term598 x) = (term599 x).
Proof. exact (MK_COMB (@lem2407887) (@lem2407886 x)). Qed.
Lemma lem2407889 (y : int) (x : int) : (term593 x y) = (term307 y x).
Proof. exact (eq_refl (term593 x y)). Qed.
Lemma lem2407890 (x : int) : (term600 x) = (term591 x).
Proof. exact (fun_ext (fun y : int => @lem2407889 y x)). Qed.
Lemma lem2407891 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407892 (x : int) : (term601 x) = (term602 x).
Proof. exact (MK_COMB (@lem2407891) (@lem2407890 x)). Qed.
Lemma lem2407893 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407894 (x : int) : (term603 x) = (term604 x).
Proof. exact (MK_COMB (@lem2407893) (@lem2407892 x)). Qed.
Lemma lem2407895 (x : int) (y : int) : (term595 x y) = (term307 x y).
Proof. exact (eq_refl (term595 x y)). Qed.
Lemma lem2407896 (x : int) : (term605 x) = (term592 x).
Proof. exact (fun_ext (fun y : int => @lem2407895 x y)). Qed.
Lemma lem2407897 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407898 (x : int) : (term606 x) = (term607 x).
Proof. exact (MK_COMB (@lem2407897) (@lem2407896 x)). Qed.
Lemma lem2407899 (x : int) : (term590 x) = (term608 x).
Proof. exact (MK_COMB (@lem2407894 x) (@lem2407898 x)). Qed.
Lemma lem2407900 (x : int) : ((term589 x) = (term590 x)) = ((term312 x) = (term608 x)).
Proof. exact (MK_COMB (@lem2407888 x) (@lem2407899 x)). Qed.
Lemma lem2407901 (x : int) : (term312 x) = (term608 x).
Proof. exact (EQ_MP (@lem2407900 x) (@lem2407878 x)). Qed.
Lemma lem2407912 : term313 = term609.
Proof. exact (fun_ext (fun x : int => @lem2407901 x)). Qed.
Lemma lem2407913 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407914 : term314 = term610.
Proof. exact (MK_COMB (@lem2407913) (@lem2407912)). Qed.
Lemma lem2407916 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2407917 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2407916 int P Q). Qed.
Lemma lem2407918 : term611 = term612.
Proof. exact (@lem2407917 term613 term614). Qed.
Lemma lem2407919 (x : int) : (term615 x) = (term602 x).
Proof. exact (eq_refl (term615 x)). Qed.
Lemma lem2407920 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407921 (x : int) : (term616 x) = (term604 x).
Proof. exact (MK_COMB (@lem2407920) (@lem2407919 x)). Qed.
Lemma lem2407922 (x : int) : (term617 x) = (term607 x).
Proof. exact (eq_refl (term617 x)). Qed.
Lemma lem2407923 (x : int) : (term618 x) = (term608 x).
Proof. exact (MK_COMB (@lem2407921 x) (@lem2407922 x)). Qed.
Lemma lem2407924 : term619 = term609.
Proof. exact (fun_ext (fun x : int => @lem2407923 x)). Qed.
Lemma lem2407925 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407926 : term611 = term610.
Proof. exact (MK_COMB (@lem2407925) (@lem2407924)). Qed.
Lemma lem2407927 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2407928 : term620 = term621.
Proof. exact (MK_COMB (@lem2407927) (@lem2407926)). Qed.
Lemma lem2407929 (x : int) : (term615 x) = (term602 x).
Proof. exact (eq_refl (term615 x)). Qed.
Lemma lem2407930 : term622 = term613.
Proof. exact (fun_ext (fun x : int => @lem2407929 x)). Qed.
Lemma lem2407931 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407932 : term623 = term624.
Proof. exact (MK_COMB (@lem2407931) (@lem2407930)). Qed.
Lemma lem2407933 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407934 : term625 = term626.
Proof. exact (MK_COMB (@lem2407933) (@lem2407932)). Qed.
Lemma lem2407935 (x : int) : (term617 x) = (term607 x).
Proof. exact (eq_refl (term617 x)). Qed.
Lemma lem2407936 : term627 = term614.
Proof. exact (fun_ext (fun x : int => @lem2407935 x)). Qed.
Lemma lem2407937 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407938 : term628 = term629.
Proof. exact (MK_COMB (@lem2407937) (@lem2407936)). Qed.
Lemma lem2407939 : term612 = term630.
Proof. exact (MK_COMB (@lem2407934) (@lem2407938)). Qed.
Lemma lem2407940 : (term611 = term612) = (term610 = term630).
Proof. exact (MK_COMB (@lem2407928) (@lem2407939)). Qed.
Lemma lem2407941 : term610 = term630.
Proof. exact (EQ_MP (@lem2407940) (@lem2407918)). Qed.
Lemma lem2407960 : term314 = term630.
Proof. exact (TRANS (@lem2407914) (@lem2407941)). Qed.
Lemma lem2407961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407962 : term514 = term631.
Proof. exact (MK_COMB (@lem2407961) (@lem2407960)). Qed.
Lemma lem2407966 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2407967 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2407966 int P Q). Qed.
Lemma lem2407968 : term632 = term633.
Proof. exact (@lem2407967 term634 term635). Qed.
Lemma lem2407969 (x : int) : (term636 x) = (term333 x).
Proof. exact (eq_refl (term636 x)). Qed.
Lemma lem2407970 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407971 (x : int) : (term637 x) = (term335 x).
Proof. exact (MK_COMB (@lem2407970) (@lem2407969 x)). Qed.
Lemma lem2407972 (x : int) : (term638 x) = (term344 x).
Proof. exact (eq_refl (term638 x)). Qed.
Lemma lem2407973 (x : int) : (term639 x) = (term345 x).
Proof. exact (MK_COMB (@lem2407971 x) (@lem2407972 x)). Qed.
Lemma lem2407974 : term640 = term346.
Proof. exact (fun_ext (fun x : int => @lem2407973 x)). Qed.
Lemma lem2407975 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407976 : term632 = term347.
Proof. exact (MK_COMB (@lem2407975) (@lem2407974)). Qed.
Lemma lem2407977 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2407978 : term641 = term642.
Proof. exact (MK_COMB (@lem2407977) (@lem2407976)). Qed.
Lemma lem2407979 (x : int) : (term636 x) = (term333 x).
Proof. exact (eq_refl (term636 x)). Qed.
Lemma lem2407980 : term643 = term634.
Proof. exact (fun_ext (fun x : int => @lem2407979 x)). Qed.
Lemma lem2407981 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407982 : term644 = term645.
Proof. exact (MK_COMB (@lem2407981) (@lem2407980)). Qed.
Lemma lem2407983 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2407984 : term646 = term647.
Proof. exact (MK_COMB (@lem2407983) (@lem2407982)). Qed.
Lemma lem2407985 (x : int) : (term638 x) = (term344 x).
Proof. exact (eq_refl (term638 x)). Qed.
Lemma lem2407986 : term648 = term635.
Proof. exact (fun_ext (fun x : int => @lem2407985 x)). Qed.
Lemma lem2407987 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2407988 : term649 = term650.
Proof. exact (MK_COMB (@lem2407987) (@lem2407986)). Qed.
Lemma lem2407989 : term633 = term651.
Proof. exact (MK_COMB (@lem2407984) (@lem2407988)). Qed.
Lemma lem2407990 : (term632 = term633) = (term347 = term651).
Proof. exact (MK_COMB (@lem2407978) (@lem2407989)). Qed.
Lemma lem2407991 : term347 = term651.
Proof. exact (EQ_MP (@lem2407990) (@lem2407968)). Qed.
Lemma lem2408002 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408003 : term512 = term652.
Proof. exact (MK_COMB (@lem2408002) (@lem2407991)). Qed.
Lemma lem2408015 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408016 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408015 int P Q). Qed.
Lemma lem2408017 (x : int) (y : int) : (term653 x y) = (term654 x y).
Proof. exact (@lem2408016 (term655 x y) (term656 x y)). Qed.
Lemma lem2408018 (x : int) (y : int) (z : int) : (term657 x y z) = (term370 x y z).
Proof. exact (eq_refl (term657 x y z)). Qed.
Lemma lem2408019 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408020 (x : int) (y : int) (z : int) : (term658 x y z) = (term372 x y z).
Proof. exact (MK_COMB (@lem2408019) (@lem2408018 x y z)). Qed.
Lemma lem2408021 (x : int) (y : int) (z : int) : (term659 x y z) = (term383 x y z).
Proof. exact (eq_refl (term659 x y z)). Qed.
Lemma lem2408022 (x : int) (y : int) (z : int) : (term660 x y z) = (term384 x y z).
Proof. exact (MK_COMB (@lem2408020 x y z) (@lem2408021 x y z)). Qed.
Lemma lem2408023 (x : int) (y : int) : (term661 x y) = (term385 x y).
Proof. exact (fun_ext (fun z : int => @lem2408022 x y z)). Qed.
Lemma lem2408024 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408025 (x : int) (y : int) : (term653 x y) = (term386 x y).
Proof. exact (MK_COMB (@lem2408024) (@lem2408023 x y)). Qed.
Lemma lem2408026 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408027 (x : int) (y : int) : (term662 x y) = (term663 x y).
Proof. exact (MK_COMB (@lem2408026) (@lem2408025 x y)). Qed.
Lemma lem2408028 (x : int) (y : int) (z : int) : (term657 x y z) = (term370 x y z).
Proof. exact (eq_refl (term657 x y z)). Qed.
Lemma lem2408029 (x : int) (y : int) : (term664 x y) = (term655 x y).
Proof. exact (fun_ext (fun z : int => @lem2408028 x y z)). Qed.
Lemma lem2408030 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408031 (x : int) (y : int) : (term665 x y) = (term666 x y).
Proof. exact (MK_COMB (@lem2408030) (@lem2408029 x y)). Qed.
Lemma lem2408032 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408033 (x : int) (y : int) : (term667 x y) = (term668 x y).
Proof. exact (MK_COMB (@lem2408032) (@lem2408031 x y)). Qed.
Lemma lem2408034 (x : int) (y : int) (z : int) : (term659 x y z) = (term383 x y z).
Proof. exact (eq_refl (term659 x y z)). Qed.
Lemma lem2408035 (x : int) (y : int) : (term669 x y) = (term656 x y).
Proof. exact (fun_ext (fun z : int => @lem2408034 x y z)). Qed.
Lemma lem2408036 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408037 (x : int) (y : int) : (term670 x y) = (term671 x y).
Proof. exact (MK_COMB (@lem2408036) (@lem2408035 x y)). Qed.
Lemma lem2408038 (x : int) (y : int) : (term654 x y) = (term672 x y).
Proof. exact (MK_COMB (@lem2408033 x y) (@lem2408037 x y)). Qed.
Lemma lem2408039 (x : int) (y : int) : ((term653 x y) = (term654 x y)) = ((term386 x y) = (term672 x y)).
Proof. exact (MK_COMB (@lem2408027 x y) (@lem2408038 x y)). Qed.
Lemma lem2408040 (x : int) (y : int) : (term386 x y) = (term672 x y).
Proof. exact (EQ_MP (@lem2408039 x y) (@lem2408017 x y)). Qed.
Lemma lem2408051 (x : int) : (term387 x) = (term673 x).
Proof. exact (fun_ext (fun y : int => @lem2408040 x y)). Qed.
Lemma lem2408052 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408053 (x : int) : (term388 x) = (term674 x).
Proof. exact (MK_COMB (@lem2408052) (@lem2408051 x)). Qed.
Lemma lem2408055 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408056 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408055 int P Q). Qed.
Lemma lem2408057 (x : int) : (term675 x) = (term676 x).
Proof. exact (@lem2408056 (term677 x) (term678 x)). Qed.
Lemma lem2408058 (x : int) (y : int) : (term679 x y) = (term666 x y).
Proof. exact (eq_refl (term679 x y)). Qed.
Lemma lem2408059 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408060 (x : int) (y : int) : (term680 x y) = (term668 x y).
Proof. exact (MK_COMB (@lem2408059) (@lem2408058 x y)). Qed.
Lemma lem2408061 (x : int) (y : int) : (term681 x y) = (term671 x y).
Proof. exact (eq_refl (term681 x y)). Qed.
Lemma lem2408062 (x : int) (y : int) : (term682 x y) = (term672 x y).
Proof. exact (MK_COMB (@lem2408060 x y) (@lem2408061 x y)). Qed.
Lemma lem2408063 (x : int) : (term683 x) = (term673 x).
Proof. exact (fun_ext (fun y : int => @lem2408062 x y)). Qed.
Lemma lem2408064 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408065 (x : int) : (term675 x) = (term674 x).
Proof. exact (MK_COMB (@lem2408064) (@lem2408063 x)). Qed.
Lemma lem2408066 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408067 (x : int) : (term684 x) = (term685 x).
Proof. exact (MK_COMB (@lem2408066) (@lem2408065 x)). Qed.
Lemma lem2408068 (x : int) (y : int) : (term679 x y) = (term666 x y).
Proof. exact (eq_refl (term679 x y)). Qed.
Lemma lem2408069 (x : int) : (term686 x) = (term677 x).
Proof. exact (fun_ext (fun y : int => @lem2408068 x y)). Qed.
Lemma lem2408070 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408071 (x : int) : (term687 x) = (term688 x).
Proof. exact (MK_COMB (@lem2408070) (@lem2408069 x)). Qed.
Lemma lem2408072 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408073 (x : int) : (term689 x) = (term690 x).
Proof. exact (MK_COMB (@lem2408072) (@lem2408071 x)). Qed.
Lemma lem2408074 (x : int) (y : int) : (term681 x y) = (term671 x y).
Proof. exact (eq_refl (term681 x y)). Qed.
Lemma lem2408075 (x : int) : (term691 x) = (term678 x).
Proof. exact (fun_ext (fun y : int => @lem2408074 x y)). Qed.
Lemma lem2408076 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408077 (x : int) : (term692 x) = (term693 x).
Proof. exact (MK_COMB (@lem2408076) (@lem2408075 x)). Qed.
Lemma lem2408078 (x : int) : (term676 x) = (term694 x).
Proof. exact (MK_COMB (@lem2408073 x) (@lem2408077 x)). Qed.
Lemma lem2408079 (x : int) : ((term675 x) = (term676 x)) = ((term674 x) = (term694 x)).
Proof. exact (MK_COMB (@lem2408067 x) (@lem2408078 x)). Qed.
Lemma lem2408080 (x : int) : (term674 x) = (term694 x).
Proof. exact (EQ_MP (@lem2408079 x) (@lem2408057 x)). Qed.
Lemma lem2408099 (x : int) : (term388 x) = (term694 x).
Proof. exact (TRANS (@lem2408053 x) (@lem2408080 x)). Qed.
Lemma lem2408100 : term389 = term695.
Proof. exact (fun_ext (fun x : int => @lem2408099 x)). Qed.
Lemma lem2408101 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408102 : term390 = term696.
Proof. exact (MK_COMB (@lem2408101) (@lem2408100)). Qed.
Lemma lem2408104 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408105 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408104 int P Q). Qed.
Lemma lem2408106 : term697 = term698.
Proof. exact (@lem2408105 term699 term700). Qed.
Lemma lem2408107 (x : int) : (term701 x) = (term688 x).
Proof. exact (eq_refl (term701 x)). Qed.
Lemma lem2408108 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408109 (x : int) : (term702 x) = (term690 x).
Proof. exact (MK_COMB (@lem2408108) (@lem2408107 x)). Qed.
Lemma lem2408110 (x : int) : (term703 x) = (term693 x).
Proof. exact (eq_refl (term703 x)). Qed.
Lemma lem2408111 (x : int) : (term704 x) = (term694 x).
Proof. exact (MK_COMB (@lem2408109 x) (@lem2408110 x)). Qed.
Lemma lem2408112 : term705 = term695.
Proof. exact (fun_ext (fun x : int => @lem2408111 x)). Qed.
Lemma lem2408113 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408114 : term697 = term696.
Proof. exact (MK_COMB (@lem2408113) (@lem2408112)). Qed.
Lemma lem2408115 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408116 : term706 = term707.
Proof. exact (MK_COMB (@lem2408115) (@lem2408114)). Qed.
Lemma lem2408117 (x : int) : (term701 x) = (term688 x).
Proof. exact (eq_refl (term701 x)). Qed.
Lemma lem2408118 : term708 = term699.
Proof. exact (fun_ext (fun x : int => @lem2408117 x)). Qed.
Lemma lem2408119 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408120 : term709 = term710.
Proof. exact (MK_COMB (@lem2408119) (@lem2408118)). Qed.
Lemma lem2408121 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408122 : term711 = term712.
Proof. exact (MK_COMB (@lem2408121) (@lem2408120)). Qed.
Lemma lem2408123 (x : int) : (term703 x) = (term693 x).
Proof. exact (eq_refl (term703 x)). Qed.
Lemma lem2408124 : term713 = term700.
Proof. exact (fun_ext (fun x : int => @lem2408123 x)). Qed.
Lemma lem2408125 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408126 : term714 = term715.
Proof. exact (MK_COMB (@lem2408125) (@lem2408124)). Qed.
Lemma lem2408127 : term698 = term716.
Proof. exact (MK_COMB (@lem2408122) (@lem2408126)). Qed.
Lemma lem2408128 : (term697 = term698) = (term696 = term716).
Proof. exact (MK_COMB (@lem2408116) (@lem2408127)). Qed.
Lemma lem2408129 : term696 = term716.
Proof. exact (EQ_MP (@lem2408128) (@lem2408106)). Qed.
Lemma lem2408156 : term390 = term716.
Proof. exact (TRANS (@lem2408102) (@lem2408129)). Qed.
Lemma lem2408157 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408158 : term510 = term717.
Proof. exact (MK_COMB (@lem2408157) (@lem2408156)). Qed.
Lemma lem2408166 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408167 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408166 int P Q). Qed.
Lemma lem2408168 (x : int) : (term718 x) = (term719 x).
Proof. exact (@lem2408167 (term720 x) (term721 x)). Qed.
Lemma lem2408169 (y : int) (x : int) : (term722 x y) = (term402 y x).
Proof. exact (eq_refl (term722 x y)). Qed.
Lemma lem2408170 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408171 (y : int) (x : int) : (term723 x y) = (term404 y x).
Proof. exact (MK_COMB (@lem2408170) (@lem2408169 y x)). Qed.
Lemma lem2408172 (x : int) (y : int) : (term724 x y) = (term402 x y).
Proof. exact (eq_refl (term724 x y)). Qed.
Lemma lem2408173 (x : int) (y : int) : (term725 x y) = (term405 x y).
Proof. exact (MK_COMB (@lem2408171 y x) (@lem2408172 x y)). Qed.
Lemma lem2408174 (x : int) : (term726 x) = (term406 x).
Proof. exact (fun_ext (fun y : int => @lem2408173 x y)). Qed.
Lemma lem2408175 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408176 (x : int) : (term718 x) = (term407 x).
Proof. exact (MK_COMB (@lem2408175) (@lem2408174 x)). Qed.
Lemma lem2408177 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408178 (x : int) : (term727 x) = (term728 x).
Proof. exact (MK_COMB (@lem2408177) (@lem2408176 x)). Qed.
Lemma lem2408179 (y : int) (x : int) : (term722 x y) = (term402 y x).
Proof. exact (eq_refl (term722 x y)). Qed.
Lemma lem2408180 (x : int) : (term729 x) = (term720 x).
Proof. exact (fun_ext (fun y : int => @lem2408179 y x)). Qed.
Lemma lem2408181 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408182 (x : int) : (term730 x) = (term731 x).
Proof. exact (MK_COMB (@lem2408181) (@lem2408180 x)). Qed.
Lemma lem2408183 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408184 (x : int) : (term732 x) = (term733 x).
Proof. exact (MK_COMB (@lem2408183) (@lem2408182 x)). Qed.
Lemma lem2408185 (x : int) (y : int) : (term724 x y) = (term402 x y).
Proof. exact (eq_refl (term724 x y)). Qed.
Lemma lem2408186 (x : int) : (term734 x) = (term721 x).
Proof. exact (fun_ext (fun y : int => @lem2408185 x y)). Qed.
Lemma lem2408187 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408188 (x : int) : (term735 x) = (term736 x).
Proof. exact (MK_COMB (@lem2408187) (@lem2408186 x)). Qed.
Lemma lem2408189 (x : int) : (term719 x) = (term737 x).
Proof. exact (MK_COMB (@lem2408184 x) (@lem2408188 x)). Qed.
Lemma lem2408190 (x : int) : ((term718 x) = (term719 x)) = ((term407 x) = (term737 x)).
Proof. exact (MK_COMB (@lem2408178 x) (@lem2408189 x)). Qed.
Lemma lem2408191 (x : int) : (term407 x) = (term737 x).
Proof. exact (EQ_MP (@lem2408190 x) (@lem2408168 x)). Qed.
Lemma lem2408202 : term408 = term738.
Proof. exact (fun_ext (fun x : int => @lem2408191 x)). Qed.
Lemma lem2408203 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408204 : term409 = term739.
Proof. exact (MK_COMB (@lem2408203) (@lem2408202)). Qed.
Lemma lem2408206 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408207 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408206 int P Q). Qed.
Lemma lem2408208 : term740 = term741.
Proof. exact (@lem2408207 term742 term743). Qed.
Lemma lem2408209 (x : int) : (term744 x) = (term731 x).
Proof. exact (eq_refl (term744 x)). Qed.
Lemma lem2408210 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408211 (x : int) : (term745 x) = (term733 x).
Proof. exact (MK_COMB (@lem2408210) (@lem2408209 x)). Qed.
Lemma lem2408212 (x : int) : (term746 x) = (term736 x).
Proof. exact (eq_refl (term746 x)). Qed.
Lemma lem2408213 (x : int) : (term747 x) = (term737 x).
Proof. exact (MK_COMB (@lem2408211 x) (@lem2408212 x)). Qed.
Lemma lem2408214 : term748 = term738.
Proof. exact (fun_ext (fun x : int => @lem2408213 x)). Qed.
Lemma lem2408215 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408216 : term740 = term739.
Proof. exact (MK_COMB (@lem2408215) (@lem2408214)). Qed.
Lemma lem2408217 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408218 : term749 = term750.
Proof. exact (MK_COMB (@lem2408217) (@lem2408216)). Qed.
Lemma lem2408219 (x : int) : (term744 x) = (term731 x).
Proof. exact (eq_refl (term744 x)). Qed.
Lemma lem2408220 : term751 = term742.
Proof. exact (fun_ext (fun x : int => @lem2408219 x)). Qed.
Lemma lem2408221 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408222 : term752 = term753.
Proof. exact (MK_COMB (@lem2408221) (@lem2408220)). Qed.
Lemma lem2408223 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408224 : term754 = term755.
Proof. exact (MK_COMB (@lem2408223) (@lem2408222)). Qed.
Lemma lem2408225 (x : int) : (term746 x) = (term736 x).
Proof. exact (eq_refl (term746 x)). Qed.
Lemma lem2408226 : term756 = term743.
Proof. exact (fun_ext (fun x : int => @lem2408225 x)). Qed.
Lemma lem2408227 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408228 : term757 = term758.
Proof. exact (MK_COMB (@lem2408227) (@lem2408226)). Qed.
Lemma lem2408229 : term741 = term759.
Proof. exact (MK_COMB (@lem2408224) (@lem2408228)). Qed.
Lemma lem2408230 : (term740 = term741) = (term739 = term759).
Proof. exact (MK_COMB (@lem2408218) (@lem2408229)). Qed.
Lemma lem2408231 : term739 = term759.
Proof. exact (EQ_MP (@lem2408230) (@lem2408208)). Qed.
Lemma lem2408250 : term409 = term759.
Proof. exact (TRANS (@lem2408204) (@lem2408231)). Qed.
Lemma lem2408251 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408252 : term508 = term760.
Proof. exact (MK_COMB (@lem2408251) (@lem2408250)). Qed.
Lemma lem2408256 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408257 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408256 int P Q). Qed.
Lemma lem2408258 : term761 = term762.
Proof. exact (@lem2408257 term763 term764). Qed.
Lemma lem2408259 (x : int) : (term765 x) = (term426 x).
Proof. exact (eq_refl (term765 x)). Qed.
Lemma lem2408260 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408261 (x : int) : (term766 x) = (term428 x).
Proof. exact (MK_COMB (@lem2408260) (@lem2408259 x)). Qed.
Lemma lem2408262 (x : int) : (term767 x) = (term431 x).
Proof. exact (eq_refl (term767 x)). Qed.
Lemma lem2408263 (x : int) : (term768 x) = (term432 x).
Proof. exact (MK_COMB (@lem2408261 x) (@lem2408262 x)). Qed.
Lemma lem2408264 : term769 = term433.
Proof. exact (fun_ext (fun x : int => @lem2408263 x)). Qed.
Lemma lem2408265 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408266 : term761 = term434.
Proof. exact (MK_COMB (@lem2408265) (@lem2408264)). Qed.
Lemma lem2408267 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408268 : term770 = term771.
Proof. exact (MK_COMB (@lem2408267) (@lem2408266)). Qed.
Lemma lem2408269 (x : int) : (term765 x) = (term426 x).
Proof. exact (eq_refl (term765 x)). Qed.
Lemma lem2408270 : term772 = term763.
Proof. exact (fun_ext (fun x : int => @lem2408269 x)). Qed.
Lemma lem2408271 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408272 : term773 = term774.
Proof. exact (MK_COMB (@lem2408271) (@lem2408270)). Qed.
Lemma lem2408273 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408274 : term775 = term776.
Proof. exact (MK_COMB (@lem2408273) (@lem2408272)). Qed.
Lemma lem2408275 (x : int) : (term767 x) = (term431 x).
Proof. exact (eq_refl (term767 x)). Qed.
Lemma lem2408276 : term777 = term764.
Proof. exact (fun_ext (fun x : int => @lem2408275 x)). Qed.
Lemma lem2408277 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408278 : term778 = term779.
Proof. exact (MK_COMB (@lem2408277) (@lem2408276)). Qed.
Lemma lem2408279 : term762 = term780.
Proof. exact (MK_COMB (@lem2408274) (@lem2408278)). Qed.
Lemma lem2408280 : (term761 = term762) = (term434 = term780).
Proof. exact (MK_COMB (@lem2408268) (@lem2408279)). Qed.
Lemma lem2408281 : term434 = term780.
Proof. exact (EQ_MP (@lem2408280) (@lem2408258)). Qed.
Lemma lem2408292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408293 : term506 = term781.
Proof. exact (MK_COMB (@lem2408292) (@lem2408281)). Qed.
Lemma lem2408297 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408298 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408297 int P Q). Qed.
Lemma lem2408299 : term782 = term783.
Proof. exact (@lem2408298 term784 term785). Qed.
Lemma lem2408300 (x : int) : (term786 x) = (term451 x).
Proof. exact (eq_refl (term786 x)). Qed.
Lemma lem2408301 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408302 (x : int) : (term787 x) = (term453 x).
Proof. exact (MK_COMB (@lem2408301) (@lem2408300 x)). Qed.
Lemma lem2408303 (x : int) : (term788 x) = (term462 x).
Proof. exact (eq_refl (term788 x)). Qed.
Lemma lem2408304 (x : int) : (term789 x) = (term463 x).
Proof. exact (MK_COMB (@lem2408302 x) (@lem2408303 x)). Qed.
Lemma lem2408305 : term790 = term464.
Proof. exact (fun_ext (fun x : int => @lem2408304 x)). Qed.
Lemma lem2408306 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408307 : term782 = term465.
Proof. exact (MK_COMB (@lem2408306) (@lem2408305)). Qed.
Lemma lem2408308 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408309 : term791 = term792.
Proof. exact (MK_COMB (@lem2408308) (@lem2408307)). Qed.
Lemma lem2408310 (x : int) : (term786 x) = (term451 x).
Proof. exact (eq_refl (term786 x)). Qed.
Lemma lem2408311 : term793 = term784.
Proof. exact (fun_ext (fun x : int => @lem2408310 x)). Qed.
Lemma lem2408312 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408313 : term794 = term795.
Proof. exact (MK_COMB (@lem2408312) (@lem2408311)). Qed.
Lemma lem2408314 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408315 : term796 = term797.
Proof. exact (MK_COMB (@lem2408314) (@lem2408313)). Qed.
Lemma lem2408316 (x : int) : (term788 x) = (term462 x).
Proof. exact (eq_refl (term788 x)). Qed.
Lemma lem2408317 : term798 = term785.
Proof. exact (fun_ext (fun x : int => @lem2408316 x)). Qed.
Lemma lem2408318 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408319 : term799 = term800.
Proof. exact (MK_COMB (@lem2408318) (@lem2408317)). Qed.
Lemma lem2408320 : term783 = term801.
Proof. exact (MK_COMB (@lem2408315) (@lem2408319)). Qed.
Lemma lem2408321 : (term782 = term783) = (term465 = term801).
Proof. exact (MK_COMB (@lem2408309) (@lem2408320)). Qed.
Lemma lem2408322 : term465 = term801.
Proof. exact (EQ_MP (@lem2408321) (@lem2408299)). Qed.
Lemma lem2408333 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408334 : term504 = term802.
Proof. exact (MK_COMB (@lem2408333) (@lem2408322)). Qed.
Lemma lem2408344 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408345 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408344 int P Q). Qed.
Lemma lem2408346 (x : int) (y : int) : (term803 x y) = (term804 x y).
Proof. exact (@lem2408345 (term805 y x) (term806 x y)). Qed.
Lemma lem2408347 (y : int) (x : int) (z : int) : (term807 y x z) = (term483 y x z).
Proof. exact (eq_refl (term807 y x z)). Qed.
Lemma lem2408348 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408349 (y : int) (x : int) (z : int) : (term808 y x z) = (term485 y x z).
Proof. exact (MK_COMB (@lem2408348) (@lem2408347 y x z)). Qed.
Lemma lem2408350 (x : int) (y : int) (z : int) : (term809 x y z) = (term496 x y z).
Proof. exact (eq_refl (term809 x y z)). Qed.
Lemma lem2408351 (x : int) (y : int) (z : int) : (term810 x y z) = (term497 x y z).
Proof. exact (MK_COMB (@lem2408349 y x z) (@lem2408350 x y z)). Qed.
Lemma lem2408352 (x : int) (y : int) : (term811 x y) = (term498 x y).
Proof. exact (fun_ext (fun z : int => @lem2408351 x y z)). Qed.
Lemma lem2408353 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408354 (x : int) (y : int) : (term803 x y) = (term499 x y).
Proof. exact (MK_COMB (@lem2408353) (@lem2408352 x y)). Qed.
Lemma lem2408355 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408356 (x : int) (y : int) : (term812 x y) = (term813 x y).
Proof. exact (MK_COMB (@lem2408355) (@lem2408354 x y)). Qed.
Lemma lem2408357 (y : int) (x : int) (z : int) : (term807 y x z) = (term483 y x z).
Proof. exact (eq_refl (term807 y x z)). Qed.
Lemma lem2408358 (y : int) (x : int) : (term814 y x) = (term805 y x).
Proof. exact (fun_ext (fun z : int => @lem2408357 y x z)). Qed.
Lemma lem2408359 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408360 (y : int) (x : int) : (term815 y x) = (term816 y x).
Proof. exact (MK_COMB (@lem2408359) (@lem2408358 y x)). Qed.
Lemma lem2408361 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408362 (y : int) (x : int) : (term817 y x) = (term818 y x).
Proof. exact (MK_COMB (@lem2408361) (@lem2408360 y x)). Qed.
Lemma lem2408363 (x : int) (y : int) (z : int) : (term809 x y z) = (term496 x y z).
Proof. exact (eq_refl (term809 x y z)). Qed.
Lemma lem2408364 (x : int) (y : int) : (term819 x y) = (term806 x y).
Proof. exact (fun_ext (fun z : int => @lem2408363 x y z)). Qed.
Lemma lem2408365 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408366 (x : int) (y : int) : (term820 x y) = (term821 x y).
Proof. exact (MK_COMB (@lem2408365) (@lem2408364 x y)). Qed.
Lemma lem2408367 (x : int) (y : int) : (term804 x y) = (term822 x y).
Proof. exact (MK_COMB (@lem2408362 y x) (@lem2408366 x y)). Qed.
Lemma lem2408368 (x : int) (y : int) : ((term803 x y) = (term804 x y)) = ((term499 x y) = (term822 x y)).
Proof. exact (MK_COMB (@lem2408356 x y) (@lem2408367 x y)). Qed.
Lemma lem2408369 (x : int) (y : int) : (term499 x y) = (term822 x y).
Proof. exact (EQ_MP (@lem2408368 x y) (@lem2408346 x y)). Qed.
Lemma lem2408380 (x : int) : (term500 x) = (term823 x).
Proof. exact (fun_ext (fun y : int => @lem2408369 x y)). Qed.
Lemma lem2408381 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408382 (x : int) : (term501 x) = (term824 x).
Proof. exact (MK_COMB (@lem2408381) (@lem2408380 x)). Qed.
Lemma lem2408384 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408385 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408384 int P Q). Qed.
Lemma lem2408386 (x : int) : (term825 x) = (term826 x).
Proof. exact (@lem2408385 (term827 x) (term828 x)). Qed.
Lemma lem2408387 (y : int) (x : int) : (term829 x y) = (term816 y x).
Proof. exact (eq_refl (term829 x y)). Qed.
Lemma lem2408388 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408389 (y : int) (x : int) : (term830 x y) = (term818 y x).
Proof. exact (MK_COMB (@lem2408388) (@lem2408387 y x)). Qed.
Lemma lem2408390 (x : int) (y : int) : (term831 x y) = (term821 x y).
Proof. exact (eq_refl (term831 x y)). Qed.
Lemma lem2408391 (x : int) (y : int) : (term832 x y) = (term822 x y).
Proof. exact (MK_COMB (@lem2408389 y x) (@lem2408390 x y)). Qed.
Lemma lem2408392 (x : int) : (term833 x) = (term823 x).
Proof. exact (fun_ext (fun y : int => @lem2408391 x y)). Qed.
Lemma lem2408393 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408394 (x : int) : (term825 x) = (term824 x).
Proof. exact (MK_COMB (@lem2408393) (@lem2408392 x)). Qed.
Lemma lem2408395 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408396 (x : int) : (term834 x) = (term835 x).
Proof. exact (MK_COMB (@lem2408395) (@lem2408394 x)). Qed.
Lemma lem2408397 (y : int) (x : int) : (term829 x y) = (term816 y x).
Proof. exact (eq_refl (term829 x y)). Qed.
Lemma lem2408398 (x : int) : (term836 x) = (term827 x).
Proof. exact (fun_ext (fun y : int => @lem2408397 y x)). Qed.
Lemma lem2408399 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408400 (x : int) : (term837 x) = (term838 x).
Proof. exact (MK_COMB (@lem2408399) (@lem2408398 x)). Qed.
Lemma lem2408401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408402 (x : int) : (term839 x) = (term840 x).
Proof. exact (MK_COMB (@lem2408401) (@lem2408400 x)). Qed.
Lemma lem2408403 (x : int) (y : int) : (term831 x y) = (term821 x y).
Proof. exact (eq_refl (term831 x y)). Qed.
Lemma lem2408404 (x : int) : (term841 x) = (term828 x).
Proof. exact (fun_ext (fun y : int => @lem2408403 x y)). Qed.
Lemma lem2408405 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408406 (x : int) : (term842 x) = (term843 x).
Proof. exact (MK_COMB (@lem2408405) (@lem2408404 x)). Qed.
Lemma lem2408407 (x : int) : (term826 x) = (term844 x).
Proof. exact (MK_COMB (@lem2408402 x) (@lem2408406 x)). Qed.
Lemma lem2408408 (x : int) : ((term825 x) = (term826 x)) = ((term824 x) = (term844 x)).
Proof. exact (MK_COMB (@lem2408396 x) (@lem2408407 x)). Qed.
Lemma lem2408409 (x : int) : (term824 x) = (term844 x).
Proof. exact (EQ_MP (@lem2408408 x) (@lem2408386 x)). Qed.
Lemma lem2408428 (x : int) : (term501 x) = (term844 x).
Proof. exact (TRANS (@lem2408382 x) (@lem2408409 x)). Qed.
Lemma lem2408429 : term502 = term845.
Proof. exact (fun_ext (fun x : int => @lem2408428 x)). Qed.
Lemma lem2408430 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408431 : term503 = term846.
Proof. exact (MK_COMB (@lem2408430) (@lem2408429)). Qed.
Lemma lem2408433 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term520 A P Q) = (term521 A P Q).
Proof. exact (EQ_MP (@lem16452 A P Q) (@lem16451 A P Q)). Qed.
Lemma lem2408434 (P : int -> Prop) (Q : int -> Prop) : (term522 P Q) = (term523 P Q).
Proof. exact (@lem2408433 int P Q). Qed.
Lemma lem2408435 : term847 = term848.
Proof. exact (@lem2408434 term849 term850). Qed.
Lemma lem2408436 (x : int) : (term851 x) = (term838 x).
Proof. exact (eq_refl (term851 x)). Qed.
Lemma lem2408437 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408438 (x : int) : (term852 x) = (term840 x).
Proof. exact (MK_COMB (@lem2408437) (@lem2408436 x)). Qed.
Lemma lem2408439 (x : int) : (term853 x) = (term843 x).
Proof. exact (eq_refl (term853 x)). Qed.
Lemma lem2408440 (x : int) : (term854 x) = (term844 x).
Proof. exact (MK_COMB (@lem2408438 x) (@lem2408439 x)). Qed.
Lemma lem2408441 : term855 = term845.
Proof. exact (fun_ext (fun x : int => @lem2408440 x)). Qed.
Lemma lem2408442 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408443 : term847 = term846.
Proof. exact (MK_COMB (@lem2408442) (@lem2408441)). Qed.
Lemma lem2408444 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2408445 : term856 = term857.
Proof. exact (MK_COMB (@lem2408444) (@lem2408443)). Qed.
Lemma lem2408446 (x : int) : (term851 x) = (term838 x).
Proof. exact (eq_refl (term851 x)). Qed.
Lemma lem2408447 : term858 = term849.
Proof. exact (fun_ext (fun x : int => @lem2408446 x)). Qed.
Lemma lem2408448 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408449 : term859 = term860.
Proof. exact (MK_COMB (@lem2408448) (@lem2408447)). Qed.
Lemma lem2408450 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408451 : term861 = term862.
Proof. exact (MK_COMB (@lem2408450) (@lem2408449)). Qed.
Lemma lem2408452 (x : int) : (term853 x) = (term843 x).
Proof. exact (eq_refl (term853 x)). Qed.
Lemma lem2408453 : term863 = term850.
Proof. exact (fun_ext (fun x : int => @lem2408452 x)). Qed.
Lemma lem2408454 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408455 : term864 = term865.
Proof. exact (MK_COMB (@lem2408454) (@lem2408453)). Qed.
Lemma lem2408456 : term848 = term866.
Proof. exact (MK_COMB (@lem2408451) (@lem2408455)). Qed.
Lemma lem2408457 : (term847 = term848) = (term846 = term866).
Proof. exact (MK_COMB (@lem2408445) (@lem2408456)). Qed.
Lemma lem2408458 : term846 = term866.
Proof. exact (EQ_MP (@lem2408457) (@lem2408435)). Qed.
Lemma lem2408485 : term503 = term866.
Proof. exact (TRANS (@lem2408431) (@lem2408458)). Qed.
Lemma lem2408486 : term505 = term867.
Proof. exact (MK_COMB (@lem2408334) (@lem2408485)). Qed.
Lemma lem2408489 : term507 = term868.
Proof. exact (MK_COMB (@lem2408293) (@lem2408486)). Qed.
Lemma lem2408492 : term509 = term869.
Proof. exact (MK_COMB (@lem2408252) (@lem2408489)). Qed.
Lemma lem2408495 : term511 = term870.
Proof. exact (MK_COMB (@lem2408158) (@lem2408492)). Qed.
Lemma lem2408498 : term513 = term871.
Proof. exact (MK_COMB (@lem2408003) (@lem2408495)). Qed.
Lemma lem2408501 : term515 = term872.
Proof. exact (MK_COMB (@lem2407962) (@lem2408498)). Qed.
Lemma lem2408504 : term517 = term873.
Proof. exact (MK_COMB (@lem2407868) (@lem2408501)). Qed.
Lemma lem2408508 : term519 = term873.
Proof. exact (TRANS (@lem2407713) (@lem2408504)). Qed.
Lemma lem2408509 (x : int) (y : int) (z : int) : (term277 x y z) = (term277 x y z).
Proof. exact (eq_refl (term277 x y z)). Qed.
Lemma lem2408510 (x : int) (y : int) : (term526 x y) = (term526 x y).
Proof. exact (fun_ext (fun z : int => @lem2408509 x y z)). Qed.
Lemma lem2408511 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408512 (x : int) (y : int) : (term537 x y) = (term537 x y).
Proof. exact (MK_COMB (@lem2408511) (@lem2408510 x y)). Qed.
Lemma lem2408513 (x : int) : (term548 x) = (term548 x).
Proof. exact (fun_ext (fun y : int => @lem2408512 x y)). Qed.
Lemma lem2408514 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408515 (x : int) : (term559 x) = (term559 x).
Proof. exact (MK_COMB (@lem2408514) (@lem2408513 x)). Qed.
Lemma lem2408516 : term570 = term570.
Proof. exact (fun_ext (fun x : int => @lem2408515 x)). Qed.
Lemma lem2408517 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408518 : term581 = term581.
Proof. exact (MK_COMB (@lem2408517) (@lem2408516)). Qed.
Lemma lem2408519 (x : int) (y : int) (z : int) : (term290 x y z) = (term290 x y z).
Proof. exact (eq_refl (term290 x y z)). Qed.
Lemma lem2408520 (x : int) (y : int) : (term527 x y) = (term527 x y).
Proof. exact (fun_ext (fun z : int => @lem2408519 x y z)). Qed.
Lemma lem2408521 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408522 (x : int) (y : int) : (term542 x y) = (term542 x y).
Proof. exact (MK_COMB (@lem2408521) (@lem2408520 x y)). Qed.
Lemma lem2408523 (x : int) : (term549 x) = (term549 x).
Proof. exact (fun_ext (fun y : int => @lem2408522 x y)). Qed.
Lemma lem2408524 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408525 (x : int) : (term564 x) = (term564 x).
Proof. exact (MK_COMB (@lem2408524) (@lem2408523 x)). Qed.
Lemma lem2408526 : term571 = term571.
Proof. exact (fun_ext (fun x : int => @lem2408525 x)). Qed.
Lemma lem2408527 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408528 : term586 = term586.
Proof. exact (MK_COMB (@lem2408527) (@lem2408526)). Qed.
Lemma lem2408529 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408530 : term583 = term583.
Proof. exact (MK_COMB (@lem2408529) (@lem2408518)). Qed.
Lemma lem2408531 : term587 = term587.
Proof. exact (MK_COMB (@lem2408530) (@lem2408528)). Qed.
Lemma lem2408532 (y : int) (x : int) : (term307 y x) = (term307 y x).
Proof. exact (eq_refl (term307 y x)). Qed.
Lemma lem2408533 (x : int) : (term591 x) = (term591 x).
Proof. exact (fun_ext (fun y : int => @lem2408532 y x)). Qed.
Lemma lem2408534 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408535 (x : int) : (term602 x) = (term602 x).
Proof. exact (MK_COMB (@lem2408534) (@lem2408533 x)). Qed.
Lemma lem2408536 : term613 = term613.
Proof. exact (fun_ext (fun x : int => @lem2408535 x)). Qed.
Lemma lem2408537 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408538 : term624 = term624.
Proof. exact (MK_COMB (@lem2408537) (@lem2408536)). Qed.
Lemma lem2408539 (x : int) (y : int) : (term307 x y) = (term307 x y).
Proof. exact (eq_refl (term307 x y)). Qed.
Lemma lem2408540 (x : int) : (term592 x) = (term592 x).
Proof. exact (fun_ext (fun y : int => @lem2408539 x y)). Qed.
Lemma lem2408541 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408542 (x : int) : (term607 x) = (term607 x).
Proof. exact (MK_COMB (@lem2408541) (@lem2408540 x)). Qed.
Lemma lem2408543 : term614 = term614.
Proof. exact (fun_ext (fun x : int => @lem2408542 x)). Qed.
Lemma lem2408544 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408545 : term629 = term629.
Proof. exact (MK_COMB (@lem2408544) (@lem2408543)). Qed.
Lemma lem2408546 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408547 : term626 = term626.
Proof. exact (MK_COMB (@lem2408546) (@lem2408538)). Qed.
Lemma lem2408548 : term630 = term630.
Proof. exact (MK_COMB (@lem2408547) (@lem2408545)). Qed.
Lemma lem2408549 (x : int) : (term333 x) = (term333 x).
Proof. exact (eq_refl (term333 x)). Qed.
Lemma lem2408550 : term634 = term634.
Proof. exact (fun_ext (fun x : int => @lem2408549 x)). Qed.
Lemma lem2408551 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408552 : term645 = term645.
Proof. exact (MK_COMB (@lem2408551) (@lem2408550)). Qed.
Lemma lem2408553 (x : int) : (term344 x) = (term344 x).
Proof. exact (eq_refl (term344 x)). Qed.
Lemma lem2408554 : term635 = term635.
Proof. exact (fun_ext (fun x : int => @lem2408553 x)). Qed.
Lemma lem2408555 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408556 : term650 = term650.
Proof. exact (MK_COMB (@lem2408555) (@lem2408554)). Qed.
Lemma lem2408557 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408558 : term647 = term647.
Proof. exact (MK_COMB (@lem2408557) (@lem2408552)). Qed.
Lemma lem2408559 : term651 = term651.
Proof. exact (MK_COMB (@lem2408558) (@lem2408556)). Qed.
Lemma lem2408560 (x : int) (y : int) (z : int) : (term370 x y z) = (term370 x y z).
Proof. exact (eq_refl (term370 x y z)). Qed.
Lemma lem2408561 (x : int) (y : int) : (term655 x y) = (term655 x y).
Proof. exact (fun_ext (fun z : int => @lem2408560 x y z)). Qed.
Lemma lem2408562 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408563 (x : int) (y : int) : (term666 x y) = (term666 x y).
Proof. exact (MK_COMB (@lem2408562) (@lem2408561 x y)). Qed.
Lemma lem2408564 (x : int) : (term677 x) = (term677 x).
Proof. exact (fun_ext (fun y : int => @lem2408563 x y)). Qed.
Lemma lem2408565 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408566 (x : int) : (term688 x) = (term688 x).
Proof. exact (MK_COMB (@lem2408565) (@lem2408564 x)). Qed.
Lemma lem2408567 : term699 = term699.
Proof. exact (fun_ext (fun x : int => @lem2408566 x)). Qed.
Lemma lem2408568 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408569 : term710 = term710.
Proof. exact (MK_COMB (@lem2408568) (@lem2408567)). Qed.
Lemma lem2408570 (x : int) (y : int) (z : int) : (term383 x y z) = (term383 x y z).
Proof. exact (eq_refl (term383 x y z)). Qed.
Lemma lem2408571 (x : int) (y : int) : (term656 x y) = (term656 x y).
Proof. exact (fun_ext (fun z : int => @lem2408570 x y z)). Qed.
Lemma lem2408572 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408573 (x : int) (y : int) : (term671 x y) = (term671 x y).
Proof. exact (MK_COMB (@lem2408572) (@lem2408571 x y)). Qed.
Lemma lem2408574 (x : int) : (term678 x) = (term678 x).
Proof. exact (fun_ext (fun y : int => @lem2408573 x y)). Qed.
Lemma lem2408575 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408576 (x : int) : (term693 x) = (term693 x).
Proof. exact (MK_COMB (@lem2408575) (@lem2408574 x)). Qed.
Lemma lem2408577 : term700 = term700.
Proof. exact (fun_ext (fun x : int => @lem2408576 x)). Qed.
Lemma lem2408578 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408579 : term715 = term715.
Proof. exact (MK_COMB (@lem2408578) (@lem2408577)). Qed.
Lemma lem2408580 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408581 : term712 = term712.
Proof. exact (MK_COMB (@lem2408580) (@lem2408569)). Qed.
Lemma lem2408582 : term716 = term716.
Proof. exact (MK_COMB (@lem2408581) (@lem2408579)). Qed.
Lemma lem2408583 (y : int) (x : int) : (term402 y x) = (term402 y x).
Proof. exact (eq_refl (term402 y x)). Qed.
Lemma lem2408584 (x : int) : (term720 x) = (term720 x).
Proof. exact (fun_ext (fun y : int => @lem2408583 y x)). Qed.
Lemma lem2408585 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408586 (x : int) : (term731 x) = (term731 x).
Proof. exact (MK_COMB (@lem2408585) (@lem2408584 x)). Qed.
Lemma lem2408587 : term742 = term742.
Proof. exact (fun_ext (fun x : int => @lem2408586 x)). Qed.
Lemma lem2408588 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408589 : term753 = term753.
Proof. exact (MK_COMB (@lem2408588) (@lem2408587)). Qed.
Lemma lem2408590 (x : int) (y : int) : (term402 x y) = (term402 x y).
Proof. exact (eq_refl (term402 x y)). Qed.
Lemma lem2408591 (x : int) : (term721 x) = (term721 x).
Proof. exact (fun_ext (fun y : int => @lem2408590 x y)). Qed.
Lemma lem2408592 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408593 (x : int) : (term736 x) = (term736 x).
Proof. exact (MK_COMB (@lem2408592) (@lem2408591 x)). Qed.
Lemma lem2408594 : term743 = term743.
Proof. exact (fun_ext (fun x : int => @lem2408593 x)). Qed.
Lemma lem2408595 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408596 : term758 = term758.
Proof. exact (MK_COMB (@lem2408595) (@lem2408594)). Qed.
Lemma lem2408597 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408598 : term755 = term755.
Proof. exact (MK_COMB (@lem2408597) (@lem2408589)). Qed.
Lemma lem2408599 : term759 = term759.
Proof. exact (MK_COMB (@lem2408598) (@lem2408596)). Qed.
Lemma lem2408600 (x : int) : (term426 x) = (term426 x).
Proof. exact (eq_refl (term426 x)). Qed.
Lemma lem2408601 : term763 = term763.
Proof. exact (fun_ext (fun x : int => @lem2408600 x)). Qed.
Lemma lem2408602 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408603 : term774 = term774.
Proof. exact (MK_COMB (@lem2408602) (@lem2408601)). Qed.
Lemma lem2408604 (x : int) : (term431 x) = (term431 x).
Proof. exact (eq_refl (term431 x)). Qed.
Lemma lem2408605 : term764 = term764.
Proof. exact (fun_ext (fun x : int => @lem2408604 x)). Qed.
Lemma lem2408606 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408607 : term779 = term779.
Proof. exact (MK_COMB (@lem2408606) (@lem2408605)). Qed.
Lemma lem2408608 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408609 : term776 = term776.
Proof. exact (MK_COMB (@lem2408608) (@lem2408603)). Qed.
Lemma lem2408610 : term780 = term780.
Proof. exact (MK_COMB (@lem2408609) (@lem2408607)). Qed.
Lemma lem2408611 (x : int) : (term451 x) = (term451 x).
Proof. exact (eq_refl (term451 x)). Qed.
Lemma lem2408612 : term784 = term784.
Proof. exact (fun_ext (fun x : int => @lem2408611 x)). Qed.
Lemma lem2408613 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408614 : term795 = term795.
Proof. exact (MK_COMB (@lem2408613) (@lem2408612)). Qed.
Lemma lem2408615 (x : int) : (term462 x) = (term462 x).
Proof. exact (eq_refl (term462 x)). Qed.
Lemma lem2408616 : term785 = term785.
Proof. exact (fun_ext (fun x : int => @lem2408615 x)). Qed.
Lemma lem2408617 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408618 : term800 = term800.
Proof. exact (MK_COMB (@lem2408617) (@lem2408616)). Qed.
Lemma lem2408619 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408620 : term797 = term797.
Proof. exact (MK_COMB (@lem2408619) (@lem2408614)). Qed.
Lemma lem2408621 : term801 = term801.
Proof. exact (MK_COMB (@lem2408620) (@lem2408618)). Qed.
Lemma lem2408622 (y : int) (x : int) (z : int) : (term483 y x z) = (term483 y x z).
Proof. exact (eq_refl (term483 y x z)). Qed.
Lemma lem2408623 (y : int) (x : int) : (term805 y x) = (term805 y x).
Proof. exact (fun_ext (fun z : int => @lem2408622 y x z)). Qed.
Lemma lem2408624 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408625 (y : int) (x : int) : (term816 y x) = (term816 y x).
Proof. exact (MK_COMB (@lem2408624) (@lem2408623 y x)). Qed.
Lemma lem2408626 (x : int) : (term827 x) = (term827 x).
Proof. exact (fun_ext (fun y : int => @lem2408625 y x)). Qed.
Lemma lem2408627 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408628 (x : int) : (term838 x) = (term838 x).
Proof. exact (MK_COMB (@lem2408627) (@lem2408626 x)). Qed.
Lemma lem2408629 : term849 = term849.
Proof. exact (fun_ext (fun x : int => @lem2408628 x)). Qed.
Lemma lem2408630 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408631 : term860 = term860.
Proof. exact (MK_COMB (@lem2408630) (@lem2408629)). Qed.
Lemma lem2408632 (x : int) (y : int) (z : int) : (term496 x y z) = (term496 x y z).
Proof. exact (eq_refl (term496 x y z)). Qed.
Lemma lem2408633 (x : int) (y : int) : (term806 x y) = (term806 x y).
Proof. exact (fun_ext (fun z : int => @lem2408632 x y z)). Qed.
Lemma lem2408634 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408635 (x : int) (y : int) : (term821 x y) = (term821 x y).
Proof. exact (MK_COMB (@lem2408634) (@lem2408633 x y)). Qed.
Lemma lem2408636 (x : int) : (term828 x) = (term828 x).
Proof. exact (fun_ext (fun y : int => @lem2408635 x y)). Qed.
Lemma lem2408637 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408638 (x : int) : (term843 x) = (term843 x).
Proof. exact (MK_COMB (@lem2408637) (@lem2408636 x)). Qed.
Lemma lem2408639 : term850 = term850.
Proof. exact (fun_ext (fun x : int => @lem2408638 x)). Qed.
Lemma lem2408640 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408641 : term865 = term865.
Proof. exact (MK_COMB (@lem2408640) (@lem2408639)). Qed.
Lemma lem2408642 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408643 : term862 = term862.
Proof. exact (MK_COMB (@lem2408642) (@lem2408631)). Qed.
Lemma lem2408644 : term866 = term866.
Proof. exact (MK_COMB (@lem2408643) (@lem2408641)). Qed.
Lemma lem2408645 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408646 : term802 = term802.
Proof. exact (MK_COMB (@lem2408645) (@lem2408621)). Qed.
Lemma lem2408647 : term867 = term867.
Proof. exact (MK_COMB (@lem2408646) (@lem2408644)). Qed.
Lemma lem2408648 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408649 : term781 = term781.
Proof. exact (MK_COMB (@lem2408648) (@lem2408610)). Qed.
Lemma lem2408650 : term868 = term868.
Proof. exact (MK_COMB (@lem2408649) (@lem2408647)). Qed.
Lemma lem2408651 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408652 : term760 = term760.
Proof. exact (MK_COMB (@lem2408651) (@lem2408599)). Qed.
Lemma lem2408653 : term869 = term869.
Proof. exact (MK_COMB (@lem2408652) (@lem2408650)). Qed.
Lemma lem2408654 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408655 : term717 = term717.
Proof. exact (MK_COMB (@lem2408654) (@lem2408582)). Qed.
Lemma lem2408656 : term870 = term870.
Proof. exact (MK_COMB (@lem2408655) (@lem2408653)). Qed.
Lemma lem2408657 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408658 : term652 = term652.
Proof. exact (MK_COMB (@lem2408657) (@lem2408559)). Qed.
Lemma lem2408659 : term871 = term871.
Proof. exact (MK_COMB (@lem2408658) (@lem2408656)). Qed.
Lemma lem2408660 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408661 : term631 = term631.
Proof. exact (MK_COMB (@lem2408660) (@lem2408548)). Qed.
Lemma lem2408662 : term872 = term872.
Proof. exact (MK_COMB (@lem2408661) (@lem2408659)). Qed.
Lemma lem2408663 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408664 : term588 = term588.
Proof. exact (MK_COMB (@lem2408663) (@lem2408531)). Qed.
Lemma lem2408665 : term873 = term873.
Proof. exact (MK_COMB (@lem2408664) (@lem2408662)). Qed.
Lemma lem2408666 : term519 = term873.
Proof. exact (TRANS (@lem2408508) (@lem2408665)). Qed.
Lemma lem2408667 (x : int) (y : int) (z : int) : (term277 x y z) = (term277 x y z).
Proof. exact (eq_refl (term277 x y z)). Qed.
Lemma lem2408668 (x : int) (y : int) : (term526 x y) = (term526 x y).
Proof. exact (fun_ext (fun z : int => @lem2408667 x y z)). Qed.
Lemma lem2408669 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408670 (x : int) (y : int) : (term537 x y) = (term537 x y).
Proof. exact (MK_COMB (@lem2408669) (@lem2408668 x y)). Qed.
Lemma lem2408671 (x : int) : (term548 x) = (term548 x).
Proof. exact (fun_ext (fun y : int => @lem2408670 x y)). Qed.
Lemma lem2408672 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408673 (x : int) : (term559 x) = (term559 x).
Proof. exact (MK_COMB (@lem2408672) (@lem2408671 x)). Qed.
Lemma lem2408674 : term570 = term570.
Proof. exact (fun_ext (fun x : int => @lem2408673 x)). Qed.
Lemma lem2408675 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408676 : term581 = term581.
Proof. exact (MK_COMB (@lem2408675) (@lem2408674)). Qed.
Lemma lem2408677 (x : int) (y : int) (z : int) : (term290 x y z) = (term290 x y z).
Proof. exact (eq_refl (term290 x y z)). Qed.
Lemma lem2408678 (x : int) (y : int) : (term527 x y) = (term527 x y).
Proof. exact (fun_ext (fun z : int => @lem2408677 x y z)). Qed.
Lemma lem2408679 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408680 (x : int) (y : int) : (term542 x y) = (term542 x y).
Proof. exact (MK_COMB (@lem2408679) (@lem2408678 x y)). Qed.
Lemma lem2408681 (x : int) : (term549 x) = (term549 x).
Proof. exact (fun_ext (fun y : int => @lem2408680 x y)). Qed.
Lemma lem2408682 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408683 (x : int) : (term564 x) = (term564 x).
Proof. exact (MK_COMB (@lem2408682) (@lem2408681 x)). Qed.
Lemma lem2408684 : term571 = term571.
Proof. exact (fun_ext (fun x : int => @lem2408683 x)). Qed.
Lemma lem2408685 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408686 : term586 = term586.
Proof. exact (MK_COMB (@lem2408685) (@lem2408684)). Qed.
Lemma lem2408687 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408688 : term583 = term583.
Proof. exact (MK_COMB (@lem2408687) (@lem2408676)). Qed.
Lemma lem2408689 : term587 = term587.
Proof. exact (MK_COMB (@lem2408688) (@lem2408686)). Qed.
Lemma lem2408690 (y : int) (x : int) : (term307 y x) = (term307 y x).
Proof. exact (eq_refl (term307 y x)). Qed.
Lemma lem2408691 (x : int) : (term591 x) = (term591 x).
Proof. exact (fun_ext (fun y : int => @lem2408690 y x)). Qed.
Lemma lem2408692 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408693 (x : int) : (term602 x) = (term602 x).
Proof. exact (MK_COMB (@lem2408692) (@lem2408691 x)). Qed.
Lemma lem2408694 : term613 = term613.
Proof. exact (fun_ext (fun x : int => @lem2408693 x)). Qed.
Lemma lem2408695 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408696 : term624 = term624.
Proof. exact (MK_COMB (@lem2408695) (@lem2408694)). Qed.
Lemma lem2408697 (x : int) (y : int) : (term307 x y) = (term307 x y).
Proof. exact (eq_refl (term307 x y)). Qed.
Lemma lem2408698 (x : int) : (term592 x) = (term592 x).
Proof. exact (fun_ext (fun y : int => @lem2408697 x y)). Qed.
Lemma lem2408699 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408700 (x : int) : (term607 x) = (term607 x).
Proof. exact (MK_COMB (@lem2408699) (@lem2408698 x)). Qed.
Lemma lem2408701 : term614 = term614.
Proof. exact (fun_ext (fun x : int => @lem2408700 x)). Qed.
Lemma lem2408702 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408703 : term629 = term629.
Proof. exact (MK_COMB (@lem2408702) (@lem2408701)). Qed.
Lemma lem2408704 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408705 : term626 = term626.
Proof. exact (MK_COMB (@lem2408704) (@lem2408696)). Qed.
Lemma lem2408706 : term630 = term630.
Proof. exact (MK_COMB (@lem2408705) (@lem2408703)). Qed.
Lemma lem2408707 (x : int) : (term333 x) = (term333 x).
Proof. exact (eq_refl (term333 x)). Qed.
Lemma lem2408708 : term634 = term634.
Proof. exact (fun_ext (fun x : int => @lem2408707 x)). Qed.
Lemma lem2408709 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408710 : term645 = term645.
Proof. exact (MK_COMB (@lem2408709) (@lem2408708)). Qed.
Lemma lem2408711 (x : int) : (term344 x) = (term344 x).
Proof. exact (eq_refl (term344 x)). Qed.
Lemma lem2408712 : term635 = term635.
Proof. exact (fun_ext (fun x : int => @lem2408711 x)). Qed.
Lemma lem2408713 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408714 : term650 = term650.
Proof. exact (MK_COMB (@lem2408713) (@lem2408712)). Qed.
Lemma lem2408715 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408716 : term647 = term647.
Proof. exact (MK_COMB (@lem2408715) (@lem2408710)). Qed.
Lemma lem2408717 : term651 = term651.
Proof. exact (MK_COMB (@lem2408716) (@lem2408714)). Qed.
Lemma lem2408718 (x : int) (y : int) (z : int) : (term370 x y z) = (term370 x y z).
Proof. exact (eq_refl (term370 x y z)). Qed.
Lemma lem2408719 (x : int) (y : int) : (term655 x y) = (term655 x y).
Proof. exact (fun_ext (fun z : int => @lem2408718 x y z)). Qed.
Lemma lem2408720 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408721 (x : int) (y : int) : (term666 x y) = (term666 x y).
Proof. exact (MK_COMB (@lem2408720) (@lem2408719 x y)). Qed.
Lemma lem2408722 (x : int) : (term677 x) = (term677 x).
Proof. exact (fun_ext (fun y : int => @lem2408721 x y)). Qed.
Lemma lem2408723 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408724 (x : int) : (term688 x) = (term688 x).
Proof. exact (MK_COMB (@lem2408723) (@lem2408722 x)). Qed.
Lemma lem2408725 : term699 = term699.
Proof. exact (fun_ext (fun x : int => @lem2408724 x)). Qed.
Lemma lem2408726 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408727 : term710 = term710.
Proof. exact (MK_COMB (@lem2408726) (@lem2408725)). Qed.
Lemma lem2408728 (x : int) (y : int) (z : int) : (term383 x y z) = (term383 x y z).
Proof. exact (eq_refl (term383 x y z)). Qed.
Lemma lem2408729 (x : int) (y : int) : (term656 x y) = (term656 x y).
Proof. exact (fun_ext (fun z : int => @lem2408728 x y z)). Qed.
Lemma lem2408730 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408731 (x : int) (y : int) : (term671 x y) = (term671 x y).
Proof. exact (MK_COMB (@lem2408730) (@lem2408729 x y)). Qed.
Lemma lem2408732 (x : int) : (term678 x) = (term678 x).
Proof. exact (fun_ext (fun y : int => @lem2408731 x y)). Qed.
Lemma lem2408733 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408734 (x : int) : (term693 x) = (term693 x).
Proof. exact (MK_COMB (@lem2408733) (@lem2408732 x)). Qed.
Lemma lem2408735 : term700 = term700.
Proof. exact (fun_ext (fun x : int => @lem2408734 x)). Qed.
Lemma lem2408736 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408737 : term715 = term715.
Proof. exact (MK_COMB (@lem2408736) (@lem2408735)). Qed.
Lemma lem2408738 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408739 : term712 = term712.
Proof. exact (MK_COMB (@lem2408738) (@lem2408727)). Qed.
Lemma lem2408740 : term716 = term716.
Proof. exact (MK_COMB (@lem2408739) (@lem2408737)). Qed.
Lemma lem2408741 (y : int) (x : int) : (term402 y x) = (term402 y x).
Proof. exact (eq_refl (term402 y x)). Qed.
Lemma lem2408742 (x : int) : (term720 x) = (term720 x).
Proof. exact (fun_ext (fun y : int => @lem2408741 y x)). Qed.
Lemma lem2408743 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408744 (x : int) : (term731 x) = (term731 x).
Proof. exact (MK_COMB (@lem2408743) (@lem2408742 x)). Qed.
Lemma lem2408745 : term742 = term742.
Proof. exact (fun_ext (fun x : int => @lem2408744 x)). Qed.
Lemma lem2408746 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408747 : term753 = term753.
Proof. exact (MK_COMB (@lem2408746) (@lem2408745)). Qed.
Lemma lem2408748 (x : int) (y : int) : (term402 x y) = (term402 x y).
Proof. exact (eq_refl (term402 x y)). Qed.
Lemma lem2408749 (x : int) : (term721 x) = (term721 x).
Proof. exact (fun_ext (fun y : int => @lem2408748 x y)). Qed.
Lemma lem2408750 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408751 (x : int) : (term736 x) = (term736 x).
Proof. exact (MK_COMB (@lem2408750) (@lem2408749 x)). Qed.
Lemma lem2408752 : term743 = term743.
Proof. exact (fun_ext (fun x : int => @lem2408751 x)). Qed.
Lemma lem2408753 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408754 : term758 = term758.
Proof. exact (MK_COMB (@lem2408753) (@lem2408752)). Qed.
Lemma lem2408755 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408756 : term755 = term755.
Proof. exact (MK_COMB (@lem2408755) (@lem2408747)). Qed.
Lemma lem2408757 : term759 = term759.
Proof. exact (MK_COMB (@lem2408756) (@lem2408754)). Qed.
Lemma lem2408758 (x : int) : (term426 x) = (term426 x).
Proof. exact (eq_refl (term426 x)). Qed.
Lemma lem2408759 : term763 = term763.
Proof. exact (fun_ext (fun x : int => @lem2408758 x)). Qed.
Lemma lem2408760 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408761 : term774 = term774.
Proof. exact (MK_COMB (@lem2408760) (@lem2408759)). Qed.
Lemma lem2408762 (x : int) : (term431 x) = (term431 x).
Proof. exact (eq_refl (term431 x)). Qed.
Lemma lem2408763 : term764 = term764.
Proof. exact (fun_ext (fun x : int => @lem2408762 x)). Qed.
Lemma lem2408764 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408765 : term779 = term779.
Proof. exact (MK_COMB (@lem2408764) (@lem2408763)). Qed.
Lemma lem2408766 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408767 : term776 = term776.
Proof. exact (MK_COMB (@lem2408766) (@lem2408761)). Qed.
Lemma lem2408768 : term780 = term780.
Proof. exact (MK_COMB (@lem2408767) (@lem2408765)). Qed.
Lemma lem2408769 (x : int) : (term451 x) = (term451 x).
Proof. exact (eq_refl (term451 x)). Qed.
Lemma lem2408770 : term784 = term784.
Proof. exact (fun_ext (fun x : int => @lem2408769 x)). Qed.
Lemma lem2408771 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408772 : term795 = term795.
Proof. exact (MK_COMB (@lem2408771) (@lem2408770)). Qed.
Lemma lem2408773 (x : int) : (term462 x) = (term462 x).
Proof. exact (eq_refl (term462 x)). Qed.
Lemma lem2408774 : term785 = term785.
Proof. exact (fun_ext (fun x : int => @lem2408773 x)). Qed.
Lemma lem2408775 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408776 : term800 = term800.
Proof. exact (MK_COMB (@lem2408775) (@lem2408774)). Qed.
Lemma lem2408777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408778 : term797 = term797.
Proof. exact (MK_COMB (@lem2408777) (@lem2408772)). Qed.
Lemma lem2408779 : term801 = term801.
Proof. exact (MK_COMB (@lem2408778) (@lem2408776)). Qed.
Lemma lem2408780 (y : int) (x : int) (z : int) : (term483 y x z) = (term483 y x z).
Proof. exact (eq_refl (term483 y x z)). Qed.
Lemma lem2408781 (y : int) (x : int) : (term805 y x) = (term805 y x).
Proof. exact (fun_ext (fun z : int => @lem2408780 y x z)). Qed.
Lemma lem2408782 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408783 (y : int) (x : int) : (term816 y x) = (term816 y x).
Proof. exact (MK_COMB (@lem2408782) (@lem2408781 y x)). Qed.
Lemma lem2408784 (x : int) : (term827 x) = (term827 x).
Proof. exact (fun_ext (fun y : int => @lem2408783 y x)). Qed.
Lemma lem2408785 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408786 (x : int) : (term838 x) = (term838 x).
Proof. exact (MK_COMB (@lem2408785) (@lem2408784 x)). Qed.
Lemma lem2408787 : term849 = term849.
Proof. exact (fun_ext (fun x : int => @lem2408786 x)). Qed.
Lemma lem2408788 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408789 : term860 = term860.
Proof. exact (MK_COMB (@lem2408788) (@lem2408787)). Qed.
Lemma lem2408790 (x : int) (y : int) (z : int) : (term496 x y z) = (term496 x y z).
Proof. exact (eq_refl (term496 x y z)). Qed.
Lemma lem2408791 (x : int) (y : int) : (term806 x y) = (term806 x y).
Proof. exact (fun_ext (fun z : int => @lem2408790 x y z)). Qed.
Lemma lem2408792 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408793 (x : int) (y : int) : (term821 x y) = (term821 x y).
Proof. exact (MK_COMB (@lem2408792) (@lem2408791 x y)). Qed.
Lemma lem2408794 (x : int) : (term828 x) = (term828 x).
Proof. exact (fun_ext (fun y : int => @lem2408793 x y)). Qed.
Lemma lem2408795 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408796 (x : int) : (term843 x) = (term843 x).
Proof. exact (MK_COMB (@lem2408795) (@lem2408794 x)). Qed.
Lemma lem2408797 : term850 = term850.
Proof. exact (fun_ext (fun x : int => @lem2408796 x)). Qed.
Lemma lem2408798 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2408799 : term865 = term865.
Proof. exact (MK_COMB (@lem2408798) (@lem2408797)). Qed.
Lemma lem2408800 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408801 : term862 = term862.
Proof. exact (MK_COMB (@lem2408800) (@lem2408789)). Qed.
Lemma lem2408802 : term866 = term866.
Proof. exact (MK_COMB (@lem2408801) (@lem2408799)). Qed.
Lemma lem2408803 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408804 : term802 = term802.
Proof. exact (MK_COMB (@lem2408803) (@lem2408779)). Qed.
Lemma lem2408805 : term867 = term867.
Proof. exact (MK_COMB (@lem2408804) (@lem2408802)). Qed.
Lemma lem2408806 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408807 : term781 = term781.
Proof. exact (MK_COMB (@lem2408806) (@lem2408768)). Qed.
Lemma lem2408808 : term868 = term868.
Proof. exact (MK_COMB (@lem2408807) (@lem2408805)). Qed.
Lemma lem2408809 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408810 : term760 = term760.
Proof. exact (MK_COMB (@lem2408809) (@lem2408757)). Qed.
Lemma lem2408811 : term869 = term869.
Proof. exact (MK_COMB (@lem2408810) (@lem2408808)). Qed.
Lemma lem2408812 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408813 : term717 = term717.
Proof. exact (MK_COMB (@lem2408812) (@lem2408740)). Qed.
Lemma lem2408814 : term870 = term870.
Proof. exact (MK_COMB (@lem2408813) (@lem2408811)). Qed.
Lemma lem2408815 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408816 : term652 = term652.
Proof. exact (MK_COMB (@lem2408815) (@lem2408717)). Qed.
Lemma lem2408817 : term871 = term871.
Proof. exact (MK_COMB (@lem2408816) (@lem2408814)). Qed.
Lemma lem2408818 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408819 : term631 = term631.
Proof. exact (MK_COMB (@lem2408818) (@lem2408706)). Qed.
Lemma lem2408820 : term872 = term872.
Proof. exact (MK_COMB (@lem2408819) (@lem2408817)). Qed.
Lemma lem2408821 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2408822 : term588 = term588.
Proof. exact (MK_COMB (@lem2408821) (@lem2408689)). Qed.
Lemma lem2408823 : term873 = term873.
Proof. exact (MK_COMB (@lem2408822) (@lem2408820)). Qed.
Lemma lem2408824 : term519 = term873.
Proof. exact (TRANS (@lem2408666) (@lem2408823)). Qed.
Lemma lem2408825 (x : int) (y : int) (z : int) : (term277 x y z) = (term874 x y z).
Proof. exact (@lem1988287 (term276 x y z) (term269 x y z)). Qed.
Lemma lem2408843 (x : int) (y : int) (z : int) : (term269 x y z) = (term875 x y z).
Proof. exact (@lem1982755 (real_of_int x) (term256 y z) term267). Qed.
Lemma lem2408848 (y : int) (z : int) : (term304 y z) = (term876 y z).
Proof. exact (@lem1982755 (real_of_int y) (real_of_int z) term267). Qed.
Lemma lem2408849 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2408850 (x : int) (y : int) (z : int) : (term875 x y z) = (term877 x y z).
Proof. exact (MK_COMB (@lem2408849 x) (@lem2408848 y z)). Qed.
Lemma lem2408852 (x : int) (y : int) (z : int) : (term269 x y z) = (term877 x y z).
Proof. exact (TRANS (@lem2408843 x y z) (@lem2408850 x y z)). Qed.
Lemma lem2408869 (x : int) (y : int) (z : int) : (term276 x y z) = (term262 x y z).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem2408870 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2408871 (x : int) (y : int) (z : int) : (term878 x y z) = (term879 x y z).
Proof. exact (MK_COMB (@lem2408870) (@lem2408869 x y z)). Qed.
Lemma lem2408872 (x : int) (y : int) (z : int) : (term880 x y z) = (term881 x y z).
Proof. exact (MK_COMB (@lem2408871 x y z) (@lem2408852 x y z)). Qed.
Lemma lem2408873 (x : int) (y : int) (z : int) : (term881 x y z) = (term882 x y z).
Proof. exact (@lem1982792 (term262 x y z) (term877 x y z)). Qed.
Lemma lem2408874 (x : int) (y : int) (z : int) : (term883 x y z) = (term884 x y z).
Proof. exact (@lem1982781 (real_of_int x) term885 (term876 y z)). Qed.
Lemma lem2408875 (y : int) (z : int) : (term886 y z) = (term887 y z).
Proof. exact (@lem1982781 (real_of_int y) term885 (term341 z)). Qed.
Lemma lem2408876 (z : int) : (term888 z) = (term889 z).
Proof. exact (@lem1982781 (real_of_int z) term885 term267). Qed.
Lemma lem2408878 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2408879 : term267 = term891.
Proof. exact (@lem2408878 term268). Qed.
Lemma lem2408881 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2408882 : term885 = term894.
Proof. exact (@lem2408881 term268). Qed.
Lemma lem2408883 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2408884 : term895 = term896.
Proof. exact (MK_COMB (@lem2408883) (@lem2408882)). Qed.
Lemma lem2408885 : term897 = term898.
Proof. exact (MK_COMB (@lem2408884) (@lem2408879)). Qed.
Lemma lem2408886 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2408888 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2408889 : term902 = term903.
Proof. exact (@lem2408888 term268 term268). Qed.
Lemma lem2408890 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2408891 : term905 = term268.
Proof. exact (EQ_MP (@lem2408890) (@lem940073)). Qed.
Lemma lem2408892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2408893 : term903 = term267.
Proof. exact (MK_COMB (@lem2408892) (@lem2408891)). Qed.
Lemma lem2408894 : term902 = term267.
Proof. exact (TRANS (@lem2408889) (@lem2408893)). Qed.
Lemma lem2408896 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2408897 : term897 = term908.
Proof. exact (@lem2408896 term268 term268). Qed.
Lemma lem2408898 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2408899 : term905 = term268.
Proof. exact (EQ_MP (@lem2408898) (@lem940073)). Qed.
Lemma lem2408900 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2408901 : term903 = term267.
Proof. exact (MK_COMB (@lem2408900) (@lem2408899)). Qed.
Lemma lem2408902 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2408903 : term908 = term885.
Proof. exact (MK_COMB (@lem2408902) (@lem2408901)). Qed.
Lemma lem2408904 : term897 = term885.
Proof. exact (TRANS (@lem2408897) (@lem2408903)). Qed.
Lemma lem2408905 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2408906 : term909 = term910.
Proof. exact (MK_COMB (@lem2408905) (@lem2408904)). Qed.
Lemma lem2408907 : term899 = term894.
Proof. exact (MK_COMB (@lem2408906) (@lem2408894)). Qed.
Lemma lem2408908 : term898 = term894.
Proof. exact (TRANS (@lem2408886) (@lem2408907)). Qed.
Lemma lem2408909 : term897 = term894.
Proof. exact (TRANS (@lem2408885) (@lem2408908)). Qed.
Lemma lem2408911 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2408912 : term894 = term885.
Proof. exact (@lem2408911 term885). Qed.
Lemma lem2408913 : term897 = term885.
Proof. exact (TRANS (@lem2408909) (@lem2408912)). Qed.
Lemma lem2408916 (z : int) : (term912 z) = (term912 z).
Proof. exact (eq_refl (term912 z)). Qed.
Lemma lem2408917 (z : int) : (term889 z) = (term913 z).
Proof. exact (MK_COMB (@lem2408916 z) (@lem2408913)). Qed.
Lemma lem2408918 (z : int) : (term888 z) = (term913 z).
Proof. exact (TRANS (@lem2408876 z) (@lem2408917 z)). Qed.
Lemma lem2408921 (y : int) : (term912 y) = (term912 y).
Proof. exact (eq_refl (term912 y)). Qed.
Lemma lem2408922 (y : int) (z : int) : (term887 y z) = (term914 y z).
Proof. exact (MK_COMB (@lem2408921 y) (@lem2408918 z)). Qed.
Lemma lem2408923 (y : int) (z : int) : (term886 y z) = (term914 y z).
Proof. exact (TRANS (@lem2408875 y z) (@lem2408922 y z)). Qed.
Lemma lem2408926 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2408927 (x : int) (y : int) (z : int) : (term884 x y z) = (term915 x y z).
Proof. exact (MK_COMB (@lem2408926 x) (@lem2408923 y z)). Qed.
Lemma lem2408928 (x : int) (y : int) (z : int) : (term883 x y z) = (term915 x y z).
Proof. exact (TRANS (@lem2408874 x y z) (@lem2408927 x y z)). Qed.
Lemma lem2408929 (x : int) (y : int) (z : int) : (term264 x y z) = (term264 x y z).
Proof. exact (eq_refl (term264 x y z)). Qed.
Lemma lem2408930 (x : int) (y : int) (z : int) : (term882 x y z) = (term916 x y z).
Proof. exact (MK_COMB (@lem2408929 x y z) (@lem2408928 x y z)). Qed.
Lemma lem2408931 (x : int) (y : int) (z : int) : (term916 x y z) = (term917 x y z).
Proof. exact (@lem1982753 (real_of_int x) (term918 x) (term256 y z) (term914 y z)). Qed.
Lemma lem2408932 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2408934 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2408935 : term267 = term891.
Proof. exact (@lem2408934 term268). Qed.
Lemma lem2408937 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2408938 : term885 = term894.
Proof. exact (@lem2408937 term268). Qed.
Lemma lem2408939 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2408940 : term921 = term922.
Proof. exact (MK_COMB (@lem2408939) (@lem2408938)). Qed.
Lemma lem2408941 : term923 = term924.
Proof. exact (MK_COMB (@lem2408940) (@lem2408935)). Qed.
Lemma lem2408942 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2408944 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2408945 : term927 = term928.
Proof. exact (@lem2408944 (NUMERAL 0) term268). Qed.
Lemma lem2408946 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2408947 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2408948 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2408947 h1) (fun h1 : term928 = True => @lem2408946)). Qed.
Lemma lem2408949 : term928 = True.
Proof. exact (EQ_MP (@lem2408948) (@lem2408946)). Qed.
Lemma lem2408950 : term927 = True.
Proof. exact (TRANS (@lem2408945) (@lem2408949)). Qed.
Lemma lem2408951 : True = term927.
Proof. exact (SYM (@lem2408950)). Qed.
Lemma lem2408952 : term927.
Proof. exact (EQ_MP (@lem2408951) (@lem0)). Qed.
Lemma lem2408953 : term930.
Proof. exact (@lem2408942 (@lem2408952)). Qed.
Lemma lem2408955 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2408956 : term927 = term928.
Proof. exact (@lem2408955 (NUMERAL 0) term268). Qed.
Lemma lem2408957 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2408958 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2408959 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2408958 h1) (fun h1 : term928 = True => @lem2408957)). Qed.
Lemma lem2408960 : term928 = True.
Proof. exact (EQ_MP (@lem2408959) (@lem2408957)). Qed.
Lemma lem2408961 : term927 = True.
Proof. exact (TRANS (@lem2408956) (@lem2408960)). Qed.
Lemma lem2408962 : True = term927.
Proof. exact (SYM (@lem2408961)). Qed.
Lemma lem2408963 : term927.
Proof. exact (EQ_MP (@lem2408962) (@lem0)). Qed.
Lemma lem2408964 : term931.
Proof. exact (@lem2408953 (@lem2408963)). Qed.
Lemma lem2408966 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2408967 : term927 = term928.
Proof. exact (@lem2408966 (NUMERAL 0) term268). Qed.
Lemma lem2408968 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2408969 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2408970 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2408969 h1) (fun h1 : term928 = True => @lem2408968)). Qed.
Lemma lem2408971 : term928 = True.
Proof. exact (EQ_MP (@lem2408970) (@lem2408968)). Qed.
Lemma lem2408972 : term927 = True.
Proof. exact (TRANS (@lem2408967) (@lem2408971)). Qed.
Lemma lem2408973 : True = term927.
Proof. exact (SYM (@lem2408972)). Qed.
Lemma lem2408974 : term927.
Proof. exact (EQ_MP (@lem2408973) (@lem0)). Qed.
Lemma lem2408975 : term932.
Proof. exact (@lem2408964 (@lem2408974)). Qed.
Lemma lem2408977 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2408978 : term902 = term903.
Proof. exact (@lem2408977 term268 term268). Qed.
Lemma lem2408979 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2408980 : term905 = term268.
Proof. exact (EQ_MP (@lem2408979) (@lem940073)). Qed.
Lemma lem2408981 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2408982 : term903 = term267.
Proof. exact (MK_COMB (@lem2408981) (@lem2408980)). Qed.
Lemma lem2408983 : term902 = term267.
Proof. exact (TRANS (@lem2408978) (@lem2408982)). Qed.
Lemma lem2408985 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2408986 : term897 = term908.
Proof. exact (@lem2408985 term268 term268). Qed.
Lemma lem2408987 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2408988 : term905 = term268.
Proof. exact (EQ_MP (@lem2408987) (@lem940073)). Qed.
Lemma lem2408989 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2408990 : term903 = term267.
Proof. exact (MK_COMB (@lem2408989) (@lem2408988)). Qed.
Lemma lem2408991 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2408992 : term908 = term885.
Proof. exact (MK_COMB (@lem2408991) (@lem2408990)). Qed.
Lemma lem2408993 : term897 = term885.
Proof. exact (TRANS (@lem2408986) (@lem2408992)). Qed.
Lemma lem2408994 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2408995 : term933 = term921.
Proof. exact (MK_COMB (@lem2408994) (@lem2408993)). Qed.
Lemma lem2408996 : term934 = term923.
Proof. exact (MK_COMB (@lem2408995) (@lem2408983)). Qed.
Lemma lem2408998 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2408999 : term923 = term324.
Proof. exact (@lem2408998 term268). Qed.
Lemma lem2409000 : term934 = term324.
Proof. exact (TRANS (@lem2408996) (@lem2408999)). Qed.
Lemma lem2409001 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409002 : term936 = term444.
Proof. exact (MK_COMB (@lem2409001) (@lem2409000)). Qed.
Lemma lem2409003 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409004 : term937 = term938.
Proof. exact (MK_COMB (@lem2409002) (@lem2409003)). Qed.
Lemma lem2409006 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409007 : term938 = term324.
Proof. exact (@lem2409006 term268). Qed.
Lemma lem2409008 : term937 = term324.
Proof. exact (TRANS (@lem2409004) (@lem2409007)). Qed.
Lemma lem2409010 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409011 : term902 = term903.
Proof. exact (@lem2409010 term268 term268). Qed.
Lemma lem2409012 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409013 : term905 = term268.
Proof. exact (EQ_MP (@lem2409012) (@lem940073)). Qed.
Lemma lem2409014 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409015 : term903 = term267.
Proof. exact (MK_COMB (@lem2409014) (@lem2409013)). Qed.
Lemma lem2409016 : term902 = term267.
Proof. exact (TRANS (@lem2409011) (@lem2409015)). Qed.
Lemma lem2409017 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2409018 : term940 = term938.
Proof. exact (MK_COMB (@lem2409017) (@lem2409016)). Qed.
Lemma lem2409020 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409021 : term938 = term324.
Proof. exact (@lem2409020 term268). Qed.
Lemma lem2409022 : term940 = term324.
Proof. exact (TRANS (@lem2409018) (@lem2409021)). Qed.
Lemma lem2409023 : term324 = term940.
Proof. exact (SYM (@lem2409022)). Qed.
Lemma lem2409024 : term937 = term940.
Proof. exact (TRANS (@lem2409008) (@lem2409023)). Qed.
Lemma lem2409025 : term924 = term941.
Proof. exact (@lem2408975 (@lem2409024)). Qed.
Lemma lem2409026 : term923 = term941.
Proof. exact (TRANS (@lem2408941) (@lem2409025)). Qed.
Lemma lem2409028 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2409029 : term941 = term324.
Proof. exact (@lem2409028 term324). Qed.
Lemma lem2409030 : term923 = term324.
Proof. exact (TRANS (@lem2409026) (@lem2409029)). Qed.
Lemma lem2409031 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409032 : term942 = term444.
Proof. exact (MK_COMB (@lem2409031) (@lem2409030)). Qed.
Lemma lem2409033 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2409034 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2409032) (@lem2409033 x)). Qed.
Lemma lem2409035 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2408932 x) (@lem2409034 x)). Qed.
Lemma lem2409036 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2409037 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2409035 x) (@lem2409036 x)). Qed.
Lemma lem2409038 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409039 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2409038) (@lem2409037 x)). Qed.
Lemma lem2409040 (y : int) (z : int) : (term944 y z) = (term945 y z).
Proof. exact (@lem1982753 (real_of_int y) (term918 y) (real_of_int z) (term913 z)). Qed.
Lemma lem2409041 (y : int) : (term919 y) = (term920 y).
Proof. exact (@lem1982715 term885 (real_of_int y)). Qed.
Lemma lem2409043 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409044 : term267 = term891.
Proof. exact (@lem2409043 term268). Qed.
Lemma lem2409046 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409047 : term885 = term894.
Proof. exact (@lem2409046 term268). Qed.
Lemma lem2409048 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409049 : term921 = term922.
Proof. exact (MK_COMB (@lem2409048) (@lem2409047)). Qed.
Lemma lem2409050 : term923 = term924.
Proof. exact (MK_COMB (@lem2409049) (@lem2409044)). Qed.
Lemma lem2409051 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2409053 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409054 : term927 = term928.
Proof. exact (@lem2409053 (NUMERAL 0) term268). Qed.
Lemma lem2409055 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409056 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409057 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409056 h1) (fun h1 : term928 = True => @lem2409055)). Qed.
Lemma lem2409058 : term928 = True.
Proof. exact (EQ_MP (@lem2409057) (@lem2409055)). Qed.
Lemma lem2409059 : term927 = True.
Proof. exact (TRANS (@lem2409054) (@lem2409058)). Qed.
Lemma lem2409060 : True = term927.
Proof. exact (SYM (@lem2409059)). Qed.
Lemma lem2409061 : term927.
Proof. exact (EQ_MP (@lem2409060) (@lem0)). Qed.
Lemma lem2409062 : term930.
Proof. exact (@lem2409051 (@lem2409061)). Qed.
Lemma lem2409064 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409065 : term927 = term928.
Proof. exact (@lem2409064 (NUMERAL 0) term268). Qed.
Lemma lem2409066 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409067 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409068 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409067 h1) (fun h1 : term928 = True => @lem2409066)). Qed.
Lemma lem2409069 : term928 = True.
Proof. exact (EQ_MP (@lem2409068) (@lem2409066)). Qed.
Lemma lem2409070 : term927 = True.
Proof. exact (TRANS (@lem2409065) (@lem2409069)). Qed.
Lemma lem2409071 : True = term927.
Proof. exact (SYM (@lem2409070)). Qed.
Lemma lem2409072 : term927.
Proof. exact (EQ_MP (@lem2409071) (@lem0)). Qed.
Lemma lem2409073 : term931.
Proof. exact (@lem2409062 (@lem2409072)). Qed.
Lemma lem2409075 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409076 : term927 = term928.
Proof. exact (@lem2409075 (NUMERAL 0) term268). Qed.
Lemma lem2409077 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409078 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409079 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409078 h1) (fun h1 : term928 = True => @lem2409077)). Qed.
Lemma lem2409080 : term928 = True.
Proof. exact (EQ_MP (@lem2409079) (@lem2409077)). Qed.
Lemma lem2409081 : term927 = True.
Proof. exact (TRANS (@lem2409076) (@lem2409080)). Qed.
Lemma lem2409082 : True = term927.
Proof. exact (SYM (@lem2409081)). Qed.
Lemma lem2409083 : term927.
Proof. exact (EQ_MP (@lem2409082) (@lem0)). Qed.
Lemma lem2409084 : term932.
Proof. exact (@lem2409073 (@lem2409083)). Qed.
Lemma lem2409086 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409087 : term902 = term903.
Proof. exact (@lem2409086 term268 term268). Qed.
Lemma lem2409088 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409089 : term905 = term268.
Proof. exact (EQ_MP (@lem2409088) (@lem940073)). Qed.
Lemma lem2409090 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409091 : term903 = term267.
Proof. exact (MK_COMB (@lem2409090) (@lem2409089)). Qed.
Lemma lem2409092 : term902 = term267.
Proof. exact (TRANS (@lem2409087) (@lem2409091)). Qed.
Lemma lem2409094 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409095 : term897 = term908.
Proof. exact (@lem2409094 term268 term268). Qed.
Lemma lem2409096 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409097 : term905 = term268.
Proof. exact (EQ_MP (@lem2409096) (@lem940073)). Qed.
Lemma lem2409098 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409099 : term903 = term267.
Proof. exact (MK_COMB (@lem2409098) (@lem2409097)). Qed.
Lemma lem2409100 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409101 : term908 = term885.
Proof. exact (MK_COMB (@lem2409100) (@lem2409099)). Qed.
Lemma lem2409102 : term897 = term885.
Proof. exact (TRANS (@lem2409095) (@lem2409101)). Qed.
Lemma lem2409103 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409104 : term933 = term921.
Proof. exact (MK_COMB (@lem2409103) (@lem2409102)). Qed.
Lemma lem2409105 : term934 = term923.
Proof. exact (MK_COMB (@lem2409104) (@lem2409092)). Qed.
Lemma lem2409107 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2409108 : term923 = term324.
Proof. exact (@lem2409107 term268). Qed.
Lemma lem2409109 : term934 = term324.
Proof. exact (TRANS (@lem2409105) (@lem2409108)). Qed.
Lemma lem2409110 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409111 : term936 = term444.
Proof. exact (MK_COMB (@lem2409110) (@lem2409109)). Qed.
Lemma lem2409112 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409113 : term937 = term938.
Proof. exact (MK_COMB (@lem2409111) (@lem2409112)). Qed.
Lemma lem2409115 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409116 : term938 = term324.
Proof. exact (@lem2409115 term268). Qed.
Lemma lem2409117 : term937 = term324.
Proof. exact (TRANS (@lem2409113) (@lem2409116)). Qed.
Lemma lem2409119 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409120 : term902 = term903.
Proof. exact (@lem2409119 term268 term268). Qed.
Lemma lem2409121 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409122 : term905 = term268.
Proof. exact (EQ_MP (@lem2409121) (@lem940073)). Qed.
Lemma lem2409123 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409124 : term903 = term267.
Proof. exact (MK_COMB (@lem2409123) (@lem2409122)). Qed.
Lemma lem2409125 : term902 = term267.
Proof. exact (TRANS (@lem2409120) (@lem2409124)). Qed.
Lemma lem2409126 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2409127 : term940 = term938.
Proof. exact (MK_COMB (@lem2409126) (@lem2409125)). Qed.
Lemma lem2409129 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409130 : term938 = term324.
Proof. exact (@lem2409129 term268). Qed.
Lemma lem2409131 : term940 = term324.
Proof. exact (TRANS (@lem2409127) (@lem2409130)). Qed.
Lemma lem2409132 : term324 = term940.
Proof. exact (SYM (@lem2409131)). Qed.
Lemma lem2409133 : term937 = term940.
Proof. exact (TRANS (@lem2409117) (@lem2409132)). Qed.
Lemma lem2409134 : term924 = term941.
Proof. exact (@lem2409084 (@lem2409133)). Qed.
Lemma lem2409135 : term923 = term941.
Proof. exact (TRANS (@lem2409050) (@lem2409134)). Qed.
Lemma lem2409137 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2409138 : term941 = term324.
Proof. exact (@lem2409137 term324). Qed.
Lemma lem2409139 : term923 = term324.
Proof. exact (TRANS (@lem2409135) (@lem2409138)). Qed.
Lemma lem2409140 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409141 : term942 = term444.
Proof. exact (MK_COMB (@lem2409140) (@lem2409139)). Qed.
Lemma lem2409142 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2409143 (y : int) : (term920 y) = (term445 y).
Proof. exact (MK_COMB (@lem2409141) (@lem2409142 y)). Qed.
Lemma lem2409144 (y : int) : (term919 y) = (term445 y).
Proof. exact (TRANS (@lem2409041 y) (@lem2409143 y)). Qed.
Lemma lem2409145 (y : int) : (term445 y) = term324.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2409146 (y : int) : (term919 y) = term324.
Proof. exact (TRANS (@lem2409144 y) (@lem2409145 y)). Qed.
Lemma lem2409147 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409148 (y : int) : (term943 y) = term326.
Proof. exact (MK_COMB (@lem2409147) (@lem2409146 y)). Qed.
Lemma lem2409149 (z : int) : (term946 z) = (term947 z).
Proof. exact (@lem1982763 (real_of_int z) (term918 z) term885). Qed.
Lemma lem2409150 (z : int) : (term919 z) = (term920 z).
Proof. exact (@lem1982715 term885 (real_of_int z)). Qed.
Lemma lem2409152 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409153 : term267 = term891.
Proof. exact (@lem2409152 term268). Qed.
Lemma lem2409155 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409156 : term885 = term894.
Proof. exact (@lem2409155 term268). Qed.
Lemma lem2409157 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409158 : term921 = term922.
Proof. exact (MK_COMB (@lem2409157) (@lem2409156)). Qed.
Lemma lem2409159 : term923 = term924.
Proof. exact (MK_COMB (@lem2409158) (@lem2409153)). Qed.
Lemma lem2409160 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2409162 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409163 : term927 = term928.
Proof. exact (@lem2409162 (NUMERAL 0) term268). Qed.
Lemma lem2409164 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409165 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409166 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409165 h1) (fun h1 : term928 = True => @lem2409164)). Qed.
Lemma lem2409167 : term928 = True.
Proof. exact (EQ_MP (@lem2409166) (@lem2409164)). Qed.
Lemma lem2409168 : term927 = True.
Proof. exact (TRANS (@lem2409163) (@lem2409167)). Qed.
Lemma lem2409169 : True = term927.
Proof. exact (SYM (@lem2409168)). Qed.
Lemma lem2409170 : term927.
Proof. exact (EQ_MP (@lem2409169) (@lem0)). Qed.
Lemma lem2409171 : term930.
Proof. exact (@lem2409160 (@lem2409170)). Qed.
Lemma lem2409173 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409174 : term927 = term928.
Proof. exact (@lem2409173 (NUMERAL 0) term268). Qed.
Lemma lem2409175 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409176 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409177 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409176 h1) (fun h1 : term928 = True => @lem2409175)). Qed.
Lemma lem2409178 : term928 = True.
Proof. exact (EQ_MP (@lem2409177) (@lem2409175)). Qed.
Lemma lem2409179 : term927 = True.
Proof. exact (TRANS (@lem2409174) (@lem2409178)). Qed.
Lemma lem2409180 : True = term927.
Proof. exact (SYM (@lem2409179)). Qed.
Lemma lem2409181 : term927.
Proof. exact (EQ_MP (@lem2409180) (@lem0)). Qed.
Lemma lem2409182 : term931.
Proof. exact (@lem2409171 (@lem2409181)). Qed.
Lemma lem2409184 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409185 : term927 = term928.
Proof. exact (@lem2409184 (NUMERAL 0) term268). Qed.
Lemma lem2409186 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409187 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409188 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409187 h1) (fun h1 : term928 = True => @lem2409186)). Qed.
Lemma lem2409189 : term928 = True.
Proof. exact (EQ_MP (@lem2409188) (@lem2409186)). Qed.
Lemma lem2409190 : term927 = True.
Proof. exact (TRANS (@lem2409185) (@lem2409189)). Qed.
Lemma lem2409191 : True = term927.
Proof. exact (SYM (@lem2409190)). Qed.
Lemma lem2409192 : term927.
Proof. exact (EQ_MP (@lem2409191) (@lem0)). Qed.
Lemma lem2409193 : term932.
Proof. exact (@lem2409182 (@lem2409192)). Qed.
Lemma lem2409195 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409196 : term902 = term903.
Proof. exact (@lem2409195 term268 term268). Qed.
Lemma lem2409197 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409198 : term905 = term268.
Proof. exact (EQ_MP (@lem2409197) (@lem940073)). Qed.
Lemma lem2409199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409200 : term903 = term267.
Proof. exact (MK_COMB (@lem2409199) (@lem2409198)). Qed.
Lemma lem2409201 : term902 = term267.
Proof. exact (TRANS (@lem2409196) (@lem2409200)). Qed.
Lemma lem2409203 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409204 : term897 = term908.
Proof. exact (@lem2409203 term268 term268). Qed.
Lemma lem2409205 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409206 : term905 = term268.
Proof. exact (EQ_MP (@lem2409205) (@lem940073)). Qed.
Lemma lem2409207 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409208 : term903 = term267.
Proof. exact (MK_COMB (@lem2409207) (@lem2409206)). Qed.
Lemma lem2409209 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409210 : term908 = term885.
Proof. exact (MK_COMB (@lem2409209) (@lem2409208)). Qed.
Lemma lem2409211 : term897 = term885.
Proof. exact (TRANS (@lem2409204) (@lem2409210)). Qed.
Lemma lem2409212 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409213 : term933 = term921.
Proof. exact (MK_COMB (@lem2409212) (@lem2409211)). Qed.
Lemma lem2409214 : term934 = term923.
Proof. exact (MK_COMB (@lem2409213) (@lem2409201)). Qed.
Lemma lem2409216 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2409217 : term923 = term324.
Proof. exact (@lem2409216 term268). Qed.
Lemma lem2409218 : term934 = term324.
Proof. exact (TRANS (@lem2409214) (@lem2409217)). Qed.
Lemma lem2409219 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409220 : term936 = term444.
Proof. exact (MK_COMB (@lem2409219) (@lem2409218)). Qed.
Lemma lem2409221 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409222 : term937 = term938.
Proof. exact (MK_COMB (@lem2409220) (@lem2409221)). Qed.
Lemma lem2409224 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409225 : term938 = term324.
Proof. exact (@lem2409224 term268). Qed.
Lemma lem2409226 : term937 = term324.
Proof. exact (TRANS (@lem2409222) (@lem2409225)). Qed.
Lemma lem2409228 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409229 : term902 = term903.
Proof. exact (@lem2409228 term268 term268). Qed.
Lemma lem2409230 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409231 : term905 = term268.
Proof. exact (EQ_MP (@lem2409230) (@lem940073)). Qed.
Lemma lem2409232 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409233 : term903 = term267.
Proof. exact (MK_COMB (@lem2409232) (@lem2409231)). Qed.
Lemma lem2409234 : term902 = term267.
Proof. exact (TRANS (@lem2409229) (@lem2409233)). Qed.
Lemma lem2409235 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2409236 : term940 = term938.
Proof. exact (MK_COMB (@lem2409235) (@lem2409234)). Qed.
Lemma lem2409238 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409239 : term938 = term324.
Proof. exact (@lem2409238 term268). Qed.
Lemma lem2409240 : term940 = term324.
Proof. exact (TRANS (@lem2409236) (@lem2409239)). Qed.
Lemma lem2409241 : term324 = term940.
Proof. exact (SYM (@lem2409240)). Qed.
Lemma lem2409242 : term937 = term940.
Proof. exact (TRANS (@lem2409226) (@lem2409241)). Qed.
Lemma lem2409243 : term924 = term941.
Proof. exact (@lem2409193 (@lem2409242)). Qed.
Lemma lem2409244 : term923 = term941.
Proof. exact (TRANS (@lem2409159) (@lem2409243)). Qed.
Lemma lem2409246 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2409247 : term941 = term324.
Proof. exact (@lem2409246 term324). Qed.
Lemma lem2409248 : term923 = term324.
Proof. exact (TRANS (@lem2409244) (@lem2409247)). Qed.
Lemma lem2409249 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409250 : term942 = term444.
Proof. exact (MK_COMB (@lem2409249) (@lem2409248)). Qed.
Lemma lem2409251 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2409252 (z : int) : (term920 z) = (term445 z).
Proof. exact (MK_COMB (@lem2409250) (@lem2409251 z)). Qed.
Lemma lem2409253 (z : int) : (term919 z) = (term445 z).
Proof. exact (TRANS (@lem2409150 z) (@lem2409252 z)). Qed.
Lemma lem2409254 (z : int) : (term445 z) = term324.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem2409255 (z : int) : (term919 z) = term324.
Proof. exact (TRANS (@lem2409253 z) (@lem2409254 z)). Qed.
Lemma lem2409256 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409257 (z : int) : (term943 z) = term326.
Proof. exact (MK_COMB (@lem2409256) (@lem2409255 z)). Qed.
Lemma lem2409258 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2409259 (z : int) : (term947 z) = term948.
Proof. exact (MK_COMB (@lem2409257 z) (@lem2409258)). Qed.
Lemma lem2409260 (z : int) : (term946 z) = term948.
Proof. exact (TRANS (@lem2409149 z) (@lem2409259 z)). Qed.
Lemma lem2409261 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2409262 (z : int) : (term946 z) = term885.
Proof. exact (TRANS (@lem2409260 z) (@lem2409261)). Qed.
Lemma lem2409263 (y : int) (z : int) : (term945 y z) = term948.
Proof. exact (MK_COMB (@lem2409148 y) (@lem2409262 z)). Qed.
Lemma lem2409264 (y : int) (z : int) : (term944 y z) = term948.
Proof. exact (TRANS (@lem2409040 y z) (@lem2409263 y z)). Qed.
Lemma lem2409265 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2409266 (y : int) (z : int) : (term944 y z) = term885.
Proof. exact (TRANS (@lem2409264 y z) (@lem2409265)). Qed.
Lemma lem2409267 (x : int) (y : int) (z : int) : (term917 x y z) = term948.
Proof. exact (MK_COMB (@lem2409039 x) (@lem2409266 y z)). Qed.
Lemma lem2409268 (x : int) (y : int) (z : int) : (term916 x y z) = term948.
Proof. exact (TRANS (@lem2408931 x y z) (@lem2409267 x y z)). Qed.
Lemma lem2409269 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2409270 (x : int) (y : int) (z : int) : (term916 x y z) = term885.
Proof. exact (TRANS (@lem2409268 x y z) (@lem2409269)). Qed.
Lemma lem2409271 (x : int) (y : int) (z : int) : (term882 x y z) = term885.
Proof. exact (TRANS (@lem2408930 x y z) (@lem2409270 x y z)). Qed.
Lemma lem2409272 (x : int) (y : int) (z : int) : (term881 x y z) = term885.
Proof. exact (TRANS (@lem2408873 x y z) (@lem2409271 x y z)). Qed.
Lemma lem2409273 (x : int) (y : int) (z : int) : (term880 x y z) = term885.
Proof. exact (TRANS (@lem2408872 x y z) (@lem2409272 x y z)). Qed.
Lemma lem2409274 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2409275 (x : int) (y : int) (z : int) : (term949 x y z) = term950.
Proof. exact (MK_COMB (@lem2409274) (@lem2409273 x y z)). Qed.
Lemma lem2409276 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2409277 (x : int) (y : int) (z : int) : (term874 x y z) = term951.
Proof. exact (MK_COMB (@lem2409275 x y z) (@lem2409276)). Qed.
Lemma lem2409278 (x : int) (y : int) (z : int) : (term277 x y z) = term951.
Proof. exact (TRANS (@lem2408825 x y z) (@lem2409277 x y z)). Qed.
Lemma lem2409279 (x : int) (y : int) : (term526 x y) = term952.
Proof. exact (fun_ext (fun z : int => @lem2409278 x y z)). Qed.
Lemma lem2409280 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2409281 (x : int) (y : int) : (term537 x y) = term953.
Proof. exact (MK_COMB (@lem2409280) (@lem2409279 x y)). Qed.
Lemma lem2409282 (x : int) : (term548 x) = term954.
Proof. exact (fun_ext (fun y : int => @lem2409281 x y)). Qed.
Lemma lem2409283 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2409284 (x : int) : (term559 x) = term955.
Proof. exact (MK_COMB (@lem2409283) (@lem2409282 x)). Qed.
Lemma lem2409285 : term570 = term956.
Proof. exact (fun_ext (fun x : int => @lem2409284 x)). Qed.
Lemma lem2409286 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2409287 : term581 = term957.
Proof. exact (MK_COMB (@lem2409286) (@lem2409285)). Qed.
Lemma lem2409288 (x : int) (y : int) (z : int) : (term290 x y z) = (term958 x y z).
Proof. exact (@lem1988287 (term262 x y z) (term287 x y z)). Qed.
Lemma lem2409289 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409306 (x : int) (y : int) (z : int) : (term276 x y z) = (term262 x y z).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem2409307 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409308 (x : int) (y : int) (z : int) : (term286 x y z) = (term264 x y z).
Proof. exact (MK_COMB (@lem2409307) (@lem2409306 x y z)). Qed.
Lemma lem2409309 (x : int) (y : int) (z : int) : (term287 x y z) = (term269 x y z).
Proof. exact (MK_COMB (@lem2409308 x y z) (@lem2409289)). Qed.
Lemma lem2409310 (x : int) (y : int) (z : int) : (term269 x y z) = (term875 x y z).
Proof. exact (@lem1982755 (real_of_int x) (term256 y z) term267). Qed.
Lemma lem2409315 (y : int) (z : int) : (term304 y z) = (term876 y z).
Proof. exact (@lem1982755 (real_of_int y) (real_of_int z) term267). Qed.
Lemma lem2409316 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2409317 (x : int) (y : int) (z : int) : (term875 x y z) = (term877 x y z).
Proof. exact (MK_COMB (@lem2409316 x) (@lem2409315 y z)). Qed.
Lemma lem2409318 (x : int) (y : int) (z : int) : (term269 x y z) = (term877 x y z).
Proof. exact (TRANS (@lem2409310 x y z) (@lem2409317 x y z)). Qed.
Lemma lem2409319 (x : int) (y : int) (z : int) : (term287 x y z) = (term877 x y z).
Proof. exact (TRANS (@lem2409309 x y z) (@lem2409318 x y z)). Qed.
Lemma lem2409334 (x : int) (y : int) (z : int) : (term879 x y z) = (term879 x y z).
Proof. exact (eq_refl (term879 x y z)). Qed.
Lemma lem2409335 (x : int) (y : int) (z : int) : (term959 x y z) = (term881 x y z).
Proof. exact (MK_COMB (@lem2409334 x y z) (@lem2409319 x y z)). Qed.
Lemma lem2409336 (x : int) (y : int) (z : int) : (term881 x y z) = (term882 x y z).
Proof. exact (@lem1982792 (term262 x y z) (term877 x y z)). Qed.
Lemma lem2409337 (x : int) (y : int) (z : int) : (term883 x y z) = (term884 x y z).
Proof. exact (@lem1982781 (real_of_int x) term885 (term876 y z)). Qed.
Lemma lem2409338 (y : int) (z : int) : (term886 y z) = (term887 y z).
Proof. exact (@lem1982781 (real_of_int y) term885 (term341 z)). Qed.
Lemma lem2409339 (z : int) : (term888 z) = (term889 z).
Proof. exact (@lem1982781 (real_of_int z) term885 term267). Qed.
Lemma lem2409341 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409342 : term267 = term891.
Proof. exact (@lem2409341 term268). Qed.
Lemma lem2409344 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409345 : term885 = term894.
Proof. exact (@lem2409344 term268). Qed.
Lemma lem2409346 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409347 : term895 = term896.
Proof. exact (MK_COMB (@lem2409346) (@lem2409345)). Qed.
Lemma lem2409348 : term897 = term898.
Proof. exact (MK_COMB (@lem2409347) (@lem2409342)). Qed.
Lemma lem2409349 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2409351 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409352 : term902 = term903.
Proof. exact (@lem2409351 term268 term268). Qed.
Lemma lem2409353 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409354 : term905 = term268.
Proof. exact (EQ_MP (@lem2409353) (@lem940073)). Qed.
Lemma lem2409355 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409356 : term903 = term267.
Proof. exact (MK_COMB (@lem2409355) (@lem2409354)). Qed.
Lemma lem2409357 : term902 = term267.
Proof. exact (TRANS (@lem2409352) (@lem2409356)). Qed.
Lemma lem2409359 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409360 : term897 = term908.
Proof. exact (@lem2409359 term268 term268). Qed.
Lemma lem2409361 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409362 : term905 = term268.
Proof. exact (EQ_MP (@lem2409361) (@lem940073)). Qed.
Lemma lem2409363 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409364 : term903 = term267.
Proof. exact (MK_COMB (@lem2409363) (@lem2409362)). Qed.
Lemma lem2409365 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409366 : term908 = term885.
Proof. exact (MK_COMB (@lem2409365) (@lem2409364)). Qed.
Lemma lem2409367 : term897 = term885.
Proof. exact (TRANS (@lem2409360) (@lem2409366)). Qed.
Lemma lem2409368 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2409369 : term909 = term910.
Proof. exact (MK_COMB (@lem2409368) (@lem2409367)). Qed.
Lemma lem2409370 : term899 = term894.
Proof. exact (MK_COMB (@lem2409369) (@lem2409357)). Qed.
Lemma lem2409371 : term898 = term894.
Proof. exact (TRANS (@lem2409349) (@lem2409370)). Qed.
Lemma lem2409372 : term897 = term894.
Proof. exact (TRANS (@lem2409348) (@lem2409371)). Qed.
Lemma lem2409374 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2409375 : term894 = term885.
Proof. exact (@lem2409374 term885). Qed.
Lemma lem2409376 : term897 = term885.
Proof. exact (TRANS (@lem2409372) (@lem2409375)). Qed.
Lemma lem2409379 (z : int) : (term912 z) = (term912 z).
Proof. exact (eq_refl (term912 z)). Qed.
Lemma lem2409380 (z : int) : (term889 z) = (term913 z).
Proof. exact (MK_COMB (@lem2409379 z) (@lem2409376)). Qed.
Lemma lem2409381 (z : int) : (term888 z) = (term913 z).
Proof. exact (TRANS (@lem2409339 z) (@lem2409380 z)). Qed.
Lemma lem2409384 (y : int) : (term912 y) = (term912 y).
Proof. exact (eq_refl (term912 y)). Qed.
Lemma lem2409385 (y : int) (z : int) : (term887 y z) = (term914 y z).
Proof. exact (MK_COMB (@lem2409384 y) (@lem2409381 z)). Qed.
Lemma lem2409386 (y : int) (z : int) : (term886 y z) = (term914 y z).
Proof. exact (TRANS (@lem2409338 y z) (@lem2409385 y z)). Qed.
Lemma lem2409389 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2409390 (x : int) (y : int) (z : int) : (term884 x y z) = (term915 x y z).
Proof. exact (MK_COMB (@lem2409389 x) (@lem2409386 y z)). Qed.
Lemma lem2409391 (x : int) (y : int) (z : int) : (term883 x y z) = (term915 x y z).
Proof. exact (TRANS (@lem2409337 x y z) (@lem2409390 x y z)). Qed.
Lemma lem2409392 (x : int) (y : int) (z : int) : (term264 x y z) = (term264 x y z).
Proof. exact (eq_refl (term264 x y z)). Qed.
Lemma lem2409393 (x : int) (y : int) (z : int) : (term882 x y z) = (term916 x y z).
Proof. exact (MK_COMB (@lem2409392 x y z) (@lem2409391 x y z)). Qed.
Lemma lem2409394 (x : int) (y : int) (z : int) : (term916 x y z) = (term917 x y z).
Proof. exact (@lem1982753 (real_of_int x) (term918 x) (term256 y z) (term914 y z)). Qed.
Lemma lem2409395 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2409397 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409398 : term267 = term891.
Proof. exact (@lem2409397 term268). Qed.
Lemma lem2409400 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409401 : term885 = term894.
Proof. exact (@lem2409400 term268). Qed.
Lemma lem2409402 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409403 : term921 = term922.
Proof. exact (MK_COMB (@lem2409402) (@lem2409401)). Qed.
Lemma lem2409404 : term923 = term924.
Proof. exact (MK_COMB (@lem2409403) (@lem2409398)). Qed.
Lemma lem2409405 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2409407 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409408 : term927 = term928.
Proof. exact (@lem2409407 (NUMERAL 0) term268). Qed.
Lemma lem2409409 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409410 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409411 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409410 h1) (fun h1 : term928 = True => @lem2409409)). Qed.
Lemma lem2409412 : term928 = True.
Proof. exact (EQ_MP (@lem2409411) (@lem2409409)). Qed.
Lemma lem2409413 : term927 = True.
Proof. exact (TRANS (@lem2409408) (@lem2409412)). Qed.
Lemma lem2409414 : True = term927.
Proof. exact (SYM (@lem2409413)). Qed.
Lemma lem2409415 : term927.
Proof. exact (EQ_MP (@lem2409414) (@lem0)). Qed.
Lemma lem2409416 : term930.
Proof. exact (@lem2409405 (@lem2409415)). Qed.
Lemma lem2409418 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409419 : term927 = term928.
Proof. exact (@lem2409418 (NUMERAL 0) term268). Qed.
Lemma lem2409420 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409421 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409422 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409421 h1) (fun h1 : term928 = True => @lem2409420)). Qed.
Lemma lem2409423 : term928 = True.
Proof. exact (EQ_MP (@lem2409422) (@lem2409420)). Qed.
Lemma lem2409424 : term927 = True.
Proof. exact (TRANS (@lem2409419) (@lem2409423)). Qed.
Lemma lem2409425 : True = term927.
Proof. exact (SYM (@lem2409424)). Qed.
Lemma lem2409426 : term927.
Proof. exact (EQ_MP (@lem2409425) (@lem0)). Qed.
Lemma lem2409427 : term931.
Proof. exact (@lem2409416 (@lem2409426)). Qed.
Lemma lem2409429 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409430 : term927 = term928.
Proof. exact (@lem2409429 (NUMERAL 0) term268). Qed.
Lemma lem2409431 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409432 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409433 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409432 h1) (fun h1 : term928 = True => @lem2409431)). Qed.
Lemma lem2409434 : term928 = True.
Proof. exact (EQ_MP (@lem2409433) (@lem2409431)). Qed.
Lemma lem2409435 : term927 = True.
Proof. exact (TRANS (@lem2409430) (@lem2409434)). Qed.
Lemma lem2409436 : True = term927.
Proof. exact (SYM (@lem2409435)). Qed.
Lemma lem2409437 : term927.
Proof. exact (EQ_MP (@lem2409436) (@lem0)). Qed.
Lemma lem2409438 : term932.
Proof. exact (@lem2409427 (@lem2409437)). Qed.
Lemma lem2409440 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409441 : term902 = term903.
Proof. exact (@lem2409440 term268 term268). Qed.
Lemma lem2409442 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409443 : term905 = term268.
Proof. exact (EQ_MP (@lem2409442) (@lem940073)). Qed.
Lemma lem2409444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409445 : term903 = term267.
Proof. exact (MK_COMB (@lem2409444) (@lem2409443)). Qed.
Lemma lem2409446 : term902 = term267.
Proof. exact (TRANS (@lem2409441) (@lem2409445)). Qed.
Lemma lem2409448 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409449 : term897 = term908.
Proof. exact (@lem2409448 term268 term268). Qed.
Lemma lem2409450 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409451 : term905 = term268.
Proof. exact (EQ_MP (@lem2409450) (@lem940073)). Qed.
Lemma lem2409452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409453 : term903 = term267.
Proof. exact (MK_COMB (@lem2409452) (@lem2409451)). Qed.
Lemma lem2409454 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409455 : term908 = term885.
Proof. exact (MK_COMB (@lem2409454) (@lem2409453)). Qed.
Lemma lem2409456 : term897 = term885.
Proof. exact (TRANS (@lem2409449) (@lem2409455)). Qed.
Lemma lem2409457 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409458 : term933 = term921.
Proof. exact (MK_COMB (@lem2409457) (@lem2409456)). Qed.
Lemma lem2409459 : term934 = term923.
Proof. exact (MK_COMB (@lem2409458) (@lem2409446)). Qed.
Lemma lem2409461 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2409462 : term923 = term324.
Proof. exact (@lem2409461 term268). Qed.
Lemma lem2409463 : term934 = term324.
Proof. exact (TRANS (@lem2409459) (@lem2409462)). Qed.
Lemma lem2409464 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409465 : term936 = term444.
Proof. exact (MK_COMB (@lem2409464) (@lem2409463)). Qed.
Lemma lem2409466 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409467 : term937 = term938.
Proof. exact (MK_COMB (@lem2409465) (@lem2409466)). Qed.
Lemma lem2409469 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409470 : term938 = term324.
Proof. exact (@lem2409469 term268). Qed.
Lemma lem2409471 : term937 = term324.
Proof. exact (TRANS (@lem2409467) (@lem2409470)). Qed.
Lemma lem2409473 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409474 : term902 = term903.
Proof. exact (@lem2409473 term268 term268). Qed.
Lemma lem2409475 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409476 : term905 = term268.
Proof. exact (EQ_MP (@lem2409475) (@lem940073)). Qed.
Lemma lem2409477 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409478 : term903 = term267.
Proof. exact (MK_COMB (@lem2409477) (@lem2409476)). Qed.
Lemma lem2409479 : term902 = term267.
Proof. exact (TRANS (@lem2409474) (@lem2409478)). Qed.
Lemma lem2409480 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2409481 : term940 = term938.
Proof. exact (MK_COMB (@lem2409480) (@lem2409479)). Qed.
Lemma lem2409483 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409484 : term938 = term324.
Proof. exact (@lem2409483 term268). Qed.
Lemma lem2409485 : term940 = term324.
Proof. exact (TRANS (@lem2409481) (@lem2409484)). Qed.
Lemma lem2409486 : term324 = term940.
Proof. exact (SYM (@lem2409485)). Qed.
Lemma lem2409487 : term937 = term940.
Proof. exact (TRANS (@lem2409471) (@lem2409486)). Qed.
Lemma lem2409488 : term924 = term941.
Proof. exact (@lem2409438 (@lem2409487)). Qed.
Lemma lem2409489 : term923 = term941.
Proof. exact (TRANS (@lem2409404) (@lem2409488)). Qed.
Lemma lem2409491 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2409492 : term941 = term324.
Proof. exact (@lem2409491 term324). Qed.
Lemma lem2409493 : term923 = term324.
Proof. exact (TRANS (@lem2409489) (@lem2409492)). Qed.
Lemma lem2409494 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409495 : term942 = term444.
Proof. exact (MK_COMB (@lem2409494) (@lem2409493)). Qed.
Lemma lem2409496 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2409497 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2409495) (@lem2409496 x)). Qed.
Lemma lem2409498 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2409395 x) (@lem2409497 x)). Qed.
Lemma lem2409499 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2409500 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2409498 x) (@lem2409499 x)). Qed.
Lemma lem2409501 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409502 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2409501) (@lem2409500 x)). Qed.
Lemma lem2409503 (y : int) (z : int) : (term944 y z) = (term945 y z).
Proof. exact (@lem1982753 (real_of_int y) (term918 y) (real_of_int z) (term913 z)). Qed.
Lemma lem2409504 (y : int) : (term919 y) = (term920 y).
Proof. exact (@lem1982715 term885 (real_of_int y)). Qed.
Lemma lem2409506 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409507 : term267 = term891.
Proof. exact (@lem2409506 term268). Qed.
Lemma lem2409509 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409510 : term885 = term894.
Proof. exact (@lem2409509 term268). Qed.
Lemma lem2409511 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409512 : term921 = term922.
Proof. exact (MK_COMB (@lem2409511) (@lem2409510)). Qed.
Lemma lem2409513 : term923 = term924.
Proof. exact (MK_COMB (@lem2409512) (@lem2409507)). Qed.
Lemma lem2409514 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2409516 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409517 : term927 = term928.
Proof. exact (@lem2409516 (NUMERAL 0) term268). Qed.
Lemma lem2409518 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409519 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409520 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409519 h1) (fun h1 : term928 = True => @lem2409518)). Qed.
Lemma lem2409521 : term928 = True.
Proof. exact (EQ_MP (@lem2409520) (@lem2409518)). Qed.
Lemma lem2409522 : term927 = True.
Proof. exact (TRANS (@lem2409517) (@lem2409521)). Qed.
Lemma lem2409523 : True = term927.
Proof. exact (SYM (@lem2409522)). Qed.
Lemma lem2409524 : term927.
Proof. exact (EQ_MP (@lem2409523) (@lem0)). Qed.
Lemma lem2409525 : term930.
Proof. exact (@lem2409514 (@lem2409524)). Qed.
Lemma lem2409527 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409528 : term927 = term928.
Proof. exact (@lem2409527 (NUMERAL 0) term268). Qed.
Lemma lem2409529 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409530 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409531 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409530 h1) (fun h1 : term928 = True => @lem2409529)). Qed.
Lemma lem2409532 : term928 = True.
Proof. exact (EQ_MP (@lem2409531) (@lem2409529)). Qed.
Lemma lem2409533 : term927 = True.
Proof. exact (TRANS (@lem2409528) (@lem2409532)). Qed.
Lemma lem2409534 : True = term927.
Proof. exact (SYM (@lem2409533)). Qed.
Lemma lem2409535 : term927.
Proof. exact (EQ_MP (@lem2409534) (@lem0)). Qed.
Lemma lem2409536 : term931.
Proof. exact (@lem2409525 (@lem2409535)). Qed.
Lemma lem2409538 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409539 : term927 = term928.
Proof. exact (@lem2409538 (NUMERAL 0) term268). Qed.
Lemma lem2409540 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409541 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409542 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409541 h1) (fun h1 : term928 = True => @lem2409540)). Qed.
Lemma lem2409543 : term928 = True.
Proof. exact (EQ_MP (@lem2409542) (@lem2409540)). Qed.
Lemma lem2409544 : term927 = True.
Proof. exact (TRANS (@lem2409539) (@lem2409543)). Qed.
Lemma lem2409545 : True = term927.
Proof. exact (SYM (@lem2409544)). Qed.
Lemma lem2409546 : term927.
Proof. exact (EQ_MP (@lem2409545) (@lem0)). Qed.
Lemma lem2409547 : term932.
Proof. exact (@lem2409536 (@lem2409546)). Qed.
Lemma lem2409549 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409550 : term902 = term903.
Proof. exact (@lem2409549 term268 term268). Qed.
Lemma lem2409551 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409552 : term905 = term268.
Proof. exact (EQ_MP (@lem2409551) (@lem940073)). Qed.
Lemma lem2409553 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409554 : term903 = term267.
Proof. exact (MK_COMB (@lem2409553) (@lem2409552)). Qed.
Lemma lem2409555 : term902 = term267.
Proof. exact (TRANS (@lem2409550) (@lem2409554)). Qed.
Lemma lem2409557 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409558 : term897 = term908.
Proof. exact (@lem2409557 term268 term268). Qed.
Lemma lem2409559 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409560 : term905 = term268.
Proof. exact (EQ_MP (@lem2409559) (@lem940073)). Qed.
Lemma lem2409561 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409562 : term903 = term267.
Proof. exact (MK_COMB (@lem2409561) (@lem2409560)). Qed.
Lemma lem2409563 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409564 : term908 = term885.
Proof. exact (MK_COMB (@lem2409563) (@lem2409562)). Qed.
Lemma lem2409565 : term897 = term885.
Proof. exact (TRANS (@lem2409558) (@lem2409564)). Qed.
Lemma lem2409566 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409567 : term933 = term921.
Proof. exact (MK_COMB (@lem2409566) (@lem2409565)). Qed.
Lemma lem2409568 : term934 = term923.
Proof. exact (MK_COMB (@lem2409567) (@lem2409555)). Qed.
Lemma lem2409570 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2409571 : term923 = term324.
Proof. exact (@lem2409570 term268). Qed.
Lemma lem2409572 : term934 = term324.
Proof. exact (TRANS (@lem2409568) (@lem2409571)). Qed.
Lemma lem2409573 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409574 : term936 = term444.
Proof. exact (MK_COMB (@lem2409573) (@lem2409572)). Qed.
Lemma lem2409575 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409576 : term937 = term938.
Proof. exact (MK_COMB (@lem2409574) (@lem2409575)). Qed.
Lemma lem2409578 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409579 : term938 = term324.
Proof. exact (@lem2409578 term268). Qed.
Lemma lem2409580 : term937 = term324.
Proof. exact (TRANS (@lem2409576) (@lem2409579)). Qed.
Lemma lem2409582 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409583 : term902 = term903.
Proof. exact (@lem2409582 term268 term268). Qed.
Lemma lem2409584 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409585 : term905 = term268.
Proof. exact (EQ_MP (@lem2409584) (@lem940073)). Qed.
Lemma lem2409586 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409587 : term903 = term267.
Proof. exact (MK_COMB (@lem2409586) (@lem2409585)). Qed.
Lemma lem2409588 : term902 = term267.
Proof. exact (TRANS (@lem2409583) (@lem2409587)). Qed.
Lemma lem2409589 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2409590 : term940 = term938.
Proof. exact (MK_COMB (@lem2409589) (@lem2409588)). Qed.
Lemma lem2409592 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409593 : term938 = term324.
Proof. exact (@lem2409592 term268). Qed.
Lemma lem2409594 : term940 = term324.
Proof. exact (TRANS (@lem2409590) (@lem2409593)). Qed.
Lemma lem2409595 : term324 = term940.
Proof. exact (SYM (@lem2409594)). Qed.
Lemma lem2409596 : term937 = term940.
Proof. exact (TRANS (@lem2409580) (@lem2409595)). Qed.
Lemma lem2409597 : term924 = term941.
Proof. exact (@lem2409547 (@lem2409596)). Qed.
Lemma lem2409598 : term923 = term941.
Proof. exact (TRANS (@lem2409513) (@lem2409597)). Qed.
Lemma lem2409600 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2409601 : term941 = term324.
Proof. exact (@lem2409600 term324). Qed.
Lemma lem2409602 : term923 = term324.
Proof. exact (TRANS (@lem2409598) (@lem2409601)). Qed.
Lemma lem2409603 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409604 : term942 = term444.
Proof. exact (MK_COMB (@lem2409603) (@lem2409602)). Qed.
Lemma lem2409605 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2409606 (y : int) : (term920 y) = (term445 y).
Proof. exact (MK_COMB (@lem2409604) (@lem2409605 y)). Qed.
Lemma lem2409607 (y : int) : (term919 y) = (term445 y).
Proof. exact (TRANS (@lem2409504 y) (@lem2409606 y)). Qed.
Lemma lem2409608 (y : int) : (term445 y) = term324.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2409609 (y : int) : (term919 y) = term324.
Proof. exact (TRANS (@lem2409607 y) (@lem2409608 y)). Qed.
Lemma lem2409610 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409611 (y : int) : (term943 y) = term326.
Proof. exact (MK_COMB (@lem2409610) (@lem2409609 y)). Qed.
Lemma lem2409612 (z : int) : (term946 z) = (term947 z).
Proof. exact (@lem1982763 (real_of_int z) (term918 z) term885). Qed.
Lemma lem2409613 (z : int) : (term919 z) = (term920 z).
Proof. exact (@lem1982715 term885 (real_of_int z)). Qed.
Lemma lem2409615 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409616 : term267 = term891.
Proof. exact (@lem2409615 term268). Qed.
Lemma lem2409618 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409619 : term885 = term894.
Proof. exact (@lem2409618 term268). Qed.
Lemma lem2409620 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409621 : term921 = term922.
Proof. exact (MK_COMB (@lem2409620) (@lem2409619)). Qed.
Lemma lem2409622 : term923 = term924.
Proof. exact (MK_COMB (@lem2409621) (@lem2409616)). Qed.
Lemma lem2409623 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2409625 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409626 : term927 = term928.
Proof. exact (@lem2409625 (NUMERAL 0) term268). Qed.
Lemma lem2409627 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409628 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409629 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409628 h1) (fun h1 : term928 = True => @lem2409627)). Qed.
Lemma lem2409630 : term928 = True.
Proof. exact (EQ_MP (@lem2409629) (@lem2409627)). Qed.
Lemma lem2409631 : term927 = True.
Proof. exact (TRANS (@lem2409626) (@lem2409630)). Qed.
Lemma lem2409632 : True = term927.
Proof. exact (SYM (@lem2409631)). Qed.
Lemma lem2409633 : term927.
Proof. exact (EQ_MP (@lem2409632) (@lem0)). Qed.
Lemma lem2409634 : term930.
Proof. exact (@lem2409623 (@lem2409633)). Qed.
Lemma lem2409636 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409637 : term927 = term928.
Proof. exact (@lem2409636 (NUMERAL 0) term268). Qed.
Lemma lem2409638 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409639 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409640 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409639 h1) (fun h1 : term928 = True => @lem2409638)). Qed.
Lemma lem2409641 : term928 = True.
Proof. exact (EQ_MP (@lem2409640) (@lem2409638)). Qed.
Lemma lem2409642 : term927 = True.
Proof. exact (TRANS (@lem2409637) (@lem2409641)). Qed.
Lemma lem2409643 : True = term927.
Proof. exact (SYM (@lem2409642)). Qed.
Lemma lem2409644 : term927.
Proof. exact (EQ_MP (@lem2409643) (@lem0)). Qed.
Lemma lem2409645 : term931.
Proof. exact (@lem2409634 (@lem2409644)). Qed.
Lemma lem2409647 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409648 : term927 = term928.
Proof. exact (@lem2409647 (NUMERAL 0) term268). Qed.
Lemma lem2409649 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409650 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409651 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409650 h1) (fun h1 : term928 = True => @lem2409649)). Qed.
Lemma lem2409652 : term928 = True.
Proof. exact (EQ_MP (@lem2409651) (@lem2409649)). Qed.
Lemma lem2409653 : term927 = True.
Proof. exact (TRANS (@lem2409648) (@lem2409652)). Qed.
Lemma lem2409654 : True = term927.
Proof. exact (SYM (@lem2409653)). Qed.
Lemma lem2409655 : term927.
Proof. exact (EQ_MP (@lem2409654) (@lem0)). Qed.
Lemma lem2409656 : term932.
Proof. exact (@lem2409645 (@lem2409655)). Qed.
Lemma lem2409658 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409659 : term902 = term903.
Proof. exact (@lem2409658 term268 term268). Qed.
Lemma lem2409660 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409661 : term905 = term268.
Proof. exact (EQ_MP (@lem2409660) (@lem940073)). Qed.
Lemma lem2409662 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409663 : term903 = term267.
Proof. exact (MK_COMB (@lem2409662) (@lem2409661)). Qed.
Lemma lem2409664 : term902 = term267.
Proof. exact (TRANS (@lem2409659) (@lem2409663)). Qed.
Lemma lem2409666 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409667 : term897 = term908.
Proof. exact (@lem2409666 term268 term268). Qed.
Lemma lem2409668 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409669 : term905 = term268.
Proof. exact (EQ_MP (@lem2409668) (@lem940073)). Qed.
Lemma lem2409670 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409671 : term903 = term267.
Proof. exact (MK_COMB (@lem2409670) (@lem2409669)). Qed.
Lemma lem2409672 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409673 : term908 = term885.
Proof. exact (MK_COMB (@lem2409672) (@lem2409671)). Qed.
Lemma lem2409674 : term897 = term885.
Proof. exact (TRANS (@lem2409667) (@lem2409673)). Qed.
Lemma lem2409675 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409676 : term933 = term921.
Proof. exact (MK_COMB (@lem2409675) (@lem2409674)). Qed.
Lemma lem2409677 : term934 = term923.
Proof. exact (MK_COMB (@lem2409676) (@lem2409664)). Qed.
Lemma lem2409679 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2409680 : term923 = term324.
Proof. exact (@lem2409679 term268). Qed.
Lemma lem2409681 : term934 = term324.
Proof. exact (TRANS (@lem2409677) (@lem2409680)). Qed.
Lemma lem2409682 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409683 : term936 = term444.
Proof. exact (MK_COMB (@lem2409682) (@lem2409681)). Qed.
Lemma lem2409684 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409685 : term937 = term938.
Proof. exact (MK_COMB (@lem2409683) (@lem2409684)). Qed.
Lemma lem2409687 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409688 : term938 = term324.
Proof. exact (@lem2409687 term268). Qed.
Lemma lem2409689 : term937 = term324.
Proof. exact (TRANS (@lem2409685) (@lem2409688)). Qed.
Lemma lem2409691 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409692 : term902 = term903.
Proof. exact (@lem2409691 term268 term268). Qed.
Lemma lem2409693 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409694 : term905 = term268.
Proof. exact (EQ_MP (@lem2409693) (@lem940073)). Qed.
Lemma lem2409695 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409696 : term903 = term267.
Proof. exact (MK_COMB (@lem2409695) (@lem2409694)). Qed.
Lemma lem2409697 : term902 = term267.
Proof. exact (TRANS (@lem2409692) (@lem2409696)). Qed.
Lemma lem2409698 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2409699 : term940 = term938.
Proof. exact (MK_COMB (@lem2409698) (@lem2409697)). Qed.
Lemma lem2409701 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409702 : term938 = term324.
Proof. exact (@lem2409701 term268). Qed.
Lemma lem2409703 : term940 = term324.
Proof. exact (TRANS (@lem2409699) (@lem2409702)). Qed.
Lemma lem2409704 : term324 = term940.
Proof. exact (SYM (@lem2409703)). Qed.
Lemma lem2409705 : term937 = term940.
Proof. exact (TRANS (@lem2409689) (@lem2409704)). Qed.
Lemma lem2409706 : term924 = term941.
Proof. exact (@lem2409656 (@lem2409705)). Qed.
Lemma lem2409707 : term923 = term941.
Proof. exact (TRANS (@lem2409622) (@lem2409706)). Qed.
Lemma lem2409709 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2409710 : term941 = term324.
Proof. exact (@lem2409709 term324). Qed.
Lemma lem2409711 : term923 = term324.
Proof. exact (TRANS (@lem2409707) (@lem2409710)). Qed.
Lemma lem2409712 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409713 : term942 = term444.
Proof. exact (MK_COMB (@lem2409712) (@lem2409711)). Qed.
Lemma lem2409714 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2409715 (z : int) : (term920 z) = (term445 z).
Proof. exact (MK_COMB (@lem2409713) (@lem2409714 z)). Qed.
Lemma lem2409716 (z : int) : (term919 z) = (term445 z).
Proof. exact (TRANS (@lem2409613 z) (@lem2409715 z)). Qed.
Lemma lem2409717 (z : int) : (term445 z) = term324.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem2409718 (z : int) : (term919 z) = term324.
Proof. exact (TRANS (@lem2409716 z) (@lem2409717 z)). Qed.
Lemma lem2409719 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409720 (z : int) : (term943 z) = term326.
Proof. exact (MK_COMB (@lem2409719) (@lem2409718 z)). Qed.
Lemma lem2409721 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2409722 (z : int) : (term947 z) = term948.
Proof. exact (MK_COMB (@lem2409720 z) (@lem2409721)). Qed.
Lemma lem2409723 (z : int) : (term946 z) = term948.
Proof. exact (TRANS (@lem2409612 z) (@lem2409722 z)). Qed.
Lemma lem2409724 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2409725 (z : int) : (term946 z) = term885.
Proof. exact (TRANS (@lem2409723 z) (@lem2409724)). Qed.
Lemma lem2409726 (y : int) (z : int) : (term945 y z) = term948.
Proof. exact (MK_COMB (@lem2409611 y) (@lem2409725 z)). Qed.
Lemma lem2409727 (y : int) (z : int) : (term944 y z) = term948.
Proof. exact (TRANS (@lem2409503 y z) (@lem2409726 y z)). Qed.
Lemma lem2409728 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2409729 (y : int) (z : int) : (term944 y z) = term885.
Proof. exact (TRANS (@lem2409727 y z) (@lem2409728)). Qed.
Lemma lem2409730 (x : int) (y : int) (z : int) : (term917 x y z) = term948.
Proof. exact (MK_COMB (@lem2409502 x) (@lem2409729 y z)). Qed.
Lemma lem2409731 (x : int) (y : int) (z : int) : (term916 x y z) = term948.
Proof. exact (TRANS (@lem2409394 x y z) (@lem2409730 x y z)). Qed.
Lemma lem2409732 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2409733 (x : int) (y : int) (z : int) : (term916 x y z) = term885.
Proof. exact (TRANS (@lem2409731 x y z) (@lem2409732)). Qed.
Lemma lem2409734 (x : int) (y : int) (z : int) : (term882 x y z) = term885.
Proof. exact (TRANS (@lem2409393 x y z) (@lem2409733 x y z)). Qed.
Lemma lem2409735 (x : int) (y : int) (z : int) : (term881 x y z) = term885.
Proof. exact (TRANS (@lem2409336 x y z) (@lem2409734 x y z)). Qed.
Lemma lem2409736 (x : int) (y : int) (z : int) : (term959 x y z) = term885.
Proof. exact (TRANS (@lem2409335 x y z) (@lem2409735 x y z)). Qed.
Lemma lem2409737 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2409738 (x : int) (y : int) (z : int) : (term960 x y z) = term950.
Proof. exact (MK_COMB (@lem2409737) (@lem2409736 x y z)). Qed.
Lemma lem2409739 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2409740 (x : int) (y : int) (z : int) : (term958 x y z) = term951.
Proof. exact (MK_COMB (@lem2409738 x y z) (@lem2409739)). Qed.
Lemma lem2409741 (x : int) (y : int) (z : int) : (term290 x y z) = term951.
Proof. exact (TRANS (@lem2409288 x y z) (@lem2409740 x y z)). Qed.
Lemma lem2409742 (x : int) (y : int) : (term527 x y) = term952.
Proof. exact (fun_ext (fun z : int => @lem2409741 x y z)). Qed.
Lemma lem2409743 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2409744 (x : int) (y : int) : (term542 x y) = term953.
Proof. exact (MK_COMB (@lem2409743) (@lem2409742 x y)). Qed.
Lemma lem2409745 (x : int) : (term549 x) = term954.
Proof. exact (fun_ext (fun y : int => @lem2409744 x y)). Qed.
Lemma lem2409746 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2409747 (x : int) : (term564 x) = term955.
Proof. exact (MK_COMB (@lem2409746) (@lem2409745 x)). Qed.
Lemma lem2409748 : term571 = term956.
Proof. exact (fun_ext (fun x : int => @lem2409747 x)). Qed.
Lemma lem2409749 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2409750 : term586 = term957.
Proof. exact (MK_COMB (@lem2409749) (@lem2409748)). Qed.
Lemma lem2409751 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2409752 : term583 = term961.
Proof. exact (MK_COMB (@lem2409751) (@lem2409287)). Qed.
Lemma lem2409753 : term587 = term962.
Proof. exact (MK_COMB (@lem2409752) (@lem2409750)). Qed.
Lemma lem2409754 (x : int) (y : int) : (term307 y x) = (term963 x y).
Proof. exact (@lem1988287 (term256 y x) (term304 x y)). Qed.
Lemma lem2409771 (x : int) (y : int) : (term304 x y) = (term876 x y).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) term267). Qed.
Lemma lem2409778 (x : int) (y : int) : (term256 y x) = (term256 x y).
Proof. exact (@lem1982761 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2409779 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2409780 (x : int) (y : int) : (term964 y x) = (term964 x y).
Proof. exact (MK_COMB (@lem2409779) (@lem2409778 x y)). Qed.
Lemma lem2409781 (x : int) (y : int) : (term965 x y) = (term966 x y).
Proof. exact (MK_COMB (@lem2409780 x y) (@lem2409771 x y)). Qed.
Lemma lem2409782 (x : int) (y : int) : (term966 x y) = (term967 x y).
Proof. exact (@lem1982792 (term256 x y) (term876 x y)). Qed.
Lemma lem2409783 (x : int) (y : int) : (term886 x y) = (term887 x y).
Proof. exact (@lem1982781 (real_of_int x) term885 (term341 y)). Qed.
Lemma lem2409784 (y : int) : (term888 y) = (term889 y).
Proof. exact (@lem1982781 (real_of_int y) term885 term267). Qed.
Lemma lem2409786 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409787 : term267 = term891.
Proof. exact (@lem2409786 term268). Qed.
Lemma lem2409789 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409790 : term885 = term894.
Proof. exact (@lem2409789 term268). Qed.
Lemma lem2409791 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409792 : term895 = term896.
Proof. exact (MK_COMB (@lem2409791) (@lem2409790)). Qed.
Lemma lem2409793 : term897 = term898.
Proof. exact (MK_COMB (@lem2409792) (@lem2409787)). Qed.
Lemma lem2409794 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2409796 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409797 : term902 = term903.
Proof. exact (@lem2409796 term268 term268). Qed.
Lemma lem2409798 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409799 : term905 = term268.
Proof. exact (EQ_MP (@lem2409798) (@lem940073)). Qed.
Lemma lem2409800 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409801 : term903 = term267.
Proof. exact (MK_COMB (@lem2409800) (@lem2409799)). Qed.
Lemma lem2409802 : term902 = term267.
Proof. exact (TRANS (@lem2409797) (@lem2409801)). Qed.
Lemma lem2409804 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409805 : term897 = term908.
Proof. exact (@lem2409804 term268 term268). Qed.
Lemma lem2409806 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409807 : term905 = term268.
Proof. exact (EQ_MP (@lem2409806) (@lem940073)). Qed.
Lemma lem2409808 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409809 : term903 = term267.
Proof. exact (MK_COMB (@lem2409808) (@lem2409807)). Qed.
Lemma lem2409810 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409811 : term908 = term885.
Proof. exact (MK_COMB (@lem2409810) (@lem2409809)). Qed.
Lemma lem2409812 : term897 = term885.
Proof. exact (TRANS (@lem2409805) (@lem2409811)). Qed.
Lemma lem2409813 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2409814 : term909 = term910.
Proof. exact (MK_COMB (@lem2409813) (@lem2409812)). Qed.
Lemma lem2409815 : term899 = term894.
Proof. exact (MK_COMB (@lem2409814) (@lem2409802)). Qed.
Lemma lem2409816 : term898 = term894.
Proof. exact (TRANS (@lem2409794) (@lem2409815)). Qed.
Lemma lem2409817 : term897 = term894.
Proof. exact (TRANS (@lem2409793) (@lem2409816)). Qed.
Lemma lem2409819 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2409820 : term894 = term885.
Proof. exact (@lem2409819 term885). Qed.
Lemma lem2409821 : term897 = term885.
Proof. exact (TRANS (@lem2409817) (@lem2409820)). Qed.
Lemma lem2409824 (y : int) : (term912 y) = (term912 y).
Proof. exact (eq_refl (term912 y)). Qed.
Lemma lem2409825 (y : int) : (term889 y) = (term913 y).
Proof. exact (MK_COMB (@lem2409824 y) (@lem2409821)). Qed.
Lemma lem2409826 (y : int) : (term888 y) = (term913 y).
Proof. exact (TRANS (@lem2409784 y) (@lem2409825 y)). Qed.
Lemma lem2409829 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2409830 (x : int) (y : int) : (term887 x y) = (term914 x y).
Proof. exact (MK_COMB (@lem2409829 x) (@lem2409826 y)). Qed.
Lemma lem2409831 (x : int) (y : int) : (term886 x y) = (term914 x y).
Proof. exact (TRANS (@lem2409783 x y) (@lem2409830 x y)). Qed.
Lemma lem2409832 (x : int) (y : int) : (term275 x y) = (term275 x y).
Proof. exact (eq_refl (term275 x y)). Qed.
Lemma lem2409833 (x : int) (y : int) : (term967 x y) = (term944 x y).
Proof. exact (MK_COMB (@lem2409832 x y) (@lem2409831 x y)). Qed.
Lemma lem2409834 (x : int) (y : int) : (term944 x y) = (term945 x y).
Proof. exact (@lem1982753 (real_of_int x) (term918 x) (real_of_int y) (term913 y)). Qed.
Lemma lem2409835 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2409837 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409838 : term267 = term891.
Proof. exact (@lem2409837 term268). Qed.
Lemma lem2409840 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409841 : term885 = term894.
Proof. exact (@lem2409840 term268). Qed.
Lemma lem2409842 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409843 : term921 = term922.
Proof. exact (MK_COMB (@lem2409842) (@lem2409841)). Qed.
Lemma lem2409844 : term923 = term924.
Proof. exact (MK_COMB (@lem2409843) (@lem2409838)). Qed.
Lemma lem2409845 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2409847 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409848 : term927 = term928.
Proof. exact (@lem2409847 (NUMERAL 0) term268). Qed.
Lemma lem2409849 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409850 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409851 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409850 h1) (fun h1 : term928 = True => @lem2409849)). Qed.
Lemma lem2409852 : term928 = True.
Proof. exact (EQ_MP (@lem2409851) (@lem2409849)). Qed.
Lemma lem2409853 : term927 = True.
Proof. exact (TRANS (@lem2409848) (@lem2409852)). Qed.
Lemma lem2409854 : True = term927.
Proof. exact (SYM (@lem2409853)). Qed.
Lemma lem2409855 : term927.
Proof. exact (EQ_MP (@lem2409854) (@lem0)). Qed.
Lemma lem2409856 : term930.
Proof. exact (@lem2409845 (@lem2409855)). Qed.
Lemma lem2409858 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409859 : term927 = term928.
Proof. exact (@lem2409858 (NUMERAL 0) term268). Qed.
Lemma lem2409860 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409861 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409862 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409861 h1) (fun h1 : term928 = True => @lem2409860)). Qed.
Lemma lem2409863 : term928 = True.
Proof. exact (EQ_MP (@lem2409862) (@lem2409860)). Qed.
Lemma lem2409864 : term927 = True.
Proof. exact (TRANS (@lem2409859) (@lem2409863)). Qed.
Lemma lem2409865 : True = term927.
Proof. exact (SYM (@lem2409864)). Qed.
Lemma lem2409866 : term927.
Proof. exact (EQ_MP (@lem2409865) (@lem0)). Qed.
Lemma lem2409867 : term931.
Proof. exact (@lem2409856 (@lem2409866)). Qed.
Lemma lem2409869 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409870 : term927 = term928.
Proof. exact (@lem2409869 (NUMERAL 0) term268). Qed.
Lemma lem2409871 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409872 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409873 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409872 h1) (fun h1 : term928 = True => @lem2409871)). Qed.
Lemma lem2409874 : term928 = True.
Proof. exact (EQ_MP (@lem2409873) (@lem2409871)). Qed.
Lemma lem2409875 : term927 = True.
Proof. exact (TRANS (@lem2409870) (@lem2409874)). Qed.
Lemma lem2409876 : True = term927.
Proof. exact (SYM (@lem2409875)). Qed.
Lemma lem2409877 : term927.
Proof. exact (EQ_MP (@lem2409876) (@lem0)). Qed.
Lemma lem2409878 : term932.
Proof. exact (@lem2409867 (@lem2409877)). Qed.
Lemma lem2409880 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409881 : term902 = term903.
Proof. exact (@lem2409880 term268 term268). Qed.
Lemma lem2409882 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409883 : term905 = term268.
Proof. exact (EQ_MP (@lem2409882) (@lem940073)). Qed.
Lemma lem2409884 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409885 : term903 = term267.
Proof. exact (MK_COMB (@lem2409884) (@lem2409883)). Qed.
Lemma lem2409886 : term902 = term267.
Proof. exact (TRANS (@lem2409881) (@lem2409885)). Qed.
Lemma lem2409888 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409889 : term897 = term908.
Proof. exact (@lem2409888 term268 term268). Qed.
Lemma lem2409890 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409891 : term905 = term268.
Proof. exact (EQ_MP (@lem2409890) (@lem940073)). Qed.
Lemma lem2409892 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409893 : term903 = term267.
Proof. exact (MK_COMB (@lem2409892) (@lem2409891)). Qed.
Lemma lem2409894 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2409895 : term908 = term885.
Proof. exact (MK_COMB (@lem2409894) (@lem2409893)). Qed.
Lemma lem2409896 : term897 = term885.
Proof. exact (TRANS (@lem2409889) (@lem2409895)). Qed.
Lemma lem2409897 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409898 : term933 = term921.
Proof. exact (MK_COMB (@lem2409897) (@lem2409896)). Qed.
Lemma lem2409899 : term934 = term923.
Proof. exact (MK_COMB (@lem2409898) (@lem2409886)). Qed.
Lemma lem2409901 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2409902 : term923 = term324.
Proof. exact (@lem2409901 term268). Qed.
Lemma lem2409903 : term934 = term324.
Proof. exact (TRANS (@lem2409899) (@lem2409902)). Qed.
Lemma lem2409904 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409905 : term936 = term444.
Proof. exact (MK_COMB (@lem2409904) (@lem2409903)). Qed.
Lemma lem2409906 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2409907 : term937 = term938.
Proof. exact (MK_COMB (@lem2409905) (@lem2409906)). Qed.
Lemma lem2409909 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409910 : term938 = term324.
Proof. exact (@lem2409909 term268). Qed.
Lemma lem2409911 : term937 = term324.
Proof. exact (TRANS (@lem2409907) (@lem2409910)). Qed.
Lemma lem2409913 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409914 : term902 = term903.
Proof. exact (@lem2409913 term268 term268). Qed.
Lemma lem2409915 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409916 : term905 = term268.
Proof. exact (EQ_MP (@lem2409915) (@lem940073)). Qed.
Lemma lem2409917 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409918 : term903 = term267.
Proof. exact (MK_COMB (@lem2409917) (@lem2409916)). Qed.
Lemma lem2409919 : term902 = term267.
Proof. exact (TRANS (@lem2409914) (@lem2409918)). Qed.
Lemma lem2409920 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2409921 : term940 = term938.
Proof. exact (MK_COMB (@lem2409920) (@lem2409919)). Qed.
Lemma lem2409923 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2409924 : term938 = term324.
Proof. exact (@lem2409923 term268). Qed.
Lemma lem2409925 : term940 = term324.
Proof. exact (TRANS (@lem2409921) (@lem2409924)). Qed.
Lemma lem2409926 : term324 = term940.
Proof. exact (SYM (@lem2409925)). Qed.
Lemma lem2409927 : term937 = term940.
Proof. exact (TRANS (@lem2409911) (@lem2409926)). Qed.
Lemma lem2409928 : term924 = term941.
Proof. exact (@lem2409878 (@lem2409927)). Qed.
Lemma lem2409929 : term923 = term941.
Proof. exact (TRANS (@lem2409844) (@lem2409928)). Qed.
Lemma lem2409931 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2409932 : term941 = term324.
Proof. exact (@lem2409931 term324). Qed.
Lemma lem2409933 : term923 = term324.
Proof. exact (TRANS (@lem2409929) (@lem2409932)). Qed.
Lemma lem2409934 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2409935 : term942 = term444.
Proof. exact (MK_COMB (@lem2409934) (@lem2409933)). Qed.
Lemma lem2409936 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2409937 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2409935) (@lem2409936 x)). Qed.
Lemma lem2409938 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2409835 x) (@lem2409937 x)). Qed.
Lemma lem2409939 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2409940 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2409938 x) (@lem2409939 x)). Qed.
Lemma lem2409941 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409942 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2409941) (@lem2409940 x)). Qed.
Lemma lem2409943 (y : int) : (term946 y) = (term947 y).
Proof. exact (@lem1982763 (real_of_int y) (term918 y) term885). Qed.
Lemma lem2409944 (y : int) : (term919 y) = (term920 y).
Proof. exact (@lem1982715 term885 (real_of_int y)). Qed.
Lemma lem2409946 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2409947 : term267 = term891.
Proof. exact (@lem2409946 term268). Qed.
Lemma lem2409949 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2409950 : term885 = term894.
Proof. exact (@lem2409949 term268). Qed.
Lemma lem2409951 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2409952 : term921 = term922.
Proof. exact (MK_COMB (@lem2409951) (@lem2409950)). Qed.
Lemma lem2409953 : term923 = term924.
Proof. exact (MK_COMB (@lem2409952) (@lem2409947)). Qed.
Lemma lem2409954 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2409956 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409957 : term927 = term928.
Proof. exact (@lem2409956 (NUMERAL 0) term268). Qed.
Lemma lem2409958 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409959 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409960 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409959 h1) (fun h1 : term928 = True => @lem2409958)). Qed.
Lemma lem2409961 : term928 = True.
Proof. exact (EQ_MP (@lem2409960) (@lem2409958)). Qed.
Lemma lem2409962 : term927 = True.
Proof. exact (TRANS (@lem2409957) (@lem2409961)). Qed.
Lemma lem2409963 : True = term927.
Proof. exact (SYM (@lem2409962)). Qed.
Lemma lem2409964 : term927.
Proof. exact (EQ_MP (@lem2409963) (@lem0)). Qed.
Lemma lem2409965 : term930.
Proof. exact (@lem2409954 (@lem2409964)). Qed.
Lemma lem2409967 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409968 : term927 = term928.
Proof. exact (@lem2409967 (NUMERAL 0) term268). Qed.
Lemma lem2409969 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409970 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409971 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409970 h1) (fun h1 : term928 = True => @lem2409969)). Qed.
Lemma lem2409972 : term928 = True.
Proof. exact (EQ_MP (@lem2409971) (@lem2409969)). Qed.
Lemma lem2409973 : term927 = True.
Proof. exact (TRANS (@lem2409968) (@lem2409972)). Qed.
Lemma lem2409974 : True = term927.
Proof. exact (SYM (@lem2409973)). Qed.
Lemma lem2409975 : term927.
Proof. exact (EQ_MP (@lem2409974) (@lem0)). Qed.
Lemma lem2409976 : term931.
Proof. exact (@lem2409965 (@lem2409975)). Qed.
Lemma lem2409978 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2409979 : term927 = term928.
Proof. exact (@lem2409978 (NUMERAL 0) term268). Qed.
Lemma lem2409980 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2409981 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2409982 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2409981 h1) (fun h1 : term928 = True => @lem2409980)). Qed.
Lemma lem2409983 : term928 = True.
Proof. exact (EQ_MP (@lem2409982) (@lem2409980)). Qed.
Lemma lem2409984 : term927 = True.
Proof. exact (TRANS (@lem2409979) (@lem2409983)). Qed.
Lemma lem2409985 : True = term927.
Proof. exact (SYM (@lem2409984)). Qed.
Lemma lem2409986 : term927.
Proof. exact (EQ_MP (@lem2409985) (@lem0)). Qed.
Lemma lem2409987 : term932.
Proof. exact (@lem2409976 (@lem2409986)). Qed.
Lemma lem2409989 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2409990 : term902 = term903.
Proof. exact (@lem2409989 term268 term268). Qed.
Lemma lem2409991 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2409992 : term905 = term268.
Proof. exact (EQ_MP (@lem2409991) (@lem940073)). Qed.
Lemma lem2409993 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2409994 : term903 = term267.
Proof. exact (MK_COMB (@lem2409993) (@lem2409992)). Qed.
Lemma lem2409995 : term902 = term267.
Proof. exact (TRANS (@lem2409990) (@lem2409994)). Qed.
Lemma lem2409997 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2409998 : term897 = term908.
Proof. exact (@lem2409997 term268 term268). Qed.
Lemma lem2409999 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410000 : term905 = term268.
Proof. exact (EQ_MP (@lem2409999) (@lem940073)). Qed.
Lemma lem2410001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410002 : term903 = term267.
Proof. exact (MK_COMB (@lem2410001) (@lem2410000)). Qed.
Lemma lem2410003 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410004 : term908 = term885.
Proof. exact (MK_COMB (@lem2410003) (@lem2410002)). Qed.
Lemma lem2410005 : term897 = term885.
Proof. exact (TRANS (@lem2409998) (@lem2410004)). Qed.
Lemma lem2410006 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410007 : term933 = term921.
Proof. exact (MK_COMB (@lem2410006) (@lem2410005)). Qed.
Lemma lem2410008 : term934 = term923.
Proof. exact (MK_COMB (@lem2410007) (@lem2409995)). Qed.
Lemma lem2410010 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2410011 : term923 = term324.
Proof. exact (@lem2410010 term268). Qed.
Lemma lem2410012 : term934 = term324.
Proof. exact (TRANS (@lem2410008) (@lem2410011)). Qed.
Lemma lem2410013 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410014 : term936 = term444.
Proof. exact (MK_COMB (@lem2410013) (@lem2410012)). Qed.
Lemma lem2410015 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410016 : term937 = term938.
Proof. exact (MK_COMB (@lem2410014) (@lem2410015)). Qed.
Lemma lem2410018 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410019 : term938 = term324.
Proof. exact (@lem2410018 term268). Qed.
Lemma lem2410020 : term937 = term324.
Proof. exact (TRANS (@lem2410016) (@lem2410019)). Qed.
Lemma lem2410022 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410023 : term902 = term903.
Proof. exact (@lem2410022 term268 term268). Qed.
Lemma lem2410024 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410025 : term905 = term268.
Proof. exact (EQ_MP (@lem2410024) (@lem940073)). Qed.
Lemma lem2410026 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410027 : term903 = term267.
Proof. exact (MK_COMB (@lem2410026) (@lem2410025)). Qed.
Lemma lem2410028 : term902 = term267.
Proof. exact (TRANS (@lem2410023) (@lem2410027)). Qed.
Lemma lem2410029 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2410030 : term940 = term938.
Proof. exact (MK_COMB (@lem2410029) (@lem2410028)). Qed.
Lemma lem2410032 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410033 : term938 = term324.
Proof. exact (@lem2410032 term268). Qed.
Lemma lem2410034 : term940 = term324.
Proof. exact (TRANS (@lem2410030) (@lem2410033)). Qed.
Lemma lem2410035 : term324 = term940.
Proof. exact (SYM (@lem2410034)). Qed.
Lemma lem2410036 : term937 = term940.
Proof. exact (TRANS (@lem2410020) (@lem2410035)). Qed.
Lemma lem2410037 : term924 = term941.
Proof. exact (@lem2409987 (@lem2410036)). Qed.
Lemma lem2410038 : term923 = term941.
Proof. exact (TRANS (@lem2409953) (@lem2410037)). Qed.
Lemma lem2410040 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2410041 : term941 = term324.
Proof. exact (@lem2410040 term324). Qed.
Lemma lem2410042 : term923 = term324.
Proof. exact (TRANS (@lem2410038) (@lem2410041)). Qed.
Lemma lem2410043 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410044 : term942 = term444.
Proof. exact (MK_COMB (@lem2410043) (@lem2410042)). Qed.
Lemma lem2410045 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2410046 (y : int) : (term920 y) = (term445 y).
Proof. exact (MK_COMB (@lem2410044) (@lem2410045 y)). Qed.
Lemma lem2410047 (y : int) : (term919 y) = (term445 y).
Proof. exact (TRANS (@lem2409944 y) (@lem2410046 y)). Qed.
Lemma lem2410048 (y : int) : (term445 y) = term324.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2410049 (y : int) : (term919 y) = term324.
Proof. exact (TRANS (@lem2410047 y) (@lem2410048 y)). Qed.
Lemma lem2410050 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410051 (y : int) : (term943 y) = term326.
Proof. exact (MK_COMB (@lem2410050) (@lem2410049 y)). Qed.
Lemma lem2410052 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2410053 (y : int) : (term947 y) = term948.
Proof. exact (MK_COMB (@lem2410051 y) (@lem2410052)). Qed.
Lemma lem2410054 (y : int) : (term946 y) = term948.
Proof. exact (TRANS (@lem2409943 y) (@lem2410053 y)). Qed.
Lemma lem2410055 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2410056 (y : int) : (term946 y) = term885.
Proof. exact (TRANS (@lem2410054 y) (@lem2410055)). Qed.
Lemma lem2410057 (x : int) (y : int) : (term945 x y) = term948.
Proof. exact (MK_COMB (@lem2409942 x) (@lem2410056 y)). Qed.
Lemma lem2410058 (x : int) (y : int) : (term944 x y) = term948.
Proof. exact (TRANS (@lem2409834 x y) (@lem2410057 x y)). Qed.
Lemma lem2410059 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2410060 (x : int) (y : int) : (term944 x y) = term885.
Proof. exact (TRANS (@lem2410058 x y) (@lem2410059)). Qed.
Lemma lem2410061 (x : int) (y : int) : (term967 x y) = term885.
Proof. exact (TRANS (@lem2409833 x y) (@lem2410060 x y)). Qed.
Lemma lem2410062 (x : int) (y : int) : (term966 x y) = term885.
Proof. exact (TRANS (@lem2409782 x y) (@lem2410061 x y)). Qed.
Lemma lem2410063 (x : int) (y : int) : (term965 x y) = term885.
Proof. exact (TRANS (@lem2409781 x y) (@lem2410062 x y)). Qed.
Lemma lem2410064 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2410065 (x : int) (y : int) : (term968 x y) = term950.
Proof. exact (MK_COMB (@lem2410064) (@lem2410063 x y)). Qed.
Lemma lem2410066 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2410067 (x : int) (y : int) : (term963 x y) = term951.
Proof. exact (MK_COMB (@lem2410065 x y) (@lem2410066)). Qed.
Lemma lem2410068 (y : int) (x : int) : (term307 y x) = term951.
Proof. exact (TRANS (@lem2409754 x y) (@lem2410067 x y)). Qed.
Lemma lem2410069 (x : int) : (term591 x) = term952.
Proof. exact (fun_ext (fun y : int => @lem2410068 y x)). Qed.
Lemma lem2410070 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410071 (x : int) : (term602 x) = term953.
Proof. exact (MK_COMB (@lem2410070) (@lem2410069 x)). Qed.
Lemma lem2410072 : term613 = term954.
Proof. exact (fun_ext (fun x : int => @lem2410071 x)). Qed.
Lemma lem2410073 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410074 : term624 = term955.
Proof. exact (MK_COMB (@lem2410073) (@lem2410072)). Qed.
Lemma lem2410075 (y : int) (x : int) : (term307 x y) = (term963 y x).
Proof. exact (@lem1988287 (term256 x y) (term304 y x)). Qed.
Lemma lem2410076 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410083 (x : int) (y : int) : (term256 y x) = (term256 x y).
Proof. exact (@lem1982761 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2410084 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410085 (x : int) (y : int) : (term275 y x) = (term275 x y).
Proof. exact (MK_COMB (@lem2410084) (@lem2410083 x y)). Qed.
Lemma lem2410086 (x : int) (y : int) : (term304 y x) = (term304 x y).
Proof. exact (MK_COMB (@lem2410085 x y) (@lem2410076)). Qed.
Lemma lem2410091 (x : int) (y : int) : (term304 x y) = (term876 x y).
Proof. exact (@lem1982755 (real_of_int x) (real_of_int y) term267). Qed.
Lemma lem2410092 (x : int) (y : int) : (term304 y x) = (term876 x y).
Proof. exact (TRANS (@lem2410086 x y) (@lem2410091 x y)). Qed.
Lemma lem2410101 (x : int) (y : int) : (term964 x y) = (term964 x y).
Proof. exact (eq_refl (term964 x y)). Qed.
Lemma lem2410102 (x : int) (y : int) : (term965 y x) = (term966 x y).
Proof. exact (MK_COMB (@lem2410101 x y) (@lem2410092 x y)). Qed.
Lemma lem2410103 (x : int) (y : int) : (term966 x y) = (term967 x y).
Proof. exact (@lem1982792 (term256 x y) (term876 x y)). Qed.
Lemma lem2410104 (x : int) (y : int) : (term886 x y) = (term887 x y).
Proof. exact (@lem1982781 (real_of_int x) term885 (term341 y)). Qed.
Lemma lem2410105 (y : int) : (term888 y) = (term889 y).
Proof. exact (@lem1982781 (real_of_int y) term885 term267). Qed.
Lemma lem2410107 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410108 : term267 = term891.
Proof. exact (@lem2410107 term268). Qed.
Lemma lem2410110 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410111 : term885 = term894.
Proof. exact (@lem2410110 term268). Qed.
Lemma lem2410112 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410113 : term895 = term896.
Proof. exact (MK_COMB (@lem2410112) (@lem2410111)). Qed.
Lemma lem2410114 : term897 = term898.
Proof. exact (MK_COMB (@lem2410113) (@lem2410108)). Qed.
Lemma lem2410115 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2410117 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410118 : term902 = term903.
Proof. exact (@lem2410117 term268 term268). Qed.
Lemma lem2410119 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410120 : term905 = term268.
Proof. exact (EQ_MP (@lem2410119) (@lem940073)). Qed.
Lemma lem2410121 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410122 : term903 = term267.
Proof. exact (MK_COMB (@lem2410121) (@lem2410120)). Qed.
Lemma lem2410123 : term902 = term267.
Proof. exact (TRANS (@lem2410118) (@lem2410122)). Qed.
Lemma lem2410125 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410126 : term897 = term908.
Proof. exact (@lem2410125 term268 term268). Qed.
Lemma lem2410127 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410128 : term905 = term268.
Proof. exact (EQ_MP (@lem2410127) (@lem940073)). Qed.
Lemma lem2410129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410130 : term903 = term267.
Proof. exact (MK_COMB (@lem2410129) (@lem2410128)). Qed.
Lemma lem2410131 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410132 : term908 = term885.
Proof. exact (MK_COMB (@lem2410131) (@lem2410130)). Qed.
Lemma lem2410133 : term897 = term885.
Proof. exact (TRANS (@lem2410126) (@lem2410132)). Qed.
Lemma lem2410134 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2410135 : term909 = term910.
Proof. exact (MK_COMB (@lem2410134) (@lem2410133)). Qed.
Lemma lem2410136 : term899 = term894.
Proof. exact (MK_COMB (@lem2410135) (@lem2410123)). Qed.
Lemma lem2410137 : term898 = term894.
Proof. exact (TRANS (@lem2410115) (@lem2410136)). Qed.
Lemma lem2410138 : term897 = term894.
Proof. exact (TRANS (@lem2410114) (@lem2410137)). Qed.
Lemma lem2410140 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2410141 : term894 = term885.
Proof. exact (@lem2410140 term885). Qed.
Lemma lem2410142 : term897 = term885.
Proof. exact (TRANS (@lem2410138) (@lem2410141)). Qed.
Lemma lem2410145 (y : int) : (term912 y) = (term912 y).
Proof. exact (eq_refl (term912 y)). Qed.
Lemma lem2410146 (y : int) : (term889 y) = (term913 y).
Proof. exact (MK_COMB (@lem2410145 y) (@lem2410142)). Qed.
Lemma lem2410147 (y : int) : (term888 y) = (term913 y).
Proof. exact (TRANS (@lem2410105 y) (@lem2410146 y)). Qed.
Lemma lem2410150 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2410151 (x : int) (y : int) : (term887 x y) = (term914 x y).
Proof. exact (MK_COMB (@lem2410150 x) (@lem2410147 y)). Qed.
Lemma lem2410152 (x : int) (y : int) : (term886 x y) = (term914 x y).
Proof. exact (TRANS (@lem2410104 x y) (@lem2410151 x y)). Qed.
Lemma lem2410153 (x : int) (y : int) : (term275 x y) = (term275 x y).
Proof. exact (eq_refl (term275 x y)). Qed.
Lemma lem2410154 (x : int) (y : int) : (term967 x y) = (term944 x y).
Proof. exact (MK_COMB (@lem2410153 x y) (@lem2410152 x y)). Qed.
Lemma lem2410155 (x : int) (y : int) : (term944 x y) = (term945 x y).
Proof. exact (@lem1982753 (real_of_int x) (term918 x) (real_of_int y) (term913 y)). Qed.
Lemma lem2410156 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2410158 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410159 : term267 = term891.
Proof. exact (@lem2410158 term268). Qed.
Lemma lem2410161 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410162 : term885 = term894.
Proof. exact (@lem2410161 term268). Qed.
Lemma lem2410163 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410164 : term921 = term922.
Proof. exact (MK_COMB (@lem2410163) (@lem2410162)). Qed.
Lemma lem2410165 : term923 = term924.
Proof. exact (MK_COMB (@lem2410164) (@lem2410159)). Qed.
Lemma lem2410166 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2410168 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410169 : term927 = term928.
Proof. exact (@lem2410168 (NUMERAL 0) term268). Qed.
Lemma lem2410170 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410171 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410172 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410171 h1) (fun h1 : term928 = True => @lem2410170)). Qed.
Lemma lem2410173 : term928 = True.
Proof. exact (EQ_MP (@lem2410172) (@lem2410170)). Qed.
Lemma lem2410174 : term927 = True.
Proof. exact (TRANS (@lem2410169) (@lem2410173)). Qed.
Lemma lem2410175 : True = term927.
Proof. exact (SYM (@lem2410174)). Qed.
Lemma lem2410176 : term927.
Proof. exact (EQ_MP (@lem2410175) (@lem0)). Qed.
Lemma lem2410177 : term930.
Proof. exact (@lem2410166 (@lem2410176)). Qed.
Lemma lem2410179 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410180 : term927 = term928.
Proof. exact (@lem2410179 (NUMERAL 0) term268). Qed.
Lemma lem2410181 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410182 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410183 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410182 h1) (fun h1 : term928 = True => @lem2410181)). Qed.
Lemma lem2410184 : term928 = True.
Proof. exact (EQ_MP (@lem2410183) (@lem2410181)). Qed.
Lemma lem2410185 : term927 = True.
Proof. exact (TRANS (@lem2410180) (@lem2410184)). Qed.
Lemma lem2410186 : True = term927.
Proof. exact (SYM (@lem2410185)). Qed.
Lemma lem2410187 : term927.
Proof. exact (EQ_MP (@lem2410186) (@lem0)). Qed.
Lemma lem2410188 : term931.
Proof. exact (@lem2410177 (@lem2410187)). Qed.
Lemma lem2410190 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410191 : term927 = term928.
Proof. exact (@lem2410190 (NUMERAL 0) term268). Qed.
Lemma lem2410192 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410193 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410194 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410193 h1) (fun h1 : term928 = True => @lem2410192)). Qed.
Lemma lem2410195 : term928 = True.
Proof. exact (EQ_MP (@lem2410194) (@lem2410192)). Qed.
Lemma lem2410196 : term927 = True.
Proof. exact (TRANS (@lem2410191) (@lem2410195)). Qed.
Lemma lem2410197 : True = term927.
Proof. exact (SYM (@lem2410196)). Qed.
Lemma lem2410198 : term927.
Proof. exact (EQ_MP (@lem2410197) (@lem0)). Qed.
Lemma lem2410199 : term932.
Proof. exact (@lem2410188 (@lem2410198)). Qed.
Lemma lem2410201 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410202 : term902 = term903.
Proof. exact (@lem2410201 term268 term268). Qed.
Lemma lem2410203 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410204 : term905 = term268.
Proof. exact (EQ_MP (@lem2410203) (@lem940073)). Qed.
Lemma lem2410205 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410206 : term903 = term267.
Proof. exact (MK_COMB (@lem2410205) (@lem2410204)). Qed.
Lemma lem2410207 : term902 = term267.
Proof. exact (TRANS (@lem2410202) (@lem2410206)). Qed.
Lemma lem2410209 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410210 : term897 = term908.
Proof. exact (@lem2410209 term268 term268). Qed.
Lemma lem2410211 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410212 : term905 = term268.
Proof. exact (EQ_MP (@lem2410211) (@lem940073)). Qed.
Lemma lem2410213 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410214 : term903 = term267.
Proof. exact (MK_COMB (@lem2410213) (@lem2410212)). Qed.
Lemma lem2410215 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410216 : term908 = term885.
Proof. exact (MK_COMB (@lem2410215) (@lem2410214)). Qed.
Lemma lem2410217 : term897 = term885.
Proof. exact (TRANS (@lem2410210) (@lem2410216)). Qed.
Lemma lem2410218 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410219 : term933 = term921.
Proof. exact (MK_COMB (@lem2410218) (@lem2410217)). Qed.
Lemma lem2410220 : term934 = term923.
Proof. exact (MK_COMB (@lem2410219) (@lem2410207)). Qed.
Lemma lem2410222 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2410223 : term923 = term324.
Proof. exact (@lem2410222 term268). Qed.
Lemma lem2410224 : term934 = term324.
Proof. exact (TRANS (@lem2410220) (@lem2410223)). Qed.
Lemma lem2410225 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410226 : term936 = term444.
Proof. exact (MK_COMB (@lem2410225) (@lem2410224)). Qed.
Lemma lem2410227 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410228 : term937 = term938.
Proof. exact (MK_COMB (@lem2410226) (@lem2410227)). Qed.
Lemma lem2410230 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410231 : term938 = term324.
Proof. exact (@lem2410230 term268). Qed.
Lemma lem2410232 : term937 = term324.
Proof. exact (TRANS (@lem2410228) (@lem2410231)). Qed.
Lemma lem2410234 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410235 : term902 = term903.
Proof. exact (@lem2410234 term268 term268). Qed.
Lemma lem2410236 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410237 : term905 = term268.
Proof. exact (EQ_MP (@lem2410236) (@lem940073)). Qed.
Lemma lem2410238 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410239 : term903 = term267.
Proof. exact (MK_COMB (@lem2410238) (@lem2410237)). Qed.
Lemma lem2410240 : term902 = term267.
Proof. exact (TRANS (@lem2410235) (@lem2410239)). Qed.
Lemma lem2410241 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2410242 : term940 = term938.
Proof. exact (MK_COMB (@lem2410241) (@lem2410240)). Qed.
Lemma lem2410244 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410245 : term938 = term324.
Proof. exact (@lem2410244 term268). Qed.
Lemma lem2410246 : term940 = term324.
Proof. exact (TRANS (@lem2410242) (@lem2410245)). Qed.
Lemma lem2410247 : term324 = term940.
Proof. exact (SYM (@lem2410246)). Qed.
Lemma lem2410248 : term937 = term940.
Proof. exact (TRANS (@lem2410232) (@lem2410247)). Qed.
Lemma lem2410249 : term924 = term941.
Proof. exact (@lem2410199 (@lem2410248)). Qed.
Lemma lem2410250 : term923 = term941.
Proof. exact (TRANS (@lem2410165) (@lem2410249)). Qed.
Lemma lem2410252 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2410253 : term941 = term324.
Proof. exact (@lem2410252 term324). Qed.
Lemma lem2410254 : term923 = term324.
Proof. exact (TRANS (@lem2410250) (@lem2410253)). Qed.
Lemma lem2410255 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410256 : term942 = term444.
Proof. exact (MK_COMB (@lem2410255) (@lem2410254)). Qed.
Lemma lem2410257 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2410258 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2410256) (@lem2410257 x)). Qed.
Lemma lem2410259 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2410156 x) (@lem2410258 x)). Qed.
Lemma lem2410260 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2410261 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2410259 x) (@lem2410260 x)). Qed.
Lemma lem2410262 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410263 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2410262) (@lem2410261 x)). Qed.
Lemma lem2410264 (y : int) : (term946 y) = (term947 y).
Proof. exact (@lem1982763 (real_of_int y) (term918 y) term885). Qed.
Lemma lem2410265 (y : int) : (term919 y) = (term920 y).
Proof. exact (@lem1982715 term885 (real_of_int y)). Qed.
Lemma lem2410267 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410268 : term267 = term891.
Proof. exact (@lem2410267 term268). Qed.
Lemma lem2410270 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410271 : term885 = term894.
Proof. exact (@lem2410270 term268). Qed.
Lemma lem2410272 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410273 : term921 = term922.
Proof. exact (MK_COMB (@lem2410272) (@lem2410271)). Qed.
Lemma lem2410274 : term923 = term924.
Proof. exact (MK_COMB (@lem2410273) (@lem2410268)). Qed.
Lemma lem2410275 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2410277 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410278 : term927 = term928.
Proof. exact (@lem2410277 (NUMERAL 0) term268). Qed.
Lemma lem2410279 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410280 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410281 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410280 h1) (fun h1 : term928 = True => @lem2410279)). Qed.
Lemma lem2410282 : term928 = True.
Proof. exact (EQ_MP (@lem2410281) (@lem2410279)). Qed.
Lemma lem2410283 : term927 = True.
Proof. exact (TRANS (@lem2410278) (@lem2410282)). Qed.
Lemma lem2410284 : True = term927.
Proof. exact (SYM (@lem2410283)). Qed.
Lemma lem2410285 : term927.
Proof. exact (EQ_MP (@lem2410284) (@lem0)). Qed.
Lemma lem2410286 : term930.
Proof. exact (@lem2410275 (@lem2410285)). Qed.
Lemma lem2410288 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410289 : term927 = term928.
Proof. exact (@lem2410288 (NUMERAL 0) term268). Qed.
Lemma lem2410290 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410291 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410292 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410291 h1) (fun h1 : term928 = True => @lem2410290)). Qed.
Lemma lem2410293 : term928 = True.
Proof. exact (EQ_MP (@lem2410292) (@lem2410290)). Qed.
Lemma lem2410294 : term927 = True.
Proof. exact (TRANS (@lem2410289) (@lem2410293)). Qed.
Lemma lem2410295 : True = term927.
Proof. exact (SYM (@lem2410294)). Qed.
Lemma lem2410296 : term927.
Proof. exact (EQ_MP (@lem2410295) (@lem0)). Qed.
Lemma lem2410297 : term931.
Proof. exact (@lem2410286 (@lem2410296)). Qed.
Lemma lem2410299 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410300 : term927 = term928.
Proof. exact (@lem2410299 (NUMERAL 0) term268). Qed.
Lemma lem2410301 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410302 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410303 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410302 h1) (fun h1 : term928 = True => @lem2410301)). Qed.
Lemma lem2410304 : term928 = True.
Proof. exact (EQ_MP (@lem2410303) (@lem2410301)). Qed.
Lemma lem2410305 : term927 = True.
Proof. exact (TRANS (@lem2410300) (@lem2410304)). Qed.
Lemma lem2410306 : True = term927.
Proof. exact (SYM (@lem2410305)). Qed.
Lemma lem2410307 : term927.
Proof. exact (EQ_MP (@lem2410306) (@lem0)). Qed.
Lemma lem2410308 : term932.
Proof. exact (@lem2410297 (@lem2410307)). Qed.
Lemma lem2410310 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410311 : term902 = term903.
Proof. exact (@lem2410310 term268 term268). Qed.
Lemma lem2410312 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410313 : term905 = term268.
Proof. exact (EQ_MP (@lem2410312) (@lem940073)). Qed.
Lemma lem2410314 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410315 : term903 = term267.
Proof. exact (MK_COMB (@lem2410314) (@lem2410313)). Qed.
Lemma lem2410316 : term902 = term267.
Proof. exact (TRANS (@lem2410311) (@lem2410315)). Qed.
Lemma lem2410318 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410319 : term897 = term908.
Proof. exact (@lem2410318 term268 term268). Qed.
Lemma lem2410320 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410321 : term905 = term268.
Proof. exact (EQ_MP (@lem2410320) (@lem940073)). Qed.
Lemma lem2410322 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410323 : term903 = term267.
Proof. exact (MK_COMB (@lem2410322) (@lem2410321)). Qed.
Lemma lem2410324 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410325 : term908 = term885.
Proof. exact (MK_COMB (@lem2410324) (@lem2410323)). Qed.
Lemma lem2410326 : term897 = term885.
Proof. exact (TRANS (@lem2410319) (@lem2410325)). Qed.
Lemma lem2410327 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410328 : term933 = term921.
Proof. exact (MK_COMB (@lem2410327) (@lem2410326)). Qed.
Lemma lem2410329 : term934 = term923.
Proof. exact (MK_COMB (@lem2410328) (@lem2410316)). Qed.
Lemma lem2410331 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2410332 : term923 = term324.
Proof. exact (@lem2410331 term268). Qed.
Lemma lem2410333 : term934 = term324.
Proof. exact (TRANS (@lem2410329) (@lem2410332)). Qed.
Lemma lem2410334 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410335 : term936 = term444.
Proof. exact (MK_COMB (@lem2410334) (@lem2410333)). Qed.
Lemma lem2410336 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410337 : term937 = term938.
Proof. exact (MK_COMB (@lem2410335) (@lem2410336)). Qed.
Lemma lem2410339 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410340 : term938 = term324.
Proof. exact (@lem2410339 term268). Qed.
Lemma lem2410341 : term937 = term324.
Proof. exact (TRANS (@lem2410337) (@lem2410340)). Qed.
Lemma lem2410343 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410344 : term902 = term903.
Proof. exact (@lem2410343 term268 term268). Qed.
Lemma lem2410345 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410346 : term905 = term268.
Proof. exact (EQ_MP (@lem2410345) (@lem940073)). Qed.
Lemma lem2410347 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410348 : term903 = term267.
Proof. exact (MK_COMB (@lem2410347) (@lem2410346)). Qed.
Lemma lem2410349 : term902 = term267.
Proof. exact (TRANS (@lem2410344) (@lem2410348)). Qed.
Lemma lem2410350 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2410351 : term940 = term938.
Proof. exact (MK_COMB (@lem2410350) (@lem2410349)). Qed.
Lemma lem2410353 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410354 : term938 = term324.
Proof. exact (@lem2410353 term268). Qed.
Lemma lem2410355 : term940 = term324.
Proof. exact (TRANS (@lem2410351) (@lem2410354)). Qed.
Lemma lem2410356 : term324 = term940.
Proof. exact (SYM (@lem2410355)). Qed.
Lemma lem2410357 : term937 = term940.
Proof. exact (TRANS (@lem2410341) (@lem2410356)). Qed.
Lemma lem2410358 : term924 = term941.
Proof. exact (@lem2410308 (@lem2410357)). Qed.
Lemma lem2410359 : term923 = term941.
Proof. exact (TRANS (@lem2410274) (@lem2410358)). Qed.
Lemma lem2410361 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2410362 : term941 = term324.
Proof. exact (@lem2410361 term324). Qed.
Lemma lem2410363 : term923 = term324.
Proof. exact (TRANS (@lem2410359) (@lem2410362)). Qed.
Lemma lem2410364 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410365 : term942 = term444.
Proof. exact (MK_COMB (@lem2410364) (@lem2410363)). Qed.
Lemma lem2410366 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2410367 (y : int) : (term920 y) = (term445 y).
Proof. exact (MK_COMB (@lem2410365) (@lem2410366 y)). Qed.
Lemma lem2410368 (y : int) : (term919 y) = (term445 y).
Proof. exact (TRANS (@lem2410265 y) (@lem2410367 y)). Qed.
Lemma lem2410369 (y : int) : (term445 y) = term324.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2410370 (y : int) : (term919 y) = term324.
Proof. exact (TRANS (@lem2410368 y) (@lem2410369 y)). Qed.
Lemma lem2410371 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410372 (y : int) : (term943 y) = term326.
Proof. exact (MK_COMB (@lem2410371) (@lem2410370 y)). Qed.
Lemma lem2410373 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2410374 (y : int) : (term947 y) = term948.
Proof. exact (MK_COMB (@lem2410372 y) (@lem2410373)). Qed.
Lemma lem2410375 (y : int) : (term946 y) = term948.
Proof. exact (TRANS (@lem2410264 y) (@lem2410374 y)). Qed.
Lemma lem2410376 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2410377 (y : int) : (term946 y) = term885.
Proof. exact (TRANS (@lem2410375 y) (@lem2410376)). Qed.
Lemma lem2410378 (x : int) (y : int) : (term945 x y) = term948.
Proof. exact (MK_COMB (@lem2410263 x) (@lem2410377 y)). Qed.
Lemma lem2410379 (x : int) (y : int) : (term944 x y) = term948.
Proof. exact (TRANS (@lem2410155 x y) (@lem2410378 x y)). Qed.
Lemma lem2410380 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2410381 (x : int) (y : int) : (term944 x y) = term885.
Proof. exact (TRANS (@lem2410379 x y) (@lem2410380)). Qed.
Lemma lem2410382 (x : int) (y : int) : (term967 x y) = term885.
Proof. exact (TRANS (@lem2410154 x y) (@lem2410381 x y)). Qed.
Lemma lem2410383 (x : int) (y : int) : (term966 x y) = term885.
Proof. exact (TRANS (@lem2410103 x y) (@lem2410382 x y)). Qed.
Lemma lem2410384 (y : int) (x : int) : (term965 y x) = term885.
Proof. exact (TRANS (@lem2410102 x y) (@lem2410383 x y)). Qed.
Lemma lem2410385 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2410386 (y : int) (x : int) : (term968 y x) = term950.
Proof. exact (MK_COMB (@lem2410385) (@lem2410384 y x)). Qed.
Lemma lem2410387 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2410388 (y : int) (x : int) : (term963 y x) = term951.
Proof. exact (MK_COMB (@lem2410386 y x) (@lem2410387)). Qed.
Lemma lem2410389 (x : int) (y : int) : (term307 x y) = term951.
Proof. exact (TRANS (@lem2410075 y x) (@lem2410388 y x)). Qed.
Lemma lem2410390 (x : int) : (term592 x) = term952.
Proof. exact (fun_ext (fun y : int => @lem2410389 x y)). Qed.
Lemma lem2410391 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410392 (x : int) : (term607 x) = term953.
Proof. exact (MK_COMB (@lem2410391) (@lem2410390 x)). Qed.
Lemma lem2410393 : term614 = term954.
Proof. exact (fun_ext (fun x : int => @lem2410392 x)). Qed.
Lemma lem2410394 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410395 : term629 = term955.
Proof. exact (MK_COMB (@lem2410394) (@lem2410393)). Qed.
Lemma lem2410396 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2410397 : term626 = term969.
Proof. exact (MK_COMB (@lem2410396) (@lem2410074)). Qed.
Lemma lem2410398 : term630 = term970.
Proof. exact (MK_COMB (@lem2410397) (@lem2410395)). Qed.
Lemma lem2410399 (x : int) : (term333 x) = (term971 x).
Proof. exact (@lem1988287 (real_of_int x) (term330 x)). Qed.
Lemma lem2410400 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410407 (x : int) : (term327 x) = (real_of_int x).
Proof. exact (@lem1982721 (real_of_int x)). Qed.
Lemma lem2410408 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410409 (x : int) : (term329 x) = (term261 x).
Proof. exact (MK_COMB (@lem2410408) (@lem2410407 x)). Qed.
Lemma lem2410412 (x : int) : (term330 x) = (term341 x).
Proof. exact (MK_COMB (@lem2410409 x) (@lem2410400)). Qed.
Lemma lem2410415 (x : int) : (term972 x) = (term972 x).
Proof. exact (eq_refl (term972 x)). Qed.
Lemma lem2410416 (x : int) : (term973 x) = (term974 x).
Proof. exact (MK_COMB (@lem2410415 x) (@lem2410412 x)). Qed.
Lemma lem2410417 (x : int) : (term974 x) = (term975 x).
Proof. exact (@lem1982792 (real_of_int x) (term341 x)). Qed.
Lemma lem2410418 (x : int) : (term888 x) = (term889 x).
Proof. exact (@lem1982781 (real_of_int x) term885 term267). Qed.
Lemma lem2410420 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410421 : term267 = term891.
Proof. exact (@lem2410420 term268). Qed.
Lemma lem2410423 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410424 : term885 = term894.
Proof. exact (@lem2410423 term268). Qed.
Lemma lem2410425 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410426 : term895 = term896.
Proof. exact (MK_COMB (@lem2410425) (@lem2410424)). Qed.
Lemma lem2410427 : term897 = term898.
Proof. exact (MK_COMB (@lem2410426) (@lem2410421)). Qed.
Lemma lem2410428 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2410430 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410431 : term902 = term903.
Proof. exact (@lem2410430 term268 term268). Qed.
Lemma lem2410432 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410433 : term905 = term268.
Proof. exact (EQ_MP (@lem2410432) (@lem940073)). Qed.
Lemma lem2410434 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410435 : term903 = term267.
Proof. exact (MK_COMB (@lem2410434) (@lem2410433)). Qed.
Lemma lem2410436 : term902 = term267.
Proof. exact (TRANS (@lem2410431) (@lem2410435)). Qed.
Lemma lem2410438 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410439 : term897 = term908.
Proof. exact (@lem2410438 term268 term268). Qed.
Lemma lem2410440 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410441 : term905 = term268.
Proof. exact (EQ_MP (@lem2410440) (@lem940073)). Qed.
Lemma lem2410442 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410443 : term903 = term267.
Proof. exact (MK_COMB (@lem2410442) (@lem2410441)). Qed.
Lemma lem2410444 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410445 : term908 = term885.
Proof. exact (MK_COMB (@lem2410444) (@lem2410443)). Qed.
Lemma lem2410446 : term897 = term885.
Proof. exact (TRANS (@lem2410439) (@lem2410445)). Qed.
Lemma lem2410447 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2410448 : term909 = term910.
Proof. exact (MK_COMB (@lem2410447) (@lem2410446)). Qed.
Lemma lem2410449 : term899 = term894.
Proof. exact (MK_COMB (@lem2410448) (@lem2410436)). Qed.
Lemma lem2410450 : term898 = term894.
Proof. exact (TRANS (@lem2410428) (@lem2410449)). Qed.
Lemma lem2410451 : term897 = term894.
Proof. exact (TRANS (@lem2410427) (@lem2410450)). Qed.
Lemma lem2410453 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2410454 : term894 = term885.
Proof. exact (@lem2410453 term885). Qed.
Lemma lem2410455 : term897 = term885.
Proof. exact (TRANS (@lem2410451) (@lem2410454)). Qed.
Lemma lem2410458 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2410459 (x : int) : (term889 x) = (term913 x).
Proof. exact (MK_COMB (@lem2410458 x) (@lem2410455)). Qed.
Lemma lem2410460 (x : int) : (term888 x) = (term913 x).
Proof. exact (TRANS (@lem2410418 x) (@lem2410459 x)). Qed.
Lemma lem2410461 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2410462 (x : int) : (term975 x) = (term946 x).
Proof. exact (MK_COMB (@lem2410461 x) (@lem2410460 x)). Qed.
Lemma lem2410463 (x : int) : (term946 x) = (term947 x).
Proof. exact (@lem1982763 (real_of_int x) (term918 x) term885). Qed.
Lemma lem2410464 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2410466 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410467 : term267 = term891.
Proof. exact (@lem2410466 term268). Qed.
Lemma lem2410469 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410470 : term885 = term894.
Proof. exact (@lem2410469 term268). Qed.
Lemma lem2410471 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410472 : term921 = term922.
Proof. exact (MK_COMB (@lem2410471) (@lem2410470)). Qed.
Lemma lem2410473 : term923 = term924.
Proof. exact (MK_COMB (@lem2410472) (@lem2410467)). Qed.
Lemma lem2410474 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2410476 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410477 : term927 = term928.
Proof. exact (@lem2410476 (NUMERAL 0) term268). Qed.
Lemma lem2410478 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410479 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410480 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410479 h1) (fun h1 : term928 = True => @lem2410478)). Qed.
Lemma lem2410481 : term928 = True.
Proof. exact (EQ_MP (@lem2410480) (@lem2410478)). Qed.
Lemma lem2410482 : term927 = True.
Proof. exact (TRANS (@lem2410477) (@lem2410481)). Qed.
Lemma lem2410483 : True = term927.
Proof. exact (SYM (@lem2410482)). Qed.
Lemma lem2410484 : term927.
Proof. exact (EQ_MP (@lem2410483) (@lem0)). Qed.
Lemma lem2410485 : term930.
Proof. exact (@lem2410474 (@lem2410484)). Qed.
Lemma lem2410487 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410488 : term927 = term928.
Proof. exact (@lem2410487 (NUMERAL 0) term268). Qed.
Lemma lem2410489 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410490 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410491 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410490 h1) (fun h1 : term928 = True => @lem2410489)). Qed.
Lemma lem2410492 : term928 = True.
Proof. exact (EQ_MP (@lem2410491) (@lem2410489)). Qed.
Lemma lem2410493 : term927 = True.
Proof. exact (TRANS (@lem2410488) (@lem2410492)). Qed.
Lemma lem2410494 : True = term927.
Proof. exact (SYM (@lem2410493)). Qed.
Lemma lem2410495 : term927.
Proof. exact (EQ_MP (@lem2410494) (@lem0)). Qed.
Lemma lem2410496 : term931.
Proof. exact (@lem2410485 (@lem2410495)). Qed.
Lemma lem2410498 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410499 : term927 = term928.
Proof. exact (@lem2410498 (NUMERAL 0) term268). Qed.
Lemma lem2410500 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410501 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410502 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410501 h1) (fun h1 : term928 = True => @lem2410500)). Qed.
Lemma lem2410503 : term928 = True.
Proof. exact (EQ_MP (@lem2410502) (@lem2410500)). Qed.
Lemma lem2410504 : term927 = True.
Proof. exact (TRANS (@lem2410499) (@lem2410503)). Qed.
Lemma lem2410505 : True = term927.
Proof. exact (SYM (@lem2410504)). Qed.
Lemma lem2410506 : term927.
Proof. exact (EQ_MP (@lem2410505) (@lem0)). Qed.
Lemma lem2410507 : term932.
Proof. exact (@lem2410496 (@lem2410506)). Qed.
Lemma lem2410509 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410510 : term902 = term903.
Proof. exact (@lem2410509 term268 term268). Qed.
Lemma lem2410511 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410512 : term905 = term268.
Proof. exact (EQ_MP (@lem2410511) (@lem940073)). Qed.
Lemma lem2410513 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410514 : term903 = term267.
Proof. exact (MK_COMB (@lem2410513) (@lem2410512)). Qed.
Lemma lem2410515 : term902 = term267.
Proof. exact (TRANS (@lem2410510) (@lem2410514)). Qed.
Lemma lem2410517 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410518 : term897 = term908.
Proof. exact (@lem2410517 term268 term268). Qed.
Lemma lem2410519 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410520 : term905 = term268.
Proof. exact (EQ_MP (@lem2410519) (@lem940073)). Qed.
Lemma lem2410521 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410522 : term903 = term267.
Proof. exact (MK_COMB (@lem2410521) (@lem2410520)). Qed.
Lemma lem2410523 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410524 : term908 = term885.
Proof. exact (MK_COMB (@lem2410523) (@lem2410522)). Qed.
Lemma lem2410525 : term897 = term885.
Proof. exact (TRANS (@lem2410518) (@lem2410524)). Qed.
Lemma lem2410526 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410527 : term933 = term921.
Proof. exact (MK_COMB (@lem2410526) (@lem2410525)). Qed.
Lemma lem2410528 : term934 = term923.
Proof. exact (MK_COMB (@lem2410527) (@lem2410515)). Qed.
Lemma lem2410530 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2410531 : term923 = term324.
Proof. exact (@lem2410530 term268). Qed.
Lemma lem2410532 : term934 = term324.
Proof. exact (TRANS (@lem2410528) (@lem2410531)). Qed.
Lemma lem2410533 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410534 : term936 = term444.
Proof. exact (MK_COMB (@lem2410533) (@lem2410532)). Qed.
Lemma lem2410535 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410536 : term937 = term938.
Proof. exact (MK_COMB (@lem2410534) (@lem2410535)). Qed.
Lemma lem2410538 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410539 : term938 = term324.
Proof. exact (@lem2410538 term268). Qed.
Lemma lem2410540 : term937 = term324.
Proof. exact (TRANS (@lem2410536) (@lem2410539)). Qed.
Lemma lem2410542 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410543 : term902 = term903.
Proof. exact (@lem2410542 term268 term268). Qed.
Lemma lem2410544 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410545 : term905 = term268.
Proof. exact (EQ_MP (@lem2410544) (@lem940073)). Qed.
Lemma lem2410546 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410547 : term903 = term267.
Proof. exact (MK_COMB (@lem2410546) (@lem2410545)). Qed.
Lemma lem2410548 : term902 = term267.
Proof. exact (TRANS (@lem2410543) (@lem2410547)). Qed.
Lemma lem2410549 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2410550 : term940 = term938.
Proof. exact (MK_COMB (@lem2410549) (@lem2410548)). Qed.
Lemma lem2410552 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410553 : term938 = term324.
Proof. exact (@lem2410552 term268). Qed.
Lemma lem2410554 : term940 = term324.
Proof. exact (TRANS (@lem2410550) (@lem2410553)). Qed.
Lemma lem2410555 : term324 = term940.
Proof. exact (SYM (@lem2410554)). Qed.
Lemma lem2410556 : term937 = term940.
Proof. exact (TRANS (@lem2410540) (@lem2410555)). Qed.
Lemma lem2410557 : term924 = term941.
Proof. exact (@lem2410507 (@lem2410556)). Qed.
Lemma lem2410558 : term923 = term941.
Proof. exact (TRANS (@lem2410473) (@lem2410557)). Qed.
Lemma lem2410560 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2410561 : term941 = term324.
Proof. exact (@lem2410560 term324). Qed.
Lemma lem2410562 : term923 = term324.
Proof. exact (TRANS (@lem2410558) (@lem2410561)). Qed.
Lemma lem2410563 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410564 : term942 = term444.
Proof. exact (MK_COMB (@lem2410563) (@lem2410562)). Qed.
Lemma lem2410565 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2410566 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2410564) (@lem2410565 x)). Qed.
Lemma lem2410567 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2410464 x) (@lem2410566 x)). Qed.
Lemma lem2410568 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2410569 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2410567 x) (@lem2410568 x)). Qed.
Lemma lem2410570 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410571 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2410570) (@lem2410569 x)). Qed.
Lemma lem2410572 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2410573 (x : int) : (term947 x) = term948.
Proof. exact (MK_COMB (@lem2410571 x) (@lem2410572)). Qed.
Lemma lem2410574 (x : int) : (term946 x) = term948.
Proof. exact (TRANS (@lem2410463 x) (@lem2410573 x)). Qed.
Lemma lem2410575 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2410576 (x : int) : (term946 x) = term885.
Proof. exact (TRANS (@lem2410574 x) (@lem2410575)). Qed.
Lemma lem2410577 (x : int) : (term975 x) = term885.
Proof. exact (TRANS (@lem2410462 x) (@lem2410576 x)). Qed.
Lemma lem2410578 (x : int) : (term974 x) = term885.
Proof. exact (TRANS (@lem2410417 x) (@lem2410577 x)). Qed.
Lemma lem2410579 (x : int) : (term973 x) = term885.
Proof. exact (TRANS (@lem2410416 x) (@lem2410578 x)). Qed.
Lemma lem2410580 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2410581 (x : int) : (term976 x) = term950.
Proof. exact (MK_COMB (@lem2410580) (@lem2410579 x)). Qed.
Lemma lem2410582 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2410583 (x : int) : (term971 x) = term951.
Proof. exact (MK_COMB (@lem2410581 x) (@lem2410582)). Qed.
Lemma lem2410584 (x : int) : (term333 x) = term951.
Proof. exact (TRANS (@lem2410399 x) (@lem2410583 x)). Qed.
Lemma lem2410585 : term634 = term952.
Proof. exact (fun_ext (fun x : int => @lem2410584 x)). Qed.
Lemma lem2410586 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410587 : term645 = term953.
Proof. exact (MK_COMB (@lem2410586) (@lem2410585)). Qed.
Lemma lem2410588 (x : int) : (term344 x) = (term977 x).
Proof. exact (@lem1988287 (term327 x) (term341 x)). Qed.
Lemma lem2410595 (x : int) : (term341 x) = (term341 x).
Proof. exact (eq_refl (term341 x)). Qed.
Lemma lem2410602 (x : int) : (term327 x) = (real_of_int x).
Proof. exact (@lem1982721 (real_of_int x)). Qed.
Lemma lem2410603 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2410604 (x : int) : (term978 x) = (term972 x).
Proof. exact (MK_COMB (@lem2410603) (@lem2410602 x)). Qed.
Lemma lem2410605 (x : int) : (term979 x) = (term974 x).
Proof. exact (MK_COMB (@lem2410604 x) (@lem2410595 x)). Qed.
Lemma lem2410606 (x : int) : (term974 x) = (term975 x).
Proof. exact (@lem1982792 (real_of_int x) (term341 x)). Qed.
Lemma lem2410607 (x : int) : (term888 x) = (term889 x).
Proof. exact (@lem1982781 (real_of_int x) term885 term267). Qed.
Lemma lem2410609 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410610 : term267 = term891.
Proof. exact (@lem2410609 term268). Qed.
Lemma lem2410612 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410613 : term885 = term894.
Proof. exact (@lem2410612 term268). Qed.
Lemma lem2410614 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410615 : term895 = term896.
Proof. exact (MK_COMB (@lem2410614) (@lem2410613)). Qed.
Lemma lem2410616 : term897 = term898.
Proof. exact (MK_COMB (@lem2410615) (@lem2410610)). Qed.
Lemma lem2410617 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2410619 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410620 : term902 = term903.
Proof. exact (@lem2410619 term268 term268). Qed.
Lemma lem2410621 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410622 : term905 = term268.
Proof. exact (EQ_MP (@lem2410621) (@lem940073)). Qed.
Lemma lem2410623 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410624 : term903 = term267.
Proof. exact (MK_COMB (@lem2410623) (@lem2410622)). Qed.
Lemma lem2410625 : term902 = term267.
Proof. exact (TRANS (@lem2410620) (@lem2410624)). Qed.
Lemma lem2410627 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410628 : term897 = term908.
Proof. exact (@lem2410627 term268 term268). Qed.
Lemma lem2410629 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410630 : term905 = term268.
Proof. exact (EQ_MP (@lem2410629) (@lem940073)). Qed.
Lemma lem2410631 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410632 : term903 = term267.
Proof. exact (MK_COMB (@lem2410631) (@lem2410630)). Qed.
Lemma lem2410633 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410634 : term908 = term885.
Proof. exact (MK_COMB (@lem2410633) (@lem2410632)). Qed.
Lemma lem2410635 : term897 = term885.
Proof. exact (TRANS (@lem2410628) (@lem2410634)). Qed.
Lemma lem2410636 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2410637 : term909 = term910.
Proof. exact (MK_COMB (@lem2410636) (@lem2410635)). Qed.
Lemma lem2410638 : term899 = term894.
Proof. exact (MK_COMB (@lem2410637) (@lem2410625)). Qed.
Lemma lem2410639 : term898 = term894.
Proof. exact (TRANS (@lem2410617) (@lem2410638)). Qed.
Lemma lem2410640 : term897 = term894.
Proof. exact (TRANS (@lem2410616) (@lem2410639)). Qed.
Lemma lem2410642 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2410643 : term894 = term885.
Proof. exact (@lem2410642 term885). Qed.
Lemma lem2410644 : term897 = term885.
Proof. exact (TRANS (@lem2410640) (@lem2410643)). Qed.
Lemma lem2410647 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2410648 (x : int) : (term889 x) = (term913 x).
Proof. exact (MK_COMB (@lem2410647 x) (@lem2410644)). Qed.
Lemma lem2410649 (x : int) : (term888 x) = (term913 x).
Proof. exact (TRANS (@lem2410607 x) (@lem2410648 x)). Qed.
Lemma lem2410650 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2410651 (x : int) : (term975 x) = (term946 x).
Proof. exact (MK_COMB (@lem2410650 x) (@lem2410649 x)). Qed.
Lemma lem2410652 (x : int) : (term946 x) = (term947 x).
Proof. exact (@lem1982763 (real_of_int x) (term918 x) term885). Qed.
Lemma lem2410653 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2410655 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410656 : term267 = term891.
Proof. exact (@lem2410655 term268). Qed.
Lemma lem2410658 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410659 : term885 = term894.
Proof. exact (@lem2410658 term268). Qed.
Lemma lem2410660 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410661 : term921 = term922.
Proof. exact (MK_COMB (@lem2410660) (@lem2410659)). Qed.
Lemma lem2410662 : term923 = term924.
Proof. exact (MK_COMB (@lem2410661) (@lem2410656)). Qed.
Lemma lem2410663 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2410665 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410666 : term927 = term928.
Proof. exact (@lem2410665 (NUMERAL 0) term268). Qed.
Lemma lem2410667 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410668 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410669 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410668 h1) (fun h1 : term928 = True => @lem2410667)). Qed.
Lemma lem2410670 : term928 = True.
Proof. exact (EQ_MP (@lem2410669) (@lem2410667)). Qed.
Lemma lem2410671 : term927 = True.
Proof. exact (TRANS (@lem2410666) (@lem2410670)). Qed.
Lemma lem2410672 : True = term927.
Proof. exact (SYM (@lem2410671)). Qed.
Lemma lem2410673 : term927.
Proof. exact (EQ_MP (@lem2410672) (@lem0)). Qed.
Lemma lem2410674 : term930.
Proof. exact (@lem2410663 (@lem2410673)). Qed.
Lemma lem2410676 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410677 : term927 = term928.
Proof. exact (@lem2410676 (NUMERAL 0) term268). Qed.
Lemma lem2410678 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410679 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410680 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410679 h1) (fun h1 : term928 = True => @lem2410678)). Qed.
Lemma lem2410681 : term928 = True.
Proof. exact (EQ_MP (@lem2410680) (@lem2410678)). Qed.
Lemma lem2410682 : term927 = True.
Proof. exact (TRANS (@lem2410677) (@lem2410681)). Qed.
Lemma lem2410683 : True = term927.
Proof. exact (SYM (@lem2410682)). Qed.
Lemma lem2410684 : term927.
Proof. exact (EQ_MP (@lem2410683) (@lem0)). Qed.
Lemma lem2410685 : term931.
Proof. exact (@lem2410674 (@lem2410684)). Qed.
Lemma lem2410687 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410688 : term927 = term928.
Proof. exact (@lem2410687 (NUMERAL 0) term268). Qed.
Lemma lem2410689 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410690 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410691 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410690 h1) (fun h1 : term928 = True => @lem2410689)). Qed.
Lemma lem2410692 : term928 = True.
Proof. exact (EQ_MP (@lem2410691) (@lem2410689)). Qed.
Lemma lem2410693 : term927 = True.
Proof. exact (TRANS (@lem2410688) (@lem2410692)). Qed.
Lemma lem2410694 : True = term927.
Proof. exact (SYM (@lem2410693)). Qed.
Lemma lem2410695 : term927.
Proof. exact (EQ_MP (@lem2410694) (@lem0)). Qed.
Lemma lem2410696 : term932.
Proof. exact (@lem2410685 (@lem2410695)). Qed.
Lemma lem2410698 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410699 : term902 = term903.
Proof. exact (@lem2410698 term268 term268). Qed.
Lemma lem2410700 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410701 : term905 = term268.
Proof. exact (EQ_MP (@lem2410700) (@lem940073)). Qed.
Lemma lem2410702 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410703 : term903 = term267.
Proof. exact (MK_COMB (@lem2410702) (@lem2410701)). Qed.
Lemma lem2410704 : term902 = term267.
Proof. exact (TRANS (@lem2410699) (@lem2410703)). Qed.
Lemma lem2410706 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410707 : term897 = term908.
Proof. exact (@lem2410706 term268 term268). Qed.
Lemma lem2410708 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410709 : term905 = term268.
Proof. exact (EQ_MP (@lem2410708) (@lem940073)). Qed.
Lemma lem2410710 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410711 : term903 = term267.
Proof. exact (MK_COMB (@lem2410710) (@lem2410709)). Qed.
Lemma lem2410712 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410713 : term908 = term885.
Proof. exact (MK_COMB (@lem2410712) (@lem2410711)). Qed.
Lemma lem2410714 : term897 = term885.
Proof. exact (TRANS (@lem2410707) (@lem2410713)). Qed.
Lemma lem2410715 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410716 : term933 = term921.
Proof. exact (MK_COMB (@lem2410715) (@lem2410714)). Qed.
Lemma lem2410717 : term934 = term923.
Proof. exact (MK_COMB (@lem2410716) (@lem2410704)). Qed.
Lemma lem2410719 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2410720 : term923 = term324.
Proof. exact (@lem2410719 term268). Qed.
Lemma lem2410721 : term934 = term324.
Proof. exact (TRANS (@lem2410717) (@lem2410720)). Qed.
Lemma lem2410722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410723 : term936 = term444.
Proof. exact (MK_COMB (@lem2410722) (@lem2410721)). Qed.
Lemma lem2410724 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410725 : term937 = term938.
Proof. exact (MK_COMB (@lem2410723) (@lem2410724)). Qed.
Lemma lem2410727 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410728 : term938 = term324.
Proof. exact (@lem2410727 term268). Qed.
Lemma lem2410729 : term937 = term324.
Proof. exact (TRANS (@lem2410725) (@lem2410728)). Qed.
Lemma lem2410731 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410732 : term902 = term903.
Proof. exact (@lem2410731 term268 term268). Qed.
Lemma lem2410733 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410734 : term905 = term268.
Proof. exact (EQ_MP (@lem2410733) (@lem940073)). Qed.
Lemma lem2410735 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410736 : term903 = term267.
Proof. exact (MK_COMB (@lem2410735) (@lem2410734)). Qed.
Lemma lem2410737 : term902 = term267.
Proof. exact (TRANS (@lem2410732) (@lem2410736)). Qed.
Lemma lem2410738 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2410739 : term940 = term938.
Proof. exact (MK_COMB (@lem2410738) (@lem2410737)). Qed.
Lemma lem2410741 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410742 : term938 = term324.
Proof. exact (@lem2410741 term268). Qed.
Lemma lem2410743 : term940 = term324.
Proof. exact (TRANS (@lem2410739) (@lem2410742)). Qed.
Lemma lem2410744 : term324 = term940.
Proof. exact (SYM (@lem2410743)). Qed.
Lemma lem2410745 : term937 = term940.
Proof. exact (TRANS (@lem2410729) (@lem2410744)). Qed.
Lemma lem2410746 : term924 = term941.
Proof. exact (@lem2410696 (@lem2410745)). Qed.
Lemma lem2410747 : term923 = term941.
Proof. exact (TRANS (@lem2410662) (@lem2410746)). Qed.
Lemma lem2410749 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2410750 : term941 = term324.
Proof. exact (@lem2410749 term324). Qed.
Lemma lem2410751 : term923 = term324.
Proof. exact (TRANS (@lem2410747) (@lem2410750)). Qed.
Lemma lem2410752 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410753 : term942 = term444.
Proof. exact (MK_COMB (@lem2410752) (@lem2410751)). Qed.
Lemma lem2410754 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2410755 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2410753) (@lem2410754 x)). Qed.
Lemma lem2410756 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2410653 x) (@lem2410755 x)). Qed.
Lemma lem2410757 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2410758 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2410756 x) (@lem2410757 x)). Qed.
Lemma lem2410759 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410760 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2410759) (@lem2410758 x)). Qed.
Lemma lem2410761 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2410762 (x : int) : (term947 x) = term948.
Proof. exact (MK_COMB (@lem2410760 x) (@lem2410761)). Qed.
Lemma lem2410763 (x : int) : (term946 x) = term948.
Proof. exact (TRANS (@lem2410652 x) (@lem2410762 x)). Qed.
Lemma lem2410764 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2410765 (x : int) : (term946 x) = term885.
Proof. exact (TRANS (@lem2410763 x) (@lem2410764)). Qed.
Lemma lem2410766 (x : int) : (term975 x) = term885.
Proof. exact (TRANS (@lem2410651 x) (@lem2410765 x)). Qed.
Lemma lem2410767 (x : int) : (term974 x) = term885.
Proof. exact (TRANS (@lem2410606 x) (@lem2410766 x)). Qed.
Lemma lem2410768 (x : int) : (term979 x) = term885.
Proof. exact (TRANS (@lem2410605 x) (@lem2410767 x)). Qed.
Lemma lem2410769 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2410770 (x : int) : (term980 x) = term950.
Proof. exact (MK_COMB (@lem2410769) (@lem2410768 x)). Qed.
Lemma lem2410771 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2410772 (x : int) : (term977 x) = term951.
Proof. exact (MK_COMB (@lem2410770 x) (@lem2410771)). Qed.
Lemma lem2410773 (x : int) : (term344 x) = term951.
Proof. exact (TRANS (@lem2410588 x) (@lem2410772 x)). Qed.
Lemma lem2410774 : term635 = term952.
Proof. exact (fun_ext (fun x : int => @lem2410773 x)). Qed.
Lemma lem2410775 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410776 : term650 = term953.
Proof. exact (MK_COMB (@lem2410775) (@lem2410774)). Qed.
Lemma lem2410777 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2410778 : term647 = term981.
Proof. exact (MK_COMB (@lem2410777) (@lem2410587)). Qed.
Lemma lem2410779 : term651 = term982.
Proof. exact (MK_COMB (@lem2410778) (@lem2410776)). Qed.
Lemma lem2410780 (x : int) (y : int) (z : int) : (term370 x y z) = (term983 x y z).
Proof. exact (@lem1988287 (term369 x y z) (term362 x y z)). Qed.
Lemma lem2410799 (x : int) (y : int) (z : int) : (term362 x y z) = (term362 x y z).
Proof. exact (eq_refl (term362 x y z)). Qed.
Lemma lem2410816 (x : int) (y : int) (z : int) : (term369 x y z) = (term359 x y z).
Proof. exact (@lem1982745 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem2410817 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2410818 (x : int) (y : int) (z : int) : (term984 x y z) = (term985 x y z).
Proof. exact (MK_COMB (@lem2410817) (@lem2410816 x y z)). Qed.
Lemma lem2410819 (x : int) (y : int) (z : int) : (term986 x y z) = (term987 x y z).
Proof. exact (MK_COMB (@lem2410818 x y z) (@lem2410799 x y z)). Qed.
Lemma lem2410820 (x : int) (y : int) (z : int) : (term987 x y z) = (term988 x y z).
Proof. exact (@lem1982792 (term359 x y z) (term362 x y z)). Qed.
Lemma lem2410821 (x : int) (y : int) (z : int) : (term989 x y z) = (term990 x y z).
Proof. exact (@lem1982781 (term359 x y z) term885 term267). Qed.
Lemma lem2410823 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410824 : term267 = term891.
Proof. exact (@lem2410823 term268). Qed.
Lemma lem2410826 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410827 : term885 = term894.
Proof. exact (@lem2410826 term268). Qed.
Lemma lem2410828 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410829 : term895 = term896.
Proof. exact (MK_COMB (@lem2410828) (@lem2410827)). Qed.
Lemma lem2410830 : term897 = term898.
Proof. exact (MK_COMB (@lem2410829) (@lem2410824)). Qed.
Lemma lem2410831 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2410833 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410834 : term902 = term903.
Proof. exact (@lem2410833 term268 term268). Qed.
Lemma lem2410835 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410836 : term905 = term268.
Proof. exact (EQ_MP (@lem2410835) (@lem940073)). Qed.
Lemma lem2410837 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410838 : term903 = term267.
Proof. exact (MK_COMB (@lem2410837) (@lem2410836)). Qed.
Lemma lem2410839 : term902 = term267.
Proof. exact (TRANS (@lem2410834) (@lem2410838)). Qed.
Lemma lem2410841 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410842 : term897 = term908.
Proof. exact (@lem2410841 term268 term268). Qed.
Lemma lem2410843 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410844 : term905 = term268.
Proof. exact (EQ_MP (@lem2410843) (@lem940073)). Qed.
Lemma lem2410845 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410846 : term903 = term267.
Proof. exact (MK_COMB (@lem2410845) (@lem2410844)). Qed.
Lemma lem2410847 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410848 : term908 = term885.
Proof. exact (MK_COMB (@lem2410847) (@lem2410846)). Qed.
Lemma lem2410849 : term897 = term885.
Proof. exact (TRANS (@lem2410842) (@lem2410848)). Qed.
Lemma lem2410850 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2410851 : term909 = term910.
Proof. exact (MK_COMB (@lem2410850) (@lem2410849)). Qed.
Lemma lem2410852 : term899 = term894.
Proof. exact (MK_COMB (@lem2410851) (@lem2410839)). Qed.
Lemma lem2410853 : term898 = term894.
Proof. exact (TRANS (@lem2410831) (@lem2410852)). Qed.
Lemma lem2410854 : term897 = term894.
Proof. exact (TRANS (@lem2410830) (@lem2410853)). Qed.
Lemma lem2410856 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2410857 : term894 = term885.
Proof. exact (@lem2410856 term885). Qed.
Lemma lem2410858 : term897 = term885.
Proof. exact (TRANS (@lem2410854) (@lem2410857)). Qed.
Lemma lem2410861 (x : int) (y : int) (z : int) : (term991 x y z) = (term991 x y z).
Proof. exact (eq_refl (term991 x y z)). Qed.
Lemma lem2410862 (x : int) (y : int) (z : int) : (term990 x y z) = (term992 x y z).
Proof. exact (MK_COMB (@lem2410861 x y z) (@lem2410858)). Qed.
Lemma lem2410863 (x : int) (y : int) (z : int) : (term989 x y z) = (term992 x y z).
Proof. exact (TRANS (@lem2410821 x y z) (@lem2410862 x y z)). Qed.
Lemma lem2410864 (x : int) (y : int) (z : int) : (term361 x y z) = (term361 x y z).
Proof. exact (eq_refl (term361 x y z)). Qed.
Lemma lem2410865 (x : int) (y : int) (z : int) : (term988 x y z) = (term993 x y z).
Proof. exact (MK_COMB (@lem2410864 x y z) (@lem2410863 x y z)). Qed.
Lemma lem2410866 (x : int) (y : int) (z : int) : (term993 x y z) = (term994 x y z).
Proof. exact (@lem1982763 (term359 x y z) (term995 x y z) term885). Qed.
Lemma lem2410867 (x : int) (y : int) (z : int) : (term996 x y z) = (term997 x y z).
Proof. exact (@lem1982715 term885 (term359 x y z)). Qed.
Lemma lem2410869 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2410870 : term267 = term891.
Proof. exact (@lem2410869 term268). Qed.
Lemma lem2410872 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2410873 : term885 = term894.
Proof. exact (@lem2410872 term268). Qed.
Lemma lem2410874 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410875 : term921 = term922.
Proof. exact (MK_COMB (@lem2410874) (@lem2410873)). Qed.
Lemma lem2410876 : term923 = term924.
Proof. exact (MK_COMB (@lem2410875) (@lem2410870)). Qed.
Lemma lem2410877 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2410879 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410880 : term927 = term928.
Proof. exact (@lem2410879 (NUMERAL 0) term268). Qed.
Lemma lem2410881 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410882 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410883 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410882 h1) (fun h1 : term928 = True => @lem2410881)). Qed.
Lemma lem2410884 : term928 = True.
Proof. exact (EQ_MP (@lem2410883) (@lem2410881)). Qed.
Lemma lem2410885 : term927 = True.
Proof. exact (TRANS (@lem2410880) (@lem2410884)). Qed.
Lemma lem2410886 : True = term927.
Proof. exact (SYM (@lem2410885)). Qed.
Lemma lem2410887 : term927.
Proof. exact (EQ_MP (@lem2410886) (@lem0)). Qed.
Lemma lem2410888 : term930.
Proof. exact (@lem2410877 (@lem2410887)). Qed.
Lemma lem2410890 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410891 : term927 = term928.
Proof. exact (@lem2410890 (NUMERAL 0) term268). Qed.
Lemma lem2410892 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410893 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410894 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410893 h1) (fun h1 : term928 = True => @lem2410892)). Qed.
Lemma lem2410895 : term928 = True.
Proof. exact (EQ_MP (@lem2410894) (@lem2410892)). Qed.
Lemma lem2410896 : term927 = True.
Proof. exact (TRANS (@lem2410891) (@lem2410895)). Qed.
Lemma lem2410897 : True = term927.
Proof. exact (SYM (@lem2410896)). Qed.
Lemma lem2410898 : term927.
Proof. exact (EQ_MP (@lem2410897) (@lem0)). Qed.
Lemma lem2410899 : term931.
Proof. exact (@lem2410888 (@lem2410898)). Qed.
Lemma lem2410901 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2410902 : term927 = term928.
Proof. exact (@lem2410901 (NUMERAL 0) term268). Qed.
Lemma lem2410903 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2410904 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2410905 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2410904 h1) (fun h1 : term928 = True => @lem2410903)). Qed.
Lemma lem2410906 : term928 = True.
Proof. exact (EQ_MP (@lem2410905) (@lem2410903)). Qed.
Lemma lem2410907 : term927 = True.
Proof. exact (TRANS (@lem2410902) (@lem2410906)). Qed.
Lemma lem2410908 : True = term927.
Proof. exact (SYM (@lem2410907)). Qed.
Lemma lem2410909 : term927.
Proof. exact (EQ_MP (@lem2410908) (@lem0)). Qed.
Lemma lem2410910 : term932.
Proof. exact (@lem2410899 (@lem2410909)). Qed.
Lemma lem2410912 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410913 : term902 = term903.
Proof. exact (@lem2410912 term268 term268). Qed.
Lemma lem2410914 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410915 : term905 = term268.
Proof. exact (EQ_MP (@lem2410914) (@lem940073)). Qed.
Lemma lem2410916 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410917 : term903 = term267.
Proof. exact (MK_COMB (@lem2410916) (@lem2410915)). Qed.
Lemma lem2410918 : term902 = term267.
Proof. exact (TRANS (@lem2410913) (@lem2410917)). Qed.
Lemma lem2410920 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2410921 : term897 = term908.
Proof. exact (@lem2410920 term268 term268). Qed.
Lemma lem2410922 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410923 : term905 = term268.
Proof. exact (EQ_MP (@lem2410922) (@lem940073)). Qed.
Lemma lem2410924 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410925 : term903 = term267.
Proof. exact (MK_COMB (@lem2410924) (@lem2410923)). Qed.
Lemma lem2410926 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2410927 : term908 = term885.
Proof. exact (MK_COMB (@lem2410926) (@lem2410925)). Qed.
Lemma lem2410928 : term897 = term885.
Proof. exact (TRANS (@lem2410921) (@lem2410927)). Qed.
Lemma lem2410929 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410930 : term933 = term921.
Proof. exact (MK_COMB (@lem2410929) (@lem2410928)). Qed.
Lemma lem2410931 : term934 = term923.
Proof. exact (MK_COMB (@lem2410930) (@lem2410918)). Qed.
Lemma lem2410933 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2410934 : term923 = term324.
Proof. exact (@lem2410933 term268). Qed.
Lemma lem2410935 : term934 = term324.
Proof. exact (TRANS (@lem2410931) (@lem2410934)). Qed.
Lemma lem2410936 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410937 : term936 = term444.
Proof. exact (MK_COMB (@lem2410936) (@lem2410935)). Qed.
Lemma lem2410938 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2410939 : term937 = term938.
Proof. exact (MK_COMB (@lem2410937) (@lem2410938)). Qed.
Lemma lem2410941 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410942 : term938 = term324.
Proof. exact (@lem2410941 term268). Qed.
Lemma lem2410943 : term937 = term324.
Proof. exact (TRANS (@lem2410939) (@lem2410942)). Qed.
Lemma lem2410945 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2410946 : term902 = term903.
Proof. exact (@lem2410945 term268 term268). Qed.
Lemma lem2410947 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2410948 : term905 = term268.
Proof. exact (EQ_MP (@lem2410947) (@lem940073)). Qed.
Lemma lem2410949 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2410950 : term903 = term267.
Proof. exact (MK_COMB (@lem2410949) (@lem2410948)). Qed.
Lemma lem2410951 : term902 = term267.
Proof. exact (TRANS (@lem2410946) (@lem2410950)). Qed.
Lemma lem2410952 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2410953 : term940 = term938.
Proof. exact (MK_COMB (@lem2410952) (@lem2410951)). Qed.
Lemma lem2410955 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2410956 : term938 = term324.
Proof. exact (@lem2410955 term268). Qed.
Lemma lem2410957 : term940 = term324.
Proof. exact (TRANS (@lem2410953) (@lem2410956)). Qed.
Lemma lem2410958 : term324 = term940.
Proof. exact (SYM (@lem2410957)). Qed.
Lemma lem2410959 : term937 = term940.
Proof. exact (TRANS (@lem2410943) (@lem2410958)). Qed.
Lemma lem2410960 : term924 = term941.
Proof. exact (@lem2410910 (@lem2410959)). Qed.
Lemma lem2410961 : term923 = term941.
Proof. exact (TRANS (@lem2410876) (@lem2410960)). Qed.
Lemma lem2410963 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2410964 : term941 = term324.
Proof. exact (@lem2410963 term324). Qed.
Lemma lem2410965 : term923 = term324.
Proof. exact (TRANS (@lem2410961) (@lem2410964)). Qed.
Lemma lem2410966 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2410967 : term942 = term444.
Proof. exact (MK_COMB (@lem2410966) (@lem2410965)). Qed.
Lemma lem2410968 (x : int) (y : int) (z : int) : (term359 x y z) = (term359 x y z).
Proof. exact (eq_refl (term359 x y z)). Qed.
Lemma lem2410969 (x : int) (y : int) (z : int) : (term997 x y z) = (term998 x y z).
Proof. exact (MK_COMB (@lem2410967) (@lem2410968 x y z)). Qed.
Lemma lem2410970 (x : int) (y : int) (z : int) : (term996 x y z) = (term998 x y z).
Proof. exact (TRANS (@lem2410867 x y z) (@lem2410969 x y z)). Qed.
Lemma lem2410971 (x : int) (y : int) (z : int) : (term998 x y z) = term324.
Proof. exact (@lem1982719 (term359 x y z)). Qed.
Lemma lem2410972 (x : int) (y : int) (z : int) : (term996 x y z) = term324.
Proof. exact (TRANS (@lem2410970 x y z) (@lem2410971 x y z)). Qed.
Lemma lem2410973 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2410974 (x : int) (y : int) (z : int) : (term999 x y z) = term326.
Proof. exact (MK_COMB (@lem2410973) (@lem2410972 x y z)). Qed.
Lemma lem2410975 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2410976 (x : int) (y : int) (z : int) : (term994 x y z) = term948.
Proof. exact (MK_COMB (@lem2410974 x y z) (@lem2410975)). Qed.
Lemma lem2410977 (x : int) (y : int) (z : int) : (term993 x y z) = term948.
Proof. exact (TRANS (@lem2410866 x y z) (@lem2410976 x y z)). Qed.
Lemma lem2410978 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2410979 (x : int) (y : int) (z : int) : (term993 x y z) = term885.
Proof. exact (TRANS (@lem2410977 x y z) (@lem2410978)). Qed.
Lemma lem2410980 (x : int) (y : int) (z : int) : (term988 x y z) = term885.
Proof. exact (TRANS (@lem2410865 x y z) (@lem2410979 x y z)). Qed.
Lemma lem2410981 (x : int) (y : int) (z : int) : (term987 x y z) = term885.
Proof. exact (TRANS (@lem2410820 x y z) (@lem2410980 x y z)). Qed.
Lemma lem2410982 (x : int) (y : int) (z : int) : (term986 x y z) = term885.
Proof. exact (TRANS (@lem2410819 x y z) (@lem2410981 x y z)). Qed.
Lemma lem2410983 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2410984 (x : int) (y : int) (z : int) : (term1000 x y z) = term950.
Proof. exact (MK_COMB (@lem2410983) (@lem2410982 x y z)). Qed.
Lemma lem2410985 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2410986 (x : int) (y : int) (z : int) : (term983 x y z) = term951.
Proof. exact (MK_COMB (@lem2410984 x y z) (@lem2410985)). Qed.
Lemma lem2410987 (x : int) (y : int) (z : int) : (term370 x y z) = term951.
Proof. exact (TRANS (@lem2410780 x y z) (@lem2410986 x y z)). Qed.
Lemma lem2410988 (x : int) (y : int) : (term655 x y) = term952.
Proof. exact (fun_ext (fun z : int => @lem2410987 x y z)). Qed.
Lemma lem2410989 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410990 (x : int) (y : int) : (term666 x y) = term953.
Proof. exact (MK_COMB (@lem2410989) (@lem2410988 x y)). Qed.
Lemma lem2410991 (x : int) : (term677 x) = term954.
Proof. exact (fun_ext (fun y : int => @lem2410990 x y)). Qed.
Lemma lem2410992 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410993 (x : int) : (term688 x) = term955.
Proof. exact (MK_COMB (@lem2410992) (@lem2410991 x)). Qed.
Lemma lem2410994 : term699 = term956.
Proof. exact (fun_ext (fun x : int => @lem2410993 x)). Qed.
Lemma lem2410995 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2410996 : term710 = term957.
Proof. exact (MK_COMB (@lem2410995) (@lem2410994)). Qed.
Lemma lem2410997 (x : int) (y : int) (z : int) : (term383 x y z) = (term1001 x y z).
Proof. exact (@lem1988287 (term359 x y z) (term380 x y z)). Qed.
Lemma lem2410998 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411015 (x : int) (y : int) (z : int) : (term369 x y z) = (term359 x y z).
Proof. exact (@lem1982745 (real_of_int x) (real_of_int y) (real_of_int z)). Qed.
Lemma lem2411016 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411017 (x : int) (y : int) (z : int) : (term379 x y z) = (term361 x y z).
Proof. exact (MK_COMB (@lem2411016) (@lem2411015 x y z)). Qed.
Lemma lem2411020 (x : int) (y : int) (z : int) : (term380 x y z) = (term362 x y z).
Proof. exact (MK_COMB (@lem2411017 x y z) (@lem2410998)). Qed.
Lemma lem2411035 (x : int) (y : int) (z : int) : (term985 x y z) = (term985 x y z).
Proof. exact (eq_refl (term985 x y z)). Qed.
Lemma lem2411036 (x : int) (y : int) (z : int) : (term1002 x y z) = (term987 x y z).
Proof. exact (MK_COMB (@lem2411035 x y z) (@lem2411020 x y z)). Qed.
Lemma lem2411037 (x : int) (y : int) (z : int) : (term987 x y z) = (term988 x y z).
Proof. exact (@lem1982792 (term359 x y z) (term362 x y z)). Qed.
Lemma lem2411038 (x : int) (y : int) (z : int) : (term989 x y z) = (term990 x y z).
Proof. exact (@lem1982781 (term359 x y z) term885 term267). Qed.
Lemma lem2411040 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411041 : term267 = term891.
Proof. exact (@lem2411040 term268). Qed.
Lemma lem2411043 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411044 : term885 = term894.
Proof. exact (@lem2411043 term268). Qed.
Lemma lem2411045 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411046 : term895 = term896.
Proof. exact (MK_COMB (@lem2411045) (@lem2411044)). Qed.
Lemma lem2411047 : term897 = term898.
Proof. exact (MK_COMB (@lem2411046) (@lem2411041)). Qed.
Lemma lem2411048 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2411050 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411051 : term902 = term903.
Proof. exact (@lem2411050 term268 term268). Qed.
Lemma lem2411052 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411053 : term905 = term268.
Proof. exact (EQ_MP (@lem2411052) (@lem940073)). Qed.
Lemma lem2411054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411055 : term903 = term267.
Proof. exact (MK_COMB (@lem2411054) (@lem2411053)). Qed.
Lemma lem2411056 : term902 = term267.
Proof. exact (TRANS (@lem2411051) (@lem2411055)). Qed.
Lemma lem2411058 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411059 : term897 = term908.
Proof. exact (@lem2411058 term268 term268). Qed.
Lemma lem2411060 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411061 : term905 = term268.
Proof. exact (EQ_MP (@lem2411060) (@lem940073)). Qed.
Lemma lem2411062 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411063 : term903 = term267.
Proof. exact (MK_COMB (@lem2411062) (@lem2411061)). Qed.
Lemma lem2411064 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411065 : term908 = term885.
Proof. exact (MK_COMB (@lem2411064) (@lem2411063)). Qed.
Lemma lem2411066 : term897 = term885.
Proof. exact (TRANS (@lem2411059) (@lem2411065)). Qed.
Lemma lem2411067 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2411068 : term909 = term910.
Proof. exact (MK_COMB (@lem2411067) (@lem2411066)). Qed.
Lemma lem2411069 : term899 = term894.
Proof. exact (MK_COMB (@lem2411068) (@lem2411056)). Qed.
Lemma lem2411070 : term898 = term894.
Proof. exact (TRANS (@lem2411048) (@lem2411069)). Qed.
Lemma lem2411071 : term897 = term894.
Proof. exact (TRANS (@lem2411047) (@lem2411070)). Qed.
Lemma lem2411073 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2411074 : term894 = term885.
Proof. exact (@lem2411073 term885). Qed.
Lemma lem2411075 : term897 = term885.
Proof. exact (TRANS (@lem2411071) (@lem2411074)). Qed.
Lemma lem2411078 (x : int) (y : int) (z : int) : (term991 x y z) = (term991 x y z).
Proof. exact (eq_refl (term991 x y z)). Qed.
Lemma lem2411079 (x : int) (y : int) (z : int) : (term990 x y z) = (term992 x y z).
Proof. exact (MK_COMB (@lem2411078 x y z) (@lem2411075)). Qed.
Lemma lem2411080 (x : int) (y : int) (z : int) : (term989 x y z) = (term992 x y z).
Proof. exact (TRANS (@lem2411038 x y z) (@lem2411079 x y z)). Qed.
Lemma lem2411081 (x : int) (y : int) (z : int) : (term361 x y z) = (term361 x y z).
Proof. exact (eq_refl (term361 x y z)). Qed.
Lemma lem2411082 (x : int) (y : int) (z : int) : (term988 x y z) = (term993 x y z).
Proof. exact (MK_COMB (@lem2411081 x y z) (@lem2411080 x y z)). Qed.
Lemma lem2411083 (x : int) (y : int) (z : int) : (term993 x y z) = (term994 x y z).
Proof. exact (@lem1982763 (term359 x y z) (term995 x y z) term885). Qed.
Lemma lem2411084 (x : int) (y : int) (z : int) : (term996 x y z) = (term997 x y z).
Proof. exact (@lem1982715 term885 (term359 x y z)). Qed.
Lemma lem2411086 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411087 : term267 = term891.
Proof. exact (@lem2411086 term268). Qed.
Lemma lem2411089 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411090 : term885 = term894.
Proof. exact (@lem2411089 term268). Qed.
Lemma lem2411091 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411092 : term921 = term922.
Proof. exact (MK_COMB (@lem2411091) (@lem2411090)). Qed.
Lemma lem2411093 : term923 = term924.
Proof. exact (MK_COMB (@lem2411092) (@lem2411087)). Qed.
Lemma lem2411094 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2411096 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411097 : term927 = term928.
Proof. exact (@lem2411096 (NUMERAL 0) term268). Qed.
Lemma lem2411098 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411099 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411100 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411099 h1) (fun h1 : term928 = True => @lem2411098)). Qed.
Lemma lem2411101 : term928 = True.
Proof. exact (EQ_MP (@lem2411100) (@lem2411098)). Qed.
Lemma lem2411102 : term927 = True.
Proof. exact (TRANS (@lem2411097) (@lem2411101)). Qed.
Lemma lem2411103 : True = term927.
Proof. exact (SYM (@lem2411102)). Qed.
Lemma lem2411104 : term927.
Proof. exact (EQ_MP (@lem2411103) (@lem0)). Qed.
Lemma lem2411105 : term930.
Proof. exact (@lem2411094 (@lem2411104)). Qed.
Lemma lem2411107 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411108 : term927 = term928.
Proof. exact (@lem2411107 (NUMERAL 0) term268). Qed.
Lemma lem2411109 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411110 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411111 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411110 h1) (fun h1 : term928 = True => @lem2411109)). Qed.
Lemma lem2411112 : term928 = True.
Proof. exact (EQ_MP (@lem2411111) (@lem2411109)). Qed.
Lemma lem2411113 : term927 = True.
Proof. exact (TRANS (@lem2411108) (@lem2411112)). Qed.
Lemma lem2411114 : True = term927.
Proof. exact (SYM (@lem2411113)). Qed.
Lemma lem2411115 : term927.
Proof. exact (EQ_MP (@lem2411114) (@lem0)). Qed.
Lemma lem2411116 : term931.
Proof. exact (@lem2411105 (@lem2411115)). Qed.
Lemma lem2411118 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411119 : term927 = term928.
Proof. exact (@lem2411118 (NUMERAL 0) term268). Qed.
Lemma lem2411120 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411121 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411122 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411121 h1) (fun h1 : term928 = True => @lem2411120)). Qed.
Lemma lem2411123 : term928 = True.
Proof. exact (EQ_MP (@lem2411122) (@lem2411120)). Qed.
Lemma lem2411124 : term927 = True.
Proof. exact (TRANS (@lem2411119) (@lem2411123)). Qed.
Lemma lem2411125 : True = term927.
Proof. exact (SYM (@lem2411124)). Qed.
Lemma lem2411126 : term927.
Proof. exact (EQ_MP (@lem2411125) (@lem0)). Qed.
Lemma lem2411127 : term932.
Proof. exact (@lem2411116 (@lem2411126)). Qed.
Lemma lem2411129 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411130 : term902 = term903.
Proof. exact (@lem2411129 term268 term268). Qed.
Lemma lem2411131 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411132 : term905 = term268.
Proof. exact (EQ_MP (@lem2411131) (@lem940073)). Qed.
Lemma lem2411133 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411134 : term903 = term267.
Proof. exact (MK_COMB (@lem2411133) (@lem2411132)). Qed.
Lemma lem2411135 : term902 = term267.
Proof. exact (TRANS (@lem2411130) (@lem2411134)). Qed.
Lemma lem2411137 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411138 : term897 = term908.
Proof. exact (@lem2411137 term268 term268). Qed.
Lemma lem2411139 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411140 : term905 = term268.
Proof. exact (EQ_MP (@lem2411139) (@lem940073)). Qed.
Lemma lem2411141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411142 : term903 = term267.
Proof. exact (MK_COMB (@lem2411141) (@lem2411140)). Qed.
Lemma lem2411143 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411144 : term908 = term885.
Proof. exact (MK_COMB (@lem2411143) (@lem2411142)). Qed.
Lemma lem2411145 : term897 = term885.
Proof. exact (TRANS (@lem2411138) (@lem2411144)). Qed.
Lemma lem2411146 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411147 : term933 = term921.
Proof. exact (MK_COMB (@lem2411146) (@lem2411145)). Qed.
Lemma lem2411148 : term934 = term923.
Proof. exact (MK_COMB (@lem2411147) (@lem2411135)). Qed.
Lemma lem2411150 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2411151 : term923 = term324.
Proof. exact (@lem2411150 term268). Qed.
Lemma lem2411152 : term934 = term324.
Proof. exact (TRANS (@lem2411148) (@lem2411151)). Qed.
Lemma lem2411153 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411154 : term936 = term444.
Proof. exact (MK_COMB (@lem2411153) (@lem2411152)). Qed.
Lemma lem2411155 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411156 : term937 = term938.
Proof. exact (MK_COMB (@lem2411154) (@lem2411155)). Qed.
Lemma lem2411158 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411159 : term938 = term324.
Proof. exact (@lem2411158 term268). Qed.
Lemma lem2411160 : term937 = term324.
Proof. exact (TRANS (@lem2411156) (@lem2411159)). Qed.
Lemma lem2411162 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411163 : term902 = term903.
Proof. exact (@lem2411162 term268 term268). Qed.
Lemma lem2411164 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411165 : term905 = term268.
Proof. exact (EQ_MP (@lem2411164) (@lem940073)). Qed.
Lemma lem2411166 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411167 : term903 = term267.
Proof. exact (MK_COMB (@lem2411166) (@lem2411165)). Qed.
Lemma lem2411168 : term902 = term267.
Proof. exact (TRANS (@lem2411163) (@lem2411167)). Qed.
Lemma lem2411169 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2411170 : term940 = term938.
Proof. exact (MK_COMB (@lem2411169) (@lem2411168)). Qed.
Lemma lem2411172 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411173 : term938 = term324.
Proof. exact (@lem2411172 term268). Qed.
Lemma lem2411174 : term940 = term324.
Proof. exact (TRANS (@lem2411170) (@lem2411173)). Qed.
Lemma lem2411175 : term324 = term940.
Proof. exact (SYM (@lem2411174)). Qed.
Lemma lem2411176 : term937 = term940.
Proof. exact (TRANS (@lem2411160) (@lem2411175)). Qed.
Lemma lem2411177 : term924 = term941.
Proof. exact (@lem2411127 (@lem2411176)). Qed.
Lemma lem2411178 : term923 = term941.
Proof. exact (TRANS (@lem2411093) (@lem2411177)). Qed.
Lemma lem2411180 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2411181 : term941 = term324.
Proof. exact (@lem2411180 term324). Qed.
Lemma lem2411182 : term923 = term324.
Proof. exact (TRANS (@lem2411178) (@lem2411181)). Qed.
Lemma lem2411183 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411184 : term942 = term444.
Proof. exact (MK_COMB (@lem2411183) (@lem2411182)). Qed.
Lemma lem2411185 (x : int) (y : int) (z : int) : (term359 x y z) = (term359 x y z).
Proof. exact (eq_refl (term359 x y z)). Qed.
Lemma lem2411186 (x : int) (y : int) (z : int) : (term997 x y z) = (term998 x y z).
Proof. exact (MK_COMB (@lem2411184) (@lem2411185 x y z)). Qed.
Lemma lem2411187 (x : int) (y : int) (z : int) : (term996 x y z) = (term998 x y z).
Proof. exact (TRANS (@lem2411084 x y z) (@lem2411186 x y z)). Qed.
Lemma lem2411188 (x : int) (y : int) (z : int) : (term998 x y z) = term324.
Proof. exact (@lem1982719 (term359 x y z)). Qed.
Lemma lem2411189 (x : int) (y : int) (z : int) : (term996 x y z) = term324.
Proof. exact (TRANS (@lem2411187 x y z) (@lem2411188 x y z)). Qed.
Lemma lem2411190 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411191 (x : int) (y : int) (z : int) : (term999 x y z) = term326.
Proof. exact (MK_COMB (@lem2411190) (@lem2411189 x y z)). Qed.
Lemma lem2411192 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2411193 (x : int) (y : int) (z : int) : (term994 x y z) = term948.
Proof. exact (MK_COMB (@lem2411191 x y z) (@lem2411192)). Qed.
Lemma lem2411194 (x : int) (y : int) (z : int) : (term993 x y z) = term948.
Proof. exact (TRANS (@lem2411083 x y z) (@lem2411193 x y z)). Qed.
Lemma lem2411195 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2411196 (x : int) (y : int) (z : int) : (term993 x y z) = term885.
Proof. exact (TRANS (@lem2411194 x y z) (@lem2411195)). Qed.
Lemma lem2411197 (x : int) (y : int) (z : int) : (term988 x y z) = term885.
Proof. exact (TRANS (@lem2411082 x y z) (@lem2411196 x y z)). Qed.
Lemma lem2411198 (x : int) (y : int) (z : int) : (term987 x y z) = term885.
Proof. exact (TRANS (@lem2411037 x y z) (@lem2411197 x y z)). Qed.
Lemma lem2411199 (x : int) (y : int) (z : int) : (term1002 x y z) = term885.
Proof. exact (TRANS (@lem2411036 x y z) (@lem2411198 x y z)). Qed.
Lemma lem2411200 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2411201 (x : int) (y : int) (z : int) : (term1003 x y z) = term950.
Proof. exact (MK_COMB (@lem2411200) (@lem2411199 x y z)). Qed.
Lemma lem2411202 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2411203 (x : int) (y : int) (z : int) : (term1001 x y z) = term951.
Proof. exact (MK_COMB (@lem2411201 x y z) (@lem2411202)). Qed.
Lemma lem2411204 (x : int) (y : int) (z : int) : (term383 x y z) = term951.
Proof. exact (TRANS (@lem2410997 x y z) (@lem2411203 x y z)). Qed.
Lemma lem2411205 (x : int) (y : int) : (term656 x y) = term952.
Proof. exact (fun_ext (fun z : int => @lem2411204 x y z)). Qed.
Lemma lem2411206 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411207 (x : int) (y : int) : (term671 x y) = term953.
Proof. exact (MK_COMB (@lem2411206) (@lem2411205 x y)). Qed.
Lemma lem2411208 (x : int) : (term678 x) = term954.
Proof. exact (fun_ext (fun y : int => @lem2411207 x y)). Qed.
Lemma lem2411209 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411210 (x : int) : (term693 x) = term955.
Proof. exact (MK_COMB (@lem2411209) (@lem2411208 x)). Qed.
Lemma lem2411211 : term700 = term956.
Proof. exact (fun_ext (fun x : int => @lem2411210 x)). Qed.
Lemma lem2411212 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411213 : term715 = term957.
Proof. exact (MK_COMB (@lem2411212) (@lem2411211)). Qed.
Lemma lem2411214 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2411215 : term712 = term961.
Proof. exact (MK_COMB (@lem2411214) (@lem2410996)). Qed.
Lemma lem2411216 : term716 = term962.
Proof. exact (MK_COMB (@lem2411215) (@lem2411213)). Qed.
Lemma lem2411217 (x : int) (y : int) : (term402 y x) = (term1004 x y).
Proof. exact (@lem1988287 (term355 y x) (term399 x y)). Qed.
Lemma lem2411230 (x : int) (y : int) : (term399 x y) = (term399 x y).
Proof. exact (eq_refl (term399 x y)). Qed.
Lemma lem2411237 (x : int) (y : int) : (term355 y x) = (term355 x y).
Proof. exact (@lem1982747 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2411238 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2411239 (x : int) (y : int) : (term1005 y x) = (term1005 x y).
Proof. exact (MK_COMB (@lem2411238) (@lem2411237 x y)). Qed.
Lemma lem2411240 (x : int) (y : int) : (term1006 x y) = (term1007 x y).
Proof. exact (MK_COMB (@lem2411239 x y) (@lem2411230 x y)). Qed.
Lemma lem2411241 (x : int) (y : int) : (term1007 x y) = (term1008 x y).
Proof. exact (@lem1982792 (term355 x y) (term399 x y)). Qed.
Lemma lem2411242 (x : int) (y : int) : (term1009 x y) = (term1010 x y).
Proof. exact (@lem1982781 (term355 x y) term885 term267). Qed.
Lemma lem2411244 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411245 : term267 = term891.
Proof. exact (@lem2411244 term268). Qed.
Lemma lem2411247 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411248 : term885 = term894.
Proof. exact (@lem2411247 term268). Qed.
Lemma lem2411249 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411250 : term895 = term896.
Proof. exact (MK_COMB (@lem2411249) (@lem2411248)). Qed.
Lemma lem2411251 : term897 = term898.
Proof. exact (MK_COMB (@lem2411250) (@lem2411245)). Qed.
Lemma lem2411252 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2411254 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411255 : term902 = term903.
Proof. exact (@lem2411254 term268 term268). Qed.
Lemma lem2411256 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411257 : term905 = term268.
Proof. exact (EQ_MP (@lem2411256) (@lem940073)). Qed.
Lemma lem2411258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411259 : term903 = term267.
Proof. exact (MK_COMB (@lem2411258) (@lem2411257)). Qed.
Lemma lem2411260 : term902 = term267.
Proof. exact (TRANS (@lem2411255) (@lem2411259)). Qed.
Lemma lem2411262 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411263 : term897 = term908.
Proof. exact (@lem2411262 term268 term268). Qed.
Lemma lem2411264 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411265 : term905 = term268.
Proof. exact (EQ_MP (@lem2411264) (@lem940073)). Qed.
Lemma lem2411266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411267 : term903 = term267.
Proof. exact (MK_COMB (@lem2411266) (@lem2411265)). Qed.
Lemma lem2411268 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411269 : term908 = term885.
Proof. exact (MK_COMB (@lem2411268) (@lem2411267)). Qed.
Lemma lem2411270 : term897 = term885.
Proof. exact (TRANS (@lem2411263) (@lem2411269)). Qed.
Lemma lem2411271 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2411272 : term909 = term910.
Proof. exact (MK_COMB (@lem2411271) (@lem2411270)). Qed.
Lemma lem2411273 : term899 = term894.
Proof. exact (MK_COMB (@lem2411272) (@lem2411260)). Qed.
Lemma lem2411274 : term898 = term894.
Proof. exact (TRANS (@lem2411252) (@lem2411273)). Qed.
Lemma lem2411275 : term897 = term894.
Proof. exact (TRANS (@lem2411251) (@lem2411274)). Qed.
Lemma lem2411277 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2411278 : term894 = term885.
Proof. exact (@lem2411277 term885). Qed.
Lemma lem2411279 : term897 = term885.
Proof. exact (TRANS (@lem2411275) (@lem2411278)). Qed.
Lemma lem2411282 (x : int) (y : int) : (term1011 x y) = (term1011 x y).
Proof. exact (eq_refl (term1011 x y)). Qed.
Lemma lem2411283 (x : int) (y : int) : (term1010 x y) = (term1012 x y).
Proof. exact (MK_COMB (@lem2411282 x y) (@lem2411279)). Qed.
Lemma lem2411284 (x : int) (y : int) : (term1009 x y) = (term1012 x y).
Proof. exact (TRANS (@lem2411242 x y) (@lem2411283 x y)). Qed.
Lemma lem2411285 (x : int) (y : int) : (term398 x y) = (term398 x y).
Proof. exact (eq_refl (term398 x y)). Qed.
Lemma lem2411286 (x : int) (y : int) : (term1008 x y) = (term1013 x y).
Proof. exact (MK_COMB (@lem2411285 x y) (@lem2411284 x y)). Qed.
Lemma lem2411287 (x : int) (y : int) : (term1013 x y) = (term1014 x y).
Proof. exact (@lem1982763 (term355 x y) (term1015 x y) term885). Qed.
Lemma lem2411288 (x : int) (y : int) : (term1016 x y) = (term1017 x y).
Proof. exact (@lem1982715 term885 (term355 x y)). Qed.
Lemma lem2411290 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411291 : term267 = term891.
Proof. exact (@lem2411290 term268). Qed.
Lemma lem2411293 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411294 : term885 = term894.
Proof. exact (@lem2411293 term268). Qed.
Lemma lem2411295 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411296 : term921 = term922.
Proof. exact (MK_COMB (@lem2411295) (@lem2411294)). Qed.
Lemma lem2411297 : term923 = term924.
Proof. exact (MK_COMB (@lem2411296) (@lem2411291)). Qed.
Lemma lem2411298 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2411300 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411301 : term927 = term928.
Proof. exact (@lem2411300 (NUMERAL 0) term268). Qed.
Lemma lem2411302 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411303 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411304 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411303 h1) (fun h1 : term928 = True => @lem2411302)). Qed.
Lemma lem2411305 : term928 = True.
Proof. exact (EQ_MP (@lem2411304) (@lem2411302)). Qed.
Lemma lem2411306 : term927 = True.
Proof. exact (TRANS (@lem2411301) (@lem2411305)). Qed.
Lemma lem2411307 : True = term927.
Proof. exact (SYM (@lem2411306)). Qed.
Lemma lem2411308 : term927.
Proof. exact (EQ_MP (@lem2411307) (@lem0)). Qed.
Lemma lem2411309 : term930.
Proof. exact (@lem2411298 (@lem2411308)). Qed.
Lemma lem2411311 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411312 : term927 = term928.
Proof. exact (@lem2411311 (NUMERAL 0) term268). Qed.
Lemma lem2411313 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411314 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411315 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411314 h1) (fun h1 : term928 = True => @lem2411313)). Qed.
Lemma lem2411316 : term928 = True.
Proof. exact (EQ_MP (@lem2411315) (@lem2411313)). Qed.
Lemma lem2411317 : term927 = True.
Proof. exact (TRANS (@lem2411312) (@lem2411316)). Qed.
Lemma lem2411318 : True = term927.
Proof. exact (SYM (@lem2411317)). Qed.
Lemma lem2411319 : term927.
Proof. exact (EQ_MP (@lem2411318) (@lem0)). Qed.
Lemma lem2411320 : term931.
Proof. exact (@lem2411309 (@lem2411319)). Qed.
Lemma lem2411322 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411323 : term927 = term928.
Proof. exact (@lem2411322 (NUMERAL 0) term268). Qed.
Lemma lem2411324 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411325 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411326 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411325 h1) (fun h1 : term928 = True => @lem2411324)). Qed.
Lemma lem2411327 : term928 = True.
Proof. exact (EQ_MP (@lem2411326) (@lem2411324)). Qed.
Lemma lem2411328 : term927 = True.
Proof. exact (TRANS (@lem2411323) (@lem2411327)). Qed.
Lemma lem2411329 : True = term927.
Proof. exact (SYM (@lem2411328)). Qed.
Lemma lem2411330 : term927.
Proof. exact (EQ_MP (@lem2411329) (@lem0)). Qed.
Lemma lem2411331 : term932.
Proof. exact (@lem2411320 (@lem2411330)). Qed.
Lemma lem2411333 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411334 : term902 = term903.
Proof. exact (@lem2411333 term268 term268). Qed.
Lemma lem2411335 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411336 : term905 = term268.
Proof. exact (EQ_MP (@lem2411335) (@lem940073)). Qed.
Lemma lem2411337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411338 : term903 = term267.
Proof. exact (MK_COMB (@lem2411337) (@lem2411336)). Qed.
Lemma lem2411339 : term902 = term267.
Proof. exact (TRANS (@lem2411334) (@lem2411338)). Qed.
Lemma lem2411341 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411342 : term897 = term908.
Proof. exact (@lem2411341 term268 term268). Qed.
Lemma lem2411343 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411344 : term905 = term268.
Proof. exact (EQ_MP (@lem2411343) (@lem940073)). Qed.
Lemma lem2411345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411346 : term903 = term267.
Proof. exact (MK_COMB (@lem2411345) (@lem2411344)). Qed.
Lemma lem2411347 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411348 : term908 = term885.
Proof. exact (MK_COMB (@lem2411347) (@lem2411346)). Qed.
Lemma lem2411349 : term897 = term885.
Proof. exact (TRANS (@lem2411342) (@lem2411348)). Qed.
Lemma lem2411350 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411351 : term933 = term921.
Proof. exact (MK_COMB (@lem2411350) (@lem2411349)). Qed.
Lemma lem2411352 : term934 = term923.
Proof. exact (MK_COMB (@lem2411351) (@lem2411339)). Qed.
Lemma lem2411354 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2411355 : term923 = term324.
Proof. exact (@lem2411354 term268). Qed.
Lemma lem2411356 : term934 = term324.
Proof. exact (TRANS (@lem2411352) (@lem2411355)). Qed.
Lemma lem2411357 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411358 : term936 = term444.
Proof. exact (MK_COMB (@lem2411357) (@lem2411356)). Qed.
Lemma lem2411359 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411360 : term937 = term938.
Proof. exact (MK_COMB (@lem2411358) (@lem2411359)). Qed.
Lemma lem2411362 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411363 : term938 = term324.
Proof. exact (@lem2411362 term268). Qed.
Lemma lem2411364 : term937 = term324.
Proof. exact (TRANS (@lem2411360) (@lem2411363)). Qed.
Lemma lem2411366 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411367 : term902 = term903.
Proof. exact (@lem2411366 term268 term268). Qed.
Lemma lem2411368 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411369 : term905 = term268.
Proof. exact (EQ_MP (@lem2411368) (@lem940073)). Qed.
Lemma lem2411370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411371 : term903 = term267.
Proof. exact (MK_COMB (@lem2411370) (@lem2411369)). Qed.
Lemma lem2411372 : term902 = term267.
Proof. exact (TRANS (@lem2411367) (@lem2411371)). Qed.
Lemma lem2411373 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2411374 : term940 = term938.
Proof. exact (MK_COMB (@lem2411373) (@lem2411372)). Qed.
Lemma lem2411376 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411377 : term938 = term324.
Proof. exact (@lem2411376 term268). Qed.
Lemma lem2411378 : term940 = term324.
Proof. exact (TRANS (@lem2411374) (@lem2411377)). Qed.
Lemma lem2411379 : term324 = term940.
Proof. exact (SYM (@lem2411378)). Qed.
Lemma lem2411380 : term937 = term940.
Proof. exact (TRANS (@lem2411364) (@lem2411379)). Qed.
Lemma lem2411381 : term924 = term941.
Proof. exact (@lem2411331 (@lem2411380)). Qed.
Lemma lem2411382 : term923 = term941.
Proof. exact (TRANS (@lem2411297) (@lem2411381)). Qed.
Lemma lem2411384 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2411385 : term941 = term324.
Proof. exact (@lem2411384 term324). Qed.
Lemma lem2411386 : term923 = term324.
Proof. exact (TRANS (@lem2411382) (@lem2411385)). Qed.
Lemma lem2411387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411388 : term942 = term444.
Proof. exact (MK_COMB (@lem2411387) (@lem2411386)). Qed.
Lemma lem2411389 (x : int) (y : int) : (term355 x y) = (term355 x y).
Proof. exact (eq_refl (term355 x y)). Qed.
Lemma lem2411390 (x : int) (y : int) : (term1017 x y) = (term1018 x y).
Proof. exact (MK_COMB (@lem2411388) (@lem2411389 x y)). Qed.
Lemma lem2411391 (x : int) (y : int) : (term1016 x y) = (term1018 x y).
Proof. exact (TRANS (@lem2411288 x y) (@lem2411390 x y)). Qed.
Lemma lem2411392 (x : int) (y : int) : (term1018 x y) = term324.
Proof. exact (@lem1982719 (term355 x y)). Qed.
Lemma lem2411393 (x : int) (y : int) : (term1016 x y) = term324.
Proof. exact (TRANS (@lem2411391 x y) (@lem2411392 x y)). Qed.
Lemma lem2411394 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411395 (x : int) (y : int) : (term1019 x y) = term326.
Proof. exact (MK_COMB (@lem2411394) (@lem2411393 x y)). Qed.
Lemma lem2411396 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2411397 (x : int) (y : int) : (term1014 x y) = term948.
Proof. exact (MK_COMB (@lem2411395 x y) (@lem2411396)). Qed.
Lemma lem2411398 (x : int) (y : int) : (term1013 x y) = term948.
Proof. exact (TRANS (@lem2411287 x y) (@lem2411397 x y)). Qed.
Lemma lem2411399 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2411400 (x : int) (y : int) : (term1013 x y) = term885.
Proof. exact (TRANS (@lem2411398 x y) (@lem2411399)). Qed.
Lemma lem2411401 (x : int) (y : int) : (term1008 x y) = term885.
Proof. exact (TRANS (@lem2411286 x y) (@lem2411400 x y)). Qed.
Lemma lem2411402 (x : int) (y : int) : (term1007 x y) = term885.
Proof. exact (TRANS (@lem2411241 x y) (@lem2411401 x y)). Qed.
Lemma lem2411403 (x : int) (y : int) : (term1006 x y) = term885.
Proof. exact (TRANS (@lem2411240 x y) (@lem2411402 x y)). Qed.
Lemma lem2411404 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2411405 (x : int) (y : int) : (term1020 x y) = term950.
Proof. exact (MK_COMB (@lem2411404) (@lem2411403 x y)). Qed.
Lemma lem2411406 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2411407 (x : int) (y : int) : (term1004 x y) = term951.
Proof. exact (MK_COMB (@lem2411405 x y) (@lem2411406)). Qed.
Lemma lem2411408 (y : int) (x : int) : (term402 y x) = term951.
Proof. exact (TRANS (@lem2411217 x y) (@lem2411407 x y)). Qed.
Lemma lem2411409 (x : int) : (term720 x) = term952.
Proof. exact (fun_ext (fun y : int => @lem2411408 y x)). Qed.
Lemma lem2411410 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411411 (x : int) : (term731 x) = term953.
Proof. exact (MK_COMB (@lem2411410) (@lem2411409 x)). Qed.
Lemma lem2411412 : term742 = term954.
Proof. exact (fun_ext (fun x : int => @lem2411411 x)). Qed.
Lemma lem2411413 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411414 : term753 = term955.
Proof. exact (MK_COMB (@lem2411413) (@lem2411412)). Qed.
Lemma lem2411415 (y : int) (x : int) : (term402 x y) = (term1004 y x).
Proof. exact (@lem1988287 (term355 x y) (term399 y x)). Qed.
Lemma lem2411416 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411423 (x : int) (y : int) : (term355 y x) = (term355 x y).
Proof. exact (@lem1982747 (real_of_int x) (real_of_int y)). Qed.
Lemma lem2411424 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411425 (x : int) (y : int) : (term398 y x) = (term398 x y).
Proof. exact (MK_COMB (@lem2411424) (@lem2411423 x y)). Qed.
Lemma lem2411428 (x : int) (y : int) : (term399 y x) = (term399 x y).
Proof. exact (MK_COMB (@lem2411425 x y) (@lem2411416)). Qed.
Lemma lem2411437 (x : int) (y : int) : (term1005 x y) = (term1005 x y).
Proof. exact (eq_refl (term1005 x y)). Qed.
Lemma lem2411438 (x : int) (y : int) : (term1006 y x) = (term1007 x y).
Proof. exact (MK_COMB (@lem2411437 x y) (@lem2411428 x y)). Qed.
Lemma lem2411439 (x : int) (y : int) : (term1007 x y) = (term1008 x y).
Proof. exact (@lem1982792 (term355 x y) (term399 x y)). Qed.
Lemma lem2411440 (x : int) (y : int) : (term1009 x y) = (term1010 x y).
Proof. exact (@lem1982781 (term355 x y) term885 term267). Qed.
Lemma lem2411442 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411443 : term267 = term891.
Proof. exact (@lem2411442 term268). Qed.
Lemma lem2411445 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411446 : term885 = term894.
Proof. exact (@lem2411445 term268). Qed.
Lemma lem2411447 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411448 : term895 = term896.
Proof. exact (MK_COMB (@lem2411447) (@lem2411446)). Qed.
Lemma lem2411449 : term897 = term898.
Proof. exact (MK_COMB (@lem2411448) (@lem2411443)). Qed.
Lemma lem2411450 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2411452 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411453 : term902 = term903.
Proof. exact (@lem2411452 term268 term268). Qed.
Lemma lem2411454 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411455 : term905 = term268.
Proof. exact (EQ_MP (@lem2411454) (@lem940073)). Qed.
Lemma lem2411456 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411457 : term903 = term267.
Proof. exact (MK_COMB (@lem2411456) (@lem2411455)). Qed.
Lemma lem2411458 : term902 = term267.
Proof. exact (TRANS (@lem2411453) (@lem2411457)). Qed.
Lemma lem2411460 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411461 : term897 = term908.
Proof. exact (@lem2411460 term268 term268). Qed.
Lemma lem2411462 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411463 : term905 = term268.
Proof. exact (EQ_MP (@lem2411462) (@lem940073)). Qed.
Lemma lem2411464 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411465 : term903 = term267.
Proof. exact (MK_COMB (@lem2411464) (@lem2411463)). Qed.
Lemma lem2411466 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411467 : term908 = term885.
Proof. exact (MK_COMB (@lem2411466) (@lem2411465)). Qed.
Lemma lem2411468 : term897 = term885.
Proof. exact (TRANS (@lem2411461) (@lem2411467)). Qed.
Lemma lem2411469 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2411470 : term909 = term910.
Proof. exact (MK_COMB (@lem2411469) (@lem2411468)). Qed.
Lemma lem2411471 : term899 = term894.
Proof. exact (MK_COMB (@lem2411470) (@lem2411458)). Qed.
Lemma lem2411472 : term898 = term894.
Proof. exact (TRANS (@lem2411450) (@lem2411471)). Qed.
Lemma lem2411473 : term897 = term894.
Proof. exact (TRANS (@lem2411449) (@lem2411472)). Qed.
Lemma lem2411475 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2411476 : term894 = term885.
Proof. exact (@lem2411475 term885). Qed.
Lemma lem2411477 : term897 = term885.
Proof. exact (TRANS (@lem2411473) (@lem2411476)). Qed.
Lemma lem2411480 (x : int) (y : int) : (term1011 x y) = (term1011 x y).
Proof. exact (eq_refl (term1011 x y)). Qed.
Lemma lem2411481 (x : int) (y : int) : (term1010 x y) = (term1012 x y).
Proof. exact (MK_COMB (@lem2411480 x y) (@lem2411477)). Qed.
Lemma lem2411482 (x : int) (y : int) : (term1009 x y) = (term1012 x y).
Proof. exact (TRANS (@lem2411440 x y) (@lem2411481 x y)). Qed.
Lemma lem2411483 (x : int) (y : int) : (term398 x y) = (term398 x y).
Proof. exact (eq_refl (term398 x y)). Qed.
Lemma lem2411484 (x : int) (y : int) : (term1008 x y) = (term1013 x y).
Proof. exact (MK_COMB (@lem2411483 x y) (@lem2411482 x y)). Qed.
Lemma lem2411485 (x : int) (y : int) : (term1013 x y) = (term1014 x y).
Proof. exact (@lem1982763 (term355 x y) (term1015 x y) term885). Qed.
Lemma lem2411486 (x : int) (y : int) : (term1016 x y) = (term1017 x y).
Proof. exact (@lem1982715 term885 (term355 x y)). Qed.
Lemma lem2411488 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411489 : term267 = term891.
Proof. exact (@lem2411488 term268). Qed.
Lemma lem2411491 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411492 : term885 = term894.
Proof. exact (@lem2411491 term268). Qed.
Lemma lem2411493 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411494 : term921 = term922.
Proof. exact (MK_COMB (@lem2411493) (@lem2411492)). Qed.
Lemma lem2411495 : term923 = term924.
Proof. exact (MK_COMB (@lem2411494) (@lem2411489)). Qed.
Lemma lem2411496 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2411498 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411499 : term927 = term928.
Proof. exact (@lem2411498 (NUMERAL 0) term268). Qed.
Lemma lem2411500 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411501 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411502 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411501 h1) (fun h1 : term928 = True => @lem2411500)). Qed.
Lemma lem2411503 : term928 = True.
Proof. exact (EQ_MP (@lem2411502) (@lem2411500)). Qed.
Lemma lem2411504 : term927 = True.
Proof. exact (TRANS (@lem2411499) (@lem2411503)). Qed.
Lemma lem2411505 : True = term927.
Proof. exact (SYM (@lem2411504)). Qed.
Lemma lem2411506 : term927.
Proof. exact (EQ_MP (@lem2411505) (@lem0)). Qed.
Lemma lem2411507 : term930.
Proof. exact (@lem2411496 (@lem2411506)). Qed.
Lemma lem2411509 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411510 : term927 = term928.
Proof. exact (@lem2411509 (NUMERAL 0) term268). Qed.
Lemma lem2411511 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411512 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411513 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411512 h1) (fun h1 : term928 = True => @lem2411511)). Qed.
Lemma lem2411514 : term928 = True.
Proof. exact (EQ_MP (@lem2411513) (@lem2411511)). Qed.
Lemma lem2411515 : term927 = True.
Proof. exact (TRANS (@lem2411510) (@lem2411514)). Qed.
Lemma lem2411516 : True = term927.
Proof. exact (SYM (@lem2411515)). Qed.
Lemma lem2411517 : term927.
Proof. exact (EQ_MP (@lem2411516) (@lem0)). Qed.
Lemma lem2411518 : term931.
Proof. exact (@lem2411507 (@lem2411517)). Qed.
Lemma lem2411520 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411521 : term927 = term928.
Proof. exact (@lem2411520 (NUMERAL 0) term268). Qed.
Lemma lem2411522 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411523 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411524 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411523 h1) (fun h1 : term928 = True => @lem2411522)). Qed.
Lemma lem2411525 : term928 = True.
Proof. exact (EQ_MP (@lem2411524) (@lem2411522)). Qed.
Lemma lem2411526 : term927 = True.
Proof. exact (TRANS (@lem2411521) (@lem2411525)). Qed.
Lemma lem2411527 : True = term927.
Proof. exact (SYM (@lem2411526)). Qed.
Lemma lem2411528 : term927.
Proof. exact (EQ_MP (@lem2411527) (@lem0)). Qed.
Lemma lem2411529 : term932.
Proof. exact (@lem2411518 (@lem2411528)). Qed.
Lemma lem2411531 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411532 : term902 = term903.
Proof. exact (@lem2411531 term268 term268). Qed.
Lemma lem2411533 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411534 : term905 = term268.
Proof. exact (EQ_MP (@lem2411533) (@lem940073)). Qed.
Lemma lem2411535 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411536 : term903 = term267.
Proof. exact (MK_COMB (@lem2411535) (@lem2411534)). Qed.
Lemma lem2411537 : term902 = term267.
Proof. exact (TRANS (@lem2411532) (@lem2411536)). Qed.
Lemma lem2411539 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411540 : term897 = term908.
Proof. exact (@lem2411539 term268 term268). Qed.
Lemma lem2411541 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411542 : term905 = term268.
Proof. exact (EQ_MP (@lem2411541) (@lem940073)). Qed.
Lemma lem2411543 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411544 : term903 = term267.
Proof. exact (MK_COMB (@lem2411543) (@lem2411542)). Qed.
Lemma lem2411545 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411546 : term908 = term885.
Proof. exact (MK_COMB (@lem2411545) (@lem2411544)). Qed.
Lemma lem2411547 : term897 = term885.
Proof. exact (TRANS (@lem2411540) (@lem2411546)). Qed.
Lemma lem2411548 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411549 : term933 = term921.
Proof. exact (MK_COMB (@lem2411548) (@lem2411547)). Qed.
Lemma lem2411550 : term934 = term923.
Proof. exact (MK_COMB (@lem2411549) (@lem2411537)). Qed.
Lemma lem2411552 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2411553 : term923 = term324.
Proof. exact (@lem2411552 term268). Qed.
Lemma lem2411554 : term934 = term324.
Proof. exact (TRANS (@lem2411550) (@lem2411553)). Qed.
Lemma lem2411555 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411556 : term936 = term444.
Proof. exact (MK_COMB (@lem2411555) (@lem2411554)). Qed.
Lemma lem2411557 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411558 : term937 = term938.
Proof. exact (MK_COMB (@lem2411556) (@lem2411557)). Qed.
Lemma lem2411560 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411561 : term938 = term324.
Proof. exact (@lem2411560 term268). Qed.
Lemma lem2411562 : term937 = term324.
Proof. exact (TRANS (@lem2411558) (@lem2411561)). Qed.
Lemma lem2411564 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411565 : term902 = term903.
Proof. exact (@lem2411564 term268 term268). Qed.
Lemma lem2411566 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411567 : term905 = term268.
Proof. exact (EQ_MP (@lem2411566) (@lem940073)). Qed.
Lemma lem2411568 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411569 : term903 = term267.
Proof. exact (MK_COMB (@lem2411568) (@lem2411567)). Qed.
Lemma lem2411570 : term902 = term267.
Proof. exact (TRANS (@lem2411565) (@lem2411569)). Qed.
Lemma lem2411571 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2411572 : term940 = term938.
Proof. exact (MK_COMB (@lem2411571) (@lem2411570)). Qed.
Lemma lem2411574 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411575 : term938 = term324.
Proof. exact (@lem2411574 term268). Qed.
Lemma lem2411576 : term940 = term324.
Proof. exact (TRANS (@lem2411572) (@lem2411575)). Qed.
Lemma lem2411577 : term324 = term940.
Proof. exact (SYM (@lem2411576)). Qed.
Lemma lem2411578 : term937 = term940.
Proof. exact (TRANS (@lem2411562) (@lem2411577)). Qed.
Lemma lem2411579 : term924 = term941.
Proof. exact (@lem2411529 (@lem2411578)). Qed.
Lemma lem2411580 : term923 = term941.
Proof. exact (TRANS (@lem2411495) (@lem2411579)). Qed.
Lemma lem2411582 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2411583 : term941 = term324.
Proof. exact (@lem2411582 term324). Qed.
Lemma lem2411584 : term923 = term324.
Proof. exact (TRANS (@lem2411580) (@lem2411583)). Qed.
Lemma lem2411585 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411586 : term942 = term444.
Proof. exact (MK_COMB (@lem2411585) (@lem2411584)). Qed.
Lemma lem2411587 (x : int) (y : int) : (term355 x y) = (term355 x y).
Proof. exact (eq_refl (term355 x y)). Qed.
Lemma lem2411588 (x : int) (y : int) : (term1017 x y) = (term1018 x y).
Proof. exact (MK_COMB (@lem2411586) (@lem2411587 x y)). Qed.
Lemma lem2411589 (x : int) (y : int) : (term1016 x y) = (term1018 x y).
Proof. exact (TRANS (@lem2411486 x y) (@lem2411588 x y)). Qed.
Lemma lem2411590 (x : int) (y : int) : (term1018 x y) = term324.
Proof. exact (@lem1982719 (term355 x y)). Qed.
Lemma lem2411591 (x : int) (y : int) : (term1016 x y) = term324.
Proof. exact (TRANS (@lem2411589 x y) (@lem2411590 x y)). Qed.
Lemma lem2411592 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411593 (x : int) (y : int) : (term1019 x y) = term326.
Proof. exact (MK_COMB (@lem2411592) (@lem2411591 x y)). Qed.
Lemma lem2411594 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2411595 (x : int) (y : int) : (term1014 x y) = term948.
Proof. exact (MK_COMB (@lem2411593 x y) (@lem2411594)). Qed.
Lemma lem2411596 (x : int) (y : int) : (term1013 x y) = term948.
Proof. exact (TRANS (@lem2411485 x y) (@lem2411595 x y)). Qed.
Lemma lem2411597 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2411598 (x : int) (y : int) : (term1013 x y) = term885.
Proof. exact (TRANS (@lem2411596 x y) (@lem2411597)). Qed.
Lemma lem2411599 (x : int) (y : int) : (term1008 x y) = term885.
Proof. exact (TRANS (@lem2411484 x y) (@lem2411598 x y)). Qed.
Lemma lem2411600 (x : int) (y : int) : (term1007 x y) = term885.
Proof. exact (TRANS (@lem2411439 x y) (@lem2411599 x y)). Qed.
Lemma lem2411601 (y : int) (x : int) : (term1006 y x) = term885.
Proof. exact (TRANS (@lem2411438 x y) (@lem2411600 x y)). Qed.
Lemma lem2411602 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2411603 (y : int) (x : int) : (term1020 y x) = term950.
Proof. exact (MK_COMB (@lem2411602) (@lem2411601 y x)). Qed.
Lemma lem2411604 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2411605 (y : int) (x : int) : (term1004 y x) = term951.
Proof. exact (MK_COMB (@lem2411603 y x) (@lem2411604)). Qed.
Lemma lem2411606 (x : int) (y : int) : (term402 x y) = term951.
Proof. exact (TRANS (@lem2411415 y x) (@lem2411605 y x)). Qed.
Lemma lem2411607 (x : int) : (term721 x) = term952.
Proof. exact (fun_ext (fun y : int => @lem2411606 x y)). Qed.
Lemma lem2411608 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411609 (x : int) : (term736 x) = term953.
Proof. exact (MK_COMB (@lem2411608) (@lem2411607 x)). Qed.
Lemma lem2411610 : term743 = term954.
Proof. exact (fun_ext (fun x : int => @lem2411609 x)). Qed.
Lemma lem2411611 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411612 : term758 = term955.
Proof. exact (MK_COMB (@lem2411611) (@lem2411610)). Qed.
Lemma lem2411613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2411614 : term755 = term969.
Proof. exact (MK_COMB (@lem2411613) (@lem2411414)). Qed.
Lemma lem2411615 : term759 = term970.
Proof. exact (MK_COMB (@lem2411614) (@lem2411612)). Qed.
Lemma lem2411616 (x : int) : (term426 x) = (term1021 x).
Proof. exact (@lem1988287 (real_of_int x) (term423 x)). Qed.
Lemma lem2411617 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411624 (x : int) : (term420 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2411625 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411626 (x : int) : (term422 x) = (term261 x).
Proof. exact (MK_COMB (@lem2411625) (@lem2411624 x)). Qed.
Lemma lem2411629 (x : int) : (term423 x) = (term341 x).
Proof. exact (MK_COMB (@lem2411626 x) (@lem2411617)). Qed.
Lemma lem2411632 (x : int) : (term972 x) = (term972 x).
Proof. exact (eq_refl (term972 x)). Qed.
Lemma lem2411633 (x : int) : (term1022 x) = (term974 x).
Proof. exact (MK_COMB (@lem2411632 x) (@lem2411629 x)). Qed.
Lemma lem2411634 (x : int) : (term974 x) = (term975 x).
Proof. exact (@lem1982792 (real_of_int x) (term341 x)). Qed.
Lemma lem2411635 (x : int) : (term888 x) = (term889 x).
Proof. exact (@lem1982781 (real_of_int x) term885 term267). Qed.
Lemma lem2411637 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411638 : term267 = term891.
Proof. exact (@lem2411637 term268). Qed.
Lemma lem2411640 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411641 : term885 = term894.
Proof. exact (@lem2411640 term268). Qed.
Lemma lem2411642 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411643 : term895 = term896.
Proof. exact (MK_COMB (@lem2411642) (@lem2411641)). Qed.
Lemma lem2411644 : term897 = term898.
Proof. exact (MK_COMB (@lem2411643) (@lem2411638)). Qed.
Lemma lem2411645 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2411647 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411648 : term902 = term903.
Proof. exact (@lem2411647 term268 term268). Qed.
Lemma lem2411649 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411650 : term905 = term268.
Proof. exact (EQ_MP (@lem2411649) (@lem940073)). Qed.
Lemma lem2411651 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411652 : term903 = term267.
Proof. exact (MK_COMB (@lem2411651) (@lem2411650)). Qed.
Lemma lem2411653 : term902 = term267.
Proof. exact (TRANS (@lem2411648) (@lem2411652)). Qed.
Lemma lem2411655 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411656 : term897 = term908.
Proof. exact (@lem2411655 term268 term268). Qed.
Lemma lem2411657 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411658 : term905 = term268.
Proof. exact (EQ_MP (@lem2411657) (@lem940073)). Qed.
Lemma lem2411659 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411660 : term903 = term267.
Proof. exact (MK_COMB (@lem2411659) (@lem2411658)). Qed.
Lemma lem2411661 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411662 : term908 = term885.
Proof. exact (MK_COMB (@lem2411661) (@lem2411660)). Qed.
Lemma lem2411663 : term897 = term885.
Proof. exact (TRANS (@lem2411656) (@lem2411662)). Qed.
Lemma lem2411664 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2411665 : term909 = term910.
Proof. exact (MK_COMB (@lem2411664) (@lem2411663)). Qed.
Lemma lem2411666 : term899 = term894.
Proof. exact (MK_COMB (@lem2411665) (@lem2411653)). Qed.
Lemma lem2411667 : term898 = term894.
Proof. exact (TRANS (@lem2411645) (@lem2411666)). Qed.
Lemma lem2411668 : term897 = term894.
Proof. exact (TRANS (@lem2411644) (@lem2411667)). Qed.
Lemma lem2411670 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2411671 : term894 = term885.
Proof. exact (@lem2411670 term885). Qed.
Lemma lem2411672 : term897 = term885.
Proof. exact (TRANS (@lem2411668) (@lem2411671)). Qed.
Lemma lem2411675 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2411676 (x : int) : (term889 x) = (term913 x).
Proof. exact (MK_COMB (@lem2411675 x) (@lem2411672)). Qed.
Lemma lem2411677 (x : int) : (term888 x) = (term913 x).
Proof. exact (TRANS (@lem2411635 x) (@lem2411676 x)). Qed.
Lemma lem2411678 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2411679 (x : int) : (term975 x) = (term946 x).
Proof. exact (MK_COMB (@lem2411678 x) (@lem2411677 x)). Qed.
Lemma lem2411680 (x : int) : (term946 x) = (term947 x).
Proof. exact (@lem1982763 (real_of_int x) (term918 x) term885). Qed.
Lemma lem2411681 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2411683 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411684 : term267 = term891.
Proof. exact (@lem2411683 term268). Qed.
Lemma lem2411686 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411687 : term885 = term894.
Proof. exact (@lem2411686 term268). Qed.
Lemma lem2411688 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411689 : term921 = term922.
Proof. exact (MK_COMB (@lem2411688) (@lem2411687)). Qed.
Lemma lem2411690 : term923 = term924.
Proof. exact (MK_COMB (@lem2411689) (@lem2411684)). Qed.
Lemma lem2411691 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2411693 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411694 : term927 = term928.
Proof. exact (@lem2411693 (NUMERAL 0) term268). Qed.
Lemma lem2411695 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411696 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411697 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411696 h1) (fun h1 : term928 = True => @lem2411695)). Qed.
Lemma lem2411698 : term928 = True.
Proof. exact (EQ_MP (@lem2411697) (@lem2411695)). Qed.
Lemma lem2411699 : term927 = True.
Proof. exact (TRANS (@lem2411694) (@lem2411698)). Qed.
Lemma lem2411700 : True = term927.
Proof. exact (SYM (@lem2411699)). Qed.
Lemma lem2411701 : term927.
Proof. exact (EQ_MP (@lem2411700) (@lem0)). Qed.
Lemma lem2411702 : term930.
Proof. exact (@lem2411691 (@lem2411701)). Qed.
Lemma lem2411704 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411705 : term927 = term928.
Proof. exact (@lem2411704 (NUMERAL 0) term268). Qed.
Lemma lem2411706 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411707 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411708 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411707 h1) (fun h1 : term928 = True => @lem2411706)). Qed.
Lemma lem2411709 : term928 = True.
Proof. exact (EQ_MP (@lem2411708) (@lem2411706)). Qed.
Lemma lem2411710 : term927 = True.
Proof. exact (TRANS (@lem2411705) (@lem2411709)). Qed.
Lemma lem2411711 : True = term927.
Proof. exact (SYM (@lem2411710)). Qed.
Lemma lem2411712 : term927.
Proof. exact (EQ_MP (@lem2411711) (@lem0)). Qed.
Lemma lem2411713 : term931.
Proof. exact (@lem2411702 (@lem2411712)). Qed.
Lemma lem2411715 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411716 : term927 = term928.
Proof. exact (@lem2411715 (NUMERAL 0) term268). Qed.
Lemma lem2411717 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411718 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411719 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411718 h1) (fun h1 : term928 = True => @lem2411717)). Qed.
Lemma lem2411720 : term928 = True.
Proof. exact (EQ_MP (@lem2411719) (@lem2411717)). Qed.
Lemma lem2411721 : term927 = True.
Proof. exact (TRANS (@lem2411716) (@lem2411720)). Qed.
Lemma lem2411722 : True = term927.
Proof. exact (SYM (@lem2411721)). Qed.
Lemma lem2411723 : term927.
Proof. exact (EQ_MP (@lem2411722) (@lem0)). Qed.
Lemma lem2411724 : term932.
Proof. exact (@lem2411713 (@lem2411723)). Qed.
Lemma lem2411726 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411727 : term902 = term903.
Proof. exact (@lem2411726 term268 term268). Qed.
Lemma lem2411728 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411729 : term905 = term268.
Proof. exact (EQ_MP (@lem2411728) (@lem940073)). Qed.
Lemma lem2411730 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411731 : term903 = term267.
Proof. exact (MK_COMB (@lem2411730) (@lem2411729)). Qed.
Lemma lem2411732 : term902 = term267.
Proof. exact (TRANS (@lem2411727) (@lem2411731)). Qed.
Lemma lem2411734 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411735 : term897 = term908.
Proof. exact (@lem2411734 term268 term268). Qed.
Lemma lem2411736 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411737 : term905 = term268.
Proof. exact (EQ_MP (@lem2411736) (@lem940073)). Qed.
Lemma lem2411738 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411739 : term903 = term267.
Proof. exact (MK_COMB (@lem2411738) (@lem2411737)). Qed.
Lemma lem2411740 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411741 : term908 = term885.
Proof. exact (MK_COMB (@lem2411740) (@lem2411739)). Qed.
Lemma lem2411742 : term897 = term885.
Proof. exact (TRANS (@lem2411735) (@lem2411741)). Qed.
Lemma lem2411743 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411744 : term933 = term921.
Proof. exact (MK_COMB (@lem2411743) (@lem2411742)). Qed.
Lemma lem2411745 : term934 = term923.
Proof. exact (MK_COMB (@lem2411744) (@lem2411732)). Qed.
Lemma lem2411747 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2411748 : term923 = term324.
Proof. exact (@lem2411747 term268). Qed.
Lemma lem2411749 : term934 = term324.
Proof. exact (TRANS (@lem2411745) (@lem2411748)). Qed.
Lemma lem2411750 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411751 : term936 = term444.
Proof. exact (MK_COMB (@lem2411750) (@lem2411749)). Qed.
Lemma lem2411752 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411753 : term937 = term938.
Proof. exact (MK_COMB (@lem2411751) (@lem2411752)). Qed.
Lemma lem2411755 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411756 : term938 = term324.
Proof. exact (@lem2411755 term268). Qed.
Lemma lem2411757 : term937 = term324.
Proof. exact (TRANS (@lem2411753) (@lem2411756)). Qed.
Lemma lem2411759 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411760 : term902 = term903.
Proof. exact (@lem2411759 term268 term268). Qed.
Lemma lem2411761 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411762 : term905 = term268.
Proof. exact (EQ_MP (@lem2411761) (@lem940073)). Qed.
Lemma lem2411763 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411764 : term903 = term267.
Proof. exact (MK_COMB (@lem2411763) (@lem2411762)). Qed.
Lemma lem2411765 : term902 = term267.
Proof. exact (TRANS (@lem2411760) (@lem2411764)). Qed.
Lemma lem2411766 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2411767 : term940 = term938.
Proof. exact (MK_COMB (@lem2411766) (@lem2411765)). Qed.
Lemma lem2411769 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411770 : term938 = term324.
Proof. exact (@lem2411769 term268). Qed.
Lemma lem2411771 : term940 = term324.
Proof. exact (TRANS (@lem2411767) (@lem2411770)). Qed.
Lemma lem2411772 : term324 = term940.
Proof. exact (SYM (@lem2411771)). Qed.
Lemma lem2411773 : term937 = term940.
Proof. exact (TRANS (@lem2411757) (@lem2411772)). Qed.
Lemma lem2411774 : term924 = term941.
Proof. exact (@lem2411724 (@lem2411773)). Qed.
Lemma lem2411775 : term923 = term941.
Proof. exact (TRANS (@lem2411690) (@lem2411774)). Qed.
Lemma lem2411777 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2411778 : term941 = term324.
Proof. exact (@lem2411777 term324). Qed.
Lemma lem2411779 : term923 = term324.
Proof. exact (TRANS (@lem2411775) (@lem2411778)). Qed.
Lemma lem2411780 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411781 : term942 = term444.
Proof. exact (MK_COMB (@lem2411780) (@lem2411779)). Qed.
Lemma lem2411782 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2411783 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2411781) (@lem2411782 x)). Qed.
Lemma lem2411784 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2411681 x) (@lem2411783 x)). Qed.
Lemma lem2411785 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2411786 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2411784 x) (@lem2411785 x)). Qed.
Lemma lem2411787 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411788 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2411787) (@lem2411786 x)). Qed.
Lemma lem2411789 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2411790 (x : int) : (term947 x) = term948.
Proof. exact (MK_COMB (@lem2411788 x) (@lem2411789)). Qed.
Lemma lem2411791 (x : int) : (term946 x) = term948.
Proof. exact (TRANS (@lem2411680 x) (@lem2411790 x)). Qed.
Lemma lem2411792 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2411793 (x : int) : (term946 x) = term885.
Proof. exact (TRANS (@lem2411791 x) (@lem2411792)). Qed.
Lemma lem2411794 (x : int) : (term975 x) = term885.
Proof. exact (TRANS (@lem2411679 x) (@lem2411793 x)). Qed.
Lemma lem2411795 (x : int) : (term974 x) = term885.
Proof. exact (TRANS (@lem2411634 x) (@lem2411794 x)). Qed.
Lemma lem2411796 (x : int) : (term1022 x) = term885.
Proof. exact (TRANS (@lem2411633 x) (@lem2411795 x)). Qed.
Lemma lem2411797 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2411798 (x : int) : (term1023 x) = term950.
Proof. exact (MK_COMB (@lem2411797) (@lem2411796 x)). Qed.
Lemma lem2411799 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2411800 (x : int) : (term1021 x) = term951.
Proof. exact (MK_COMB (@lem2411798 x) (@lem2411799)). Qed.
Lemma lem2411801 (x : int) : (term426 x) = term951.
Proof. exact (TRANS (@lem2411616 x) (@lem2411800 x)). Qed.
Lemma lem2411802 : term763 = term952.
Proof. exact (fun_ext (fun x : int => @lem2411801 x)). Qed.
Lemma lem2411803 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411804 : term774 = term953.
Proof. exact (MK_COMB (@lem2411803) (@lem2411802)). Qed.
Lemma lem2411805 (x : int) : (term431 x) = (term1024 x).
Proof. exact (@lem1988287 (term420 x) (term341 x)). Qed.
Lemma lem2411812 (x : int) : (term341 x) = (term341 x).
Proof. exact (eq_refl (term341 x)). Qed.
Lemma lem2411819 (x : int) : (term420 x) = (real_of_int x).
Proof. exact (@lem1982733 (real_of_int x)). Qed.
Lemma lem2411820 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2411821 (x : int) : (term1025 x) = (term972 x).
Proof. exact (MK_COMB (@lem2411820) (@lem2411819 x)). Qed.
Lemma lem2411822 (x : int) : (term1026 x) = (term974 x).
Proof. exact (MK_COMB (@lem2411821 x) (@lem2411812 x)). Qed.
Lemma lem2411823 (x : int) : (term974 x) = (term975 x).
Proof. exact (@lem1982792 (real_of_int x) (term341 x)). Qed.
Lemma lem2411824 (x : int) : (term888 x) = (term889 x).
Proof. exact (@lem1982781 (real_of_int x) term885 term267). Qed.
Lemma lem2411826 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411827 : term267 = term891.
Proof. exact (@lem2411826 term268). Qed.
Lemma lem2411829 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411830 : term885 = term894.
Proof. exact (@lem2411829 term268). Qed.
Lemma lem2411831 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411832 : term895 = term896.
Proof. exact (MK_COMB (@lem2411831) (@lem2411830)). Qed.
Lemma lem2411833 : term897 = term898.
Proof. exact (MK_COMB (@lem2411832) (@lem2411827)). Qed.
Lemma lem2411834 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2411836 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411837 : term902 = term903.
Proof. exact (@lem2411836 term268 term268). Qed.
Lemma lem2411838 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411839 : term905 = term268.
Proof. exact (EQ_MP (@lem2411838) (@lem940073)). Qed.
Lemma lem2411840 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411841 : term903 = term267.
Proof. exact (MK_COMB (@lem2411840) (@lem2411839)). Qed.
Lemma lem2411842 : term902 = term267.
Proof. exact (TRANS (@lem2411837) (@lem2411841)). Qed.
Lemma lem2411844 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411845 : term897 = term908.
Proof. exact (@lem2411844 term268 term268). Qed.
Lemma lem2411846 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411847 : term905 = term268.
Proof. exact (EQ_MP (@lem2411846) (@lem940073)). Qed.
Lemma lem2411848 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411849 : term903 = term267.
Proof. exact (MK_COMB (@lem2411848) (@lem2411847)). Qed.
Lemma lem2411850 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411851 : term908 = term885.
Proof. exact (MK_COMB (@lem2411850) (@lem2411849)). Qed.
Lemma lem2411852 : term897 = term885.
Proof. exact (TRANS (@lem2411845) (@lem2411851)). Qed.
Lemma lem2411853 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2411854 : term909 = term910.
Proof. exact (MK_COMB (@lem2411853) (@lem2411852)). Qed.
Lemma lem2411855 : term899 = term894.
Proof. exact (MK_COMB (@lem2411854) (@lem2411842)). Qed.
Lemma lem2411856 : term898 = term894.
Proof. exact (TRANS (@lem2411834) (@lem2411855)). Qed.
Lemma lem2411857 : term897 = term894.
Proof. exact (TRANS (@lem2411833) (@lem2411856)). Qed.
Lemma lem2411859 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2411860 : term894 = term885.
Proof. exact (@lem2411859 term885). Qed.
Lemma lem2411861 : term897 = term885.
Proof. exact (TRANS (@lem2411857) (@lem2411860)). Qed.
Lemma lem2411864 (x : int) : (term912 x) = (term912 x).
Proof. exact (eq_refl (term912 x)). Qed.
Lemma lem2411865 (x : int) : (term889 x) = (term913 x).
Proof. exact (MK_COMB (@lem2411864 x) (@lem2411861)). Qed.
Lemma lem2411866 (x : int) : (term888 x) = (term913 x).
Proof. exact (TRANS (@lem2411824 x) (@lem2411865 x)). Qed.
Lemma lem2411867 (x : int) : (term261 x) = (term261 x).
Proof. exact (eq_refl (term261 x)). Qed.
Lemma lem2411868 (x : int) : (term975 x) = (term946 x).
Proof. exact (MK_COMB (@lem2411867 x) (@lem2411866 x)). Qed.
Lemma lem2411869 (x : int) : (term946 x) = (term947 x).
Proof. exact (@lem1982763 (real_of_int x) (term918 x) term885). Qed.
Lemma lem2411870 (x : int) : (term919 x) = (term920 x).
Proof. exact (@lem1982715 term885 (real_of_int x)). Qed.
Lemma lem2411872 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2411873 : term267 = term891.
Proof. exact (@lem2411872 term268). Qed.
Lemma lem2411875 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2411876 : term885 = term894.
Proof. exact (@lem2411875 term268). Qed.
Lemma lem2411877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411878 : term921 = term922.
Proof. exact (MK_COMB (@lem2411877) (@lem2411876)). Qed.
Lemma lem2411879 : term923 = term924.
Proof. exact (MK_COMB (@lem2411878) (@lem2411873)). Qed.
Lemma lem2411880 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2411882 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411883 : term927 = term928.
Proof. exact (@lem2411882 (NUMERAL 0) term268). Qed.
Lemma lem2411884 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411885 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411886 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411885 h1) (fun h1 : term928 = True => @lem2411884)). Qed.
Lemma lem2411887 : term928 = True.
Proof. exact (EQ_MP (@lem2411886) (@lem2411884)). Qed.
Lemma lem2411888 : term927 = True.
Proof. exact (TRANS (@lem2411883) (@lem2411887)). Qed.
Lemma lem2411889 : True = term927.
Proof. exact (SYM (@lem2411888)). Qed.
Lemma lem2411890 : term927.
Proof. exact (EQ_MP (@lem2411889) (@lem0)). Qed.
Lemma lem2411891 : term930.
Proof. exact (@lem2411880 (@lem2411890)). Qed.
Lemma lem2411893 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411894 : term927 = term928.
Proof. exact (@lem2411893 (NUMERAL 0) term268). Qed.
Lemma lem2411895 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411896 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411897 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411896 h1) (fun h1 : term928 = True => @lem2411895)). Qed.
Lemma lem2411898 : term928 = True.
Proof. exact (EQ_MP (@lem2411897) (@lem2411895)). Qed.
Lemma lem2411899 : term927 = True.
Proof. exact (TRANS (@lem2411894) (@lem2411898)). Qed.
Lemma lem2411900 : True = term927.
Proof. exact (SYM (@lem2411899)). Qed.
Lemma lem2411901 : term927.
Proof. exact (EQ_MP (@lem2411900) (@lem0)). Qed.
Lemma lem2411902 : term931.
Proof. exact (@lem2411891 (@lem2411901)). Qed.
Lemma lem2411904 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2411905 : term927 = term928.
Proof. exact (@lem2411904 (NUMERAL 0) term268). Qed.
Lemma lem2411906 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2411907 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2411908 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2411907 h1) (fun h1 : term928 = True => @lem2411906)). Qed.
Lemma lem2411909 : term928 = True.
Proof. exact (EQ_MP (@lem2411908) (@lem2411906)). Qed.
Lemma lem2411910 : term927 = True.
Proof. exact (TRANS (@lem2411905) (@lem2411909)). Qed.
Lemma lem2411911 : True = term927.
Proof. exact (SYM (@lem2411910)). Qed.
Lemma lem2411912 : term927.
Proof. exact (EQ_MP (@lem2411911) (@lem0)). Qed.
Lemma lem2411913 : term932.
Proof. exact (@lem2411902 (@lem2411912)). Qed.
Lemma lem2411915 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411916 : term902 = term903.
Proof. exact (@lem2411915 term268 term268). Qed.
Lemma lem2411917 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411918 : term905 = term268.
Proof. exact (EQ_MP (@lem2411917) (@lem940073)). Qed.
Lemma lem2411919 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411920 : term903 = term267.
Proof. exact (MK_COMB (@lem2411919) (@lem2411918)). Qed.
Lemma lem2411921 : term902 = term267.
Proof. exact (TRANS (@lem2411916) (@lem2411920)). Qed.
Lemma lem2411923 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2411924 : term897 = term908.
Proof. exact (@lem2411923 term268 term268). Qed.
Lemma lem2411925 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411926 : term905 = term268.
Proof. exact (EQ_MP (@lem2411925) (@lem940073)). Qed.
Lemma lem2411927 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411928 : term903 = term267.
Proof. exact (MK_COMB (@lem2411927) (@lem2411926)). Qed.
Lemma lem2411929 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2411930 : term908 = term885.
Proof. exact (MK_COMB (@lem2411929) (@lem2411928)). Qed.
Lemma lem2411931 : term897 = term885.
Proof. exact (TRANS (@lem2411924) (@lem2411930)). Qed.
Lemma lem2411932 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411933 : term933 = term921.
Proof. exact (MK_COMB (@lem2411932) (@lem2411931)). Qed.
Lemma lem2411934 : term934 = term923.
Proof. exact (MK_COMB (@lem2411933) (@lem2411921)). Qed.
Lemma lem2411936 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2411937 : term923 = term324.
Proof. exact (@lem2411936 term268). Qed.
Lemma lem2411938 : term934 = term324.
Proof. exact (TRANS (@lem2411934) (@lem2411937)). Qed.
Lemma lem2411939 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411940 : term936 = term444.
Proof. exact (MK_COMB (@lem2411939) (@lem2411938)). Qed.
Lemma lem2411941 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2411942 : term937 = term938.
Proof. exact (MK_COMB (@lem2411940) (@lem2411941)). Qed.
Lemma lem2411944 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411945 : term938 = term324.
Proof. exact (@lem2411944 term268). Qed.
Lemma lem2411946 : term937 = term324.
Proof. exact (TRANS (@lem2411942) (@lem2411945)). Qed.
Lemma lem2411948 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2411949 : term902 = term903.
Proof. exact (@lem2411948 term268 term268). Qed.
Lemma lem2411950 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2411951 : term905 = term268.
Proof. exact (EQ_MP (@lem2411950) (@lem940073)). Qed.
Lemma lem2411952 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2411953 : term903 = term267.
Proof. exact (MK_COMB (@lem2411952) (@lem2411951)). Qed.
Lemma lem2411954 : term902 = term267.
Proof. exact (TRANS (@lem2411949) (@lem2411953)). Qed.
Lemma lem2411955 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2411956 : term940 = term938.
Proof. exact (MK_COMB (@lem2411955) (@lem2411954)). Qed.
Lemma lem2411958 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2411959 : term938 = term324.
Proof. exact (@lem2411958 term268). Qed.
Lemma lem2411960 : term940 = term324.
Proof. exact (TRANS (@lem2411956) (@lem2411959)). Qed.
Lemma lem2411961 : term324 = term940.
Proof. exact (SYM (@lem2411960)). Qed.
Lemma lem2411962 : term937 = term940.
Proof. exact (TRANS (@lem2411946) (@lem2411961)). Qed.
Lemma lem2411963 : term924 = term941.
Proof. exact (@lem2411913 (@lem2411962)). Qed.
Lemma lem2411964 : term923 = term941.
Proof. exact (TRANS (@lem2411879) (@lem2411963)). Qed.
Lemma lem2411966 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2411967 : term941 = term324.
Proof. exact (@lem2411966 term324). Qed.
Lemma lem2411968 : term923 = term324.
Proof. exact (TRANS (@lem2411964) (@lem2411967)). Qed.
Lemma lem2411969 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2411970 : term942 = term444.
Proof. exact (MK_COMB (@lem2411969) (@lem2411968)). Qed.
Lemma lem2411971 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2411972 (x : int) : (term920 x) = (term445 x).
Proof. exact (MK_COMB (@lem2411970) (@lem2411971 x)). Qed.
Lemma lem2411973 (x : int) : (term919 x) = (term445 x).
Proof. exact (TRANS (@lem2411870 x) (@lem2411972 x)). Qed.
Lemma lem2411974 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2411975 (x : int) : (term919 x) = term324.
Proof. exact (TRANS (@lem2411973 x) (@lem2411974 x)). Qed.
Lemma lem2411976 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2411977 (x : int) : (term943 x) = term326.
Proof. exact (MK_COMB (@lem2411976) (@lem2411975 x)). Qed.
Lemma lem2411978 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2411979 (x : int) : (term947 x) = term948.
Proof. exact (MK_COMB (@lem2411977 x) (@lem2411978)). Qed.
Lemma lem2411980 (x : int) : (term946 x) = term948.
Proof. exact (TRANS (@lem2411869 x) (@lem2411979 x)). Qed.
Lemma lem2411981 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2411982 (x : int) : (term946 x) = term885.
Proof. exact (TRANS (@lem2411980 x) (@lem2411981)). Qed.
Lemma lem2411983 (x : int) : (term975 x) = term885.
Proof. exact (TRANS (@lem2411868 x) (@lem2411982 x)). Qed.
Lemma lem2411984 (x : int) : (term974 x) = term885.
Proof. exact (TRANS (@lem2411823 x) (@lem2411983 x)). Qed.
Lemma lem2411985 (x : int) : (term1026 x) = term885.
Proof. exact (TRANS (@lem2411822 x) (@lem2411984 x)). Qed.
Lemma lem2411986 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2411987 (x : int) : (term1027 x) = term950.
Proof. exact (MK_COMB (@lem2411986) (@lem2411985 x)). Qed.
Lemma lem2411988 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2411989 (x : int) : (term1024 x) = term951.
Proof. exact (MK_COMB (@lem2411987 x) (@lem2411988)). Qed.
Lemma lem2411990 (x : int) : (term431 x) = term951.
Proof. exact (TRANS (@lem2411805 x) (@lem2411989 x)). Qed.
Lemma lem2411991 : term764 = term952.
Proof. exact (fun_ext (fun x : int => @lem2411990 x)). Qed.
Lemma lem2411992 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2411993 : term779 = term953.
Proof. exact (MK_COMB (@lem2411992) (@lem2411991)). Qed.
Lemma lem2411994 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2411995 : term776 = term981.
Proof. exact (MK_COMB (@lem2411994) (@lem2411804)). Qed.
Lemma lem2411996 : term780 = term982.
Proof. exact (MK_COMB (@lem2411995) (@lem2411993)). Qed.
Lemma lem2411997 (x : int) : (term451 x) = (term1028 x).
Proof. exact (@lem1988287 term324 (term448 x)). Qed.
Lemma lem2411998 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2412005 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982729 (real_of_int x)). Qed.
Lemma lem2412006 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412007 (x : int) : (term447 x) = term326.
Proof. exact (MK_COMB (@lem2412006) (@lem2412005 x)). Qed.
Lemma lem2412008 (x : int) : (term448 x) = term459.
Proof. exact (MK_COMB (@lem2412007 x) (@lem2411998)). Qed.
Lemma lem2412009 : term459 = term267.
Proof. exact (@lem1982721 term267). Qed.
Lemma lem2412010 (x : int) : (term448 x) = term267.
Proof. exact (TRANS (@lem2412008 x) (@lem2412009)). Qed.
Lemma lem2412013 : term1029 = term1029.
Proof. exact (eq_refl term1029). Qed.
Lemma lem2412014 (x : int) : (term1030 x) = term1031.
Proof. exact (MK_COMB (@lem2412013) (@lem2412010 x)). Qed.
Lemma lem2412015 : term1031 = term1032.
Proof. exact (@lem1982792 term324 term267). Qed.
Lemma lem2412017 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412018 : term267 = term891.
Proof. exact (@lem2412017 term268). Qed.
Lemma lem2412020 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412021 : term885 = term894.
Proof. exact (@lem2412020 term268). Qed.
Lemma lem2412022 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412023 : term895 = term896.
Proof. exact (MK_COMB (@lem2412022) (@lem2412021)). Qed.
Lemma lem2412024 : term897 = term898.
Proof. exact (MK_COMB (@lem2412023) (@lem2412018)). Qed.
Lemma lem2412025 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2412027 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412028 : term902 = term903.
Proof. exact (@lem2412027 term268 term268). Qed.
Lemma lem2412029 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412030 : term905 = term268.
Proof. exact (EQ_MP (@lem2412029) (@lem940073)). Qed.
Lemma lem2412031 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412032 : term903 = term267.
Proof. exact (MK_COMB (@lem2412031) (@lem2412030)). Qed.
Lemma lem2412033 : term902 = term267.
Proof. exact (TRANS (@lem2412028) (@lem2412032)). Qed.
Lemma lem2412035 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412036 : term897 = term908.
Proof. exact (@lem2412035 term268 term268). Qed.
Lemma lem2412037 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412038 : term905 = term268.
Proof. exact (EQ_MP (@lem2412037) (@lem940073)). Qed.
Lemma lem2412039 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412040 : term903 = term267.
Proof. exact (MK_COMB (@lem2412039) (@lem2412038)). Qed.
Lemma lem2412041 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412042 : term908 = term885.
Proof. exact (MK_COMB (@lem2412041) (@lem2412040)). Qed.
Lemma lem2412043 : term897 = term885.
Proof. exact (TRANS (@lem2412036) (@lem2412042)). Qed.
Lemma lem2412044 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2412045 : term909 = term910.
Proof. exact (MK_COMB (@lem2412044) (@lem2412043)). Qed.
Lemma lem2412046 : term899 = term894.
Proof. exact (MK_COMB (@lem2412045) (@lem2412033)). Qed.
Lemma lem2412047 : term898 = term894.
Proof. exact (TRANS (@lem2412025) (@lem2412046)). Qed.
Lemma lem2412048 : term897 = term894.
Proof. exact (TRANS (@lem2412024) (@lem2412047)). Qed.
Lemma lem2412050 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2412051 : term894 = term885.
Proof. exact (@lem2412050 term885). Qed.
Lemma lem2412052 : term897 = term885.
Proof. exact (TRANS (@lem2412048) (@lem2412051)). Qed.
Lemma lem2412053 : term326 = term326.
Proof. exact (eq_refl term326). Qed.
Lemma lem2412054 : term1032 = term948.
Proof. exact (MK_COMB (@lem2412053) (@lem2412052)). Qed.
Lemma lem2412055 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2412056 : term1032 = term885.
Proof. exact (TRANS (@lem2412054) (@lem2412055)). Qed.
Lemma lem2412057 : term1031 = term885.
Proof. exact (TRANS (@lem2412015) (@lem2412056)). Qed.
Lemma lem2412058 (x : int) : (term1030 x) = term885.
Proof. exact (TRANS (@lem2412014 x) (@lem2412057)). Qed.
Lemma lem2412059 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2412060 (x : int) : (term1033 x) = term950.
Proof. exact (MK_COMB (@lem2412059) (@lem2412058 x)). Qed.
Lemma lem2412061 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2412062 (x : int) : (term1028 x) = term951.
Proof. exact (MK_COMB (@lem2412060 x) (@lem2412061)). Qed.
Lemma lem2412063 (x : int) : (term451 x) = term951.
Proof. exact (TRANS (@lem2411997 x) (@lem2412062 x)). Qed.
Lemma lem2412064 : term784 = term952.
Proof. exact (fun_ext (fun x : int => @lem2412063 x)). Qed.
Lemma lem2412065 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412066 : term795 = term953.
Proof. exact (MK_COMB (@lem2412065) (@lem2412064)). Qed.
Lemma lem2412067 (x : int) : (term462 x) = (term1034 x).
Proof. exact (@lem1988287 (term445 x) term459). Qed.
Lemma lem2412074 : term459 = term267.
Proof. exact (@lem1982721 term267). Qed.
Lemma lem2412081 (x : int) : (term445 x) = term324.
Proof. exact (@lem1982729 (real_of_int x)). Qed.
Lemma lem2412082 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2412083 (x : int) : (term1035 x) = term1029.
Proof. exact (MK_COMB (@lem2412082) (@lem2412081 x)). Qed.
Lemma lem2412084 (x : int) : (term1036 x) = term1031.
Proof. exact (MK_COMB (@lem2412083 x) (@lem2412074)). Qed.
Lemma lem2412085 : term1031 = term1032.
Proof. exact (@lem1982792 term324 term267). Qed.
Lemma lem2412087 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412088 : term267 = term891.
Proof. exact (@lem2412087 term268). Qed.
Lemma lem2412090 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412091 : term885 = term894.
Proof. exact (@lem2412090 term268). Qed.
Lemma lem2412092 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412093 : term895 = term896.
Proof. exact (MK_COMB (@lem2412092) (@lem2412091)). Qed.
Lemma lem2412094 : term897 = term898.
Proof. exact (MK_COMB (@lem2412093) (@lem2412088)). Qed.
Lemma lem2412095 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2412097 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412098 : term902 = term903.
Proof. exact (@lem2412097 term268 term268). Qed.
Lemma lem2412099 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412100 : term905 = term268.
Proof. exact (EQ_MP (@lem2412099) (@lem940073)). Qed.
Lemma lem2412101 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412102 : term903 = term267.
Proof. exact (MK_COMB (@lem2412101) (@lem2412100)). Qed.
Lemma lem2412103 : term902 = term267.
Proof. exact (TRANS (@lem2412098) (@lem2412102)). Qed.
Lemma lem2412105 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412106 : term897 = term908.
Proof. exact (@lem2412105 term268 term268). Qed.
Lemma lem2412107 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412108 : term905 = term268.
Proof. exact (EQ_MP (@lem2412107) (@lem940073)). Qed.
Lemma lem2412109 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412110 : term903 = term267.
Proof. exact (MK_COMB (@lem2412109) (@lem2412108)). Qed.
Lemma lem2412111 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412112 : term908 = term885.
Proof. exact (MK_COMB (@lem2412111) (@lem2412110)). Qed.
Lemma lem2412113 : term897 = term885.
Proof. exact (TRANS (@lem2412106) (@lem2412112)). Qed.
Lemma lem2412114 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2412115 : term909 = term910.
Proof. exact (MK_COMB (@lem2412114) (@lem2412113)). Qed.
Lemma lem2412116 : term899 = term894.
Proof. exact (MK_COMB (@lem2412115) (@lem2412103)). Qed.
Lemma lem2412117 : term898 = term894.
Proof. exact (TRANS (@lem2412095) (@lem2412116)). Qed.
Lemma lem2412118 : term897 = term894.
Proof. exact (TRANS (@lem2412094) (@lem2412117)). Qed.
Lemma lem2412120 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2412121 : term894 = term885.
Proof. exact (@lem2412120 term885). Qed.
Lemma lem2412122 : term897 = term885.
Proof. exact (TRANS (@lem2412118) (@lem2412121)). Qed.
Lemma lem2412123 : term326 = term326.
Proof. exact (eq_refl term326). Qed.
Lemma lem2412124 : term1032 = term948.
Proof. exact (MK_COMB (@lem2412123) (@lem2412122)). Qed.
Lemma lem2412125 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2412126 : term1032 = term885.
Proof. exact (TRANS (@lem2412124) (@lem2412125)). Qed.
Lemma lem2412127 : term1031 = term885.
Proof. exact (TRANS (@lem2412085) (@lem2412126)). Qed.
Lemma lem2412128 (x : int) : (term1036 x) = term885.
Proof. exact (TRANS (@lem2412084 x) (@lem2412127)). Qed.
Lemma lem2412129 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2412130 (x : int) : (term1037 x) = term950.
Proof. exact (MK_COMB (@lem2412129) (@lem2412128 x)). Qed.
Lemma lem2412131 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2412132 (x : int) : (term1034 x) = term951.
Proof. exact (MK_COMB (@lem2412130 x) (@lem2412131)). Qed.
Lemma lem2412133 (x : int) : (term462 x) = term951.
Proof. exact (TRANS (@lem2412067 x) (@lem2412132 x)). Qed.
Lemma lem2412134 : term785 = term952.
Proof. exact (fun_ext (fun x : int => @lem2412133 x)). Qed.
Lemma lem2412135 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412136 : term800 = term953.
Proof. exact (MK_COMB (@lem2412135) (@lem2412134)). Qed.
Lemma lem2412137 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412138 : term797 = term981.
Proof. exact (MK_COMB (@lem2412137) (@lem2412066)). Qed.
Lemma lem2412139 : term801 = term982.
Proof. exact (MK_COMB (@lem2412138) (@lem2412136)). Qed.
Lemma lem2412140 (x : int) (y : int) (z : int) : (term483 y x z) = (term1038 x y z).
Proof. exact (@lem1988287 (term482 y x z) (term477 x y z)). Qed.
Lemma lem2412141 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2412160 (y : int) (x : int) (z : int) : (term474 x y z) = (term482 y x z).
Proof. exact (@lem1982781 (real_of_int y) (real_of_int x) (real_of_int z)). Qed.
Lemma lem2412161 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412162 (y : int) (x : int) (z : int) : (term476 x y z) = (term492 y x z).
Proof. exact (MK_COMB (@lem2412161) (@lem2412160 y x z)). Qed.
Lemma lem2412163 (y : int) (x : int) (z : int) : (term477 x y z) = (term493 y x z).
Proof. exact (MK_COMB (@lem2412162 y x z) (@lem2412141)). Qed.
Lemma lem2412168 (y : int) (x : int) (z : int) : (term493 y x z) = (term1039 y x z).
Proof. exact (@lem1982755 (term355 x y) (term355 x z) term267). Qed.
Lemma lem2412169 (y : int) (x : int) (z : int) : (term477 x y z) = (term1039 y x z).
Proof. exact (TRANS (@lem2412163 y x z) (@lem2412168 y x z)). Qed.
Lemma lem2412190 (y : int) (x : int) (z : int) : (term1040 y x z) = (term1040 y x z).
Proof. exact (eq_refl (term1040 y x z)). Qed.
Lemma lem2412191 (y : int) (x : int) (z : int) : (term1041 x y z) = (term1042 y x z).
Proof. exact (MK_COMB (@lem2412190 y x z) (@lem2412169 y x z)). Qed.
Lemma lem2412192 (y : int) (x : int) (z : int) : (term1042 y x z) = (term1043 y x z).
Proof. exact (@lem1982792 (term482 y x z) (term1039 y x z)). Qed.
Lemma lem2412193 (y : int) (x : int) (z : int) : (term1044 y x z) = (term1045 y x z).
Proof. exact (@lem1982781 (term355 x y) term885 (term399 x z)). Qed.
Lemma lem2412194 (x : int) (z : int) : (term1009 x z) = (term1010 x z).
Proof. exact (@lem1982781 (term355 x z) term885 term267). Qed.
Lemma lem2412196 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412197 : term267 = term891.
Proof. exact (@lem2412196 term268). Qed.
Lemma lem2412199 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412200 : term885 = term894.
Proof. exact (@lem2412199 term268). Qed.
Lemma lem2412201 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412202 : term895 = term896.
Proof. exact (MK_COMB (@lem2412201) (@lem2412200)). Qed.
Lemma lem2412203 : term897 = term898.
Proof. exact (MK_COMB (@lem2412202) (@lem2412197)). Qed.
Lemma lem2412204 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2412206 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412207 : term902 = term903.
Proof. exact (@lem2412206 term268 term268). Qed.
Lemma lem2412208 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412209 : term905 = term268.
Proof. exact (EQ_MP (@lem2412208) (@lem940073)). Qed.
Lemma lem2412210 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412211 : term903 = term267.
Proof. exact (MK_COMB (@lem2412210) (@lem2412209)). Qed.
Lemma lem2412212 : term902 = term267.
Proof. exact (TRANS (@lem2412207) (@lem2412211)). Qed.
Lemma lem2412214 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412215 : term897 = term908.
Proof. exact (@lem2412214 term268 term268). Qed.
Lemma lem2412216 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412217 : term905 = term268.
Proof. exact (EQ_MP (@lem2412216) (@lem940073)). Qed.
Lemma lem2412218 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412219 : term903 = term267.
Proof. exact (MK_COMB (@lem2412218) (@lem2412217)). Qed.
Lemma lem2412220 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412221 : term908 = term885.
Proof. exact (MK_COMB (@lem2412220) (@lem2412219)). Qed.
Lemma lem2412222 : term897 = term885.
Proof. exact (TRANS (@lem2412215) (@lem2412221)). Qed.
Lemma lem2412223 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2412224 : term909 = term910.
Proof. exact (MK_COMB (@lem2412223) (@lem2412222)). Qed.
Lemma lem2412225 : term899 = term894.
Proof. exact (MK_COMB (@lem2412224) (@lem2412212)). Qed.
Lemma lem2412226 : term898 = term894.
Proof. exact (TRANS (@lem2412204) (@lem2412225)). Qed.
Lemma lem2412227 : term897 = term894.
Proof. exact (TRANS (@lem2412203) (@lem2412226)). Qed.
Lemma lem2412229 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2412230 : term894 = term885.
Proof. exact (@lem2412229 term885). Qed.
Lemma lem2412231 : term897 = term885.
Proof. exact (TRANS (@lem2412227) (@lem2412230)). Qed.
Lemma lem2412234 (x : int) (z : int) : (term1011 x z) = (term1011 x z).
Proof. exact (eq_refl (term1011 x z)). Qed.
Lemma lem2412235 (x : int) (z : int) : (term1010 x z) = (term1012 x z).
Proof. exact (MK_COMB (@lem2412234 x z) (@lem2412231)). Qed.
Lemma lem2412236 (x : int) (z : int) : (term1009 x z) = (term1012 x z).
Proof. exact (TRANS (@lem2412194 x z) (@lem2412235 x z)). Qed.
Lemma lem2412239 (x : int) (y : int) : (term1011 x y) = (term1011 x y).
Proof. exact (eq_refl (term1011 x y)). Qed.
Lemma lem2412240 (y : int) (x : int) (z : int) : (term1045 y x z) = (term1046 y x z).
Proof. exact (MK_COMB (@lem2412239 x y) (@lem2412236 x z)). Qed.
Lemma lem2412241 (y : int) (x : int) (z : int) : (term1044 y x z) = (term1046 y x z).
Proof. exact (TRANS (@lem2412193 y x z) (@lem2412240 y x z)). Qed.
Lemma lem2412242 (y : int) (x : int) (z : int) : (term492 y x z) = (term492 y x z).
Proof. exact (eq_refl (term492 y x z)). Qed.
Lemma lem2412243 (y : int) (x : int) (z : int) : (term1043 y x z) = (term1047 y x z).
Proof. exact (MK_COMB (@lem2412242 y x z) (@lem2412241 y x z)). Qed.
Lemma lem2412244 (y : int) (x : int) (z : int) : (term1047 y x z) = (term1048 y x z).
Proof. exact (@lem1982753 (term355 x y) (term1015 x y) (term355 x z) (term1012 x z)). Qed.
Lemma lem2412245 (x : int) (y : int) : (term1016 x y) = (term1017 x y).
Proof. exact (@lem1982715 term885 (term355 x y)). Qed.
Lemma lem2412247 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412248 : term267 = term891.
Proof. exact (@lem2412247 term268). Qed.
Lemma lem2412250 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412251 : term885 = term894.
Proof. exact (@lem2412250 term268). Qed.
Lemma lem2412252 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412253 : term921 = term922.
Proof. exact (MK_COMB (@lem2412252) (@lem2412251)). Qed.
Lemma lem2412254 : term923 = term924.
Proof. exact (MK_COMB (@lem2412253) (@lem2412248)). Qed.
Lemma lem2412255 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2412257 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412258 : term927 = term928.
Proof. exact (@lem2412257 (NUMERAL 0) term268). Qed.
Lemma lem2412259 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412260 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412261 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412260 h1) (fun h1 : term928 = True => @lem2412259)). Qed.
Lemma lem2412262 : term928 = True.
Proof. exact (EQ_MP (@lem2412261) (@lem2412259)). Qed.
Lemma lem2412263 : term927 = True.
Proof. exact (TRANS (@lem2412258) (@lem2412262)). Qed.
Lemma lem2412264 : True = term927.
Proof. exact (SYM (@lem2412263)). Qed.
Lemma lem2412265 : term927.
Proof. exact (EQ_MP (@lem2412264) (@lem0)). Qed.
Lemma lem2412266 : term930.
Proof. exact (@lem2412255 (@lem2412265)). Qed.
Lemma lem2412268 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412269 : term927 = term928.
Proof. exact (@lem2412268 (NUMERAL 0) term268). Qed.
Lemma lem2412270 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412271 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412272 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412271 h1) (fun h1 : term928 = True => @lem2412270)). Qed.
Lemma lem2412273 : term928 = True.
Proof. exact (EQ_MP (@lem2412272) (@lem2412270)). Qed.
Lemma lem2412274 : term927 = True.
Proof. exact (TRANS (@lem2412269) (@lem2412273)). Qed.
Lemma lem2412275 : True = term927.
Proof. exact (SYM (@lem2412274)). Qed.
Lemma lem2412276 : term927.
Proof. exact (EQ_MP (@lem2412275) (@lem0)). Qed.
Lemma lem2412277 : term931.
Proof. exact (@lem2412266 (@lem2412276)). Qed.
Lemma lem2412279 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412280 : term927 = term928.
Proof. exact (@lem2412279 (NUMERAL 0) term268). Qed.
Lemma lem2412281 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412282 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412283 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412282 h1) (fun h1 : term928 = True => @lem2412281)). Qed.
Lemma lem2412284 : term928 = True.
Proof. exact (EQ_MP (@lem2412283) (@lem2412281)). Qed.
Lemma lem2412285 : term927 = True.
Proof. exact (TRANS (@lem2412280) (@lem2412284)). Qed.
Lemma lem2412286 : True = term927.
Proof. exact (SYM (@lem2412285)). Qed.
Lemma lem2412287 : term927.
Proof. exact (EQ_MP (@lem2412286) (@lem0)). Qed.
Lemma lem2412288 : term932.
Proof. exact (@lem2412277 (@lem2412287)). Qed.
Lemma lem2412290 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412291 : term902 = term903.
Proof. exact (@lem2412290 term268 term268). Qed.
Lemma lem2412292 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412293 : term905 = term268.
Proof. exact (EQ_MP (@lem2412292) (@lem940073)). Qed.
Lemma lem2412294 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412295 : term903 = term267.
Proof. exact (MK_COMB (@lem2412294) (@lem2412293)). Qed.
Lemma lem2412296 : term902 = term267.
Proof. exact (TRANS (@lem2412291) (@lem2412295)). Qed.
Lemma lem2412298 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412299 : term897 = term908.
Proof. exact (@lem2412298 term268 term268). Qed.
Lemma lem2412300 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412301 : term905 = term268.
Proof. exact (EQ_MP (@lem2412300) (@lem940073)). Qed.
Lemma lem2412302 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412303 : term903 = term267.
Proof. exact (MK_COMB (@lem2412302) (@lem2412301)). Qed.
Lemma lem2412304 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412305 : term908 = term885.
Proof. exact (MK_COMB (@lem2412304) (@lem2412303)). Qed.
Lemma lem2412306 : term897 = term885.
Proof. exact (TRANS (@lem2412299) (@lem2412305)). Qed.
Lemma lem2412307 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412308 : term933 = term921.
Proof. exact (MK_COMB (@lem2412307) (@lem2412306)). Qed.
Lemma lem2412309 : term934 = term923.
Proof. exact (MK_COMB (@lem2412308) (@lem2412296)). Qed.
Lemma lem2412311 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2412312 : term923 = term324.
Proof. exact (@lem2412311 term268). Qed.
Lemma lem2412313 : term934 = term324.
Proof. exact (TRANS (@lem2412309) (@lem2412312)). Qed.
Lemma lem2412314 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412315 : term936 = term444.
Proof. exact (MK_COMB (@lem2412314) (@lem2412313)). Qed.
Lemma lem2412316 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2412317 : term937 = term938.
Proof. exact (MK_COMB (@lem2412315) (@lem2412316)). Qed.
Lemma lem2412319 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412320 : term938 = term324.
Proof. exact (@lem2412319 term268). Qed.
Lemma lem2412321 : term937 = term324.
Proof. exact (TRANS (@lem2412317) (@lem2412320)). Qed.
Lemma lem2412323 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412324 : term902 = term903.
Proof. exact (@lem2412323 term268 term268). Qed.
Lemma lem2412325 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412326 : term905 = term268.
Proof. exact (EQ_MP (@lem2412325) (@lem940073)). Qed.
Lemma lem2412327 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412328 : term903 = term267.
Proof. exact (MK_COMB (@lem2412327) (@lem2412326)). Qed.
Lemma lem2412329 : term902 = term267.
Proof. exact (TRANS (@lem2412324) (@lem2412328)). Qed.
Lemma lem2412330 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2412331 : term940 = term938.
Proof. exact (MK_COMB (@lem2412330) (@lem2412329)). Qed.
Lemma lem2412333 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412334 : term938 = term324.
Proof. exact (@lem2412333 term268). Qed.
Lemma lem2412335 : term940 = term324.
Proof. exact (TRANS (@lem2412331) (@lem2412334)). Qed.
Lemma lem2412336 : term324 = term940.
Proof. exact (SYM (@lem2412335)). Qed.
Lemma lem2412337 : term937 = term940.
Proof. exact (TRANS (@lem2412321) (@lem2412336)). Qed.
Lemma lem2412338 : term924 = term941.
Proof. exact (@lem2412288 (@lem2412337)). Qed.
Lemma lem2412339 : term923 = term941.
Proof. exact (TRANS (@lem2412254) (@lem2412338)). Qed.
Lemma lem2412341 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2412342 : term941 = term324.
Proof. exact (@lem2412341 term324). Qed.
Lemma lem2412343 : term923 = term324.
Proof. exact (TRANS (@lem2412339) (@lem2412342)). Qed.
Lemma lem2412344 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412345 : term942 = term444.
Proof. exact (MK_COMB (@lem2412344) (@lem2412343)). Qed.
Lemma lem2412346 (x : int) (y : int) : (term355 x y) = (term355 x y).
Proof. exact (eq_refl (term355 x y)). Qed.
Lemma lem2412347 (x : int) (y : int) : (term1017 x y) = (term1018 x y).
Proof. exact (MK_COMB (@lem2412345) (@lem2412346 x y)). Qed.
Lemma lem2412348 (x : int) (y : int) : (term1016 x y) = (term1018 x y).
Proof. exact (TRANS (@lem2412245 x y) (@lem2412347 x y)). Qed.
Lemma lem2412349 (x : int) (y : int) : (term1018 x y) = term324.
Proof. exact (@lem1982719 (term355 x y)). Qed.
Lemma lem2412350 (x : int) (y : int) : (term1016 x y) = term324.
Proof. exact (TRANS (@lem2412348 x y) (@lem2412349 x y)). Qed.
Lemma lem2412351 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412352 (x : int) (y : int) : (term1019 x y) = term326.
Proof. exact (MK_COMB (@lem2412351) (@lem2412350 x y)). Qed.
Lemma lem2412353 (x : int) (z : int) : (term1013 x z) = (term1014 x z).
Proof. exact (@lem1982763 (term355 x z) (term1015 x z) term885). Qed.
Lemma lem2412354 (x : int) (z : int) : (term1016 x z) = (term1017 x z).
Proof. exact (@lem1982715 term885 (term355 x z)). Qed.
Lemma lem2412356 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412357 : term267 = term891.
Proof. exact (@lem2412356 term268). Qed.
Lemma lem2412359 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412360 : term885 = term894.
Proof. exact (@lem2412359 term268). Qed.
Lemma lem2412361 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412362 : term921 = term922.
Proof. exact (MK_COMB (@lem2412361) (@lem2412360)). Qed.
Lemma lem2412363 : term923 = term924.
Proof. exact (MK_COMB (@lem2412362) (@lem2412357)). Qed.
Lemma lem2412364 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2412366 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412367 : term927 = term928.
Proof. exact (@lem2412366 (NUMERAL 0) term268). Qed.
Lemma lem2412368 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412369 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412370 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412369 h1) (fun h1 : term928 = True => @lem2412368)). Qed.
Lemma lem2412371 : term928 = True.
Proof. exact (EQ_MP (@lem2412370) (@lem2412368)). Qed.
Lemma lem2412372 : term927 = True.
Proof. exact (TRANS (@lem2412367) (@lem2412371)). Qed.
Lemma lem2412373 : True = term927.
Proof. exact (SYM (@lem2412372)). Qed.
Lemma lem2412374 : term927.
Proof. exact (EQ_MP (@lem2412373) (@lem0)). Qed.
Lemma lem2412375 : term930.
Proof. exact (@lem2412364 (@lem2412374)). Qed.
Lemma lem2412377 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412378 : term927 = term928.
Proof. exact (@lem2412377 (NUMERAL 0) term268). Qed.
Lemma lem2412379 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412380 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412381 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412380 h1) (fun h1 : term928 = True => @lem2412379)). Qed.
Lemma lem2412382 : term928 = True.
Proof. exact (EQ_MP (@lem2412381) (@lem2412379)). Qed.
Lemma lem2412383 : term927 = True.
Proof. exact (TRANS (@lem2412378) (@lem2412382)). Qed.
Lemma lem2412384 : True = term927.
Proof. exact (SYM (@lem2412383)). Qed.
Lemma lem2412385 : term927.
Proof. exact (EQ_MP (@lem2412384) (@lem0)). Qed.
Lemma lem2412386 : term931.
Proof. exact (@lem2412375 (@lem2412385)). Qed.
Lemma lem2412388 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412389 : term927 = term928.
Proof. exact (@lem2412388 (NUMERAL 0) term268). Qed.
Lemma lem2412390 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412391 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412392 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412391 h1) (fun h1 : term928 = True => @lem2412390)). Qed.
Lemma lem2412393 : term928 = True.
Proof. exact (EQ_MP (@lem2412392) (@lem2412390)). Qed.
Lemma lem2412394 : term927 = True.
Proof. exact (TRANS (@lem2412389) (@lem2412393)). Qed.
Lemma lem2412395 : True = term927.
Proof. exact (SYM (@lem2412394)). Qed.
Lemma lem2412396 : term927.
Proof. exact (EQ_MP (@lem2412395) (@lem0)). Qed.
Lemma lem2412397 : term932.
Proof. exact (@lem2412386 (@lem2412396)). Qed.
Lemma lem2412399 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412400 : term902 = term903.
Proof. exact (@lem2412399 term268 term268). Qed.
Lemma lem2412401 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412402 : term905 = term268.
Proof. exact (EQ_MP (@lem2412401) (@lem940073)). Qed.
Lemma lem2412403 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412404 : term903 = term267.
Proof. exact (MK_COMB (@lem2412403) (@lem2412402)). Qed.
Lemma lem2412405 : term902 = term267.
Proof. exact (TRANS (@lem2412400) (@lem2412404)). Qed.
Lemma lem2412407 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412408 : term897 = term908.
Proof. exact (@lem2412407 term268 term268). Qed.
Lemma lem2412409 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412410 : term905 = term268.
Proof. exact (EQ_MP (@lem2412409) (@lem940073)). Qed.
Lemma lem2412411 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412412 : term903 = term267.
Proof. exact (MK_COMB (@lem2412411) (@lem2412410)). Qed.
Lemma lem2412413 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412414 : term908 = term885.
Proof. exact (MK_COMB (@lem2412413) (@lem2412412)). Qed.
Lemma lem2412415 : term897 = term885.
Proof. exact (TRANS (@lem2412408) (@lem2412414)). Qed.
Lemma lem2412416 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412417 : term933 = term921.
Proof. exact (MK_COMB (@lem2412416) (@lem2412415)). Qed.
Lemma lem2412418 : term934 = term923.
Proof. exact (MK_COMB (@lem2412417) (@lem2412405)). Qed.
Lemma lem2412420 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2412421 : term923 = term324.
Proof. exact (@lem2412420 term268). Qed.
Lemma lem2412422 : term934 = term324.
Proof. exact (TRANS (@lem2412418) (@lem2412421)). Qed.
Lemma lem2412423 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412424 : term936 = term444.
Proof. exact (MK_COMB (@lem2412423) (@lem2412422)). Qed.
Lemma lem2412425 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2412426 : term937 = term938.
Proof. exact (MK_COMB (@lem2412424) (@lem2412425)). Qed.
Lemma lem2412428 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412429 : term938 = term324.
Proof. exact (@lem2412428 term268). Qed.
Lemma lem2412430 : term937 = term324.
Proof. exact (TRANS (@lem2412426) (@lem2412429)). Qed.
Lemma lem2412432 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412433 : term902 = term903.
Proof. exact (@lem2412432 term268 term268). Qed.
Lemma lem2412434 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412435 : term905 = term268.
Proof. exact (EQ_MP (@lem2412434) (@lem940073)). Qed.
Lemma lem2412436 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412437 : term903 = term267.
Proof. exact (MK_COMB (@lem2412436) (@lem2412435)). Qed.
Lemma lem2412438 : term902 = term267.
Proof. exact (TRANS (@lem2412433) (@lem2412437)). Qed.
Lemma lem2412439 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2412440 : term940 = term938.
Proof. exact (MK_COMB (@lem2412439) (@lem2412438)). Qed.
Lemma lem2412442 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412443 : term938 = term324.
Proof. exact (@lem2412442 term268). Qed.
Lemma lem2412444 : term940 = term324.
Proof. exact (TRANS (@lem2412440) (@lem2412443)). Qed.
Lemma lem2412445 : term324 = term940.
Proof. exact (SYM (@lem2412444)). Qed.
Lemma lem2412446 : term937 = term940.
Proof. exact (TRANS (@lem2412430) (@lem2412445)). Qed.
Lemma lem2412447 : term924 = term941.
Proof. exact (@lem2412397 (@lem2412446)). Qed.
Lemma lem2412448 : term923 = term941.
Proof. exact (TRANS (@lem2412363) (@lem2412447)). Qed.
Lemma lem2412450 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2412451 : term941 = term324.
Proof. exact (@lem2412450 term324). Qed.
Lemma lem2412452 : term923 = term324.
Proof. exact (TRANS (@lem2412448) (@lem2412451)). Qed.
Lemma lem2412453 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412454 : term942 = term444.
Proof. exact (MK_COMB (@lem2412453) (@lem2412452)). Qed.
Lemma lem2412455 (x : int) (z : int) : (term355 x z) = (term355 x z).
Proof. exact (eq_refl (term355 x z)). Qed.
Lemma lem2412456 (x : int) (z : int) : (term1017 x z) = (term1018 x z).
Proof. exact (MK_COMB (@lem2412454) (@lem2412455 x z)). Qed.
Lemma lem2412457 (x : int) (z : int) : (term1016 x z) = (term1018 x z).
Proof. exact (TRANS (@lem2412354 x z) (@lem2412456 x z)). Qed.
Lemma lem2412458 (x : int) (z : int) : (term1018 x z) = term324.
Proof. exact (@lem1982719 (term355 x z)). Qed.
Lemma lem2412459 (x : int) (z : int) : (term1016 x z) = term324.
Proof. exact (TRANS (@lem2412457 x z) (@lem2412458 x z)). Qed.
Lemma lem2412460 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412461 (x : int) (z : int) : (term1019 x z) = term326.
Proof. exact (MK_COMB (@lem2412460) (@lem2412459 x z)). Qed.
Lemma lem2412462 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2412463 (x : int) (z : int) : (term1014 x z) = term948.
Proof. exact (MK_COMB (@lem2412461 x z) (@lem2412462)). Qed.
Lemma lem2412464 (x : int) (z : int) : (term1013 x z) = term948.
Proof. exact (TRANS (@lem2412353 x z) (@lem2412463 x z)). Qed.
Lemma lem2412465 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2412466 (x : int) (z : int) : (term1013 x z) = term885.
Proof. exact (TRANS (@lem2412464 x z) (@lem2412465)). Qed.
Lemma lem2412467 (y : int) (x : int) (z : int) : (term1048 y x z) = term948.
Proof. exact (MK_COMB (@lem2412352 x y) (@lem2412466 x z)). Qed.
Lemma lem2412468 (y : int) (x : int) (z : int) : (term1047 y x z) = term948.
Proof. exact (TRANS (@lem2412244 y x z) (@lem2412467 y x z)). Qed.
Lemma lem2412469 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2412470 (y : int) (x : int) (z : int) : (term1047 y x z) = term885.
Proof. exact (TRANS (@lem2412468 y x z) (@lem2412469)). Qed.
Lemma lem2412471 (y : int) (x : int) (z : int) : (term1043 y x z) = term885.
Proof. exact (TRANS (@lem2412243 y x z) (@lem2412470 y x z)). Qed.
Lemma lem2412472 (y : int) (x : int) (z : int) : (term1042 y x z) = term885.
Proof. exact (TRANS (@lem2412192 y x z) (@lem2412471 y x z)). Qed.
Lemma lem2412473 (x : int) (y : int) (z : int) : (term1041 x y z) = term885.
Proof. exact (TRANS (@lem2412191 y x z) (@lem2412472 y x z)). Qed.
Lemma lem2412474 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2412475 (x : int) (y : int) (z : int) : (term1049 x y z) = term950.
Proof. exact (MK_COMB (@lem2412474) (@lem2412473 x y z)). Qed.
Lemma lem2412476 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2412477 (x : int) (y : int) (z : int) : (term1038 x y z) = term951.
Proof. exact (MK_COMB (@lem2412475 x y z) (@lem2412476)). Qed.
Lemma lem2412478 (y : int) (x : int) (z : int) : (term483 y x z) = term951.
Proof. exact (TRANS (@lem2412140 x y z) (@lem2412477 x y z)). Qed.
Lemma lem2412479 (y : int) (x : int) : (term805 y x) = term952.
Proof. exact (fun_ext (fun z : int => @lem2412478 y x z)). Qed.
Lemma lem2412480 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412481 (y : int) (x : int) : (term816 y x) = term953.
Proof. exact (MK_COMB (@lem2412480) (@lem2412479 y x)). Qed.
Lemma lem2412482 (x : int) : (term827 x) = term954.
Proof. exact (fun_ext (fun y : int => @lem2412481 y x)). Qed.
Lemma lem2412483 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412484 (x : int) : (term838 x) = term955.
Proof. exact (MK_COMB (@lem2412483) (@lem2412482 x)). Qed.
Lemma lem2412485 : term849 = term956.
Proof. exact (fun_ext (fun x : int => @lem2412484 x)). Qed.
Lemma lem2412486 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412487 : term860 = term957.
Proof. exact (MK_COMB (@lem2412486) (@lem2412485)). Qed.
Lemma lem2412488 (y : int) (x : int) (z : int) : (term496 x y z) = (term1050 y x z).
Proof. exact (@lem1988287 (term474 x y z) (term493 y x z)). Qed.
Lemma lem2412517 (y : int) (x : int) (z : int) : (term493 y x z) = (term1039 y x z).
Proof. exact (@lem1982755 (term355 x y) (term355 x z) term267). Qed.
Lemma lem2412536 (y : int) (x : int) (z : int) : (term474 x y z) = (term482 y x z).
Proof. exact (@lem1982781 (real_of_int y) (real_of_int x) (real_of_int z)). Qed.
Lemma lem2412537 : real_sub = real_sub.
Proof. exact (eq_refl real_sub). Qed.
Lemma lem2412538 (y : int) (x : int) (z : int) : (term1051 x y z) = (term1040 y x z).
Proof. exact (MK_COMB (@lem2412537) (@lem2412536 y x z)). Qed.
Lemma lem2412539 (y : int) (x : int) (z : int) : (term1052 y x z) = (term1042 y x z).
Proof. exact (MK_COMB (@lem2412538 y x z) (@lem2412517 y x z)). Qed.
Lemma lem2412540 (y : int) (x : int) (z : int) : (term1042 y x z) = (term1043 y x z).
Proof. exact (@lem1982792 (term482 y x z) (term1039 y x z)). Qed.
Lemma lem2412541 (y : int) (x : int) (z : int) : (term1044 y x z) = (term1045 y x z).
Proof. exact (@lem1982781 (term355 x y) term885 (term399 x z)). Qed.
Lemma lem2412542 (x : int) (z : int) : (term1009 x z) = (term1010 x z).
Proof. exact (@lem1982781 (term355 x z) term885 term267). Qed.
Lemma lem2412544 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412545 : term267 = term891.
Proof. exact (@lem2412544 term268). Qed.
Lemma lem2412547 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412548 : term885 = term894.
Proof. exact (@lem2412547 term268). Qed.
Lemma lem2412549 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412550 : term895 = term896.
Proof. exact (MK_COMB (@lem2412549) (@lem2412548)). Qed.
Lemma lem2412551 : term897 = term898.
Proof. exact (MK_COMB (@lem2412550) (@lem2412545)). Qed.
Lemma lem2412552 : term898 = term899.
Proof. exact (@lem1981613 term885 term267 term267 term267). Qed.
Lemma lem2412554 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412555 : term902 = term903.
Proof. exact (@lem2412554 term268 term268). Qed.
Lemma lem2412556 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412557 : term905 = term268.
Proof. exact (EQ_MP (@lem2412556) (@lem940073)). Qed.
Lemma lem2412558 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412559 : term903 = term267.
Proof. exact (MK_COMB (@lem2412558) (@lem2412557)). Qed.
Lemma lem2412560 : term902 = term267.
Proof. exact (TRANS (@lem2412555) (@lem2412559)). Qed.
Lemma lem2412562 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412563 : term897 = term908.
Proof. exact (@lem2412562 term268 term268). Qed.
Lemma lem2412564 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412565 : term905 = term268.
Proof. exact (EQ_MP (@lem2412564) (@lem940073)). Qed.
Lemma lem2412566 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412567 : term903 = term267.
Proof. exact (MK_COMB (@lem2412566) (@lem2412565)). Qed.
Lemma lem2412568 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412569 : term908 = term885.
Proof. exact (MK_COMB (@lem2412568) (@lem2412567)). Qed.
Lemma lem2412570 : term897 = term885.
Proof. exact (TRANS (@lem2412563) (@lem2412569)). Qed.
Lemma lem2412571 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2412572 : term909 = term910.
Proof. exact (MK_COMB (@lem2412571) (@lem2412570)). Qed.
Lemma lem2412573 : term899 = term894.
Proof. exact (MK_COMB (@lem2412572) (@lem2412560)). Qed.
Lemma lem2412574 : term898 = term894.
Proof. exact (TRANS (@lem2412552) (@lem2412573)). Qed.
Lemma lem2412575 : term897 = term894.
Proof. exact (TRANS (@lem2412551) (@lem2412574)). Qed.
Lemma lem2412577 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2412578 : term894 = term885.
Proof. exact (@lem2412577 term885). Qed.
Lemma lem2412579 : term897 = term885.
Proof. exact (TRANS (@lem2412575) (@lem2412578)). Qed.
Lemma lem2412582 (x : int) (z : int) : (term1011 x z) = (term1011 x z).
Proof. exact (eq_refl (term1011 x z)). Qed.
Lemma lem2412583 (x : int) (z : int) : (term1010 x z) = (term1012 x z).
Proof. exact (MK_COMB (@lem2412582 x z) (@lem2412579)). Qed.
Lemma lem2412584 (x : int) (z : int) : (term1009 x z) = (term1012 x z).
Proof. exact (TRANS (@lem2412542 x z) (@lem2412583 x z)). Qed.
Lemma lem2412587 (x : int) (y : int) : (term1011 x y) = (term1011 x y).
Proof. exact (eq_refl (term1011 x y)). Qed.
Lemma lem2412588 (y : int) (x : int) (z : int) : (term1045 y x z) = (term1046 y x z).
Proof. exact (MK_COMB (@lem2412587 x y) (@lem2412584 x z)). Qed.
Lemma lem2412589 (y : int) (x : int) (z : int) : (term1044 y x z) = (term1046 y x z).
Proof. exact (TRANS (@lem2412541 y x z) (@lem2412588 y x z)). Qed.
Lemma lem2412590 (y : int) (x : int) (z : int) : (term492 y x z) = (term492 y x z).
Proof. exact (eq_refl (term492 y x z)). Qed.
Lemma lem2412591 (y : int) (x : int) (z : int) : (term1043 y x z) = (term1047 y x z).
Proof. exact (MK_COMB (@lem2412590 y x z) (@lem2412589 y x z)). Qed.
Lemma lem2412592 (y : int) (x : int) (z : int) : (term1047 y x z) = (term1048 y x z).
Proof. exact (@lem1982753 (term355 x y) (term1015 x y) (term355 x z) (term1012 x z)). Qed.
Lemma lem2412593 (x : int) (y : int) : (term1016 x y) = (term1017 x y).
Proof. exact (@lem1982715 term885 (term355 x y)). Qed.
Lemma lem2412595 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412596 : term267 = term891.
Proof. exact (@lem2412595 term268). Qed.
Lemma lem2412598 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412599 : term885 = term894.
Proof. exact (@lem2412598 term268). Qed.
Lemma lem2412600 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412601 : term921 = term922.
Proof. exact (MK_COMB (@lem2412600) (@lem2412599)). Qed.
Lemma lem2412602 : term923 = term924.
Proof. exact (MK_COMB (@lem2412601) (@lem2412596)). Qed.
Lemma lem2412603 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2412605 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412606 : term927 = term928.
Proof. exact (@lem2412605 (NUMERAL 0) term268). Qed.
Lemma lem2412607 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412608 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412609 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412608 h1) (fun h1 : term928 = True => @lem2412607)). Qed.
Lemma lem2412610 : term928 = True.
Proof. exact (EQ_MP (@lem2412609) (@lem2412607)). Qed.
Lemma lem2412611 : term927 = True.
Proof. exact (TRANS (@lem2412606) (@lem2412610)). Qed.
Lemma lem2412612 : True = term927.
Proof. exact (SYM (@lem2412611)). Qed.
Lemma lem2412613 : term927.
Proof. exact (EQ_MP (@lem2412612) (@lem0)). Qed.
Lemma lem2412614 : term930.
Proof. exact (@lem2412603 (@lem2412613)). Qed.
Lemma lem2412616 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412617 : term927 = term928.
Proof. exact (@lem2412616 (NUMERAL 0) term268). Qed.
Lemma lem2412618 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412619 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412620 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412619 h1) (fun h1 : term928 = True => @lem2412618)). Qed.
Lemma lem2412621 : term928 = True.
Proof. exact (EQ_MP (@lem2412620) (@lem2412618)). Qed.
Lemma lem2412622 : term927 = True.
Proof. exact (TRANS (@lem2412617) (@lem2412621)). Qed.
Lemma lem2412623 : True = term927.
Proof. exact (SYM (@lem2412622)). Qed.
Lemma lem2412624 : term927.
Proof. exact (EQ_MP (@lem2412623) (@lem0)). Qed.
Lemma lem2412625 : term931.
Proof. exact (@lem2412614 (@lem2412624)). Qed.
Lemma lem2412627 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412628 : term927 = term928.
Proof. exact (@lem2412627 (NUMERAL 0) term268). Qed.
Lemma lem2412629 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412630 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412631 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412630 h1) (fun h1 : term928 = True => @lem2412629)). Qed.
Lemma lem2412632 : term928 = True.
Proof. exact (EQ_MP (@lem2412631) (@lem2412629)). Qed.
Lemma lem2412633 : term927 = True.
Proof. exact (TRANS (@lem2412628) (@lem2412632)). Qed.
Lemma lem2412634 : True = term927.
Proof. exact (SYM (@lem2412633)). Qed.
Lemma lem2412635 : term927.
Proof. exact (EQ_MP (@lem2412634) (@lem0)). Qed.
Lemma lem2412636 : term932.
Proof. exact (@lem2412625 (@lem2412635)). Qed.
Lemma lem2412638 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412639 : term902 = term903.
Proof. exact (@lem2412638 term268 term268). Qed.
Lemma lem2412640 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412641 : term905 = term268.
Proof. exact (EQ_MP (@lem2412640) (@lem940073)). Qed.
Lemma lem2412642 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412643 : term903 = term267.
Proof. exact (MK_COMB (@lem2412642) (@lem2412641)). Qed.
Lemma lem2412644 : term902 = term267.
Proof. exact (TRANS (@lem2412639) (@lem2412643)). Qed.
Lemma lem2412646 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412647 : term897 = term908.
Proof. exact (@lem2412646 term268 term268). Qed.
Lemma lem2412648 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412649 : term905 = term268.
Proof. exact (EQ_MP (@lem2412648) (@lem940073)). Qed.
Lemma lem2412650 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412651 : term903 = term267.
Proof. exact (MK_COMB (@lem2412650) (@lem2412649)). Qed.
Lemma lem2412652 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412653 : term908 = term885.
Proof. exact (MK_COMB (@lem2412652) (@lem2412651)). Qed.
Lemma lem2412654 : term897 = term885.
Proof. exact (TRANS (@lem2412647) (@lem2412653)). Qed.
Lemma lem2412655 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412656 : term933 = term921.
Proof. exact (MK_COMB (@lem2412655) (@lem2412654)). Qed.
Lemma lem2412657 : term934 = term923.
Proof. exact (MK_COMB (@lem2412656) (@lem2412644)). Qed.
Lemma lem2412659 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2412660 : term923 = term324.
Proof. exact (@lem2412659 term268). Qed.
Lemma lem2412661 : term934 = term324.
Proof. exact (TRANS (@lem2412657) (@lem2412660)). Qed.
Lemma lem2412662 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412663 : term936 = term444.
Proof. exact (MK_COMB (@lem2412662) (@lem2412661)). Qed.
Lemma lem2412664 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2412665 : term937 = term938.
Proof. exact (MK_COMB (@lem2412663) (@lem2412664)). Qed.
Lemma lem2412667 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412668 : term938 = term324.
Proof. exact (@lem2412667 term268). Qed.
Lemma lem2412669 : term937 = term324.
Proof. exact (TRANS (@lem2412665) (@lem2412668)). Qed.
Lemma lem2412671 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412672 : term902 = term903.
Proof. exact (@lem2412671 term268 term268). Qed.
Lemma lem2412673 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412674 : term905 = term268.
Proof. exact (EQ_MP (@lem2412673) (@lem940073)). Qed.
Lemma lem2412675 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412676 : term903 = term267.
Proof. exact (MK_COMB (@lem2412675) (@lem2412674)). Qed.
Lemma lem2412677 : term902 = term267.
Proof. exact (TRANS (@lem2412672) (@lem2412676)). Qed.
Lemma lem2412678 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2412679 : term940 = term938.
Proof. exact (MK_COMB (@lem2412678) (@lem2412677)). Qed.
Lemma lem2412681 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412682 : term938 = term324.
Proof. exact (@lem2412681 term268). Qed.
Lemma lem2412683 : term940 = term324.
Proof. exact (TRANS (@lem2412679) (@lem2412682)). Qed.
Lemma lem2412684 : term324 = term940.
Proof. exact (SYM (@lem2412683)). Qed.
Lemma lem2412685 : term937 = term940.
Proof. exact (TRANS (@lem2412669) (@lem2412684)). Qed.
Lemma lem2412686 : term924 = term941.
Proof. exact (@lem2412636 (@lem2412685)). Qed.
Lemma lem2412687 : term923 = term941.
Proof. exact (TRANS (@lem2412602) (@lem2412686)). Qed.
Lemma lem2412689 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2412690 : term941 = term324.
Proof. exact (@lem2412689 term324). Qed.
Lemma lem2412691 : term923 = term324.
Proof. exact (TRANS (@lem2412687) (@lem2412690)). Qed.
Lemma lem2412692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412693 : term942 = term444.
Proof. exact (MK_COMB (@lem2412692) (@lem2412691)). Qed.
Lemma lem2412694 (x : int) (y : int) : (term355 x y) = (term355 x y).
Proof. exact (eq_refl (term355 x y)). Qed.
Lemma lem2412695 (x : int) (y : int) : (term1017 x y) = (term1018 x y).
Proof. exact (MK_COMB (@lem2412693) (@lem2412694 x y)). Qed.
Lemma lem2412696 (x : int) (y : int) : (term1016 x y) = (term1018 x y).
Proof. exact (TRANS (@lem2412593 x y) (@lem2412695 x y)). Qed.
Lemma lem2412697 (x : int) (y : int) : (term1018 x y) = term324.
Proof. exact (@lem1982719 (term355 x y)). Qed.
Lemma lem2412698 (x : int) (y : int) : (term1016 x y) = term324.
Proof. exact (TRANS (@lem2412696 x y) (@lem2412697 x y)). Qed.
Lemma lem2412699 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412700 (x : int) (y : int) : (term1019 x y) = term326.
Proof. exact (MK_COMB (@lem2412699) (@lem2412698 x y)). Qed.
Lemma lem2412701 (x : int) (z : int) : (term1013 x z) = (term1014 x z).
Proof. exact (@lem1982763 (term355 x z) (term1015 x z) term885). Qed.
Lemma lem2412702 (x : int) (z : int) : (term1016 x z) = (term1017 x z).
Proof. exact (@lem1982715 term885 (term355 x z)). Qed.
Lemma lem2412704 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2412705 : term267 = term891.
Proof. exact (@lem2412704 term268). Qed.
Lemma lem2412707 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2412708 : term885 = term894.
Proof. exact (@lem2412707 term268). Qed.
Lemma lem2412709 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412710 : term921 = term922.
Proof. exact (MK_COMB (@lem2412709) (@lem2412708)). Qed.
Lemma lem2412711 : term923 = term924.
Proof. exact (MK_COMB (@lem2412710) (@lem2412705)). Qed.
Lemma lem2412712 : term925.
Proof. exact (@lem1981473 term885 term267 term267 term267 term324 term267). Qed.
Lemma lem2412714 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412715 : term927 = term928.
Proof. exact (@lem2412714 (NUMERAL 0) term268). Qed.
Lemma lem2412716 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412717 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412718 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412717 h1) (fun h1 : term928 = True => @lem2412716)). Qed.
Lemma lem2412719 : term928 = True.
Proof. exact (EQ_MP (@lem2412718) (@lem2412716)). Qed.
Lemma lem2412720 : term927 = True.
Proof. exact (TRANS (@lem2412715) (@lem2412719)). Qed.
Lemma lem2412721 : True = term927.
Proof. exact (SYM (@lem2412720)). Qed.
Lemma lem2412722 : term927.
Proof. exact (EQ_MP (@lem2412721) (@lem0)). Qed.
Lemma lem2412723 : term930.
Proof. exact (@lem2412712 (@lem2412722)). Qed.
Lemma lem2412725 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412726 : term927 = term928.
Proof. exact (@lem2412725 (NUMERAL 0) term268). Qed.
Lemma lem2412727 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412728 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412729 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412728 h1) (fun h1 : term928 = True => @lem2412727)). Qed.
Lemma lem2412730 : term928 = True.
Proof. exact (EQ_MP (@lem2412729) (@lem2412727)). Qed.
Lemma lem2412731 : term927 = True.
Proof. exact (TRANS (@lem2412726) (@lem2412730)). Qed.
Lemma lem2412732 : True = term927.
Proof. exact (SYM (@lem2412731)). Qed.
Lemma lem2412733 : term927.
Proof. exact (EQ_MP (@lem2412732) (@lem0)). Qed.
Lemma lem2412734 : term931.
Proof. exact (@lem2412723 (@lem2412733)). Qed.
Lemma lem2412736 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2412737 : term927 = term928.
Proof. exact (@lem2412736 (NUMERAL 0) term268). Qed.
Lemma lem2412738 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2412739 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2412740 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2412739 h1) (fun h1 : term928 = True => @lem2412738)). Qed.
Lemma lem2412741 : term928 = True.
Proof. exact (EQ_MP (@lem2412740) (@lem2412738)). Qed.
Lemma lem2412742 : term927 = True.
Proof. exact (TRANS (@lem2412737) (@lem2412741)). Qed.
Lemma lem2412743 : True = term927.
Proof. exact (SYM (@lem2412742)). Qed.
Lemma lem2412744 : term927.
Proof. exact (EQ_MP (@lem2412743) (@lem0)). Qed.
Lemma lem2412745 : term932.
Proof. exact (@lem2412734 (@lem2412744)). Qed.
Lemma lem2412747 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412748 : term902 = term903.
Proof. exact (@lem2412747 term268 term268). Qed.
Lemma lem2412749 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412750 : term905 = term268.
Proof. exact (EQ_MP (@lem2412749) (@lem940073)). Qed.
Lemma lem2412751 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412752 : term903 = term267.
Proof. exact (MK_COMB (@lem2412751) (@lem2412750)). Qed.
Lemma lem2412753 : term902 = term267.
Proof. exact (TRANS (@lem2412748) (@lem2412752)). Qed.
Lemma lem2412755 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2412756 : term897 = term908.
Proof. exact (@lem2412755 term268 term268). Qed.
Lemma lem2412757 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412758 : term905 = term268.
Proof. exact (EQ_MP (@lem2412757) (@lem940073)). Qed.
Lemma lem2412759 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412760 : term903 = term267.
Proof. exact (MK_COMB (@lem2412759) (@lem2412758)). Qed.
Lemma lem2412761 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2412762 : term908 = term885.
Proof. exact (MK_COMB (@lem2412761) (@lem2412760)). Qed.
Lemma lem2412763 : term897 = term885.
Proof. exact (TRANS (@lem2412756) (@lem2412762)). Qed.
Lemma lem2412764 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412765 : term933 = term921.
Proof. exact (MK_COMB (@lem2412764) (@lem2412763)). Qed.
Lemma lem2412766 : term934 = term923.
Proof. exact (MK_COMB (@lem2412765) (@lem2412753)). Qed.
Lemma lem2412768 (m : nat) : (term935 m) = term324.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2412769 : term923 = term324.
Proof. exact (@lem2412768 term268). Qed.
Lemma lem2412770 : term934 = term324.
Proof. exact (TRANS (@lem2412766) (@lem2412769)). Qed.
Lemma lem2412771 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412772 : term936 = term444.
Proof. exact (MK_COMB (@lem2412771) (@lem2412770)). Qed.
Lemma lem2412773 : term267 = term267.
Proof. exact (eq_refl term267). Qed.
Lemma lem2412774 : term937 = term938.
Proof. exact (MK_COMB (@lem2412772) (@lem2412773)). Qed.
Lemma lem2412776 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412777 : term938 = term324.
Proof. exact (@lem2412776 term268). Qed.
Lemma lem2412778 : term937 = term324.
Proof. exact (TRANS (@lem2412774) (@lem2412777)). Qed.
Lemma lem2412780 (m : nat) (n : nat) : (term900 m n) = (term901 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2412781 : term902 = term903.
Proof. exact (@lem2412780 term268 term268). Qed.
Lemma lem2412782 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2412783 : term905 = term268.
Proof. exact (EQ_MP (@lem2412782) (@lem940073)). Qed.
Lemma lem2412784 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2412785 : term903 = term267.
Proof. exact (MK_COMB (@lem2412784) (@lem2412783)). Qed.
Lemma lem2412786 : term902 = term267.
Proof. exact (TRANS (@lem2412781) (@lem2412785)). Qed.
Lemma lem2412787 : term444 = term444.
Proof. exact (eq_refl term444). Qed.
Lemma lem2412788 : term940 = term938.
Proof. exact (MK_COMB (@lem2412787) (@lem2412786)). Qed.
Lemma lem2412790 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2412791 : term938 = term324.
Proof. exact (@lem2412790 term268). Qed.
Lemma lem2412792 : term940 = term324.
Proof. exact (TRANS (@lem2412788) (@lem2412791)). Qed.
Lemma lem2412793 : term324 = term940.
Proof. exact (SYM (@lem2412792)). Qed.
Lemma lem2412794 : term937 = term940.
Proof. exact (TRANS (@lem2412778) (@lem2412793)). Qed.
Lemma lem2412795 : term924 = term941.
Proof. exact (@lem2412745 (@lem2412794)). Qed.
Lemma lem2412796 : term923 = term941.
Proof. exact (TRANS (@lem2412711) (@lem2412795)). Qed.
Lemma lem2412798 (x : real) : (term911 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2412799 : term941 = term324.
Proof. exact (@lem2412798 term324). Qed.
Lemma lem2412800 : term923 = term324.
Proof. exact (TRANS (@lem2412796) (@lem2412799)). Qed.
Lemma lem2412801 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2412802 : term942 = term444.
Proof. exact (MK_COMB (@lem2412801) (@lem2412800)). Qed.
Lemma lem2412803 (x : int) (z : int) : (term355 x z) = (term355 x z).
Proof. exact (eq_refl (term355 x z)). Qed.
Lemma lem2412804 (x : int) (z : int) : (term1017 x z) = (term1018 x z).
Proof. exact (MK_COMB (@lem2412802) (@lem2412803 x z)). Qed.
Lemma lem2412805 (x : int) (z : int) : (term1016 x z) = (term1018 x z).
Proof. exact (TRANS (@lem2412702 x z) (@lem2412804 x z)). Qed.
Lemma lem2412806 (x : int) (z : int) : (term1018 x z) = term324.
Proof. exact (@lem1982719 (term355 x z)). Qed.
Lemma lem2412807 (x : int) (z : int) : (term1016 x z) = term324.
Proof. exact (TRANS (@lem2412805 x z) (@lem2412806 x z)). Qed.
Lemma lem2412808 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2412809 (x : int) (z : int) : (term1019 x z) = term326.
Proof. exact (MK_COMB (@lem2412808) (@lem2412807 x z)). Qed.
Lemma lem2412810 : term885 = term885.
Proof. exact (eq_refl term885). Qed.
Lemma lem2412811 (x : int) (z : int) : (term1014 x z) = term948.
Proof. exact (MK_COMB (@lem2412809 x z) (@lem2412810)). Qed.
Lemma lem2412812 (x : int) (z : int) : (term1013 x z) = term948.
Proof. exact (TRANS (@lem2412701 x z) (@lem2412811 x z)). Qed.
Lemma lem2412813 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2412814 (x : int) (z : int) : (term1013 x z) = term885.
Proof. exact (TRANS (@lem2412812 x z) (@lem2412813)). Qed.
Lemma lem2412815 (y : int) (x : int) (z : int) : (term1048 y x z) = term948.
Proof. exact (MK_COMB (@lem2412700 x y) (@lem2412814 x z)). Qed.
Lemma lem2412816 (y : int) (x : int) (z : int) : (term1047 y x z) = term948.
Proof. exact (TRANS (@lem2412592 y x z) (@lem2412815 y x z)). Qed.
Lemma lem2412817 : term948 = term885.
Proof. exact (@lem1982721 term885). Qed.
Lemma lem2412818 (y : int) (x : int) (z : int) : (term1047 y x z) = term885.
Proof. exact (TRANS (@lem2412816 y x z) (@lem2412817)). Qed.
Lemma lem2412819 (y : int) (x : int) (z : int) : (term1043 y x z) = term885.
Proof. exact (TRANS (@lem2412591 y x z) (@lem2412818 y x z)). Qed.
Lemma lem2412820 (y : int) (x : int) (z : int) : (term1042 y x z) = term885.
Proof. exact (TRANS (@lem2412540 y x z) (@lem2412819 y x z)). Qed.
Lemma lem2412821 (y : int) (x : int) (z : int) : (term1052 y x z) = term885.
Proof. exact (TRANS (@lem2412539 y x z) (@lem2412820 y x z)). Qed.
Lemma lem2412822 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2412823 (y : int) (x : int) (z : int) : (term1053 y x z) = term950.
Proof. exact (MK_COMB (@lem2412822) (@lem2412821 y x z)). Qed.
Lemma lem2412824 : term324 = term324.
Proof. exact (eq_refl term324). Qed.
Lemma lem2412825 (y : int) (x : int) (z : int) : (term1050 y x z) = term951.
Proof. exact (MK_COMB (@lem2412823 y x z) (@lem2412824)). Qed.
Lemma lem2412826 (x : int) (y : int) (z : int) : (term496 x y z) = term951.
Proof. exact (TRANS (@lem2412488 y x z) (@lem2412825 y x z)). Qed.
Lemma lem2412827 (x : int) (y : int) : (term806 x y) = term952.
Proof. exact (fun_ext (fun z : int => @lem2412826 x y z)). Qed.
Lemma lem2412828 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412829 (x : int) (y : int) : (term821 x y) = term953.
Proof. exact (MK_COMB (@lem2412828) (@lem2412827 x y)). Qed.
Lemma lem2412830 (x : int) : (term828 x) = term954.
Proof. exact (fun_ext (fun y : int => @lem2412829 x y)). Qed.
Lemma lem2412831 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412832 (x : int) : (term843 x) = term955.
Proof. exact (MK_COMB (@lem2412831) (@lem2412830 x)). Qed.
Lemma lem2412833 : term850 = term956.
Proof. exact (fun_ext (fun x : int => @lem2412832 x)). Qed.
Lemma lem2412834 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2412835 : term865 = term957.
Proof. exact (MK_COMB (@lem2412834) (@lem2412833)). Qed.
Lemma lem2412836 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412837 : term862 = term961.
Proof. exact (MK_COMB (@lem2412836) (@lem2412487)). Qed.
Lemma lem2412838 : term866 = term962.
Proof. exact (MK_COMB (@lem2412837) (@lem2412835)). Qed.
Lemma lem2412839 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412840 : term802 = term1054.
Proof. exact (MK_COMB (@lem2412839) (@lem2412139)). Qed.
Lemma lem2412841 : term867 = term1055.
Proof. exact (MK_COMB (@lem2412840) (@lem2412838)). Qed.
Lemma lem2412842 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412843 : term781 = term1054.
Proof. exact (MK_COMB (@lem2412842) (@lem2411996)). Qed.
Lemma lem2412844 : term868 = term1056.
Proof. exact (MK_COMB (@lem2412843) (@lem2412841)). Qed.
Lemma lem2412845 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412846 : term760 = term1057.
Proof. exact (MK_COMB (@lem2412845) (@lem2411615)). Qed.
Lemma lem2412847 : term869 = term1058.
Proof. exact (MK_COMB (@lem2412846) (@lem2412844)). Qed.
Lemma lem2412848 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412849 : term717 = term1059.
Proof. exact (MK_COMB (@lem2412848) (@lem2411216)). Qed.
Lemma lem2412850 : term870 = term1060.
Proof. exact (MK_COMB (@lem2412849) (@lem2412847)). Qed.
Lemma lem2412851 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412852 : term652 = term1054.
Proof. exact (MK_COMB (@lem2412851) (@lem2410779)). Qed.
Lemma lem2412853 : term871 = term1061.
Proof. exact (MK_COMB (@lem2412852) (@lem2412850)). Qed.
Lemma lem2412854 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412855 : term631 = term1057.
Proof. exact (MK_COMB (@lem2412854) (@lem2410398)). Qed.
Lemma lem2412856 : term872 = term1062.
Proof. exact (MK_COMB (@lem2412855) (@lem2412853)). Qed.
Lemma lem2412857 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412858 : term588 = term1059.
Proof. exact (MK_COMB (@lem2412857) (@lem2409753)). Qed.
Lemma lem2412859 : term873 = term1063.
Proof. exact (MK_COMB (@lem2412858) (@lem2412856)). Qed.
Lemma lem2412860 : term519 = term1063.
Proof. exact (TRANS (@lem2408824) (@lem2412859)). Qed.
Lemma lem2412862 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412863 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412862 int t). Qed.
Lemma lem2412864 : term957 = term955.
Proof. exact (@lem2412863 term955). Qed.
Lemma lem2412866 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412867 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412866 int t). Qed.
Lemma lem2412868 : term955 = term953.
Proof. exact (@lem2412867 term953). Qed.
Lemma lem2412870 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412871 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412870 int t). Qed.
Lemma lem2412872 : term953 = term951.
Proof. exact (@lem2412871 term951). Qed.
Lemma lem2412873 : term955 = term951.
Proof. exact (TRANS (@lem2412868) (@lem2412872)). Qed.
Lemma lem2412874 : term957 = term951.
Proof. exact (TRANS (@lem2412864) (@lem2412873)). Qed.
Lemma lem2412875 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412876 : term961 = term1066.
Proof. exact (MK_COMB (@lem2412875) (@lem2412874)). Qed.
Lemma lem2412878 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412879 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412878 int t). Qed.
Lemma lem2412880 : term957 = term955.
Proof. exact (@lem2412879 term955). Qed.
Lemma lem2412882 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412883 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412882 int t). Qed.
Lemma lem2412884 : term955 = term953.
Proof. exact (@lem2412883 term953). Qed.
Lemma lem2412886 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412887 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412886 int t). Qed.
Lemma lem2412888 : term953 = term951.
Proof. exact (@lem2412887 term951). Qed.
Lemma lem2412889 : term955 = term951.
Proof. exact (TRANS (@lem2412884) (@lem2412888)). Qed.
Lemma lem2412890 : term957 = term951.
Proof. exact (TRANS (@lem2412880) (@lem2412889)). Qed.
Lemma lem2412891 : term962 = term1067.
Proof. exact (MK_COMB (@lem2412876) (@lem2412890)). Qed.
Lemma lem2412892 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412893 : term1059 = term1068.
Proof. exact (MK_COMB (@lem2412892) (@lem2412891)). Qed.
Lemma lem2412895 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412896 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412895 int t). Qed.
Lemma lem2412897 : term955 = term953.
Proof. exact (@lem2412896 term953). Qed.
Lemma lem2412899 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412900 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412899 int t). Qed.
Lemma lem2412901 : term953 = term951.
Proof. exact (@lem2412900 term951). Qed.
Lemma lem2412902 : term955 = term951.
Proof. exact (TRANS (@lem2412897) (@lem2412901)). Qed.
Lemma lem2412903 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412904 : term969 = term1066.
Proof. exact (MK_COMB (@lem2412903) (@lem2412902)). Qed.
Lemma lem2412906 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412907 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412906 int t). Qed.
Lemma lem2412908 : term955 = term953.
Proof. exact (@lem2412907 term953). Qed.
Lemma lem2412910 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412911 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412910 int t). Qed.
Lemma lem2412912 : term953 = term951.
Proof. exact (@lem2412911 term951). Qed.
Lemma lem2412913 : term955 = term951.
Proof. exact (TRANS (@lem2412908) (@lem2412912)). Qed.
Lemma lem2412914 : term970 = term1067.
Proof. exact (MK_COMB (@lem2412904) (@lem2412913)). Qed.
Lemma lem2412915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412916 : term1057 = term1068.
Proof. exact (MK_COMB (@lem2412915) (@lem2412914)). Qed.
Lemma lem2412918 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412919 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412918 int t). Qed.
Lemma lem2412920 : term953 = term951.
Proof. exact (@lem2412919 term951). Qed.
Lemma lem2412921 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412922 : term981 = term1066.
Proof. exact (MK_COMB (@lem2412921) (@lem2412920)). Qed.
Lemma lem2412924 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412925 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412924 int t). Qed.
Lemma lem2412926 : term953 = term951.
Proof. exact (@lem2412925 term951). Qed.
Lemma lem2412927 : term982 = term1067.
Proof. exact (MK_COMB (@lem2412922) (@lem2412926)). Qed.
Lemma lem2412928 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412929 : term1054 = term1068.
Proof. exact (MK_COMB (@lem2412928) (@lem2412927)). Qed.
Lemma lem2412931 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412932 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412931 int t). Qed.
Lemma lem2412933 : term957 = term955.
Proof. exact (@lem2412932 term955). Qed.
Lemma lem2412935 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412936 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412935 int t). Qed.
Lemma lem2412937 : term955 = term953.
Proof. exact (@lem2412936 term953). Qed.
Lemma lem2412939 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412940 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412939 int t). Qed.
Lemma lem2412941 : term953 = term951.
Proof. exact (@lem2412940 term951). Qed.
Lemma lem2412942 : term955 = term951.
Proof. exact (TRANS (@lem2412937) (@lem2412941)). Qed.
Lemma lem2412943 : term957 = term951.
Proof. exact (TRANS (@lem2412933) (@lem2412942)). Qed.
Lemma lem2412944 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412945 : term961 = term1066.
Proof. exact (MK_COMB (@lem2412944) (@lem2412943)). Qed.
Lemma lem2412947 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412948 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412947 int t). Qed.
Lemma lem2412949 : term957 = term955.
Proof. exact (@lem2412948 term955). Qed.
Lemma lem2412951 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412952 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412951 int t). Qed.
Lemma lem2412953 : term955 = term953.
Proof. exact (@lem2412952 term953). Qed.
Lemma lem2412955 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412956 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412955 int t). Qed.
Lemma lem2412957 : term953 = term951.
Proof. exact (@lem2412956 term951). Qed.
Lemma lem2412958 : term955 = term951.
Proof. exact (TRANS (@lem2412953) (@lem2412957)). Qed.
Lemma lem2412959 : term957 = term951.
Proof. exact (TRANS (@lem2412949) (@lem2412958)). Qed.
Lemma lem2412960 : term962 = term1067.
Proof. exact (MK_COMB (@lem2412945) (@lem2412959)). Qed.
Lemma lem2412961 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412962 : term1059 = term1068.
Proof. exact (MK_COMB (@lem2412961) (@lem2412960)). Qed.
Lemma lem2412964 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412965 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412964 int t). Qed.
Lemma lem2412966 : term955 = term953.
Proof. exact (@lem2412965 term953). Qed.
Lemma lem2412968 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412969 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412968 int t). Qed.
Lemma lem2412970 : term953 = term951.
Proof. exact (@lem2412969 term951). Qed.
Lemma lem2412971 : term955 = term951.
Proof. exact (TRANS (@lem2412966) (@lem2412970)). Qed.
Lemma lem2412972 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412973 : term969 = term1066.
Proof. exact (MK_COMB (@lem2412972) (@lem2412971)). Qed.
Lemma lem2412975 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412976 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412975 int t). Qed.
Lemma lem2412977 : term955 = term953.
Proof. exact (@lem2412976 term953). Qed.
Lemma lem2412979 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412980 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412979 int t). Qed.
Lemma lem2412981 : term953 = term951.
Proof. exact (@lem2412980 term951). Qed.
Lemma lem2412982 : term955 = term951.
Proof. exact (TRANS (@lem2412977) (@lem2412981)). Qed.
Lemma lem2412983 : term970 = term1067.
Proof. exact (MK_COMB (@lem2412973) (@lem2412982)). Qed.
Lemma lem2412984 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412985 : term1057 = term1068.
Proof. exact (MK_COMB (@lem2412984) (@lem2412983)). Qed.
Lemma lem2412987 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412988 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412987 int t). Qed.
Lemma lem2412989 : term953 = term951.
Proof. exact (@lem2412988 term951). Qed.
Lemma lem2412990 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412991 : term981 = term1066.
Proof. exact (MK_COMB (@lem2412990) (@lem2412989)). Qed.
Lemma lem2412993 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2412994 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2412993 int t). Qed.
Lemma lem2412995 : term953 = term951.
Proof. exact (@lem2412994 term951). Qed.
Lemma lem2412996 : term982 = term1067.
Proof. exact (MK_COMB (@lem2412991) (@lem2412995)). Qed.
Lemma lem2412997 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2412998 : term1054 = term1068.
Proof. exact (MK_COMB (@lem2412997) (@lem2412996)). Qed.
Lemma lem2413000 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413001 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413000 int t). Qed.
Lemma lem2413002 : term953 = term951.
Proof. exact (@lem2413001 term951). Qed.
Lemma lem2413003 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2413004 : term981 = term1066.
Proof. exact (MK_COMB (@lem2413003) (@lem2413002)). Qed.
Lemma lem2413006 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413007 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413006 int t). Qed.
Lemma lem2413008 : term953 = term951.
Proof. exact (@lem2413007 term951). Qed.
Lemma lem2413009 : term982 = term1067.
Proof. exact (MK_COMB (@lem2413004) (@lem2413008)). Qed.
Lemma lem2413010 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2413011 : term1054 = term1068.
Proof. exact (MK_COMB (@lem2413010) (@lem2413009)). Qed.
Lemma lem2413013 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413014 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413013 int t). Qed.
Lemma lem2413015 : term957 = term955.
Proof. exact (@lem2413014 term955). Qed.
Lemma lem2413017 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413018 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413017 int t). Qed.
Lemma lem2413019 : term955 = term953.
Proof. exact (@lem2413018 term953). Qed.
Lemma lem2413021 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413022 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413021 int t). Qed.
Lemma lem2413023 : term953 = term951.
Proof. exact (@lem2413022 term951). Qed.
Lemma lem2413024 : term955 = term951.
Proof. exact (TRANS (@lem2413019) (@lem2413023)). Qed.
Lemma lem2413025 : term957 = term951.
Proof. exact (TRANS (@lem2413015) (@lem2413024)). Qed.
Lemma lem2413026 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2413027 : term961 = term1066.
Proof. exact (MK_COMB (@lem2413026) (@lem2413025)). Qed.
Lemma lem2413029 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413030 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413029 int t). Qed.
Lemma lem2413031 : term957 = term955.
Proof. exact (@lem2413030 term955). Qed.
Lemma lem2413033 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413034 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413033 int t). Qed.
Lemma lem2413035 : term955 = term953.
Proof. exact (@lem2413034 term953). Qed.
Lemma lem2413037 {A : Type'} (t : Prop) : (term1064 A t) = t.
Proof. exact (EQ_MP (@lem18932 A t) (@lem18931 A t)). Qed.
Lemma lem2413038 (t : Prop) : (term1065 t) = t.
Proof. exact (@lem2413037 int t). Qed.
Lemma lem2413039 : term953 = term951.
Proof. exact (@lem2413038 term951). Qed.
Lemma lem2413040 : term955 = term951.
Proof. exact (TRANS (@lem2413035) (@lem2413039)). Qed.
Lemma lem2413041 : term957 = term951.
Proof. exact (TRANS (@lem2413031) (@lem2413040)). Qed.
Lemma lem2413042 : term962 = term1067.
Proof. exact (MK_COMB (@lem2413027) (@lem2413041)). Qed.
Lemma lem2413043 : term1055 = term1069.
Proof. exact (MK_COMB (@lem2413011) (@lem2413042)). Qed.
Lemma lem2413044 : term1056 = term1070.
Proof. exact (MK_COMB (@lem2412998) (@lem2413043)). Qed.
Lemma lem2413045 : term1058 = term1071.
Proof. exact (MK_COMB (@lem2412985) (@lem2413044)). Qed.
Lemma lem2413046 : term1060 = term1072.
Proof. exact (MK_COMB (@lem2412962) (@lem2413045)). Qed.
Lemma lem2413047 : term1061 = term1073.
Proof. exact (MK_COMB (@lem2412929) (@lem2413046)). Qed.
Lemma lem2413048 : term1062 = term1074.
Proof. exact (MK_COMB (@lem2412916) (@lem2413047)). Qed.
Lemma lem2413051 : term1063 = term1075.
Proof. exact (MK_COMB (@lem2412893) (@lem2413048)). Qed.
Lemma lem2413116 : term519 = term1075.
Proof. exact (TRANS (@lem2412860) (@lem2413051)). Qed.
Lemma lem2413210 (h1 : term1075) : term1075.
Proof. exact (h1). Qed.
Lemma lem2413211 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2413212 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413214 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413215 : term951 = term1076.
Proof. exact (@lem2413214 term324 term885). Qed.
Lemma lem2413217 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413218 : term885 = term894.
Proof. exact (@lem2413217 term268). Qed.
Lemma lem2413220 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413221 : term324 = term941.
Proof. exact (@lem2413220 (NUMERAL 0)). Qed.
Lemma lem2413222 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413223 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413222) (@lem2413221)). Qed.
Lemma lem2413224 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413223) (@lem2413218)). Qed.
Lemma lem2413225 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413227 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413228 : term927 = term928.
Proof. exact (@lem2413227 (NUMERAL 0) term268). Qed.
Lemma lem2413229 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413230 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413231 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413230 h1) (fun h1 : term928 = True => @lem2413229)). Qed.
Lemma lem2413232 : term928 = True.
Proof. exact (EQ_MP (@lem2413231) (@lem2413229)). Qed.
Lemma lem2413233 : term927 = True.
Proof. exact (TRANS (@lem2413228) (@lem2413232)). Qed.
Lemma lem2413234 : True = term927.
Proof. exact (SYM (@lem2413233)). Qed.
Lemma lem2413235 : term927.
Proof. exact (EQ_MP (@lem2413234) (@lem0)). Qed.
Lemma lem2413236 : term1081.
Proof. exact (@lem2413225 (@lem2413235)). Qed.
Lemma lem2413238 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413239 : term927 = term928.
Proof. exact (@lem2413238 (NUMERAL 0) term268). Qed.
Lemma lem2413240 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413241 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413242 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413241 h1) (fun h1 : term928 = True => @lem2413240)). Qed.
Lemma lem2413243 : term928 = True.
Proof. exact (EQ_MP (@lem2413242) (@lem2413240)). Qed.
Lemma lem2413244 : term927 = True.
Proof. exact (TRANS (@lem2413239) (@lem2413243)). Qed.
Lemma lem2413245 : True = term927.
Proof. exact (SYM (@lem2413244)). Qed.
Lemma lem2413246 : term927.
Proof. exact (EQ_MP (@lem2413245) (@lem0)). Qed.
Lemma lem2413247 : term1079 = term1082.
Proof. exact (@lem2413236 (@lem2413246)). Qed.
Lemma lem2413249 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413250 : term897 = term908.
Proof. exact (@lem2413249 term268 term268). Qed.
Lemma lem2413251 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413252 : term905 = term268.
Proof. exact (EQ_MP (@lem2413251) (@lem940073)). Qed.
Lemma lem2413253 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413254 : term903 = term267.
Proof. exact (MK_COMB (@lem2413253) (@lem2413252)). Qed.
Lemma lem2413255 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413256 : term908 = term885.
Proof. exact (MK_COMB (@lem2413255) (@lem2413254)). Qed.
Lemma lem2413257 : term897 = term885.
Proof. exact (TRANS (@lem2413250) (@lem2413256)). Qed.
Lemma lem2413259 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413260 : term938 = term324.
Proof. exact (@lem2413259 term268). Qed.
Lemma lem2413261 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413262 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413261) (@lem2413260)). Qed.
Lemma lem2413263 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413262) (@lem2413257)). Qed.
Lemma lem2413265 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413266 : term1076 = term1086.
Proof. exact (@lem2413265 (NUMERAL 0) term268). Qed.
Lemma lem2413267 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413268 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413269 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413268 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413267)). Qed.
Lemma lem2413270 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413269) (@lem2413267)). Qed.
Lemma lem2413271 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413272 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413273 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413272) (@lem2413271)). Qed.
Lemma lem2413274 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413273) (@lem2413270)). Qed.
Lemma lem2413276 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413277 : term1086 = False.
Proof. exact (TRANS (@lem2413274) (@lem2413276)). Qed.
Lemma lem2413278 : term1076 = False.
Proof. exact (TRANS (@lem2413266) (@lem2413277)). Qed.
Lemma lem2413279 : term1082 = False.
Proof. exact (TRANS (@lem2413263) (@lem2413278)). Qed.
Lemma lem2413280 : term1079 = False.
Proof. exact (TRANS (@lem2413247) (@lem2413279)). Qed.
Lemma lem2413281 : term1076 = False.
Proof. exact (TRANS (@lem2413224) (@lem2413280)). Qed.
Lemma lem2413282 : term951 = False.
Proof. exact (TRANS (@lem2413215) (@lem2413281)). Qed.
Lemma lem2413283 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413282) (@lem2413212 h1)). Qed.
Lemma lem2413284 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413286 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413287 : term951 = term1076.
Proof. exact (@lem2413286 term324 term885). Qed.
Lemma lem2413289 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413290 : term885 = term894.
Proof. exact (@lem2413289 term268). Qed.
Lemma lem2413292 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413293 : term324 = term941.
Proof. exact (@lem2413292 (NUMERAL 0)). Qed.
Lemma lem2413294 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413295 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413294) (@lem2413293)). Qed.
Lemma lem2413296 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413295) (@lem2413290)). Qed.
Lemma lem2413297 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413299 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413300 : term927 = term928.
Proof. exact (@lem2413299 (NUMERAL 0) term268). Qed.
Lemma lem2413301 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413302 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413303 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413302 h1) (fun h1 : term928 = True => @lem2413301)). Qed.
Lemma lem2413304 : term928 = True.
Proof. exact (EQ_MP (@lem2413303) (@lem2413301)). Qed.
Lemma lem2413305 : term927 = True.
Proof. exact (TRANS (@lem2413300) (@lem2413304)). Qed.
Lemma lem2413306 : True = term927.
Proof. exact (SYM (@lem2413305)). Qed.
Lemma lem2413307 : term927.
Proof. exact (EQ_MP (@lem2413306) (@lem0)). Qed.
Lemma lem2413308 : term1081.
Proof. exact (@lem2413297 (@lem2413307)). Qed.
Lemma lem2413310 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413311 : term927 = term928.
Proof. exact (@lem2413310 (NUMERAL 0) term268). Qed.
Lemma lem2413312 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413313 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413314 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413313 h1) (fun h1 : term928 = True => @lem2413312)). Qed.
Lemma lem2413315 : term928 = True.
Proof. exact (EQ_MP (@lem2413314) (@lem2413312)). Qed.
Lemma lem2413316 : term927 = True.
Proof. exact (TRANS (@lem2413311) (@lem2413315)). Qed.
Lemma lem2413317 : True = term927.
Proof. exact (SYM (@lem2413316)). Qed.
Lemma lem2413318 : term927.
Proof. exact (EQ_MP (@lem2413317) (@lem0)). Qed.
Lemma lem2413319 : term1079 = term1082.
Proof. exact (@lem2413308 (@lem2413318)). Qed.
Lemma lem2413321 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413322 : term897 = term908.
Proof. exact (@lem2413321 term268 term268). Qed.
Lemma lem2413323 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413324 : term905 = term268.
Proof. exact (EQ_MP (@lem2413323) (@lem940073)). Qed.
Lemma lem2413325 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413326 : term903 = term267.
Proof. exact (MK_COMB (@lem2413325) (@lem2413324)). Qed.
Lemma lem2413327 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413328 : term908 = term885.
Proof. exact (MK_COMB (@lem2413327) (@lem2413326)). Qed.
Lemma lem2413329 : term897 = term885.
Proof. exact (TRANS (@lem2413322) (@lem2413328)). Qed.
Lemma lem2413331 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413332 : term938 = term324.
Proof. exact (@lem2413331 term268). Qed.
Lemma lem2413333 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413334 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413333) (@lem2413332)). Qed.
Lemma lem2413335 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413334) (@lem2413329)). Qed.
Lemma lem2413337 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413338 : term1076 = term1086.
Proof. exact (@lem2413337 (NUMERAL 0) term268). Qed.
Lemma lem2413339 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413340 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413341 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413340 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413339)). Qed.
Lemma lem2413342 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413341) (@lem2413339)). Qed.
Lemma lem2413343 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413344 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413345 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413344) (@lem2413343)). Qed.
Lemma lem2413346 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413345) (@lem2413342)). Qed.
Lemma lem2413348 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413349 : term1086 = False.
Proof. exact (TRANS (@lem2413346) (@lem2413348)). Qed.
Lemma lem2413350 : term1076 = False.
Proof. exact (TRANS (@lem2413338) (@lem2413349)). Qed.
Lemma lem2413351 : term1082 = False.
Proof. exact (TRANS (@lem2413335) (@lem2413350)). Qed.
Lemma lem2413352 : term1079 = False.
Proof. exact (TRANS (@lem2413319) (@lem2413351)). Qed.
Lemma lem2413353 : term1076 = False.
Proof. exact (TRANS (@lem2413296) (@lem2413352)). Qed.
Lemma lem2413354 : term951 = False.
Proof. exact (TRANS (@lem2413287) (@lem2413353)). Qed.
Lemma lem2413355 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413354) (@lem2413284 h1)). Qed.
Lemma lem2413356 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2413211 h1) (fun h0 : term951 => @lem2413283 h0) (fun h0 : term951 => @lem2413355 h0)). Qed.
Lemma lem2413357 (h1 : term1074) : term1074.
Proof. exact (h1). Qed.
Lemma lem2413358 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2413359 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413361 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413362 : term951 = term1076.
Proof. exact (@lem2413361 term324 term885). Qed.
Lemma lem2413364 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413365 : term885 = term894.
Proof. exact (@lem2413364 term268). Qed.
Lemma lem2413367 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413368 : term324 = term941.
Proof. exact (@lem2413367 (NUMERAL 0)). Qed.
Lemma lem2413369 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413370 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413369) (@lem2413368)). Qed.
Lemma lem2413371 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413370) (@lem2413365)). Qed.
Lemma lem2413372 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413374 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413375 : term927 = term928.
Proof. exact (@lem2413374 (NUMERAL 0) term268). Qed.
Lemma lem2413376 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413377 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413378 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413377 h1) (fun h1 : term928 = True => @lem2413376)). Qed.
Lemma lem2413379 : term928 = True.
Proof. exact (EQ_MP (@lem2413378) (@lem2413376)). Qed.
Lemma lem2413380 : term927 = True.
Proof. exact (TRANS (@lem2413375) (@lem2413379)). Qed.
Lemma lem2413381 : True = term927.
Proof. exact (SYM (@lem2413380)). Qed.
Lemma lem2413382 : term927.
Proof. exact (EQ_MP (@lem2413381) (@lem0)). Qed.
Lemma lem2413383 : term1081.
Proof. exact (@lem2413372 (@lem2413382)). Qed.
Lemma lem2413385 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413386 : term927 = term928.
Proof. exact (@lem2413385 (NUMERAL 0) term268). Qed.
Lemma lem2413387 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413388 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413389 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413388 h1) (fun h1 : term928 = True => @lem2413387)). Qed.
Lemma lem2413390 : term928 = True.
Proof. exact (EQ_MP (@lem2413389) (@lem2413387)). Qed.
Lemma lem2413391 : term927 = True.
Proof. exact (TRANS (@lem2413386) (@lem2413390)). Qed.
Lemma lem2413392 : True = term927.
Proof. exact (SYM (@lem2413391)). Qed.
Lemma lem2413393 : term927.
Proof. exact (EQ_MP (@lem2413392) (@lem0)). Qed.
Lemma lem2413394 : term1079 = term1082.
Proof. exact (@lem2413383 (@lem2413393)). Qed.
Lemma lem2413396 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413397 : term897 = term908.
Proof. exact (@lem2413396 term268 term268). Qed.
Lemma lem2413398 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413399 : term905 = term268.
Proof. exact (EQ_MP (@lem2413398) (@lem940073)). Qed.
Lemma lem2413400 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413401 : term903 = term267.
Proof. exact (MK_COMB (@lem2413400) (@lem2413399)). Qed.
Lemma lem2413402 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413403 : term908 = term885.
Proof. exact (MK_COMB (@lem2413402) (@lem2413401)). Qed.
Lemma lem2413404 : term897 = term885.
Proof. exact (TRANS (@lem2413397) (@lem2413403)). Qed.
Lemma lem2413406 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413407 : term938 = term324.
Proof. exact (@lem2413406 term268). Qed.
Lemma lem2413408 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413409 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413408) (@lem2413407)). Qed.
Lemma lem2413410 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413409) (@lem2413404)). Qed.
Lemma lem2413412 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413413 : term1076 = term1086.
Proof. exact (@lem2413412 (NUMERAL 0) term268). Qed.
Lemma lem2413414 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413415 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413416 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413415 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413414)). Qed.
Lemma lem2413417 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413416) (@lem2413414)). Qed.
Lemma lem2413418 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413419 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413420 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413419) (@lem2413418)). Qed.
Lemma lem2413421 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413420) (@lem2413417)). Qed.
Lemma lem2413423 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413424 : term1086 = False.
Proof. exact (TRANS (@lem2413421) (@lem2413423)). Qed.
Lemma lem2413425 : term1076 = False.
Proof. exact (TRANS (@lem2413413) (@lem2413424)). Qed.
Lemma lem2413426 : term1082 = False.
Proof. exact (TRANS (@lem2413410) (@lem2413425)). Qed.
Lemma lem2413427 : term1079 = False.
Proof. exact (TRANS (@lem2413394) (@lem2413426)). Qed.
Lemma lem2413428 : term1076 = False.
Proof. exact (TRANS (@lem2413371) (@lem2413427)). Qed.
Lemma lem2413429 : term951 = False.
Proof. exact (TRANS (@lem2413362) (@lem2413428)). Qed.
Lemma lem2413430 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413429) (@lem2413359 h1)). Qed.
Lemma lem2413431 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413433 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413434 : term951 = term1076.
Proof. exact (@lem2413433 term324 term885). Qed.
Lemma lem2413436 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413437 : term885 = term894.
Proof. exact (@lem2413436 term268). Qed.
Lemma lem2413439 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413440 : term324 = term941.
Proof. exact (@lem2413439 (NUMERAL 0)). Qed.
Lemma lem2413441 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413442 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413441) (@lem2413440)). Qed.
Lemma lem2413443 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413442) (@lem2413437)). Qed.
Lemma lem2413444 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413446 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413447 : term927 = term928.
Proof. exact (@lem2413446 (NUMERAL 0) term268). Qed.
Lemma lem2413448 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413449 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413450 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413449 h1) (fun h1 : term928 = True => @lem2413448)). Qed.
Lemma lem2413451 : term928 = True.
Proof. exact (EQ_MP (@lem2413450) (@lem2413448)). Qed.
Lemma lem2413452 : term927 = True.
Proof. exact (TRANS (@lem2413447) (@lem2413451)). Qed.
Lemma lem2413453 : True = term927.
Proof. exact (SYM (@lem2413452)). Qed.
Lemma lem2413454 : term927.
Proof. exact (EQ_MP (@lem2413453) (@lem0)). Qed.
Lemma lem2413455 : term1081.
Proof. exact (@lem2413444 (@lem2413454)). Qed.
Lemma lem2413457 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413458 : term927 = term928.
Proof. exact (@lem2413457 (NUMERAL 0) term268). Qed.
Lemma lem2413459 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413460 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413461 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413460 h1) (fun h1 : term928 = True => @lem2413459)). Qed.
Lemma lem2413462 : term928 = True.
Proof. exact (EQ_MP (@lem2413461) (@lem2413459)). Qed.
Lemma lem2413463 : term927 = True.
Proof. exact (TRANS (@lem2413458) (@lem2413462)). Qed.
Lemma lem2413464 : True = term927.
Proof. exact (SYM (@lem2413463)). Qed.
Lemma lem2413465 : term927.
Proof. exact (EQ_MP (@lem2413464) (@lem0)). Qed.
Lemma lem2413466 : term1079 = term1082.
Proof. exact (@lem2413455 (@lem2413465)). Qed.
Lemma lem2413468 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413469 : term897 = term908.
Proof. exact (@lem2413468 term268 term268). Qed.
Lemma lem2413470 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413471 : term905 = term268.
Proof. exact (EQ_MP (@lem2413470) (@lem940073)). Qed.
Lemma lem2413472 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413473 : term903 = term267.
Proof. exact (MK_COMB (@lem2413472) (@lem2413471)). Qed.
Lemma lem2413474 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413475 : term908 = term885.
Proof. exact (MK_COMB (@lem2413474) (@lem2413473)). Qed.
Lemma lem2413476 : term897 = term885.
Proof. exact (TRANS (@lem2413469) (@lem2413475)). Qed.
Lemma lem2413478 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413479 : term938 = term324.
Proof. exact (@lem2413478 term268). Qed.
Lemma lem2413480 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413481 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413480) (@lem2413479)). Qed.
Lemma lem2413482 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413481) (@lem2413476)). Qed.
Lemma lem2413484 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413485 : term1076 = term1086.
Proof. exact (@lem2413484 (NUMERAL 0) term268). Qed.
Lemma lem2413486 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413487 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413488 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413487 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413486)). Qed.
Lemma lem2413489 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413488) (@lem2413486)). Qed.
Lemma lem2413490 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413491 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413492 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413491) (@lem2413490)). Qed.
Lemma lem2413493 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413492) (@lem2413489)). Qed.
Lemma lem2413495 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413496 : term1086 = False.
Proof. exact (TRANS (@lem2413493) (@lem2413495)). Qed.
Lemma lem2413497 : term1076 = False.
Proof. exact (TRANS (@lem2413485) (@lem2413496)). Qed.
Lemma lem2413498 : term1082 = False.
Proof. exact (TRANS (@lem2413482) (@lem2413497)). Qed.
Lemma lem2413499 : term1079 = False.
Proof. exact (TRANS (@lem2413466) (@lem2413498)). Qed.
Lemma lem2413500 : term1076 = False.
Proof. exact (TRANS (@lem2413443) (@lem2413499)). Qed.
Lemma lem2413501 : term951 = False.
Proof. exact (TRANS (@lem2413434) (@lem2413500)). Qed.
Lemma lem2413502 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413501) (@lem2413431 h1)). Qed.
Lemma lem2413503 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2413358 h1) (fun h0 : term951 => @lem2413430 h0) (fun h0 : term951 => @lem2413502 h0)). Qed.
Lemma lem2413504 (h1 : term1073) : term1073.
Proof. exact (h1). Qed.
Lemma lem2413505 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2413506 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413508 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413509 : term951 = term1076.
Proof. exact (@lem2413508 term324 term885). Qed.
Lemma lem2413511 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413512 : term885 = term894.
Proof. exact (@lem2413511 term268). Qed.
Lemma lem2413514 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413515 : term324 = term941.
Proof. exact (@lem2413514 (NUMERAL 0)). Qed.
Lemma lem2413516 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413517 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413516) (@lem2413515)). Qed.
Lemma lem2413518 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413517) (@lem2413512)). Qed.
Lemma lem2413519 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413521 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413522 : term927 = term928.
Proof. exact (@lem2413521 (NUMERAL 0) term268). Qed.
Lemma lem2413523 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413524 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413525 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413524 h1) (fun h1 : term928 = True => @lem2413523)). Qed.
Lemma lem2413526 : term928 = True.
Proof. exact (EQ_MP (@lem2413525) (@lem2413523)). Qed.
Lemma lem2413527 : term927 = True.
Proof. exact (TRANS (@lem2413522) (@lem2413526)). Qed.
Lemma lem2413528 : True = term927.
Proof. exact (SYM (@lem2413527)). Qed.
Lemma lem2413529 : term927.
Proof. exact (EQ_MP (@lem2413528) (@lem0)). Qed.
Lemma lem2413530 : term1081.
Proof. exact (@lem2413519 (@lem2413529)). Qed.
Lemma lem2413532 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413533 : term927 = term928.
Proof. exact (@lem2413532 (NUMERAL 0) term268). Qed.
Lemma lem2413534 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413535 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413536 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413535 h1) (fun h1 : term928 = True => @lem2413534)). Qed.
Lemma lem2413537 : term928 = True.
Proof. exact (EQ_MP (@lem2413536) (@lem2413534)). Qed.
Lemma lem2413538 : term927 = True.
Proof. exact (TRANS (@lem2413533) (@lem2413537)). Qed.
Lemma lem2413539 : True = term927.
Proof. exact (SYM (@lem2413538)). Qed.
Lemma lem2413540 : term927.
Proof. exact (EQ_MP (@lem2413539) (@lem0)). Qed.
Lemma lem2413541 : term1079 = term1082.
Proof. exact (@lem2413530 (@lem2413540)). Qed.
Lemma lem2413543 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413544 : term897 = term908.
Proof. exact (@lem2413543 term268 term268). Qed.
Lemma lem2413545 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413546 : term905 = term268.
Proof. exact (EQ_MP (@lem2413545) (@lem940073)). Qed.
Lemma lem2413547 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413548 : term903 = term267.
Proof. exact (MK_COMB (@lem2413547) (@lem2413546)). Qed.
Lemma lem2413549 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413550 : term908 = term885.
Proof. exact (MK_COMB (@lem2413549) (@lem2413548)). Qed.
Lemma lem2413551 : term897 = term885.
Proof. exact (TRANS (@lem2413544) (@lem2413550)). Qed.
Lemma lem2413553 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413554 : term938 = term324.
Proof. exact (@lem2413553 term268). Qed.
Lemma lem2413555 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413556 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413555) (@lem2413554)). Qed.
Lemma lem2413557 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413556) (@lem2413551)). Qed.
Lemma lem2413559 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413560 : term1076 = term1086.
Proof. exact (@lem2413559 (NUMERAL 0) term268). Qed.
Lemma lem2413561 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413562 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413563 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413562 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413561)). Qed.
Lemma lem2413564 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413563) (@lem2413561)). Qed.
Lemma lem2413565 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413566 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413567 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413566) (@lem2413565)). Qed.
Lemma lem2413568 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413567) (@lem2413564)). Qed.
Lemma lem2413570 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413571 : term1086 = False.
Proof. exact (TRANS (@lem2413568) (@lem2413570)). Qed.
Lemma lem2413572 : term1076 = False.
Proof. exact (TRANS (@lem2413560) (@lem2413571)). Qed.
Lemma lem2413573 : term1082 = False.
Proof. exact (TRANS (@lem2413557) (@lem2413572)). Qed.
Lemma lem2413574 : term1079 = False.
Proof. exact (TRANS (@lem2413541) (@lem2413573)). Qed.
Lemma lem2413575 : term1076 = False.
Proof. exact (TRANS (@lem2413518) (@lem2413574)). Qed.
Lemma lem2413576 : term951 = False.
Proof. exact (TRANS (@lem2413509) (@lem2413575)). Qed.
Lemma lem2413577 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413576) (@lem2413506 h1)). Qed.
Lemma lem2413578 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413580 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413581 : term951 = term1076.
Proof. exact (@lem2413580 term324 term885). Qed.
Lemma lem2413583 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413584 : term885 = term894.
Proof. exact (@lem2413583 term268). Qed.
Lemma lem2413586 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413587 : term324 = term941.
Proof. exact (@lem2413586 (NUMERAL 0)). Qed.
Lemma lem2413588 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413589 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413588) (@lem2413587)). Qed.
Lemma lem2413590 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413589) (@lem2413584)). Qed.
Lemma lem2413591 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413593 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413594 : term927 = term928.
Proof. exact (@lem2413593 (NUMERAL 0) term268). Qed.
Lemma lem2413595 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413596 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413597 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413596 h1) (fun h1 : term928 = True => @lem2413595)). Qed.
Lemma lem2413598 : term928 = True.
Proof. exact (EQ_MP (@lem2413597) (@lem2413595)). Qed.
Lemma lem2413599 : term927 = True.
Proof. exact (TRANS (@lem2413594) (@lem2413598)). Qed.
Lemma lem2413600 : True = term927.
Proof. exact (SYM (@lem2413599)). Qed.
Lemma lem2413601 : term927.
Proof. exact (EQ_MP (@lem2413600) (@lem0)). Qed.
Lemma lem2413602 : term1081.
Proof. exact (@lem2413591 (@lem2413601)). Qed.
Lemma lem2413604 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413605 : term927 = term928.
Proof. exact (@lem2413604 (NUMERAL 0) term268). Qed.
Lemma lem2413606 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413607 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413608 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413607 h1) (fun h1 : term928 = True => @lem2413606)). Qed.
Lemma lem2413609 : term928 = True.
Proof. exact (EQ_MP (@lem2413608) (@lem2413606)). Qed.
Lemma lem2413610 : term927 = True.
Proof. exact (TRANS (@lem2413605) (@lem2413609)). Qed.
Lemma lem2413611 : True = term927.
Proof. exact (SYM (@lem2413610)). Qed.
Lemma lem2413612 : term927.
Proof. exact (EQ_MP (@lem2413611) (@lem0)). Qed.
Lemma lem2413613 : term1079 = term1082.
Proof. exact (@lem2413602 (@lem2413612)). Qed.
Lemma lem2413615 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413616 : term897 = term908.
Proof. exact (@lem2413615 term268 term268). Qed.
Lemma lem2413617 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413618 : term905 = term268.
Proof. exact (EQ_MP (@lem2413617) (@lem940073)). Qed.
Lemma lem2413619 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413620 : term903 = term267.
Proof. exact (MK_COMB (@lem2413619) (@lem2413618)). Qed.
Lemma lem2413621 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413622 : term908 = term885.
Proof. exact (MK_COMB (@lem2413621) (@lem2413620)). Qed.
Lemma lem2413623 : term897 = term885.
Proof. exact (TRANS (@lem2413616) (@lem2413622)). Qed.
Lemma lem2413625 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413626 : term938 = term324.
Proof. exact (@lem2413625 term268). Qed.
Lemma lem2413627 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413628 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413627) (@lem2413626)). Qed.
Lemma lem2413629 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413628) (@lem2413623)). Qed.
Lemma lem2413631 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413632 : term1076 = term1086.
Proof. exact (@lem2413631 (NUMERAL 0) term268). Qed.
Lemma lem2413633 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413634 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413635 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413634 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413633)). Qed.
Lemma lem2413636 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413635) (@lem2413633)). Qed.
Lemma lem2413637 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413638 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413639 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413638) (@lem2413637)). Qed.
Lemma lem2413640 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413639) (@lem2413636)). Qed.
Lemma lem2413642 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413643 : term1086 = False.
Proof. exact (TRANS (@lem2413640) (@lem2413642)). Qed.
Lemma lem2413644 : term1076 = False.
Proof. exact (TRANS (@lem2413632) (@lem2413643)). Qed.
Lemma lem2413645 : term1082 = False.
Proof. exact (TRANS (@lem2413629) (@lem2413644)). Qed.
Lemma lem2413646 : term1079 = False.
Proof. exact (TRANS (@lem2413613) (@lem2413645)). Qed.
Lemma lem2413647 : term1076 = False.
Proof. exact (TRANS (@lem2413590) (@lem2413646)). Qed.
Lemma lem2413648 : term951 = False.
Proof. exact (TRANS (@lem2413581) (@lem2413647)). Qed.
Lemma lem2413649 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413648) (@lem2413578 h1)). Qed.
Lemma lem2413650 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2413505 h1) (fun h0 : term951 => @lem2413577 h0) (fun h0 : term951 => @lem2413649 h0)). Qed.
Lemma lem2413651 (h1 : term1072) : term1072.
Proof. exact (h1). Qed.
Lemma lem2413652 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2413653 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413655 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413656 : term951 = term1076.
Proof. exact (@lem2413655 term324 term885). Qed.
Lemma lem2413658 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413659 : term885 = term894.
Proof. exact (@lem2413658 term268). Qed.
Lemma lem2413661 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413662 : term324 = term941.
Proof. exact (@lem2413661 (NUMERAL 0)). Qed.
Lemma lem2413663 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413664 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413663) (@lem2413662)). Qed.
Lemma lem2413665 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413664) (@lem2413659)). Qed.
Lemma lem2413666 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413668 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413669 : term927 = term928.
Proof. exact (@lem2413668 (NUMERAL 0) term268). Qed.
Lemma lem2413670 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413671 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413672 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413671 h1) (fun h1 : term928 = True => @lem2413670)). Qed.
Lemma lem2413673 : term928 = True.
Proof. exact (EQ_MP (@lem2413672) (@lem2413670)). Qed.
Lemma lem2413674 : term927 = True.
Proof. exact (TRANS (@lem2413669) (@lem2413673)). Qed.
Lemma lem2413675 : True = term927.
Proof. exact (SYM (@lem2413674)). Qed.
Lemma lem2413676 : term927.
Proof. exact (EQ_MP (@lem2413675) (@lem0)). Qed.
Lemma lem2413677 : term1081.
Proof. exact (@lem2413666 (@lem2413676)). Qed.
Lemma lem2413679 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413680 : term927 = term928.
Proof. exact (@lem2413679 (NUMERAL 0) term268). Qed.
Lemma lem2413681 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413682 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413683 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413682 h1) (fun h1 : term928 = True => @lem2413681)). Qed.
Lemma lem2413684 : term928 = True.
Proof. exact (EQ_MP (@lem2413683) (@lem2413681)). Qed.
Lemma lem2413685 : term927 = True.
Proof. exact (TRANS (@lem2413680) (@lem2413684)). Qed.
Lemma lem2413686 : True = term927.
Proof. exact (SYM (@lem2413685)). Qed.
Lemma lem2413687 : term927.
Proof. exact (EQ_MP (@lem2413686) (@lem0)). Qed.
Lemma lem2413688 : term1079 = term1082.
Proof. exact (@lem2413677 (@lem2413687)). Qed.
Lemma lem2413690 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413691 : term897 = term908.
Proof. exact (@lem2413690 term268 term268). Qed.
Lemma lem2413692 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413693 : term905 = term268.
Proof. exact (EQ_MP (@lem2413692) (@lem940073)). Qed.
Lemma lem2413694 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413695 : term903 = term267.
Proof. exact (MK_COMB (@lem2413694) (@lem2413693)). Qed.
Lemma lem2413696 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413697 : term908 = term885.
Proof. exact (MK_COMB (@lem2413696) (@lem2413695)). Qed.
Lemma lem2413698 : term897 = term885.
Proof. exact (TRANS (@lem2413691) (@lem2413697)). Qed.
Lemma lem2413700 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413701 : term938 = term324.
Proof. exact (@lem2413700 term268). Qed.
Lemma lem2413702 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413703 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413702) (@lem2413701)). Qed.
Lemma lem2413704 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413703) (@lem2413698)). Qed.
Lemma lem2413706 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413707 : term1076 = term1086.
Proof. exact (@lem2413706 (NUMERAL 0) term268). Qed.
Lemma lem2413708 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413709 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413710 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413709 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413708)). Qed.
Lemma lem2413711 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413710) (@lem2413708)). Qed.
Lemma lem2413712 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413714 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413713) (@lem2413712)). Qed.
Lemma lem2413715 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413714) (@lem2413711)). Qed.
Lemma lem2413717 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413718 : term1086 = False.
Proof. exact (TRANS (@lem2413715) (@lem2413717)). Qed.
Lemma lem2413719 : term1076 = False.
Proof. exact (TRANS (@lem2413707) (@lem2413718)). Qed.
Lemma lem2413720 : term1082 = False.
Proof. exact (TRANS (@lem2413704) (@lem2413719)). Qed.
Lemma lem2413721 : term1079 = False.
Proof. exact (TRANS (@lem2413688) (@lem2413720)). Qed.
Lemma lem2413722 : term1076 = False.
Proof. exact (TRANS (@lem2413665) (@lem2413721)). Qed.
Lemma lem2413723 : term951 = False.
Proof. exact (TRANS (@lem2413656) (@lem2413722)). Qed.
Lemma lem2413724 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413723) (@lem2413653 h1)). Qed.
Lemma lem2413725 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413727 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413728 : term951 = term1076.
Proof. exact (@lem2413727 term324 term885). Qed.
Lemma lem2413730 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413731 : term885 = term894.
Proof. exact (@lem2413730 term268). Qed.
Lemma lem2413733 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413734 : term324 = term941.
Proof. exact (@lem2413733 (NUMERAL 0)). Qed.
Lemma lem2413735 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413736 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413735) (@lem2413734)). Qed.
Lemma lem2413737 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413736) (@lem2413731)). Qed.
Lemma lem2413738 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413740 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413741 : term927 = term928.
Proof. exact (@lem2413740 (NUMERAL 0) term268). Qed.
Lemma lem2413742 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413743 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413744 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413743 h1) (fun h1 : term928 = True => @lem2413742)). Qed.
Lemma lem2413745 : term928 = True.
Proof. exact (EQ_MP (@lem2413744) (@lem2413742)). Qed.
Lemma lem2413746 : term927 = True.
Proof. exact (TRANS (@lem2413741) (@lem2413745)). Qed.
Lemma lem2413747 : True = term927.
Proof. exact (SYM (@lem2413746)). Qed.
Lemma lem2413748 : term927.
Proof. exact (EQ_MP (@lem2413747) (@lem0)). Qed.
Lemma lem2413749 : term1081.
Proof. exact (@lem2413738 (@lem2413748)). Qed.
Lemma lem2413751 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413752 : term927 = term928.
Proof. exact (@lem2413751 (NUMERAL 0) term268). Qed.
Lemma lem2413753 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413754 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413755 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413754 h1) (fun h1 : term928 = True => @lem2413753)). Qed.
Lemma lem2413756 : term928 = True.
Proof. exact (EQ_MP (@lem2413755) (@lem2413753)). Qed.
Lemma lem2413757 : term927 = True.
Proof. exact (TRANS (@lem2413752) (@lem2413756)). Qed.
Lemma lem2413758 : True = term927.
Proof. exact (SYM (@lem2413757)). Qed.
Lemma lem2413759 : term927.
Proof. exact (EQ_MP (@lem2413758) (@lem0)). Qed.
Lemma lem2413760 : term1079 = term1082.
Proof. exact (@lem2413749 (@lem2413759)). Qed.
Lemma lem2413762 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413763 : term897 = term908.
Proof. exact (@lem2413762 term268 term268). Qed.
Lemma lem2413764 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413765 : term905 = term268.
Proof. exact (EQ_MP (@lem2413764) (@lem940073)). Qed.
Lemma lem2413766 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413767 : term903 = term267.
Proof. exact (MK_COMB (@lem2413766) (@lem2413765)). Qed.
Lemma lem2413768 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413769 : term908 = term885.
Proof. exact (MK_COMB (@lem2413768) (@lem2413767)). Qed.
Lemma lem2413770 : term897 = term885.
Proof. exact (TRANS (@lem2413763) (@lem2413769)). Qed.
Lemma lem2413772 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413773 : term938 = term324.
Proof. exact (@lem2413772 term268). Qed.
Lemma lem2413774 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413775 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413774) (@lem2413773)). Qed.
Lemma lem2413776 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413775) (@lem2413770)). Qed.
Lemma lem2413778 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413779 : term1076 = term1086.
Proof. exact (@lem2413778 (NUMERAL 0) term268). Qed.
Lemma lem2413780 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413781 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413782 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413781 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413780)). Qed.
Lemma lem2413783 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413782) (@lem2413780)). Qed.
Lemma lem2413784 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413785 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413786 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413785) (@lem2413784)). Qed.
Lemma lem2413787 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413786) (@lem2413783)). Qed.
Lemma lem2413789 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413790 : term1086 = False.
Proof. exact (TRANS (@lem2413787) (@lem2413789)). Qed.
Lemma lem2413791 : term1076 = False.
Proof. exact (TRANS (@lem2413779) (@lem2413790)). Qed.
Lemma lem2413792 : term1082 = False.
Proof. exact (TRANS (@lem2413776) (@lem2413791)). Qed.
Lemma lem2413793 : term1079 = False.
Proof. exact (TRANS (@lem2413760) (@lem2413792)). Qed.
Lemma lem2413794 : term1076 = False.
Proof. exact (TRANS (@lem2413737) (@lem2413793)). Qed.
Lemma lem2413795 : term951 = False.
Proof. exact (TRANS (@lem2413728) (@lem2413794)). Qed.
Lemma lem2413796 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413795) (@lem2413725 h1)). Qed.
Lemma lem2413797 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2413652 h1) (fun h0 : term951 => @lem2413724 h0) (fun h0 : term951 => @lem2413796 h0)). Qed.
Lemma lem2413798 (h1 : term1071) : term1071.
Proof. exact (h1). Qed.
Lemma lem2413799 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2413800 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413802 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413803 : term951 = term1076.
Proof. exact (@lem2413802 term324 term885). Qed.
Lemma lem2413805 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413806 : term885 = term894.
Proof. exact (@lem2413805 term268). Qed.
Lemma lem2413808 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413809 : term324 = term941.
Proof. exact (@lem2413808 (NUMERAL 0)). Qed.
Lemma lem2413810 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413811 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413810) (@lem2413809)). Qed.
Lemma lem2413812 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413811) (@lem2413806)). Qed.
Lemma lem2413813 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413815 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413816 : term927 = term928.
Proof. exact (@lem2413815 (NUMERAL 0) term268). Qed.
Lemma lem2413817 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413818 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413819 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413818 h1) (fun h1 : term928 = True => @lem2413817)). Qed.
Lemma lem2413820 : term928 = True.
Proof. exact (EQ_MP (@lem2413819) (@lem2413817)). Qed.
Lemma lem2413821 : term927 = True.
Proof. exact (TRANS (@lem2413816) (@lem2413820)). Qed.
Lemma lem2413822 : True = term927.
Proof. exact (SYM (@lem2413821)). Qed.
Lemma lem2413823 : term927.
Proof. exact (EQ_MP (@lem2413822) (@lem0)). Qed.
Lemma lem2413824 : term1081.
Proof. exact (@lem2413813 (@lem2413823)). Qed.
Lemma lem2413826 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413827 : term927 = term928.
Proof. exact (@lem2413826 (NUMERAL 0) term268). Qed.
Lemma lem2413828 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413829 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413830 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413829 h1) (fun h1 : term928 = True => @lem2413828)). Qed.
Lemma lem2413831 : term928 = True.
Proof. exact (EQ_MP (@lem2413830) (@lem2413828)). Qed.
Lemma lem2413832 : term927 = True.
Proof. exact (TRANS (@lem2413827) (@lem2413831)). Qed.
Lemma lem2413833 : True = term927.
Proof. exact (SYM (@lem2413832)). Qed.
Lemma lem2413834 : term927.
Proof. exact (EQ_MP (@lem2413833) (@lem0)). Qed.
Lemma lem2413835 : term1079 = term1082.
Proof. exact (@lem2413824 (@lem2413834)). Qed.
Lemma lem2413837 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413838 : term897 = term908.
Proof. exact (@lem2413837 term268 term268). Qed.
Lemma lem2413839 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413840 : term905 = term268.
Proof. exact (EQ_MP (@lem2413839) (@lem940073)). Qed.
Lemma lem2413841 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413842 : term903 = term267.
Proof. exact (MK_COMB (@lem2413841) (@lem2413840)). Qed.
Lemma lem2413843 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413844 : term908 = term885.
Proof. exact (MK_COMB (@lem2413843) (@lem2413842)). Qed.
Lemma lem2413845 : term897 = term885.
Proof. exact (TRANS (@lem2413838) (@lem2413844)). Qed.
Lemma lem2413847 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413848 : term938 = term324.
Proof. exact (@lem2413847 term268). Qed.
Lemma lem2413849 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413850 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413849) (@lem2413848)). Qed.
Lemma lem2413851 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413850) (@lem2413845)). Qed.
Lemma lem2413853 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413854 : term1076 = term1086.
Proof. exact (@lem2413853 (NUMERAL 0) term268). Qed.
Lemma lem2413855 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413856 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413857 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413856 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413855)). Qed.
Lemma lem2413858 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413857) (@lem2413855)). Qed.
Lemma lem2413859 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413860 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413861 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413860) (@lem2413859)). Qed.
Lemma lem2413862 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413861) (@lem2413858)). Qed.
Lemma lem2413864 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413865 : term1086 = False.
Proof. exact (TRANS (@lem2413862) (@lem2413864)). Qed.
Lemma lem2413866 : term1076 = False.
Proof. exact (TRANS (@lem2413854) (@lem2413865)). Qed.
Lemma lem2413867 : term1082 = False.
Proof. exact (TRANS (@lem2413851) (@lem2413866)). Qed.
Lemma lem2413868 : term1079 = False.
Proof. exact (TRANS (@lem2413835) (@lem2413867)). Qed.
Lemma lem2413869 : term1076 = False.
Proof. exact (TRANS (@lem2413812) (@lem2413868)). Qed.
Lemma lem2413870 : term951 = False.
Proof. exact (TRANS (@lem2413803) (@lem2413869)). Qed.
Lemma lem2413871 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413870) (@lem2413800 h1)). Qed.
Lemma lem2413872 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413874 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413875 : term951 = term1076.
Proof. exact (@lem2413874 term324 term885). Qed.
Lemma lem2413877 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413878 : term885 = term894.
Proof. exact (@lem2413877 term268). Qed.
Lemma lem2413880 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413881 : term324 = term941.
Proof. exact (@lem2413880 (NUMERAL 0)). Qed.
Lemma lem2413882 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413883 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413882) (@lem2413881)). Qed.
Lemma lem2413884 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413883) (@lem2413878)). Qed.
Lemma lem2413885 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413887 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413888 : term927 = term928.
Proof. exact (@lem2413887 (NUMERAL 0) term268). Qed.
Lemma lem2413889 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413890 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413891 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413890 h1) (fun h1 : term928 = True => @lem2413889)). Qed.
Lemma lem2413892 : term928 = True.
Proof. exact (EQ_MP (@lem2413891) (@lem2413889)). Qed.
Lemma lem2413893 : term927 = True.
Proof. exact (TRANS (@lem2413888) (@lem2413892)). Qed.
Lemma lem2413894 : True = term927.
Proof. exact (SYM (@lem2413893)). Qed.
Lemma lem2413895 : term927.
Proof. exact (EQ_MP (@lem2413894) (@lem0)). Qed.
Lemma lem2413896 : term1081.
Proof. exact (@lem2413885 (@lem2413895)). Qed.
Lemma lem2413898 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413899 : term927 = term928.
Proof. exact (@lem2413898 (NUMERAL 0) term268). Qed.
Lemma lem2413900 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413901 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413902 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413901 h1) (fun h1 : term928 = True => @lem2413900)). Qed.
Lemma lem2413903 : term928 = True.
Proof. exact (EQ_MP (@lem2413902) (@lem2413900)). Qed.
Lemma lem2413904 : term927 = True.
Proof. exact (TRANS (@lem2413899) (@lem2413903)). Qed.
Lemma lem2413905 : True = term927.
Proof. exact (SYM (@lem2413904)). Qed.
Lemma lem2413906 : term927.
Proof. exact (EQ_MP (@lem2413905) (@lem0)). Qed.
Lemma lem2413907 : term1079 = term1082.
Proof. exact (@lem2413896 (@lem2413906)). Qed.
Lemma lem2413909 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413910 : term897 = term908.
Proof. exact (@lem2413909 term268 term268). Qed.
Lemma lem2413911 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413912 : term905 = term268.
Proof. exact (EQ_MP (@lem2413911) (@lem940073)). Qed.
Lemma lem2413913 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413914 : term903 = term267.
Proof. exact (MK_COMB (@lem2413913) (@lem2413912)). Qed.
Lemma lem2413915 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413916 : term908 = term885.
Proof. exact (MK_COMB (@lem2413915) (@lem2413914)). Qed.
Lemma lem2413917 : term897 = term885.
Proof. exact (TRANS (@lem2413910) (@lem2413916)). Qed.
Lemma lem2413919 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413920 : term938 = term324.
Proof. exact (@lem2413919 term268). Qed.
Lemma lem2413921 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413922 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413921) (@lem2413920)). Qed.
Lemma lem2413923 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413922) (@lem2413917)). Qed.
Lemma lem2413925 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2413926 : term1076 = term1086.
Proof. exact (@lem2413925 (NUMERAL 0) term268). Qed.
Lemma lem2413927 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413928 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2413929 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413928 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2413927)). Qed.
Lemma lem2413930 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2413929) (@lem2413927)). Qed.
Lemma lem2413931 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2413932 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2413933 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2413932) (@lem2413931)). Qed.
Lemma lem2413934 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2413933) (@lem2413930)). Qed.
Lemma lem2413936 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2413937 : term1086 = False.
Proof. exact (TRANS (@lem2413934) (@lem2413936)). Qed.
Lemma lem2413938 : term1076 = False.
Proof. exact (TRANS (@lem2413926) (@lem2413937)). Qed.
Lemma lem2413939 : term1082 = False.
Proof. exact (TRANS (@lem2413923) (@lem2413938)). Qed.
Lemma lem2413940 : term1079 = False.
Proof. exact (TRANS (@lem2413907) (@lem2413939)). Qed.
Lemma lem2413941 : term1076 = False.
Proof. exact (TRANS (@lem2413884) (@lem2413940)). Qed.
Lemma lem2413942 : term951 = False.
Proof. exact (TRANS (@lem2413875) (@lem2413941)). Qed.
Lemma lem2413943 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2413942) (@lem2413872 h1)). Qed.
Lemma lem2413944 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2413799 h1) (fun h0 : term951 => @lem2413871 h0) (fun h0 : term951 => @lem2413943 h0)). Qed.
Lemma lem2413945 (h1 : term1070) : term1070.
Proof. exact (h1). Qed.
Lemma lem2413946 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2413947 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2413949 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2413950 : term951 = term1076.
Proof. exact (@lem2413949 term324 term885). Qed.
Lemma lem2413952 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2413953 : term885 = term894.
Proof. exact (@lem2413952 term268). Qed.
Lemma lem2413955 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2413956 : term324 = term941.
Proof. exact (@lem2413955 (NUMERAL 0)). Qed.
Lemma lem2413957 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413958 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2413957) (@lem2413956)). Qed.
Lemma lem2413959 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2413958) (@lem2413953)). Qed.
Lemma lem2413960 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2413962 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413963 : term927 = term928.
Proof. exact (@lem2413962 (NUMERAL 0) term268). Qed.
Lemma lem2413964 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413965 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413966 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413965 h1) (fun h1 : term928 = True => @lem2413964)). Qed.
Lemma lem2413967 : term928 = True.
Proof. exact (EQ_MP (@lem2413966) (@lem2413964)). Qed.
Lemma lem2413968 : term927 = True.
Proof. exact (TRANS (@lem2413963) (@lem2413967)). Qed.
Lemma lem2413969 : True = term927.
Proof. exact (SYM (@lem2413968)). Qed.
Lemma lem2413970 : term927.
Proof. exact (EQ_MP (@lem2413969) (@lem0)). Qed.
Lemma lem2413971 : term1081.
Proof. exact (@lem2413960 (@lem2413970)). Qed.
Lemma lem2413973 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2413974 : term927 = term928.
Proof. exact (@lem2413973 (NUMERAL 0) term268). Qed.
Lemma lem2413975 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2413976 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2413977 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2413976 h1) (fun h1 : term928 = True => @lem2413975)). Qed.
Lemma lem2413978 : term928 = True.
Proof. exact (EQ_MP (@lem2413977) (@lem2413975)). Qed.
Lemma lem2413979 : term927 = True.
Proof. exact (TRANS (@lem2413974) (@lem2413978)). Qed.
Lemma lem2413980 : True = term927.
Proof. exact (SYM (@lem2413979)). Qed.
Lemma lem2413981 : term927.
Proof. exact (EQ_MP (@lem2413980) (@lem0)). Qed.
Lemma lem2413982 : term1079 = term1082.
Proof. exact (@lem2413971 (@lem2413981)). Qed.
Lemma lem2413984 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2413985 : term897 = term908.
Proof. exact (@lem2413984 term268 term268). Qed.
Lemma lem2413986 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2413987 : term905 = term268.
Proof. exact (EQ_MP (@lem2413986) (@lem940073)). Qed.
Lemma lem2413988 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2413989 : term903 = term267.
Proof. exact (MK_COMB (@lem2413988) (@lem2413987)). Qed.
Lemma lem2413990 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2413991 : term908 = term885.
Proof. exact (MK_COMB (@lem2413990) (@lem2413989)). Qed.
Lemma lem2413992 : term897 = term885.
Proof. exact (TRANS (@lem2413985) (@lem2413991)). Qed.
Lemma lem2413994 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2413995 : term938 = term324.
Proof. exact (@lem2413994 term268). Qed.
Lemma lem2413996 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2413997 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2413996) (@lem2413995)). Qed.
Lemma lem2413998 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2413997) (@lem2413992)). Qed.
Lemma lem2414000 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2414001 : term1076 = term1086.
Proof. exact (@lem2414000 (NUMERAL 0) term268). Qed.
Lemma lem2414002 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414003 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2414004 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414003 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2414002)). Qed.
Lemma lem2414005 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2414004) (@lem2414002)). Qed.
Lemma lem2414006 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2414007 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2414008 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2414007) (@lem2414006)). Qed.
Lemma lem2414009 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2414008) (@lem2414005)). Qed.
Lemma lem2414011 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2414012 : term1086 = False.
Proof. exact (TRANS (@lem2414009) (@lem2414011)). Qed.
Lemma lem2414013 : term1076 = False.
Proof. exact (TRANS (@lem2414001) (@lem2414012)). Qed.
Lemma lem2414014 : term1082 = False.
Proof. exact (TRANS (@lem2413998) (@lem2414013)). Qed.
Lemma lem2414015 : term1079 = False.
Proof. exact (TRANS (@lem2413982) (@lem2414014)). Qed.
Lemma lem2414016 : term1076 = False.
Proof. exact (TRANS (@lem2413959) (@lem2414015)). Qed.
Lemma lem2414017 : term951 = False.
Proof. exact (TRANS (@lem2413950) (@lem2414016)). Qed.
Lemma lem2414018 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2414017) (@lem2413947 h1)). Qed.
Lemma lem2414019 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2414021 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2414022 : term951 = term1076.
Proof. exact (@lem2414021 term324 term885). Qed.
Lemma lem2414024 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414025 : term885 = term894.
Proof. exact (@lem2414024 term268). Qed.
Lemma lem2414027 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2414028 : term324 = term941.
Proof. exact (@lem2414027 (NUMERAL 0)). Qed.
Lemma lem2414029 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414030 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2414029) (@lem2414028)). Qed.
Lemma lem2414031 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2414030) (@lem2414025)). Qed.
Lemma lem2414032 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2414034 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414035 : term927 = term928.
Proof. exact (@lem2414034 (NUMERAL 0) term268). Qed.
Lemma lem2414036 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414037 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414038 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414037 h1) (fun h1 : term928 = True => @lem2414036)). Qed.
Lemma lem2414039 : term928 = True.
Proof. exact (EQ_MP (@lem2414038) (@lem2414036)). Qed.
Lemma lem2414040 : term927 = True.
Proof. exact (TRANS (@lem2414035) (@lem2414039)). Qed.
Lemma lem2414041 : True = term927.
Proof. exact (SYM (@lem2414040)). Qed.
Lemma lem2414042 : term927.
Proof. exact (EQ_MP (@lem2414041) (@lem0)). Qed.
Lemma lem2414043 : term1081.
Proof. exact (@lem2414032 (@lem2414042)). Qed.
Lemma lem2414045 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414046 : term927 = term928.
Proof. exact (@lem2414045 (NUMERAL 0) term268). Qed.
Lemma lem2414047 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414048 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414049 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414048 h1) (fun h1 : term928 = True => @lem2414047)). Qed.
Lemma lem2414050 : term928 = True.
Proof. exact (EQ_MP (@lem2414049) (@lem2414047)). Qed.
Lemma lem2414051 : term927 = True.
Proof. exact (TRANS (@lem2414046) (@lem2414050)). Qed.
Lemma lem2414052 : True = term927.
Proof. exact (SYM (@lem2414051)). Qed.
Lemma lem2414053 : term927.
Proof. exact (EQ_MP (@lem2414052) (@lem0)). Qed.
Lemma lem2414054 : term1079 = term1082.
Proof. exact (@lem2414043 (@lem2414053)). Qed.
Lemma lem2414056 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2414057 : term897 = term908.
Proof. exact (@lem2414056 term268 term268). Qed.
Lemma lem2414058 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414059 : term905 = term268.
Proof. exact (EQ_MP (@lem2414058) (@lem940073)). Qed.
Lemma lem2414060 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414061 : term903 = term267.
Proof. exact (MK_COMB (@lem2414060) (@lem2414059)). Qed.
Lemma lem2414062 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414063 : term908 = term885.
Proof. exact (MK_COMB (@lem2414062) (@lem2414061)). Qed.
Lemma lem2414064 : term897 = term885.
Proof. exact (TRANS (@lem2414057) (@lem2414063)). Qed.
Lemma lem2414066 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2414067 : term938 = term324.
Proof. exact (@lem2414066 term268). Qed.
Lemma lem2414068 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414069 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2414068) (@lem2414067)). Qed.
Lemma lem2414070 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2414069) (@lem2414064)). Qed.
Lemma lem2414072 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2414073 : term1076 = term1086.
Proof. exact (@lem2414072 (NUMERAL 0) term268). Qed.
Lemma lem2414074 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414075 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2414076 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414075 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2414074)). Qed.
Lemma lem2414077 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2414076) (@lem2414074)). Qed.
Lemma lem2414078 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2414079 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2414080 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2414079) (@lem2414078)). Qed.
Lemma lem2414081 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2414080) (@lem2414077)). Qed.
Lemma lem2414083 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2414084 : term1086 = False.
Proof. exact (TRANS (@lem2414081) (@lem2414083)). Qed.
Lemma lem2414085 : term1076 = False.
Proof. exact (TRANS (@lem2414073) (@lem2414084)). Qed.
Lemma lem2414086 : term1082 = False.
Proof. exact (TRANS (@lem2414070) (@lem2414085)). Qed.
Lemma lem2414087 : term1079 = False.
Proof. exact (TRANS (@lem2414054) (@lem2414086)). Qed.
Lemma lem2414088 : term1076 = False.
Proof. exact (TRANS (@lem2414031) (@lem2414087)). Qed.
Lemma lem2414089 : term951 = False.
Proof. exact (TRANS (@lem2414022) (@lem2414088)). Qed.
Lemma lem2414090 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2414089) (@lem2414019 h1)). Qed.
Lemma lem2414091 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2413946 h1) (fun h0 : term951 => @lem2414018 h0) (fun h0 : term951 => @lem2414090 h0)). Qed.
Lemma lem2414092 (h1 : term1069) : term1069.
Proof. exact (h1). Qed.
Lemma lem2414093 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2414094 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2414096 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2414097 : term951 = term1076.
Proof. exact (@lem2414096 term324 term885). Qed.
Lemma lem2414099 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414100 : term885 = term894.
Proof. exact (@lem2414099 term268). Qed.
Lemma lem2414102 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2414103 : term324 = term941.
Proof. exact (@lem2414102 (NUMERAL 0)). Qed.
Lemma lem2414104 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414105 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2414104) (@lem2414103)). Qed.
Lemma lem2414106 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2414105) (@lem2414100)). Qed.
Lemma lem2414107 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2414109 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414110 : term927 = term928.
Proof. exact (@lem2414109 (NUMERAL 0) term268). Qed.
Lemma lem2414111 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414112 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414113 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414112 h1) (fun h1 : term928 = True => @lem2414111)). Qed.
Lemma lem2414114 : term928 = True.
Proof. exact (EQ_MP (@lem2414113) (@lem2414111)). Qed.
Lemma lem2414115 : term927 = True.
Proof. exact (TRANS (@lem2414110) (@lem2414114)). Qed.
Lemma lem2414116 : True = term927.
Proof. exact (SYM (@lem2414115)). Qed.
Lemma lem2414117 : term927.
Proof. exact (EQ_MP (@lem2414116) (@lem0)). Qed.
Lemma lem2414118 : term1081.
Proof. exact (@lem2414107 (@lem2414117)). Qed.
Lemma lem2414120 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414121 : term927 = term928.
Proof. exact (@lem2414120 (NUMERAL 0) term268). Qed.
Lemma lem2414122 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414123 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414124 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414123 h1) (fun h1 : term928 = True => @lem2414122)). Qed.
Lemma lem2414125 : term928 = True.
Proof. exact (EQ_MP (@lem2414124) (@lem2414122)). Qed.
Lemma lem2414126 : term927 = True.
Proof. exact (TRANS (@lem2414121) (@lem2414125)). Qed.
Lemma lem2414127 : True = term927.
Proof. exact (SYM (@lem2414126)). Qed.
Lemma lem2414128 : term927.
Proof. exact (EQ_MP (@lem2414127) (@lem0)). Qed.
Lemma lem2414129 : term1079 = term1082.
Proof. exact (@lem2414118 (@lem2414128)). Qed.
Lemma lem2414131 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2414132 : term897 = term908.
Proof. exact (@lem2414131 term268 term268). Qed.
Lemma lem2414133 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414134 : term905 = term268.
Proof. exact (EQ_MP (@lem2414133) (@lem940073)). Qed.
Lemma lem2414135 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414136 : term903 = term267.
Proof. exact (MK_COMB (@lem2414135) (@lem2414134)). Qed.
Lemma lem2414137 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414138 : term908 = term885.
Proof. exact (MK_COMB (@lem2414137) (@lem2414136)). Qed.
Lemma lem2414139 : term897 = term885.
Proof. exact (TRANS (@lem2414132) (@lem2414138)). Qed.
Lemma lem2414141 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2414142 : term938 = term324.
Proof. exact (@lem2414141 term268). Qed.
Lemma lem2414143 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414144 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2414143) (@lem2414142)). Qed.
Lemma lem2414145 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2414144) (@lem2414139)). Qed.
Lemma lem2414147 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2414148 : term1076 = term1086.
Proof. exact (@lem2414147 (NUMERAL 0) term268). Qed.
Lemma lem2414149 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414150 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2414151 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414150 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2414149)). Qed.
Lemma lem2414152 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2414151) (@lem2414149)). Qed.
Lemma lem2414153 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2414154 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2414155 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2414154) (@lem2414153)). Qed.
Lemma lem2414156 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2414155) (@lem2414152)). Qed.
Lemma lem2414158 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2414159 : term1086 = False.
Proof. exact (TRANS (@lem2414156) (@lem2414158)). Qed.
Lemma lem2414160 : term1076 = False.
Proof. exact (TRANS (@lem2414148) (@lem2414159)). Qed.
Lemma lem2414161 : term1082 = False.
Proof. exact (TRANS (@lem2414145) (@lem2414160)). Qed.
Lemma lem2414162 : term1079 = False.
Proof. exact (TRANS (@lem2414129) (@lem2414161)). Qed.
Lemma lem2414163 : term1076 = False.
Proof. exact (TRANS (@lem2414106) (@lem2414162)). Qed.
Lemma lem2414164 : term951 = False.
Proof. exact (TRANS (@lem2414097) (@lem2414163)). Qed.
Lemma lem2414165 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2414164) (@lem2414094 h1)). Qed.
Lemma lem2414166 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2414168 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2414169 : term951 = term1076.
Proof. exact (@lem2414168 term324 term885). Qed.
Lemma lem2414171 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414172 : term885 = term894.
Proof. exact (@lem2414171 term268). Qed.
Lemma lem2414174 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2414175 : term324 = term941.
Proof. exact (@lem2414174 (NUMERAL 0)). Qed.
Lemma lem2414176 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414177 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2414176) (@lem2414175)). Qed.
Lemma lem2414178 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2414177) (@lem2414172)). Qed.
Lemma lem2414179 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2414181 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414182 : term927 = term928.
Proof. exact (@lem2414181 (NUMERAL 0) term268). Qed.
Lemma lem2414183 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414184 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414185 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414184 h1) (fun h1 : term928 = True => @lem2414183)). Qed.
Lemma lem2414186 : term928 = True.
Proof. exact (EQ_MP (@lem2414185) (@lem2414183)). Qed.
Lemma lem2414187 : term927 = True.
Proof. exact (TRANS (@lem2414182) (@lem2414186)). Qed.
Lemma lem2414188 : True = term927.
Proof. exact (SYM (@lem2414187)). Qed.
Lemma lem2414189 : term927.
Proof. exact (EQ_MP (@lem2414188) (@lem0)). Qed.
Lemma lem2414190 : term1081.
Proof. exact (@lem2414179 (@lem2414189)). Qed.
Lemma lem2414192 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414193 : term927 = term928.
Proof. exact (@lem2414192 (NUMERAL 0) term268). Qed.
Lemma lem2414194 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414195 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414196 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414195 h1) (fun h1 : term928 = True => @lem2414194)). Qed.
Lemma lem2414197 : term928 = True.
Proof. exact (EQ_MP (@lem2414196) (@lem2414194)). Qed.
Lemma lem2414198 : term927 = True.
Proof. exact (TRANS (@lem2414193) (@lem2414197)). Qed.
Lemma lem2414199 : True = term927.
Proof. exact (SYM (@lem2414198)). Qed.
Lemma lem2414200 : term927.
Proof. exact (EQ_MP (@lem2414199) (@lem0)). Qed.
Lemma lem2414201 : term1079 = term1082.
Proof. exact (@lem2414190 (@lem2414200)). Qed.
Lemma lem2414203 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2414204 : term897 = term908.
Proof. exact (@lem2414203 term268 term268). Qed.
Lemma lem2414205 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414206 : term905 = term268.
Proof. exact (EQ_MP (@lem2414205) (@lem940073)). Qed.
Lemma lem2414207 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414208 : term903 = term267.
Proof. exact (MK_COMB (@lem2414207) (@lem2414206)). Qed.
Lemma lem2414209 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414210 : term908 = term885.
Proof. exact (MK_COMB (@lem2414209) (@lem2414208)). Qed.
Lemma lem2414211 : term897 = term885.
Proof. exact (TRANS (@lem2414204) (@lem2414210)). Qed.
Lemma lem2414213 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2414214 : term938 = term324.
Proof. exact (@lem2414213 term268). Qed.
Lemma lem2414215 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414216 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2414215) (@lem2414214)). Qed.
Lemma lem2414217 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2414216) (@lem2414211)). Qed.
Lemma lem2414219 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2414220 : term1076 = term1086.
Proof. exact (@lem2414219 (NUMERAL 0) term268). Qed.
Lemma lem2414221 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414222 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2414223 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414222 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2414221)). Qed.
Lemma lem2414224 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2414223) (@lem2414221)). Qed.
Lemma lem2414225 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2414226 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2414227 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2414226) (@lem2414225)). Qed.
Lemma lem2414228 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2414227) (@lem2414224)). Qed.
Lemma lem2414230 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2414231 : term1086 = False.
Proof. exact (TRANS (@lem2414228) (@lem2414230)). Qed.
Lemma lem2414232 : term1076 = False.
Proof. exact (TRANS (@lem2414220) (@lem2414231)). Qed.
Lemma lem2414233 : term1082 = False.
Proof. exact (TRANS (@lem2414217) (@lem2414232)). Qed.
Lemma lem2414234 : term1079 = False.
Proof. exact (TRANS (@lem2414201) (@lem2414233)). Qed.
Lemma lem2414235 : term1076 = False.
Proof. exact (TRANS (@lem2414178) (@lem2414234)). Qed.
Lemma lem2414236 : term951 = False.
Proof. exact (TRANS (@lem2414169) (@lem2414235)). Qed.
Lemma lem2414237 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2414236) (@lem2414166 h1)). Qed.
Lemma lem2414238 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2414093 h1) (fun h0 : term951 => @lem2414165 h0) (fun h0 : term951 => @lem2414237 h0)). Qed.
Lemma lem2414239 (h1 : term1067) : term1067.
Proof. exact (h1). Qed.
Lemma lem2414240 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2414242 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2414243 : term951 = term1076.
Proof. exact (@lem2414242 term324 term885). Qed.
Lemma lem2414245 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414246 : term885 = term894.
Proof. exact (@lem2414245 term268). Qed.
Lemma lem2414248 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2414249 : term324 = term941.
Proof. exact (@lem2414248 (NUMERAL 0)). Qed.
Lemma lem2414250 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414251 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2414250) (@lem2414249)). Qed.
Lemma lem2414252 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2414251) (@lem2414246)). Qed.
Lemma lem2414253 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2414255 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414256 : term927 = term928.
Proof. exact (@lem2414255 (NUMERAL 0) term268). Qed.
Lemma lem2414257 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414258 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414259 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414258 h1) (fun h1 : term928 = True => @lem2414257)). Qed.
Lemma lem2414260 : term928 = True.
Proof. exact (EQ_MP (@lem2414259) (@lem2414257)). Qed.
Lemma lem2414261 : term927 = True.
Proof. exact (TRANS (@lem2414256) (@lem2414260)). Qed.
Lemma lem2414262 : True = term927.
Proof. exact (SYM (@lem2414261)). Qed.
Lemma lem2414263 : term927.
Proof. exact (EQ_MP (@lem2414262) (@lem0)). Qed.
Lemma lem2414264 : term1081.
Proof. exact (@lem2414253 (@lem2414263)). Qed.
Lemma lem2414266 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414267 : term927 = term928.
Proof. exact (@lem2414266 (NUMERAL 0) term268). Qed.
Lemma lem2414268 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414269 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414270 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414269 h1) (fun h1 : term928 = True => @lem2414268)). Qed.
Lemma lem2414271 : term928 = True.
Proof. exact (EQ_MP (@lem2414270) (@lem2414268)). Qed.
Lemma lem2414272 : term927 = True.
Proof. exact (TRANS (@lem2414267) (@lem2414271)). Qed.
Lemma lem2414273 : True = term927.
Proof. exact (SYM (@lem2414272)). Qed.
Lemma lem2414274 : term927.
Proof. exact (EQ_MP (@lem2414273) (@lem0)). Qed.
Lemma lem2414275 : term1079 = term1082.
Proof. exact (@lem2414264 (@lem2414274)). Qed.
Lemma lem2414277 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2414278 : term897 = term908.
Proof. exact (@lem2414277 term268 term268). Qed.
Lemma lem2414279 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414280 : term905 = term268.
Proof. exact (EQ_MP (@lem2414279) (@lem940073)). Qed.
Lemma lem2414281 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414282 : term903 = term267.
Proof. exact (MK_COMB (@lem2414281) (@lem2414280)). Qed.
Lemma lem2414283 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414284 : term908 = term885.
Proof. exact (MK_COMB (@lem2414283) (@lem2414282)). Qed.
Lemma lem2414285 : term897 = term885.
Proof. exact (TRANS (@lem2414278) (@lem2414284)). Qed.
Lemma lem2414287 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2414288 : term938 = term324.
Proof. exact (@lem2414287 term268). Qed.
Lemma lem2414289 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414290 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2414289) (@lem2414288)). Qed.
Lemma lem2414291 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2414290) (@lem2414285)). Qed.
Lemma lem2414293 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2414294 : term1076 = term1086.
Proof. exact (@lem2414293 (NUMERAL 0) term268). Qed.
Lemma lem2414295 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414296 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2414297 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414296 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2414295)). Qed.
Lemma lem2414298 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2414297) (@lem2414295)). Qed.
Lemma lem2414299 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2414300 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2414301 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2414300) (@lem2414299)). Qed.
Lemma lem2414302 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2414301) (@lem2414298)). Qed.
Lemma lem2414304 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2414305 : term1086 = False.
Proof. exact (TRANS (@lem2414302) (@lem2414304)). Qed.
Lemma lem2414306 : term1076 = False.
Proof. exact (TRANS (@lem2414294) (@lem2414305)). Qed.
Lemma lem2414307 : term1082 = False.
Proof. exact (TRANS (@lem2414291) (@lem2414306)). Qed.
Lemma lem2414308 : term1079 = False.
Proof. exact (TRANS (@lem2414275) (@lem2414307)). Qed.
Lemma lem2414309 : term1076 = False.
Proof. exact (TRANS (@lem2414252) (@lem2414308)). Qed.
Lemma lem2414310 : term951 = False.
Proof. exact (TRANS (@lem2414243) (@lem2414309)). Qed.
Lemma lem2414311 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2414310) (@lem2414240 h1)). Qed.
Lemma lem2414312 (h1 : term951) : term951.
Proof. exact (h1). Qed.
Lemma lem2414314 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2414315 : term951 = term1076.
Proof. exact (@lem2414314 term324 term885). Qed.
Lemma lem2414317 (x : nat) : (term892 x) = (term893 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2414318 : term885 = term894.
Proof. exact (@lem2414317 term268). Qed.
Lemma lem2414320 (x : nat) : (real_of_num x) = (term890 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2414321 : term324 = term941.
Proof. exact (@lem2414320 (NUMERAL 0)). Qed.
Lemma lem2414322 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414323 : term1077 = term1078.
Proof. exact (MK_COMB (@lem2414322) (@lem2414321)). Qed.
Lemma lem2414324 : term1076 = term1079.
Proof. exact (MK_COMB (@lem2414323) (@lem2414318)). Qed.
Lemma lem2414325 : term1080.
Proof. exact (@lem1980026 term324 term267 term885 term267). Qed.
Lemma lem2414327 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414328 : term927 = term928.
Proof. exact (@lem2414327 (NUMERAL 0) term268). Qed.
Lemma lem2414329 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414330 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414331 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414330 h1) (fun h1 : term928 = True => @lem2414329)). Qed.
Lemma lem2414332 : term928 = True.
Proof. exact (EQ_MP (@lem2414331) (@lem2414329)). Qed.
Lemma lem2414333 : term927 = True.
Proof. exact (TRANS (@lem2414328) (@lem2414332)). Qed.
Lemma lem2414334 : True = term927.
Proof. exact (SYM (@lem2414333)). Qed.
Lemma lem2414335 : term927.
Proof. exact (EQ_MP (@lem2414334) (@lem0)). Qed.
Lemma lem2414336 : term1081.
Proof. exact (@lem2414325 (@lem2414335)). Qed.
Lemma lem2414338 (m : nat) (n : nat) : (term926 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2414339 : term927 = term928.
Proof. exact (@lem2414338 (NUMERAL 0) term268). Qed.
Lemma lem2414340 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414341 (h1 : term929 = (BIT1 0)) : term928 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2414342 : (term929 = (BIT1 0)) = (term928 = True).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414341 h1) (fun h1 : term928 = True => @lem2414340)). Qed.
Lemma lem2414343 : term928 = True.
Proof. exact (EQ_MP (@lem2414342) (@lem2414340)). Qed.
Lemma lem2414344 : term927 = True.
Proof. exact (TRANS (@lem2414339) (@lem2414343)). Qed.
Lemma lem2414345 : True = term927.
Proof. exact (SYM (@lem2414344)). Qed.
Lemma lem2414346 : term927.
Proof. exact (EQ_MP (@lem2414345) (@lem0)). Qed.
Lemma lem2414347 : term1079 = term1082.
Proof. exact (@lem2414336 (@lem2414346)). Qed.
Lemma lem2414349 (m : nat) (n : nat) : (term906 m n) = (term907 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2414350 : term897 = term908.
Proof. exact (@lem2414349 term268 term268). Qed.
Lemma lem2414351 : (term904 = (BIT1 0)) = (term905 = term268).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2414352 : term905 = term268.
Proof. exact (EQ_MP (@lem2414351) (@lem940073)). Qed.
Lemma lem2414353 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2414354 : term903 = term267.
Proof. exact (MK_COMB (@lem2414353) (@lem2414352)). Qed.
Lemma lem2414355 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2414356 : term908 = term885.
Proof. exact (MK_COMB (@lem2414355) (@lem2414354)). Qed.
Lemma lem2414357 : term897 = term885.
Proof. exact (TRANS (@lem2414350) (@lem2414356)). Qed.
Lemma lem2414359 (x : nat) : (term939 x) = term324.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2414360 : term938 = term324.
Proof. exact (@lem2414359 term268). Qed.
Lemma lem2414361 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2414362 : term1083 = term1077.
Proof. exact (MK_COMB (@lem2414361) (@lem2414360)). Qed.
Lemma lem2414363 : term1082 = term1076.
Proof. exact (MK_COMB (@lem2414362) (@lem2414357)). Qed.
Lemma lem2414365 (m : nat) (n : nat) : (term1084 m n) = (term1085 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2414366 : term1076 = term1086.
Proof. exact (@lem2414365 (NUMERAL 0) term268). Qed.
Lemma lem2414367 : term929 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2414368 (h1 : term929 = (BIT1 0)) : (term268 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2414369 : (term929 = (BIT1 0)) = ((term268 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term929 = (BIT1 0) => @lem2414368 h1) (fun h1 : (term268 = (NUMERAL 0)) = False => @lem2414367)). Qed.
Lemma lem2414370 : (term268 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2414369) (@lem2414367)). Qed.
Lemma lem2414371 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2414372 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2414373 : term1087 = (and True).
Proof. exact (MK_COMB (@lem2414372) (@lem2414371)). Qed.
Lemma lem2414374 : term1086 = (True /\ False).
Proof. exact (MK_COMB (@lem2414373) (@lem2414370)). Qed.
Lemma lem2414376 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2414377 : term1086 = False.
Proof. exact (TRANS (@lem2414374) (@lem2414376)). Qed.
Lemma lem2414378 : term1076 = False.
Proof. exact (TRANS (@lem2414366) (@lem2414377)). Qed.
Lemma lem2414379 : term1082 = False.
Proof. exact (TRANS (@lem2414363) (@lem2414378)). Qed.
Lemma lem2414380 : term1079 = False.
Proof. exact (TRANS (@lem2414347) (@lem2414379)). Qed.
Lemma lem2414381 : term1076 = False.
Proof. exact (TRANS (@lem2414324) (@lem2414380)). Qed.
Lemma lem2414382 : term951 = False.
Proof. exact (TRANS (@lem2414315) (@lem2414381)). Qed.
Lemma lem2414383 (h1 : term951) : False.
Proof. exact (EQ_MP (@lem2414382) (@lem2414312 h1)). Qed.
Lemma lem2414384 (h1 : term1067) : False.
Proof. exact (or_elim (@lem2414239 h1) (fun h0 : term951 => @lem2414311 h0) (fun h0 : term951 => @lem2414383 h0)). Qed.
Lemma lem2414385 (h1 : term1069) : False.
Proof. exact (or_elim (@lem2414092 h1) (fun h0 : term1067 => @lem2414238 h0) (fun h0 : term1067 => @lem2414384 h0)). Qed.
Lemma lem2414386 (h1 : term1070) : False.
Proof. exact (or_elim (@lem2413945 h1) (fun h0 : term1067 => @lem2414091 h0) (fun h0 : term1069 => @lem2414385 h0)). Qed.
Lemma lem2414387 (h1 : term1071) : False.
Proof. exact (or_elim (@lem2413798 h1) (fun h0 : term1067 => @lem2413944 h0) (fun h0 : term1070 => @lem2414386 h0)). Qed.
Lemma lem2414388 (h1 : term1072) : False.
Proof. exact (or_elim (@lem2413651 h1) (fun h0 : term1067 => @lem2413797 h0) (fun h0 : term1071 => @lem2414387 h0)). Qed.
Lemma lem2414389 (h1 : term1073) : False.
Proof. exact (or_elim (@lem2413504 h1) (fun h0 : term1067 => @lem2413650 h0) (fun h0 : term1072 => @lem2414388 h0)). Qed.
Lemma lem2414390 (h1 : term1074) : False.
Proof. exact (or_elim (@lem2413357 h1) (fun h0 : term1067 => @lem2413503 h0) (fun h0 : term1073 => @lem2414389 h0)). Qed.
Lemma lem2414391 (h1 : term1075) : False.
Proof. exact (or_elim (@lem2413210 h1) (fun h0 : term1067 => @lem2413356 h0) (fun h0 : term1074 => @lem2414390 h0)). Qed.
Lemma lem2414393 (h1 : term1075) : term1075.
Proof. exact (h1). Qed.
Lemma lem2414394 (h1 : term1075) : term1075 = False.
Proof. exact (prop_ext (fun h2 : term1075 => @lem2414391 h1) (fun h2 : False => @lem2414393 h1)). Qed.
Lemma lem2414395 (h1 : term1075) : False.
Proof. exact (EQ_MP (@lem2414394 h1) (@lem2414393 h1)). Qed.
Lemma lem2414396 (h1 : term519) : term519.
Proof. exact (h1). Qed.
Lemma lem2414397 (h1 : term519) : term1075.
Proof. exact (EQ_MP (@lem2413116) (@lem2414396 h1)). Qed.
Lemma lem2414398 (h1 : term519) : term1075 = False.
Proof. exact (prop_ext (fun h2 : term1075 => @lem2414395 h2) (fun h2 : False => @lem2414397 h1)). Qed.
Lemma lem2414399 (h1 : term519) : False.
Proof. exact (EQ_MP (@lem2414398 h1) (@lem2414397 h1)). Qed.
Lemma lem2414400 : term1088.
Proof. exact (fun h0 : term519 => @lem2414399 h0). Qed.
Lemma lem2414401 : term1089.
Proof. exact (@lem1386578 term1090). Qed.
Lemma lem2414404 : term1090.
Proof. exact (@lem2414401 (@lem2414400)). Qed.
Lemma lem2414405 : term517 = term246.
Proof. exact (SYM (@lem2407708)). Qed.
Lemma lem2414406 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2414407 : term1090 = term49.
Proof. exact (MK_COMB (@lem2414406) (@lem2414405)). Qed.
Lemma lem2414408 : term49.
Proof. exact (EQ_MP (@lem2414407) (@lem2414404)). Qed.
Lemma lem2414409 : term48.
Proof. exact (EQ_MP (@lem2406719) (@lem2414408)). Qed.
Lemma lem2414410 : term48 = (term48 = True).
Proof. exact (@lem7 term48). Qed.
Lemma lem2414411 : term48 = True.
Proof. exact (EQ_MP (@lem2414410) (@lem2414409)). Qed.
Lemma lem2414412 : True = term48.
Proof. exact (SYM (@lem2414411)). Qed.
Lemma lem2414413 : term48.
Proof. exact (EQ_MP (@lem2414412) (@lem0)). Qed.
Lemma lem2414414 : term47.
Proof. exact (EQ_MP (@lem2406718) (@lem2414413)). Qed.
