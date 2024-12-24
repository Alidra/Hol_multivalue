Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import LT_TRANS_term_abbrevs.
Require Import LT_0_spec.
Require Import LT_SUC_spec.
Require Import thm0_spec.
Require Import thm1821_spec.
Require Import thm1822_spec.
Require Import thm1823_spec.
Require Import thm1842_spec.
Require Import thm1843_spec.
Require Import thm1844_spec.
Require Import thm1845_spec.
Require Import thm7_spec.
Require Import thm75622_spec.
Require Import thm75623_spec.
Require Import thm89994_spec.
Lemma lem93767 : term0.
Proof. exact (proj1 (@lem89994)). Qed.
Lemma lem93768 (m : nat) : term1 m.
Proof. exact (@lem93767 m). Qed.
Lemma lem93769 (m : nat) : (term1 m) = ((term2 m) = False).
Proof. exact (eq_refl (term1 m)). Qed.
Lemma lem93772 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93773 : term4.
Proof. exact (@lem93772 term5). Qed.
Lemma lem93774 : term6 = term7.
Proof. exact (eq_refl term6). Qed.
Lemma lem93775 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93776 : term8 = term9.
Proof. exact (MK_COMB (@lem93775) (@lem93774)). Qed.
Lemma lem93777 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem93778 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93779 (m : nat) : (term12 m) = (term13 m).
Proof. exact (MK_COMB (@lem93778) (@lem93777 m)). Qed.
Lemma lem93780 (m : nat) : (term14 m) = (term15 m).
Proof. exact (eq_refl (term14 m)). Qed.
Lemma lem93781 (m : nat) : (term16 m) = (term17 m).
Proof. exact (MK_COMB (@lem93779 m) (@lem93780 m)). Qed.
Lemma lem93782 : term18 = term19.
Proof. exact (fun_ext (fun m : nat => @lem93781 m)). Qed.
Lemma lem93783 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93784 : term20 = term21.
Proof. exact (MK_COMB (@lem93783) (@lem93782)). Qed.
Lemma lem93785 : term22 = term23.
Proof. exact (MK_COMB (@lem93776) (@lem93784)). Qed.
Lemma lem93786 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93787 : term24 = term25.
Proof. exact (MK_COMB (@lem93786) (@lem93785)). Qed.
Lemma lem93788 (m : nat) : (term10 m) = (term11 m).
Proof. exact (eq_refl (term10 m)). Qed.
Lemma lem93789 : term26 = term5.
Proof. exact (fun_ext (fun m : nat => @lem93788 m)). Qed.
Lemma lem93790 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93791 : term27 = term28.
Proof. exact (MK_COMB (@lem93790) (@lem93789)). Qed.
Lemma lem93792 : term4 = term29.
Proof. exact (MK_COMB (@lem93787) (@lem93791)). Qed.
Lemma lem93793 : term29.
Proof. exact (EQ_MP (@lem93792) (@lem93773)). Qed.
Lemma lem93794 (m : nat) (h1 : term11 m) : term11 m.
Proof. exact (h1). Qed.
Lemma lem93796 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93797 : term30.
Proof. exact (@lem93796 term31). Qed.
Lemma lem93798 : term32 = term33.
Proof. exact (eq_refl term32). Qed.
Lemma lem93799 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93800 : term34 = term35.
Proof. exact (MK_COMB (@lem93799) (@lem93798)). Qed.
Lemma lem93801 (n : nat) : (term36 n) = (term37 n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem93802 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93803 (n : nat) : (term38 n) = (term39 n).
Proof. exact (MK_COMB (@lem93802) (@lem93801 n)). Qed.
Lemma lem93804 (n : nat) : (term40 n) = (term41 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem93805 (n : nat) : (term42 n) = (term43 n).
Proof. exact (MK_COMB (@lem93803 n) (@lem93804 n)). Qed.
Lemma lem93806 : term44 = term45.
Proof. exact (fun_ext (fun n : nat => @lem93805 n)). Qed.
Lemma lem93807 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93808 : term46 = term47.
Proof. exact (MK_COMB (@lem93807) (@lem93806)). Qed.
Lemma lem93809 : term48 = term49.
Proof. exact (MK_COMB (@lem93800) (@lem93808)). Qed.
Lemma lem93810 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93811 : term50 = term51.
Proof. exact (MK_COMB (@lem93810) (@lem93809)). Qed.
Lemma lem93812 (n : nat) : (term36 n) = (term37 n).
Proof. exact (eq_refl (term36 n)). Qed.
Lemma lem93813 : term52 = term31.
Proof. exact (fun_ext (fun n : nat => @lem93812 n)). Qed.
Lemma lem93814 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93815 : term53 = term7.
Proof. exact (MK_COMB (@lem93814) (@lem93813)). Qed.
Lemma lem93816 : term30 = term54.
Proof. exact (MK_COMB (@lem93811) (@lem93815)). Qed.
Lemma lem93817 : term54.
Proof. exact (EQ_MP (@lem93816) (@lem93797)). Qed.
Lemma lem93820 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93821 : term55.
Proof. exact (@lem93820 term56). Qed.
Lemma lem93822 : term57 = term58.
Proof. exact (eq_refl term57). Qed.
Lemma lem93823 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93824 : term59 = term60.
Proof. exact (MK_COMB (@lem93823) (@lem93822)). Qed.
Lemma lem93825 (p : nat) : (term61 p) = (term62 p).
Proof. exact (eq_refl (term61 p)). Qed.
Lemma lem93826 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93827 (p : nat) : (term63 p) = (term64 p).
Proof. exact (MK_COMB (@lem93826) (@lem93825 p)). Qed.
Lemma lem93828 (p : nat) : (term65 p) = (term66 p).
Proof. exact (eq_refl (term65 p)). Qed.
Lemma lem93829 (p : nat) : (term67 p) = (term68 p).
Proof. exact (MK_COMB (@lem93827 p) (@lem93828 p)). Qed.
Lemma lem93830 : term69 = term70.
Proof. exact (fun_ext (fun p : nat => @lem93829 p)). Qed.
Lemma lem93831 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93832 : term71 = term72.
Proof. exact (MK_COMB (@lem93831) (@lem93830)). Qed.
Lemma lem93833 : term73 = term74.
Proof. exact (MK_COMB (@lem93824) (@lem93832)). Qed.
Lemma lem93834 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93835 : term75 = term76.
Proof. exact (MK_COMB (@lem93834) (@lem93833)). Qed.
Lemma lem93836 (p : nat) : (term61 p) = (term62 p).
Proof. exact (eq_refl (term61 p)). Qed.
Lemma lem93837 : term77 = term56.
Proof. exact (fun_ext (fun p : nat => @lem93836 p)). Qed.
Lemma lem93838 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93839 : term78 = term33.
Proof. exact (MK_COMB (@lem93838) (@lem93837)). Qed.
Lemma lem93840 : term55 = term79.
Proof. exact (MK_COMB (@lem93835) (@lem93839)). Qed.
Lemma lem93841 : term79.
Proof. exact (EQ_MP (@lem93840) (@lem93821)). Qed.
Lemma lem93848 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93849 (n : nat) : term80 n.
Proof. exact (@lem93848 (term81 n)). Qed.
Lemma lem93850 (n : nat) : (term82 n) = (term83 n).
Proof. exact (eq_refl (term82 n)). Qed.
Lemma lem93851 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93852 (n : nat) : (term84 n) = (term85 n).
Proof. exact (MK_COMB (@lem93851) (@lem93850 n)). Qed.
Lemma lem93853 (n : nat) (p : nat) : (term86 n p) = (term87 n p).
Proof. exact (eq_refl (term86 n p)). Qed.
Lemma lem93854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93855 (n : nat) (p : nat) : (term88 n p) = (term89 n p).
Proof. exact (MK_COMB (@lem93854) (@lem93853 n p)). Qed.
Lemma lem93856 (n : nat) (p : nat) : (term90 n p) = (term91 n p).
Proof. exact (eq_refl (term90 n p)). Qed.
Lemma lem93857 (n : nat) (p : nat) : (term92 n p) = (term93 n p).
Proof. exact (MK_COMB (@lem93855 n p) (@lem93856 n p)). Qed.
Lemma lem93858 (n : nat) : (term94 n) = (term95 n).
Proof. exact (fun_ext (fun p : nat => @lem93857 n p)). Qed.
Lemma lem93859 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93860 (n : nat) : (term96 n) = (term97 n).
Proof. exact (MK_COMB (@lem93859) (@lem93858 n)). Qed.
Lemma lem93861 (n : nat) : (term98 n) = (term99 n).
Proof. exact (MK_COMB (@lem93852 n) (@lem93860 n)). Qed.
Lemma lem93862 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93863 (n : nat) : (term100 n) = (term101 n).
Proof. exact (MK_COMB (@lem93862) (@lem93861 n)). Qed.
Lemma lem93864 (n : nat) (p : nat) : (term86 n p) = (term87 n p).
Proof. exact (eq_refl (term86 n p)). Qed.
Lemma lem93865 (n : nat) : (term102 n) = (term81 n).
Proof. exact (fun_ext (fun p : nat => @lem93864 n p)). Qed.
Lemma lem93866 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93867 (n : nat) : (term103 n) = (term41 n).
Proof. exact (MK_COMB (@lem93866) (@lem93865 n)). Qed.
Lemma lem93868 (n : nat) : (term80 n) = (term104 n).
Proof. exact (MK_COMB (@lem93863 n) (@lem93867 n)). Qed.
Lemma lem93869 (n : nat) : term104 n.
Proof. exact (EQ_MP (@lem93868 n) (@lem93849 n)). Qed.
Lemma lem93876 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93877 (m : nat) : term105 m.
Proof. exact (@lem93876 (term106 m)). Qed.
Lemma lem93878 (m : nat) : (term107 m) = (term108 m).
Proof. exact (eq_refl (term107 m)). Qed.
Lemma lem93879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93880 (m : nat) : (term109 m) = (term110 m).
Proof. exact (MK_COMB (@lem93879) (@lem93878 m)). Qed.
Lemma lem93881 (n : nat) (m : nat) : (term111 m n) = (term112 n m).
Proof. exact (eq_refl (term111 m n)). Qed.
Lemma lem93882 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93883 (n : nat) (m : nat) : (term113 m n) = (term114 n m).
Proof. exact (MK_COMB (@lem93882) (@lem93881 n m)). Qed.
Lemma lem93884 (n : nat) (m : nat) : (term115 m n) = (term116 n m).
Proof. exact (eq_refl (term115 m n)). Qed.
Lemma lem93885 (n : nat) (m : nat) : (term117 m n) = (term118 n m).
Proof. exact (MK_COMB (@lem93883 n m) (@lem93884 n m)). Qed.
Lemma lem93886 (m : nat) : (term119 m) = (term120 m).
Proof. exact (fun_ext (fun n : nat => @lem93885 n m)). Qed.
Lemma lem93887 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93888 (m : nat) : (term121 m) = (term122 m).
Proof. exact (MK_COMB (@lem93887) (@lem93886 m)). Qed.
Lemma lem93889 (m : nat) : (term123 m) = (term124 m).
Proof. exact (MK_COMB (@lem93880 m) (@lem93888 m)). Qed.
Lemma lem93890 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93891 (m : nat) : (term125 m) = (term126 m).
Proof. exact (MK_COMB (@lem93890) (@lem93889 m)). Qed.
Lemma lem93892 (n : nat) (m : nat) : (term111 m n) = (term112 n m).
Proof. exact (eq_refl (term111 m n)). Qed.
Lemma lem93893 (m : nat) : (term127 m) = (term106 m).
Proof. exact (fun_ext (fun n : nat => @lem93892 n m)). Qed.
Lemma lem93894 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93895 (m : nat) : (term128 m) = (term15 m).
Proof. exact (MK_COMB (@lem93894) (@lem93893 m)). Qed.
Lemma lem93896 (m : nat) : (term105 m) = (term129 m).
Proof. exact (MK_COMB (@lem93891 m) (@lem93895 m)). Qed.
Lemma lem93897 (m : nat) : term129 m.
Proof. exact (EQ_MP (@lem93896 m) (@lem93877 m)). Qed.
Lemma lem93900 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93901 (m : nat) : term130 m.
Proof. exact (@lem93900 (term131 m)). Qed.
Lemma lem93902 (m : nat) : (term132 m) = (term133 m).
Proof. exact (eq_refl (term132 m)). Qed.
Lemma lem93903 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93904 (m : nat) : (term134 m) = (term135 m).
Proof. exact (MK_COMB (@lem93903) (@lem93902 m)). Qed.
Lemma lem93905 (m : nat) (p : nat) : (term136 m p) = (term137 m p).
Proof. exact (eq_refl (term136 m p)). Qed.
Lemma lem93906 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93907 (m : nat) (p : nat) : (term138 m p) = (term139 m p).
Proof. exact (MK_COMB (@lem93906) (@lem93905 m p)). Qed.
Lemma lem93908 (m : nat) (p : nat) : (term140 m p) = (term141 m p).
Proof. exact (eq_refl (term140 m p)). Qed.
Lemma lem93909 (m : nat) (p : nat) : (term142 m p) = (term143 m p).
Proof. exact (MK_COMB (@lem93907 m p) (@lem93908 m p)). Qed.
Lemma lem93910 (m : nat) : (term144 m) = (term145 m).
Proof. exact (fun_ext (fun p : nat => @lem93909 m p)). Qed.
Lemma lem93911 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93912 (m : nat) : (term146 m) = (term147 m).
Proof. exact (MK_COMB (@lem93911) (@lem93910 m)). Qed.
Lemma lem93913 (m : nat) : (term148 m) = (term149 m).
Proof. exact (MK_COMB (@lem93904 m) (@lem93912 m)). Qed.
Lemma lem93914 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93915 (m : nat) : (term150 m) = (term151 m).
Proof. exact (MK_COMB (@lem93914) (@lem93913 m)). Qed.
Lemma lem93916 (m : nat) (p : nat) : (term136 m p) = (term137 m p).
Proof. exact (eq_refl (term136 m p)). Qed.
Lemma lem93917 (m : nat) : (term152 m) = (term131 m).
Proof. exact (fun_ext (fun p : nat => @lem93916 m p)). Qed.
Lemma lem93918 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93919 (m : nat) : (term153 m) = (term108 m).
Proof. exact (MK_COMB (@lem93918) (@lem93917 m)). Qed.
Lemma lem93920 (m : nat) : (term130 m) = (term154 m).
Proof. exact (MK_COMB (@lem93915 m) (@lem93919 m)). Qed.
Lemma lem93921 (m : nat) : term154 m.
Proof. exact (EQ_MP (@lem93920 m) (@lem93901 m)). Qed.
Lemma lem93928 (P : nat -> Prop) : term3 P.
Proof. exact (EQ_MP (@lem75623 P) (@lem75622 P)). Qed.
Lemma lem93929 (n : nat) (m : nat) : term155 n m.
Proof. exact (@lem93928 (term156 n m)). Qed.
Lemma lem93930 (n : nat) (m : nat) : (term157 n m) = (term158 n m).
Proof. exact (eq_refl (term157 n m)). Qed.
Lemma lem93931 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem93932 (n : nat) (m : nat) : (term159 n m) = (term160 n m).
Proof. exact (MK_COMB (@lem93931) (@lem93930 n m)). Qed.
Lemma lem93933 (n : nat) (m : nat) (p : nat) : (term161 n m p) = (term162 n m p).
Proof. exact (eq_refl (term161 n m p)). Qed.
Lemma lem93934 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93935 (n : nat) (m : nat) (p : nat) : (term163 n m p) = (term164 n m p).
Proof. exact (MK_COMB (@lem93934) (@lem93933 n m p)). Qed.
Lemma lem93936 (n : nat) (m : nat) (p : nat) : (term165 n m p) = (term166 n m p).
Proof. exact (eq_refl (term165 n m p)). Qed.
Lemma lem93937 (n : nat) (m : nat) (p : nat) : (term167 n m p) = (term168 n m p).
Proof. exact (MK_COMB (@lem93935 n m p) (@lem93936 n m p)). Qed.
Lemma lem93938 (n : nat) (m : nat) : (term169 n m) = (term170 n m).
Proof. exact (fun_ext (fun p : nat => @lem93937 n m p)). Qed.
Lemma lem93939 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93940 (n : nat) (m : nat) : (term171 n m) = (term172 n m).
Proof. exact (MK_COMB (@lem93939) (@lem93938 n m)). Qed.
Lemma lem93941 (n : nat) (m : nat) : (term173 n m) = (term174 n m).
Proof. exact (MK_COMB (@lem93932 n m) (@lem93940 n m)). Qed.
Lemma lem93942 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93943 (n : nat) (m : nat) : (term175 n m) = (term176 n m).
Proof. exact (MK_COMB (@lem93942) (@lem93941 n m)). Qed.
Lemma lem93944 (n : nat) (m : nat) (p : nat) : (term161 n m p) = (term162 n m p).
Proof. exact (eq_refl (term161 n m p)). Qed.
Lemma lem93945 (n : nat) (m : nat) : (term177 n m) = (term156 n m).
Proof. exact (fun_ext (fun p : nat => @lem93944 n m p)). Qed.
Lemma lem93946 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem93947 (n : nat) (m : nat) : (term178 n m) = (term116 n m).
Proof. exact (MK_COMB (@lem93946) (@lem93945 n m)). Qed.
Lemma lem93948 (n : nat) (m : nat) : (term155 n m) = (term179 n m).
Proof. exact (MK_COMB (@lem93943 n m) (@lem93947 n m)). Qed.
Lemma lem93949 (n : nat) (m : nat) : term179 n m.
Proof. exact (EQ_MP (@lem93948 n m) (@lem93929 n m)). Qed.
Lemma lem93969 (t : Prop) : (t /\ t) = t.
Proof. exact (proj2 (@lem1845 t)). Qed.
Lemma lem93970 : term180 = term181.
Proof. exact (@lem93969 term181). Qed.
Lemma lem93971 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem93972 : term182 = term183.
Proof. exact (MK_COMB (@lem93971) (@lem93970)). Qed.
Lemma lem93973 : term181 = term181.
Proof. exact (eq_refl term181). Qed.
Lemma lem93974 : term58 = term184.
Proof. exact (MK_COMB (@lem93972) (@lem93973)). Qed.
Lemma lem93976 (t : Prop) : (t -> t) = True.
Proof. exact (proj1 (@lem1823 t)). Qed.
Lemma lem93977 : term184 = True.
Proof. exact (@lem93976 term181). Qed.
Lemma lem93978 : term58 = True.
Proof. exact (TRANS (@lem93974) (@lem93977)). Qed.
Lemma lem93979 : True = term58.
Proof. exact (SYM (@lem93978)). Qed.
Lemma lem93980 : term58.
Proof. exact (EQ_MP (@lem93979) (@lem0)). Qed.
Lemma lem93981 (n : nat) : term185 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem93982 (n : nat) : (term185 n) = (term186 n).
Proof. exact (eq_refl (term185 n)). Qed.
Lemma lem93983 (n : nat) : term186 n.
Proof. exact (EQ_MP (@lem93982 n) (@lem93981 n)). Qed.
Lemma lem93984 (n : nat) : (term186 n) = ((term186 n) = True).
Proof. exact (@lem7 (term186 n)). Qed.
Lemma lem93999 (n : nat) : (term186 n) = True.
Proof. exact (EQ_MP (@lem93984 n) (@lem93983 n)). Qed.
Lemma lem94000 (p : nat) : (term186 p) = True.
Proof. exact (@lem93999 p). Qed.
Lemma lem94001 : term187 = term187.
Proof. exact (eq_refl term187). Qed.
Lemma lem94002 (p : nat) : (term188 p) = term189.
Proof. exact (MK_COMB (@lem94001) (@lem94000 p)). Qed.
Lemma lem94004 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem94005 : term189 = term181.
Proof. exact (@lem94004 term181). Qed.
Lemma lem94006 (p : nat) : (term188 p) = term181.
Proof. exact (TRANS (@lem94002 p) (@lem94005)). Qed.
Lemma lem94007 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94008 (p : nat) : (term190 p) = term183.
Proof. exact (MK_COMB (@lem94007) (@lem94006 p)). Qed.
Lemma lem94010 (n : nat) : (term186 n) = True.
Proof. exact (EQ_MP (@lem93984 n) (@lem93983 n)). Qed.
Lemma lem94011 (p : nat) : (term186 p) = True.
Proof. exact (@lem94010 p). Qed.
Lemma lem94012 (p : nat) : (term66 p) = term191.
Proof. exact (MK_COMB (@lem94008 p) (@lem94011 p)). Qed.
Lemma lem94014 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem94015 : term191 = True.
Proof. exact (@lem94014 term181). Qed.
Lemma lem94016 (p : nat) : (term66 p) = True.
Proof. exact (TRANS (@lem94012 p) (@lem94015)). Qed.
Lemma lem94017 (p : nat) : True = (term66 p).
Proof. exact (SYM (@lem94016 p)). Qed.
Lemma lem94018 (p : nat) : term66 p.
Proof. exact (EQ_MP (@lem94017 p) (@lem0)). Qed.
Lemma lem94019 (n : nat) : term185 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem94020 (n : nat) : (term185 n) = (term186 n).
Proof. exact (eq_refl (term185 n)). Qed.
Lemma lem94021 (n : nat) : term186 n.
Proof. exact (EQ_MP (@lem94020 n) (@lem94019 n)). Qed.
Lemma lem94022 (n : nat) : (term186 n) = ((term186 n) = True).
Proof. exact (@lem7 (term186 n)). Qed.
Lemma lem94040 (n : nat) : (term186 n) = True.
Proof. exact (EQ_MP (@lem94022 n) (@lem94021 n)). Qed.
Lemma lem94041 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94042 (n : nat) : (term192 n) = (and True).
Proof. exact (MK_COMB (@lem94041) (@lem94040 n)). Qed.
Lemma lem94043 (n : nat) : (term193 n) = (term193 n).
Proof. exact (eq_refl (term193 n)). Qed.
Lemma lem94044 (n : nat) : (term194 n) = (term195 n).
Proof. exact (MK_COMB (@lem94042 n) (@lem94043 n)). Qed.
Lemma lem94046 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem94047 (n : nat) : (term195 n) = (term193 n).
Proof. exact (@lem94046 (term193 n)). Qed.
Lemma lem94048 (n : nat) : (term194 n) = (term193 n).
Proof. exact (TRANS (@lem94044 n) (@lem94047 n)). Qed.
Lemma lem94049 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94050 (n : nat) : (term196 n) = (term197 n).
Proof. exact (MK_COMB (@lem94049) (@lem94048 n)). Qed.
Lemma lem94051 : term181 = term181.
Proof. exact (eq_refl term181). Qed.
Lemma lem94052 (n : nat) : (term83 n) = (term198 n).
Proof. exact (MK_COMB (@lem94050 n) (@lem94051)). Qed.
Lemma lem94055 (n : nat) : (term198 n) = (term83 n).
Proof. exact (SYM (@lem94052 n)). Qed.
Lemma lem94056 (n : nat) : term185 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem94057 (n : nat) : (term185 n) = (term186 n).
Proof. exact (eq_refl (term185 n)). Qed.
Lemma lem94058 (n : nat) : term186 n.
Proof. exact (EQ_MP (@lem94057 n) (@lem94056 n)). Qed.
Lemma lem94059 (n : nat) : (term186 n) = ((term186 n) = True).
Proof. exact (@lem7 (term186 n)). Qed.
Lemma lem94061 (m : nat) : term199 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem94062 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem94063 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem94062 m) (@lem94061 m)). Qed.
Lemma lem94064 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem94063 m n). Qed.
Lemma lem94065 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem94079 (n : nat) : (term186 n) = True.
Proof. exact (EQ_MP (@lem94059 n) (@lem94058 n)). Qed.
Lemma lem94080 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94081 (n : nat) : (term192 n) = (and True).
Proof. exact (MK_COMB (@lem94080) (@lem94079 n)). Qed.
Lemma lem94083 (m : nat) (n : nat) : (term202 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94065 m n) (@lem94064 m n)). Qed.
Lemma lem94084 (n : nat) (p : nat) : (term202 n p) = (Peano.lt n p).
Proof. exact (@lem94083 n p). Qed.
Lemma lem94085 (n : nat) (p : nat) : (term203 n p) = (term204 n p).
Proof. exact (MK_COMB (@lem94081 n) (@lem94084 n p)). Qed.
Lemma lem94087 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem94088 (n : nat) (p : nat) : (term204 n p) = (Peano.lt n p).
Proof. exact (@lem94087 (Peano.lt n p)). Qed.
Lemma lem94089 (n : nat) (p : nat) : (term203 n p) = (Peano.lt n p).
Proof. exact (TRANS (@lem94085 n p) (@lem94088 n p)). Qed.
Lemma lem94090 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94091 (n : nat) (p : nat) : (term205 n p) = (term206 n p).
Proof. exact (MK_COMB (@lem94090) (@lem94089 n p)). Qed.
Lemma lem94093 (n : nat) : (term186 n) = True.
Proof. exact (EQ_MP (@lem94059 n) (@lem94058 n)). Qed.
Lemma lem94094 (p : nat) : (term186 p) = True.
Proof. exact (@lem94093 p). Qed.
Lemma lem94095 (n : nat) (p : nat) : (term91 n p) = (term207 n p).
Proof. exact (MK_COMB (@lem94091 n p) (@lem94094 p)). Qed.
Lemma lem94097 (t : Prop) : (t -> True) = True.
Proof. exact (proj1 (@lem1821 t)). Qed.
Lemma lem94098 (n : nat) (p : nat) : (term207 n p) = True.
Proof. exact (@lem94097 (Peano.lt n p)). Qed.
Lemma lem94099 (n : nat) (p : nat) : (term91 n p) = True.
Proof. exact (TRANS (@lem94095 n p) (@lem94098 n p)). Qed.
Lemma lem94100 (n : nat) (p : nat) : True = (term91 n p).
Proof. exact (SYM (@lem94099 n p)). Qed.
Lemma lem94101 (n : nat) (p : nat) : term91 n p.
Proof. exact (EQ_MP (@lem94100 n p) (@lem0)). Qed.
Lemma lem94127 (n : nat) : term185 n.
Proof. exact (@lem91530 n). Qed.
Lemma lem94128 (n : nat) : (term185 n) = (term186 n).
Proof. exact (eq_refl (term185 n)). Qed.
Lemma lem94129 (n : nat) : term186 n.
Proof. exact (EQ_MP (@lem94128 n) (@lem94127 n)). Qed.
Lemma lem94130 (n : nat) : (term186 n) = ((term186 n) = True).
Proof. exact (@lem7 (term186 n)). Qed.
Lemma lem94132 (m : nat) : term199 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem94133 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem94134 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem94133 m) (@lem94132 m)). Qed.
Lemma lem94135 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem94134 m n). Qed.
Lemma lem94136 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem94153 (n : nat) : (term186 n) = True.
Proof. exact (EQ_MP (@lem94130 n) (@lem94129 n)). Qed.
Lemma lem94154 (p : nat) : (term186 p) = True.
Proof. exact (@lem94153 p). Qed.
Lemma lem94155 (m : nat) : (term208 m) = (term208 m).
Proof. exact (eq_refl (term208 m)). Qed.
Lemma lem94156 (p : nat) (m : nat) : (term209 m p) = (term210 m).
Proof. exact (MK_COMB (@lem94155 m) (@lem94154 p)). Qed.
Lemma lem94158 (t : Prop) : (t /\ True) = t.
Proof. exact (proj1 (@lem1843 t)). Qed.
Lemma lem94159 (m : nat) : (term210 m) = (term193 m).
Proof. exact (@lem94158 (term193 m)). Qed.
Lemma lem94160 (p : nat) (m : nat) : (term209 m p) = (term193 m).
Proof. exact (TRANS (@lem94156 p m) (@lem94159 m)). Qed.
Lemma lem94161 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94162 (p : nat) (m : nat) : (term211 m p) = (term197 m).
Proof. exact (MK_COMB (@lem94161) (@lem94160 p m)). Qed.
Lemma lem94164 (m : nat) (n : nat) : (term202 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94136 m n) (@lem94135 m n)). Qed.
Lemma lem94165 (m : nat) (p : nat) : (term202 m p) = (Peano.lt m p).
Proof. exact (@lem94164 m p). Qed.
Lemma lem94166 (m : nat) (p : nat) : (term141 m p) = (term212 m p).
Proof. exact (MK_COMB (@lem94162 p m) (@lem94165 m p)). Qed.
Lemma lem94169 (m : nat) (p : nat) : (term212 m p) = (term141 m p).
Proof. exact (SYM (@lem94166 m p)). Qed.
Lemma lem94175 (m : nat) : term199 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem94176 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem94177 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem94176 m) (@lem94175 m)). Qed.
Lemma lem94178 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem94177 m n). Qed.
Lemma lem94179 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem94199 (m : nat) (n : nat) : (term202 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94179 m n) (@lem94178 m n)). Qed.
Lemma lem94200 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94201 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (MK_COMB (@lem94200) (@lem94199 m n)). Qed.
Lemma lem94202 (n : nat) : (term193 n) = (term193 n).
Proof. exact (eq_refl (term193 n)). Qed.
Lemma lem94203 (m : nat) (n : nat) : (term215 m n) = (term216 m n).
Proof. exact (MK_COMB (@lem94201 m n) (@lem94202 n)). Qed.
Lemma lem94206 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94207 (m : nat) (n : nat) : (term217 m n) = (term218 m n).
Proof. exact (MK_COMB (@lem94206) (@lem94203 m n)). Qed.
Lemma lem94208 (m : nat) : (term193 m) = (term193 m).
Proof. exact (eq_refl (term193 m)). Qed.
Lemma lem94209 (n : nat) (m : nat) : (term158 n m) = (term219 n m).
Proof. exact (MK_COMB (@lem94207 m n) (@lem94208 m)). Qed.
Lemma lem94212 (n : nat) (m : nat) : (term219 n m) = (term158 n m).
Proof. exact (SYM (@lem94209 n m)). Qed.
Lemma lem94218 (m : nat) : term199 m.
Proof. exact (@lem91415 m). Qed.
Lemma lem94219 (m : nat) : (term199 m) = (term200 m).
Proof. exact (eq_refl (term199 m)). Qed.
Lemma lem94220 (m : nat) : term200 m.
Proof. exact (EQ_MP (@lem94219 m) (@lem94218 m)). Qed.
Lemma lem94221 (m : nat) (n : nat) : term201 m n.
Proof. exact (@lem94220 m n). Qed.
Lemma lem94222 (m : nat) (n : nat) : (term201 m n) = ((term202 m n) = (Peano.lt m n)).
Proof. exact (eq_refl (term201 m n)). Qed.
Lemma lem94224 (n : nat) (m : nat) (h1 : term11 m) : term220 m n.
Proof. exact (@lem93794 m h1 n). Qed.
Lemma lem94225 (n : nat) (m : nat) : (term220 m n) = (term221 n m).
Proof. exact (eq_refl (term220 m n)). Qed.
Lemma lem94226 (n : nat) (m : nat) (h1 : term11 m) : term221 n m.
Proof. exact (EQ_MP (@lem94225 n m) (@lem94224 n m h1)). Qed.
Lemma lem94227 (n : nat) (p : nat) (m : nat) (h1 : term11 m) : term222 n m p.
Proof. exact (@lem94226 n m h1 p). Qed.
Lemma lem94228 (n : nat) (m : nat) (p : nat) : (term222 n m p) = (term223 n m p).
Proof. exact (eq_refl (term222 n m p)). Qed.
Lemma lem94229 (n : nat) (p : nat) (m : nat) (h1 : term11 m) : term223 n m p.
Proof. exact (EQ_MP (@lem94228 n m p) (@lem94227 n p m h1)). Qed.
Lemma lem94230 (n : nat) (m : nat) (p : nat) : (term223 n m p) = ((term223 n m p) = True).
Proof. exact (@lem7 (term223 n m p)). Qed.
Lemma lem94244 (m : nat) (n : nat) : (term202 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94222 m n) (@lem94221 m n)). Qed.
Lemma lem94245 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94246 (m : nat) (n : nat) : (term213 m n) = (term214 m n).
Proof. exact (MK_COMB (@lem94245) (@lem94244 m n)). Qed.
Lemma lem94248 (m : nat) (n : nat) : (term202 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94222 m n) (@lem94221 m n)). Qed.
Lemma lem94249 (n : nat) (p : nat) : (term202 n p) = (Peano.lt n p).
Proof. exact (@lem94248 n p). Qed.
Lemma lem94250 (m : nat) (n : nat) (p : nat) : (term224 m n p) = (term225 m n p).
Proof. exact (MK_COMB (@lem94246 m n) (@lem94249 n p)). Qed.
Lemma lem94253 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94254 (m : nat) (n : nat) (p : nat) : (term226 m n p) = (term227 m n p).
Proof. exact (MK_COMB (@lem94253) (@lem94250 m n p)). Qed.
Lemma lem94256 (m : nat) (n : nat) : (term202 m n) = (Peano.lt m n).
Proof. exact (EQ_MP (@lem94222 m n) (@lem94221 m n)). Qed.
Lemma lem94257 (m : nat) (p : nat) : (term202 m p) = (Peano.lt m p).
Proof. exact (@lem94256 m p). Qed.
Lemma lem94258 (n : nat) (m : nat) (p : nat) : (term166 n m p) = (term223 n m p).
Proof. exact (MK_COMB (@lem94254 m n p) (@lem94257 m p)). Qed.
Lemma lem94260 (n : nat) (p : nat) (m : nat) (h1 : term11 m) : (term223 n m p) = True.
Proof. exact (EQ_MP (@lem94230 n m p) (@lem94229 n p m h1)). Qed.
Lemma lem94261 (n : nat) (p : nat) (m : nat) (h1 : term11 m) : (term166 n m p) = True.
Proof. exact (TRANS (@lem94258 n m p) (@lem94260 n p m h1)). Qed.
Lemma lem94262 (n : nat) (p : nat) (m : nat) (h1 : term11 m) : True = (term166 n m p).
Proof. exact (SYM (@lem94261 n p m h1)). Qed.
Lemma lem94263 (n : nat) (p : nat) (m : nat) (h1 : term11 m) : term166 n m p.
Proof. exact (EQ_MP (@lem94262 n p m h1) (@lem0)). Qed.
Lemma lem94267 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94268 (n : nat) : (term193 n) = False.
Proof. exact (@lem94267 (S n)). Qed.
Lemma lem94269 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94270 (n : nat) : (term197 n) = (imp False).
Proof. exact (MK_COMB (@lem94269) (@lem94268 n)). Qed.
Lemma lem94272 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94273 : term181 = False.
Proof. exact (@lem94272 (NUMERAL 0)). Qed.
Lemma lem94274 (n : nat) : (term198 n) = (False -> False).
Proof. exact (MK_COMB (@lem94270 n) (@lem94273)). Qed.
Lemma lem94276 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem94277 : (False -> False) = True.
Proof. exact (@lem94276 False). Qed.
Lemma lem94278 (n : nat) : (term198 n) = True.
Proof. exact (TRANS (@lem94274 n) (@lem94277)). Qed.
Lemma lem94279 (n : nat) : True = (term198 n).
Proof. exact (SYM (@lem94278 n)). Qed.
Lemma lem94280 (n : nat) : term198 n.
Proof. exact (EQ_MP (@lem94279 n) (@lem0)). Qed.
Lemma lem94286 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94287 (m : nat) : (term193 m) = False.
Proof. exact (@lem94286 (S m)). Qed.
Lemma lem94288 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem94289 (m : nat) : (term208 m) = (and False).
Proof. exact (MK_COMB (@lem94288) (@lem94287 m)). Qed.
Lemma lem94291 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94292 : term181 = False.
Proof. exact (@lem94291 (NUMERAL 0)). Qed.
Lemma lem94293 (m : nat) : (term228 m) = (False /\ False).
Proof. exact (MK_COMB (@lem94289 m) (@lem94292)). Qed.
Lemma lem94295 (t : Prop) : (False /\ t) = False.
Proof. exact (proj1 (@lem1844 t)). Qed.
Lemma lem94296 : (False /\ False) = False.
Proof. exact (@lem94295 False). Qed.
Lemma lem94297 (m : nat) : (term228 m) = False.
Proof. exact (TRANS (@lem94293 m) (@lem94296)). Qed.
Lemma lem94298 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94299 (m : nat) : (term229 m) = (imp False).
Proof. exact (MK_COMB (@lem94298) (@lem94297 m)). Qed.
Lemma lem94301 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94302 (m : nat) : (term193 m) = False.
Proof. exact (@lem94301 (S m)). Qed.
Lemma lem94303 (m : nat) : (term133 m) = (False -> False).
Proof. exact (MK_COMB (@lem94299 m) (@lem94302 m)). Qed.
Lemma lem94305 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem94306 : (False -> False) = True.
Proof. exact (@lem94305 False). Qed.
Lemma lem94307 (m : nat) : (term133 m) = True.
Proof. exact (TRANS (@lem94303 m) (@lem94306)). Qed.
Lemma lem94308 (m : nat) : True = (term133 m).
Proof. exact (SYM (@lem94307 m)). Qed.
Lemma lem94313 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94314 (m : nat) : (term193 m) = False.
Proof. exact (@lem94313 (S m)). Qed.
Lemma lem94315 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94316 (m : nat) : (term197 m) = (imp False).
Proof. exact (MK_COMB (@lem94315) (@lem94314 m)). Qed.
Lemma lem94317 (m : nat) (p : nat) : (Peano.lt m p) = (Peano.lt m p).
Proof. exact (eq_refl (Peano.lt m p)). Qed.
Lemma lem94318 (m : nat) (p : nat) : (term212 m p) = (term230 m p).
Proof. exact (MK_COMB (@lem94316 m) (@lem94317 m p)). Qed.
Lemma lem94320 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem94321 (m : nat) (p : nat) : (term230 m p) = True.
Proof. exact (@lem94320 (Peano.lt m p)). Qed.
Lemma lem94322 (m : nat) (p : nat) : (term212 m p) = True.
Proof. exact (TRANS (@lem94318 m p) (@lem94321 m p)). Qed.
Lemma lem94323 (m : nat) (p : nat) : True = (term212 m p).
Proof. exact (SYM (@lem94322 m p)). Qed.
Lemma lem94324 (m : nat) (p : nat) : term212 m p.
Proof. exact (EQ_MP (@lem94323 m p) (@lem0)). Qed.
Lemma lem94330 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94331 (n : nat) : (term193 n) = False.
Proof. exact (@lem94330 (S n)). Qed.
Lemma lem94332 (m : nat) (n : nat) : (term214 m n) = (term214 m n).
Proof. exact (eq_refl (term214 m n)). Qed.
Lemma lem94333 (m : nat) (n : nat) : (term216 m n) = (term231 m n).
Proof. exact (MK_COMB (@lem94332 m n) (@lem94331 n)). Qed.
Lemma lem94335 (t : Prop) : (t /\ False) = False.
Proof. exact (proj1 (@lem1845 t)). Qed.
Lemma lem94336 (m : nat) (n : nat) : (term231 m n) = False.
Proof. exact (@lem94335 (Peano.lt m n)). Qed.
Lemma lem94337 (m : nat) (n : nat) : (term216 m n) = False.
Proof. exact (TRANS (@lem94333 m n) (@lem94336 m n)). Qed.
Lemma lem94338 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem94339 (m : nat) (n : nat) : (term218 m n) = (imp False).
Proof. exact (MK_COMB (@lem94338) (@lem94337 m n)). Qed.
Lemma lem94341 (m : nat) : (term2 m) = False.
Proof. exact (EQ_MP (@lem93769 m) (@lem93768 m)). Qed.
Lemma lem94342 (m : nat) : (term193 m) = False.
Proof. exact (@lem94341 (S m)). Qed.
Lemma lem94343 (n : nat) (m : nat) : (term219 n m) = (False -> False).
Proof. exact (MK_COMB (@lem94339 m n) (@lem94342 m)). Qed.
Lemma lem94345 (t : Prop) : (False -> t) = True.
Proof. exact (proj1 (@lem1822 t)). Qed.
Lemma lem94346 : (False -> False) = True.
Proof. exact (@lem94345 False). Qed.
Lemma lem94347 (n : nat) (m : nat) : (term219 n m) = True.
Proof. exact (TRANS (@lem94343 n m) (@lem94346)). Qed.
Lemma lem94348 (n : nat) (m : nat) : True = (term219 n m).
Proof. exact (SYM (@lem94347 n m)). Qed.
Lemma lem94349 (n : nat) (m : nat) : term219 n m.
Proof. exact (EQ_MP (@lem94348 n m) (@lem0)). Qed.
Lemma lem94350 (n : nat) (m : nat) : term158 n m.
Proof. exact (EQ_MP (@lem94212 n m) (@lem94349 n m)). Qed.
Lemma lem94351 (m : nat) (p : nat) : term141 m p.
Proof. exact (EQ_MP (@lem94169 m p) (@lem94324 m p)). Qed.
Lemma lem94352 (m : nat) : term133 m.
Proof. exact (EQ_MP (@lem94308 m) (@lem0)). Qed.
Lemma lem94353 (n : nat) : term83 n.
Proof. exact (EQ_MP (@lem94055 n) (@lem94280 n)). Qed.
Lemma lem94354 (n : nat) (p : nat) (m : nat) (h1 : term11 m) : term168 n m p.
Proof. exact (fun h0 : term162 n m p => @lem94263 n p m h1). Qed.
Lemma lem94359 (n : nat) (m : nat) (h1 : term11 m) : term172 n m.
Proof. exact (fun p : nat => @lem94354 n p m h1). Qed.
Lemma lem94360 (n : nat) (m : nat) (h1 : term11 m) : term174 n m.
Proof. exact (conj (@lem94350 n m) (@lem94359 n m h1)). Qed.
Lemma lem94361 (n : nat) (m : nat) (h1 : term11 m) : term116 n m.
Proof. exact (@lem93949 n m (@lem94360 n m h1)). Qed.
Lemma lem94362 (m : nat) (p : nat) : term143 m p.
Proof. exact (fun h0 : term137 m p => @lem94351 m p). Qed.
Lemma lem94367 (m : nat) : term147 m.
Proof. exact (fun p : nat => @lem94362 m p). Qed.
Lemma lem94368 (m : nat) : term149 m.
Proof. exact (conj (@lem94352 m) (@lem94367 m)). Qed.
Lemma lem94369 (m : nat) : term108 m.
Proof. exact (@lem93921 m (@lem94368 m)). Qed.
Lemma lem94370 (n : nat) (m : nat) (h1 : term11 m) : term118 n m.
Proof. exact (fun h0 : term112 n m => @lem94361 n m h1). Qed.
Lemma lem94375 (m : nat) (h1 : term11 m) : term122 m.
Proof. exact (fun n : nat => @lem94370 n m h1). Qed.
Lemma lem94376 (m : nat) (h1 : term11 m) : term124 m.
Proof. exact (conj (@lem94369 m) (@lem94375 m h1)). Qed.
Lemma lem94377 (m : nat) (h1 : term11 m) : term15 m.
Proof. exact (@lem93897 m (@lem94376 m h1)). Qed.
Lemma lem94378 (n : nat) (p : nat) : term93 n p.
Proof. exact (fun h0 : term87 n p => @lem94101 n p). Qed.
Lemma lem94383 (n : nat) : term97 n.
Proof. exact (fun p : nat => @lem94378 n p). Qed.
Lemma lem94384 (n : nat) : term99 n.
Proof. exact (conj (@lem94353 n) (@lem94383 n)). Qed.
Lemma lem94385 (n : nat) : term41 n.
Proof. exact (@lem93869 n (@lem94384 n)). Qed.
Lemma lem94386 (p : nat) : term68 p.
Proof. exact (fun h0 : term62 p => @lem94018 p). Qed.
Lemma lem94391 : term72.
Proof. exact (fun p : nat => @lem94386 p). Qed.
Lemma lem94392 : term74.
Proof. exact (conj (@lem93980) (@lem94391)). Qed.
Lemma lem94393 : term33.
Proof. exact (@lem93841 (@lem94392)). Qed.
Lemma lem94394 (n : nat) : term43 n.
Proof. exact (fun h0 : term37 n => @lem94385 n). Qed.
Lemma lem94399 : term47.
Proof. exact (fun n : nat => @lem94394 n). Qed.
Lemma lem94400 : term49.
Proof. exact (conj (@lem94393) (@lem94399)). Qed.
Lemma lem94401 : term7.
Proof. exact (@lem93817 (@lem94400)). Qed.
Lemma lem94402 (m : nat) : term17 m.
Proof. exact (fun h0 : term11 m => @lem94377 m h0). Qed.
Lemma lem94407 : term21.
Proof. exact (fun m : nat => @lem94402 m). Qed.
Lemma lem94408 : term23.
Proof. exact (conj (@lem94401) (@lem94407)). Qed.
Lemma lem94409 : term28.
Proof. exact (@lem93793 (@lem94408)). Qed.
