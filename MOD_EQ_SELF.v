Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import MOD_EQ_SELF_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import DIVISION_spec.
Require Import LE_1_spec.
Require Import MOD_LT_spec.
Require Import MOD_ZERO_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm16933_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17646_spec.
Require Import thm18392_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18970_spec.
Require Import thm18971_spec.
Require Import thm19490_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm69_spec.
Lemma lem170685 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem170686 : term1 = term2.
Proof. exact (@lem170685 term1). Qed.
Lemma lem170687 : term2 = term1.
Proof. exact (SYM (@lem170686)). Qed.
Lemma lem170688 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem170691 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem170692 : term5.
Proof. exact (fun h0 : term4 => @lem170691 h0). Qed.
Lemma lem170693 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem170694 (h1 : term4) : term4.
Proof. exact (h1). Qed.
Lemma lem170695 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem170693 h2 (@lem170694 h1)). Qed.
Lemma lem170696 (h1 : term4) : term6.
Proof. exact (fun h0 : term5 => @lem170695 h1 h0). Qed.
Lemma lem170697 (h1 : term5) : term5.
Proof. exact (h1). Qed.
Lemma lem170698 (h1 : term4) (h2 : term5) : term4.
Proof. exact (@lem170696 h1 (@lem170697 h2)). Qed.
Lemma lem170699 (h1 : term5) : term5.
Proof. exact (fun h0 : term4 => @lem170698 h0 h1). Qed.
Lemma lem170700 : term7.
Proof. exact (fun h0 : term5 => @lem170699 h0). Qed.
Lemma lem170703 : term5.
Proof. exact (@lem170700 (@lem170692)). Qed.
Lemma lem170791 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem170792 : term8 = term9.
Proof. exact (@lem170791 term10). Qed.
Lemma lem170797 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem170798 : term12 = term13.
Proof. exact (MK_COMB (@lem170797) (@lem170792)). Qed.
Lemma lem170801 : term14 = term14.
Proof. exact (eq_refl term14). Qed.
Lemma lem170802 : term15 = term16.
Proof. exact (MK_COMB (@lem170801) (@lem170798)). Qed.
Lemma lem170805 : term17 = term17.
Proof. exact (eq_refl term17). Qed.
Lemma lem170806 : term18 = term19.
Proof. exact (MK_COMB (@lem170805) (@lem170802)). Qed.
Lemma lem170809 : term20 = term20.
Proof. exact (eq_refl term20). Qed.
Lemma lem170816 : term4 = term21.
Proof. exact (MK_COMB (@lem170809) (@lem170806)). Qed.
Lemma lem170817 (n : nat) : ((term22 n) = n) = ((term22 n) = n).
Proof. exact (eq_refl ((term22 n) = n)). Qed.
Lemma lem170818 : term23 = term23.
Proof. exact (fun_ext (fun n : nat => @lem170817 n)). Qed.
Lemma lem170819 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170820 : term10 = term10.
Proof. exact (MK_COMB (@lem170819) (@lem170818)). Qed.
Lemma lem170821 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem170822 : term9 = term9.
Proof. exact (MK_COMB (@lem170821) (@lem170820)). Qed.
Lemma lem170827 (n : nat) (m : nat) : (term24 n m) = (term24 n m).
Proof. exact (eq_refl (term24 n m)). Qed.
Lemma lem170828 (m : nat) : (term25 m) = (term25 m).
Proof. exact (fun_ext (fun n : nat => @lem170827 n m)). Qed.
Lemma lem170829 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170830 (m : nat) : (term26 m) = (term26 m).
Proof. exact (MK_COMB (@lem170829) (@lem170828 m)). Qed.
Lemma lem170831 : term27 = term27.
Proof. exact (fun_ext (fun m : nat => @lem170830 m)). Qed.
Lemma lem170832 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170833 : term28 = term28.
Proof. exact (MK_COMB (@lem170832) (@lem170831)). Qed.
Lemma lem170834 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem170835 : term11 = term11.
Proof. exact (MK_COMB (@lem170834) (@lem170833)). Qed.
Lemma lem170836 : term13 = term13.
Proof. exact (MK_COMB (@lem170835) (@lem170822)). Qed.
Lemma lem170847 (m : nat) (n : nat) : (term29 m n) = (term29 m n).
Proof. exact (eq_refl (term29 m n)). Qed.
Lemma lem170848 (m : nat) : (term30 m) = (term30 m).
Proof. exact (fun_ext (fun n : nat => @lem170847 m n)). Qed.
Lemma lem170849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170850 (m : nat) : (term31 m) = (term31 m).
Proof. exact (MK_COMB (@lem170849) (@lem170848 m)). Qed.
Lemma lem170851 : term32 = term32.
Proof. exact (fun_ext (fun m : nat => @lem170850 m)). Qed.
Lemma lem170852 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170853 : term33 = term33.
Proof. exact (MK_COMB (@lem170852) (@lem170851)). Qed.
Lemma lem170854 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem170855 : term14 = term14.
Proof. exact (MK_COMB (@lem170854) (@lem170853)). Qed.
Lemma lem170856 : term16 = term16.
Proof. exact (MK_COMB (@lem170855) (@lem170836)). Qed.
Lemma lem170863 (n : nat) : (term34 n) = (term34 n).
Proof. exact (eq_refl (term34 n)). Qed.
Lemma lem170864 : term35 = term35.
Proof. exact (fun_ext (fun n : nat => @lem170863 n)). Qed.
Lemma lem170865 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170866 : term36 = term36.
Proof. exact (MK_COMB (@lem170865) (@lem170864)). Qed.
Lemma lem170871 (n : nat) : (term37 n) = (term37 n).
Proof. exact (eq_refl (term37 n)). Qed.
Lemma lem170872 : term38 = term38.
Proof. exact (fun_ext (fun n : nat => @lem170871 n)). Qed.
Lemma lem170873 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170874 : term39 = term39.
Proof. exact (MK_COMB (@lem170873) (@lem170872)). Qed.
Lemma lem170875 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170876 : term40 = term40.
Proof. exact (MK_COMB (@lem170875) (@lem170874)). Qed.
Lemma lem170877 : term41 = term41.
Proof. exact (MK_COMB (@lem170876) (@lem170866)). Qed.
Lemma lem170882 (n : nat) : (term42 n) = (term42 n).
Proof. exact (eq_refl (term42 n)). Qed.
Lemma lem170883 : term43 = term43.
Proof. exact (fun_ext (fun n : nat => @lem170882 n)). Qed.
Lemma lem170884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170885 : term44 = term44.
Proof. exact (MK_COMB (@lem170884) (@lem170883)). Qed.
Lemma lem170886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170887 : term45 = term45.
Proof. exact (MK_COMB (@lem170886) (@lem170885)). Qed.
Lemma lem170888 : term46 = term46.
Proof. exact (MK_COMB (@lem170887) (@lem170877)). Qed.
Lemma lem170895 (n : nat) : (term47 n) = (term47 n).
Proof. exact (eq_refl (term47 n)). Qed.
Lemma lem170896 : term48 = term48.
Proof. exact (fun_ext (fun n : nat => @lem170895 n)). Qed.
Lemma lem170897 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170898 : term49 = term49.
Proof. exact (MK_COMB (@lem170897) (@lem170896)). Qed.
Lemma lem170899 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170900 : term50 = term50.
Proof. exact (MK_COMB (@lem170899) (@lem170898)). Qed.
Lemma lem170901 : term51 = term51.
Proof. exact (MK_COMB (@lem170900) (@lem170888)). Qed.
Lemma lem170908 (n : nat) : (term52 n) = (term52 n).
Proof. exact (eq_refl (term52 n)). Qed.
Lemma lem170909 : term53 = term53.
Proof. exact (fun_ext (fun n : nat => @lem170908 n)). Qed.
Lemma lem170910 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170911 : term54 = term54.
Proof. exact (MK_COMB (@lem170910) (@lem170909)). Qed.
Lemma lem170912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170913 : term55 = term55.
Proof. exact (MK_COMB (@lem170912) (@lem170911)). Qed.
Lemma lem170914 : term56 = term56.
Proof. exact (MK_COMB (@lem170913) (@lem170901)). Qed.
Lemma lem170921 (n : nat) : (term57 n) = (term57 n).
Proof. exact (eq_refl (term57 n)). Qed.
Lemma lem170922 : term58 = term58.
Proof. exact (fun_ext (fun n : nat => @lem170921 n)). Qed.
Lemma lem170923 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170924 : term59 = term59.
Proof. exact (MK_COMB (@lem170923) (@lem170922)). Qed.
Lemma lem170925 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem170926 : term60 = term60.
Proof. exact (MK_COMB (@lem170925) (@lem170924)). Qed.
Lemma lem170927 : term61 = term61.
Proof. exact (MK_COMB (@lem170926) (@lem170914)). Qed.
Lemma lem170928 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem170929 : term17 = term17.
Proof. exact (MK_COMB (@lem170928) (@lem170927)). Qed.
Lemma lem170930 : term19 = term19.
Proof. exact (MK_COMB (@lem170929) (@lem170856)). Qed.
Lemma lem170939 (m : nat) (n : nat) : (((Nat.modulo m n) = m) = (term62 m n)) = (((Nat.modulo m n) = m) = (term62 m n)).
Proof. exact (eq_refl (((Nat.modulo m n) = m) = (term62 m n))). Qed.
Lemma lem170940 (m : nat) : (term63 m) = (term63 m).
Proof. exact (fun_ext (fun n : nat => @lem170939 m n)). Qed.
Lemma lem170941 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170942 (m : nat) : (term64 m) = (term64 m).
Proof. exact (MK_COMB (@lem170941) (@lem170940 m)). Qed.
Lemma lem170943 : term65 = term65.
Proof. exact (fun_ext (fun m : nat => @lem170942 m)). Qed.
Lemma lem170944 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem170945 : term1 = term1.
Proof. exact (MK_COMB (@lem170944) (@lem170943)). Qed.
Lemma lem170946 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem170947 : term3 = term3.
Proof. exact (MK_COMB (@lem170946) (@lem170945)). Qed.
Lemma lem170948 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem170949 : term20 = term20.
Proof. exact (MK_COMB (@lem170948) (@lem170947)). Qed.
Lemma lem170950 : term21 = term21.
Proof. exact (MK_COMB (@lem170949) (@lem170930)). Qed.
Lemma lem171069 : term4 = term21.
Proof. exact (TRANS (@lem170816) (@lem170950)). Qed.
Lemma lem171070 : term21 = term4.
Proof. exact (SYM (@lem171069)). Qed.
Lemma lem171071 (h1 : term3) : term3.
Proof. exact (h1). Qed.
Lemma lem171073 (h1 : term33) : term33.
Proof. exact (h1). Qed.
Lemma lem171074 (h1 : term28) : term28.
Proof. exact (h1). Qed.
Lemma lem171075 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem171086 (m : nat) (n : nat) : (term66 m n) = (term67 m n).
Proof. exact (@lem17160 (n = (NUMERAL 0)) (Peano.lt m n)). Qed.
Lemma lem171092 (m : nat) (n : nat) : (term68 m n) = (term68 m n).
Proof. exact (eq_refl (term68 m n)). Qed.
Lemma lem171094 (n : nat) (m : nat) : (term69 n m) = (term69 n m).
Proof. exact (eq_refl (term69 n m)). Qed.
Lemma lem171095 (m : nat) (n : nat) : (term70 m n) = (term71 m n).
Proof. exact (MK_COMB (@lem171094 n m) (@lem171086 m n)). Qed.
Lemma lem171096 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171097 (m : nat) (n : nat) : (term72 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem171096) (@lem171095 m n)). Qed.
Lemma lem171098 (m : nat) (n : nat) : (term74 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem171097 m n) (@lem171092 m n)). Qed.
Lemma lem171099 (m : nat) (n : nat) : (term76 m n) = (term74 m n).
Proof. exact (@lem17646 ((Nat.modulo m n) = m) (term62 m n)). Qed.
Lemma lem171100 (m : nat) (n : nat) : (term76 m n) = (term75 m n).
Proof. exact (TRANS (@lem171099 m n) (@lem171098 m n)). Qed.
Lemma lem171101 (P : nat -> Prop) : (term77 P) = (term78 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem171102 (m : nat) : (term79 m) = (term80 m).
Proof. exact (@lem171101 (term63 m)). Qed.
Lemma lem171103 (m : nat) (n : nat) : (term81 m n) = (((Nat.modulo m n) = m) = (term62 m n)).
Proof. exact (eq_refl (term81 m n)). Qed.
Lemma lem171104 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem171105 (m : nat) (n : nat) : (term82 m n) = (term76 m n).
Proof. exact (MK_COMB (@lem171104) (@lem171103 m n)). Qed.
Lemma lem171106 (m : nat) (n : nat) : (term82 m n) = (term75 m n).
Proof. exact (TRANS (@lem171105 m n) (@lem171100 m n)). Qed.
Lemma lem171107 (m : nat) : (term83 m) = (term84 m).
Proof. exact (fun_ext (fun n : nat => @lem171106 m n)). Qed.
Lemma lem171108 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171109 (m : nat) : (term80 m) = (term85 m).
Proof. exact (MK_COMB (@lem171108) (@lem171107 m)). Qed.
Lemma lem171110 (m : nat) : (term79 m) = (term85 m).
Proof. exact (TRANS (@lem171102 m) (@lem171109 m)). Qed.
Lemma lem171111 (P : nat -> Prop) : (term77 P) = (term78 P).
Proof. exact (@lem18392 nat P). Qed.
Lemma lem171112 : term3 = term86.
Proof. exact (@lem171111 term65). Qed.
Lemma lem171113 (m : nat) : (term87 m) = (term64 m).
Proof. exact (eq_refl (term87 m)). Qed.
Lemma lem171114 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem171115 (m : nat) : (term88 m) = (term79 m).
Proof. exact (MK_COMB (@lem171114) (@lem171113 m)). Qed.
Lemma lem171116 (m : nat) : (term88 m) = (term85 m).
Proof. exact (TRANS (@lem171115 m) (@lem171110 m)). Qed.
Lemma lem171117 : term89 = term90.
Proof. exact (fun_ext (fun m : nat => @lem171116 m)). Qed.
Lemma lem171118 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171119 : term86 = term91.
Proof. exact (MK_COMB (@lem171118) (@lem171117)). Qed.
Lemma lem171120 : term3 = term91.
Proof. exact (TRANS (@lem171112) (@lem171119)). Qed.
Lemma lem171126 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem171127 (P : nat -> Prop) (Q : nat -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem171126 nat P Q). Qed.
Lemma lem171128 (m : nat) : (term96 m) = (term97 m).
Proof. exact (@lem171127 (term98 m) (term99 m)). Qed.
Lemma lem171129 (m : nat) (n : nat) : (term100 m n) = (term71 m n).
Proof. exact (eq_refl (term100 m n)). Qed.
Lemma lem171130 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171131 (m : nat) (n : nat) : (term101 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem171130) (@lem171129 m n)). Qed.
Lemma lem171132 (m : nat) (n : nat) : (term102 m n) = (term68 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem171133 (m : nat) (n : nat) : (term103 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem171131 m n) (@lem171132 m n)). Qed.
Lemma lem171134 (m : nat) : (term104 m) = (term84 m).
Proof. exact (fun_ext (fun n : nat => @lem171133 m n)). Qed.
Lemma lem171135 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171136 (m : nat) : (term96 m) = (term85 m).
Proof. exact (MK_COMB (@lem171135) (@lem171134 m)). Qed.
Lemma lem171137 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem171138 (m : nat) : (term105 m) = (term106 m).
Proof. exact (MK_COMB (@lem171137) (@lem171136 m)). Qed.
Lemma lem171139 (m : nat) (n : nat) : (term100 m n) = (term71 m n).
Proof. exact (eq_refl (term100 m n)). Qed.
Lemma lem171140 (m : nat) : (term107 m) = (term98 m).
Proof. exact (fun_ext (fun n : nat => @lem171139 m n)). Qed.
Lemma lem171141 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171142 (m : nat) : (term108 m) = (term109 m).
Proof. exact (MK_COMB (@lem171141) (@lem171140 m)). Qed.
Lemma lem171143 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171144 (m : nat) : (term110 m) = (term111 m).
Proof. exact (MK_COMB (@lem171143) (@lem171142 m)). Qed.
Lemma lem171145 (m : nat) (n : nat) : (term102 m n) = (term68 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem171146 (m : nat) : (term112 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem171145 m n)). Qed.
Lemma lem171147 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171148 (m : nat) : (term113 m) = (term114 m).
Proof. exact (MK_COMB (@lem171147) (@lem171146 m)). Qed.
Lemma lem171149 (m : nat) : (term97 m) = (term115 m).
Proof. exact (MK_COMB (@lem171144 m) (@lem171148 m)). Qed.
Lemma lem171150 (m : nat) : ((term96 m) = (term97 m)) = ((term85 m) = (term115 m)).
Proof. exact (MK_COMB (@lem171138 m) (@lem171149 m)). Qed.
Lemma lem171151 (m : nat) : (term85 m) = (term115 m).
Proof. exact (EQ_MP (@lem171150 m) (@lem171128 m)). Qed.
Lemma lem171248 : term90 = term116.
Proof. exact (fun_ext (fun m : nat => @lem171151 m)). Qed.
Lemma lem171249 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171250 : term91 = term117.
Proof. exact (MK_COMB (@lem171249) (@lem171248)). Qed.
Lemma lem171252 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term92 A P Q) = (term93 A P Q).
Proof. exact (EQ_MP (@lem18971 A P Q) (@lem18970 A P Q)). Qed.
Lemma lem171253 (P : nat -> Prop) (Q : nat -> Prop) : (term94 P Q) = (term95 P Q).
Proof. exact (@lem171252 nat P Q). Qed.
Lemma lem171254 : term118 = term119.
Proof. exact (@lem171253 term120 term121). Qed.
Lemma lem171255 (m : nat) : (term122 m) = (term109 m).
Proof. exact (eq_refl (term122 m)). Qed.
Lemma lem171256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171257 (m : nat) : (term123 m) = (term111 m).
Proof. exact (MK_COMB (@lem171256) (@lem171255 m)). Qed.
Lemma lem171258 (m : nat) : (term124 m) = (term114 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem171259 (m : nat) : (term125 m) = (term115 m).
Proof. exact (MK_COMB (@lem171257 m) (@lem171258 m)). Qed.
Lemma lem171260 : term126 = term116.
Proof. exact (fun_ext (fun m : nat => @lem171259 m)). Qed.
Lemma lem171261 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171262 : term118 = term117.
Proof. exact (MK_COMB (@lem171261) (@lem171260)). Qed.
Lemma lem171263 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem171264 : term127 = term128.
Proof. exact (MK_COMB (@lem171263) (@lem171262)). Qed.
Lemma lem171265 (m : nat) : (term122 m) = (term109 m).
Proof. exact (eq_refl (term122 m)). Qed.
Lemma lem171266 : term129 = term120.
Proof. exact (fun_ext (fun m : nat => @lem171265 m)). Qed.
Lemma lem171267 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171268 : term130 = term131.
Proof. exact (MK_COMB (@lem171267) (@lem171266)). Qed.
Lemma lem171269 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171270 : term132 = term133.
Proof. exact (MK_COMB (@lem171269) (@lem171268)). Qed.
Lemma lem171271 (m : nat) : (term124 m) = (term114 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem171272 : term134 = term121.
Proof. exact (fun_ext (fun m : nat => @lem171271 m)). Qed.
Lemma lem171273 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171274 : term135 = term136.
Proof. exact (MK_COMB (@lem171273) (@lem171272)). Qed.
Lemma lem171275 : term119 = term137.
Proof. exact (MK_COMB (@lem171270) (@lem171274)). Qed.
Lemma lem171276 : (term118 = term119) = (term117 = term137).
Proof. exact (MK_COMB (@lem171264) (@lem171275)). Qed.
Lemma lem171277 : term117 = term137.
Proof. exact (EQ_MP (@lem171276) (@lem171254)). Qed.
Lemma lem171382 : term91 = term137.
Proof. exact (TRANS (@lem171250) (@lem171277)). Qed.
Lemma lem171384 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem171385 (P : nat -> Prop) (Q : nat -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem171384 nat P Q). Qed.
Lemma lem171386 : term119 = term118.
Proof. exact (@lem171385 term120 term121). Qed.
Lemma lem171387 (m : nat) : (term122 m) = (term109 m).
Proof. exact (eq_refl (term122 m)). Qed.
Lemma lem171388 : term129 = term120.
Proof. exact (fun_ext (fun m : nat => @lem171387 m)). Qed.
Lemma lem171389 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171390 : term130 = term131.
Proof. exact (MK_COMB (@lem171389) (@lem171388)). Qed.
Lemma lem171391 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171392 : term132 = term133.
Proof. exact (MK_COMB (@lem171391) (@lem171390)). Qed.
Lemma lem171393 (m : nat) : (term124 m) = (term114 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem171394 : term134 = term121.
Proof. exact (fun_ext (fun m : nat => @lem171393 m)). Qed.
Lemma lem171395 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171396 : term135 = term136.
Proof. exact (MK_COMB (@lem171395) (@lem171394)). Qed.
Lemma lem171397 : term119 = term137.
Proof. exact (MK_COMB (@lem171392) (@lem171396)). Qed.
Lemma lem171398 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem171399 : term138 = term139.
Proof. exact (MK_COMB (@lem171398) (@lem171397)). Qed.
Lemma lem171400 (m : nat) : (term122 m) = (term109 m).
Proof. exact (eq_refl (term122 m)). Qed.
Lemma lem171401 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171402 (m : nat) : (term123 m) = (term111 m).
Proof. exact (MK_COMB (@lem171401) (@lem171400 m)). Qed.
Lemma lem171403 (m : nat) : (term124 m) = (term114 m).
Proof. exact (eq_refl (term124 m)). Qed.
Lemma lem171404 (m : nat) : (term125 m) = (term115 m).
Proof. exact (MK_COMB (@lem171402 m) (@lem171403 m)). Qed.
Lemma lem171405 : term126 = term116.
Proof. exact (fun_ext (fun m : nat => @lem171404 m)). Qed.
Lemma lem171406 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171407 : term118 = term117.
Proof. exact (MK_COMB (@lem171406) (@lem171405)). Qed.
Lemma lem171408 : (term119 = term118) = (term137 = term117).
Proof. exact (MK_COMB (@lem171399) (@lem171407)). Qed.
Lemma lem171409 : term137 = term117.
Proof. exact (EQ_MP (@lem171408) (@lem171386)). Qed.
Lemma lem171411 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term93 A P Q) = (term92 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem171412 (P : nat -> Prop) (Q : nat -> Prop) : (term95 P Q) = (term94 P Q).
Proof. exact (@lem171411 nat P Q). Qed.
Lemma lem171413 (m : nat) : (term97 m) = (term96 m).
Proof. exact (@lem171412 (term98 m) (term99 m)). Qed.
Lemma lem171414 (m : nat) (n : nat) : (term100 m n) = (term71 m n).
Proof. exact (eq_refl (term100 m n)). Qed.
Lemma lem171415 (m : nat) : (term107 m) = (term98 m).
Proof. exact (fun_ext (fun n : nat => @lem171414 m n)). Qed.
Lemma lem171416 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171417 (m : nat) : (term108 m) = (term109 m).
Proof. exact (MK_COMB (@lem171416) (@lem171415 m)). Qed.
Lemma lem171418 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171419 (m : nat) : (term110 m) = (term111 m).
Proof. exact (MK_COMB (@lem171418) (@lem171417 m)). Qed.
Lemma lem171420 (m : nat) (n : nat) : (term102 m n) = (term68 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem171421 (m : nat) : (term112 m) = (term99 m).
Proof. exact (fun_ext (fun n : nat => @lem171420 m n)). Qed.
Lemma lem171422 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171423 (m : nat) : (term113 m) = (term114 m).
Proof. exact (MK_COMB (@lem171422) (@lem171421 m)). Qed.
Lemma lem171424 (m : nat) : (term97 m) = (term115 m).
Proof. exact (MK_COMB (@lem171419 m) (@lem171423 m)). Qed.
Lemma lem171425 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem171426 (m : nat) : (term140 m) = (term141 m).
Proof. exact (MK_COMB (@lem171425) (@lem171424 m)). Qed.
Lemma lem171427 (m : nat) (n : nat) : (term100 m n) = (term71 m n).
Proof. exact (eq_refl (term100 m n)). Qed.
Lemma lem171428 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171429 (m : nat) (n : nat) : (term101 m n) = (term73 m n).
Proof. exact (MK_COMB (@lem171428) (@lem171427 m n)). Qed.
Lemma lem171430 (m : nat) (n : nat) : (term102 m n) = (term68 m n).
Proof. exact (eq_refl (term102 m n)). Qed.
Lemma lem171431 (m : nat) (n : nat) : (term103 m n) = (term75 m n).
Proof. exact (MK_COMB (@lem171429 m n) (@lem171430 m n)). Qed.
Lemma lem171432 (m : nat) : (term104 m) = (term84 m).
Proof. exact (fun_ext (fun n : nat => @lem171431 m n)). Qed.
Lemma lem171433 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171434 (m : nat) : (term96 m) = (term85 m).
Proof. exact (MK_COMB (@lem171433) (@lem171432 m)). Qed.
Lemma lem171435 (m : nat) : ((term97 m) = (term96 m)) = ((term115 m) = (term85 m)).
Proof. exact (MK_COMB (@lem171426 m) (@lem171434 m)). Qed.
Lemma lem171436 (m : nat) : (term115 m) = (term85 m).
Proof. exact (EQ_MP (@lem171435 m) (@lem171413 m)). Qed.
Lemma lem171437 : term116 = term90.
Proof. exact (fun_ext (fun m : nat => @lem171436 m)). Qed.
Lemma lem171438 : (@ex nat) = (@ex nat).
Proof. exact (eq_refl (@ex nat)). Qed.
Lemma lem171439 : term117 = term91.
Proof. exact (MK_COMB (@lem171438) (@lem171437)). Qed.
Lemma lem171440 : term137 = term91.
Proof. exact (TRANS (@lem171409) (@lem171439)). Qed.
Lemma lem171441 : term91 = term91.
Proof. exact (TRANS (@lem171382) (@lem171440)). Qed.
Lemma lem171442 : term3 = term91.
Proof. exact (TRANS (@lem171120) (@lem171441)). Qed.
Lemma lem171443 (h1 : term3) : term91.
Proof. exact (EQ_MP (@lem171442) (@lem171071 h1)). Qed.
Lemma lem171818 (n : nat) : (term142 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem171823 (m : nat) (n : nat) : (term143 m n) = (term143 m n).
Proof. exact (eq_refl (term143 m n)). Qed.
Lemma lem171824 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem171825 (n : nat) : (term144 n) = (term145 n).
Proof. exact (MK_COMB (@lem171824) (@lem171818 n)). Qed.
Lemma lem171826 (m : nat) (n : nat) : (term146 m n) = (term147 m n).
Proof. exact (MK_COMB (@lem171825 n) (@lem171823 m n)). Qed.
Lemma lem171827 (m : nat) (n : nat) : (term29 m n) = (term146 m n).
Proof. exact (@lem17265 (term148 n) (term143 m n)). Qed.
Lemma lem171828 (m : nat) (n : nat) : (term29 m n) = (term147 m n).
Proof. exact (TRANS (@lem171827 m n) (@lem171826 m n)). Qed.
Lemma lem171829 (m : nat) : (term30 m) = (term149 m).
Proof. exact (fun_ext (fun n : nat => @lem171828 m n)). Qed.
Lemma lem171830 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem171831 (m : nat) : (term31 m) = (term150 m).
Proof. exact (MK_COMB (@lem171830) (@lem171829 m)). Qed.
Lemma lem171832 : term32 = term151.
Proof. exact (fun_ext (fun m : nat => @lem171831 m)). Qed.
Lemma lem171833 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem171890 : term33 = term152.
Proof. exact (MK_COMB (@lem171833) (@lem171832)). Qed.
Lemma lem171891 (h1 : term33) : term152.
Proof. exact (EQ_MP (@lem171890) (@lem171073 h1)). Qed.
Lemma lem171898 (n : nat) (m : nat) : (term24 n m) = (term153 n m).
Proof. exact (@lem17265 (Peano.lt m n) ((Nat.modulo m n) = m)). Qed.
Lemma lem171899 (m : nat) : (term25 m) = (term154 m).
Proof. exact (fun_ext (fun n : nat => @lem171898 n m)). Qed.
Lemma lem171900 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem171901 (m : nat) : (term26 m) = (term155 m).
Proof. exact (MK_COMB (@lem171900) (@lem171899 m)). Qed.
Lemma lem171902 : term27 = term156.
Proof. exact (fun_ext (fun m : nat => @lem171901 m)). Qed.
Lemma lem171903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem171960 : term28 = term157.
Proof. exact (MK_COMB (@lem171903) (@lem171902)). Qed.
Lemma lem171961 (h1 : term28) : term157.
Proof. exact (EQ_MP (@lem171960) (@lem171074 h1)). Qed.
Lemma lem171962 (n : nat) : ((term22 n) = n) = ((term22 n) = n).
Proof. exact (eq_refl ((term22 n) = n)). Qed.
Lemma lem171963 : term23 = term23.
Proof. exact (fun_ext (fun n : nat => @lem171962 n)). Qed.
Lemma lem171964 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem171973 : term10 = term10.
Proof. exact (MK_COMB (@lem171964) (@lem171963)). Qed.
Lemma lem171974 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem171973) (@lem171075 h1)). Qed.
Lemma lem171975 (m : nat) (h1 : term85 m) : term85 m.
Proof. exact (h1). Qed.
Lemma lem172175 (m : nat) (n : nat) : (term147 m n) = (term147 m n).
Proof. exact (eq_refl (term147 m n)). Qed.
Lemma lem172176 (m : nat) : (term149 m) = (term149 m).
Proof. exact (fun_ext (fun n : nat => @lem172175 m n)). Qed.
Lemma lem172177 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172178 (m : nat) : (term150 m) = (term150 m).
Proof. exact (MK_COMB (@lem172177) (@lem172176 m)). Qed.
Lemma lem172179 : term151 = term151.
Proof. exact (fun_ext (fun m : nat => @lem172178 m)). Qed.
Lemma lem172180 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172181 : term152 = term152.
Proof. exact (MK_COMB (@lem172180) (@lem172179)). Qed.
Lemma lem172182 (h1 : term33) : term152.
Proof. exact (EQ_MP (@lem172181) (@lem171891 h1)). Qed.
Lemma lem172201 (n : nat) (m : nat) : (term153 n m) = (term153 n m).
Proof. exact (eq_refl (term153 n m)). Qed.
Lemma lem172202 (m : nat) : (term154 m) = (term154 m).
Proof. exact (fun_ext (fun n : nat => @lem172201 n m)). Qed.
Lemma lem172203 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172204 (m : nat) : (term155 m) = (term155 m).
Proof. exact (MK_COMB (@lem172203) (@lem172202 m)). Qed.
Lemma lem172205 : term156 = term156.
Proof. exact (fun_ext (fun m : nat => @lem172204 m)). Qed.
Lemma lem172206 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172207 : term157 = term157.
Proof. exact (MK_COMB (@lem172206) (@lem172205)). Qed.
Lemma lem172208 (h1 : term28) : term157.
Proof. exact (EQ_MP (@lem172207) (@lem171961 h1)). Qed.
Lemma lem172219 (n : nat) : ((term22 n) = n) = ((term22 n) = n).
Proof. exact (eq_refl ((term22 n) = n)). Qed.
Lemma lem172220 : term23 = term23.
Proof. exact (fun_ext (fun n : nat => @lem172219 n)). Qed.
Lemma lem172221 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172222 : term10 = term10.
Proof. exact (MK_COMB (@lem172221) (@lem172220)). Qed.
Lemma lem172223 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem172222) (@lem171974 h1)). Qed.
Lemma lem172287 (m : nat) (n : nat) (h1 : term75 m n) : term75 m n.
Proof. exact (h1). Qed.
Lemma lem172298 (m : nat) (n : nat) (h1 : term71 m n) : term71 m n.
Proof. exact (h1). Qed.
Lemma lem172299 (m : nat) (n : nat) (h1 : term68 m n) : term68 m n.
Proof. exact (h1). Qed.
Lemma lem172300 (m : nat) (n : nat) (h1 : term71 m n) : term67 m n.
Proof. exact (proj2 (@lem172298 m n h1)). Qed.
Lemma lem172304 (m : nat) (n : nat) (h1 : term68 m n) : term62 m n.
Proof. exact (proj2 (@lem172299 m n h1)). Qed.
Lemma lem172325 (m : nat) (n : nat) : (term147 m n) = (term158 m n).
Proof. exact (@lem19490 (m = (term159 m n)) (n = (NUMERAL 0)) (term160 m n)). Qed.
Lemma lem172326 (m : nat) : (term149 m) = (term161 m).
Proof. exact (fun_ext (fun n : nat => @lem172325 m n)). Qed.
Lemma lem172327 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172328 (m : nat) : (term150 m) = (term162 m).
Proof. exact (MK_COMB (@lem172327) (@lem172326 m)). Qed.
Lemma lem172329 : term151 = term163.
Proof. exact (fun_ext (fun m : nat => @lem172328 m)). Qed.
Lemma lem172330 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172332 : term152 = term164.
Proof. exact (MK_COMB (@lem172330) (@lem172329)). Qed.
Lemma lem172333 (h1 : term33) : term164.
Proof. exact (EQ_MP (@lem172332) (@lem172182 h1)). Qed.
Lemma lem172490 (n : nat) : ((term22 n) = n) = ((term22 n) = n).
Proof. exact (eq_refl ((term22 n) = n)). Qed.
Lemma lem172491 : term23 = term23.
Proof. exact (fun_ext (fun n : nat => @lem172490 n)). Qed.
Lemma lem172492 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172494 : term10 = term10.
Proof. exact (MK_COMB (@lem172492) (@lem172491)). Qed.
Lemma lem172495 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem172494) (@lem172223 h1)). Qed.
Lemma lem172581 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem172615 (n : nat) (m : nat) : (term153 n m) = (term153 n m).
Proof. exact (eq_refl (term153 n m)). Qed.
Lemma lem172616 (m : nat) : (term154 m) = (term154 m).
Proof. exact (fun_ext (fun n : nat => @lem172615 n m)). Qed.
Lemma lem172617 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172618 (m : nat) : (term155 m) = (term155 m).
Proof. exact (MK_COMB (@lem172617) (@lem172616 m)). Qed.
Lemma lem172619 : term156 = term156.
Proof. exact (fun_ext (fun m : nat => @lem172618 m)). Qed.
Lemma lem172620 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem172622 : term157 = term157.
Proof. exact (MK_COMB (@lem172620) (@lem172619)). Qed.
Lemma lem172623 (h1 : term28) : term157.
Proof. exact (EQ_MP (@lem172622) (@lem172208 h1)). Qed.
Lemma lem172716 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem172717 (_3504 : nat) (h1 : term33) : term165 _3504.
Proof. exact (@lem172333 h1 _3504). Qed.
Lemma lem172718 (_3504 : nat) : (term165 _3504) = (term162 _3504).
Proof. exact (eq_refl (term165 _3504)). Qed.
Lemma lem172719 (_3504 : nat) (h1 : term33) : term162 _3504.
Proof. exact (EQ_MP (@lem172718 _3504) (@lem172717 _3504 h1)). Qed.
Lemma lem172720 (_3504 : nat) (_3505 : nat) (h1 : term33) : term166 _3504 _3505.
Proof. exact (@lem172719 _3504 h1 _3505). Qed.
Lemma lem172721 (_3504 : nat) (_3505 : nat) : (term166 _3504 _3505) = (term158 _3504 _3505).
Proof. exact (eq_refl (term166 _3504 _3505)). Qed.
Lemma lem172722 (_3504 : nat) (_3505 : nat) (h1 : term33) : term158 _3504 _3505.
Proof. exact (EQ_MP (@lem172721 _3504 _3505) (@lem172720 _3504 _3505 h1)). Qed.
Lemma lem172762 (_3519 : nat) (h1 : term10) : term167 _3519.
Proof. exact (@lem172495 h1 _3519). Qed.
Lemma lem172763 (_3519 : nat) : (term167 _3519) = ((term22 _3519) = _3519).
Proof. exact (eq_refl (term167 _3519)). Qed.
Lemma lem172789 (_3528 : nat) (h1 : term28) : term168 _3528.
Proof. exact (@lem172623 h1 _3528). Qed.
Lemma lem172790 (_3528 : nat) : (term168 _3528) = (term155 _3528).
Proof. exact (eq_refl (term168 _3528)). Qed.
Lemma lem172791 (_3528 : nat) (h1 : term28) : term155 _3528.
Proof. exact (EQ_MP (@lem172790 _3528) (@lem172789 _3528 h1)). Qed.
Lemma lem172792 (_3528 : nat) (_3529 : nat) (h1 : term28) : term169 _3528 _3529.
Proof. exact (@lem172791 _3528 h1 _3529). Qed.
Lemma lem172793 (_3529 : nat) (_3528 : nat) : (term169 _3528 _3529) = (term153 _3529 _3528).
Proof. exact (eq_refl (term169 _3528 _3529)). Qed.
Lemma lem172871 (m : nat) (n : nat) (h1 : term71 m n) : term170 m n.
Proof. exact (proj2 (@lem172300 m n h1)). Qed.
Lemma lem172883 (_3504 : nat) (_3505 : nat) (h1 : term33) : term171 _3504 _3505.
Proof. exact (proj2 (@lem172722 _3504 _3505 h1)). Qed.
Lemma lem172929 (m : nat) (n : nat) (h1 : term68 m n) : term172 n m.
Proof. exact (proj1 (@lem172299 m n h1)). Qed.
Lemma lem172931 (n : nat) (h1 : n = (NUMERAL 0)) : n = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem172949 (_3529 : nat) (_3528 : nat) (h1 : term28) : term153 _3529 _3528.
Proof. exact (EQ_MP (@lem172793 _3529 _3528) (@lem172792 _3528 _3529 h1)). Qed.
Lemma lem172989 (m : nat) (n : nat) (h1 : term68 m n) : term172 n m.
Proof. exact (proj1 (@lem172299 m n h1)). Qed.
Lemma lem172991 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem173130 (m : nat) : (term173 m) = (term173 m).
Proof. exact (eq_refl (term173 m)). Qed.
Lemma lem173131 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term174 m n) = (term175 m).
Proof. exact (MK_COMB (@lem173130 m) (@lem172931 n h1)). Qed.
Lemma lem173132 (m : nat) : (term175 m) = (term176 m).
Proof. exact (eq_refl (term175 m)). Qed.
Lemma lem173133 (m : nat) (n : nat) : (term177 m n) = (term177 m n).
Proof. exact (eq_refl (term177 m n)). Qed.
Lemma lem173134 (n : nat) (m : nat) : ((term174 m n) = (term175 m)) = ((term174 m n) = (term176 m)).
Proof. exact (MK_COMB (@lem173133 m n) (@lem173132 m)). Qed.
Lemma lem173135 (n : nat) (m : nat) : (term174 m n) = (term172 n m).
Proof. exact (eq_refl (term174 m n)). Qed.
Lemma lem173136 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem173137 (n : nat) (m : nat) : (term177 m n) = (term178 n m).
Proof. exact (MK_COMB (@lem173136) (@lem173135 n m)). Qed.
Lemma lem173138 (m : nat) : (term176 m) = (term176 m).
Proof. exact (eq_refl (term176 m)). Qed.
Lemma lem173139 (n : nat) (m : nat) : ((term174 m n) = (term176 m)) = ((term172 n m) = (term176 m)).
Proof. exact (MK_COMB (@lem173137 n m) (@lem173138 m)). Qed.
Lemma lem173140 (n : nat) (m : nat) : ((term174 m n) = (term175 m)) = ((term172 n m) = (term176 m)).
Proof. exact (TRANS (@lem173134 n m) (@lem173139 n m)). Qed.
Lemma lem173141 (m : nat) (n : nat) (h1 : n = (NUMERAL 0)) : (term172 n m) = (term176 m).
Proof. exact (EQ_MP (@lem173140 n m) (@lem173131 m n h1)). Qed.
Lemma lem173142 (m : nat) (n : nat) (h1 : term68 m n) (h2 : n = (NUMERAL 0)) : term176 m.
Proof. exact (EQ_MP (@lem173141 m n h2) (@lem172929 m n h1)). Qed.
Lemma lem173190 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem173191 (_3565 : nat) (_3567 : nat) (h1 : _3565 = _3567) : _3565 = _3567.
Proof. exact (h1). Qed.
Lemma lem173192 (_3566 : nat) (_3568 : nat) (h1 : _3566 = _3568) : _3566 = _3568.
Proof. exact (h1). Qed.
Lemma lem173193 (_3565 : nat) (_3567 : nat) (h1 : _3565 = _3567) : (Peano.lt _3565) = (Peano.lt _3567).
Proof. exact (MK_COMB (@lem173190) (@lem173191 _3565 _3567 h1)). Qed.
Lemma lem173194 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) (h1 : _3565 = _3567) (h2 : _3566 = _3568) : (Peano.lt _3565 _3566) = (Peano.lt _3567 _3568).
Proof. exact (MK_COMB (@lem173193 _3565 _3567 h1) (@lem173192 _3566 _3568 h2)). Qed.
Lemma lem173196 (b : Prop) (a : Prop) : term179 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem173197 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : term180 _3567 _3568 _3565 _3566.
Proof. exact (@lem173196 (Peano.lt _3567 _3568) (Peano.lt _3565 _3566)). Qed.
Lemma lem173198 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) (h1 : _3565 = _3567) (h2 : _3566 = _3568) : term181 _3567 _3568 _3565 _3566.
Proof. exact (@lem173197 _3567 _3568 _3565 _3566 (@lem173194 _3565 _3567 _3566 _3568 h1 h2)). Qed.
Lemma lem173199 (_3568 : nat) (_3566 : nat) (_3565 : nat) (_3567 : nat) (h1 : _3565 = _3567) : term182 _3567 _3568 _3565 _3566.
Proof. exact (fun h0 : _3566 = _3568 => @lem173198 _3565 _3567 _3566 _3568 h1 h0). Qed.
Lemma lem173201 (a : Prop) (b : Prop) : (a -> b) = (term183 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem173202 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term182 _3567 _3568 _3565 _3566) = (term184 _3567 _3568 _3565 _3566).
Proof. exact (@lem173201 (_3566 = _3568) (term181 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173203 (_3568 : nat) (_3566 : nat) (_3565 : nat) (_3567 : nat) (h1 : _3565 = _3567) : term184 _3567 _3568 _3565 _3566.
Proof. exact (EQ_MP (@lem173202 _3567 _3568 _3565 _3566) (@lem173199 _3568 _3566 _3565 _3567 h1)). Qed.
Lemma lem173204 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : term185 _3567 _3568 _3565 _3566.
Proof. exact (fun h0 : _3565 = _3567 => @lem173203 _3568 _3566 _3565 _3567 h0). Qed.
Lemma lem173206 (a : Prop) (b : Prop) : (a -> b) = (term183 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem173207 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term185 _3567 _3568 _3565 _3566) = (term186 _3567 _3568 _3565 _3566).
Proof. exact (@lem173206 (_3565 = _3567) (term184 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173208 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : term186 _3567 _3568 _3565 _3566.
Proof. exact (EQ_MP (@lem173207 _3567 _3568 _3565 _3566) (@lem173204 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173288 (m : nat) (n : nat) (h1 : term71 m n) : (Nat.modulo m n) = m.
Proof. exact (proj1 (@lem172298 m n h1)). Qed.
Lemma lem173289 (m : nat) (n : nat) (h1 : term71 m n) : term187 n m.
Proof. exact (fun h0 : term172 n m => @lem173288 m n h1). Qed.
Lemma lem173291 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173292 (n : nat) (m : nat) : (term187 n m) = ((Nat.modulo m n) = m).
Proof. exact (@lem173291 ((Nat.modulo m n) = m)). Qed.
Lemma lem173293 (m : nat) (n : nat) (h1 : term71 m n) : (Nat.modulo m n) = m.
Proof. exact (EQ_MP (@lem173292 n m) (@lem173289 m n h1)). Qed.
Lemma lem173295 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem173296 (n : nat) : n = n.
Proof. exact (@lem173295 n). Qed.
Lemma lem173297 (n : nat) : term189 n.
Proof. exact (fun h0 : term190 n => @lem173296 n). Qed.
Lemma lem173299 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173300 (n : nat) : (term189 n) = (n = n).
Proof. exact (@lem173299 (n = n)). Qed.
Lemma lem173301 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem173300 n) (@lem173297 n)). Qed.
Lemma lem173303 (m : nat) (n : nat) (h1 : term71 m n) : term148 n.
Proof. exact (proj1 (@lem172300 m n h1)). Qed.
Lemma lem173304 (m : nat) (n : nat) (h1 : term71 m n) : term191 n.
Proof. exact (fun h0 : n = (NUMERAL 0) => @lem173303 m n h1). Qed.
Lemma lem173306 (p : Prop) : (term192 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem173307 (n : nat) : (term191 n) = (term148 n).
Proof. exact (@lem173306 (n = (NUMERAL 0))). Qed.
Lemma lem173308 (m : nat) (n : nat) (h1 : term71 m n) : term148 n.
Proof. exact (EQ_MP (@lem173307 n) (@lem173304 m n h1)). Qed.
Lemma lem173314 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem173315 (_3504 : nat) (_3505 : nat) : (term171 _3504 _3505) = (term193 _3504 _3505).
Proof. exact (@lem173314 (term160 _3504 _3505) (_3505 = (NUMERAL 0))). Qed.
Lemma lem173323 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem173324 (_3504 : nat) (_3505 : nat) : (term194 _3504 _3505) = (term195 _3504 _3505).
Proof. exact (MK_COMB (@lem173323) (@lem173315 _3504 _3505)). Qed.
Lemma lem173332 (_3504 : nat) (_3505 : nat) : (term193 _3504 _3505) = (term193 _3504 _3505).
Proof. exact (eq_refl (term193 _3504 _3505)). Qed.
Lemma lem173333 (_3504 : nat) (_3505 : nat) : ((term171 _3504 _3505) = (term193 _3504 _3505)) = ((term193 _3504 _3505) = (term193 _3504 _3505)).
Proof. exact (MK_COMB (@lem173324 _3504 _3505) (@lem173332 _3504 _3505)). Qed.
Lemma lem173335 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem173336 (x : Prop) : (x = x) = True.
Proof. exact (@lem173335 Prop x). Qed.
Lemma lem173337 (_3504 : nat) (_3505 : nat) : ((term193 _3504 _3505) = (term193 _3504 _3505)) = True.
Proof. exact (@lem173336 (term193 _3504 _3505)). Qed.
Lemma lem173338 (_3504 : nat) (_3505 : nat) : ((term171 _3504 _3505) = (term193 _3504 _3505)) = True.
Proof. exact (TRANS (@lem173333 _3504 _3505) (@lem173337 _3504 _3505)). Qed.
Lemma lem173339 (_3504 : nat) (_3505 : nat) : True = ((term171 _3504 _3505) = (term193 _3504 _3505)).
Proof. exact (SYM (@lem173338 _3504 _3505)). Qed.
Lemma lem173340 (_3504 : nat) (_3505 : nat) : (term171 _3504 _3505) = (term193 _3504 _3505).
Proof. exact (EQ_MP (@lem173339 _3504 _3505) (@lem0)). Qed.
Lemma lem173341 (_3504 : nat) (_3505 : nat) (h1 : term33) : term193 _3504 _3505.
Proof. exact (EQ_MP (@lem173340 _3504 _3505) (@lem172883 _3504 _3505 h1)). Qed.
Lemma lem173343 (b : Prop) (a : Prop) : (a \/ b) = (term196 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem173346 (_3504 : nat) (_3505 : nat) : (term193 _3504 _3505) = (term197 _3504 _3505).
Proof. exact (@lem173343 (_3505 = (NUMERAL 0)) (term160 _3504 _3505)). Qed.
Lemma lem173349 (_3504 : nat) (_3505 : nat) (h1 : term33) : term197 _3504 _3505.
Proof. exact (EQ_MP (@lem173346 _3504 _3505) (@lem173341 _3504 _3505 h1)). Qed.
Lemma lem173350 (_3504 : nat) (n : nat) (h1 : term33) : term197 _3504 n.
Proof. exact (@lem173349 _3504 n h1). Qed.
Lemma lem173353 (_3504 : nat) (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term160 _3504 n.
Proof. exact (@lem173350 _3504 n h1 (@lem173308 m n h2)). Qed.
Lemma lem173354 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term160 m n.
Proof. exact (@lem173353 m m n h1 h2). Qed.
Lemma lem173355 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term198 m n.
Proof. exact (fun h0 : term199 m n => @lem173354 m n h1 h2). Qed.
Lemma lem173357 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173358 (m : nat) (n : nat) : (term198 m n) = (term160 m n).
Proof. exact (@lem173357 (term160 m n)). Qed.
Lemma lem173359 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term160 m n.
Proof. exact (EQ_MP (@lem173358 m n) (@lem173355 m n h1 h2)). Qed.
Lemma lem173377 (q : Prop) (p : Prop) (r : Prop) : (term200 p q r) = (term200 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem173378 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term184 _3567 _3568 _3565 _3566) = (term201 _3567 _3568 _3565 _3566).
Proof. exact (@lem173377 (Peano.lt _3567 _3568) (term202 _3566 _3568) (term170 _3565 _3566)). Qed.
Lemma lem173392 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem173393 (_3565 : nat) (_3566 : nat) (_3568 : nat) : (term203 _3568 _3565 _3566) = (term204 _3565 _3566 _3568).
Proof. exact (@lem173392 (term170 _3565 _3566) (term202 _3566 _3568)). Qed.
Lemma lem173401 (_3567 : nat) (_3568 : nat) : (term205 _3567 _3568) = (term205 _3567 _3568).
Proof. exact (eq_refl (term205 _3567 _3568)). Qed.
Lemma lem173402 (_3567 : nat) (_3565 : nat) (_3566 : nat) (_3568 : nat) : (term201 _3567 _3568 _3565 _3566) = (term206 _3567 _3565 _3566 _3568).
Proof. exact (MK_COMB (@lem173401 _3567 _3568) (@lem173393 _3565 _3566 _3568)). Qed.
Lemma lem173413 (_3567 : nat) (_3565 : nat) (_3566 : nat) (_3568 : nat) : (term184 _3567 _3568 _3565 _3566) = (term206 _3567 _3565 _3566 _3568).
Proof. exact (TRANS (@lem173378 _3567 _3568 _3565 _3566) (@lem173402 _3567 _3565 _3566 _3568)). Qed.
Lemma lem173414 (_3565 : nat) (_3567 : nat) : (term207 _3565 _3567) = (term207 _3565 _3567).
Proof. exact (eq_refl (term207 _3565 _3567)). Qed.
Lemma lem173415 (_3567 : nat) (_3565 : nat) (_3566 : nat) (_3568 : nat) : (term186 _3567 _3568 _3565 _3566) = (term208 _3567 _3565 _3566 _3568).
Proof. exact (MK_COMB (@lem173414 _3565 _3567) (@lem173413 _3567 _3565 _3566 _3568)). Qed.
Lemma lem173419 (q : Prop) (p : Prop) (r : Prop) : (term200 p q r) = (term200 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem173420 (_3567 : nat) (_3565 : nat) (_3566 : nat) (_3568 : nat) : (term208 _3567 _3565 _3566 _3568) = (term209 _3567 _3565 _3566 _3568).
Proof. exact (@lem173419 (Peano.lt _3567 _3568) (term202 _3565 _3567) (term204 _3565 _3566 _3568)). Qed.
Lemma lem173434 (q : Prop) (p : Prop) (r : Prop) : (term200 p q r) = (term200 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem173435 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term210 _3567 _3565 _3566 _3568) = (term211 _3565 _3567 _3566 _3568).
Proof. exact (@lem173434 (term170 _3565 _3566) (term202 _3565 _3567) (term202 _3566 _3568)). Qed.
Lemma lem173455 (_3567 : nat) (_3568 : nat) : (term205 _3567 _3568) = (term205 _3567 _3568).
Proof. exact (eq_refl (term205 _3567 _3568)). Qed.
Lemma lem173456 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term209 _3567 _3565 _3566 _3568) = (term212 _3565 _3567 _3566 _3568).
Proof. exact (MK_COMB (@lem173455 _3567 _3568) (@lem173435 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173467 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term208 _3567 _3565 _3566 _3568) = (term212 _3565 _3567 _3566 _3568).
Proof. exact (TRANS (@lem173420 _3567 _3565 _3566 _3568) (@lem173456 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173468 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term186 _3567 _3568 _3565 _3566) = (term212 _3565 _3567 _3566 _3568).
Proof. exact (TRANS (@lem173415 _3567 _3565 _3566 _3568) (@lem173467 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173469 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem173470 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term213 _3567 _3568 _3565 _3566) = (term214 _3565 _3567 _3566 _3568).
Proof. exact (MK_COMB (@lem173469) (@lem173468 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173496 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem173497 (_3565 : nat) (_3566 : nat) (_3568 : nat) : (term203 _3568 _3565 _3566) = (term204 _3565 _3566 _3568).
Proof. exact (@lem173496 (term170 _3565 _3566) (term202 _3566 _3568)). Qed.
Lemma lem173505 (_3565 : nat) (_3567 : nat) : (term207 _3565 _3567) = (term207 _3565 _3567).
Proof. exact (eq_refl (term207 _3565 _3567)). Qed.
Lemma lem173506 (_3567 : nat) (_3565 : nat) (_3566 : nat) (_3568 : nat) : (term215 _3567 _3568 _3565 _3566) = (term210 _3567 _3565 _3566 _3568).
Proof. exact (MK_COMB (@lem173505 _3565 _3567) (@lem173497 _3565 _3566 _3568)). Qed.
Lemma lem173510 (q : Prop) (p : Prop) (r : Prop) : (term200 p q r) = (term200 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem173511 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term210 _3567 _3565 _3566 _3568) = (term211 _3565 _3567 _3566 _3568).
Proof. exact (@lem173510 (term170 _3565 _3566) (term202 _3565 _3567) (term202 _3566 _3568)). Qed.
Lemma lem173531 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term215 _3567 _3568 _3565 _3566) = (term211 _3565 _3567 _3566 _3568).
Proof. exact (TRANS (@lem173506 _3567 _3565 _3566 _3568) (@lem173511 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173532 (_3567 : nat) (_3568 : nat) : (term205 _3567 _3568) = (term205 _3567 _3568).
Proof. exact (eq_refl (term205 _3567 _3568)). Qed.
Lemma lem173533 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : (term216 _3567 _3568 _3565 _3566) = (term212 _3565 _3567 _3566 _3568).
Proof. exact (MK_COMB (@lem173532 _3567 _3568) (@lem173531 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173544 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : ((term186 _3567 _3568 _3565 _3566) = (term216 _3567 _3568 _3565 _3566)) = ((term212 _3565 _3567 _3566 _3568) = (term212 _3565 _3567 _3566 _3568)).
Proof. exact (MK_COMB (@lem173470 _3565 _3567 _3566 _3568) (@lem173533 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173546 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem173547 (x : Prop) : (x = x) = True.
Proof. exact (@lem173546 Prop x). Qed.
Lemma lem173548 (_3565 : nat) (_3567 : nat) (_3566 : nat) (_3568 : nat) : ((term212 _3565 _3567 _3566 _3568) = (term212 _3565 _3567 _3566 _3568)) = True.
Proof. exact (@lem173547 (term212 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173549 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : ((term186 _3567 _3568 _3565 _3566) = (term216 _3567 _3568 _3565 _3566)) = True.
Proof. exact (TRANS (@lem173544 _3565 _3567 _3566 _3568) (@lem173548 _3565 _3567 _3566 _3568)). Qed.
Lemma lem173550 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : True = ((term186 _3567 _3568 _3565 _3566) = (term216 _3567 _3568 _3565 _3566)).
Proof. exact (SYM (@lem173549 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173551 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term186 _3567 _3568 _3565 _3566) = (term216 _3567 _3568 _3565 _3566).
Proof. exact (EQ_MP (@lem173550 _3567 _3568 _3565 _3566) (@lem0)). Qed.
Lemma lem173552 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : term216 _3567 _3568 _3565 _3566.
Proof. exact (EQ_MP (@lem173551 _3567 _3568 _3565 _3566) (@lem173208 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173554 (b : Prop) (a : Prop) : (a \/ b) = (term196 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem173555 (_3565 : nat) (_3566 : nat) (_3567 : nat) (_3568 : nat) : (term216 _3567 _3568 _3565 _3566) = (term217 _3565 _3566 _3567 _3568).
Proof. exact (@lem173554 (term215 _3567 _3568 _3565 _3566) (Peano.lt _3567 _3568)). Qed.
Lemma lem173557 (a : Prop) (b : Prop) : (term218 a b) = (term219 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem173558 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term220 _3567 _3568 _3565 _3566) = (term221 _3567 _3568 _3565 _3566).
Proof. exact (@lem173557 (term202 _3565 _3567) (term203 _3568 _3565 _3566)). Qed.
Lemma lem173560 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem173561 (_3565 : nat) (_3567 : nat) : (term223 _3565 _3567) = (_3565 = _3567).
Proof. exact (@lem173560 (_3565 = _3567)). Qed.
Lemma lem173562 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem173563 (_3565 : nat) (_3567 : nat) : (term224 _3565 _3567) = (term225 _3565 _3567).
Proof. exact (MK_COMB (@lem173562) (@lem173561 _3565 _3567)). Qed.
Lemma lem173565 (a : Prop) (b : Prop) : (term218 a b) = (term219 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem173566 (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term226 _3568 _3565 _3566) = (term227 _3568 _3565 _3566).
Proof. exact (@lem173565 (term202 _3566 _3568) (term170 _3565 _3566)). Qed.
Lemma lem173568 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem173569 (_3566 : nat) (_3568 : nat) : (term223 _3566 _3568) = (_3566 = _3568).
Proof. exact (@lem173568 (_3566 = _3568)). Qed.
Lemma lem173570 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem173571 (_3566 : nat) (_3568 : nat) : (term224 _3566 _3568) = (term225 _3566 _3568).
Proof. exact (MK_COMB (@lem173570) (@lem173569 _3566 _3568)). Qed.
Lemma lem173573 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem173574 (_3565 : nat) (_3566 : nat) : (term228 _3565 _3566) = (Peano.lt _3565 _3566).
Proof. exact (@lem173573 (Peano.lt _3565 _3566)). Qed.
Lemma lem173575 (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term227 _3568 _3565 _3566) = (term229 _3568 _3565 _3566).
Proof. exact (MK_COMB (@lem173571 _3566 _3568) (@lem173574 _3565 _3566)). Qed.
Lemma lem173576 (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term226 _3568 _3565 _3566) = (term229 _3568 _3565 _3566).
Proof. exact (TRANS (@lem173566 _3568 _3565 _3566) (@lem173575 _3568 _3565 _3566)). Qed.
Lemma lem173577 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term221 _3567 _3568 _3565 _3566) = (term230 _3567 _3568 _3565 _3566).
Proof. exact (MK_COMB (@lem173563 _3565 _3567) (@lem173576 _3568 _3565 _3566)). Qed.
Lemma lem173578 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term220 _3567 _3568 _3565 _3566) = (term230 _3567 _3568 _3565 _3566).
Proof. exact (TRANS (@lem173558 _3567 _3568 _3565 _3566) (@lem173577 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173579 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem173580 (_3567 : nat) (_3568 : nat) (_3565 : nat) (_3566 : nat) : (term231 _3567 _3568 _3565 _3566) = (term232 _3567 _3568 _3565 _3566).
Proof. exact (MK_COMB (@lem173579) (@lem173578 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173581 (_3567 : nat) (_3568 : nat) : (Peano.lt _3567 _3568) = (Peano.lt _3567 _3568).
Proof. exact (eq_refl (Peano.lt _3567 _3568)). Qed.
Lemma lem173582 (_3565 : nat) (_3566 : nat) (_3567 : nat) (_3568 : nat) : (term217 _3565 _3566 _3567 _3568) = (term233 _3565 _3566 _3567 _3568).
Proof. exact (MK_COMB (@lem173580 _3567 _3568 _3565 _3566) (@lem173581 _3567 _3568)). Qed.
Lemma lem173583 (_3565 : nat) (_3566 : nat) (_3567 : nat) (_3568 : nat) : (term216 _3567 _3568 _3565 _3566) = (term233 _3565 _3566 _3567 _3568).
Proof. exact (TRANS (@lem173555 _3565 _3566 _3567 _3568) (@lem173582 _3565 _3566 _3567 _3568)). Qed.
Lemma lem173585 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term234 m n.
Proof. exact (conj (@lem173301 n) (@lem173359 m n h1 h2)). Qed.
Lemma lem173586 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term235 m n.
Proof. exact (conj (@lem173293 m n h2) (@lem173585 m n h1 h2)). Qed.
Lemma lem173588 (_3565 : nat) (_3566 : nat) (_3567 : nat) (_3568 : nat) : term233 _3565 _3566 _3567 _3568.
Proof. exact (EQ_MP (@lem173583 _3565 _3566 _3567 _3568) (@lem173552 _3567 _3568 _3565 _3566)). Qed.
Lemma lem173589 (m : nat) (n : nat) : term236 m n.
Proof. exact (@lem173588 (Nat.modulo m n) n m n). Qed.
Lemma lem173592 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : Peano.lt m n.
Proof. exact (@lem173589 m n (@lem173586 m n h1 h2)). Qed.
Lemma lem173593 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term237 m n.
Proof. exact (fun h0 : term170 m n => @lem173592 m n h1 h2). Qed.
Lemma lem173595 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173596 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (@lem173595 (Peano.lt m n)). Qed.
Lemma lem173597 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem173596 m n) (@lem173593 m n h1 h2)). Qed.
Lemma lem173600 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem173602 (m : nat) (n : nat) : (term170 m n) = (term238 m n).
Proof. exact (@lem173600 (Peano.lt m n)). Qed.
Lemma lem173605 (m : nat) (n : nat) (h1 : term71 m n) : term238 m n.
Proof. exact (EQ_MP (@lem173602 m n) (@lem172871 m n h1)). Qed.
Lemma lem173608 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : False.
Proof. exact (@lem173605 m n h2 (@lem173597 m n h1 h2)). Qed.
Lemma lem173609 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : term239.
Proof. exact (fun h0 : ~ False => @lem173608 m n h1 h2). Qed.
Lemma lem173611 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173612 : term239 = False.
Proof. exact (@lem173611 False). Qed.
Lemma lem173613 (m : nat) (n : nat) (h1 : term33) (h2 : term71 m n) : False.
Proof. exact (EQ_MP (@lem173612) (@lem173609 m n h1 h2)). Qed.
Lemma lem173731 (_3519 : nat) (h1 : term10) : (term22 _3519) = _3519.
Proof. exact (EQ_MP (@lem172763 _3519) (@lem172762 _3519 h1)). Qed.
Lemma lem173732 (m : nat) (h1 : term10) : (term22 m) = m.
Proof. exact (@lem173731 m h1). Qed.
Lemma lem173733 (m : nat) (h1 : term10) : term240 m.
Proof. exact (fun h0 : term176 m => @lem173732 m h1). Qed.
Lemma lem173735 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173736 (m : nat) : (term240 m) = ((term22 m) = m).
Proof. exact (@lem173735 ((term22 m) = m)). Qed.
Lemma lem173737 (m : nat) (h1 : term10) : (term22 m) = m.
Proof. exact (EQ_MP (@lem173736 m) (@lem173733 m h1)). Qed.
Lemma lem173740 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem173742 (m : nat) : (term176 m) = (term241 m).
Proof. exact (@lem173740 ((term22 m) = m)). Qed.
Lemma lem173745 (m : nat) (n : nat) (h1 : term68 m n) (h2 : n = (NUMERAL 0)) : term241 m.
Proof. exact (EQ_MP (@lem173742 m) (@lem173142 m n h1 h2)). Qed.
Lemma lem173748 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (@lem173745 m n h2 h3 (@lem173737 m h1)). Qed.
Lemma lem173749 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : term239.
Proof. exact (fun h0 : ~ False => @lem173748 m n h1 h2 h3). Qed.
Lemma lem173751 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173752 : term239 = False.
Proof. exact (@lem173751 False). Qed.
Lemma lem173871 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (h1). Qed.
Lemma lem173872 (m : nat) (n : nat) (h1 : Peano.lt m n) : term237 m n.
Proof. exact (fun h0 : term170 m n => @lem173871 m n h1). Qed.
Lemma lem173874 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173875 (m : nat) (n : nat) : (term237 m n) = (Peano.lt m n).
Proof. exact (@lem173874 (Peano.lt m n)). Qed.
Lemma lem173876 (m : nat) (n : nat) (h1 : Peano.lt m n) : Peano.lt m n.
Proof. exact (EQ_MP (@lem173875 m n) (@lem173872 m n h1)). Qed.
Lemma lem173882 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem173883 (_3528 : nat) (_3529 : nat) : (term153 _3529 _3528) = (term242 _3528 _3529).
Proof. exact (@lem173882 ((Nat.modulo _3528 _3529) = _3528) (term170 _3528 _3529)). Qed.
Lemma lem173891 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem173892 (_3528 : nat) (_3529 : nat) : (term243 _3529 _3528) = (term244 _3528 _3529).
Proof. exact (MK_COMB (@lem173891) (@lem173883 _3528 _3529)). Qed.
Lemma lem173900 (_3528 : nat) (_3529 : nat) : (term242 _3528 _3529) = (term242 _3528 _3529).
Proof. exact (eq_refl (term242 _3528 _3529)). Qed.
Lemma lem173901 (_3528 : nat) (_3529 : nat) : ((term153 _3529 _3528) = (term242 _3528 _3529)) = ((term242 _3528 _3529) = (term242 _3528 _3529)).
Proof. exact (MK_COMB (@lem173892 _3528 _3529) (@lem173900 _3528 _3529)). Qed.
Lemma lem173903 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem173904 (x : Prop) : (x = x) = True.
Proof. exact (@lem173903 Prop x). Qed.
Lemma lem173905 (_3528 : nat) (_3529 : nat) : ((term242 _3528 _3529) = (term242 _3528 _3529)) = True.
Proof. exact (@lem173904 (term242 _3528 _3529)). Qed.
Lemma lem173906 (_3528 : nat) (_3529 : nat) : ((term153 _3529 _3528) = (term242 _3528 _3529)) = True.
Proof. exact (TRANS (@lem173901 _3528 _3529) (@lem173905 _3528 _3529)). Qed.
Lemma lem173907 (_3528 : nat) (_3529 : nat) : True = ((term153 _3529 _3528) = (term242 _3528 _3529)).
Proof. exact (SYM (@lem173906 _3528 _3529)). Qed.
Lemma lem173908 (_3528 : nat) (_3529 : nat) : (term153 _3529 _3528) = (term242 _3528 _3529).
Proof. exact (EQ_MP (@lem173907 _3528 _3529) (@lem0)). Qed.
Lemma lem173909 (_3528 : nat) (_3529 : nat) (h1 : term28) : term242 _3528 _3529.
Proof. exact (EQ_MP (@lem173908 _3528 _3529) (@lem172949 _3529 _3528 h1)). Qed.
Lemma lem173911 (b : Prop) (a : Prop) : (a \/ b) = (term196 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem173912 (_3529 : nat) (_3528 : nat) : (term242 _3528 _3529) = (term245 _3529 _3528).
Proof. exact (@lem173911 (term170 _3528 _3529) ((Nat.modulo _3528 _3529) = _3528)). Qed.
Lemma lem173914 (a : Prop) : (term222 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem173915 (_3528 : nat) (_3529 : nat) : (term228 _3528 _3529) = (Peano.lt _3528 _3529).
Proof. exact (@lem173914 (Peano.lt _3528 _3529)). Qed.
Lemma lem173916 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem173917 (_3528 : nat) (_3529 : nat) : (term246 _3528 _3529) = (term247 _3528 _3529).
Proof. exact (MK_COMB (@lem173916) (@lem173915 _3528 _3529)). Qed.
Lemma lem173918 (_3529 : nat) (_3528 : nat) : ((Nat.modulo _3528 _3529) = _3528) = ((Nat.modulo _3528 _3529) = _3528).
Proof. exact (eq_refl ((Nat.modulo _3528 _3529) = _3528)). Qed.
Lemma lem173919 (_3529 : nat) (_3528 : nat) : (term245 _3529 _3528) = (term24 _3529 _3528).
Proof. exact (MK_COMB (@lem173917 _3528 _3529) (@lem173918 _3529 _3528)). Qed.
Lemma lem173920 (_3529 : nat) (_3528 : nat) : (term242 _3528 _3529) = (term24 _3529 _3528).
Proof. exact (TRANS (@lem173912 _3529 _3528) (@lem173919 _3529 _3528)). Qed.
Lemma lem173923 (_3529 : nat) (_3528 : nat) (h1 : term28) : term24 _3529 _3528.
Proof. exact (EQ_MP (@lem173920 _3529 _3528) (@lem173909 _3528 _3529 h1)). Qed.
Lemma lem173924 (n : nat) (m : nat) (h1 : term28) : term24 n m.
Proof. exact (@lem173923 n m h1). Qed.
Lemma lem173927 (m : nat) (n : nat) (h1 : term28) (h2 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (@lem173924 n m h1 (@lem173876 m n h2)). Qed.
Lemma lem173928 (m : nat) (n : nat) (h1 : term28) (h2 : Peano.lt m n) : term187 n m.
Proof. exact (fun h0 : term172 n m => @lem173927 m n h1 h2). Qed.
Lemma lem173930 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173931 (n : nat) (m : nat) : (term187 n m) = ((Nat.modulo m n) = m).
Proof. exact (@lem173930 ((Nat.modulo m n) = m)). Qed.
Lemma lem173932 (m : nat) (n : nat) (h1 : term28) (h2 : Peano.lt m n) : (Nat.modulo m n) = m.
Proof. exact (EQ_MP (@lem173931 n m) (@lem173928 m n h1 h2)). Qed.
Lemma lem173935 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem173937 (n : nat) (m : nat) : (term172 n m) = (term248 n m).
Proof. exact (@lem173935 ((Nat.modulo m n) = m)). Qed.
Lemma lem173940 (m : nat) (n : nat) (h1 : term68 m n) : term248 n m.
Proof. exact (EQ_MP (@lem173937 n m) (@lem172989 m n h1)). Qed.
Lemma lem173943 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : False.
Proof. exact (@lem173940 m n h2 (@lem173932 m n h1 h3)). Qed.
Lemma lem173944 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : term239.
Proof. exact (fun h0 : ~ False => @lem173943 m n h1 h2 h3). Qed.
Lemma lem173946 (p : Prop) : (term188 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem173947 : term239 = False.
Proof. exact (@lem173946 False). Qed.
Lemma lem173948 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem173947) (@lem173944 m n h1 h2 h3)). Qed.
Lemma lem173949 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem173752) (@lem173749 m n h1 h2 h3)). Qed.
Lemma lem173950 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt m n => @lem173948 m n h1 h2 h3) (fun h4 : False => @lem172991 m n h3)). Qed.
Lemma lem173951 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem173950 m n h1 h2 h3) (@lem172991 m n h3)). Qed.
Lemma lem173952 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem173949 m n h1 h2 h3) (fun h4 : False => @lem172931 n h3)). Qed.
Lemma lem173953 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem173952 m n h1 h2 h3) (@lem172931 n h3)). Qed.
Lemma lem173954 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt m n => @lem173951 m n h1 h2 h3) (fun h4 : False => @lem172716 m n h3)). Qed.
Lemma lem173955 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem173954 m n h1 h2 h3) (@lem172716 m n h3)). Qed.
Lemma lem173956 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem173953 m n h1 h2 h3) (fun h4 : False => @lem172581 n h3)). Qed.
Lemma lem173957 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem173956 m n h1 h2 h3) (@lem172581 n h3)). Qed.
Lemma lem173958 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : (Peano.lt m n) = False.
Proof. exact (prop_ext (fun h4 : Peano.lt m n => @lem173955 m n h1 h2 h3) (fun h4 : False => @lem172716 m n h3)). Qed.
Lemma lem173959 (m : nat) (n : nat) (h1 : term28) (h2 : term68 m n) (h3 : Peano.lt m n) : False.
Proof. exact (EQ_MP (@lem173958 m n h1 h2 h3) (@lem172716 m n h3)). Qed.
Lemma lem173960 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : (n = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h4 : n = (NUMERAL 0) => @lem173957 m n h1 h2 h3) (fun h4 : False => @lem172581 n h3)). Qed.
Lemma lem173961 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem173960 m n h1 h2 h3) (@lem172581 n h3)). Qed.
Lemma lem173962 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem173961 m n h1 h2 h3) (fun h4 : False => @lem172495 h1)). Qed.
Lemma lem173963 (m : nat) (n : nat) (h1 : term10) (h2 : term68 m n) (h3 : n = (NUMERAL 0)) : False.
Proof. exact (EQ_MP (@lem173962 m n h1 h2 h3) (@lem172495 h1)). Qed.
Lemma lem173964 (m : nat) (n : nat) (h1 : term28) (h2 : term10) (h3 : term68 m n) : False.
Proof. exact (or_elim (@lem172304 m n h3) (fun h0 : n = (NUMERAL 0) => @lem173963 m n h2 h3 h0) (fun h0 : Peano.lt m n => @lem173959 m n h1 h3 h0)). Qed.
Lemma lem173965 (m : nat) (n : nat) (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term75 m n) : False.
Proof. exact (or_elim (@lem172287 m n h4) (fun h0 : term71 m n => @lem173613 m n h1 h0) (fun h0 : term68 m n => @lem173964 m n h2 h3 h0)). Qed.
Lemma lem173966 (m : nat) (n : nat) (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term75 m n) : (term75 m n) = False.
Proof. exact (prop_ext (fun h5 : term75 m n => @lem173965 m n h1 h2 h3 h4) (fun h5 : False => @lem172287 m n h4)). Qed.
Lemma lem173967 (m : nat) (n : nat) (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term75 m n) : False.
Proof. exact (EQ_MP (@lem173966 m n h1 h2 h3 h4) (@lem172287 m n h4)). Qed.
Lemma lem173968 (m : nat) (n : nat) (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term75 m n) : term10 = False.
Proof. exact (prop_ext (fun h5 : term10 => @lem173967 m n h1 h2 h3 h4) (fun h5 : False => @lem172223 h3)). Qed.
Lemma lem173969 (m : nat) (n : nat) (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term75 m n) : False.
Proof. exact (EQ_MP (@lem173968 m n h1 h2 h3 h4) (@lem172223 h3)). Qed.
Lemma lem173970 (m : nat) (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term85 m) : False.
Proof. exact (ex_elim (@lem171975 m h4) (fun n : nat => fun h0 : term84 m n => @lem173969 m n h1 h2 h3 h0)). Qed.
Lemma lem173971 (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term3) : False.
Proof. exact (ex_elim (@lem171443 h4) (fun m : nat => fun h0 : term90 m => @lem173970 m h1 h2 h3 h0)). Qed.
Lemma lem173972 (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term3) : term10 = False.
Proof. exact (prop_ext (fun h5 : term10 => @lem173971 h1 h2 h3 h4) (fun h5 : False => @lem171974 h3)). Qed.
Lemma lem173973 (h1 : term33) (h2 : term28) (h3 : term10) (h4 : term3) : False.
Proof. exact (EQ_MP (@lem173972 h1 h2 h3 h4) (@lem171974 h3)). Qed.
Lemma lem173974 (h1 : term33) (h2 : term28) (h3 : term3) : term8.
Proof. exact (fun h0 : term10 => @lem173973 h1 h2 h0 h3). Qed.
Lemma lem173975 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem173976 (h1 : term33) (h2 : term28) (h3 : term3) : term9.
Proof. exact (EQ_MP (@lem173975) (@lem173974 h1 h2 h3)). Qed.
Lemma lem173977 (h1 : term33) (h2 : term3) : term13.
Proof. exact (fun h0 : term28 => @lem173976 h1 h0 h2). Qed.
Lemma lem173978 (h1 : term3) : term16.
Proof. exact (fun h0 : term33 => @lem173977 h0 h1). Qed.
Lemma lem173979 (h1 : term3) : term19.
Proof. exact (fun h0 : term61 => @lem173978 h1). Qed.
Lemma lem173980 : term21.
Proof. exact (fun h0 : term3 => @lem173979 h0). Qed.
Lemma lem173981 : term4.
Proof. exact (EQ_MP (@lem171070) (@lem173980)). Qed.
Lemma lem173983 : term4.
Proof. exact (@lem170703 (@lem173981)). Qed.
Lemma lem173984 (h1 : term3) : term18.
Proof. exact (@lem173983 (@lem170688 h1)). Qed.
Lemma lem173985 (h1 : term3) : term15.
Proof. exact (@lem173984 h1 (@lem99082)). Qed.
Lemma lem173986 (h1 : term3) : term12.
Proof. exact (@lem173985 h1 (@lem157261)). Qed.
Lemma lem173987 (h1 : term3) : term8.
Proof. exact (@lem173986 h1 (@lem170673)). Qed.
Lemma lem173988 (h1 : term3) : False.
Proof. exact (@lem173987 h1 (@lem159121)). Qed.
Lemma lem173989 (h1 : term3) : term3 = False.
Proof. exact (prop_ext (fun h2 : term3 => @lem173988 h1) (fun h2 : False => @lem170688 h1)). Qed.
Lemma lem173990 (h1 : term3) : False.
Proof. exact (EQ_MP (@lem173989 h1) (@lem170688 h1)). Qed.
Lemma lem173991 : term2.
Proof. exact (fun h0 : term3 => @lem173990 h0). Qed.
Lemma lem173992 : term1.
Proof. exact (EQ_MP (@lem170687) (@lem173991)). Qed.
