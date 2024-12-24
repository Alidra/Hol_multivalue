Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import thm996236_term_abbrevs.
Require Import DISJ_ACI_spec.
Require Import MULT_CLAUSES_spec.
Require Import thm0_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm16474_spec.
Require Import thm17045_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm21021_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21385_spec.
Require Import thm21386_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm69_spec.
Require Import thm75543_spec.
Lemma lem994730 (p : Prop) : p = (term0 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem994731 (n : nat) (m : nat) : (term1 n m) = (term2 n m).
Proof. exact (@lem994730 (term1 n m)). Qed.
Lemma lem994732 (n : nat) (m : nat) : (term2 n m) = (term1 n m).
Proof. exact (SYM (@lem994731 n m)). Qed.
Lemma lem994733 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem994736 (n : nat) (m : nat) (h1 : term4 n m) : term4 n m.
Proof. exact (h1). Qed.
Lemma lem994737 (n : nat) (m : nat) : term5 n m.
Proof. exact (fun h0 : term4 n m => @lem994736 n m h0). Qed.
Lemma lem994738 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (h1). Qed.
Lemma lem994739 (n : nat) (m : nat) (h1 : term4 n m) : term4 n m.
Proof. exact (h1). Qed.
Lemma lem994740 (n : nat) (m : nat) (h1 : term4 n m) (h2 : term5 n m) : term4 n m.
Proof. exact (@lem994738 n m h2 (@lem994739 n m h1)). Qed.
Lemma lem994741 (n : nat) (m : nat) (h1 : term4 n m) : term6 n m.
Proof. exact (fun h0 : term5 n m => @lem994740 n m h1 h0). Qed.
Lemma lem994742 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (h1). Qed.
Lemma lem994743 (n : nat) (m : nat) (h1 : term4 n m) (h2 : term5 n m) : term4 n m.
Proof. exact (@lem994741 n m h1 (@lem994742 n m h2)). Qed.
Lemma lem994744 (n : nat) (m : nat) (h1 : term5 n m) : term5 n m.
Proof. exact (fun h0 : term4 n m => @lem994743 n m h0 h1). Qed.
Lemma lem994745 (n : nat) (m : nat) : term7 n m.
Proof. exact (fun h0 : term5 n m => @lem994744 n m h0). Qed.
Lemma lem994748 (n : nat) (m : nat) : term5 n m.
Proof. exact (@lem994745 n m (@lem994737 n m)). Qed.
Lemma lem994806 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem994807 : term8 = term9.
Proof. exact (@lem994806 term10). Qed.
Lemma lem994812 : term11 = term11.
Proof. exact (eq_refl term11). Qed.
Lemma lem994813 : term12 = term13.
Proof. exact (MK_COMB (@lem994812) (@lem994807)). Qed.
Lemma lem994816 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem994817 (n : nat) (m : nat) : (term4 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem994816 n m) (@lem994813)). Qed.
Lemma lem994820 (m : nat) : (term16 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem994817 n m)). Qed.
Lemma lem994821 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994822 (m : nat) : (term18 m) = (term19 m).
Proof. exact (MK_COMB (@lem994821) (@lem994820 m)). Qed.
Lemma lem994827 : term20 = term21.
Proof. exact (fun_ext (fun m : nat => @lem994822 m)). Qed.
Lemma lem994828 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994837 : term22 = term23.
Proof. exact (MK_COMB (@lem994828) (@lem994827)). Qed.
Lemma lem994838 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem994839 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem994838 n)). Qed.
Lemma lem994840 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994841 : term10 = term10.
Proof. exact (MK_COMB (@lem994840) (@lem994839)). Qed.
Lemma lem994842 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem994843 : term9 = term9.
Proof. exact (MK_COMB (@lem994842) (@lem994841)). Qed.
Lemma lem994844 (m : nat) (n : nat) : ((term25 m n) = (term26 m n)) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl ((term25 m n) = (term26 m n))). Qed.
Lemma lem994845 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem994844 m n)). Qed.
Lemma lem994846 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994847 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem994846) (@lem994845 m)). Qed.
Lemma lem994848 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem994847 m)). Qed.
Lemma lem994849 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994850 : term30 = term30.
Proof. exact (MK_COMB (@lem994849) (@lem994848)). Qed.
Lemma lem994851 (m : nat) (n : nat) : ((term31 m n) = (term32 m n)) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl ((term31 m n) = (term32 m n))). Qed.
Lemma lem994852 (m : nat) : (term33 m) = (term33 m).
Proof. exact (fun_ext (fun n : nat => @lem994851 m n)). Qed.
Lemma lem994853 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994854 (m : nat) : (term34 m) = (term34 m).
Proof. exact (MK_COMB (@lem994853) (@lem994852 m)). Qed.
Lemma lem994855 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem994854 m)). Qed.
Lemma lem994856 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994857 : term36 = term36.
Proof. exact (MK_COMB (@lem994856) (@lem994855)). Qed.
Lemma lem994858 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994859 : term37 = term37.
Proof. exact (MK_COMB (@lem994858) (@lem994857)). Qed.
Lemma lem994860 : term38 = term38.
Proof. exact (MK_COMB (@lem994859) (@lem994850)). Qed.
Lemma lem994861 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem994862 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem994861 m)). Qed.
Lemma lem994863 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994864 : term41 = term41.
Proof. exact (MK_COMB (@lem994863) (@lem994862)). Qed.
Lemma lem994865 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994866 : term42 = term42.
Proof. exact (MK_COMB (@lem994865) (@lem994864)). Qed.
Lemma lem994867 : term43 = term43.
Proof. exact (MK_COMB (@lem994866) (@lem994860)). Qed.
Lemma lem994868 (n : nat) : ((term44 n) = n) = ((term44 n) = n).
Proof. exact (eq_refl ((term44 n) = n)). Qed.
Lemma lem994869 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem994868 n)). Qed.
Lemma lem994870 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994871 : term46 = term46.
Proof. exact (MK_COMB (@lem994870) (@lem994869)). Qed.
Lemma lem994872 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994873 : term47 = term47.
Proof. exact (MK_COMB (@lem994872) (@lem994871)). Qed.
Lemma lem994874 : term48 = term48.
Proof. exact (MK_COMB (@lem994873) (@lem994867)). Qed.
Lemma lem994875 (m : nat) : ((term49 m) = (NUMERAL 0)) = ((term49 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term49 m) = (NUMERAL 0))). Qed.
Lemma lem994876 : term50 = term50.
Proof. exact (fun_ext (fun m : nat => @lem994875 m)). Qed.
Lemma lem994877 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994878 : term51 = term51.
Proof. exact (MK_COMB (@lem994877) (@lem994876)). Qed.
Lemma lem994879 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994880 : term52 = term52.
Proof. exact (MK_COMB (@lem994879) (@lem994878)). Qed.
Lemma lem994881 : term53 = term53.
Proof. exact (MK_COMB (@lem994880) (@lem994874)). Qed.
Lemma lem994882 (n : nat) : ((term54 n) = (NUMERAL 0)) = ((term54 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term54 n) = (NUMERAL 0))). Qed.
Lemma lem994883 : term55 = term55.
Proof. exact (fun_ext (fun n : nat => @lem994882 n)). Qed.
Lemma lem994884 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994885 : term56 = term56.
Proof. exact (MK_COMB (@lem994884) (@lem994883)). Qed.
Lemma lem994886 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem994887 : term57 = term57.
Proof. exact (MK_COMB (@lem994886) (@lem994885)). Qed.
Lemma lem994888 : term58 = term58.
Proof. exact (MK_COMB (@lem994887) (@lem994881)). Qed.
Lemma lem994889 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem994890 : term11 = term11.
Proof. exact (MK_COMB (@lem994889) (@lem994888)). Qed.
Lemma lem994891 : term13 = term13.
Proof. exact (MK_COMB (@lem994890) (@lem994843)). Qed.
Lemma lem994900 (n : nat) (m : nat) : (term14 n m) = (term14 n m).
Proof. exact (eq_refl (term14 n m)). Qed.
Lemma lem994901 (n : nat) (m : nat) : (term15 n m) = (term15 n m).
Proof. exact (MK_COMB (@lem994900 n m) (@lem994891)). Qed.
Lemma lem994902 (m : nat) : (term17 m) = (term17 m).
Proof. exact (fun_ext (fun n : nat => @lem994901 n m)). Qed.
Lemma lem994903 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994904 (m : nat) : (term19 m) = (term19 m).
Proof. exact (MK_COMB (@lem994903) (@lem994902 m)). Qed.
Lemma lem994905 : term21 = term21.
Proof. exact (fun_ext (fun m : nat => @lem994904 m)). Qed.
Lemma lem994906 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem994907 : term23 = term23.
Proof. exact (MK_COMB (@lem994906) (@lem994905)). Qed.
Lemma lem994992 : term22 = term23.
Proof. exact (TRANS (@lem994837) (@lem994907)). Qed.
Lemma lem994993 : term23 = term22.
Proof. exact (SYM (@lem994992)). Qed.
Lemma lem994994 (n : nat) (m : nat) (h1 : term3 n m) : term3 n m.
Proof. exact (h1). Qed.
Lemma lem994995 (h1 : term58) : term58.
Proof. exact (h1). Qed.
Lemma lem994996 (h1 : term10) : term10.
Proof. exact (h1). Qed.
Lemma lem995007 (n : nat) (m : nat) : (term3 n m) = (term59 n m).
Proof. exact (@lem17045 ((term60 n) = n) ((term61 m) = m)). Qed.
Lemma lem995009 (n : nat) : ((term54 n) = (NUMERAL 0)) = ((term54 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term54 n) = (NUMERAL 0))). Qed.
Lemma lem995010 : term55 = term55.
Proof. exact (fun_ext (fun n : nat => @lem995009 n)). Qed.
Lemma lem995011 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995012 : term56 = term56.
Proof. exact (MK_COMB (@lem995011) (@lem995010)). Qed.
Lemma lem995013 (m : nat) : ((term49 m) = (NUMERAL 0)) = ((term49 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term49 m) = (NUMERAL 0))). Qed.
Lemma lem995014 : term50 = term50.
Proof. exact (fun_ext (fun m : nat => @lem995013 m)). Qed.
Lemma lem995015 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995016 : term51 = term51.
Proof. exact (MK_COMB (@lem995015) (@lem995014)). Qed.
Lemma lem995017 (n : nat) : ((term44 n) = n) = ((term44 n) = n).
Proof. exact (eq_refl ((term44 n) = n)). Qed.
Lemma lem995018 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem995017 n)). Qed.
Lemma lem995019 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995020 : term46 = term46.
Proof. exact (MK_COMB (@lem995019) (@lem995018)). Qed.
Lemma lem995021 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem995022 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem995021 m)). Qed.
Lemma lem995023 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995024 : term41 = term41.
Proof. exact (MK_COMB (@lem995023) (@lem995022)). Qed.
Lemma lem995025 (m : nat) (n : nat) : ((term31 m n) = (term32 m n)) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl ((term31 m n) = (term32 m n))). Qed.
Lemma lem995026 (m : nat) : (term33 m) = (term33 m).
Proof. exact (fun_ext (fun n : nat => @lem995025 m n)). Qed.
Lemma lem995027 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995028 (m : nat) : (term34 m) = (term34 m).
Proof. exact (MK_COMB (@lem995027) (@lem995026 m)). Qed.
Lemma lem995029 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem995028 m)). Qed.
Lemma lem995030 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995031 : term36 = term36.
Proof. exact (MK_COMB (@lem995030) (@lem995029)). Qed.
Lemma lem995032 (m : nat) (n : nat) : ((term25 m n) = (term26 m n)) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl ((term25 m n) = (term26 m n))). Qed.
Lemma lem995033 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem995032 m n)). Qed.
Lemma lem995034 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995035 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem995034) (@lem995033 m)). Qed.
Lemma lem995036 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem995035 m)). Qed.
Lemma lem995037 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995038 : term30 = term30.
Proof. exact (MK_COMB (@lem995037) (@lem995036)). Qed.
Lemma lem995039 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995040 : term37 = term37.
Proof. exact (MK_COMB (@lem995039) (@lem995031)). Qed.
Lemma lem995041 : term38 = term38.
Proof. exact (MK_COMB (@lem995040) (@lem995038)). Qed.
Lemma lem995042 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995043 : term42 = term42.
Proof. exact (MK_COMB (@lem995042) (@lem995024)). Qed.
Lemma lem995044 : term43 = term43.
Proof. exact (MK_COMB (@lem995043) (@lem995041)). Qed.
Lemma lem995045 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995046 : term47 = term47.
Proof. exact (MK_COMB (@lem995045) (@lem995020)). Qed.
Lemma lem995047 : term48 = term48.
Proof. exact (MK_COMB (@lem995046) (@lem995044)). Qed.
Lemma lem995048 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995049 : term52 = term52.
Proof. exact (MK_COMB (@lem995048) (@lem995016)). Qed.
Lemma lem995050 : term53 = term53.
Proof. exact (MK_COMB (@lem995049) (@lem995047)). Qed.
Lemma lem995051 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995052 : term57 = term57.
Proof. exact (MK_COMB (@lem995051) (@lem995012)). Qed.
Lemma lem995089 : term58 = term58.
Proof. exact (MK_COMB (@lem995052) (@lem995050)). Qed.
Lemma lem995090 (h1 : term58) : term58.
Proof. exact (EQ_MP (@lem995089) (@lem994995 h1)). Qed.
Lemma lem995091 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem995092 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem995091 n)). Qed.
Lemma lem995093 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995102 : term10 = term10.
Proof. exact (MK_COMB (@lem995093) (@lem995092)). Qed.
Lemma lem995103 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem995102) (@lem994996 h1)). Qed.
Lemma lem995133 (n : nat) (m : nat) (h1 : term3 n m) : term59 n m.
Proof. exact (EQ_MP (@lem995007 n m) (@lem994994 n m h1)). Qed.
Lemma lem995152 (m : nat) (n : nat) : ((term25 m n) = (term26 m n)) = ((term25 m n) = (term26 m n)).
Proof. exact (eq_refl ((term25 m n) = (term26 m n))). Qed.
Lemma lem995153 (m : nat) : (term27 m) = (term27 m).
Proof. exact (fun_ext (fun n : nat => @lem995152 m n)). Qed.
Lemma lem995154 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995155 (m : nat) : (term28 m) = (term28 m).
Proof. exact (MK_COMB (@lem995154) (@lem995153 m)). Qed.
Lemma lem995156 : term29 = term29.
Proof. exact (fun_ext (fun m : nat => @lem995155 m)). Qed.
Lemma lem995157 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995158 : term30 = term30.
Proof. exact (MK_COMB (@lem995157) (@lem995156)). Qed.
Lemma lem995177 (m : nat) (n : nat) : ((term31 m n) = (term32 m n)) = ((term31 m n) = (term32 m n)).
Proof. exact (eq_refl ((term31 m n) = (term32 m n))). Qed.
Lemma lem995178 (m : nat) : (term33 m) = (term33 m).
Proof. exact (fun_ext (fun n : nat => @lem995177 m n)). Qed.
Lemma lem995179 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995180 (m : nat) : (term34 m) = (term34 m).
Proof. exact (MK_COMB (@lem995179) (@lem995178 m)). Qed.
Lemma lem995181 : term35 = term35.
Proof. exact (fun_ext (fun m : nat => @lem995180 m)). Qed.
Lemma lem995182 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995183 : term36 = term36.
Proof. exact (MK_COMB (@lem995182) (@lem995181)). Qed.
Lemma lem995184 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995185 : term37 = term37.
Proof. exact (MK_COMB (@lem995184) (@lem995183)). Qed.
Lemma lem995186 : term38 = term38.
Proof. exact (MK_COMB (@lem995185) (@lem995158)). Qed.
Lemma lem995199 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem995200 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem995199 m)). Qed.
Lemma lem995201 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995202 : term41 = term41.
Proof. exact (MK_COMB (@lem995201) (@lem995200)). Qed.
Lemma lem995203 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995204 : term42 = term42.
Proof. exact (MK_COMB (@lem995203) (@lem995202)). Qed.
Lemma lem995205 : term43 = term43.
Proof. exact (MK_COMB (@lem995204) (@lem995186)). Qed.
Lemma lem995218 (n : nat) : ((term44 n) = n) = ((term44 n) = n).
Proof. exact (eq_refl ((term44 n) = n)). Qed.
Lemma lem995219 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem995218 n)). Qed.
Lemma lem995220 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995221 : term46 = term46.
Proof. exact (MK_COMB (@lem995220) (@lem995219)). Qed.
Lemma lem995222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995223 : term47 = term47.
Proof. exact (MK_COMB (@lem995222) (@lem995221)). Qed.
Lemma lem995224 : term48 = term48.
Proof. exact (MK_COMB (@lem995223) (@lem995205)). Qed.
Lemma lem995237 (m : nat) : ((term49 m) = (NUMERAL 0)) = ((term49 m) = (NUMERAL 0)).
Proof. exact (eq_refl ((term49 m) = (NUMERAL 0))). Qed.
Lemma lem995238 : term50 = term50.
Proof. exact (fun_ext (fun m : nat => @lem995237 m)). Qed.
Lemma lem995239 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995240 : term51 = term51.
Proof. exact (MK_COMB (@lem995239) (@lem995238)). Qed.
Lemma lem995241 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995242 : term52 = term52.
Proof. exact (MK_COMB (@lem995241) (@lem995240)). Qed.
Lemma lem995243 : term53 = term53.
Proof. exact (MK_COMB (@lem995242) (@lem995224)). Qed.
Lemma lem995256 (n : nat) : ((term54 n) = (NUMERAL 0)) = ((term54 n) = (NUMERAL 0)).
Proof. exact (eq_refl ((term54 n) = (NUMERAL 0))). Qed.
Lemma lem995257 : term55 = term55.
Proof. exact (fun_ext (fun n : nat => @lem995256 n)). Qed.
Lemma lem995258 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995259 : term56 = term56.
Proof. exact (MK_COMB (@lem995258) (@lem995257)). Qed.
Lemma lem995260 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995261 : term57 = term57.
Proof. exact (MK_COMB (@lem995260) (@lem995259)). Qed.
Lemma lem995262 : term58 = term58.
Proof. exact (MK_COMB (@lem995261) (@lem995243)). Qed.
Lemma lem995263 (h1 : term58) : term58.
Proof. exact (EQ_MP (@lem995262) (@lem995090 h1)). Qed.
Lemma lem995270 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem995271 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem995270 n)). Qed.
Lemma lem995272 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995273 : term10 = term10.
Proof. exact (MK_COMB (@lem995272) (@lem995271)). Qed.
Lemma lem995274 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem995273) (@lem995103 h1)). Qed.
Lemma lem995275 (h1 : term58) : term53.
Proof. exact (proj2 (@lem995263 h1)). Qed.
Lemma lem995277 (h1 : term58) : term48.
Proof. exact (proj2 (@lem995275 h1)). Qed.
Lemma lem995279 (h1 : term58) : term43.
Proof. exact (proj2 (@lem995277 h1)). Qed.
Lemma lem995280 (h1 : term58) : term46.
Proof. exact (proj1 (@lem995277 h1)). Qed.
Lemma lem995282 (h1 : term58) : term41.
Proof. exact (proj1 (@lem995279 h1)). Qed.
Lemma lem995288 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem995289 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem995288 n)). Qed.
Lemma lem995290 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995292 : term10 = term10.
Proof. exact (MK_COMB (@lem995290) (@lem995289)). Qed.
Lemma lem995293 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem995292) (@lem995274 h1)). Qed.
Lemma lem995309 (n : nat) : ((term44 n) = n) = ((term44 n) = n).
Proof. exact (eq_refl ((term44 n) = n)). Qed.
Lemma lem995310 : term45 = term45.
Proof. exact (fun_ext (fun n : nat => @lem995309 n)). Qed.
Lemma lem995311 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995313 : term46 = term46.
Proof. exact (MK_COMB (@lem995311) (@lem995310)). Qed.
Lemma lem995314 (h1 : term58) : term46.
Proof. exact (EQ_MP (@lem995313) (@lem995280 h1)). Qed.
Lemma lem995345 (n : nat) (h1 : term62 n) : term62 n.
Proof. exact (h1). Qed.
Lemma lem995347 (n : nat) : ((NUMERAL n) = n) = ((NUMERAL n) = n).
Proof. exact (eq_refl ((NUMERAL n) = n)). Qed.
Lemma lem995348 : term24 = term24.
Proof. exact (fun_ext (fun n : nat => @lem995347 n)). Qed.
Lemma lem995349 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995351 : term10 = term10.
Proof. exact (MK_COMB (@lem995349) (@lem995348)). Qed.
Lemma lem995352 (h1 : term10) : term10.
Proof. exact (EQ_MP (@lem995351) (@lem995274 h1)). Qed.
Lemma lem995375 (m : nat) : ((term39 m) = m) = ((term39 m) = m).
Proof. exact (eq_refl ((term39 m) = m)). Qed.
Lemma lem995376 : term40 = term40.
Proof. exact (fun_ext (fun m : nat => @lem995375 m)). Qed.
Lemma lem995377 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem995379 : term41 = term41.
Proof. exact (MK_COMB (@lem995377) (@lem995376)). Qed.
Lemma lem995380 (h1 : term58) : term41.
Proof. exact (EQ_MP (@lem995379) (@lem995282 h1)). Qed.
Lemma lem995404 (m : nat) (h1 : term63 m) : term63 m.
Proof. exact (h1). Qed.
Lemma lem995405 (_16134 : nat) (h1 : term10) : term64 _16134.
Proof. exact (@lem995293 h1 _16134). Qed.
Lemma lem995406 (_16134 : nat) : (term64 _16134) = ((NUMERAL _16134) = _16134).
Proof. exact (eq_refl (term64 _16134)). Qed.
Lemma lem995414 (_16137 : nat) (h1 : term58) : term65 _16137.
Proof. exact (@lem995314 h1 _16137). Qed.
Lemma lem995415 (_16137 : nat) : (term65 _16137) = ((term44 _16137) = _16137).
Proof. exact (eq_refl (term65 _16137)). Qed.
Lemma lem995432 (_16143 : nat) (h1 : term10) : term64 _16143.
Proof. exact (@lem995352 h1 _16143). Qed.
Lemma lem995433 (_16143 : nat) : (term64 _16143) = ((NUMERAL _16143) = _16143).
Proof. exact (eq_refl (term64 _16143)). Qed.
Lemma lem995444 (_16147 : nat) (h1 : term58) : term66 _16147.
Proof. exact (@lem995380 h1 _16147). Qed.
Lemma lem995445 (_16147 : nat) : (term66 _16147) = ((term39 _16147) = _16147).
Proof. exact (eq_refl (term66 _16147)). Qed.
Lemma lem995474 (n : nat) (h1 : term62 n) : term62 n.
Proof. exact (h1). Qed.
Lemma lem995490 (m : nat) (h1 : term63 m) : term63 m.
Proof. exact (h1). Qed.
Lemma lem995522 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem995523 (_16160 : nat) (_16162 : nat) (h1 : _16160 = _16162) : _16160 = _16162.
Proof. exact (h1). Qed.
Lemma lem995524 (_16161 : nat) (_16163 : nat) (h1 : _16161 = _16163) : _16161 = _16163.
Proof. exact (h1). Qed.
Lemma lem995525 (_16160 : nat) (_16162 : nat) (h1 : _16160 = _16162) : (Nat.mul _16160) = (Nat.mul _16162).
Proof. exact (MK_COMB (@lem995522) (@lem995523 _16160 _16162 h1)). Qed.
Lemma lem995526 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) (h1 : _16160 = _16162) (h2 : _16161 = _16163) : (Nat.mul _16160 _16161) = (Nat.mul _16162 _16163).
Proof. exact (MK_COMB (@lem995525 _16160 _16162 h1) (@lem995524 _16161 _16163 h2)). Qed.
Lemma lem995527 (_16161 : nat) (_16163 : nat) (_16160 : nat) (_16162 : nat) (h1 : _16160 = _16162) : term67 _16160 _16161 _16162 _16163.
Proof. exact (fun h0 : _16161 = _16163 => @lem995526 _16160 _16162 _16161 _16163 h1 h0). Qed.
Lemma lem995529 (a : Prop) (b : Prop) : (a -> b) = (term68 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem995530 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : (term67 _16160 _16161 _16162 _16163) = (term69 _16160 _16161 _16162 _16163).
Proof. exact (@lem995529 (_16161 = _16163) ((Nat.mul _16160 _16161) = (Nat.mul _16162 _16163))). Qed.
Lemma lem995531 (_16161 : nat) (_16163 : nat) (_16160 : nat) (_16162 : nat) (h1 : _16160 = _16162) : term69 _16160 _16161 _16162 _16163.
Proof. exact (EQ_MP (@lem995530 _16160 _16161 _16162 _16163) (@lem995527 _16161 _16163 _16160 _16162 h1)). Qed.
Lemma lem995532 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : term70 _16160 _16161 _16162 _16163.
Proof. exact (fun h0 : _16160 = _16162 => @lem995531 _16161 _16163 _16160 _16162 h0). Qed.
Lemma lem995534 (a : Prop) (b : Prop) : (a -> b) = (term68 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem995535 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : (term70 _16160 _16161 _16162 _16163) = (term71 _16160 _16161 _16162 _16163).
Proof. exact (@lem995534 (_16160 = _16162) (term69 _16160 _16161 _16162 _16163)). Qed.
Lemma lem995536 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : term71 _16160 _16161 _16162 _16163.
Proof. exact (EQ_MP (@lem995535 _16160 _16161 _16162 _16163) (@lem995532 _16160 _16161 _16162 _16163)). Qed.
Lemma lem995546 (x : nat) (y : nat) (z : nat) : term72 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem995548 (_16134 : nat) (h1 : term10) : (NUMERAL _16134) = _16134.
Proof. exact (EQ_MP (@lem995406 _16134) (@lem995405 _16134 h1)). Qed.
Lemma lem995549 (h1 : term10) : term73 = (BIT1 0).
Proof. exact (@lem995548 (BIT1 0) h1). Qed.
Lemma lem995550 (h1 : term10) : term74.
Proof. exact (fun h0 : term75 => @lem995549 h1). Qed.
Lemma lem995552 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995553 : term74 = (term73 = (BIT1 0)).
Proof. exact (@lem995552 (term73 = (BIT1 0))). Qed.
Lemma lem995554 (h1 : term10) : term73 = (BIT1 0).
Proof. exact (EQ_MP (@lem995553) (@lem995550 h1)). Qed.
Lemma lem995556 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem995557 (n : nat) : n = n.
Proof. exact (@lem995556 n). Qed.
Lemma lem995558 (n : nat) : term77 n.
Proof. exact (fun h0 : term78 n => @lem995557 n). Qed.
Lemma lem995560 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995561 (n : nat) : (term77 n) = (n = n).
Proof. exact (@lem995560 (n = n)). Qed.
Lemma lem995562 (n : nat) : n = n.
Proof. exact (EQ_MP (@lem995561 n) (@lem995558 n)). Qed.
Lemma lem995580 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem995581 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term69 _16160 _16161 _16162 _16163) = (term79 _16160 _16162 _16161 _16163).
Proof. exact (@lem995580 ((Nat.mul _16160 _16161) = (Nat.mul _16162 _16163)) (term80 _16161 _16163)). Qed.
Lemma lem995591 (_16160 : nat) (_16162 : nat) : (term81 _16160 _16162) = (term81 _16160 _16162).
Proof. exact (eq_refl (term81 _16160 _16162)). Qed.
Lemma lem995592 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term71 _16160 _16161 _16162 _16163) = (term82 _16160 _16162 _16161 _16163).
Proof. exact (MK_COMB (@lem995591 _16160 _16162) (@lem995581 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995596 (q : Prop) (p : Prop) (r : Prop) : (term83 p q r) = (term83 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem995597 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term82 _16160 _16162 _16161 _16163) = (term84 _16160 _16162 _16161 _16163).
Proof. exact (@lem995596 ((Nat.mul _16160 _16161) = (Nat.mul _16162 _16163)) (term80 _16160 _16162) (term80 _16161 _16163)). Qed.
Lemma lem995619 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term71 _16160 _16161 _16162 _16163) = (term84 _16160 _16162 _16161 _16163).
Proof. exact (TRANS (@lem995592 _16160 _16162 _16161 _16163) (@lem995597 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995620 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem995621 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term85 _16160 _16161 _16162 _16163) = (term86 _16160 _16162 _16161 _16163).
Proof. exact (MK_COMB (@lem995620) (@lem995619 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995643 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term84 _16160 _16162 _16161 _16163) = (term84 _16160 _16162 _16161 _16163).
Proof. exact (eq_refl (term84 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995644 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : ((term71 _16160 _16161 _16162 _16163) = (term84 _16160 _16162 _16161 _16163)) = ((term84 _16160 _16162 _16161 _16163) = (term84 _16160 _16162 _16161 _16163)).
Proof. exact (MK_COMB (@lem995621 _16160 _16162 _16161 _16163) (@lem995643 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995646 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem995647 (x : Prop) : (x = x) = True.
Proof. exact (@lem995646 Prop x). Qed.
Lemma lem995648 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : ((term84 _16160 _16162 _16161 _16163) = (term84 _16160 _16162 _16161 _16163)) = True.
Proof. exact (@lem995647 (term84 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995649 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : ((term71 _16160 _16161 _16162 _16163) = (term84 _16160 _16162 _16161 _16163)) = True.
Proof. exact (TRANS (@lem995644 _16160 _16162 _16161 _16163) (@lem995648 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995650 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : True = ((term71 _16160 _16161 _16162 _16163) = (term84 _16160 _16162 _16161 _16163)).
Proof. exact (SYM (@lem995649 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995651 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term71 _16160 _16161 _16162 _16163) = (term84 _16160 _16162 _16161 _16163).
Proof. exact (EQ_MP (@lem995650 _16160 _16162 _16161 _16163) (@lem0)). Qed.
Lemma lem995652 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : term84 _16160 _16162 _16161 _16163.
Proof. exact (EQ_MP (@lem995651 _16160 _16162 _16161 _16163) (@lem995536 _16160 _16161 _16162 _16163)). Qed.
Lemma lem995654 (b : Prop) (a : Prop) : (a \/ b) = (term87 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem995655 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : (term84 _16160 _16162 _16161 _16163) = (term88 _16160 _16161 _16162 _16163).
Proof. exact (@lem995654 (term89 _16160 _16162 _16161 _16163) ((Nat.mul _16160 _16161) = (Nat.mul _16162 _16163))). Qed.
Lemma lem995657 (a : Prop) (b : Prop) : (term90 a b) = (term91 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem995658 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term92 _16160 _16162 _16161 _16163) = (term93 _16160 _16162 _16161 _16163).
Proof. exact (@lem995657 (term80 _16160 _16162) (term80 _16161 _16163)). Qed.
Lemma lem995660 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem995661 (_16160 : nat) (_16162 : nat) : (term95 _16160 _16162) = (_16160 = _16162).
Proof. exact (@lem995660 (_16160 = _16162)). Qed.
Lemma lem995662 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995663 (_16160 : nat) (_16162 : nat) : (term96 _16160 _16162) = (term97 _16160 _16162).
Proof. exact (MK_COMB (@lem995662) (@lem995661 _16160 _16162)). Qed.
Lemma lem995665 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem995666 (_16161 : nat) (_16163 : nat) : (term95 _16161 _16163) = (_16161 = _16163).
Proof. exact (@lem995665 (_16161 = _16163)). Qed.
Lemma lem995667 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term93 _16160 _16162 _16161 _16163) = (term98 _16160 _16162 _16161 _16163).
Proof. exact (MK_COMB (@lem995663 _16160 _16162) (@lem995666 _16161 _16163)). Qed.
Lemma lem995668 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term92 _16160 _16162 _16161 _16163) = (term98 _16160 _16162 _16161 _16163).
Proof. exact (TRANS (@lem995658 _16160 _16162 _16161 _16163) (@lem995667 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995669 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem995670 (_16160 : nat) (_16162 : nat) (_16161 : nat) (_16163 : nat) : (term99 _16160 _16162 _16161 _16163) = (term100 _16160 _16162 _16161 _16163).
Proof. exact (MK_COMB (@lem995669) (@lem995668 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995671 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : ((Nat.mul _16160 _16161) = (Nat.mul _16162 _16163)) = ((Nat.mul _16160 _16161) = (Nat.mul _16162 _16163)).
Proof. exact (eq_refl ((Nat.mul _16160 _16161) = (Nat.mul _16162 _16163))). Qed.
Lemma lem995672 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : (term88 _16160 _16161 _16162 _16163) = (term101 _16160 _16161 _16162 _16163).
Proof. exact (MK_COMB (@lem995670 _16160 _16162 _16161 _16163) (@lem995671 _16160 _16161 _16162 _16163)). Qed.
Lemma lem995673 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : (term84 _16160 _16162 _16161 _16163) = (term101 _16160 _16161 _16162 _16163).
Proof. exact (TRANS (@lem995655 _16160 _16161 _16162 _16163) (@lem995672 _16160 _16161 _16162 _16163)). Qed.
Lemma lem995675 (n : nat) (h1 : term10) : term102 n.
Proof. exact (conj (@lem995554 h1) (@lem995562 n)). Qed.
Lemma lem995677 (_16160 : nat) (_16161 : nat) (_16162 : nat) (_16163 : nat) : term101 _16160 _16161 _16162 _16163.
Proof. exact (EQ_MP (@lem995673 _16160 _16161 _16162 _16163) (@lem995652 _16160 _16162 _16161 _16163)). Qed.
Lemma lem995678 (n : nat) : term103 n.
Proof. exact (@lem995677 term73 n (BIT1 0) n). Qed.
Lemma lem995681 (n : nat) (h1 : term10) : (term44 n) = (term60 n).
Proof. exact (@lem995678 n (@lem995675 n h1)). Qed.
Lemma lem995682 (n : nat) (h1 : term10) : term104 n.
Proof. exact (fun h0 : term105 n => @lem995681 n h1). Qed.
Lemma lem995684 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995685 (n : nat) : (term104 n) = ((term44 n) = (term60 n)).
Proof. exact (@lem995684 ((term44 n) = (term60 n))). Qed.
Lemma lem995686 (n : nat) (h1 : term10) : (term44 n) = (term60 n).
Proof. exact (EQ_MP (@lem995685 n) (@lem995682 n h1)). Qed.
Lemma lem995688 (_16137 : nat) (h1 : term58) : (term44 _16137) = _16137.
Proof. exact (EQ_MP (@lem995415 _16137) (@lem995414 _16137 h1)). Qed.
Lemma lem995689 (n : nat) (h1 : term58) : (term44 n) = n.
Proof. exact (@lem995688 n h1). Qed.
Lemma lem995690 (n : nat) (h1 : term58) : term106 n.
Proof. exact (fun h0 : term107 n => @lem995689 n h1). Qed.
Lemma lem995692 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995693 (n : nat) : (term106 n) = ((term44 n) = n).
Proof. exact (@lem995692 ((term44 n) = n)). Qed.
Lemma lem995694 (n : nat) (h1 : term58) : (term44 n) = n.
Proof. exact (EQ_MP (@lem995693 n) (@lem995690 n h1)). Qed.
Lemma lem995712 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem995713 (y : nat) (x : nat) (z : nat) : (term108 x y z) = (term109 y x z).
Proof. exact (@lem995712 (y = z) (term80 x z)). Qed.
Lemma lem995723 (x : nat) (y : nat) : (term81 x y) = (term81 x y).
Proof. exact (eq_refl (term81 x y)). Qed.
Lemma lem995724 (y : nat) (x : nat) (z : nat) : (term72 x y z) = (term110 y x z).
Proof. exact (MK_COMB (@lem995723 x y) (@lem995713 y x z)). Qed.
Lemma lem995728 (q : Prop) (p : Prop) (r : Prop) : (term83 p q r) = (term83 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem995729 (y : nat) (x : nat) (z : nat) : (term110 y x z) = (term111 y x z).
Proof. exact (@lem995728 (y = z) (term80 x y) (term80 x z)). Qed.
Lemma lem995751 (y : nat) (x : nat) (z : nat) : (term72 x y z) = (term111 y x z).
Proof. exact (TRANS (@lem995724 y x z) (@lem995729 y x z)). Qed.
Lemma lem995752 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem995753 (y : nat) (x : nat) (z : nat) : (term112 x y z) = (term113 y x z).
Proof. exact (MK_COMB (@lem995752) (@lem995751 y x z)). Qed.
Lemma lem995775 (y : nat) (x : nat) (z : nat) : (term111 y x z) = (term111 y x z).
Proof. exact (eq_refl (term111 y x z)). Qed.
Lemma lem995776 (y : nat) (x : nat) (z : nat) : ((term72 x y z) = (term111 y x z)) = ((term111 y x z) = (term111 y x z)).
Proof. exact (MK_COMB (@lem995753 y x z) (@lem995775 y x z)). Qed.
Lemma lem995778 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem995779 (x : Prop) : (x = x) = True.
Proof. exact (@lem995778 Prop x). Qed.
Lemma lem995780 (y : nat) (x : nat) (z : nat) : ((term111 y x z) = (term111 y x z)) = True.
Proof. exact (@lem995779 (term111 y x z)). Qed.
Lemma lem995781 (y : nat) (x : nat) (z : nat) : ((term72 x y z) = (term111 y x z)) = True.
Proof. exact (TRANS (@lem995776 y x z) (@lem995780 y x z)). Qed.
Lemma lem995782 (y : nat) (x : nat) (z : nat) : True = ((term72 x y z) = (term111 y x z)).
Proof. exact (SYM (@lem995781 y x z)). Qed.
Lemma lem995783 (y : nat) (x : nat) (z : nat) : (term72 x y z) = (term111 y x z).
Proof. exact (EQ_MP (@lem995782 y x z) (@lem0)). Qed.
Lemma lem995784 (y : nat) (x : nat) (z : nat) : term111 y x z.
Proof. exact (EQ_MP (@lem995783 y x z) (@lem995546 x y z)). Qed.
Lemma lem995786 (b : Prop) (a : Prop) : (a \/ b) = (term87 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem995787 (x : nat) (y : nat) (z : nat) : (term111 y x z) = (term114 x y z).
Proof. exact (@lem995786 (term115 y x z) (y = z)). Qed.
Lemma lem995789 (a : Prop) (b : Prop) : (term90 a b) = (term91 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem995790 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term117 y x z).
Proof. exact (@lem995789 (term80 x y) (term80 x z)). Qed.
Lemma lem995792 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem995793 (x : nat) (y : nat) : (term95 x y) = (x = y).
Proof. exact (@lem995792 (x = y)). Qed.
Lemma lem995794 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem995795 (x : nat) (y : nat) : (term96 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem995794) (@lem995793 x y)). Qed.
Lemma lem995797 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem995798 (x : nat) (z : nat) : (term95 x z) = (x = z).
Proof. exact (@lem995797 (x = z)). Qed.
Lemma lem995799 (y : nat) (x : nat) (z : nat) : (term117 y x z) = (term118 y x z).
Proof. exact (MK_COMB (@lem995795 x y) (@lem995798 x z)). Qed.
Lemma lem995800 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term118 y x z).
Proof. exact (TRANS (@lem995790 y x z) (@lem995799 y x z)). Qed.
Lemma lem995801 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem995802 (y : nat) (x : nat) (z : nat) : (term119 y x z) = (term120 y x z).
Proof. exact (MK_COMB (@lem995801) (@lem995800 y x z)). Qed.
Lemma lem995803 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem995804 (x : nat) (y : nat) (z : nat) : (term114 x y z) = (term121 x y z).
Proof. exact (MK_COMB (@lem995802 y x z) (@lem995803 y z)). Qed.
Lemma lem995805 (x : nat) (y : nat) (z : nat) : (term111 y x z) = (term121 x y z).
Proof. exact (TRANS (@lem995787 x y z) (@lem995804 x y z)). Qed.
Lemma lem995807 (n : nat) (h1 : term10) (h2 : term58) : term122 n.
Proof. exact (conj (@lem995686 n h1) (@lem995694 n h2)). Qed.
Lemma lem995809 (x : nat) (y : nat) (z : nat) : term121 x y z.
Proof. exact (EQ_MP (@lem995805 x y z) (@lem995784 y x z)). Qed.
Lemma lem995810 (n : nat) : term123 n.
Proof. exact (@lem995809 (term44 n) (term60 n) n). Qed.
Lemma lem995813 (n : nat) (h1 : term10) (h2 : term58) : (term60 n) = n.
Proof. exact (@lem995810 n (@lem995807 n h1 h2)). Qed.
Lemma lem995814 (n : nat) (h1 : term10) (h2 : term58) : term124 n.
Proof. exact (fun h0 : term62 n => @lem995813 n h1 h2). Qed.
Lemma lem995816 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995817 (n : nat) : (term124 n) = ((term60 n) = n).
Proof. exact (@lem995816 ((term60 n) = n)). Qed.
Lemma lem995818 (n : nat) (h1 : term10) (h2 : term58) : (term60 n) = n.
Proof. exact (EQ_MP (@lem995817 n) (@lem995814 n h1 h2)). Qed.
Lemma lem995821 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem995823 (n : nat) : (term62 n) = (term125 n).
Proof. exact (@lem995821 ((term60 n) = n)). Qed.
Lemma lem995826 (n : nat) (h1 : term62 n) : term125 n.
Proof. exact (EQ_MP (@lem995823 n) (@lem995474 n h1)). Qed.
Lemma lem995829 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : False.
Proof. exact (@lem995826 n h2 (@lem995818 n h1 h3)). Qed.
Lemma lem995830 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : term126.
Proof. exact (fun h0 : ~ False => @lem995829 n h1 h2 h3). Qed.
Lemma lem995832 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995833 : term126 = False.
Proof. exact (@lem995832 False). Qed.
Lemma lem995834 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem995833) (@lem995830 n h1 h2 h3)). Qed.
Lemma lem995866 : Nat.mul = Nat.mul.
Proof. exact (eq_refl Nat.mul). Qed.
Lemma lem995867 (_16174 : nat) (_16176 : nat) (h1 : _16174 = _16176) : _16174 = _16176.
Proof. exact (h1). Qed.
Lemma lem995868 (_16175 : nat) (_16177 : nat) (h1 : _16175 = _16177) : _16175 = _16177.
Proof. exact (h1). Qed.
Lemma lem995869 (_16174 : nat) (_16176 : nat) (h1 : _16174 = _16176) : (Nat.mul _16174) = (Nat.mul _16176).
Proof. exact (MK_COMB (@lem995866) (@lem995867 _16174 _16176 h1)). Qed.
Lemma lem995870 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) (h1 : _16174 = _16176) (h2 : _16175 = _16177) : (Nat.mul _16174 _16175) = (Nat.mul _16176 _16177).
Proof. exact (MK_COMB (@lem995869 _16174 _16176 h1) (@lem995868 _16175 _16177 h2)). Qed.
Lemma lem995871 (_16175 : nat) (_16177 : nat) (_16174 : nat) (_16176 : nat) (h1 : _16174 = _16176) : term67 _16174 _16175 _16176 _16177.
Proof. exact (fun h0 : _16175 = _16177 => @lem995870 _16174 _16176 _16175 _16177 h1 h0). Qed.
Lemma lem995873 (a : Prop) (b : Prop) : (a -> b) = (term68 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem995874 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : (term67 _16174 _16175 _16176 _16177) = (term69 _16174 _16175 _16176 _16177).
Proof. exact (@lem995873 (_16175 = _16177) ((Nat.mul _16174 _16175) = (Nat.mul _16176 _16177))). Qed.
Lemma lem995875 (_16175 : nat) (_16177 : nat) (_16174 : nat) (_16176 : nat) (h1 : _16174 = _16176) : term69 _16174 _16175 _16176 _16177.
Proof. exact (EQ_MP (@lem995874 _16174 _16175 _16176 _16177) (@lem995871 _16175 _16177 _16174 _16176 h1)). Qed.
Lemma lem995876 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : term70 _16174 _16175 _16176 _16177.
Proof. exact (fun h0 : _16174 = _16176 => @lem995875 _16175 _16177 _16174 _16176 h0). Qed.
Lemma lem995878 (a : Prop) (b : Prop) : (a -> b) = (term68 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem995879 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : (term70 _16174 _16175 _16176 _16177) = (term71 _16174 _16175 _16176 _16177).
Proof. exact (@lem995878 (_16174 = _16176) (term69 _16174 _16175 _16176 _16177)). Qed.
Lemma lem995880 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : term71 _16174 _16175 _16176 _16177.
Proof. exact (EQ_MP (@lem995879 _16174 _16175 _16176 _16177) (@lem995876 _16174 _16175 _16176 _16177)). Qed.
Lemma lem995890 (x : nat) (y : nat) (z : nat) : term72 x y z.
Proof. exact (@lem21385 nat x y z). Qed.
Lemma lem995892 (x : nat) : x = x.
Proof. exact (@lem21386 nat x). Qed.
Lemma lem995893 (m : nat) : m = m.
Proof. exact (@lem995892 m). Qed.
Lemma lem995894 (m : nat) : term77 m.
Proof. exact (fun h0 : term78 m => @lem995893 m). Qed.
Lemma lem995896 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995897 (m : nat) : (term77 m) = (m = m).
Proof. exact (@lem995896 (m = m)). Qed.
Lemma lem995898 (m : nat) : m = m.
Proof. exact (EQ_MP (@lem995897 m) (@lem995894 m)). Qed.
Lemma lem995900 (_16143 : nat) (h1 : term10) : (NUMERAL _16143) = _16143.
Proof. exact (EQ_MP (@lem995433 _16143) (@lem995432 _16143 h1)). Qed.
Lemma lem995901 (h1 : term10) : term73 = (BIT1 0).
Proof. exact (@lem995900 (BIT1 0) h1). Qed.
Lemma lem995902 (h1 : term10) : term74.
Proof. exact (fun h0 : term75 => @lem995901 h1). Qed.
Lemma lem995904 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem995905 : term74 = (term73 = (BIT1 0)).
Proof. exact (@lem995904 (term73 = (BIT1 0))). Qed.
Lemma lem995906 (h1 : term10) : term73 = (BIT1 0).
Proof. exact (EQ_MP (@lem995905) (@lem995902 h1)). Qed.
Lemma lem995924 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem995925 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term69 _16174 _16175 _16176 _16177) = (term79 _16174 _16176 _16175 _16177).
Proof. exact (@lem995924 ((Nat.mul _16174 _16175) = (Nat.mul _16176 _16177)) (term80 _16175 _16177)). Qed.
Lemma lem995935 (_16174 : nat) (_16176 : nat) : (term81 _16174 _16176) = (term81 _16174 _16176).
Proof. exact (eq_refl (term81 _16174 _16176)). Qed.
Lemma lem995936 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term71 _16174 _16175 _16176 _16177) = (term82 _16174 _16176 _16175 _16177).
Proof. exact (MK_COMB (@lem995935 _16174 _16176) (@lem995925 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995940 (q : Prop) (p : Prop) (r : Prop) : (term83 p q r) = (term83 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem995941 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term82 _16174 _16176 _16175 _16177) = (term84 _16174 _16176 _16175 _16177).
Proof. exact (@lem995940 ((Nat.mul _16174 _16175) = (Nat.mul _16176 _16177)) (term80 _16174 _16176) (term80 _16175 _16177)). Qed.
Lemma lem995963 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term71 _16174 _16175 _16176 _16177) = (term84 _16174 _16176 _16175 _16177).
Proof. exact (TRANS (@lem995936 _16174 _16176 _16175 _16177) (@lem995941 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem995965 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term85 _16174 _16175 _16176 _16177) = (term86 _16174 _16176 _16175 _16177).
Proof. exact (MK_COMB (@lem995964) (@lem995963 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995987 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term84 _16174 _16176 _16175 _16177) = (term84 _16174 _16176 _16175 _16177).
Proof. exact (eq_refl (term84 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995988 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : ((term71 _16174 _16175 _16176 _16177) = (term84 _16174 _16176 _16175 _16177)) = ((term84 _16174 _16176 _16175 _16177) = (term84 _16174 _16176 _16175 _16177)).
Proof. exact (MK_COMB (@lem995965 _16174 _16176 _16175 _16177) (@lem995987 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995990 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem995991 (x : Prop) : (x = x) = True.
Proof. exact (@lem995990 Prop x). Qed.
Lemma lem995992 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : ((term84 _16174 _16176 _16175 _16177) = (term84 _16174 _16176 _16175 _16177)) = True.
Proof. exact (@lem995991 (term84 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995993 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : ((term71 _16174 _16175 _16176 _16177) = (term84 _16174 _16176 _16175 _16177)) = True.
Proof. exact (TRANS (@lem995988 _16174 _16176 _16175 _16177) (@lem995992 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995994 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : True = ((term71 _16174 _16175 _16176 _16177) = (term84 _16174 _16176 _16175 _16177)).
Proof. exact (SYM (@lem995993 _16174 _16176 _16175 _16177)). Qed.
Lemma lem995995 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term71 _16174 _16175 _16176 _16177) = (term84 _16174 _16176 _16175 _16177).
Proof. exact (EQ_MP (@lem995994 _16174 _16176 _16175 _16177) (@lem0)). Qed.
Lemma lem995996 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : term84 _16174 _16176 _16175 _16177.
Proof. exact (EQ_MP (@lem995995 _16174 _16176 _16175 _16177) (@lem995880 _16174 _16175 _16176 _16177)). Qed.
Lemma lem995998 (b : Prop) (a : Prop) : (a \/ b) = (term87 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem995999 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : (term84 _16174 _16176 _16175 _16177) = (term88 _16174 _16175 _16176 _16177).
Proof. exact (@lem995998 (term89 _16174 _16176 _16175 _16177) ((Nat.mul _16174 _16175) = (Nat.mul _16176 _16177))). Qed.
Lemma lem996001 (a : Prop) (b : Prop) : (term90 a b) = (term91 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem996002 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term92 _16174 _16176 _16175 _16177) = (term93 _16174 _16176 _16175 _16177).
Proof. exact (@lem996001 (term80 _16174 _16176) (term80 _16175 _16177)). Qed.
Lemma lem996004 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem996005 (_16174 : nat) (_16176 : nat) : (term95 _16174 _16176) = (_16174 = _16176).
Proof. exact (@lem996004 (_16174 = _16176)). Qed.
Lemma lem996006 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem996007 (_16174 : nat) (_16176 : nat) : (term96 _16174 _16176) = (term97 _16174 _16176).
Proof. exact (MK_COMB (@lem996006) (@lem996005 _16174 _16176)). Qed.
Lemma lem996009 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem996010 (_16175 : nat) (_16177 : nat) : (term95 _16175 _16177) = (_16175 = _16177).
Proof. exact (@lem996009 (_16175 = _16177)). Qed.
Lemma lem996011 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term93 _16174 _16176 _16175 _16177) = (term98 _16174 _16176 _16175 _16177).
Proof. exact (MK_COMB (@lem996007 _16174 _16176) (@lem996010 _16175 _16177)). Qed.
Lemma lem996012 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term92 _16174 _16176 _16175 _16177) = (term98 _16174 _16176 _16175 _16177).
Proof. exact (TRANS (@lem996002 _16174 _16176 _16175 _16177) (@lem996011 _16174 _16176 _16175 _16177)). Qed.
Lemma lem996013 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem996014 (_16174 : nat) (_16176 : nat) (_16175 : nat) (_16177 : nat) : (term99 _16174 _16176 _16175 _16177) = (term100 _16174 _16176 _16175 _16177).
Proof. exact (MK_COMB (@lem996013) (@lem996012 _16174 _16176 _16175 _16177)). Qed.
Lemma lem996015 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : ((Nat.mul _16174 _16175) = (Nat.mul _16176 _16177)) = ((Nat.mul _16174 _16175) = (Nat.mul _16176 _16177)).
Proof. exact (eq_refl ((Nat.mul _16174 _16175) = (Nat.mul _16176 _16177))). Qed.
Lemma lem996016 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : (term88 _16174 _16175 _16176 _16177) = (term101 _16174 _16175 _16176 _16177).
Proof. exact (MK_COMB (@lem996014 _16174 _16176 _16175 _16177) (@lem996015 _16174 _16175 _16176 _16177)). Qed.
Lemma lem996017 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : (term84 _16174 _16176 _16175 _16177) = (term101 _16174 _16175 _16176 _16177).
Proof. exact (TRANS (@lem995999 _16174 _16175 _16176 _16177) (@lem996016 _16174 _16175 _16176 _16177)). Qed.
Lemma lem996019 (m : nat) (h1 : term10) : term127 m.
Proof. exact (conj (@lem995898 m) (@lem995906 h1)). Qed.
Lemma lem996021 (_16174 : nat) (_16175 : nat) (_16176 : nat) (_16177 : nat) : term101 _16174 _16175 _16176 _16177.
Proof. exact (EQ_MP (@lem996017 _16174 _16175 _16176 _16177) (@lem995996 _16174 _16176 _16175 _16177)). Qed.
Lemma lem996022 (m : nat) : term128 m.
Proof. exact (@lem996021 m term73 m (BIT1 0)). Qed.
Lemma lem996025 (m : nat) (h1 : term10) : (term39 m) = (term61 m).
Proof. exact (@lem996022 m (@lem996019 m h1)). Qed.
Lemma lem996026 (m : nat) (h1 : term10) : term129 m.
Proof. exact (fun h0 : term130 m => @lem996025 m h1). Qed.
Lemma lem996028 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem996029 (m : nat) : (term129 m) = ((term39 m) = (term61 m)).
Proof. exact (@lem996028 ((term39 m) = (term61 m))). Qed.
Lemma lem996030 (m : nat) (h1 : term10) : (term39 m) = (term61 m).
Proof. exact (EQ_MP (@lem996029 m) (@lem996026 m h1)). Qed.
Lemma lem996032 (_16147 : nat) (h1 : term58) : (term39 _16147) = _16147.
Proof. exact (EQ_MP (@lem995445 _16147) (@lem995444 _16147 h1)). Qed.
Lemma lem996033 (m : nat) (h1 : term58) : (term39 m) = m.
Proof. exact (@lem996032 m h1). Qed.
Lemma lem996034 (m : nat) (h1 : term58) : term131 m.
Proof. exact (fun h0 : term132 m => @lem996033 m h1). Qed.
Lemma lem996036 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem996037 (m : nat) : (term131 m) = ((term39 m) = m).
Proof. exact (@lem996036 ((term39 m) = m)). Qed.
Lemma lem996038 (m : nat) (h1 : term58) : (term39 m) = m.
Proof. exact (EQ_MP (@lem996037 m) (@lem996034 m h1)). Qed.
Lemma lem996056 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem996057 (y : nat) (x : nat) (z : nat) : (term108 x y z) = (term109 y x z).
Proof. exact (@lem996056 (y = z) (term80 x z)). Qed.
Lemma lem996067 (x : nat) (y : nat) : (term81 x y) = (term81 x y).
Proof. exact (eq_refl (term81 x y)). Qed.
Lemma lem996068 (y : nat) (x : nat) (z : nat) : (term72 x y z) = (term110 y x z).
Proof. exact (MK_COMB (@lem996067 x y) (@lem996057 y x z)). Qed.
Lemma lem996072 (q : Prop) (p : Prop) (r : Prop) : (term83 p q r) = (term83 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem996073 (y : nat) (x : nat) (z : nat) : (term110 y x z) = (term111 y x z).
Proof. exact (@lem996072 (y = z) (term80 x y) (term80 x z)). Qed.
Lemma lem996095 (y : nat) (x : nat) (z : nat) : (term72 x y z) = (term111 y x z).
Proof. exact (TRANS (@lem996068 y x z) (@lem996073 y x z)). Qed.
Lemma lem996096 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem996097 (y : nat) (x : nat) (z : nat) : (term112 x y z) = (term113 y x z).
Proof. exact (MK_COMB (@lem996096) (@lem996095 y x z)). Qed.
Lemma lem996119 (y : nat) (x : nat) (z : nat) : (term111 y x z) = (term111 y x z).
Proof. exact (eq_refl (term111 y x z)). Qed.
Lemma lem996120 (y : nat) (x : nat) (z : nat) : ((term72 x y z) = (term111 y x z)) = ((term111 y x z) = (term111 y x z)).
Proof. exact (MK_COMB (@lem996097 y x z) (@lem996119 y x z)). Qed.
Lemma lem996122 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem996123 (x : Prop) : (x = x) = True.
Proof. exact (@lem996122 Prop x). Qed.
Lemma lem996124 (y : nat) (x : nat) (z : nat) : ((term111 y x z) = (term111 y x z)) = True.
Proof. exact (@lem996123 (term111 y x z)). Qed.
Lemma lem996125 (y : nat) (x : nat) (z : nat) : ((term72 x y z) = (term111 y x z)) = True.
Proof. exact (TRANS (@lem996120 y x z) (@lem996124 y x z)). Qed.
Lemma lem996126 (y : nat) (x : nat) (z : nat) : True = ((term72 x y z) = (term111 y x z)).
Proof. exact (SYM (@lem996125 y x z)). Qed.
Lemma lem996127 (y : nat) (x : nat) (z : nat) : (term72 x y z) = (term111 y x z).
Proof. exact (EQ_MP (@lem996126 y x z) (@lem0)). Qed.
Lemma lem996128 (y : nat) (x : nat) (z : nat) : term111 y x z.
Proof. exact (EQ_MP (@lem996127 y x z) (@lem995890 x y z)). Qed.
Lemma lem996130 (b : Prop) (a : Prop) : (a \/ b) = (term87 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem996131 (x : nat) (y : nat) (z : nat) : (term111 y x z) = (term114 x y z).
Proof. exact (@lem996130 (term115 y x z) (y = z)). Qed.
Lemma lem996133 (a : Prop) (b : Prop) : (term90 a b) = (term91 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem996134 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term117 y x z).
Proof. exact (@lem996133 (term80 x y) (term80 x z)). Qed.
Lemma lem996136 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem996137 (x : nat) (y : nat) : (term95 x y) = (x = y).
Proof. exact (@lem996136 (x = y)). Qed.
Lemma lem996138 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem996139 (x : nat) (y : nat) : (term96 x y) = (term97 x y).
Proof. exact (MK_COMB (@lem996138) (@lem996137 x y)). Qed.
Lemma lem996141 (a : Prop) : (term94 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem996142 (x : nat) (z : nat) : (term95 x z) = (x = z).
Proof. exact (@lem996141 (x = z)). Qed.
Lemma lem996143 (y : nat) (x : nat) (z : nat) : (term117 y x z) = (term118 y x z).
Proof. exact (MK_COMB (@lem996139 x y) (@lem996142 x z)). Qed.
Lemma lem996144 (y : nat) (x : nat) (z : nat) : (term116 y x z) = (term118 y x z).
Proof. exact (TRANS (@lem996134 y x z) (@lem996143 y x z)). Qed.
Lemma lem996145 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem996146 (y : nat) (x : nat) (z : nat) : (term119 y x z) = (term120 y x z).
Proof. exact (MK_COMB (@lem996145) (@lem996144 y x z)). Qed.
Lemma lem996147 (y : nat) (z : nat) : (y = z) = (y = z).
Proof. exact (eq_refl (y = z)). Qed.
Lemma lem996148 (x : nat) (y : nat) (z : nat) : (term114 x y z) = (term121 x y z).
Proof. exact (MK_COMB (@lem996146 y x z) (@lem996147 y z)). Qed.
Lemma lem996149 (x : nat) (y : nat) (z : nat) : (term111 y x z) = (term121 x y z).
Proof. exact (TRANS (@lem996131 x y z) (@lem996148 x y z)). Qed.
Lemma lem996151 (m : nat) (h1 : term10) (h2 : term58) : term133 m.
Proof. exact (conj (@lem996030 m h1) (@lem996038 m h2)). Qed.
Lemma lem996153 (x : nat) (y : nat) (z : nat) : term121 x y z.
Proof. exact (EQ_MP (@lem996149 x y z) (@lem996128 y x z)). Qed.
Lemma lem996154 (m : nat) : term134 m.
Proof. exact (@lem996153 (term39 m) (term61 m) m). Qed.
Lemma lem996157 (m : nat) (h1 : term10) (h2 : term58) : (term61 m) = m.
Proof. exact (@lem996154 m (@lem996151 m h1 h2)). Qed.
Lemma lem996158 (m : nat) (h1 : term10) (h2 : term58) : term135 m.
Proof. exact (fun h0 : term63 m => @lem996157 m h1 h2). Qed.
Lemma lem996160 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem996161 (m : nat) : (term135 m) = ((term61 m) = m).
Proof. exact (@lem996160 ((term61 m) = m)). Qed.
Lemma lem996162 (m : nat) (h1 : term10) (h2 : term58) : (term61 m) = m.
Proof. exact (EQ_MP (@lem996161 m) (@lem996158 m h1 h2)). Qed.
Lemma lem996165 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem996167 (m : nat) : (term63 m) = (term136 m).
Proof. exact (@lem996165 ((term61 m) = m)). Qed.
Lemma lem996170 (m : nat) (h1 : term63 m) : term136 m.
Proof. exact (EQ_MP (@lem996167 m) (@lem995490 m h1)). Qed.
Lemma lem996173 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : False.
Proof. exact (@lem996170 m h2 (@lem996162 m h1 h3)). Qed.
Lemma lem996174 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : term126.
Proof. exact (fun h0 : ~ False => @lem996173 m h1 h2 h3). Qed.
Lemma lem996176 (p : Prop) : (term76 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem996177 : term126 = False.
Proof. exact (@lem996176 False). Qed.
Lemma lem996178 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996177) (@lem996174 m h1 h2 h3)). Qed.
Lemma lem996179 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : (term63 m) = False.
Proof. exact (prop_ext (fun h4 : term63 m => @lem996178 m h1 h2 h3) (fun h4 : False => @lem995490 m h2)). Qed.
Lemma lem996180 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996179 m h1 h2 h3) (@lem995490 m h2)). Qed.
Lemma lem996181 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : (term62 n) = False.
Proof. exact (prop_ext (fun h4 : term62 n => @lem995834 n h1 h2 h3) (fun h4 : False => @lem995474 n h2)). Qed.
Lemma lem996182 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996181 n h1 h2 h3) (@lem995474 n h2)). Qed.
Lemma lem996183 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : (term63 m) = False.
Proof. exact (prop_ext (fun h4 : term63 m => @lem996180 m h1 h2 h3) (fun h4 : False => @lem995404 m h2)). Qed.
Lemma lem996184 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996183 m h1 h2 h3) (@lem995404 m h2)). Qed.
Lemma lem996185 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : (term62 n) = False.
Proof. exact (prop_ext (fun h4 : term62 n => @lem996182 n h1 h2 h3) (fun h4 : False => @lem995345 n h2)). Qed.
Lemma lem996186 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996185 n h1 h2 h3) (@lem995345 n h2)). Qed.
Lemma lem996187 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : (term63 m) = False.
Proof. exact (prop_ext (fun h4 : term63 m => @lem996184 m h1 h2 h3) (fun h4 : False => @lem995404 m h2)). Qed.
Lemma lem996188 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996187 m h1 h2 h3) (@lem995404 m h2)). Qed.
Lemma lem996189 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem996188 m h1 h2 h3) (fun h4 : False => @lem995352 h1)). Qed.
Lemma lem996190 (m : nat) (h1 : term10) (h2 : term63 m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996189 m h1 h2 h3) (@lem995352 h1)). Qed.
Lemma lem996191 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : (term62 n) = False.
Proof. exact (prop_ext (fun h4 : term62 n => @lem996186 n h1 h2 h3) (fun h4 : False => @lem995345 n h2)). Qed.
Lemma lem996192 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996191 n h1 h2 h3) (@lem995345 n h2)). Qed.
Lemma lem996193 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem996192 n h1 h2 h3) (fun h4 : False => @lem995293 h1)). Qed.
Lemma lem996194 (n : nat) (h1 : term10) (h2 : term62 n) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996193 n h1 h2 h3) (@lem995293 h1)). Qed.
Lemma lem996195 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (or_elim (@lem995133 n m h2) (fun h0 : term62 n => @lem996194 n h1 h0 h3) (fun h0 : term63 m => @lem996190 m h1 h0 h3)). Qed.
Lemma lem996196 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem996195 n m h1 h2 h3) (fun h4 : False => @lem995274 h1)). Qed.
Lemma lem996197 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996196 n m h1 h2 h3) (@lem995274 h1)). Qed.
Lemma lem996198 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term58 = False.
Proof. exact (prop_ext (fun h4 : term58 => @lem996197 n m h1 h2 h3) (fun h4 : False => @lem995263 h3)). Qed.
Lemma lem996199 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996198 n m h1 h2 h3) (@lem995263 h3)). Qed.
Lemma lem996200 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term10 = False.
Proof. exact (prop_ext (fun h4 : term10 => @lem996199 n m h1 h2 h3) (fun h4 : False => @lem995103 h1)). Qed.
Lemma lem996201 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996200 n m h1 h2 h3) (@lem995103 h1)). Qed.
Lemma lem996202 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : term58 = False.
Proof. exact (prop_ext (fun h4 : term58 => @lem996201 n m h1 h2 h3) (fun h4 : False => @lem995090 h3)). Qed.
Lemma lem996203 (n : nat) (m : nat) (h1 : term10) (h2 : term3 n m) (h3 : term58) : False.
Proof. exact (EQ_MP (@lem996202 n m h1 h2 h3) (@lem995090 h3)). Qed.
Lemma lem996204 (n : nat) (m : nat) (h1 : term3 n m) (h2 : term58) : term8.
Proof. exact (fun h0 : term10 => @lem996203 n m h0 h1 h2). Qed.
Lemma lem996205 : term8 = term9.
Proof. exact (@lem69 term10). Qed.
Lemma lem996206 (n : nat) (m : nat) (h1 : term3 n m) (h2 : term58) : term9.
Proof. exact (EQ_MP (@lem996205) (@lem996204 n m h1 h2)). Qed.
Lemma lem996207 (n : nat) (m : nat) (h1 : term3 n m) : term13.
Proof. exact (fun h0 : term58 => @lem996206 n m h1 h0). Qed.
Lemma lem996208 (n : nat) (m : nat) : term15 n m.
Proof. exact (fun h0 : term3 n m => @lem996207 n m h0). Qed.
Lemma lem996213 (m : nat) : term19 m.
Proof. exact (fun n : nat => @lem996208 n m). Qed.
Lemma lem996218 : term23.
Proof. exact (fun m : nat => @lem996213 m). Qed.
Lemma lem996219 : term22.
Proof. exact (EQ_MP (@lem994993) (@lem996218)). Qed.
Lemma lem996220 (m : nat) : term137 m.
Proof. exact (@lem996219 m). Qed.
Lemma lem996221 (m : nat) : (term137 m) = (term18 m).
Proof. exact (eq_refl (term137 m)). Qed.
Lemma lem996222 (m : nat) : term18 m.
Proof. exact (EQ_MP (@lem996221 m) (@lem996220 m)). Qed.
Lemma lem996223 (m : nat) (n : nat) : term138 m n.
Proof. exact (@lem996222 m n). Qed.
Lemma lem996224 (n : nat) (m : nat) : (term138 m n) = (term4 n m).
Proof. exact (eq_refl (term138 m n)). Qed.
Lemma lem996225 (n : nat) (m : nat) : term4 n m.
Proof. exact (EQ_MP (@lem996224 n m) (@lem996223 m n)). Qed.
Lemma lem996227 (n : nat) (m : nat) : term4 n m.
Proof. exact (@lem994748 n m (@lem996225 n m)). Qed.
Lemma lem996228 (n : nat) (m : nat) (h1 : term3 n m) : term12.
Proof. exact (@lem996227 n m (@lem994733 n m h1)). Qed.
Lemma lem996229 (n : nat) (m : nat) (h1 : term3 n m) : term8.
Proof. exact (@lem996228 n m h1 (@lem81645)). Qed.
Lemma lem996230 (n : nat) (m : nat) (h1 : term3 n m) : False.
Proof. exact (@lem996229 n m h1 (@lem75543)). Qed.
Lemma lem996231 (n : nat) (m : nat) (h1 : term3 n m) : (term3 n m) = False.
Proof. exact (prop_ext (fun h2 : term3 n m => @lem996230 n m h1) (fun h2 : False => @lem994733 n m h1)). Qed.
Lemma lem996232 (n : nat) (m : nat) (h1 : term3 n m) : False.
Proof. exact (EQ_MP (@lem996231 n m h1) (@lem994733 n m h1)). Qed.
Lemma lem996233 (n : nat) (m : nat) : term2 n m.
Proof. exact (fun h0 : term3 n m => @lem996232 n m h0). Qed.
Lemma lem996236 (n : nat) (m : nat) : term1 n m.
Proof. exact (EQ_MP (@lem994732 n m) (@lem996233 n m)). Qed.
