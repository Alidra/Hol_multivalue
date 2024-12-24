Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import INT_LE_TRANS_LT_term_abbrevs.
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
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm18392_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm19367_spec.
Require Import thm1980010_spec.
Require Import thm1980011_spec.
Require Import thm1980026_spec.
Require Import thm1980255_spec.
Require Import thm1980259_spec.
Require Import thm1980260_spec.
Require Import thm1980265_spec.
Require Import thm1980266_spec.
Require Import thm1981473_spec.
Require Import thm1981474_spec.
Require Import thm1981475_spec.
Require Import thm1981613_spec.
Require Import thm1982627_spec.
Require Import thm1982628_spec.
Require Import thm1982713_spec.
Require Import thm1982715_spec.
Require Import thm1982719_spec.
Require Import thm1982721_spec.
Require Import thm1982723_spec.
Require Import thm1982733_spec.
Require Import thm1982753_spec.
Require Import thm1982755_spec.
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982761_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988332_spec.
Require Import thm1988342_spec.
Require Import thm2318495_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318604_spec.
Require Import thm32_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem2333928 (y : int) (x : int) : (term0 y x) = (term1 y x).
Proof. exact (@lem2318604 (term1 y x)). Qed.
Lemma lem2333949 (y : int) (x : int) (z : int) : (term2 y x z) = (term3 y x z).
Proof. exact (@lem17362 (int_lt y z) (int_lt x z)). Qed.
Lemma lem2333950 (P : int -> Prop) : (term4 P) = (term5 P).
Proof. exact (@lem18392 int P). Qed.
Lemma lem2333951 (y : int) (x : int) : (term6 y x) = (term7 y x).
Proof. exact (@lem2333950 (term8 y x)). Qed.
Lemma lem2333952 (y : int) (x : int) (z : int) : (term9 y x z) = (term10 y x z).
Proof. exact (eq_refl (term9 y x z)). Qed.
Lemma lem2333953 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2333954 (y : int) (x : int) (z : int) : (term11 y x z) = (term2 y x z).
Proof. exact (MK_COMB (@lem2333953) (@lem2333952 y x z)). Qed.
Lemma lem2333955 (y : int) (x : int) (z : int) : (term11 y x z) = (term3 y x z).
Proof. exact (TRANS (@lem2333954 y x z) (@lem2333949 y x z)). Qed.
Lemma lem2333956 (y : int) (x : int) : (term12 y x) = (term13 y x).
Proof. exact (fun_ext (fun z : int => @lem2333955 y x z)). Qed.
Lemma lem2333957 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2333958 (y : int) (x : int) : (term7 y x) = (term14 y x).
Proof. exact (MK_COMB (@lem2333957) (@lem2333956 y x)). Qed.
Lemma lem2333959 (y : int) (x : int) : (term6 y x) = (term14 y x).
Proof. exact (TRANS (@lem2333951 y x) (@lem2333958 y x)). Qed.
Lemma lem2333961 (x : int) (y : int) : (term15 x y) = (term15 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem2333962 (y : int) (x : int) : (term16 y x) = (term17 y x).
Proof. exact (MK_COMB (@lem2333961 x y) (@lem2333959 y x)). Qed.
Lemma lem2333963 (y : int) (x : int) : (term18 y x) = (term16 y x).
Proof. exact (@lem17362 (int_le x y) (term19 y x)). Qed.
Lemma lem2333965 (y : int) (x : int) : (term18 y x) = (term17 y x).
Proof. exact (TRANS (@lem2333963 y x) (@lem2333962 y x)). Qed.
Lemma lem2333972 (y : int) (x : int) (z : int) : (term3 y x z) = (term3 y x z).
Proof. exact (eq_refl (term3 y x z)). Qed.
Lemma lem2333973 (y : int) (x : int) : (term13 y x) = (term13 y x).
Proof. exact (fun_ext (fun z : int => @lem2333972 y x z)). Qed.
Lemma lem2333974 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2333975 (y : int) (x : int) : (term14 y x) = (term14 y x).
Proof. exact (MK_COMB (@lem2333974) (@lem2333973 y x)). Qed.
Lemma lem2333978 (x : int) (y : int) : (term15 x y) = (term15 x y).
Proof. exact (eq_refl (term15 x y)). Qed.
Lemma lem2333979 (y : int) (x : int) : (term17 y x) = (term17 y x).
Proof. exact (MK_COMB (@lem2333978 x y) (@lem2333975 y x)). Qed.
Lemma lem2333980 (y : int) (x : int) : (term18 y x) = (term17 y x).
Proof. exact (TRANS (@lem2333965 y x) (@lem2333979 y x)). Qed.
Lemma lem2333984 (x : int) (y : int) : (int_le x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2333986 (x : int) (y : int) : (int_lt x y) = (term21 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2333987 (y : int) (z : int) : (int_lt y z) = (term21 y z).
Proof. exact (@lem2333986 y z). Qed.
Lemma lem2333989 (x : int) (y : int) : (int_le x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2333990 (y : int) (z : int) : (term21 y z) = (term22 y z).
Proof. exact (@lem2333989 (term23 y) z). Qed.
Lemma lem2333992 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2333993 (y : int) : (term26 y) = (term27 y).
Proof. exact (@lem2333992 y term28). Qed.
Lemma lem2333995 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2333996 : term30 = term31.
Proof. exact (@lem2333995 term32). Qed.
Lemma lem2333997 (y : int) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem2333998 (y : int) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem2333997 y) (@lem2333996)). Qed.
Lemma lem2333999 (y : int) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem2333993 y) (@lem2333998 y)). Qed.
Lemma lem2334000 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2334001 (y : int) : (term35 y) = (term36 y).
Proof. exact (MK_COMB (@lem2334000) (@lem2333999 y)). Qed.
Lemma lem2334002 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2334003 (y : int) (z : int) : (term22 y z) = (term37 y z).
Proof. exact (MK_COMB (@lem2334001 y) (@lem2334002 z)). Qed.
Lemma lem2334004 (y : int) (z : int) : (term21 y z) = (term37 y z).
Proof. exact (TRANS (@lem2333990 y z) (@lem2334003 y z)). Qed.
Lemma lem2334005 (y : int) (z : int) : (int_lt y z) = (term37 y z).
Proof. exact (TRANS (@lem2333987 y z) (@lem2334004 y z)). Qed.
Lemma lem2334007 (y : int) (x : int) : (term38 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2334008 (z : int) (x : int) : (term38 x z) = (int_le z x).
Proof. exact (@lem2334007 z x). Qed.
Lemma lem2334010 (x : int) (y : int) : (int_le x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2334011 (z : int) (x : int) : (int_le z x) = (term20 z x).
Proof. exact (@lem2334010 z x). Qed.
Lemma lem2334012 (z : int) (x : int) : (term38 x z) = (term20 z x).
Proof. exact (TRANS (@lem2334008 z x) (@lem2334011 z x)). Qed.
Lemma lem2334013 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2334014 (y : int) (z : int) : (term39 y z) = (term40 y z).
Proof. exact (MK_COMB (@lem2334013) (@lem2334005 y z)). Qed.
Lemma lem2334015 (y : int) (z : int) (x : int) : (term3 y x z) = (term41 y z x).
Proof. exact (MK_COMB (@lem2334014 y z) (@lem2334012 z x)). Qed.
Lemma lem2334016 (y : int) (x : int) : (term13 y x) = (term42 y x).
Proof. exact (fun_ext (fun z : int => @lem2334015 y z x)). Qed.
Lemma lem2334017 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2334018 (y : int) (x : int) : (term14 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem2334017) (@lem2334016 y x)). Qed.
Lemma lem2334019 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2334020 (x : int) (y : int) : (term15 x y) = (term44 x y).
Proof. exact (MK_COMB (@lem2334019) (@lem2333984 x y)). Qed.
Lemma lem2334021 (y : int) (x : int) : (term17 y x) = (term45 y x).
Proof. exact (MK_COMB (@lem2334020 x y) (@lem2334018 y x)). Qed.
Lemma lem2334022 (y : int) (x : int) : (term18 y x) = (term45 y x).
Proof. exact (TRANS (@lem2333980 y x) (@lem2334021 y x)). Qed.
Lemma lem2334026 (t : Prop) : (term46 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2334080 (y : int) (x : int) : (term47 y x) = (term45 y x).
Proof. exact (@lem2334026 (term45 y x)). Qed.
Lemma lem2334086 (y : int) (z : int) (x : int) : (term41 y z x) = (term41 y z x).
Proof. exact (eq_refl (term41 y z x)). Qed.
Lemma lem2334087 (y : int) (x : int) : (term42 y x) = (term42 y x).
Proof. exact (fun_ext (fun z : int => @lem2334086 y z x)). Qed.
Lemma lem2334088 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2334089 (y : int) (x : int) : (term43 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem2334088) (@lem2334087 y x)). Qed.
Lemma lem2334091 (x : int) (y : int) : (term44 x y) = (term44 x y).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem2334092 (y : int) (x : int) : (term45 y x) = (term45 y x).
Proof. exact (MK_COMB (@lem2334091 x y) (@lem2334089 y x)). Qed.
Lemma lem2334093 (y : int) (x : int) : (term47 y x) = (term45 y x).
Proof. exact (TRANS (@lem2334080 y x) (@lem2334092 y x)). Qed.
Lemma lem2334098 (y : int) (z : int) (x : int) : (term41 y z x) = (term41 y z x).
Proof. exact (eq_refl (term41 y z x)). Qed.
Lemma lem2334099 (y : int) (x : int) : (term42 y x) = (term42 y x).
Proof. exact (fun_ext (fun z : int => @lem2334098 y z x)). Qed.
Lemma lem2334100 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2334101 (y : int) (x : int) : (term43 y x) = (term43 y x).
Proof. exact (MK_COMB (@lem2334100) (@lem2334099 y x)). Qed.
Lemma lem2334104 (x : int) (y : int) : (term44 x y) = (term44 x y).
Proof. exact (eq_refl (term44 x y)). Qed.
Lemma lem2334105 (y : int) (x : int) : (term45 y x) = (term45 y x).
Proof. exact (MK_COMB (@lem2334104 x y) (@lem2334101 y x)). Qed.
Lemma lem2334106 (y : int) (x : int) : (term47 y x) = (term45 y x).
Proof. exact (TRANS (@lem2334093 y x) (@lem2334105 y x)). Qed.
Lemma lem2334107 (y : int) (x : int) : (term20 x y) = (term48 y x).
Proof. exact (@lem1988287 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2334113 (y : int) (x : int) : (term49 y x) = (term50 y x).
Proof. exact (@lem1982792 (real_of_int y) (real_of_int x)). Qed.
Lemma lem2334118 (x : int) (y : int) : (term50 y x) = (term51 x y).
Proof. exact (@lem1982761 (term52 x) (real_of_int y)). Qed.
Lemma lem2334120 (x : int) (y : int) : (term49 y x) = (term51 x y).
Proof. exact (TRANS (@lem2334113 y x) (@lem2334118 x y)). Qed.
Lemma lem2334121 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334122 (x : int) (y : int) : (term53 y x) = (term54 x y).
Proof. exact (MK_COMB (@lem2334121) (@lem2334120 x y)). Qed.
Lemma lem2334123 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334124 (x : int) (y : int) : (term48 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem2334122 x y) (@lem2334123)). Qed.
Lemma lem2334125 (x : int) (y : int) : (term20 x y) = (term56 x y).
Proof. exact (TRANS (@lem2334107 y x) (@lem2334124 x y)). Qed.
Lemma lem2334126 (z : int) (y : int) : (term37 y z) = (term57 z y).
Proof. exact (@lem1988287 (real_of_int z) (term34 y)). Qed.
Lemma lem2334138 (z : int) (y : int) : (term58 z y) = (term59 z y).
Proof. exact (@lem1982792 (real_of_int z) (term34 y)). Qed.
Lemma lem2334139 (y : int) : (term60 y) = (term61 y).
Proof. exact (@lem1982781 (real_of_int y) term62 term31). Qed.
Lemma lem2334141 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334142 : term31 = term64.
Proof. exact (@lem2334141 term32). Qed.
Lemma lem2334144 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2334145 : term62 = term67.
Proof. exact (@lem2334144 term32). Qed.
Lemma lem2334146 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2334147 : term68 = term69.
Proof. exact (MK_COMB (@lem2334146) (@lem2334145)). Qed.
Lemma lem2334148 : term70 = term71.
Proof. exact (MK_COMB (@lem2334147) (@lem2334142)). Qed.
Lemma lem2334149 : term71 = term72.
Proof. exact (@lem1981613 term62 term31 term31 term31). Qed.
Lemma lem2334151 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334152 : term75 = term76.
Proof. exact (@lem2334151 term32 term32). Qed.
Lemma lem2334153 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334154 : term78 = term32.
Proof. exact (EQ_MP (@lem2334153) (@lem940073)). Qed.
Lemma lem2334155 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334156 : term76 = term31.
Proof. exact (MK_COMB (@lem2334155) (@lem2334154)). Qed.
Lemma lem2334157 : term75 = term31.
Proof. exact (TRANS (@lem2334152) (@lem2334156)). Qed.
Lemma lem2334159 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2334160 : term70 = term81.
Proof. exact (@lem2334159 term32 term32). Qed.
Lemma lem2334161 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334162 : term78 = term32.
Proof. exact (EQ_MP (@lem2334161) (@lem940073)). Qed.
Lemma lem2334163 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334164 : term76 = term31.
Proof. exact (MK_COMB (@lem2334163) (@lem2334162)). Qed.
Lemma lem2334165 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2334166 : term81 = term62.
Proof. exact (MK_COMB (@lem2334165) (@lem2334164)). Qed.
Lemma lem2334167 : term70 = term62.
Proof. exact (TRANS (@lem2334160) (@lem2334166)). Qed.
Lemma lem2334168 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2334169 : term82 = term83.
Proof. exact (MK_COMB (@lem2334168) (@lem2334167)). Qed.
Lemma lem2334170 : term72 = term67.
Proof. exact (MK_COMB (@lem2334169) (@lem2334157)). Qed.
Lemma lem2334171 : term71 = term67.
Proof. exact (TRANS (@lem2334149) (@lem2334170)). Qed.
Lemma lem2334172 : term70 = term67.
Proof. exact (TRANS (@lem2334148) (@lem2334171)). Qed.
Lemma lem2334174 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2334175 : term67 = term62.
Proof. exact (@lem2334174 term62). Qed.
Lemma lem2334176 : term70 = term62.
Proof. exact (TRANS (@lem2334172) (@lem2334175)). Qed.
Lemma lem2334179 (y : int) : (term85 y) = (term85 y).
Proof. exact (eq_refl (term85 y)). Qed.
Lemma lem2334180 (y : int) : (term61 y) = (term86 y).
Proof. exact (MK_COMB (@lem2334179 y) (@lem2334176)). Qed.
Lemma lem2334181 (y : int) : (term60 y) = (term86 y).
Proof. exact (TRANS (@lem2334139 y) (@lem2334180 y)). Qed.
Lemma lem2334182 (z : int) : (term33 z) = (term33 z).
Proof. exact (eq_refl (term33 z)). Qed.
Lemma lem2334183 (z : int) (y : int) : (term59 z y) = (term87 z y).
Proof. exact (MK_COMB (@lem2334182 z) (@lem2334181 y)). Qed.
Lemma lem2334188 (y : int) (z : int) : (term87 z y) = (term88 y z).
Proof. exact (@lem1982757 (term52 y) (real_of_int z) term62). Qed.
Lemma lem2334189 (y : int) (z : int) : (term59 z y) = (term88 y z).
Proof. exact (TRANS (@lem2334183 z y) (@lem2334188 y z)). Qed.
Lemma lem2334191 (y : int) (z : int) : (term58 z y) = (term88 y z).
Proof. exact (TRANS (@lem2334138 z y) (@lem2334189 y z)). Qed.
Lemma lem2334192 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334193 (y : int) (z : int) : (term89 z y) = (term90 y z).
Proof. exact (MK_COMB (@lem2334192) (@lem2334191 y z)). Qed.
Lemma lem2334194 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334195 (y : int) (z : int) : (term57 z y) = (term91 y z).
Proof. exact (MK_COMB (@lem2334193 y z) (@lem2334194)). Qed.
Lemma lem2334196 (y : int) (z : int) : (term37 y z) = (term91 y z).
Proof. exact (TRANS (@lem2334126 z y) (@lem2334195 y z)). Qed.
Lemma lem2334197 (x : int) (z : int) : (term20 z x) = (term48 x z).
Proof. exact (@lem1988287 (real_of_int x) (real_of_int z)). Qed.
Lemma lem2334210 (x : int) (z : int) : (term49 x z) = (term50 x z).
Proof. exact (@lem1982792 (real_of_int x) (real_of_int z)). Qed.
Lemma lem2334211 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334212 (x : int) (z : int) : (term53 x z) = (term92 x z).
Proof. exact (MK_COMB (@lem2334211) (@lem2334210 x z)). Qed.
Lemma lem2334213 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334214 (x : int) (z : int) : (term48 x z) = (term93 x z).
Proof. exact (MK_COMB (@lem2334212 x z) (@lem2334213)). Qed.
Lemma lem2334215 (x : int) (z : int) : (term20 z x) = (term93 x z).
Proof. exact (TRANS (@lem2334197 x z) (@lem2334214 x z)). Qed.
Lemma lem2334216 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2334217 (y : int) (z : int) : (term40 y z) = (term94 y z).
Proof. exact (MK_COMB (@lem2334216) (@lem2334196 y z)). Qed.
Lemma lem2334218 (y : int) (x : int) (z : int) : (term41 y z x) = (term95 y x z).
Proof. exact (MK_COMB (@lem2334217 y z) (@lem2334215 x z)). Qed.
Lemma lem2334219 (y : int) (x : int) : (term42 y x) = (term96 y x).
Proof. exact (fun_ext (fun z : int => @lem2334218 y x z)). Qed.
Lemma lem2334220 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2334221 (y : int) (x : int) : (term43 y x) = (term97 y x).
Proof. exact (MK_COMB (@lem2334220) (@lem2334219 y x)). Qed.
Lemma lem2334222 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2334223 (x : int) (y : int) : (term44 x y) = (term98 x y).
Proof. exact (MK_COMB (@lem2334222) (@lem2334125 x y)). Qed.
Lemma lem2334224 (y : int) (x : int) : (term45 y x) = (term99 y x).
Proof. exact (MK_COMB (@lem2334223 x y) (@lem2334221 y x)). Qed.
Lemma lem2334225 (y : int) (x : int) : (term47 y x) = (term99 y x).
Proof. exact (TRANS (@lem2334106 y x) (@lem2334224 y x)). Qed.
Lemma lem2334276 {A : Type'} (P : Prop) (Q : A -> Prop) : (term100 A P Q) = (term101 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem2334277 (P : Prop) (Q : int -> Prop) : (term102 P Q) = (term103 P Q).
Proof. exact (@lem2334276 int P Q). Qed.
Lemma lem2334278 (y : int) (x : int) : (term104 y x) = (term105 y x).
Proof. exact (@lem2334277 (term56 x y) (term96 y x)). Qed.
Lemma lem2334279 (y : int) (x : int) (z : int) : (term106 y x z) = (term95 y x z).
Proof. exact (eq_refl (term106 y x z)). Qed.
Lemma lem2334280 (y : int) (x : int) : (term107 y x) = (term96 y x).
Proof. exact (fun_ext (fun z : int => @lem2334279 y x z)). Qed.
Lemma lem2334281 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2334282 (y : int) (x : int) : (term108 y x) = (term97 y x).
Proof. exact (MK_COMB (@lem2334281) (@lem2334280 y x)). Qed.
Lemma lem2334283 (x : int) (y : int) : (term98 x y) = (term98 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem2334284 (y : int) (x : int) : (term104 y x) = (term99 y x).
Proof. exact (MK_COMB (@lem2334283 x y) (@lem2334282 y x)). Qed.
Lemma lem2334285 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem2334286 (y : int) (x : int) : (term109 y x) = (term110 y x).
Proof. exact (MK_COMB (@lem2334285) (@lem2334284 y x)). Qed.
Lemma lem2334287 (y : int) (x : int) (z : int) : (term106 y x z) = (term95 y x z).
Proof. exact (eq_refl (term106 y x z)). Qed.
Lemma lem2334288 (x : int) (y : int) : (term98 x y) = (term98 x y).
Proof. exact (eq_refl (term98 x y)). Qed.
Lemma lem2334289 (y : int) (x : int) (z : int) : (term111 y x z) = (term112 y x z).
Proof. exact (MK_COMB (@lem2334288 x y) (@lem2334287 y x z)). Qed.
Lemma lem2334290 (y : int) (x : int) : (term113 y x) = (term114 y x).
Proof. exact (fun_ext (fun z : int => @lem2334289 y x z)). Qed.
Lemma lem2334291 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2334292 (y : int) (x : int) : (term105 y x) = (term115 y x).
Proof. exact (MK_COMB (@lem2334291) (@lem2334290 y x)). Qed.
Lemma lem2334293 (y : int) (x : int) : ((term104 y x) = (term105 y x)) = ((term99 y x) = (term115 y x)).
Proof. exact (MK_COMB (@lem2334286 y x) (@lem2334292 y x)). Qed.
Lemma lem2334295 (y : int) (x : int) : (term99 y x) = (term115 y x).
Proof. exact (EQ_MP (@lem2334293 y x) (@lem2334278 y x)). Qed.
Lemma lem2334298 (y : int) (x : int) : (term47 y x) = (term115 y x).
Proof. exact (TRANS (@lem2334225 y x) (@lem2334295 y x)). Qed.
Lemma lem2334311 (y : int) (x : int) (z : int) : (term112 y x z) = (term112 y x z).
Proof. exact (eq_refl (term112 y x z)). Qed.
Lemma lem2334312 (y : int) (x : int) : (term114 y x) = (term114 y x).
Proof. exact (fun_ext (fun z : int => @lem2334311 y x z)). Qed.
Lemma lem2334313 : (@ex int) = (@ex int).
Proof. exact (eq_refl (@ex int)). Qed.
Lemma lem2334314 (y : int) (x : int) : (term115 y x) = (term115 y x).
Proof. exact (MK_COMB (@lem2334313) (@lem2334312 y x)). Qed.
Lemma lem2334315 (y : int) (x : int) : (term47 y x) = (term115 y x).
Proof. exact (TRANS (@lem2334298 y x) (@lem2334314 y x)). Qed.
Lemma lem2334319 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term112 y x z.
Proof. exact (h1). Qed.
Lemma lem2334320 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term95 y x z.
Proof. exact (proj2 (@lem2334319 y x z h1)). Qed.
Lemma lem2334321 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term56 x y.
Proof. exact (proj1 (@lem2334319 y x z h1)). Qed.
Lemma lem2334322 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term93 x z.
Proof. exact (proj2 (@lem2334320 y x z h1)). Qed.
Lemma lem2334323 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term91 y z.
Proof. exact (proj1 (@lem2334320 y x z h1)). Qed.
Lemma lem2334325 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2334326 : term116 = term117.
Proof. exact (@lem2334325 term55 term31). Qed.
Lemma lem2334328 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334329 : term31 = term64.
Proof. exact (@lem2334328 term32). Qed.
Lemma lem2334331 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334332 : term55 = term118.
Proof. exact (@lem2334331 (NUMERAL 0)). Qed.
Lemma lem2334333 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334334 : term119 = term120.
Proof. exact (MK_COMB (@lem2334333) (@lem2334332)). Qed.
Lemma lem2334335 : term117 = term121.
Proof. exact (MK_COMB (@lem2334334) (@lem2334329)). Qed.
Lemma lem2334336 : term122.
Proof. exact (@lem1980255 term55 term31 term31 term31). Qed.
Lemma lem2334338 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334339 : term117 = term124.
Proof. exact (@lem2334338 (NUMERAL 0) term32). Qed.
Lemma lem2334340 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334341 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334342 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334341 h1) (fun h1 : term124 = True => @lem2334340)). Qed.
Lemma lem2334343 : term124 = True.
Proof. exact (EQ_MP (@lem2334342) (@lem2334340)). Qed.
Lemma lem2334344 : term117 = True.
Proof. exact (TRANS (@lem2334339) (@lem2334343)). Qed.
Lemma lem2334345 : True = term117.
Proof. exact (SYM (@lem2334344)). Qed.
Lemma lem2334346 : term117.
Proof. exact (EQ_MP (@lem2334345) (@lem0)). Qed.
Lemma lem2334347 : term126.
Proof. exact (@lem2334336 (@lem2334346)). Qed.
Lemma lem2334349 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334350 : term117 = term124.
Proof. exact (@lem2334349 (NUMERAL 0) term32). Qed.
Lemma lem2334351 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334352 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334353 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334352 h1) (fun h1 : term124 = True => @lem2334351)). Qed.
Lemma lem2334354 : term124 = True.
Proof. exact (EQ_MP (@lem2334353) (@lem2334351)). Qed.
Lemma lem2334355 : term117 = True.
Proof. exact (TRANS (@lem2334350) (@lem2334354)). Qed.
Lemma lem2334356 : True = term117.
Proof. exact (SYM (@lem2334355)). Qed.
Lemma lem2334357 : term117.
Proof. exact (EQ_MP (@lem2334356) (@lem0)). Qed.
Lemma lem2334358 : term121 = term127.
Proof. exact (@lem2334347 (@lem2334357)). Qed.
Lemma lem2334360 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334361 : term75 = term76.
Proof. exact (@lem2334360 term32 term32). Qed.
Lemma lem2334362 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334363 : term78 = term32.
Proof. exact (EQ_MP (@lem2334362) (@lem940073)). Qed.
Lemma lem2334364 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334365 : term76 = term31.
Proof. exact (MK_COMB (@lem2334364) (@lem2334363)). Qed.
Lemma lem2334366 : term75 = term31.
Proof. exact (TRANS (@lem2334361) (@lem2334365)). Qed.
Lemma lem2334368 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334369 : term129 = term55.
Proof. exact (@lem2334368 term32). Qed.
Lemma lem2334370 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334371 : term130 = term119.
Proof. exact (MK_COMB (@lem2334370) (@lem2334369)). Qed.
Lemma lem2334372 : term127 = term117.
Proof. exact (MK_COMB (@lem2334371) (@lem2334366)). Qed.
Lemma lem2334374 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334375 : term117 = term124.
Proof. exact (@lem2334374 (NUMERAL 0) term32). Qed.
Lemma lem2334376 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334377 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334378 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334377 h1) (fun h1 : term124 = True => @lem2334376)). Qed.
Lemma lem2334379 : term124 = True.
Proof. exact (EQ_MP (@lem2334378) (@lem2334376)). Qed.
Lemma lem2334380 : term117 = True.
Proof. exact (TRANS (@lem2334375) (@lem2334379)). Qed.
Lemma lem2334381 : term127 = True.
Proof. exact (TRANS (@lem2334372) (@lem2334380)). Qed.
Lemma lem2334382 : term121 = True.
Proof. exact (TRANS (@lem2334358) (@lem2334381)). Qed.
Lemma lem2334383 : term117 = True.
Proof. exact (TRANS (@lem2334335) (@lem2334382)). Qed.
Lemma lem2334384 : term116 = True.
Proof. exact (TRANS (@lem2334326) (@lem2334383)). Qed.
Lemma lem2334385 : True = term116.
Proof. exact (SYM (@lem2334384)). Qed.
Lemma lem2334386 : term116.
Proof. exact (EQ_MP (@lem2334385) (@lem0)). Qed.
Lemma lem2334387 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term131 x z.
Proof. exact (conj (@lem2334386) (@lem2334322 y x z h1)). Qed.
Lemma lem2334389 (x : real) (y : real) : term132 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2334390 (x : int) (z : int) : term133 x z.
Proof. exact (@lem2334389 term31 (term50 x z)). Qed.
Lemma lem2334391 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term134 x z.
Proof. exact (@lem2334390 x z (@lem2334387 y x z h1)). Qed.
Lemma lem2334392 (x : int) (z : int) : (term135 x z) = (term50 x z).
Proof. exact (@lem1982733 (term50 x z)). Qed.
Lemma lem2334393 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334394 (x : int) (z : int) : (term136 x z) = (term92 x z).
Proof. exact (MK_COMB (@lem2334393) (@lem2334392 x z)). Qed.
Lemma lem2334395 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334396 (x : int) (z : int) : (term134 x z) = (term93 x z).
Proof. exact (MK_COMB (@lem2334394 x z) (@lem2334395)). Qed.
Lemma lem2334397 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term93 x z.
Proof. exact (EQ_MP (@lem2334396 x z) (@lem2334391 y x z h1)). Qed.
Lemma lem2334399 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2334400 : term116 = term117.
Proof. exact (@lem2334399 term55 term31). Qed.
Lemma lem2334402 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334403 : term31 = term64.
Proof. exact (@lem2334402 term32). Qed.
Lemma lem2334405 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334406 : term55 = term118.
Proof. exact (@lem2334405 (NUMERAL 0)). Qed.
Lemma lem2334407 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334408 : term119 = term120.
Proof. exact (MK_COMB (@lem2334407) (@lem2334406)). Qed.
Lemma lem2334409 : term117 = term121.
Proof. exact (MK_COMB (@lem2334408) (@lem2334403)). Qed.
Lemma lem2334410 : term122.
Proof. exact (@lem1980255 term55 term31 term31 term31). Qed.
Lemma lem2334412 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334413 : term117 = term124.
Proof. exact (@lem2334412 (NUMERAL 0) term32). Qed.
Lemma lem2334414 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334415 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334416 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334415 h1) (fun h1 : term124 = True => @lem2334414)). Qed.
Lemma lem2334417 : term124 = True.
Proof. exact (EQ_MP (@lem2334416) (@lem2334414)). Qed.
Lemma lem2334418 : term117 = True.
Proof. exact (TRANS (@lem2334413) (@lem2334417)). Qed.
Lemma lem2334419 : True = term117.
Proof. exact (SYM (@lem2334418)). Qed.
Lemma lem2334420 : term117.
Proof. exact (EQ_MP (@lem2334419) (@lem0)). Qed.
Lemma lem2334421 : term126.
Proof. exact (@lem2334410 (@lem2334420)). Qed.
Lemma lem2334423 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334424 : term117 = term124.
Proof. exact (@lem2334423 (NUMERAL 0) term32). Qed.
Lemma lem2334425 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334426 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334427 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334426 h1) (fun h1 : term124 = True => @lem2334425)). Qed.
Lemma lem2334428 : term124 = True.
Proof. exact (EQ_MP (@lem2334427) (@lem2334425)). Qed.
Lemma lem2334429 : term117 = True.
Proof. exact (TRANS (@lem2334424) (@lem2334428)). Qed.
Lemma lem2334430 : True = term117.
Proof. exact (SYM (@lem2334429)). Qed.
Lemma lem2334431 : term117.
Proof. exact (EQ_MP (@lem2334430) (@lem0)). Qed.
Lemma lem2334432 : term121 = term127.
Proof. exact (@lem2334421 (@lem2334431)). Qed.
Lemma lem2334434 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334435 : term75 = term76.
Proof. exact (@lem2334434 term32 term32). Qed.
Lemma lem2334436 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334437 : term78 = term32.
Proof. exact (EQ_MP (@lem2334436) (@lem940073)). Qed.
Lemma lem2334438 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334439 : term76 = term31.
Proof. exact (MK_COMB (@lem2334438) (@lem2334437)). Qed.
Lemma lem2334440 : term75 = term31.
Proof. exact (TRANS (@lem2334435) (@lem2334439)). Qed.
Lemma lem2334442 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334443 : term129 = term55.
Proof. exact (@lem2334442 term32). Qed.
Lemma lem2334444 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334445 : term130 = term119.
Proof. exact (MK_COMB (@lem2334444) (@lem2334443)). Qed.
Lemma lem2334446 : term127 = term117.
Proof. exact (MK_COMB (@lem2334445) (@lem2334440)). Qed.
Lemma lem2334448 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334449 : term117 = term124.
Proof. exact (@lem2334448 (NUMERAL 0) term32). Qed.
Lemma lem2334450 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334451 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334452 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334451 h1) (fun h1 : term124 = True => @lem2334450)). Qed.
Lemma lem2334453 : term124 = True.
Proof. exact (EQ_MP (@lem2334452) (@lem2334450)). Qed.
Lemma lem2334454 : term117 = True.
Proof. exact (TRANS (@lem2334449) (@lem2334453)). Qed.
Lemma lem2334455 : term127 = True.
Proof. exact (TRANS (@lem2334446) (@lem2334454)). Qed.
Lemma lem2334456 : term121 = True.
Proof. exact (TRANS (@lem2334432) (@lem2334455)). Qed.
Lemma lem2334457 : term117 = True.
Proof. exact (TRANS (@lem2334409) (@lem2334456)). Qed.
Lemma lem2334458 : term116 = True.
Proof. exact (TRANS (@lem2334400) (@lem2334457)). Qed.
Lemma lem2334459 : True = term116.
Proof. exact (SYM (@lem2334458)). Qed.
Lemma lem2334460 : term116.
Proof. exact (EQ_MP (@lem2334459) (@lem0)). Qed.
Lemma lem2334461 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term137 x y.
Proof. exact (conj (@lem2334460) (@lem2334321 y x z h1)). Qed.
Lemma lem2334463 (x : real) (y : real) : term132 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2334464 (x : int) (y : int) : term138 x y.
Proof. exact (@lem2334463 term31 (term51 x y)). Qed.
Lemma lem2334465 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term139 x y.
Proof. exact (@lem2334464 x y (@lem2334461 y x z h1)). Qed.
Lemma lem2334466 (x : int) (y : int) : (term140 x y) = (term51 x y).
Proof. exact (@lem1982733 (term51 x y)). Qed.
Lemma lem2334467 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334468 (x : int) (y : int) : (term141 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem2334467) (@lem2334466 x y)). Qed.
Lemma lem2334469 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334470 (x : int) (y : int) : (term139 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem2334468 x y) (@lem2334469)). Qed.
Lemma lem2334471 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term56 x y.
Proof. exact (EQ_MP (@lem2334470 x y) (@lem2334465 y x z h1)). Qed.
Lemma lem2334473 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2334474 : term116 = term117.
Proof. exact (@lem2334473 term55 term31). Qed.
Lemma lem2334476 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334477 : term31 = term64.
Proof. exact (@lem2334476 term32). Qed.
Lemma lem2334479 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334480 : term55 = term118.
Proof. exact (@lem2334479 (NUMERAL 0)). Qed.
Lemma lem2334481 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334482 : term119 = term120.
Proof. exact (MK_COMB (@lem2334481) (@lem2334480)). Qed.
Lemma lem2334483 : term117 = term121.
Proof. exact (MK_COMB (@lem2334482) (@lem2334477)). Qed.
Lemma lem2334484 : term122.
Proof. exact (@lem1980255 term55 term31 term31 term31). Qed.
Lemma lem2334486 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334487 : term117 = term124.
Proof. exact (@lem2334486 (NUMERAL 0) term32). Qed.
Lemma lem2334488 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334489 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334490 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334489 h1) (fun h1 : term124 = True => @lem2334488)). Qed.
Lemma lem2334491 : term124 = True.
Proof. exact (EQ_MP (@lem2334490) (@lem2334488)). Qed.
Lemma lem2334492 : term117 = True.
Proof. exact (TRANS (@lem2334487) (@lem2334491)). Qed.
Lemma lem2334493 : True = term117.
Proof. exact (SYM (@lem2334492)). Qed.
Lemma lem2334494 : term117.
Proof. exact (EQ_MP (@lem2334493) (@lem0)). Qed.
Lemma lem2334495 : term126.
Proof. exact (@lem2334484 (@lem2334494)). Qed.
Lemma lem2334497 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334498 : term117 = term124.
Proof. exact (@lem2334497 (NUMERAL 0) term32). Qed.
Lemma lem2334499 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334500 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334501 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334500 h1) (fun h1 : term124 = True => @lem2334499)). Qed.
Lemma lem2334502 : term124 = True.
Proof. exact (EQ_MP (@lem2334501) (@lem2334499)). Qed.
Lemma lem2334503 : term117 = True.
Proof. exact (TRANS (@lem2334498) (@lem2334502)). Qed.
Lemma lem2334504 : True = term117.
Proof. exact (SYM (@lem2334503)). Qed.
Lemma lem2334505 : term117.
Proof. exact (EQ_MP (@lem2334504) (@lem0)). Qed.
Lemma lem2334506 : term121 = term127.
Proof. exact (@lem2334495 (@lem2334505)). Qed.
Lemma lem2334508 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334509 : term75 = term76.
Proof. exact (@lem2334508 term32 term32). Qed.
Lemma lem2334510 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334511 : term78 = term32.
Proof. exact (EQ_MP (@lem2334510) (@lem940073)). Qed.
Lemma lem2334512 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334513 : term76 = term31.
Proof. exact (MK_COMB (@lem2334512) (@lem2334511)). Qed.
Lemma lem2334514 : term75 = term31.
Proof. exact (TRANS (@lem2334509) (@lem2334513)). Qed.
Lemma lem2334516 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334517 : term129 = term55.
Proof. exact (@lem2334516 term32). Qed.
Lemma lem2334518 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334519 : term130 = term119.
Proof. exact (MK_COMB (@lem2334518) (@lem2334517)). Qed.
Lemma lem2334520 : term127 = term117.
Proof. exact (MK_COMB (@lem2334519) (@lem2334514)). Qed.
Lemma lem2334522 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334523 : term117 = term124.
Proof. exact (@lem2334522 (NUMERAL 0) term32). Qed.
Lemma lem2334524 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334525 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334526 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334525 h1) (fun h1 : term124 = True => @lem2334524)). Qed.
Lemma lem2334527 : term124 = True.
Proof. exact (EQ_MP (@lem2334526) (@lem2334524)). Qed.
Lemma lem2334528 : term117 = True.
Proof. exact (TRANS (@lem2334523) (@lem2334527)). Qed.
Lemma lem2334529 : term127 = True.
Proof. exact (TRANS (@lem2334520) (@lem2334528)). Qed.
Lemma lem2334530 : term121 = True.
Proof. exact (TRANS (@lem2334506) (@lem2334529)). Qed.
Lemma lem2334531 : term117 = True.
Proof. exact (TRANS (@lem2334483) (@lem2334530)). Qed.
Lemma lem2334532 : term116 = True.
Proof. exact (TRANS (@lem2334474) (@lem2334531)). Qed.
Lemma lem2334533 : True = term116.
Proof. exact (SYM (@lem2334532)). Qed.
Lemma lem2334534 : term116.
Proof. exact (EQ_MP (@lem2334533) (@lem0)). Qed.
Lemma lem2334535 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term142 y z.
Proof. exact (conj (@lem2334534) (@lem2334323 y x z h1)). Qed.
Lemma lem2334537 (x : real) (y : real) : term132 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2334538 (y : int) (z : int) : term143 y z.
Proof. exact (@lem2334537 term31 (term88 y z)). Qed.
Lemma lem2334539 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term144 y z.
Proof. exact (@lem2334538 y z (@lem2334535 y x z h1)). Qed.
Lemma lem2334540 (y : int) (z : int) : (term145 y z) = (term88 y z).
Proof. exact (@lem1982733 (term88 y z)). Qed.
Lemma lem2334541 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334542 (y : int) (z : int) : (term146 y z) = (term90 y z).
Proof. exact (MK_COMB (@lem2334541) (@lem2334540 y z)). Qed.
Lemma lem2334543 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334544 (y : int) (z : int) : (term144 y z) = (term91 y z).
Proof. exact (MK_COMB (@lem2334542 y z) (@lem2334543)). Qed.
Lemma lem2334545 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term91 y z.
Proof. exact (EQ_MP (@lem2334544 y z) (@lem2334539 y x z h1)). Qed.
Lemma lem2334546 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term147 z x y.
Proof. exact (conj (@lem2334545 y x z h1) (@lem2334471 y x z h1)). Qed.
Lemma lem2334548 (x : real) (y : real) : term148 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2334549 (z : int) (x : int) (y : int) : term149 z x y.
Proof. exact (@lem2334548 (term88 y z) (term51 x y)). Qed.
Lemma lem2334550 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term150 z x y.
Proof. exact (@lem2334549 z x y (@lem2334546 y x z h1)). Qed.
Lemma lem2334551 (x : int) (z : int) (y : int) : (term151 z x y) = (term152 x z y).
Proof. exact (@lem1982757 (term52 x) (term88 y z) (real_of_int y)). Qed.
Lemma lem2334552 (y : int) (z : int) : (term153 z y) = (term154 y z).
Proof. exact (@lem1982759 (term52 y) (real_of_int y) (term155 z)). Qed.
Lemma lem2334553 (y : int) : (term156 y) = (term157 y).
Proof. exact (@lem1982713 term62 (real_of_int y)). Qed.
Lemma lem2334555 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334556 : term31 = term64.
Proof. exact (@lem2334555 term32). Qed.
Lemma lem2334558 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2334559 : term62 = term67.
Proof. exact (@lem2334558 term32). Qed.
Lemma lem2334560 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334561 : term158 = term159.
Proof. exact (MK_COMB (@lem2334560) (@lem2334559)). Qed.
Lemma lem2334562 : term160 = term161.
Proof. exact (MK_COMB (@lem2334561) (@lem2334556)). Qed.
Lemma lem2334563 : term162.
Proof. exact (@lem1981473 term62 term31 term31 term31 term55 term31). Qed.
Lemma lem2334565 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334566 : term117 = term124.
Proof. exact (@lem2334565 (NUMERAL 0) term32). Qed.
Lemma lem2334567 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334568 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334569 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334568 h1) (fun h1 : term124 = True => @lem2334567)). Qed.
Lemma lem2334570 : term124 = True.
Proof. exact (EQ_MP (@lem2334569) (@lem2334567)). Qed.
Lemma lem2334571 : term117 = True.
Proof. exact (TRANS (@lem2334566) (@lem2334570)). Qed.
Lemma lem2334572 : True = term117.
Proof. exact (SYM (@lem2334571)). Qed.
Lemma lem2334573 : term117.
Proof. exact (EQ_MP (@lem2334572) (@lem0)). Qed.
Lemma lem2334574 : term163.
Proof. exact (@lem2334563 (@lem2334573)). Qed.
Lemma lem2334576 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334577 : term117 = term124.
Proof. exact (@lem2334576 (NUMERAL 0) term32). Qed.
Lemma lem2334578 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334579 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334580 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334579 h1) (fun h1 : term124 = True => @lem2334578)). Qed.
Lemma lem2334581 : term124 = True.
Proof. exact (EQ_MP (@lem2334580) (@lem2334578)). Qed.
Lemma lem2334582 : term117 = True.
Proof. exact (TRANS (@lem2334577) (@lem2334581)). Qed.
Lemma lem2334583 : True = term117.
Proof. exact (SYM (@lem2334582)). Qed.
Lemma lem2334584 : term117.
Proof. exact (EQ_MP (@lem2334583) (@lem0)). Qed.
Lemma lem2334585 : term164.
Proof. exact (@lem2334574 (@lem2334584)). Qed.
Lemma lem2334587 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334588 : term117 = term124.
Proof. exact (@lem2334587 (NUMERAL 0) term32). Qed.
Lemma lem2334589 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334590 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334591 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334590 h1) (fun h1 : term124 = True => @lem2334589)). Qed.
Lemma lem2334592 : term124 = True.
Proof. exact (EQ_MP (@lem2334591) (@lem2334589)). Qed.
Lemma lem2334593 : term117 = True.
Proof. exact (TRANS (@lem2334588) (@lem2334592)). Qed.
Lemma lem2334594 : True = term117.
Proof. exact (SYM (@lem2334593)). Qed.
Lemma lem2334595 : term117.
Proof. exact (EQ_MP (@lem2334594) (@lem0)). Qed.
Lemma lem2334596 : term165.
Proof. exact (@lem2334585 (@lem2334595)). Qed.
Lemma lem2334598 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334599 : term75 = term76.
Proof. exact (@lem2334598 term32 term32). Qed.
Lemma lem2334600 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334601 : term78 = term32.
Proof. exact (EQ_MP (@lem2334600) (@lem940073)). Qed.
Lemma lem2334602 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334603 : term76 = term31.
Proof. exact (MK_COMB (@lem2334602) (@lem2334601)). Qed.
Lemma lem2334604 : term75 = term31.
Proof. exact (TRANS (@lem2334599) (@lem2334603)). Qed.
Lemma lem2334606 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2334607 : term70 = term81.
Proof. exact (@lem2334606 term32 term32). Qed.
Lemma lem2334608 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334609 : term78 = term32.
Proof. exact (EQ_MP (@lem2334608) (@lem940073)). Qed.
Lemma lem2334610 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334611 : term76 = term31.
Proof. exact (MK_COMB (@lem2334610) (@lem2334609)). Qed.
Lemma lem2334612 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2334613 : term81 = term62.
Proof. exact (MK_COMB (@lem2334612) (@lem2334611)). Qed.
Lemma lem2334614 : term70 = term62.
Proof. exact (TRANS (@lem2334607) (@lem2334613)). Qed.
Lemma lem2334615 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334616 : term166 = term158.
Proof. exact (MK_COMB (@lem2334615) (@lem2334614)). Qed.
Lemma lem2334617 : term167 = term160.
Proof. exact (MK_COMB (@lem2334616) (@lem2334604)). Qed.
Lemma lem2334619 (m : nat) : (term168 m) = term55.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2334620 : term160 = term55.
Proof. exact (@lem2334619 term32). Qed.
Lemma lem2334621 : term167 = term55.
Proof. exact (TRANS (@lem2334617) (@lem2334620)). Qed.
Lemma lem2334622 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2334623 : term169 = term170.
Proof. exact (MK_COMB (@lem2334622) (@lem2334621)). Qed.
Lemma lem2334624 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2334625 : term171 = term129.
Proof. exact (MK_COMB (@lem2334623) (@lem2334624)). Qed.
Lemma lem2334627 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334628 : term129 = term55.
Proof. exact (@lem2334627 term32). Qed.
Lemma lem2334629 : term171 = term55.
Proof. exact (TRANS (@lem2334625) (@lem2334628)). Qed.
Lemma lem2334631 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334632 : term75 = term76.
Proof. exact (@lem2334631 term32 term32). Qed.
Lemma lem2334633 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334634 : term78 = term32.
Proof. exact (EQ_MP (@lem2334633) (@lem940073)). Qed.
Lemma lem2334635 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334636 : term76 = term31.
Proof. exact (MK_COMB (@lem2334635) (@lem2334634)). Qed.
Lemma lem2334637 : term75 = term31.
Proof. exact (TRANS (@lem2334632) (@lem2334636)). Qed.
Lemma lem2334638 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem2334639 : term172 = term129.
Proof. exact (MK_COMB (@lem2334638) (@lem2334637)). Qed.
Lemma lem2334641 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334642 : term129 = term55.
Proof. exact (@lem2334641 term32). Qed.
Lemma lem2334643 : term172 = term55.
Proof. exact (TRANS (@lem2334639) (@lem2334642)). Qed.
Lemma lem2334644 : term55 = term172.
Proof. exact (SYM (@lem2334643)). Qed.
Lemma lem2334645 : term171 = term172.
Proof. exact (TRANS (@lem2334629) (@lem2334644)). Qed.
Lemma lem2334646 : term161 = term118.
Proof. exact (@lem2334596 (@lem2334645)). Qed.
Lemma lem2334647 : term160 = term118.
Proof. exact (TRANS (@lem2334562) (@lem2334646)). Qed.
Lemma lem2334649 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2334650 : term118 = term55.
Proof. exact (@lem2334649 term55). Qed.
Lemma lem2334651 : term160 = term55.
Proof. exact (TRANS (@lem2334647) (@lem2334650)). Qed.
Lemma lem2334652 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2334653 : term173 = term170.
Proof. exact (MK_COMB (@lem2334652) (@lem2334651)). Qed.
Lemma lem2334654 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2334655 (y : int) : (term157 y) = (term174 y).
Proof. exact (MK_COMB (@lem2334653) (@lem2334654 y)). Qed.
Lemma lem2334656 (y : int) : (term156 y) = (term174 y).
Proof. exact (TRANS (@lem2334553 y) (@lem2334655 y)). Qed.
Lemma lem2334657 (y : int) : (term174 y) = term55.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2334658 (y : int) : (term156 y) = term55.
Proof. exact (TRANS (@lem2334656 y) (@lem2334657 y)). Qed.
Lemma lem2334659 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334660 (y : int) : (term175 y) = term176.
Proof. exact (MK_COMB (@lem2334659) (@lem2334658 y)). Qed.
Lemma lem2334661 (z : int) : (term155 z) = (term155 z).
Proof. exact (eq_refl (term155 z)). Qed.
Lemma lem2334662 (y : int) (z : int) : (term154 y z) = (term177 z).
Proof. exact (MK_COMB (@lem2334660 y) (@lem2334661 z)). Qed.
Lemma lem2334663 (y : int) (z : int) : (term153 z y) = (term177 z).
Proof. exact (TRANS (@lem2334552 y z) (@lem2334662 y z)). Qed.
Lemma lem2334664 (z : int) : (term177 z) = (term155 z).
Proof. exact (@lem1982721 (term155 z)). Qed.
Lemma lem2334665 (y : int) (z : int) : (term153 z y) = (term155 z).
Proof. exact (TRANS (@lem2334663 y z) (@lem2334664 z)). Qed.
Lemma lem2334666 (x : int) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem2334667 (y : int) (x : int) (z : int) : (term152 x z y) = (term88 x z).
Proof. exact (MK_COMB (@lem2334666 x) (@lem2334665 y z)). Qed.
Lemma lem2334668 (y : int) (x : int) (z : int) : (term151 z x y) = (term88 x z).
Proof. exact (TRANS (@lem2334551 x z y) (@lem2334667 y x z)). Qed.
Lemma lem2334669 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334670 (y : int) (x : int) (z : int) : (term178 z x y) = (term90 x z).
Proof. exact (MK_COMB (@lem2334669) (@lem2334668 y x z)). Qed.
Lemma lem2334671 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334672 (y : int) (x : int) (z : int) : (term150 z x y) = (term91 x z).
Proof. exact (MK_COMB (@lem2334670 y x z) (@lem2334671)). Qed.
Lemma lem2334673 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term91 x z.
Proof. exact (EQ_MP (@lem2334672 y x z) (@lem2334550 y x z h1)). Qed.
Lemma lem2334675 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2334676 : term116 = term117.
Proof. exact (@lem2334675 term55 term31). Qed.
Lemma lem2334678 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334679 : term31 = term64.
Proof. exact (@lem2334678 term32). Qed.
Lemma lem2334681 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334682 : term55 = term118.
Proof. exact (@lem2334681 (NUMERAL 0)). Qed.
Lemma lem2334683 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334684 : term119 = term120.
Proof. exact (MK_COMB (@lem2334683) (@lem2334682)). Qed.
Lemma lem2334685 : term117 = term121.
Proof. exact (MK_COMB (@lem2334684) (@lem2334679)). Qed.
Lemma lem2334686 : term122.
Proof. exact (@lem1980255 term55 term31 term31 term31). Qed.
Lemma lem2334688 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334689 : term117 = term124.
Proof. exact (@lem2334688 (NUMERAL 0) term32). Qed.
Lemma lem2334690 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334691 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334692 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334691 h1) (fun h1 : term124 = True => @lem2334690)). Qed.
Lemma lem2334693 : term124 = True.
Proof. exact (EQ_MP (@lem2334692) (@lem2334690)). Qed.
Lemma lem2334694 : term117 = True.
Proof. exact (TRANS (@lem2334689) (@lem2334693)). Qed.
Lemma lem2334695 : True = term117.
Proof. exact (SYM (@lem2334694)). Qed.
Lemma lem2334696 : term117.
Proof. exact (EQ_MP (@lem2334695) (@lem0)). Qed.
Lemma lem2334697 : term126.
Proof. exact (@lem2334686 (@lem2334696)). Qed.
Lemma lem2334699 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334700 : term117 = term124.
Proof. exact (@lem2334699 (NUMERAL 0) term32). Qed.
Lemma lem2334701 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334702 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334703 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334702 h1) (fun h1 : term124 = True => @lem2334701)). Qed.
Lemma lem2334704 : term124 = True.
Proof. exact (EQ_MP (@lem2334703) (@lem2334701)). Qed.
Lemma lem2334705 : term117 = True.
Proof. exact (TRANS (@lem2334700) (@lem2334704)). Qed.
Lemma lem2334706 : True = term117.
Proof. exact (SYM (@lem2334705)). Qed.
Lemma lem2334707 : term117.
Proof. exact (EQ_MP (@lem2334706) (@lem0)). Qed.
Lemma lem2334708 : term121 = term127.
Proof. exact (@lem2334697 (@lem2334707)). Qed.
Lemma lem2334710 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334711 : term75 = term76.
Proof. exact (@lem2334710 term32 term32). Qed.
Lemma lem2334712 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334713 : term78 = term32.
Proof. exact (EQ_MP (@lem2334712) (@lem940073)). Qed.
Lemma lem2334714 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334715 : term76 = term31.
Proof. exact (MK_COMB (@lem2334714) (@lem2334713)). Qed.
Lemma lem2334716 : term75 = term31.
Proof. exact (TRANS (@lem2334711) (@lem2334715)). Qed.
Lemma lem2334718 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334719 : term129 = term55.
Proof. exact (@lem2334718 term32). Qed.
Lemma lem2334720 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2334721 : term130 = term119.
Proof. exact (MK_COMB (@lem2334720) (@lem2334719)). Qed.
Lemma lem2334722 : term127 = term117.
Proof. exact (MK_COMB (@lem2334721) (@lem2334716)). Qed.
Lemma lem2334724 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334725 : term117 = term124.
Proof. exact (@lem2334724 (NUMERAL 0) term32). Qed.
Lemma lem2334726 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334727 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334728 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334727 h1) (fun h1 : term124 = True => @lem2334726)). Qed.
Lemma lem2334729 : term124 = True.
Proof. exact (EQ_MP (@lem2334728) (@lem2334726)). Qed.
Lemma lem2334730 : term117 = True.
Proof. exact (TRANS (@lem2334725) (@lem2334729)). Qed.
Lemma lem2334731 : term127 = True.
Proof. exact (TRANS (@lem2334722) (@lem2334730)). Qed.
Lemma lem2334732 : term121 = True.
Proof. exact (TRANS (@lem2334708) (@lem2334731)). Qed.
Lemma lem2334733 : term117 = True.
Proof. exact (TRANS (@lem2334685) (@lem2334732)). Qed.
Lemma lem2334734 : term116 = True.
Proof. exact (TRANS (@lem2334676) (@lem2334733)). Qed.
Lemma lem2334735 : True = term116.
Proof. exact (SYM (@lem2334734)). Qed.
Lemma lem2334736 : term116.
Proof. exact (EQ_MP (@lem2334735) (@lem0)). Qed.
Lemma lem2334737 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term142 x z.
Proof. exact (conj (@lem2334736) (@lem2334673 y x z h1)). Qed.
Lemma lem2334739 (x : real) (y : real) : term132 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2334740 (x : int) (z : int) : term143 x z.
Proof. exact (@lem2334739 term31 (term88 x z)). Qed.
Lemma lem2334741 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term144 x z.
Proof. exact (@lem2334740 x z (@lem2334737 y x z h1)). Qed.
Lemma lem2334742 (x : int) (z : int) : (term145 x z) = (term88 x z).
Proof. exact (@lem1982733 (term88 x z)). Qed.
Lemma lem2334743 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334744 (x : int) (z : int) : (term146 x z) = (term90 x z).
Proof. exact (MK_COMB (@lem2334743) (@lem2334742 x z)). Qed.
Lemma lem2334745 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334746 (x : int) (z : int) : (term144 x z) = (term91 x z).
Proof. exact (MK_COMB (@lem2334744 x z) (@lem2334745)). Qed.
Lemma lem2334747 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term91 x z.
Proof. exact (EQ_MP (@lem2334746 x z) (@lem2334741 y x z h1)). Qed.
Lemma lem2334748 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term179 x z.
Proof. exact (conj (@lem2334747 y x z h1) (@lem2334397 y x z h1)). Qed.
Lemma lem2334750 (x : real) (y : real) : term148 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2334751 (x : int) (z : int) : term180 x z.
Proof. exact (@lem2334750 (term88 x z) (term50 x z)). Qed.
Lemma lem2334752 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term181 x z.
Proof. exact (@lem2334751 x z (@lem2334748 y x z h1)). Qed.
Lemma lem2334753 (x : int) (z : int) : (term182 x z) = (term183 x z).
Proof. exact (@lem1982753 (term52 x) (real_of_int x) (term155 z) (term52 z)). Qed.
Lemma lem2334754 (x : int) : (term156 x) = (term157 x).
Proof. exact (@lem1982713 term62 (real_of_int x)). Qed.
Lemma lem2334756 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334757 : term31 = term64.
Proof. exact (@lem2334756 term32). Qed.
Lemma lem2334759 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2334760 : term62 = term67.
Proof. exact (@lem2334759 term32). Qed.
Lemma lem2334761 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334762 : term158 = term159.
Proof. exact (MK_COMB (@lem2334761) (@lem2334760)). Qed.
Lemma lem2334763 : term160 = term161.
Proof. exact (MK_COMB (@lem2334762) (@lem2334757)). Qed.
Lemma lem2334764 : term162.
Proof. exact (@lem1981473 term62 term31 term31 term31 term55 term31). Qed.
Lemma lem2334766 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334767 : term117 = term124.
Proof. exact (@lem2334766 (NUMERAL 0) term32). Qed.
Lemma lem2334768 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334769 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334770 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334769 h1) (fun h1 : term124 = True => @lem2334768)). Qed.
Lemma lem2334771 : term124 = True.
Proof. exact (EQ_MP (@lem2334770) (@lem2334768)). Qed.
Lemma lem2334772 : term117 = True.
Proof. exact (TRANS (@lem2334767) (@lem2334771)). Qed.
Lemma lem2334773 : True = term117.
Proof. exact (SYM (@lem2334772)). Qed.
Lemma lem2334774 : term117.
Proof. exact (EQ_MP (@lem2334773) (@lem0)). Qed.
Lemma lem2334775 : term163.
Proof. exact (@lem2334764 (@lem2334774)). Qed.
Lemma lem2334777 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334778 : term117 = term124.
Proof. exact (@lem2334777 (NUMERAL 0) term32). Qed.
Lemma lem2334779 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334780 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334781 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334780 h1) (fun h1 : term124 = True => @lem2334779)). Qed.
Lemma lem2334782 : term124 = True.
Proof. exact (EQ_MP (@lem2334781) (@lem2334779)). Qed.
Lemma lem2334783 : term117 = True.
Proof. exact (TRANS (@lem2334778) (@lem2334782)). Qed.
Lemma lem2334784 : True = term117.
Proof. exact (SYM (@lem2334783)). Qed.
Lemma lem2334785 : term117.
Proof. exact (EQ_MP (@lem2334784) (@lem0)). Qed.
Lemma lem2334786 : term164.
Proof. exact (@lem2334775 (@lem2334785)). Qed.
Lemma lem2334788 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334789 : term117 = term124.
Proof. exact (@lem2334788 (NUMERAL 0) term32). Qed.
Lemma lem2334790 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334791 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334792 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334791 h1) (fun h1 : term124 = True => @lem2334790)). Qed.
Lemma lem2334793 : term124 = True.
Proof. exact (EQ_MP (@lem2334792) (@lem2334790)). Qed.
Lemma lem2334794 : term117 = True.
Proof. exact (TRANS (@lem2334789) (@lem2334793)). Qed.
Lemma lem2334795 : True = term117.
Proof. exact (SYM (@lem2334794)). Qed.
Lemma lem2334796 : term117.
Proof. exact (EQ_MP (@lem2334795) (@lem0)). Qed.
Lemma lem2334797 : term165.
Proof. exact (@lem2334786 (@lem2334796)). Qed.
Lemma lem2334799 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334800 : term75 = term76.
Proof. exact (@lem2334799 term32 term32). Qed.
Lemma lem2334801 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334802 : term78 = term32.
Proof. exact (EQ_MP (@lem2334801) (@lem940073)). Qed.
Lemma lem2334803 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334804 : term76 = term31.
Proof. exact (MK_COMB (@lem2334803) (@lem2334802)). Qed.
Lemma lem2334805 : term75 = term31.
Proof. exact (TRANS (@lem2334800) (@lem2334804)). Qed.
Lemma lem2334807 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2334808 : term70 = term81.
Proof. exact (@lem2334807 term32 term32). Qed.
Lemma lem2334809 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334810 : term78 = term32.
Proof. exact (EQ_MP (@lem2334809) (@lem940073)). Qed.
Lemma lem2334811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334812 : term76 = term31.
Proof. exact (MK_COMB (@lem2334811) (@lem2334810)). Qed.
Lemma lem2334813 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2334814 : term81 = term62.
Proof. exact (MK_COMB (@lem2334813) (@lem2334812)). Qed.
Lemma lem2334815 : term70 = term62.
Proof. exact (TRANS (@lem2334808) (@lem2334814)). Qed.
Lemma lem2334816 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334817 : term166 = term158.
Proof. exact (MK_COMB (@lem2334816) (@lem2334815)). Qed.
Lemma lem2334818 : term167 = term160.
Proof. exact (MK_COMB (@lem2334817) (@lem2334805)). Qed.
Lemma lem2334820 (m : nat) : (term168 m) = term55.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2334821 : term160 = term55.
Proof. exact (@lem2334820 term32). Qed.
Lemma lem2334822 : term167 = term55.
Proof. exact (TRANS (@lem2334818) (@lem2334821)). Qed.
Lemma lem2334823 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2334824 : term169 = term170.
Proof. exact (MK_COMB (@lem2334823) (@lem2334822)). Qed.
Lemma lem2334825 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2334826 : term171 = term129.
Proof. exact (MK_COMB (@lem2334824) (@lem2334825)). Qed.
Lemma lem2334828 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334829 : term129 = term55.
Proof. exact (@lem2334828 term32). Qed.
Lemma lem2334830 : term171 = term55.
Proof. exact (TRANS (@lem2334826) (@lem2334829)). Qed.
Lemma lem2334832 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334833 : term75 = term76.
Proof. exact (@lem2334832 term32 term32). Qed.
Lemma lem2334834 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334835 : term78 = term32.
Proof. exact (EQ_MP (@lem2334834) (@lem940073)). Qed.
Lemma lem2334836 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334837 : term76 = term31.
Proof. exact (MK_COMB (@lem2334836) (@lem2334835)). Qed.
Lemma lem2334838 : term75 = term31.
Proof. exact (TRANS (@lem2334833) (@lem2334837)). Qed.
Lemma lem2334839 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem2334840 : term172 = term129.
Proof. exact (MK_COMB (@lem2334839) (@lem2334838)). Qed.
Lemma lem2334842 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334843 : term129 = term55.
Proof. exact (@lem2334842 term32). Qed.
Lemma lem2334844 : term172 = term55.
Proof. exact (TRANS (@lem2334840) (@lem2334843)). Qed.
Lemma lem2334845 : term55 = term172.
Proof. exact (SYM (@lem2334844)). Qed.
Lemma lem2334846 : term171 = term172.
Proof. exact (TRANS (@lem2334830) (@lem2334845)). Qed.
Lemma lem2334847 : term161 = term118.
Proof. exact (@lem2334797 (@lem2334846)). Qed.
Lemma lem2334848 : term160 = term118.
Proof. exact (TRANS (@lem2334763) (@lem2334847)). Qed.
Lemma lem2334850 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2334851 : term118 = term55.
Proof. exact (@lem2334850 term55). Qed.
Lemma lem2334852 : term160 = term55.
Proof. exact (TRANS (@lem2334848) (@lem2334851)). Qed.
Lemma lem2334853 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2334854 : term173 = term170.
Proof. exact (MK_COMB (@lem2334853) (@lem2334852)). Qed.
Lemma lem2334855 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2334856 (x : int) : (term157 x) = (term174 x).
Proof. exact (MK_COMB (@lem2334854) (@lem2334855 x)). Qed.
Lemma lem2334857 (x : int) : (term156 x) = (term174 x).
Proof. exact (TRANS (@lem2334754 x) (@lem2334856 x)). Qed.
Lemma lem2334858 (x : int) : (term174 x) = term55.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2334859 (x : int) : (term156 x) = term55.
Proof. exact (TRANS (@lem2334857 x) (@lem2334858 x)). Qed.
Lemma lem2334860 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334861 (x : int) : (term175 x) = term176.
Proof. exact (MK_COMB (@lem2334860) (@lem2334859 x)). Qed.
Lemma lem2334862 (z : int) : (term184 z) = (term185 z).
Proof. exact (@lem1982759 (real_of_int z) (term52 z) term62). Qed.
Lemma lem2334863 (z : int) : (term186 z) = (term157 z).
Proof. exact (@lem1982715 term62 (real_of_int z)). Qed.
Lemma lem2334865 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334866 : term31 = term64.
Proof. exact (@lem2334865 term32). Qed.
Lemma lem2334868 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2334869 : term62 = term67.
Proof. exact (@lem2334868 term32). Qed.
Lemma lem2334870 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334871 : term158 = term159.
Proof. exact (MK_COMB (@lem2334870) (@lem2334869)). Qed.
Lemma lem2334872 : term160 = term161.
Proof. exact (MK_COMB (@lem2334871) (@lem2334866)). Qed.
Lemma lem2334873 : term162.
Proof. exact (@lem1981473 term62 term31 term31 term31 term55 term31). Qed.
Lemma lem2334875 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334876 : term117 = term124.
Proof. exact (@lem2334875 (NUMERAL 0) term32). Qed.
Lemma lem2334877 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334878 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334879 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334878 h1) (fun h1 : term124 = True => @lem2334877)). Qed.
Lemma lem2334880 : term124 = True.
Proof. exact (EQ_MP (@lem2334879) (@lem2334877)). Qed.
Lemma lem2334881 : term117 = True.
Proof. exact (TRANS (@lem2334876) (@lem2334880)). Qed.
Lemma lem2334882 : True = term117.
Proof. exact (SYM (@lem2334881)). Qed.
Lemma lem2334883 : term117.
Proof. exact (EQ_MP (@lem2334882) (@lem0)). Qed.
Lemma lem2334884 : term163.
Proof. exact (@lem2334873 (@lem2334883)). Qed.
Lemma lem2334886 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334887 : term117 = term124.
Proof. exact (@lem2334886 (NUMERAL 0) term32). Qed.
Lemma lem2334888 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334889 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334890 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334889 h1) (fun h1 : term124 = True => @lem2334888)). Qed.
Lemma lem2334891 : term124 = True.
Proof. exact (EQ_MP (@lem2334890) (@lem2334888)). Qed.
Lemma lem2334892 : term117 = True.
Proof. exact (TRANS (@lem2334887) (@lem2334891)). Qed.
Lemma lem2334893 : True = term117.
Proof. exact (SYM (@lem2334892)). Qed.
Lemma lem2334894 : term117.
Proof. exact (EQ_MP (@lem2334893) (@lem0)). Qed.
Lemma lem2334895 : term164.
Proof. exact (@lem2334884 (@lem2334894)). Qed.
Lemma lem2334897 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2334898 : term117 = term124.
Proof. exact (@lem2334897 (NUMERAL 0) term32). Qed.
Lemma lem2334899 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2334900 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2334901 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2334900 h1) (fun h1 : term124 = True => @lem2334899)). Qed.
Lemma lem2334902 : term124 = True.
Proof. exact (EQ_MP (@lem2334901) (@lem2334899)). Qed.
Lemma lem2334903 : term117 = True.
Proof. exact (TRANS (@lem2334898) (@lem2334902)). Qed.
Lemma lem2334904 : True = term117.
Proof. exact (SYM (@lem2334903)). Qed.
Lemma lem2334905 : term117.
Proof. exact (EQ_MP (@lem2334904) (@lem0)). Qed.
Lemma lem2334906 : term165.
Proof. exact (@lem2334895 (@lem2334905)). Qed.
Lemma lem2334908 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334909 : term75 = term76.
Proof. exact (@lem2334908 term32 term32). Qed.
Lemma lem2334910 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334911 : term78 = term32.
Proof. exact (EQ_MP (@lem2334910) (@lem940073)). Qed.
Lemma lem2334912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334913 : term76 = term31.
Proof. exact (MK_COMB (@lem2334912) (@lem2334911)). Qed.
Lemma lem2334914 : term75 = term31.
Proof. exact (TRANS (@lem2334909) (@lem2334913)). Qed.
Lemma lem2334916 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2334917 : term70 = term81.
Proof. exact (@lem2334916 term32 term32). Qed.
Lemma lem2334918 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334919 : term78 = term32.
Proof. exact (EQ_MP (@lem2334918) (@lem940073)). Qed.
Lemma lem2334920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334921 : term76 = term31.
Proof. exact (MK_COMB (@lem2334920) (@lem2334919)). Qed.
Lemma lem2334922 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2334923 : term81 = term62.
Proof. exact (MK_COMB (@lem2334922) (@lem2334921)). Qed.
Lemma lem2334924 : term70 = term62.
Proof. exact (TRANS (@lem2334917) (@lem2334923)). Qed.
Lemma lem2334925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334926 : term166 = term158.
Proof. exact (MK_COMB (@lem2334925) (@lem2334924)). Qed.
Lemma lem2334927 : term167 = term160.
Proof. exact (MK_COMB (@lem2334926) (@lem2334914)). Qed.
Lemma lem2334929 (m : nat) : (term168 m) = term55.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2334930 : term160 = term55.
Proof. exact (@lem2334929 term32). Qed.
Lemma lem2334931 : term167 = term55.
Proof. exact (TRANS (@lem2334927) (@lem2334930)). Qed.
Lemma lem2334932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2334933 : term169 = term170.
Proof. exact (MK_COMB (@lem2334932) (@lem2334931)). Qed.
Lemma lem2334934 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2334935 : term171 = term129.
Proof. exact (MK_COMB (@lem2334933) (@lem2334934)). Qed.
Lemma lem2334937 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334938 : term129 = term55.
Proof. exact (@lem2334937 term32). Qed.
Lemma lem2334939 : term171 = term55.
Proof. exact (TRANS (@lem2334935) (@lem2334938)). Qed.
Lemma lem2334941 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2334942 : term75 = term76.
Proof. exact (@lem2334941 term32 term32). Qed.
Lemma lem2334943 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2334944 : term78 = term32.
Proof. exact (EQ_MP (@lem2334943) (@lem940073)). Qed.
Lemma lem2334945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2334946 : term76 = term31.
Proof. exact (MK_COMB (@lem2334945) (@lem2334944)). Qed.
Lemma lem2334947 : term75 = term31.
Proof. exact (TRANS (@lem2334942) (@lem2334946)). Qed.
Lemma lem2334948 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem2334949 : term172 = term129.
Proof. exact (MK_COMB (@lem2334948) (@lem2334947)). Qed.
Lemma lem2334951 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2334952 : term129 = term55.
Proof. exact (@lem2334951 term32). Qed.
Lemma lem2334953 : term172 = term55.
Proof. exact (TRANS (@lem2334949) (@lem2334952)). Qed.
Lemma lem2334954 : term55 = term172.
Proof. exact (SYM (@lem2334953)). Qed.
Lemma lem2334955 : term171 = term172.
Proof. exact (TRANS (@lem2334939) (@lem2334954)). Qed.
Lemma lem2334956 : term161 = term118.
Proof. exact (@lem2334906 (@lem2334955)). Qed.
Lemma lem2334957 : term160 = term118.
Proof. exact (TRANS (@lem2334872) (@lem2334956)). Qed.
Lemma lem2334959 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2334960 : term118 = term55.
Proof. exact (@lem2334959 term55). Qed.
Lemma lem2334961 : term160 = term55.
Proof. exact (TRANS (@lem2334957) (@lem2334960)). Qed.
Lemma lem2334962 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2334963 : term173 = term170.
Proof. exact (MK_COMB (@lem2334962) (@lem2334961)). Qed.
Lemma lem2334964 (z : int) : (real_of_int z) = (real_of_int z).
Proof. exact (eq_refl (real_of_int z)). Qed.
Lemma lem2334965 (z : int) : (term157 z) = (term174 z).
Proof. exact (MK_COMB (@lem2334963) (@lem2334964 z)). Qed.
Lemma lem2334966 (z : int) : (term186 z) = (term174 z).
Proof. exact (TRANS (@lem2334863 z) (@lem2334965 z)). Qed.
Lemma lem2334967 (z : int) : (term174 z) = term55.
Proof. exact (@lem1982719 (real_of_int z)). Qed.
Lemma lem2334968 (z : int) : (term186 z) = term55.
Proof. exact (TRANS (@lem2334966 z) (@lem2334967 z)). Qed.
Lemma lem2334969 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2334970 (z : int) : (term187 z) = term176.
Proof. exact (MK_COMB (@lem2334969) (@lem2334968 z)). Qed.
Lemma lem2334971 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem2334972 (z : int) : (term185 z) = term188.
Proof. exact (MK_COMB (@lem2334970 z) (@lem2334971)). Qed.
Lemma lem2334973 (z : int) : (term184 z) = term188.
Proof. exact (TRANS (@lem2334862 z) (@lem2334972 z)). Qed.
Lemma lem2334974 : term188 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem2334975 (z : int) : (term184 z) = term62.
Proof. exact (TRANS (@lem2334973 z) (@lem2334974)). Qed.
Lemma lem2334976 (x : int) (z : int) : (term183 x z) = term188.
Proof. exact (MK_COMB (@lem2334861 x) (@lem2334975 z)). Qed.
Lemma lem2334977 (x : int) (z : int) : (term182 x z) = term188.
Proof. exact (TRANS (@lem2334753 x z) (@lem2334976 x z)). Qed.
Lemma lem2334978 : term188 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem2334979 (x : int) (z : int) : (term182 x z) = term62.
Proof. exact (TRANS (@lem2334977 x z) (@lem2334978)). Qed.
Lemma lem2334980 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2334981 (x : int) (z : int) : (term189 x z) = term190.
Proof. exact (MK_COMB (@lem2334980) (@lem2334979 x z)). Qed.
Lemma lem2334982 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2334983 (x : int) (z : int) : (term181 x z) = term191.
Proof. exact (MK_COMB (@lem2334981 x z) (@lem2334982)). Qed.
Lemma lem2334984 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term191.
Proof. exact (EQ_MP (@lem2334983 x z) (@lem2334752 y x z h1)). Qed.
Lemma lem2334986 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2334987 : term191 = term192.
Proof. exact (@lem2334986 term55 term62). Qed.
Lemma lem2334989 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2334990 : term62 = term67.
Proof. exact (@lem2334989 term32). Qed.
Lemma lem2334992 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2334993 : term55 = term118.
Proof. exact (@lem2334992 (NUMERAL 0)). Qed.
Lemma lem2334994 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2334995 : term193 = term194.
Proof. exact (MK_COMB (@lem2334994) (@lem2334993)). Qed.
Lemma lem2334996 : term192 = term195.
Proof. exact (MK_COMB (@lem2334995) (@lem2334990)). Qed.
Lemma lem2334997 : term196.
Proof. exact (@lem1980026 term55 term31 term62 term31). Qed.
Lemma lem2334999 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335000 : term117 = term124.
Proof. exact (@lem2334999 (NUMERAL 0) term32). Qed.
Lemma lem2335001 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335002 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335003 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335002 h1) (fun h1 : term124 = True => @lem2335001)). Qed.
Lemma lem2335004 : term124 = True.
Proof. exact (EQ_MP (@lem2335003) (@lem2335001)). Qed.
Lemma lem2335005 : term117 = True.
Proof. exact (TRANS (@lem2335000) (@lem2335004)). Qed.
Lemma lem2335006 : True = term117.
Proof. exact (SYM (@lem2335005)). Qed.
Lemma lem2335007 : term117.
Proof. exact (EQ_MP (@lem2335006) (@lem0)). Qed.
Lemma lem2335008 : term197.
Proof. exact (@lem2334997 (@lem2335007)). Qed.
Lemma lem2335010 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335011 : term117 = term124.
Proof. exact (@lem2335010 (NUMERAL 0) term32). Qed.
Lemma lem2335012 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335013 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335014 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335013 h1) (fun h1 : term124 = True => @lem2335012)). Qed.
Lemma lem2335015 : term124 = True.
Proof. exact (EQ_MP (@lem2335014) (@lem2335012)). Qed.
Lemma lem2335016 : term117 = True.
Proof. exact (TRANS (@lem2335011) (@lem2335015)). Qed.
Lemma lem2335017 : True = term117.
Proof. exact (SYM (@lem2335016)). Qed.
Lemma lem2335018 : term117.
Proof. exact (EQ_MP (@lem2335017) (@lem0)). Qed.
Lemma lem2335019 : term195 = term198.
Proof. exact (@lem2335008 (@lem2335018)). Qed.
Lemma lem2335021 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335022 : term70 = term81.
Proof. exact (@lem2335021 term32 term32). Qed.
Lemma lem2335023 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335024 : term78 = term32.
Proof. exact (EQ_MP (@lem2335023) (@lem940073)). Qed.
Lemma lem2335025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335026 : term76 = term31.
Proof. exact (MK_COMB (@lem2335025) (@lem2335024)). Qed.
Lemma lem2335027 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335028 : term81 = term62.
Proof. exact (MK_COMB (@lem2335027) (@lem2335026)). Qed.
Lemma lem2335029 : term70 = term62.
Proof. exact (TRANS (@lem2335022) (@lem2335028)). Qed.
Lemma lem2335031 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335032 : term129 = term55.
Proof. exact (@lem2335031 term32). Qed.
Lemma lem2335033 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2335034 : term199 = term193.
Proof. exact (MK_COMB (@lem2335033) (@lem2335032)). Qed.
Lemma lem2335035 : term198 = term192.
Proof. exact (MK_COMB (@lem2335034) (@lem2335029)). Qed.
Lemma lem2335037 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2335038 : term192 = term202.
Proof. exact (@lem2335037 (NUMERAL 0) term32). Qed.
Lemma lem2335039 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335040 (h1 : term125 = (BIT1 0)) : (term32 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2335041 : (term125 = (BIT1 0)) = ((term32 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335040 h1) (fun h1 : (term32 = (NUMERAL 0)) = False => @lem2335039)). Qed.
Lemma lem2335042 : (term32 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2335041) (@lem2335039)). Qed.
Lemma lem2335043 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2335044 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2335045 : term203 = (and True).
Proof. exact (MK_COMB (@lem2335044) (@lem2335043)). Qed.
Lemma lem2335046 : term202 = (True /\ False).
Proof. exact (MK_COMB (@lem2335045) (@lem2335042)). Qed.
Lemma lem2335048 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2335049 : term202 = False.
Proof. exact (TRANS (@lem2335046) (@lem2335048)). Qed.
Lemma lem2335050 : term192 = False.
Proof. exact (TRANS (@lem2335038) (@lem2335049)). Qed.
Lemma lem2335051 : term198 = False.
Proof. exact (TRANS (@lem2335035) (@lem2335050)). Qed.
Lemma lem2335052 : term195 = False.
Proof. exact (TRANS (@lem2335019) (@lem2335051)). Qed.
Lemma lem2335053 : term192 = False.
Proof. exact (TRANS (@lem2334996) (@lem2335052)). Qed.
Lemma lem2335054 : term191 = False.
Proof. exact (TRANS (@lem2334987) (@lem2335053)). Qed.
Lemma lem2335055 (y : int) (x : int) (z : int) (h1 : term112 y x z) : False.
Proof. exact (EQ_MP (@lem2335054) (@lem2334984 y x z h1)). Qed.
Lemma lem2335057 (y : int) (x : int) (z : int) (h1 : term112 y x z) : term112 y x z.
Proof. exact (h1). Qed.
Lemma lem2335058 (y : int) (x : int) (z : int) (h1 : term112 y x z) : (term112 y x z) = False.
Proof. exact (prop_ext (fun h2 : term112 y x z => @lem2335055 y x z h1) (fun h2 : False => @lem2335057 y x z h1)). Qed.
Lemma lem2335059 (y : int) (x : int) (z : int) (h1 : term112 y x z) : False.
Proof. exact (EQ_MP (@lem2335058 y x z h1) (@lem2335057 y x z h1)). Qed.
Lemma lem2335060 (y : int) (x : int) (h1 : term115 y x) : term115 y x.
Proof. exact (h1). Qed.
Lemma lem2335061 (y : int) (x : int) (h1 : term115 y x) : False.
Proof. exact (ex_elim (@lem2335060 y x h1) (fun z : int => fun h0 : term114 y x z => @lem2335059 y x z h0)). Qed.
Lemma lem2335062 (y : int) (x : int) (h1 : term47 y x) : term47 y x.
Proof. exact (h1). Qed.
Lemma lem2335063 (y : int) (x : int) (h1 : term47 y x) : term115 y x.
Proof. exact (EQ_MP (@lem2334315 y x) (@lem2335062 y x h1)). Qed.
Lemma lem2335064 (y : int) (x : int) (h1 : term47 y x) : (term115 y x) = False.
Proof. exact (prop_ext (fun h2 : term115 y x => @lem2335061 y x h2) (fun h2 : False => @lem2335063 y x h1)). Qed.
Lemma lem2335065 (y : int) (x : int) (h1 : term47 y x) : False.
Proof. exact (EQ_MP (@lem2335064 y x h1) (@lem2335063 y x h1)). Qed.
Lemma lem2335066 (y : int) (x : int) : term204 y x.
Proof. exact (fun h0 : term47 y x => @lem2335065 y x h0). Qed.
Lemma lem2335067 (y : int) (x : int) : term205 y x.
Proof. exact (@lem1386578 (term206 y x)). Qed.
Lemma lem2335070 (y : int) (x : int) : term206 y x.
Proof. exact (@lem2335067 y x (@lem2335066 y x)). Qed.
Lemma lem2335071 (y : int) (x : int) : (term45 y x) = (term18 y x).
Proof. exact (SYM (@lem2334022 y x)). Qed.
Lemma lem2335072 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2335073 (y : int) (x : int) : (term206 y x) = (term0 y x).
Proof. exact (MK_COMB (@lem2335072) (@lem2335071 y x)). Qed.
Lemma lem2335074 (y : int) (x : int) : term0 y x.
Proof. exact (EQ_MP (@lem2335073 y x) (@lem2335070 y x)). Qed.
Lemma lem2335075 (y : int) (x : int) : term1 y x.
Proof. exact (EQ_MP (@lem2333928 y x) (@lem2335074 y x)). Qed.
Lemma lem2335076 (y : int) (x : int) : (term1 y x) = ((term1 y x) = True).
Proof. exact (@lem7 (term1 y x)). Qed.
Lemma lem2335077 (y : int) (x : int) : (term1 y x) = True.
Proof. exact (EQ_MP (@lem2335076 y x) (@lem2335075 y x)). Qed.
Lemma lem2335078 (y : int) (x : int) : True = (term1 y x).
Proof. exact (SYM (@lem2335077 y x)). Qed.
Lemma lem2335079 (y : int) (x : int) : term1 y x.
Proof. exact (EQ_MP (@lem2335078 y x) (@lem0)). Qed.
Lemma lem2335080 (y : int) (x : int) (h1 : term19 y x) : term19 y x.
Proof. exact (h1). Qed.
Lemma lem2335081 (y : int) (x : int) (h1 : term19 y x) : term207 x y.
Proof. exact (@lem2335080 y x h1 (term23 y)). Qed.
Lemma lem2335082 (x : int) (y : int) : (term207 x y) = (term208 x y).
Proof. exact (eq_refl (term207 x y)). Qed.
Lemma lem2335083 (y : int) (x : int) (h1 : term19 y x) : term208 x y.
Proof. exact (EQ_MP (@lem2335082 x y) (@lem2335081 y x h1)). Qed.
Lemma lem2335084 (x : int) (y : int) : (term209 x y) = (term210 x y).
Proof. exact (@lem2318604 (term210 x y)). Qed.
Lemma lem2335100 (x : int) (y : int) : (term208 x y) = (term211 x y).
Proof. exact (@lem17265 (term212 y) (term213 x y)). Qed.
Lemma lem2335101 (x : int) (y : int) : (term214 x y) = (term214 x y).
Proof. exact (eq_refl (term214 x y)). Qed.
Lemma lem2335102 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2335103 (x : int) (y : int) : (term215 x y) = (term216 x y).
Proof. exact (MK_COMB (@lem2335102) (@lem2335100 x y)). Qed.
Lemma lem2335104 (x : int) (y : int) : (term217 x y) = (term218 x y).
Proof. exact (MK_COMB (@lem2335103 x y) (@lem2335101 x y)). Qed.
Lemma lem2335105 (x : int) (y : int) : (term219 x y) = (term217 x y).
Proof. exact (@lem17362 (term208 x y) (int_le x y)). Qed.
Lemma lem2335121 (x : int) (y : int) : (term219 x y) = (term218 x y).
Proof. exact (TRANS (@lem2335105 x y) (@lem2335104 x y)). Qed.
Lemma lem2335123 (y : int) (x : int) : (term38 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem2335124 (y : int) : (term220 y) = (term221 y).
Proof. exact (@lem2335123 (term23 y) y). Qed.
Lemma lem2335126 (x : int) (y : int) : (int_le x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2335127 (y : int) : (term221 y) = (term222 y).
Proof. exact (@lem2335126 (term23 y) y). Qed.
Lemma lem2335129 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2335130 (y : int) : (term26 y) = (term27 y).
Proof. exact (@lem2335129 y term28). Qed.
Lemma lem2335132 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2335133 : term30 = term31.
Proof. exact (@lem2335132 term32). Qed.
Lemma lem2335134 (y : int) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem2335135 (y : int) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem2335134 y) (@lem2335133)). Qed.
Lemma lem2335136 (y : int) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem2335130 y) (@lem2335135 y)). Qed.
Lemma lem2335137 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2335138 (y : int) : (term35 y) = (term36 y).
Proof. exact (MK_COMB (@lem2335137) (@lem2335136 y)). Qed.
Lemma lem2335139 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2335140 (y : int) : (term222 y) = (term223 y).
Proof. exact (MK_COMB (@lem2335138 y) (@lem2335139 y)). Qed.
Lemma lem2335141 (y : int) : (term221 y) = (term223 y).
Proof. exact (TRANS (@lem2335127 y) (@lem2335140 y)). Qed.
Lemma lem2335142 (y : int) : (term220 y) = (term223 y).
Proof. exact (TRANS (@lem2335124 y) (@lem2335141 y)). Qed.
Lemma lem2335144 (x : int) (y : int) : (int_lt x y) = (term21 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem2335145 (x : int) (y : int) : (term213 x y) = (term224 x y).
Proof. exact (@lem2335144 x (term23 y)). Qed.
Lemma lem2335147 (x : int) (y : int) : (int_le x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2335148 (x : int) (y : int) : (term224 x y) = (term225 x y).
Proof. exact (@lem2335147 (term23 x) (term23 y)). Qed.
Lemma lem2335150 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2335151 (x : int) : (term26 x) = (term27 x).
Proof. exact (@lem2335150 x term28). Qed.
Lemma lem2335153 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2335154 : term30 = term31.
Proof. exact (@lem2335153 term32). Qed.
Lemma lem2335155 (x : int) : (term33 x) = (term33 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem2335156 (x : int) : (term27 x) = (term34 x).
Proof. exact (MK_COMB (@lem2335155 x) (@lem2335154)). Qed.
Lemma lem2335157 (x : int) : (term26 x) = (term34 x).
Proof. exact (TRANS (@lem2335151 x) (@lem2335156 x)). Qed.
Lemma lem2335158 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2335159 (x : int) : (term35 x) = (term36 x).
Proof. exact (MK_COMB (@lem2335158) (@lem2335157 x)). Qed.
Lemma lem2335161 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2335162 (y : int) : (term26 y) = (term27 y).
Proof. exact (@lem2335161 y term28). Qed.
Lemma lem2335164 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2335165 : term30 = term31.
Proof. exact (@lem2335164 term32). Qed.
Lemma lem2335166 (y : int) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem2335167 (y : int) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem2335166 y) (@lem2335165)). Qed.
Lemma lem2335168 (y : int) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem2335162 y) (@lem2335167 y)). Qed.
Lemma lem2335169 (x : int) (y : int) : (term225 x y) = (term226 x y).
Proof. exact (MK_COMB (@lem2335159 x) (@lem2335168 y)). Qed.
Lemma lem2335170 (x : int) (y : int) : (term224 x y) = (term226 x y).
Proof. exact (TRANS (@lem2335148 x y) (@lem2335169 x y)). Qed.
Lemma lem2335171 (x : int) (y : int) : (term213 x y) = (term226 x y).
Proof. exact (TRANS (@lem2335145 x y) (@lem2335170 x y)). Qed.
Lemma lem2335172 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2335173 (y : int) : (term227 y) = (term228 y).
Proof. exact (MK_COMB (@lem2335172) (@lem2335142 y)). Qed.
Lemma lem2335174 (x : int) (y : int) : (term211 x y) = (term229 x y).
Proof. exact (MK_COMB (@lem2335173 y) (@lem2335171 x y)). Qed.
Lemma lem2335176 (y : int) (x : int) : (term214 x y) = (term21 y x).
Proof. exact (proj1 (@lem2318495 x y)). Qed.
Lemma lem2335178 (x : int) (y : int) : (int_le x y) = (term20 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem2335179 (y : int) (x : int) : (term21 y x) = (term22 y x).
Proof. exact (@lem2335178 (term23 y) x). Qed.
Lemma lem2335181 (x : int) (y : int) : (term24 x y) = (term25 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem2335182 (y : int) : (term26 y) = (term27 y).
Proof. exact (@lem2335181 y term28). Qed.
Lemma lem2335184 (n : nat) : (term29 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem2335185 : term30 = term31.
Proof. exact (@lem2335184 term32). Qed.
Lemma lem2335186 (y : int) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem2335187 (y : int) : (term27 y) = (term34 y).
Proof. exact (MK_COMB (@lem2335186 y) (@lem2335185)). Qed.
Lemma lem2335188 (y : int) : (term26 y) = (term34 y).
Proof. exact (TRANS (@lem2335182 y) (@lem2335187 y)). Qed.
Lemma lem2335189 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2335190 (y : int) : (term35 y) = (term36 y).
Proof. exact (MK_COMB (@lem2335189) (@lem2335188 y)). Qed.
Lemma lem2335191 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2335192 (y : int) (x : int) : (term22 y x) = (term37 y x).
Proof. exact (MK_COMB (@lem2335190 y) (@lem2335191 x)). Qed.
Lemma lem2335193 (y : int) (x : int) : (term21 y x) = (term37 y x).
Proof. exact (TRANS (@lem2335179 y x) (@lem2335192 y x)). Qed.
Lemma lem2335194 (y : int) (x : int) : (term214 x y) = (term37 y x).
Proof. exact (TRANS (@lem2335176 y x) (@lem2335193 y x)). Qed.
Lemma lem2335195 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2335196 (x : int) (y : int) : (term216 x y) = (term230 x y).
Proof. exact (MK_COMB (@lem2335195) (@lem2335174 x y)). Qed.
Lemma lem2335197 (y : int) (x : int) : (term218 x y) = (term231 y x).
Proof. exact (MK_COMB (@lem2335196 x y) (@lem2335194 y x)). Qed.
Lemma lem2335198 (y : int) (x : int) : (term219 x y) = (term231 y x).
Proof. exact (TRANS (@lem2335121 x y) (@lem2335197 y x)). Qed.
Lemma lem2335202 (t : Prop) : (term46 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem2335228 (y : int) (x : int) : (term232 y x) = (term231 y x).
Proof. exact (@lem2335202 (term231 y x)). Qed.
Lemma lem2335229 (y : int) : (term223 y) = (term233 y).
Proof. exact (@lem1988287 (real_of_int y) (term34 y)). Qed.
Lemma lem2335241 (y : int) : (term234 y) = (term235 y).
Proof. exact (@lem1982792 (real_of_int y) (term34 y)). Qed.
Lemma lem2335242 (y : int) : (term60 y) = (term61 y).
Proof. exact (@lem1982781 (real_of_int y) term62 term31). Qed.
Lemma lem2335244 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335245 : term31 = term64.
Proof. exact (@lem2335244 term32). Qed.
Lemma lem2335247 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2335248 : term62 = term67.
Proof. exact (@lem2335247 term32). Qed.
Lemma lem2335249 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2335250 : term68 = term69.
Proof. exact (MK_COMB (@lem2335249) (@lem2335248)). Qed.
Lemma lem2335251 : term70 = term71.
Proof. exact (MK_COMB (@lem2335250) (@lem2335245)). Qed.
Lemma lem2335252 : term71 = term72.
Proof. exact (@lem1981613 term62 term31 term31 term31). Qed.
Lemma lem2335254 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335255 : term75 = term76.
Proof. exact (@lem2335254 term32 term32). Qed.
Lemma lem2335256 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335257 : term78 = term32.
Proof. exact (EQ_MP (@lem2335256) (@lem940073)). Qed.
Lemma lem2335258 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335259 : term76 = term31.
Proof. exact (MK_COMB (@lem2335258) (@lem2335257)). Qed.
Lemma lem2335260 : term75 = term31.
Proof. exact (TRANS (@lem2335255) (@lem2335259)). Qed.
Lemma lem2335262 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335263 : term70 = term81.
Proof. exact (@lem2335262 term32 term32). Qed.
Lemma lem2335264 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335265 : term78 = term32.
Proof. exact (EQ_MP (@lem2335264) (@lem940073)). Qed.
Lemma lem2335266 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335267 : term76 = term31.
Proof. exact (MK_COMB (@lem2335266) (@lem2335265)). Qed.
Lemma lem2335268 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335269 : term81 = term62.
Proof. exact (MK_COMB (@lem2335268) (@lem2335267)). Qed.
Lemma lem2335270 : term70 = term62.
Proof. exact (TRANS (@lem2335263) (@lem2335269)). Qed.
Lemma lem2335271 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2335272 : term82 = term83.
Proof. exact (MK_COMB (@lem2335271) (@lem2335270)). Qed.
Lemma lem2335273 : term72 = term67.
Proof. exact (MK_COMB (@lem2335272) (@lem2335260)). Qed.
Lemma lem2335274 : term71 = term67.
Proof. exact (TRANS (@lem2335252) (@lem2335273)). Qed.
Lemma lem2335275 : term70 = term67.
Proof. exact (TRANS (@lem2335251) (@lem2335274)). Qed.
Lemma lem2335277 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2335278 : term67 = term62.
Proof. exact (@lem2335277 term62). Qed.
Lemma lem2335279 : term70 = term62.
Proof. exact (TRANS (@lem2335275) (@lem2335278)). Qed.
Lemma lem2335282 (y : int) : (term85 y) = (term85 y).
Proof. exact (eq_refl (term85 y)). Qed.
Lemma lem2335283 (y : int) : (term61 y) = (term86 y).
Proof. exact (MK_COMB (@lem2335282 y) (@lem2335279)). Qed.
Lemma lem2335284 (y : int) : (term60 y) = (term86 y).
Proof. exact (TRANS (@lem2335242 y) (@lem2335283 y)). Qed.
Lemma lem2335285 (y : int) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem2335286 (y : int) : (term235 y) = (term236 y).
Proof. exact (MK_COMB (@lem2335285 y) (@lem2335284 y)). Qed.
Lemma lem2335287 (y : int) : (term236 y) = (term185 y).
Proof. exact (@lem1982763 (real_of_int y) (term52 y) term62). Qed.
Lemma lem2335288 (y : int) : (term186 y) = (term157 y).
Proof. exact (@lem1982715 term62 (real_of_int y)). Qed.
Lemma lem2335290 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335291 : term31 = term64.
Proof. exact (@lem2335290 term32). Qed.
Lemma lem2335293 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2335294 : term62 = term67.
Proof. exact (@lem2335293 term32). Qed.
Lemma lem2335295 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2335296 : term158 = term159.
Proof. exact (MK_COMB (@lem2335295) (@lem2335294)). Qed.
Lemma lem2335297 : term160 = term161.
Proof. exact (MK_COMB (@lem2335296) (@lem2335291)). Qed.
Lemma lem2335298 : term162.
Proof. exact (@lem1981473 term62 term31 term31 term31 term55 term31). Qed.
Lemma lem2335300 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335301 : term117 = term124.
Proof. exact (@lem2335300 (NUMERAL 0) term32). Qed.
Lemma lem2335302 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335303 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335304 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335303 h1) (fun h1 : term124 = True => @lem2335302)). Qed.
Lemma lem2335305 : term124 = True.
Proof. exact (EQ_MP (@lem2335304) (@lem2335302)). Qed.
Lemma lem2335306 : term117 = True.
Proof. exact (TRANS (@lem2335301) (@lem2335305)). Qed.
Lemma lem2335307 : True = term117.
Proof. exact (SYM (@lem2335306)). Qed.
Lemma lem2335308 : term117.
Proof. exact (EQ_MP (@lem2335307) (@lem0)). Qed.
Lemma lem2335309 : term163.
Proof. exact (@lem2335298 (@lem2335308)). Qed.
Lemma lem2335311 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335312 : term117 = term124.
Proof. exact (@lem2335311 (NUMERAL 0) term32). Qed.
Lemma lem2335313 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335314 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335315 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335314 h1) (fun h1 : term124 = True => @lem2335313)). Qed.
Lemma lem2335316 : term124 = True.
Proof. exact (EQ_MP (@lem2335315) (@lem2335313)). Qed.
Lemma lem2335317 : term117 = True.
Proof. exact (TRANS (@lem2335312) (@lem2335316)). Qed.
Lemma lem2335318 : True = term117.
Proof. exact (SYM (@lem2335317)). Qed.
Lemma lem2335319 : term117.
Proof. exact (EQ_MP (@lem2335318) (@lem0)). Qed.
Lemma lem2335320 : term164.
Proof. exact (@lem2335309 (@lem2335319)). Qed.
Lemma lem2335322 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335323 : term117 = term124.
Proof. exact (@lem2335322 (NUMERAL 0) term32). Qed.
Lemma lem2335324 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335325 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335326 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335325 h1) (fun h1 : term124 = True => @lem2335324)). Qed.
Lemma lem2335327 : term124 = True.
Proof. exact (EQ_MP (@lem2335326) (@lem2335324)). Qed.
Lemma lem2335328 : term117 = True.
Proof. exact (TRANS (@lem2335323) (@lem2335327)). Qed.
Lemma lem2335329 : True = term117.
Proof. exact (SYM (@lem2335328)). Qed.
Lemma lem2335330 : term117.
Proof. exact (EQ_MP (@lem2335329) (@lem0)). Qed.
Lemma lem2335331 : term165.
Proof. exact (@lem2335320 (@lem2335330)). Qed.
Lemma lem2335333 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335334 : term75 = term76.
Proof. exact (@lem2335333 term32 term32). Qed.
Lemma lem2335335 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335336 : term78 = term32.
Proof. exact (EQ_MP (@lem2335335) (@lem940073)). Qed.
Lemma lem2335337 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335338 : term76 = term31.
Proof. exact (MK_COMB (@lem2335337) (@lem2335336)). Qed.
Lemma lem2335339 : term75 = term31.
Proof. exact (TRANS (@lem2335334) (@lem2335338)). Qed.
Lemma lem2335341 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335342 : term70 = term81.
Proof. exact (@lem2335341 term32 term32). Qed.
Lemma lem2335343 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335344 : term78 = term32.
Proof. exact (EQ_MP (@lem2335343) (@lem940073)). Qed.
Lemma lem2335345 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335346 : term76 = term31.
Proof. exact (MK_COMB (@lem2335345) (@lem2335344)). Qed.
Lemma lem2335347 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335348 : term81 = term62.
Proof. exact (MK_COMB (@lem2335347) (@lem2335346)). Qed.
Lemma lem2335349 : term70 = term62.
Proof. exact (TRANS (@lem2335342) (@lem2335348)). Qed.
Lemma lem2335350 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2335351 : term166 = term158.
Proof. exact (MK_COMB (@lem2335350) (@lem2335349)). Qed.
Lemma lem2335352 : term167 = term160.
Proof. exact (MK_COMB (@lem2335351) (@lem2335339)). Qed.
Lemma lem2335354 (m : nat) : (term168 m) = term55.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2335355 : term160 = term55.
Proof. exact (@lem2335354 term32). Qed.
Lemma lem2335356 : term167 = term55.
Proof. exact (TRANS (@lem2335352) (@lem2335355)). Qed.
Lemma lem2335357 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2335358 : term169 = term170.
Proof. exact (MK_COMB (@lem2335357) (@lem2335356)). Qed.
Lemma lem2335359 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2335360 : term171 = term129.
Proof. exact (MK_COMB (@lem2335358) (@lem2335359)). Qed.
Lemma lem2335362 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335363 : term129 = term55.
Proof. exact (@lem2335362 term32). Qed.
Lemma lem2335364 : term171 = term55.
Proof. exact (TRANS (@lem2335360) (@lem2335363)). Qed.
Lemma lem2335366 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335367 : term75 = term76.
Proof. exact (@lem2335366 term32 term32). Qed.
Lemma lem2335368 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335369 : term78 = term32.
Proof. exact (EQ_MP (@lem2335368) (@lem940073)). Qed.
Lemma lem2335370 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335371 : term76 = term31.
Proof. exact (MK_COMB (@lem2335370) (@lem2335369)). Qed.
Lemma lem2335372 : term75 = term31.
Proof. exact (TRANS (@lem2335367) (@lem2335371)). Qed.
Lemma lem2335373 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem2335374 : term172 = term129.
Proof. exact (MK_COMB (@lem2335373) (@lem2335372)). Qed.
Lemma lem2335376 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335377 : term129 = term55.
Proof. exact (@lem2335376 term32). Qed.
Lemma lem2335378 : term172 = term55.
Proof. exact (TRANS (@lem2335374) (@lem2335377)). Qed.
Lemma lem2335379 : term55 = term172.
Proof. exact (SYM (@lem2335378)). Qed.
Lemma lem2335380 : term171 = term172.
Proof. exact (TRANS (@lem2335364) (@lem2335379)). Qed.
Lemma lem2335381 : term161 = term118.
Proof. exact (@lem2335331 (@lem2335380)). Qed.
Lemma lem2335382 : term160 = term118.
Proof. exact (TRANS (@lem2335297) (@lem2335381)). Qed.
Lemma lem2335384 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2335385 : term118 = term55.
Proof. exact (@lem2335384 term55). Qed.
Lemma lem2335386 : term160 = term55.
Proof. exact (TRANS (@lem2335382) (@lem2335385)). Qed.
Lemma lem2335387 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2335388 : term173 = term170.
Proof. exact (MK_COMB (@lem2335387) (@lem2335386)). Qed.
Lemma lem2335389 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2335390 (y : int) : (term157 y) = (term174 y).
Proof. exact (MK_COMB (@lem2335388) (@lem2335389 y)). Qed.
Lemma lem2335391 (y : int) : (term186 y) = (term174 y).
Proof. exact (TRANS (@lem2335288 y) (@lem2335390 y)). Qed.
Lemma lem2335392 (y : int) : (term174 y) = term55.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2335393 (y : int) : (term186 y) = term55.
Proof. exact (TRANS (@lem2335391 y) (@lem2335392 y)). Qed.
Lemma lem2335394 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2335395 (y : int) : (term187 y) = term176.
Proof. exact (MK_COMB (@lem2335394) (@lem2335393 y)). Qed.
Lemma lem2335396 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem2335397 (y : int) : (term185 y) = term188.
Proof. exact (MK_COMB (@lem2335395 y) (@lem2335396)). Qed.
Lemma lem2335398 (y : int) : (term236 y) = term188.
Proof. exact (TRANS (@lem2335287 y) (@lem2335397 y)). Qed.
Lemma lem2335399 : term188 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem2335400 (y : int) : (term236 y) = term62.
Proof. exact (TRANS (@lem2335398 y) (@lem2335399)). Qed.
Lemma lem2335401 (y : int) : (term235 y) = term62.
Proof. exact (TRANS (@lem2335286 y) (@lem2335400 y)). Qed.
Lemma lem2335403 (y : int) : (term234 y) = term62.
Proof. exact (TRANS (@lem2335241 y) (@lem2335401 y)). Qed.
Lemma lem2335404 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2335405 (y : int) : (term237 y) = term190.
Proof. exact (MK_COMB (@lem2335404) (@lem2335403 y)). Qed.
Lemma lem2335406 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2335407 (y : int) : (term233 y) = term191.
Proof. exact (MK_COMB (@lem2335405 y) (@lem2335406)). Qed.
Lemma lem2335408 (y : int) : (term223 y) = term191.
Proof. exact (TRANS (@lem2335229 y) (@lem2335407 y)). Qed.
Lemma lem2335409 (y : int) (x : int) : (term226 x y) = (term238 y x).
Proof. exact (@lem1988287 (term34 y) (term34 x)). Qed.
Lemma lem2335427 (y : int) (x : int) : (term239 y x) = (term240 y x).
Proof. exact (@lem1982792 (term34 y) (term34 x)). Qed.
Lemma lem2335428 (x : int) : (term60 x) = (term61 x).
Proof. exact (@lem1982781 (real_of_int x) term62 term31). Qed.
Lemma lem2335430 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335431 : term31 = term64.
Proof. exact (@lem2335430 term32). Qed.
Lemma lem2335433 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2335434 : term62 = term67.
Proof. exact (@lem2335433 term32). Qed.
Lemma lem2335435 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2335436 : term68 = term69.
Proof. exact (MK_COMB (@lem2335435) (@lem2335434)). Qed.
Lemma lem2335437 : term70 = term71.
Proof. exact (MK_COMB (@lem2335436) (@lem2335431)). Qed.
Lemma lem2335438 : term71 = term72.
Proof. exact (@lem1981613 term62 term31 term31 term31). Qed.
Lemma lem2335440 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335441 : term75 = term76.
Proof. exact (@lem2335440 term32 term32). Qed.
Lemma lem2335442 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335443 : term78 = term32.
Proof. exact (EQ_MP (@lem2335442) (@lem940073)). Qed.
Lemma lem2335444 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335445 : term76 = term31.
Proof. exact (MK_COMB (@lem2335444) (@lem2335443)). Qed.
Lemma lem2335446 : term75 = term31.
Proof. exact (TRANS (@lem2335441) (@lem2335445)). Qed.
Lemma lem2335448 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335449 : term70 = term81.
Proof. exact (@lem2335448 term32 term32). Qed.
Lemma lem2335450 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335451 : term78 = term32.
Proof. exact (EQ_MP (@lem2335450) (@lem940073)). Qed.
Lemma lem2335452 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335453 : term76 = term31.
Proof. exact (MK_COMB (@lem2335452) (@lem2335451)). Qed.
Lemma lem2335454 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335455 : term81 = term62.
Proof. exact (MK_COMB (@lem2335454) (@lem2335453)). Qed.
Lemma lem2335456 : term70 = term62.
Proof. exact (TRANS (@lem2335449) (@lem2335455)). Qed.
Lemma lem2335457 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2335458 : term82 = term83.
Proof. exact (MK_COMB (@lem2335457) (@lem2335456)). Qed.
Lemma lem2335459 : term72 = term67.
Proof. exact (MK_COMB (@lem2335458) (@lem2335446)). Qed.
Lemma lem2335460 : term71 = term67.
Proof. exact (TRANS (@lem2335438) (@lem2335459)). Qed.
Lemma lem2335461 : term70 = term67.
Proof. exact (TRANS (@lem2335437) (@lem2335460)). Qed.
Lemma lem2335463 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2335464 : term67 = term62.
Proof. exact (@lem2335463 term62). Qed.
Lemma lem2335465 : term70 = term62.
Proof. exact (TRANS (@lem2335461) (@lem2335464)). Qed.
Lemma lem2335468 (x : int) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem2335469 (x : int) : (term61 x) = (term86 x).
Proof. exact (MK_COMB (@lem2335468 x) (@lem2335465)). Qed.
Lemma lem2335470 (x : int) : (term60 x) = (term86 x).
Proof. exact (TRANS (@lem2335428 x) (@lem2335469 x)). Qed.
Lemma lem2335471 (y : int) : (term241 y) = (term241 y).
Proof. exact (eq_refl (term241 y)). Qed.
Lemma lem2335472 (y : int) (x : int) : (term240 y x) = (term242 y x).
Proof. exact (MK_COMB (@lem2335471 y) (@lem2335470 x)). Qed.
Lemma lem2335473 (x : int) (y : int) : (term242 y x) = (term243 x y).
Proof. exact (@lem1982757 (term52 x) (term34 y) term62). Qed.
Lemma lem2335474 (y : int) : (term244 y) = (term245 y).
Proof. exact (@lem1982755 (real_of_int y) term31 term62). Qed.
Lemma lem2335476 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2335477 : term62 = term67.
Proof. exact (@lem2335476 term32). Qed.
Lemma lem2335479 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335480 : term31 = term64.
Proof. exact (@lem2335479 term32). Qed.
Lemma lem2335481 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2335482 : term246 = term247.
Proof. exact (MK_COMB (@lem2335481) (@lem2335480)). Qed.
Lemma lem2335483 : term248 = term249.
Proof. exact (MK_COMB (@lem2335482) (@lem2335477)). Qed.
Lemma lem2335484 : term250.
Proof. exact (@lem1981473 term31 term31 term62 term31 term55 term31). Qed.
Lemma lem2335486 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335487 : term117 = term124.
Proof. exact (@lem2335486 (NUMERAL 0) term32). Qed.
Lemma lem2335488 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335489 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335490 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335489 h1) (fun h1 : term124 = True => @lem2335488)). Qed.
Lemma lem2335491 : term124 = True.
Proof. exact (EQ_MP (@lem2335490) (@lem2335488)). Qed.
Lemma lem2335492 : term117 = True.
Proof. exact (TRANS (@lem2335487) (@lem2335491)). Qed.
Lemma lem2335493 : True = term117.
Proof. exact (SYM (@lem2335492)). Qed.
Lemma lem2335494 : term117.
Proof. exact (EQ_MP (@lem2335493) (@lem0)). Qed.
Lemma lem2335495 : term251.
Proof. exact (@lem2335484 (@lem2335494)). Qed.
Lemma lem2335497 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335498 : term117 = term124.
Proof. exact (@lem2335497 (NUMERAL 0) term32). Qed.
Lemma lem2335499 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335500 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335501 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335500 h1) (fun h1 : term124 = True => @lem2335499)). Qed.
Lemma lem2335502 : term124 = True.
Proof. exact (EQ_MP (@lem2335501) (@lem2335499)). Qed.
Lemma lem2335503 : term117 = True.
Proof. exact (TRANS (@lem2335498) (@lem2335502)). Qed.
Lemma lem2335504 : True = term117.
Proof. exact (SYM (@lem2335503)). Qed.
Lemma lem2335505 : term117.
Proof. exact (EQ_MP (@lem2335504) (@lem0)). Qed.
Lemma lem2335506 : term252.
Proof. exact (@lem2335495 (@lem2335505)). Qed.
Lemma lem2335508 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335509 : term117 = term124.
Proof. exact (@lem2335508 (NUMERAL 0) term32). Qed.
Lemma lem2335510 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335511 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335512 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335511 h1) (fun h1 : term124 = True => @lem2335510)). Qed.
Lemma lem2335513 : term124 = True.
Proof. exact (EQ_MP (@lem2335512) (@lem2335510)). Qed.
Lemma lem2335514 : term117 = True.
Proof. exact (TRANS (@lem2335509) (@lem2335513)). Qed.
Lemma lem2335515 : True = term117.
Proof. exact (SYM (@lem2335514)). Qed.
Lemma lem2335516 : term117.
Proof. exact (EQ_MP (@lem2335515) (@lem0)). Qed.
Lemma lem2335517 : term253.
Proof. exact (@lem2335506 (@lem2335516)). Qed.
Lemma lem2335519 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335520 : term70 = term81.
Proof. exact (@lem2335519 term32 term32). Qed.
Lemma lem2335521 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335522 : term78 = term32.
Proof. exact (EQ_MP (@lem2335521) (@lem940073)). Qed.
Lemma lem2335523 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335524 : term76 = term31.
Proof. exact (MK_COMB (@lem2335523) (@lem2335522)). Qed.
Lemma lem2335525 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335526 : term81 = term62.
Proof. exact (MK_COMB (@lem2335525) (@lem2335524)). Qed.
Lemma lem2335527 : term70 = term62.
Proof. exact (TRANS (@lem2335520) (@lem2335526)). Qed.
Lemma lem2335529 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335530 : term75 = term76.
Proof. exact (@lem2335529 term32 term32). Qed.
Lemma lem2335531 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335532 : term78 = term32.
Proof. exact (EQ_MP (@lem2335531) (@lem940073)). Qed.
Lemma lem2335533 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335534 : term76 = term31.
Proof. exact (MK_COMB (@lem2335533) (@lem2335532)). Qed.
Lemma lem2335535 : term75 = term31.
Proof. exact (TRANS (@lem2335530) (@lem2335534)). Qed.
Lemma lem2335536 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2335537 : term254 = term246.
Proof. exact (MK_COMB (@lem2335536) (@lem2335535)). Qed.
Lemma lem2335538 : term255 = term248.
Proof. exact (MK_COMB (@lem2335537) (@lem2335527)). Qed.
Lemma lem2335540 (m : nat) : (term256 m) = term55.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem2335541 : term248 = term55.
Proof. exact (@lem2335540 term32). Qed.
Lemma lem2335542 : term255 = term55.
Proof. exact (TRANS (@lem2335538) (@lem2335541)). Qed.
Lemma lem2335543 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2335544 : term257 = term170.
Proof. exact (MK_COMB (@lem2335543) (@lem2335542)). Qed.
Lemma lem2335545 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2335546 : term258 = term129.
Proof. exact (MK_COMB (@lem2335544) (@lem2335545)). Qed.
Lemma lem2335548 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335549 : term129 = term55.
Proof. exact (@lem2335548 term32). Qed.
Lemma lem2335550 : term258 = term55.
Proof. exact (TRANS (@lem2335546) (@lem2335549)). Qed.
Lemma lem2335552 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335553 : term75 = term76.
Proof. exact (@lem2335552 term32 term32). Qed.
Lemma lem2335554 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335555 : term78 = term32.
Proof. exact (EQ_MP (@lem2335554) (@lem940073)). Qed.
Lemma lem2335556 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335557 : term76 = term31.
Proof. exact (MK_COMB (@lem2335556) (@lem2335555)). Qed.
Lemma lem2335558 : term75 = term31.
Proof. exact (TRANS (@lem2335553) (@lem2335557)). Qed.
Lemma lem2335559 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem2335560 : term172 = term129.
Proof. exact (MK_COMB (@lem2335559) (@lem2335558)). Qed.
Lemma lem2335562 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335563 : term129 = term55.
Proof. exact (@lem2335562 term32). Qed.
Lemma lem2335564 : term172 = term55.
Proof. exact (TRANS (@lem2335560) (@lem2335563)). Qed.
Lemma lem2335565 : term55 = term172.
Proof. exact (SYM (@lem2335564)). Qed.
Lemma lem2335566 : term258 = term172.
Proof. exact (TRANS (@lem2335550) (@lem2335565)). Qed.
Lemma lem2335567 : term249 = term118.
Proof. exact (@lem2335517 (@lem2335566)). Qed.
Lemma lem2335568 : term248 = term118.
Proof. exact (TRANS (@lem2335483) (@lem2335567)). Qed.
Lemma lem2335570 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2335571 : term118 = term55.
Proof. exact (@lem2335570 term55). Qed.
Lemma lem2335572 : term248 = term55.
Proof. exact (TRANS (@lem2335568) (@lem2335571)). Qed.
Lemma lem2335573 (y : int) : (term33 y) = (term33 y).
Proof. exact (eq_refl (term33 y)). Qed.
Lemma lem2335574 (y : int) : (term245 y) = (term259 y).
Proof. exact (MK_COMB (@lem2335573 y) (@lem2335572)). Qed.
Lemma lem2335575 (y : int) : (term244 y) = (term259 y).
Proof. exact (TRANS (@lem2335474 y) (@lem2335574 y)). Qed.
Lemma lem2335576 (y : int) : (term259 y) = (real_of_int y).
Proof. exact (@lem1982723 (real_of_int y)). Qed.
Lemma lem2335577 (y : int) : (term244 y) = (real_of_int y).
Proof. exact (TRANS (@lem2335575 y) (@lem2335576 y)). Qed.
Lemma lem2335578 (x : int) : (term85 x) = (term85 x).
Proof. exact (eq_refl (term85 x)). Qed.
Lemma lem2335579 (x : int) (y : int) : (term243 x y) = (term51 x y).
Proof. exact (MK_COMB (@lem2335578 x) (@lem2335577 y)). Qed.
Lemma lem2335580 (x : int) (y : int) : (term242 y x) = (term51 x y).
Proof. exact (TRANS (@lem2335473 x y) (@lem2335579 x y)). Qed.
Lemma lem2335581 (x : int) (y : int) : (term240 y x) = (term51 x y).
Proof. exact (TRANS (@lem2335472 y x) (@lem2335580 x y)). Qed.
Lemma lem2335583 (x : int) (y : int) : (term239 y x) = (term51 x y).
Proof. exact (TRANS (@lem2335427 y x) (@lem2335581 x y)). Qed.
Lemma lem2335584 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2335585 (x : int) (y : int) : (term260 y x) = (term54 x y).
Proof. exact (MK_COMB (@lem2335584) (@lem2335583 x y)). Qed.
Lemma lem2335586 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2335587 (x : int) (y : int) : (term238 y x) = (term56 x y).
Proof. exact (MK_COMB (@lem2335585 x y) (@lem2335586)). Qed.
Lemma lem2335588 (x : int) (y : int) : (term226 x y) = (term56 x y).
Proof. exact (TRANS (@lem2335409 y x) (@lem2335587 x y)). Qed.
Lemma lem2335589 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem2335590 (y : int) : (term228 y) = term261.
Proof. exact (MK_COMB (@lem2335589) (@lem2335408 y)). Qed.
Lemma lem2335591 (x : int) (y : int) : (term229 x y) = (term262 x y).
Proof. exact (MK_COMB (@lem2335590 y) (@lem2335588 x y)). Qed.
Lemma lem2335592 (x : int) (y : int) : (term37 y x) = (term57 x y).
Proof. exact (@lem1988287 (real_of_int x) (term34 y)). Qed.
Lemma lem2335604 (x : int) (y : int) : (term58 x y) = (term59 x y).
Proof. exact (@lem1982792 (real_of_int x) (term34 y)). Qed.
Lemma lem2335605 (y : int) : (term60 y) = (term61 y).
Proof. exact (@lem1982781 (real_of_int y) term62 term31). Qed.
Lemma lem2335607 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335608 : term31 = term64.
Proof. exact (@lem2335607 term32). Qed.
Lemma lem2335610 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2335611 : term62 = term67.
Proof. exact (@lem2335610 term32). Qed.
Lemma lem2335612 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2335613 : term68 = term69.
Proof. exact (MK_COMB (@lem2335612) (@lem2335611)). Qed.
Lemma lem2335614 : term70 = term71.
Proof. exact (MK_COMB (@lem2335613) (@lem2335608)). Qed.
Lemma lem2335615 : term71 = term72.
Proof. exact (@lem1981613 term62 term31 term31 term31). Qed.
Lemma lem2335617 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335618 : term75 = term76.
Proof. exact (@lem2335617 term32 term32). Qed.
Lemma lem2335619 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335620 : term78 = term32.
Proof. exact (EQ_MP (@lem2335619) (@lem940073)). Qed.
Lemma lem2335621 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335622 : term76 = term31.
Proof. exact (MK_COMB (@lem2335621) (@lem2335620)). Qed.
Lemma lem2335623 : term75 = term31.
Proof. exact (TRANS (@lem2335618) (@lem2335622)). Qed.
Lemma lem2335625 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335626 : term70 = term81.
Proof. exact (@lem2335625 term32 term32). Qed.
Lemma lem2335627 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335628 : term78 = term32.
Proof. exact (EQ_MP (@lem2335627) (@lem940073)). Qed.
Lemma lem2335629 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335630 : term76 = term31.
Proof. exact (MK_COMB (@lem2335629) (@lem2335628)). Qed.
Lemma lem2335631 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335632 : term81 = term62.
Proof. exact (MK_COMB (@lem2335631) (@lem2335630)). Qed.
Lemma lem2335633 : term70 = term62.
Proof. exact (TRANS (@lem2335626) (@lem2335632)). Qed.
Lemma lem2335634 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem2335635 : term82 = term83.
Proof. exact (MK_COMB (@lem2335634) (@lem2335633)). Qed.
Lemma lem2335636 : term72 = term67.
Proof. exact (MK_COMB (@lem2335635) (@lem2335623)). Qed.
Lemma lem2335637 : term71 = term67.
Proof. exact (TRANS (@lem2335615) (@lem2335636)). Qed.
Lemma lem2335638 : term70 = term67.
Proof. exact (TRANS (@lem2335614) (@lem2335637)). Qed.
Lemma lem2335640 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem2335641 : term67 = term62.
Proof. exact (@lem2335640 term62). Qed.
Lemma lem2335642 : term70 = term62.
Proof. exact (TRANS (@lem2335638) (@lem2335641)). Qed.
Lemma lem2335645 (y : int) : (term85 y) = (term85 y).
Proof. exact (eq_refl (term85 y)). Qed.
Lemma lem2335646 (y : int) : (term61 y) = (term86 y).
Proof. exact (MK_COMB (@lem2335645 y) (@lem2335642)). Qed.
Lemma lem2335647 (y : int) : (term60 y) = (term86 y).
Proof. exact (TRANS (@lem2335605 y) (@lem2335646 y)). Qed.
Lemma lem2335648 (x : int) : (term33 x) = (term33 x).
Proof. exact (eq_refl (term33 x)). Qed.
Lemma lem2335651 (x : int) (y : int) : (term59 x y) = (term87 x y).
Proof. exact (MK_COMB (@lem2335648 x) (@lem2335647 y)). Qed.
Lemma lem2335653 (x : int) (y : int) : (term58 x y) = (term87 x y).
Proof. exact (TRANS (@lem2335604 x y) (@lem2335651 x y)). Qed.
Lemma lem2335654 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2335655 (x : int) (y : int) : (term89 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem2335654) (@lem2335653 x y)). Qed.
Lemma lem2335656 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2335657 (x : int) (y : int) : (term57 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem2335655 x y) (@lem2335656)). Qed.
Lemma lem2335658 (x : int) (y : int) : (term37 y x) = (term264 x y).
Proof. exact (TRANS (@lem2335592 x y) (@lem2335657 x y)). Qed.
Lemma lem2335659 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2335660 (x : int) (y : int) : (term230 x y) = (term265 x y).
Proof. exact (MK_COMB (@lem2335659) (@lem2335591 x y)). Qed.
Lemma lem2335661 (x : int) (y : int) : (term231 y x) = (term266 x y).
Proof. exact (MK_COMB (@lem2335660 x y) (@lem2335658 x y)). Qed.
Lemma lem2335668 (x : int) (y : int) : (term232 y x) = (term266 x y).
Proof. exact (TRANS (@lem2335228 y x) (@lem2335661 x y)). Qed.
Lemma lem2335685 (x : int) (y : int) : (term266 x y) = (term267 x y).
Proof. exact (@lem19367 term191 (term56 x y) (term264 x y)). Qed.
Lemma lem2335686 (x : int) (y : int) : (term232 y x) = (term267 x y).
Proof. exact (TRANS (@lem2335668 x y) (@lem2335685 x y)). Qed.
Lemma lem2335696 (x : int) (y : int) (h1 : term267 x y) : term267 x y.
Proof. exact (h1). Qed.
Lemma lem2335697 (x : int) (y : int) (h1 : term268 x y) : term268 x y.
Proof. exact (h1). Qed.
Lemma lem2335699 (x : int) (y : int) (h1 : term268 x y) : term191.
Proof. exact (proj1 (@lem2335697 x y h1)). Qed.
Lemma lem2335701 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2335702 : term191 = term192.
Proof. exact (@lem2335701 term55 term62). Qed.
Lemma lem2335704 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2335705 : term62 = term67.
Proof. exact (@lem2335704 term32). Qed.
Lemma lem2335707 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335708 : term55 = term118.
Proof. exact (@lem2335707 (NUMERAL 0)). Qed.
Lemma lem2335709 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2335710 : term193 = term194.
Proof. exact (MK_COMB (@lem2335709) (@lem2335708)). Qed.
Lemma lem2335711 : term192 = term195.
Proof. exact (MK_COMB (@lem2335710) (@lem2335705)). Qed.
Lemma lem2335712 : term196.
Proof. exact (@lem1980026 term55 term31 term62 term31). Qed.
Lemma lem2335714 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335715 : term117 = term124.
Proof. exact (@lem2335714 (NUMERAL 0) term32). Qed.
Lemma lem2335716 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335717 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335718 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335717 h1) (fun h1 : term124 = True => @lem2335716)). Qed.
Lemma lem2335719 : term124 = True.
Proof. exact (EQ_MP (@lem2335718) (@lem2335716)). Qed.
Lemma lem2335720 : term117 = True.
Proof. exact (TRANS (@lem2335715) (@lem2335719)). Qed.
Lemma lem2335721 : True = term117.
Proof. exact (SYM (@lem2335720)). Qed.
Lemma lem2335722 : term117.
Proof. exact (EQ_MP (@lem2335721) (@lem0)). Qed.
Lemma lem2335723 : term197.
Proof. exact (@lem2335712 (@lem2335722)). Qed.
Lemma lem2335725 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335726 : term117 = term124.
Proof. exact (@lem2335725 (NUMERAL 0) term32). Qed.
Lemma lem2335727 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335728 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335729 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335728 h1) (fun h1 : term124 = True => @lem2335727)). Qed.
Lemma lem2335730 : term124 = True.
Proof. exact (EQ_MP (@lem2335729) (@lem2335727)). Qed.
Lemma lem2335731 : term117 = True.
Proof. exact (TRANS (@lem2335726) (@lem2335730)). Qed.
Lemma lem2335732 : True = term117.
Proof. exact (SYM (@lem2335731)). Qed.
Lemma lem2335733 : term117.
Proof. exact (EQ_MP (@lem2335732) (@lem0)). Qed.
Lemma lem2335734 : term195 = term198.
Proof. exact (@lem2335723 (@lem2335733)). Qed.
Lemma lem2335736 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335737 : term70 = term81.
Proof. exact (@lem2335736 term32 term32). Qed.
Lemma lem2335738 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335739 : term78 = term32.
Proof. exact (EQ_MP (@lem2335738) (@lem940073)). Qed.
Lemma lem2335740 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335741 : term76 = term31.
Proof. exact (MK_COMB (@lem2335740) (@lem2335739)). Qed.
Lemma lem2335742 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335743 : term81 = term62.
Proof. exact (MK_COMB (@lem2335742) (@lem2335741)). Qed.
Lemma lem2335744 : term70 = term62.
Proof. exact (TRANS (@lem2335737) (@lem2335743)). Qed.
Lemma lem2335746 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335747 : term129 = term55.
Proof. exact (@lem2335746 term32). Qed.
Lemma lem2335748 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2335749 : term199 = term193.
Proof. exact (MK_COMB (@lem2335748) (@lem2335747)). Qed.
Lemma lem2335750 : term198 = term192.
Proof. exact (MK_COMB (@lem2335749) (@lem2335744)). Qed.
Lemma lem2335752 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2335753 : term192 = term202.
Proof. exact (@lem2335752 (NUMERAL 0) term32). Qed.
Lemma lem2335754 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335755 (h1 : term125 = (BIT1 0)) : (term32 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2335756 : (term125 = (BIT1 0)) = ((term32 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335755 h1) (fun h1 : (term32 = (NUMERAL 0)) = False => @lem2335754)). Qed.
Lemma lem2335757 : (term32 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2335756) (@lem2335754)). Qed.
Lemma lem2335758 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2335759 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2335760 : term203 = (and True).
Proof. exact (MK_COMB (@lem2335759) (@lem2335758)). Qed.
Lemma lem2335761 : term202 = (True /\ False).
Proof. exact (MK_COMB (@lem2335760) (@lem2335757)). Qed.
Lemma lem2335763 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2335764 : term202 = False.
Proof. exact (TRANS (@lem2335761) (@lem2335763)). Qed.
Lemma lem2335765 : term192 = False.
Proof. exact (TRANS (@lem2335753) (@lem2335764)). Qed.
Lemma lem2335766 : term198 = False.
Proof. exact (TRANS (@lem2335750) (@lem2335765)). Qed.
Lemma lem2335767 : term195 = False.
Proof. exact (TRANS (@lem2335734) (@lem2335766)). Qed.
Lemma lem2335768 : term192 = False.
Proof. exact (TRANS (@lem2335711) (@lem2335767)). Qed.
Lemma lem2335769 : term191 = False.
Proof. exact (TRANS (@lem2335702) (@lem2335768)). Qed.
Lemma lem2335770 (x : int) (y : int) (h1 : term268 x y) : False.
Proof. exact (EQ_MP (@lem2335769) (@lem2335699 x y h1)). Qed.
Lemma lem2335771 (x : int) (y : int) (h1 : term269 x y) : term269 x y.
Proof. exact (h1). Qed.
Lemma lem2335772 (x : int) (y : int) (h1 : term269 x y) : term264 x y.
Proof. exact (proj2 (@lem2335771 x y h1)). Qed.
Lemma lem2335773 (x : int) (y : int) (h1 : term269 x y) : term56 x y.
Proof. exact (proj1 (@lem2335771 x y h1)). Qed.
Lemma lem2335775 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2335776 : term116 = term117.
Proof. exact (@lem2335775 term55 term31). Qed.
Lemma lem2335778 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335779 : term31 = term64.
Proof. exact (@lem2335778 term32). Qed.
Lemma lem2335781 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335782 : term55 = term118.
Proof. exact (@lem2335781 (NUMERAL 0)). Qed.
Lemma lem2335783 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2335784 : term119 = term120.
Proof. exact (MK_COMB (@lem2335783) (@lem2335782)). Qed.
Lemma lem2335785 : term117 = term121.
Proof. exact (MK_COMB (@lem2335784) (@lem2335779)). Qed.
Lemma lem2335786 : term122.
Proof. exact (@lem1980255 term55 term31 term31 term31). Qed.
Lemma lem2335788 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335789 : term117 = term124.
Proof. exact (@lem2335788 (NUMERAL 0) term32). Qed.
Lemma lem2335790 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335791 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335792 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335791 h1) (fun h1 : term124 = True => @lem2335790)). Qed.
Lemma lem2335793 : term124 = True.
Proof. exact (EQ_MP (@lem2335792) (@lem2335790)). Qed.
Lemma lem2335794 : term117 = True.
Proof. exact (TRANS (@lem2335789) (@lem2335793)). Qed.
Lemma lem2335795 : True = term117.
Proof. exact (SYM (@lem2335794)). Qed.
Lemma lem2335796 : term117.
Proof. exact (EQ_MP (@lem2335795) (@lem0)). Qed.
Lemma lem2335797 : term126.
Proof. exact (@lem2335786 (@lem2335796)). Qed.
Lemma lem2335799 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335800 : term117 = term124.
Proof. exact (@lem2335799 (NUMERAL 0) term32). Qed.
Lemma lem2335801 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335802 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335803 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335802 h1) (fun h1 : term124 = True => @lem2335801)). Qed.
Lemma lem2335804 : term124 = True.
Proof. exact (EQ_MP (@lem2335803) (@lem2335801)). Qed.
Lemma lem2335805 : term117 = True.
Proof. exact (TRANS (@lem2335800) (@lem2335804)). Qed.
Lemma lem2335806 : True = term117.
Proof. exact (SYM (@lem2335805)). Qed.
Lemma lem2335807 : term117.
Proof. exact (EQ_MP (@lem2335806) (@lem0)). Qed.
Lemma lem2335808 : term121 = term127.
Proof. exact (@lem2335797 (@lem2335807)). Qed.
Lemma lem2335810 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335811 : term75 = term76.
Proof. exact (@lem2335810 term32 term32). Qed.
Lemma lem2335812 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335813 : term78 = term32.
Proof. exact (EQ_MP (@lem2335812) (@lem940073)). Qed.
Lemma lem2335814 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335815 : term76 = term31.
Proof. exact (MK_COMB (@lem2335814) (@lem2335813)). Qed.
Lemma lem2335816 : term75 = term31.
Proof. exact (TRANS (@lem2335811) (@lem2335815)). Qed.
Lemma lem2335818 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335819 : term129 = term55.
Proof. exact (@lem2335818 term32). Qed.
Lemma lem2335820 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2335821 : term130 = term119.
Proof. exact (MK_COMB (@lem2335820) (@lem2335819)). Qed.
Lemma lem2335822 : term127 = term117.
Proof. exact (MK_COMB (@lem2335821) (@lem2335816)). Qed.
Lemma lem2335824 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335825 : term117 = term124.
Proof. exact (@lem2335824 (NUMERAL 0) term32). Qed.
Lemma lem2335826 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335827 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335828 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335827 h1) (fun h1 : term124 = True => @lem2335826)). Qed.
Lemma lem2335829 : term124 = True.
Proof. exact (EQ_MP (@lem2335828) (@lem2335826)). Qed.
Lemma lem2335830 : term117 = True.
Proof. exact (TRANS (@lem2335825) (@lem2335829)). Qed.
Lemma lem2335831 : term127 = True.
Proof. exact (TRANS (@lem2335822) (@lem2335830)). Qed.
Lemma lem2335832 : term121 = True.
Proof. exact (TRANS (@lem2335808) (@lem2335831)). Qed.
Lemma lem2335833 : term117 = True.
Proof. exact (TRANS (@lem2335785) (@lem2335832)). Qed.
Lemma lem2335834 : term116 = True.
Proof. exact (TRANS (@lem2335776) (@lem2335833)). Qed.
Lemma lem2335835 : True = term116.
Proof. exact (SYM (@lem2335834)). Qed.
Lemma lem2335836 : term116.
Proof. exact (EQ_MP (@lem2335835) (@lem0)). Qed.
Lemma lem2335837 (x : int) (y : int) (h1 : term269 x y) : term137 x y.
Proof. exact (conj (@lem2335836) (@lem2335773 x y h1)). Qed.
Lemma lem2335839 (x : real) (y : real) : term132 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2335840 (x : int) (y : int) : term138 x y.
Proof. exact (@lem2335839 term31 (term51 x y)). Qed.
Lemma lem2335841 (x : int) (y : int) (h1 : term269 x y) : term139 x y.
Proof. exact (@lem2335840 x y (@lem2335837 x y h1)). Qed.
Lemma lem2335842 (x : int) (y : int) : (term140 x y) = (term51 x y).
Proof. exact (@lem1982733 (term51 x y)). Qed.
Lemma lem2335843 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2335844 (x : int) (y : int) : (term141 x y) = (term54 x y).
Proof. exact (MK_COMB (@lem2335843) (@lem2335842 x y)). Qed.
Lemma lem2335845 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2335846 (x : int) (y : int) : (term139 x y) = (term56 x y).
Proof. exact (MK_COMB (@lem2335844 x y) (@lem2335845)). Qed.
Lemma lem2335847 (x : int) (y : int) (h1 : term269 x y) : term56 x y.
Proof. exact (EQ_MP (@lem2335846 x y) (@lem2335841 x y h1)). Qed.
Lemma lem2335849 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem2335850 : term116 = term117.
Proof. exact (@lem2335849 term55 term31). Qed.
Lemma lem2335852 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335853 : term31 = term64.
Proof. exact (@lem2335852 term32). Qed.
Lemma lem2335855 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335856 : term55 = term118.
Proof. exact (@lem2335855 (NUMERAL 0)). Qed.
Lemma lem2335857 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2335858 : term119 = term120.
Proof. exact (MK_COMB (@lem2335857) (@lem2335856)). Qed.
Lemma lem2335859 : term117 = term121.
Proof. exact (MK_COMB (@lem2335858) (@lem2335853)). Qed.
Lemma lem2335860 : term122.
Proof. exact (@lem1980255 term55 term31 term31 term31). Qed.
Lemma lem2335862 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335863 : term117 = term124.
Proof. exact (@lem2335862 (NUMERAL 0) term32). Qed.
Lemma lem2335864 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335865 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335866 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335865 h1) (fun h1 : term124 = True => @lem2335864)). Qed.
Lemma lem2335867 : term124 = True.
Proof. exact (EQ_MP (@lem2335866) (@lem2335864)). Qed.
Lemma lem2335868 : term117 = True.
Proof. exact (TRANS (@lem2335863) (@lem2335867)). Qed.
Lemma lem2335869 : True = term117.
Proof. exact (SYM (@lem2335868)). Qed.
Lemma lem2335870 : term117.
Proof. exact (EQ_MP (@lem2335869) (@lem0)). Qed.
Lemma lem2335871 : term126.
Proof. exact (@lem2335860 (@lem2335870)). Qed.
Lemma lem2335873 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335874 : term117 = term124.
Proof. exact (@lem2335873 (NUMERAL 0) term32). Qed.
Lemma lem2335875 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335876 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335877 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335876 h1) (fun h1 : term124 = True => @lem2335875)). Qed.
Lemma lem2335878 : term124 = True.
Proof. exact (EQ_MP (@lem2335877) (@lem2335875)). Qed.
Lemma lem2335879 : term117 = True.
Proof. exact (TRANS (@lem2335874) (@lem2335878)). Qed.
Lemma lem2335880 : True = term117.
Proof. exact (SYM (@lem2335879)). Qed.
Lemma lem2335881 : term117.
Proof. exact (EQ_MP (@lem2335880) (@lem0)). Qed.
Lemma lem2335882 : term121 = term127.
Proof. exact (@lem2335871 (@lem2335881)). Qed.
Lemma lem2335884 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335885 : term75 = term76.
Proof. exact (@lem2335884 term32 term32). Qed.
Lemma lem2335886 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335887 : term78 = term32.
Proof. exact (EQ_MP (@lem2335886) (@lem940073)). Qed.
Lemma lem2335888 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335889 : term76 = term31.
Proof. exact (MK_COMB (@lem2335888) (@lem2335887)). Qed.
Lemma lem2335890 : term75 = term31.
Proof. exact (TRANS (@lem2335885) (@lem2335889)). Qed.
Lemma lem2335892 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2335893 : term129 = term55.
Proof. exact (@lem2335892 term32). Qed.
Lemma lem2335894 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem2335895 : term130 = term119.
Proof. exact (MK_COMB (@lem2335894) (@lem2335893)). Qed.
Lemma lem2335896 : term127 = term117.
Proof. exact (MK_COMB (@lem2335895) (@lem2335890)). Qed.
Lemma lem2335898 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335899 : term117 = term124.
Proof. exact (@lem2335898 (NUMERAL 0) term32). Qed.
Lemma lem2335900 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335901 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335902 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335901 h1) (fun h1 : term124 = True => @lem2335900)). Qed.
Lemma lem2335903 : term124 = True.
Proof. exact (EQ_MP (@lem2335902) (@lem2335900)). Qed.
Lemma lem2335904 : term117 = True.
Proof. exact (TRANS (@lem2335899) (@lem2335903)). Qed.
Lemma lem2335905 : term127 = True.
Proof. exact (TRANS (@lem2335896) (@lem2335904)). Qed.
Lemma lem2335906 : term121 = True.
Proof. exact (TRANS (@lem2335882) (@lem2335905)). Qed.
Lemma lem2335907 : term117 = True.
Proof. exact (TRANS (@lem2335859) (@lem2335906)). Qed.
Lemma lem2335908 : term116 = True.
Proof. exact (TRANS (@lem2335850) (@lem2335907)). Qed.
Lemma lem2335909 : True = term116.
Proof. exact (SYM (@lem2335908)). Qed.
Lemma lem2335910 : term116.
Proof. exact (EQ_MP (@lem2335909) (@lem0)). Qed.
Lemma lem2335911 (x : int) (y : int) (h1 : term269 x y) : term270 x y.
Proof. exact (conj (@lem2335910) (@lem2335772 x y h1)). Qed.
Lemma lem2335913 (x : real) (y : real) : term132 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem2335914 (x : int) (y : int) : term271 x y.
Proof. exact (@lem2335913 term31 (term87 x y)). Qed.
Lemma lem2335915 (x : int) (y : int) (h1 : term269 x y) : term272 x y.
Proof. exact (@lem2335914 x y (@lem2335911 x y h1)). Qed.
Lemma lem2335916 (x : int) (y : int) : (term273 x y) = (term87 x y).
Proof. exact (@lem1982733 (term87 x y)). Qed.
Lemma lem2335917 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2335918 (x : int) (y : int) : (term274 x y) = (term263 x y).
Proof. exact (MK_COMB (@lem2335917) (@lem2335916 x y)). Qed.
Lemma lem2335919 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2335920 (x : int) (y : int) : (term272 x y) = (term264 x y).
Proof. exact (MK_COMB (@lem2335918 x y) (@lem2335919)). Qed.
Lemma lem2335921 (x : int) (y : int) (h1 : term269 x y) : term264 x y.
Proof. exact (EQ_MP (@lem2335920 x y) (@lem2335915 x y h1)). Qed.
Lemma lem2335922 (x : int) (y : int) (h1 : term269 x y) : term275 x y.
Proof. exact (conj (@lem2335921 x y h1) (@lem2335847 x y h1)). Qed.
Lemma lem2335924 (x : real) (y : real) : term148 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem2335925 (x : int) (y : int) : term276 x y.
Proof. exact (@lem2335924 (term87 x y) (term51 x y)). Qed.
Lemma lem2335926 (x : int) (y : int) (h1 : term269 x y) : term277 x y.
Proof. exact (@lem2335925 x y (@lem2335922 x y h1)). Qed.
Lemma lem2335927 (x : int) (y : int) : (term278 x y) = (term279 x y).
Proof. exact (@lem1982753 (real_of_int x) (term52 x) (term86 y) (real_of_int y)). Qed.
Lemma lem2335928 (x : int) : (term186 x) = (term157 x).
Proof. exact (@lem1982715 term62 (real_of_int x)). Qed.
Lemma lem2335930 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2335931 : term31 = term64.
Proof. exact (@lem2335930 term32). Qed.
Lemma lem2335933 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2335934 : term62 = term67.
Proof. exact (@lem2335933 term32). Qed.
Lemma lem2335935 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2335936 : term158 = term159.
Proof. exact (MK_COMB (@lem2335935) (@lem2335934)). Qed.
Lemma lem2335937 : term160 = term161.
Proof. exact (MK_COMB (@lem2335936) (@lem2335931)). Qed.
Lemma lem2335938 : term162.
Proof. exact (@lem1981473 term62 term31 term31 term31 term55 term31). Qed.
Lemma lem2335940 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335941 : term117 = term124.
Proof. exact (@lem2335940 (NUMERAL 0) term32). Qed.
Lemma lem2335942 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335943 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335944 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335943 h1) (fun h1 : term124 = True => @lem2335942)). Qed.
Lemma lem2335945 : term124 = True.
Proof. exact (EQ_MP (@lem2335944) (@lem2335942)). Qed.
Lemma lem2335946 : term117 = True.
Proof. exact (TRANS (@lem2335941) (@lem2335945)). Qed.
Lemma lem2335947 : True = term117.
Proof. exact (SYM (@lem2335946)). Qed.
Lemma lem2335948 : term117.
Proof. exact (EQ_MP (@lem2335947) (@lem0)). Qed.
Lemma lem2335949 : term163.
Proof. exact (@lem2335938 (@lem2335948)). Qed.
Lemma lem2335951 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335952 : term117 = term124.
Proof. exact (@lem2335951 (NUMERAL 0) term32). Qed.
Lemma lem2335953 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335954 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335955 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335954 h1) (fun h1 : term124 = True => @lem2335953)). Qed.
Lemma lem2335956 : term124 = True.
Proof. exact (EQ_MP (@lem2335955) (@lem2335953)). Qed.
Lemma lem2335957 : term117 = True.
Proof. exact (TRANS (@lem2335952) (@lem2335956)). Qed.
Lemma lem2335958 : True = term117.
Proof. exact (SYM (@lem2335957)). Qed.
Lemma lem2335959 : term117.
Proof. exact (EQ_MP (@lem2335958) (@lem0)). Qed.
Lemma lem2335960 : term164.
Proof. exact (@lem2335949 (@lem2335959)). Qed.
Lemma lem2335962 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2335963 : term117 = term124.
Proof. exact (@lem2335962 (NUMERAL 0) term32). Qed.
Lemma lem2335964 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2335965 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2335966 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2335965 h1) (fun h1 : term124 = True => @lem2335964)). Qed.
Lemma lem2335967 : term124 = True.
Proof. exact (EQ_MP (@lem2335966) (@lem2335964)). Qed.
Lemma lem2335968 : term117 = True.
Proof. exact (TRANS (@lem2335963) (@lem2335967)). Qed.
Lemma lem2335969 : True = term117.
Proof. exact (SYM (@lem2335968)). Qed.
Lemma lem2335970 : term117.
Proof. exact (EQ_MP (@lem2335969) (@lem0)). Qed.
Lemma lem2335971 : term165.
Proof. exact (@lem2335960 (@lem2335970)). Qed.
Lemma lem2335973 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2335974 : term75 = term76.
Proof. exact (@lem2335973 term32 term32). Qed.
Lemma lem2335975 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335976 : term78 = term32.
Proof. exact (EQ_MP (@lem2335975) (@lem940073)). Qed.
Lemma lem2335977 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335978 : term76 = term31.
Proof. exact (MK_COMB (@lem2335977) (@lem2335976)). Qed.
Lemma lem2335979 : term75 = term31.
Proof. exact (TRANS (@lem2335974) (@lem2335978)). Qed.
Lemma lem2335981 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2335982 : term70 = term81.
Proof. exact (@lem2335981 term32 term32). Qed.
Lemma lem2335983 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2335984 : term78 = term32.
Proof. exact (EQ_MP (@lem2335983) (@lem940073)). Qed.
Lemma lem2335985 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2335986 : term76 = term31.
Proof. exact (MK_COMB (@lem2335985) (@lem2335984)). Qed.
Lemma lem2335987 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2335988 : term81 = term62.
Proof. exact (MK_COMB (@lem2335987) (@lem2335986)). Qed.
Lemma lem2335989 : term70 = term62.
Proof. exact (TRANS (@lem2335982) (@lem2335988)). Qed.
Lemma lem2335990 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2335991 : term166 = term158.
Proof. exact (MK_COMB (@lem2335990) (@lem2335989)). Qed.
Lemma lem2335992 : term167 = term160.
Proof. exact (MK_COMB (@lem2335991) (@lem2335979)). Qed.
Lemma lem2335994 (m : nat) : (term168 m) = term55.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2335995 : term160 = term55.
Proof. exact (@lem2335994 term32). Qed.
Lemma lem2335996 : term167 = term55.
Proof. exact (TRANS (@lem2335992) (@lem2335995)). Qed.
Lemma lem2335997 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2335998 : term169 = term170.
Proof. exact (MK_COMB (@lem2335997) (@lem2335996)). Qed.
Lemma lem2335999 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2336000 : term171 = term129.
Proof. exact (MK_COMB (@lem2335998) (@lem2335999)). Qed.
Lemma lem2336002 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2336003 : term129 = term55.
Proof. exact (@lem2336002 term32). Qed.
Lemma lem2336004 : term171 = term55.
Proof. exact (TRANS (@lem2336000) (@lem2336003)). Qed.
Lemma lem2336006 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2336007 : term75 = term76.
Proof. exact (@lem2336006 term32 term32). Qed.
Lemma lem2336008 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2336009 : term78 = term32.
Proof. exact (EQ_MP (@lem2336008) (@lem940073)). Qed.
Lemma lem2336010 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2336011 : term76 = term31.
Proof. exact (MK_COMB (@lem2336010) (@lem2336009)). Qed.
Lemma lem2336012 : term75 = term31.
Proof. exact (TRANS (@lem2336007) (@lem2336011)). Qed.
Lemma lem2336013 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem2336014 : term172 = term129.
Proof. exact (MK_COMB (@lem2336013) (@lem2336012)). Qed.
Lemma lem2336016 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2336017 : term129 = term55.
Proof. exact (@lem2336016 term32). Qed.
Lemma lem2336018 : term172 = term55.
Proof. exact (TRANS (@lem2336014) (@lem2336017)). Qed.
Lemma lem2336019 : term55 = term172.
Proof. exact (SYM (@lem2336018)). Qed.
Lemma lem2336020 : term171 = term172.
Proof. exact (TRANS (@lem2336004) (@lem2336019)). Qed.
Lemma lem2336021 : term161 = term118.
Proof. exact (@lem2335971 (@lem2336020)). Qed.
Lemma lem2336022 : term160 = term118.
Proof. exact (TRANS (@lem2335937) (@lem2336021)). Qed.
Lemma lem2336024 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2336025 : term118 = term55.
Proof. exact (@lem2336024 term55). Qed.
Lemma lem2336026 : term160 = term55.
Proof. exact (TRANS (@lem2336022) (@lem2336025)). Qed.
Lemma lem2336027 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2336028 : term173 = term170.
Proof. exact (MK_COMB (@lem2336027) (@lem2336026)). Qed.
Lemma lem2336029 (x : int) : (real_of_int x) = (real_of_int x).
Proof. exact (eq_refl (real_of_int x)). Qed.
Lemma lem2336030 (x : int) : (term157 x) = (term174 x).
Proof. exact (MK_COMB (@lem2336028) (@lem2336029 x)). Qed.
Lemma lem2336031 (x : int) : (term186 x) = (term174 x).
Proof. exact (TRANS (@lem2335928 x) (@lem2336030 x)). Qed.
Lemma lem2336032 (x : int) : (term174 x) = term55.
Proof. exact (@lem1982719 (real_of_int x)). Qed.
Lemma lem2336033 (x : int) : (term186 x) = term55.
Proof. exact (TRANS (@lem2336031 x) (@lem2336032 x)). Qed.
Lemma lem2336034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2336035 (x : int) : (term187 x) = term176.
Proof. exact (MK_COMB (@lem2336034) (@lem2336033 x)). Qed.
Lemma lem2336036 (y : int) : (term280 y) = (term281 y).
Proof. exact (@lem1982759 (term52 y) (real_of_int y) term62). Qed.
Lemma lem2336037 (y : int) : (term156 y) = (term157 y).
Proof. exact (@lem1982713 term62 (real_of_int y)). Qed.
Lemma lem2336039 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2336040 : term31 = term64.
Proof. exact (@lem2336039 term32). Qed.
Lemma lem2336042 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2336043 : term62 = term67.
Proof. exact (@lem2336042 term32). Qed.
Lemma lem2336044 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2336045 : term158 = term159.
Proof. exact (MK_COMB (@lem2336044) (@lem2336043)). Qed.
Lemma lem2336046 : term160 = term161.
Proof. exact (MK_COMB (@lem2336045) (@lem2336040)). Qed.
Lemma lem2336047 : term162.
Proof. exact (@lem1981473 term62 term31 term31 term31 term55 term31). Qed.
Lemma lem2336049 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2336050 : term117 = term124.
Proof. exact (@lem2336049 (NUMERAL 0) term32). Qed.
Lemma lem2336051 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2336052 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2336053 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2336052 h1) (fun h1 : term124 = True => @lem2336051)). Qed.
Lemma lem2336054 : term124 = True.
Proof. exact (EQ_MP (@lem2336053) (@lem2336051)). Qed.
Lemma lem2336055 : term117 = True.
Proof. exact (TRANS (@lem2336050) (@lem2336054)). Qed.
Lemma lem2336056 : True = term117.
Proof. exact (SYM (@lem2336055)). Qed.
Lemma lem2336057 : term117.
Proof. exact (EQ_MP (@lem2336056) (@lem0)). Qed.
Lemma lem2336058 : term163.
Proof. exact (@lem2336047 (@lem2336057)). Qed.
Lemma lem2336060 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2336061 : term117 = term124.
Proof. exact (@lem2336060 (NUMERAL 0) term32). Qed.
Lemma lem2336062 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2336063 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2336064 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2336063 h1) (fun h1 : term124 = True => @lem2336062)). Qed.
Lemma lem2336065 : term124 = True.
Proof. exact (EQ_MP (@lem2336064) (@lem2336062)). Qed.
Lemma lem2336066 : term117 = True.
Proof. exact (TRANS (@lem2336061) (@lem2336065)). Qed.
Lemma lem2336067 : True = term117.
Proof. exact (SYM (@lem2336066)). Qed.
Lemma lem2336068 : term117.
Proof. exact (EQ_MP (@lem2336067) (@lem0)). Qed.
Lemma lem2336069 : term164.
Proof. exact (@lem2336058 (@lem2336068)). Qed.
Lemma lem2336071 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2336072 : term117 = term124.
Proof. exact (@lem2336071 (NUMERAL 0) term32). Qed.
Lemma lem2336073 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2336074 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2336075 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2336074 h1) (fun h1 : term124 = True => @lem2336073)). Qed.
Lemma lem2336076 : term124 = True.
Proof. exact (EQ_MP (@lem2336075) (@lem2336073)). Qed.
Lemma lem2336077 : term117 = True.
Proof. exact (TRANS (@lem2336072) (@lem2336076)). Qed.
Lemma lem2336078 : True = term117.
Proof. exact (SYM (@lem2336077)). Qed.
Lemma lem2336079 : term117.
Proof. exact (EQ_MP (@lem2336078) (@lem0)). Qed.
Lemma lem2336080 : term165.
Proof. exact (@lem2336069 (@lem2336079)). Qed.
Lemma lem2336082 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2336083 : term75 = term76.
Proof. exact (@lem2336082 term32 term32). Qed.
Lemma lem2336084 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2336085 : term78 = term32.
Proof. exact (EQ_MP (@lem2336084) (@lem940073)). Qed.
Lemma lem2336086 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2336087 : term76 = term31.
Proof. exact (MK_COMB (@lem2336086) (@lem2336085)). Qed.
Lemma lem2336088 : term75 = term31.
Proof. exact (TRANS (@lem2336083) (@lem2336087)). Qed.
Lemma lem2336090 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2336091 : term70 = term81.
Proof. exact (@lem2336090 term32 term32). Qed.
Lemma lem2336092 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2336093 : term78 = term32.
Proof. exact (EQ_MP (@lem2336092) (@lem940073)). Qed.
Lemma lem2336094 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2336095 : term76 = term31.
Proof. exact (MK_COMB (@lem2336094) (@lem2336093)). Qed.
Lemma lem2336096 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2336097 : term81 = term62.
Proof. exact (MK_COMB (@lem2336096) (@lem2336095)). Qed.
Lemma lem2336098 : term70 = term62.
Proof. exact (TRANS (@lem2336091) (@lem2336097)). Qed.
Lemma lem2336099 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2336100 : term166 = term158.
Proof. exact (MK_COMB (@lem2336099) (@lem2336098)). Qed.
Lemma lem2336101 : term167 = term160.
Proof. exact (MK_COMB (@lem2336100) (@lem2336088)). Qed.
Lemma lem2336103 (m : nat) : (term168 m) = term55.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem2336104 : term160 = term55.
Proof. exact (@lem2336103 term32). Qed.
Lemma lem2336105 : term167 = term55.
Proof. exact (TRANS (@lem2336101) (@lem2336104)). Qed.
Lemma lem2336106 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2336107 : term169 = term170.
Proof. exact (MK_COMB (@lem2336106) (@lem2336105)). Qed.
Lemma lem2336108 : term31 = term31.
Proof. exact (eq_refl term31). Qed.
Lemma lem2336109 : term171 = term129.
Proof. exact (MK_COMB (@lem2336107) (@lem2336108)). Qed.
Lemma lem2336111 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2336112 : term129 = term55.
Proof. exact (@lem2336111 term32). Qed.
Lemma lem2336113 : term171 = term55.
Proof. exact (TRANS (@lem2336109) (@lem2336112)). Qed.
Lemma lem2336115 (m : nat) (n : nat) : (term73 m n) = (term74 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem2336116 : term75 = term76.
Proof. exact (@lem2336115 term32 term32). Qed.
Lemma lem2336117 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2336118 : term78 = term32.
Proof. exact (EQ_MP (@lem2336117) (@lem940073)). Qed.
Lemma lem2336119 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2336120 : term76 = term31.
Proof. exact (MK_COMB (@lem2336119) (@lem2336118)). Qed.
Lemma lem2336121 : term75 = term31.
Proof. exact (TRANS (@lem2336116) (@lem2336120)). Qed.
Lemma lem2336122 : term170 = term170.
Proof. exact (eq_refl term170). Qed.
Lemma lem2336123 : term172 = term129.
Proof. exact (MK_COMB (@lem2336122) (@lem2336121)). Qed.
Lemma lem2336125 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2336126 : term129 = term55.
Proof. exact (@lem2336125 term32). Qed.
Lemma lem2336127 : term172 = term55.
Proof. exact (TRANS (@lem2336123) (@lem2336126)). Qed.
Lemma lem2336128 : term55 = term172.
Proof. exact (SYM (@lem2336127)). Qed.
Lemma lem2336129 : term171 = term172.
Proof. exact (TRANS (@lem2336113) (@lem2336128)). Qed.
Lemma lem2336130 : term161 = term118.
Proof. exact (@lem2336080 (@lem2336129)). Qed.
Lemma lem2336131 : term160 = term118.
Proof. exact (TRANS (@lem2336046) (@lem2336130)). Qed.
Lemma lem2336133 (x : real) : (term84 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem2336134 : term118 = term55.
Proof. exact (@lem2336133 term55). Qed.
Lemma lem2336135 : term160 = term55.
Proof. exact (TRANS (@lem2336131) (@lem2336134)). Qed.
Lemma lem2336136 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem2336137 : term173 = term170.
Proof. exact (MK_COMB (@lem2336136) (@lem2336135)). Qed.
Lemma lem2336138 (y : int) : (real_of_int y) = (real_of_int y).
Proof. exact (eq_refl (real_of_int y)). Qed.
Lemma lem2336139 (y : int) : (term157 y) = (term174 y).
Proof. exact (MK_COMB (@lem2336137) (@lem2336138 y)). Qed.
Lemma lem2336140 (y : int) : (term156 y) = (term174 y).
Proof. exact (TRANS (@lem2336037 y) (@lem2336139 y)). Qed.
Lemma lem2336141 (y : int) : (term174 y) = term55.
Proof. exact (@lem1982719 (real_of_int y)). Qed.
Lemma lem2336142 (y : int) : (term156 y) = term55.
Proof. exact (TRANS (@lem2336140 y) (@lem2336141 y)). Qed.
Lemma lem2336143 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem2336144 (y : int) : (term175 y) = term176.
Proof. exact (MK_COMB (@lem2336143) (@lem2336142 y)). Qed.
Lemma lem2336145 : term62 = term62.
Proof. exact (eq_refl term62). Qed.
Lemma lem2336146 (y : int) : (term281 y) = term188.
Proof. exact (MK_COMB (@lem2336144 y) (@lem2336145)). Qed.
Lemma lem2336147 (y : int) : (term280 y) = term188.
Proof. exact (TRANS (@lem2336036 y) (@lem2336146 y)). Qed.
Lemma lem2336148 : term188 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem2336149 (y : int) : (term280 y) = term62.
Proof. exact (TRANS (@lem2336147 y) (@lem2336148)). Qed.
Lemma lem2336150 (x : int) (y : int) : (term279 x y) = term188.
Proof. exact (MK_COMB (@lem2336035 x) (@lem2336149 y)). Qed.
Lemma lem2336151 (x : int) (y : int) : (term278 x y) = term188.
Proof. exact (TRANS (@lem2335927 x y) (@lem2336150 x y)). Qed.
Lemma lem2336152 : term188 = term62.
Proof. exact (@lem1982721 term62). Qed.
Lemma lem2336153 (x : int) (y : int) : (term278 x y) = term62.
Proof. exact (TRANS (@lem2336151 x y) (@lem2336152)). Qed.
Lemma lem2336154 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem2336155 (x : int) (y : int) : (term282 x y) = term190.
Proof. exact (MK_COMB (@lem2336154) (@lem2336153 x y)). Qed.
Lemma lem2336156 : term55 = term55.
Proof. exact (eq_refl term55). Qed.
Lemma lem2336157 (x : int) (y : int) : (term277 x y) = term191.
Proof. exact (MK_COMB (@lem2336155 x y) (@lem2336156)). Qed.
Lemma lem2336158 (x : int) (y : int) (h1 : term269 x y) : term191.
Proof. exact (EQ_MP (@lem2336157 x y) (@lem2335926 x y h1)). Qed.
Lemma lem2336160 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem2336161 : term191 = term192.
Proof. exact (@lem2336160 term55 term62). Qed.
Lemma lem2336163 (x : nat) : (term65 x) = (term66 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem2336164 : term62 = term67.
Proof. exact (@lem2336163 term32). Qed.
Lemma lem2336166 (x : nat) : (real_of_num x) = (term63 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem2336167 : term55 = term118.
Proof. exact (@lem2336166 (NUMERAL 0)). Qed.
Lemma lem2336168 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2336169 : term193 = term194.
Proof. exact (MK_COMB (@lem2336168) (@lem2336167)). Qed.
Lemma lem2336170 : term192 = term195.
Proof. exact (MK_COMB (@lem2336169) (@lem2336164)). Qed.
Lemma lem2336171 : term196.
Proof. exact (@lem1980026 term55 term31 term62 term31). Qed.
Lemma lem2336173 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2336174 : term117 = term124.
Proof. exact (@lem2336173 (NUMERAL 0) term32). Qed.
Lemma lem2336175 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2336176 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2336177 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2336176 h1) (fun h1 : term124 = True => @lem2336175)). Qed.
Lemma lem2336178 : term124 = True.
Proof. exact (EQ_MP (@lem2336177) (@lem2336175)). Qed.
Lemma lem2336179 : term117 = True.
Proof. exact (TRANS (@lem2336174) (@lem2336178)). Qed.
Lemma lem2336180 : True = term117.
Proof. exact (SYM (@lem2336179)). Qed.
Lemma lem2336181 : term117.
Proof. exact (EQ_MP (@lem2336180) (@lem0)). Qed.
Lemma lem2336182 : term197.
Proof. exact (@lem2336171 (@lem2336181)). Qed.
Lemma lem2336184 (m : nat) (n : nat) : (term123 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem2336185 : term117 = term124.
Proof. exact (@lem2336184 (NUMERAL 0) term32). Qed.
Lemma lem2336186 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2336187 (h1 : term125 = (BIT1 0)) : term124 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem2336188 : (term125 = (BIT1 0)) = (term124 = True).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2336187 h1) (fun h1 : term124 = True => @lem2336186)). Qed.
Lemma lem2336189 : term124 = True.
Proof. exact (EQ_MP (@lem2336188) (@lem2336186)). Qed.
Lemma lem2336190 : term117 = True.
Proof. exact (TRANS (@lem2336185) (@lem2336189)). Qed.
Lemma lem2336191 : True = term117.
Proof. exact (SYM (@lem2336190)). Qed.
Lemma lem2336192 : term117.
Proof. exact (EQ_MP (@lem2336191) (@lem0)). Qed.
Lemma lem2336193 : term195 = term198.
Proof. exact (@lem2336182 (@lem2336192)). Qed.
Lemma lem2336195 (m : nat) (n : nat) : (term79 m n) = (term80 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem2336196 : term70 = term81.
Proof. exact (@lem2336195 term32 term32). Qed.
Lemma lem2336197 : (term77 = (BIT1 0)) = (term78 = term32).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem2336198 : term78 = term32.
Proof. exact (EQ_MP (@lem2336197) (@lem940073)). Qed.
Lemma lem2336199 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem2336200 : term76 = term31.
Proof. exact (MK_COMB (@lem2336199) (@lem2336198)). Qed.
Lemma lem2336201 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem2336202 : term81 = term62.
Proof. exact (MK_COMB (@lem2336201) (@lem2336200)). Qed.
Lemma lem2336203 : term70 = term62.
Proof. exact (TRANS (@lem2336196) (@lem2336202)). Qed.
Lemma lem2336205 (x : nat) : (term128 x) = term55.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem2336206 : term129 = term55.
Proof. exact (@lem2336205 term32). Qed.
Lemma lem2336207 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem2336208 : term199 = term193.
Proof. exact (MK_COMB (@lem2336207) (@lem2336206)). Qed.
Lemma lem2336209 : term198 = term192.
Proof. exact (MK_COMB (@lem2336208) (@lem2336203)). Qed.
Lemma lem2336211 (m : nat) (n : nat) : (term200 m n) = (term201 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem2336212 : term192 = term202.
Proof. exact (@lem2336211 (NUMERAL 0) term32). Qed.
Lemma lem2336213 : term125 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem2336214 (h1 : term125 = (BIT1 0)) : (term32 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem2336215 : (term125 = (BIT1 0)) = ((term32 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term125 = (BIT1 0) => @lem2336214 h1) (fun h1 : (term32 = (NUMERAL 0)) = False => @lem2336213)). Qed.
Lemma lem2336216 : (term32 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem2336215) (@lem2336213)). Qed.
Lemma lem2336217 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem2336218 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem2336219 : term203 = (and True).
Proof. exact (MK_COMB (@lem2336218) (@lem2336217)). Qed.
Lemma lem2336220 : term202 = (True /\ False).
Proof. exact (MK_COMB (@lem2336219) (@lem2336216)). Qed.
Lemma lem2336222 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem2336223 : term202 = False.
Proof. exact (TRANS (@lem2336220) (@lem2336222)). Qed.
Lemma lem2336224 : term192 = False.
Proof. exact (TRANS (@lem2336212) (@lem2336223)). Qed.
Lemma lem2336225 : term198 = False.
Proof. exact (TRANS (@lem2336209) (@lem2336224)). Qed.
Lemma lem2336226 : term195 = False.
Proof. exact (TRANS (@lem2336193) (@lem2336225)). Qed.
Lemma lem2336227 : term192 = False.
Proof. exact (TRANS (@lem2336170) (@lem2336226)). Qed.
Lemma lem2336228 : term191 = False.
Proof. exact (TRANS (@lem2336161) (@lem2336227)). Qed.
Lemma lem2336229 (x : int) (y : int) (h1 : term269 x y) : False.
Proof. exact (EQ_MP (@lem2336228) (@lem2336158 x y h1)). Qed.
Lemma lem2336230 (x : int) (y : int) (h1 : term267 x y) : False.
Proof. exact (or_elim (@lem2335696 x y h1) (fun h0 : term268 x y => @lem2335770 x y h0) (fun h0 : term269 x y => @lem2336229 x y h0)). Qed.
Lemma lem2336232 (x : int) (y : int) (h1 : term267 x y) : term267 x y.
Proof. exact (h1). Qed.
Lemma lem2336233 (x : int) (y : int) (h1 : term267 x y) : (term267 x y) = False.
Proof. exact (prop_ext (fun h2 : term267 x y => @lem2336230 x y h1) (fun h2 : False => @lem2336232 x y h1)). Qed.
Lemma lem2336234 (x : int) (y : int) (h1 : term267 x y) : False.
Proof. exact (EQ_MP (@lem2336233 x y h1) (@lem2336232 x y h1)). Qed.
Lemma lem2336235 (y : int) (x : int) (h1 : term232 y x) : term232 y x.
Proof. exact (h1). Qed.
Lemma lem2336236 (y : int) (x : int) (h1 : term232 y x) : term267 x y.
Proof. exact (EQ_MP (@lem2335686 x y) (@lem2336235 y x h1)). Qed.
Lemma lem2336237 (y : int) (x : int) (h1 : term232 y x) : (term267 x y) = False.
Proof. exact (prop_ext (fun h2 : term267 x y => @lem2336234 x y h2) (fun h2 : False => @lem2336236 y x h1)). Qed.
Lemma lem2336238 (y : int) (x : int) (h1 : term232 y x) : False.
Proof. exact (EQ_MP (@lem2336237 y x h1) (@lem2336236 y x h1)). Qed.
Lemma lem2336239 (y : int) (x : int) : term283 y x.
Proof. exact (fun h0 : term232 y x => @lem2336238 y x h0). Qed.
Lemma lem2336240 (y : int) (x : int) : term284 y x.
Proof. exact (@lem1386578 (term285 y x)). Qed.
Lemma lem2336243 (y : int) (x : int) : term285 y x.
Proof. exact (@lem2336240 y x (@lem2336239 y x)). Qed.
Lemma lem2336244 (x : int) (y : int) : (term231 y x) = (term219 x y).
Proof. exact (SYM (@lem2335198 y x)). Qed.
Lemma lem2336245 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem2336246 (x : int) (y : int) : (term285 y x) = (term209 x y).
Proof. exact (MK_COMB (@lem2336245) (@lem2336244 x y)). Qed.
Lemma lem2336247 (x : int) (y : int) : term209 x y.
Proof. exact (EQ_MP (@lem2336246 x y) (@lem2336243 y x)). Qed.
Lemma lem2336248 (x : int) (y : int) : term210 x y.
Proof. exact (EQ_MP (@lem2335084 x y) (@lem2336247 x y)). Qed.
Lemma lem2336249 (x : int) (y : int) : (term210 x y) = ((term210 x y) = True).
Proof. exact (@lem7 (term210 x y)). Qed.
Lemma lem2336250 (x : int) (y : int) : (term210 x y) = True.
Proof. exact (EQ_MP (@lem2336249 x y) (@lem2336248 x y)). Qed.
Lemma lem2336251 (x : int) (y : int) : True = (term210 x y).
Proof. exact (SYM (@lem2336250 x y)). Qed.
Lemma lem2336252 (x : int) (y : int) : term210 x y.
Proof. exact (EQ_MP (@lem2336251 x y) (@lem0)). Qed.
Lemma lem2336253 (y : int) (x : int) (h1 : term19 y x) : int_le x y.
Proof. exact (@lem2336252 x y (@lem2335083 y x h1)). Qed.
Lemma lem2336254 (x : int) (y : int) : term286 x y.
Proof. exact (fun h0 : term19 y x => @lem2336253 y x h0). Qed.
Lemma lem2336255 (x : int) (y : int) : term287 x y.
Proof. exact (conj (@lem2335079 y x) (@lem2336254 x y)). Qed.
Lemma lem2336256 (y : int) (x : int) : (term287 x y) = ((int_le x y) = (term19 y x)).
Proof. exact (@lem32 (int_le x y) (term19 y x)). Qed.
Lemma lem2336257 (y : int) (x : int) : (int_le x y) = (term19 y x).
Proof. exact (EQ_MP (@lem2336256 y x) (@lem2336255 x y)). Qed.
Lemma lem2336262 (x : int) : term288 x.
Proof. exact (fun y : int => @lem2336257 y x). Qed.
Lemma lem2336267 : term289.
Proof. exact (fun x : int => @lem2336262 x). Qed.
