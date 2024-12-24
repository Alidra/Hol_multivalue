Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Require Import hol_axioms.
Require Import hol_type_abbrevs.
Require Import CARD_PSUBSET_term_abbrevs.
Require Import CARD_DELETE_spec.
Require Import CARD_EQ_0_spec.
Require Import CARD_SUBSET_spec.
Require Import DISJ_ACI_spec.
Require Import FINITE_DELETE_spec.
Require Import INT_POS_spec.
Require Import LET_TRANS_spec.
Require Import MEMBER_NOT_EMPTY_spec.
Require Import thm0_spec.
Require Import thm1008952_spec.
Require Import thm1009824_spec.
Require Import thm1013352_spec.
Require Import thm1013364_spec.
Require Import thm1032098_spec.
Require Import thm1032781_spec.
Require Import thm10578_spec.
Require Import thm10597_spec.
Require Import thm12653_spec.
Require Import thm1365106_spec.
Require Import thm1365406_spec.
Require Import thm1365721_spec.
Require Import thm1367111_spec.
Require Import thm1367247_spec.
Require Import thm1367248_spec.
Require Import thm1367254_spec.
Require Import thm1367303_spec.
Require Import thm1386578_spec.
Require Import thm1393126_spec.
Require Import thm1396750_spec.
Require Import thm14781_spec.
Require Import thm15222_spec.
Require Import thm16474_spec.
Require Import thm16506_spec.
Require Import thm16507_spec.
Require Import thm16933_spec.
Require Import thm17045_spec.
Require Import thm17160_spec.
Require Import thm17265_spec.
Require Import thm17362_spec.
Require Import thm17500_spec.
Require Import thm17646_spec.
Require Import thm17784_spec.
Require Import thm17930_spec.
Require Import thm18392_spec.
Require Import thm18394_spec.
Require Import thm1842_spec.
Require Import thm18898_spec.
Require Import thm18899_spec.
Require Import thm18904_spec.
Require Import thm18905_spec.
Require Import thm18910_spec.
Require Import thm18911_spec.
Require Import thm18916_spec.
Require Import thm18917_spec.
Require Import thm18922_spec.
Require Import thm18923_spec.
Require Import thm18928_spec.
Require Import thm18929_spec.
Require Import thm18952_spec.
Require Import thm18953_spec.
Require Import thm19012_spec.
Require Import thm19013_spec.
Require Import thm19158_spec.
Require Import thm19367_spec.
Require Import thm19490_spec.
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
Require Import thm1982757_spec.
Require Import thm1982759_spec.
Require Import thm1982763_spec.
Require Import thm1982781_spec.
Require Import thm1982792_spec.
Require Import thm1988287_spec.
Require Import thm1988293_spec.
Require Import thm1988330_spec.
Require Import thm1988332_spec.
Require Import thm1988336_spec.
Require Import thm1988342_spec.
Require Import thm20664_spec.
Require Import thm20665_spec.
Require Import thm20668_spec.
Require Import thm20682_spec.
Require Import thm20764_spec.
Require Import thm20780_spec.
Require Import thm20789_spec.
Require Import thm20895_spec.
Require Import thm20904_spec.
Require Import thm21007_spec.
Require Import thm21021_spec.
Require Import thm21028_spec.
Require Import thm21107_spec.
Require Import thm21114_spec.
Require Import thm21182_spec.
Require Import thm21394_spec.
Require Import thm21490_spec.
Require Import thm21501_spec.
Require Import thm21598_spec.
Require Import thm2318496_spec.
Require Import thm2318497_spec.
Require Import thm2318538_spec.
Require Import thm2318539_spec.
Require Import thm2318544_spec.
Require Import thm2318545_spec.
Require Import thm2318568_spec.
Require Import thm2318569_spec.
Require Import thm2318574_spec.
Require Import thm2318575_spec.
Require Import thm2318604_spec.
Require Import thm2841383_spec.
Require Import thm2841384_spec.
Require Import thm2841401_spec.
Require Import thm2841402_spec.
Require Import thm2841413_spec.
Require Import thm2841414_spec.
Require Import thm3211609_spec.
Require Import thm3211610_spec.
Require Import thm3211683_spec.
Require Import thm3211684_spec.
Require Import thm3211744_spec.
Require Import thm3211745_spec.
Require Import thm3211750_spec.
Require Import thm3211751_spec.
Require Import thm3211756_spec.
Require Import thm3211757_spec.
Require Import thm69_spec.
Require Import thm7_spec.
Require Import thm912739_spec.
Require Import thm940073_spec.
Lemma lem3908902 (n : nat) : (term0 n) = (n = (NUMERAL 0)).
Proof. exact (@lem16933 (n = (NUMERAL 0))). Qed.
Lemma lem3908904 (n : nat) : (term1 n) = (term1 n).
Proof. exact (eq_refl (term1 n)). Qed.
Lemma lem3908905 (n : nat) : (term2 n) = (term3 n).
Proof. exact (MK_COMB (@lem3908904 n) (@lem3908902 n)). Qed.
Lemma lem3908910 (n : nat) : (term4 n) = (term4 n).
Proof. exact (eq_refl (term4 n)). Qed.
Lemma lem3908911 (n : nat) : (term5 n) = (term6 n).
Proof. exact (MK_COMB (@lem3908910 n) (@lem3908905 n)). Qed.
Lemma lem3908912 (n : nat) : ((term7 n) = (term8 n)) = (term5 n).
Proof. exact (@lem17500 (term7 n) (term8 n)). Qed.
Lemma lem3908914 (n : nat) : ((term7 n) = (term8 n)) = (term6 n).
Proof. exact (TRANS (@lem3908912 n) (@lem3908911 n)). Qed.
Lemma lem3908915 (n : nat) : (term9 n) = (term10 n).
Proof. exact (@lem1032781 n term11 (term12 n)). Qed.
Lemma lem3908916 (d : nat) (n : nat) : (term13 n d) = (term14 d n).
Proof. exact (eq_refl (term13 n d)). Qed.
Lemma lem3908917 (n : nat) (d : nat) : (term15 n d) = (term15 n d).
Proof. exact (eq_refl (term15 n d)). Qed.
Lemma lem3908918 (d : nat) (n : nat) : (term16 n d) = (term17 d n).
Proof. exact (MK_COMB (@lem3908917 n d) (@lem3908916 d n)). Qed.
Lemma lem3908919 (n : nat) : (term18 n) = (term19 n).
Proof. exact (fun_ext (fun d : nat => @lem3908918 d n)). Qed.
Lemma lem3908920 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3908921 (n : nat) : (term10 n) = (term20 n).
Proof. exact (MK_COMB (@lem3908920) (@lem3908919 n)). Qed.
Lemma lem3908922 (n : nat) : (term9 n) = (term6 n).
Proof. exact (eq_refl (term9 n)). Qed.
Lemma lem3908923 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3908924 (n : nat) : (term21 n) = (term22 n).
Proof. exact (MK_COMB (@lem3908923) (@lem3908922 n)). Qed.
Lemma lem3908925 (n : nat) : ((term9 n) = (term10 n)) = ((term6 n) = (term20 n)).
Proof. exact (MK_COMB (@lem3908924 n) (@lem3908921 n)). Qed.
Lemma lem3908926 (n : nat) : (term6 n) = (term20 n).
Proof. exact (EQ_MP (@lem3908925 n) (@lem3908915 n)). Qed.
Lemma lem3908927 (d : nat) (n : nat) : (term17 d n) = (term17 d n).
Proof. exact (eq_refl (term17 d n)). Qed.
Lemma lem3908928 (n : nat) : (term19 n) = (term19 n).
Proof. exact (fun_ext (fun d : nat => @lem3908927 d n)). Qed.
Lemma lem3908929 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3908930 (n : nat) : (term20 n) = (term20 n).
Proof. exact (MK_COMB (@lem3908929) (@lem3908928 n)). Qed.
Lemma lem3908931 (n : nat) : (term22 n) = (term22 n).
Proof. exact (eq_refl (term22 n)). Qed.
Lemma lem3908932 (n : nat) : ((term6 n) = (term20 n)) = ((term6 n) = (term20 n)).
Proof. exact (MK_COMB (@lem3908931 n) (@lem3908930 n)). Qed.
Lemma lem3908933 (n : nat) : (term6 n) = (term20 n).
Proof. exact (EQ_MP (@lem3908932 n) (@lem3908926 n)). Qed.
Lemma lem3908964 (n : nat) : ((term7 n) = (term8 n)) = (term20 n).
Proof. exact (TRANS (@lem3908914 n) (@lem3908933 n)). Qed.
Lemma lem3908997 (d : nat) (n : nat) : (term14 d n) = (term14 d n).
Proof. exact (eq_refl (term14 d n)). Qed.
Lemma lem3909014 (n : nat) (d : nat) : (term23 n d) = (term23 n d).
Proof. exact (eq_refl (term23 n d)). Qed.
Lemma lem3909021 (d : nat) : (term24 d) = (term25 d).
Proof. exact (@lem1032098 d term11). Qed.
Lemma lem3909024 (n : nat) : (@eq nat n) = (@eq nat n).
Proof. exact (eq_refl (@eq nat n)). Qed.
Lemma lem3909025 (n : nat) (d : nat) : (n = (term24 d)) = (n = (term25 d)).
Proof. exact (MK_COMB (@lem3909024 n) (@lem3909021 d)). Qed.
Lemma lem3909026 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3909027 (n : nat) (d : nat) : (term26 n d) = (term27 n d).
Proof. exact (MK_COMB (@lem3909026) (@lem3909025 n d)). Qed.
Lemma lem3909028 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909029 (n : nat) (d : nat) : (term28 n d) = (term29 n d).
Proof. exact (MK_COMB (@lem3909028) (@lem3909027 n d)). Qed.
Lemma lem3909030 (n : nat) (d : nat) : (term30 n d) = (term31 n d).
Proof. exact (MK_COMB (@lem3909029 n d) (@lem3909014 n d)). Qed.
Lemma lem3909031 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909032 (n : nat) (d : nat) : (term15 n d) = (term32 n d).
Proof. exact (MK_COMB (@lem3909031) (@lem3909030 n d)). Qed.
Lemma lem3909033 (d : nat) (n : nat) : (term17 d n) = (term33 d n).
Proof. exact (MK_COMB (@lem3909032 n d) (@lem3908997 d n)). Qed.
Lemma lem3909034 (n : nat) : (term19 n) = (term34 n).
Proof. exact (fun_ext (fun d : nat => @lem3909033 d n)). Qed.
Lemma lem3909035 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3909036 (n : nat) : (term20 n) = (term35 n).
Proof. exact (MK_COMB (@lem3909035) (@lem3909034 n)). Qed.
Lemma lem3909039 (n : nat) : ((term7 n) = (term8 n)) = (term35 n).
Proof. exact (TRANS (@lem3908964 n) (@lem3909036 n)). Qed.
Lemma lem3909041 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3909042 (n : nat) (d : nat) : (n = (term25 d)) = ((int_of_num n) = (term36 d)).
Proof. exact (@lem3909041 n (term25 d)). Qed.
Lemma lem3909046 (m : nat) (n : nat) : (term37 m n) = (term38 m n).
Proof. exact (EQ_MP (@lem2841384 m n) (@lem2841383 m n)). Qed.
Lemma lem3909047 (d : nat) : (term36 d) = (term39 d).
Proof. exact (@lem3909046 d term11). Qed.
Lemma lem3909048 (n : nat) : (term40 n) = (term40 n).
Proof. exact (eq_refl (term40 n)). Qed.
Lemma lem3909049 (n : nat) (d : nat) : ((int_of_num n) = (term36 d)) = ((int_of_num n) = (term39 d)).
Proof. exact (MK_COMB (@lem3909048 n) (@lem3909047 d)). Qed.
Lemma lem3909050 (n : nat) (d : nat) : (n = (term25 d)) = ((int_of_num n) = (term39 d)).
Proof. exact (TRANS (@lem3909042 n d) (@lem3909049 n d)). Qed.
Lemma lem3909051 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3909052 (n : nat) (d : nat) : (term27 n d) = (term41 n d).
Proof. exact (MK_COMB (@lem3909051) (@lem3909050 n d)). Qed.
Lemma lem3909053 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909054 (n : nat) (d : nat) : (term29 n d) = (term42 n d).
Proof. exact (MK_COMB (@lem3909053) (@lem3909052 n d)). Qed.
Lemma lem3909056 (m : nat) (n : nat) : (Peano.lt m n) = (term43 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3909057 (n : nat) : (term44 n) = (term45 n).
Proof. exact (@lem3909056 n term11). Qed.
Lemma lem3909058 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3909059 (n : nat) : (term46 n) = (term47 n).
Proof. exact (MK_COMB (@lem3909058) (@lem3909057 n)). Qed.
Lemma lem3909060 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909061 (n : nat) : (term48 n) = (term49 n).
Proof. exact (MK_COMB (@lem3909060) (@lem3909059 n)). Qed.
Lemma lem3909063 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3909064 (d : nat) : (d = (NUMERAL 0)) = ((int_of_num d) = term50).
Proof. exact (@lem3909063 d (NUMERAL 0)). Qed.
Lemma lem3909067 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3909068 (d : nat) : (term8 d) = (term51 d).
Proof. exact (MK_COMB (@lem3909067) (@lem3909064 d)). Qed.
Lemma lem3909069 (n : nat) (d : nat) : (term23 n d) = (term52 n d).
Proof. exact (MK_COMB (@lem3909061 n) (@lem3909068 d)). Qed.
Lemma lem3909070 (n : nat) (d : nat) : (term31 n d) = (term53 n d).
Proof. exact (MK_COMB (@lem3909054 n d) (@lem3909069 n d)). Qed.
Lemma lem3909071 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909072 (n : nat) (d : nat) : (term32 n d) = (term54 n d).
Proof. exact (MK_COMB (@lem3909071) (@lem3909070 n d)). Qed.
Lemma lem3909074 (m : nat) (n : nat) : (Peano.lt m n) = (term43 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3909075 (d : nat) (n : nat) : (Peano.lt d n) = (term43 d n).
Proof. exact (@lem3909074 d n). Qed.
Lemma lem3909076 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909077 (d : nat) (n : nat) : (term55 d n) = (term56 d n).
Proof. exact (MK_COMB (@lem3909076) (@lem3909075 d n)). Qed.
Lemma lem3909079 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3909080 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term50).
Proof. exact (@lem3909079 n (NUMERAL 0)). Qed.
Lemma lem3909083 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3909084 (n : nat) : (term8 n) = (term51 n).
Proof. exact (MK_COMB (@lem3909083) (@lem3909080 n)). Qed.
Lemma lem3909085 (d : nat) (n : nat) : (term57 d n) = (term58 d n).
Proof. exact (MK_COMB (@lem3909077 d n) (@lem3909084 n)). Qed.
Lemma lem3909086 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909087 (d : nat) (n : nat) : (term59 d n) = (term60 d n).
Proof. exact (MK_COMB (@lem3909086) (@lem3909085 d n)). Qed.
Lemma lem3909089 (m : nat) (n : nat) : (Peano.lt m n) = (term43 m n).
Proof. exact (EQ_MP (@lem2841402 m n) (@lem2841401 m n)). Qed.
Lemma lem3909090 (d : nat) (n : nat) : (Peano.lt d n) = (term43 d n).
Proof. exact (@lem3909089 d n). Qed.
Lemma lem3909091 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3909092 (d : nat) (n : nat) : (term61 d n) = (term62 d n).
Proof. exact (MK_COMB (@lem3909091) (@lem3909090 d n)). Qed.
Lemma lem3909093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909094 (d : nat) (n : nat) : (term63 d n) = (term64 d n).
Proof. exact (MK_COMB (@lem3909093) (@lem3909092 d n)). Qed.
Lemma lem3909096 (m : nat) (n : nat) : (m = n) = ((int_of_num m) = (int_of_num n)).
Proof. exact (EQ_MP (@lem2841414 m n) (@lem2841413 m n)). Qed.
Lemma lem3909097 (n : nat) : (n = (NUMERAL 0)) = ((int_of_num n) = term50).
Proof. exact (@lem3909096 n (NUMERAL 0)). Qed.
Lemma lem3909100 (d : nat) (n : nat) : (term65 d n) = (term66 d n).
Proof. exact (MK_COMB (@lem3909094 d n) (@lem3909097 n)). Qed.
Lemma lem3909101 (d : nat) (n : nat) : (term14 d n) = (term67 d n).
Proof. exact (MK_COMB (@lem3909087 d n) (@lem3909100 d n)). Qed.
Lemma lem3909102 (d : nat) (n : nat) : (term33 d n) = (term68 d n).
Proof. exact (MK_COMB (@lem3909072 n d) (@lem3909101 d n)). Qed.
Lemma lem3909103 (n : nat) : (term34 n) = (term69 n).
Proof. exact (fun_ext (fun d : nat => @lem3909102 d n)). Qed.
Lemma lem3909104 : (@all nat) = (@all nat).
Proof. exact (eq_refl (@all nat)). Qed.
Lemma lem3909105 (n : nat) : (term35 n) = (term70 n).
Proof. exact (MK_COMB (@lem3909104) (@lem3909103 n)). Qed.
Lemma lem3909106 (n : nat) : ((term7 n) = (term8 n)) = (term70 n).
Proof. exact (TRANS (@lem3909039 n) (@lem3909105 n)). Qed.
Lemma lem3909107 (d : nat) : term71 d.
Proof. exact (@lem2307535 d). Qed.
Lemma lem3909108 (d : nat) : (term71 d) = (term72 d).
Proof. exact (eq_refl (term71 d)). Qed.
Lemma lem3909109 (d : nat) : term72 d.
Proof. exact (EQ_MP (@lem3909108 d) (@lem3909107 d)). Qed.
Lemma lem3909110 (n : nat) : term71 n.
Proof. exact (@lem2307535 n). Qed.
Lemma lem3909111 (n : nat) : (term71 n) = (term72 n).
Proof. exact (eq_refl (term71 n)). Qed.
Lemma lem3909112 (n : nat) : term72 n.
Proof. exact (EQ_MP (@lem3909111 n) (@lem3909110 n)). Qed.
Lemma lem3909113 (_45438 : int) (_45439 : int) : (term73 _45438 _45439) = (term74 _45438 _45439).
Proof. exact (@lem2318604 (term74 _45438 _45439)). Qed.
Lemma lem3909139 (_45439 : int) (_45438 : int) : (term75 _45439 _45438) = (_45439 = (term76 _45438)).
Proof. exact (@lem16933 (_45439 = (term76 _45438))). Qed.
Lemma lem3909142 (_45439 : int) : (term77 _45439) = (term78 _45439).
Proof. exact (@lem16933 (term78 _45439)). Qed.
Lemma lem3909145 (_45438 : int) : (term79 _45438) = (_45438 = term50).
Proof. exact (@lem16933 (_45438 = term50)). Qed.
Lemma lem3909146 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909147 (_45439 : int) : (term80 _45439) = (term81 _45439).
Proof. exact (MK_COMB (@lem3909146) (@lem3909142 _45439)). Qed.
Lemma lem3909148 (_45439 : int) (_45438 : int) : (term82 _45439 _45438) = (term83 _45439 _45438).
Proof. exact (MK_COMB (@lem3909147 _45439) (@lem3909145 _45438)). Qed.
Lemma lem3909149 (_45439 : int) (_45438 : int) : (term84 _45439 _45438) = (term82 _45439 _45438).
Proof. exact (@lem17160 (term85 _45439) (term86 _45438)). Qed.
Lemma lem3909150 (_45439 : int) (_45438 : int) : (term84 _45439 _45438) = (term83 _45439 _45438).
Proof. exact (TRANS (@lem3909149 _45439 _45438) (@lem3909148 _45439 _45438)). Qed.
Lemma lem3909151 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909152 (_45439 : int) (_45438 : int) : (term87 _45439 _45438) = (term88 _45439 _45438).
Proof. exact (MK_COMB (@lem3909151) (@lem3909139 _45439 _45438)). Qed.
Lemma lem3909153 (_45439 : int) (_45438 : int) : (term89 _45439 _45438) = (term90 _45439 _45438).
Proof. exact (MK_COMB (@lem3909152 _45439 _45438) (@lem3909150 _45439 _45438)). Qed.
Lemma lem3909154 (_45439 : int) (_45438 : int) : (term91 _45439 _45438) = (term89 _45439 _45438).
Proof. exact (@lem17045 (term92 _45439 _45438) (term93 _45439 _45438)). Qed.
Lemma lem3909155 (_45439 : int) (_45438 : int) : (term91 _45439 _45438) = (term90 _45439 _45438).
Proof. exact (TRANS (@lem3909154 _45439 _45438) (@lem3909153 _45439 _45438)). Qed.
Lemma lem3909159 (_45439 : int) : (term79 _45439) = (_45439 = term50).
Proof. exact (@lem16933 (_45439 = term50)). Qed.
Lemma lem3909161 (_45438 : int) (_45439 : int) : (term94 _45438 _45439) = (term94 _45438 _45439).
Proof. exact (eq_refl (term94 _45438 _45439)). Qed.
Lemma lem3909162 (_45438 : int) (_45439 : int) : (term95 _45438 _45439) = (term96 _45438 _45439).
Proof. exact (MK_COMB (@lem3909161 _45438 _45439) (@lem3909159 _45439)). Qed.
Lemma lem3909163 (_45438 : int) (_45439 : int) : (term97 _45438 _45439) = (term95 _45438 _45439).
Proof. exact (@lem17045 (int_lt _45438 _45439) (term86 _45439)). Qed.
Lemma lem3909164 (_45438 : int) (_45439 : int) : (term97 _45438 _45439) = (term96 _45438 _45439).
Proof. exact (TRANS (@lem3909163 _45438 _45439) (@lem3909162 _45438 _45439)). Qed.
Lemma lem3909167 (_45438 : int) (_45439 : int) : (term98 _45438 _45439) = (int_lt _45438 _45439).
Proof. exact (@lem16933 (int_lt _45438 _45439)). Qed.
Lemma lem3909168 (_45439 : int) : (term86 _45439) = (term86 _45439).
Proof. exact (eq_refl (term86 _45439)). Qed.
Lemma lem3909169 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909170 (_45438 : int) (_45439 : int) : (term99 _45438 _45439) = (term100 _45438 _45439).
Proof. exact (MK_COMB (@lem3909169) (@lem3909167 _45438 _45439)). Qed.
Lemma lem3909171 (_45438 : int) (_45439 : int) : (term101 _45438 _45439) = (term102 _45438 _45439).
Proof. exact (MK_COMB (@lem3909170 _45438 _45439) (@lem3909168 _45439)). Qed.
Lemma lem3909172 (_45438 : int) (_45439 : int) : (term103 _45438 _45439) = (term101 _45438 _45439).
Proof. exact (@lem17045 (term104 _45438 _45439) (_45439 = term50)). Qed.
Lemma lem3909173 (_45438 : int) (_45439 : int) : (term103 _45438 _45439) = (term102 _45438 _45439).
Proof. exact (TRANS (@lem3909172 _45438 _45439) (@lem3909171 _45438 _45439)). Qed.
Lemma lem3909174 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909175 (_45438 : int) (_45439 : int) : (term105 _45438 _45439) = (term106 _45438 _45439).
Proof. exact (MK_COMB (@lem3909174) (@lem3909164 _45438 _45439)). Qed.
Lemma lem3909176 (_45438 : int) (_45439 : int) : (term107 _45438 _45439) = (term108 _45438 _45439).
Proof. exact (MK_COMB (@lem3909175 _45438 _45439) (@lem3909173 _45438 _45439)). Qed.
Lemma lem3909177 (_45438 : int) (_45439 : int) : (term109 _45438 _45439) = (term107 _45438 _45439).
Proof. exact (@lem17160 (term110 _45438 _45439) (term111 _45438 _45439)). Qed.
Lemma lem3909178 (_45438 : int) (_45439 : int) : (term109 _45438 _45439) = (term108 _45438 _45439).
Proof. exact (TRANS (@lem3909177 _45438 _45439) (@lem3909176 _45438 _45439)). Qed.
Lemma lem3909179 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909180 (_45439 : int) (_45438 : int) : (term112 _45439 _45438) = (term113 _45439 _45438).
Proof. exact (MK_COMB (@lem3909179) (@lem3909155 _45439 _45438)). Qed.
Lemma lem3909181 (_45438 : int) (_45439 : int) : (term114 _45438 _45439) = (term115 _45438 _45439).
Proof. exact (MK_COMB (@lem3909180 _45439 _45438) (@lem3909178 _45438 _45439)). Qed.
Lemma lem3909182 (_45438 : int) (_45439 : int) : (term116 _45438 _45439) = (term114 _45438 _45439).
Proof. exact (@lem17160 (term117 _45439 _45438) (term118 _45438 _45439)). Qed.
Lemma lem3909183 (_45438 : int) (_45439 : int) : (term116 _45438 _45439) = (term115 _45438 _45439).
Proof. exact (TRANS (@lem3909182 _45438 _45439) (@lem3909181 _45438 _45439)). Qed.
Lemma lem3909185 (_45439 : int) : (term119 _45439) = (term119 _45439).
Proof. exact (eq_refl (term119 _45439)). Qed.
Lemma lem3909186 (_45438 : int) (_45439 : int) : (term120 _45438 _45439) = (term121 _45438 _45439).
Proof. exact (MK_COMB (@lem3909185 _45439) (@lem3909183 _45438 _45439)). Qed.
Lemma lem3909187 (_45438 : int) (_45439 : int) : (term122 _45438 _45439) = (term120 _45438 _45439).
Proof. exact (@lem17362 (term123 _45439) (term124 _45438 _45439)). Qed.
Lemma lem3909188 (_45438 : int) (_45439 : int) : (term122 _45438 _45439) = (term121 _45438 _45439).
Proof. exact (TRANS (@lem3909187 _45438 _45439) (@lem3909186 _45438 _45439)). Qed.
Lemma lem3909190 (_45438 : int) : (term119 _45438) = (term119 _45438).
Proof. exact (eq_refl (term119 _45438)). Qed.
Lemma lem3909191 (_45438 : int) (_45439 : int) : (term125 _45438 _45439) = (term126 _45438 _45439).
Proof. exact (MK_COMB (@lem3909190 _45438) (@lem3909188 _45438 _45439)). Qed.
Lemma lem3909192 (_45438 : int) (_45439 : int) : (term127 _45438 _45439) = (term125 _45438 _45439).
Proof. exact (@lem17362 (term123 _45438) (term128 _45438 _45439)). Qed.
Lemma lem3909232 (_45438 : int) (_45439 : int) : (term127 _45438 _45439) = (term126 _45438 _45439).
Proof. exact (TRANS (@lem3909192 _45438 _45439) (@lem3909191 _45438 _45439)). Qed.
Lemma lem3909235 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3909236 (_45438 : int) : (term123 _45438) = (term130 _45438).
Proof. exact (@lem3909235 term50 _45438). Qed.
Lemma lem3909238 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909239 : term132 = term133.
Proof. exact (@lem3909238 (NUMERAL 0)). Qed.
Lemma lem3909240 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3909241 : term134 = term135.
Proof. exact (MK_COMB (@lem3909240) (@lem3909239)). Qed.
Lemma lem3909242 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3909243 (_45438 : int) : (term130 _45438) = (term136 _45438).
Proof. exact (MK_COMB (@lem3909241) (@lem3909242 _45438)). Qed.
Lemma lem3909245 (_45438 : int) : (term123 _45438) = (term136 _45438).
Proof. exact (TRANS (@lem3909236 _45438) (@lem3909243 _45438)). Qed.
Lemma lem3909248 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3909249 (_45439 : int) : (term123 _45439) = (term130 _45439).
Proof. exact (@lem3909248 term50 _45439). Qed.
Lemma lem3909251 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909252 : term132 = term133.
Proof. exact (@lem3909251 (NUMERAL 0)). Qed.
Lemma lem3909253 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3909254 : term134 = term135.
Proof. exact (MK_COMB (@lem3909253) (@lem3909252)). Qed.
Lemma lem3909255 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3909256 (_45439 : int) : (term130 _45439) = (term136 _45439).
Proof. exact (MK_COMB (@lem3909254) (@lem3909255 _45439)). Qed.
Lemma lem3909258 (_45439 : int) : (term123 _45439) = (term136 _45439).
Proof. exact (TRANS (@lem3909249 _45439) (@lem3909256 _45439)). Qed.
Lemma lem3909261 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3909262 (_45439 : int) (_45438 : int) : (_45439 = (term76 _45438)) = ((real_of_int _45439) = (term137 _45438)).
Proof. exact (@lem3909261 _45439 (term76 _45438)). Qed.
Lemma lem3909266 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3909267 (_45438 : int) : (term137 _45438) = (term140 _45438).
Proof. exact (@lem3909266 _45438 term141). Qed.
Lemma lem3909269 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909270 : term142 = term143.
Proof. exact (@lem3909269 term11). Qed.
Lemma lem3909271 (_45438 : int) : (term144 _45438) = (term144 _45438).
Proof. exact (eq_refl (term144 _45438)). Qed.
Lemma lem3909272 (_45438 : int) : (term140 _45438) = (term145 _45438).
Proof. exact (MK_COMB (@lem3909271 _45438) (@lem3909270)). Qed.
Lemma lem3909273 (_45438 : int) : (term137 _45438) = (term145 _45438).
Proof. exact (TRANS (@lem3909267 _45438) (@lem3909272 _45438)). Qed.
Lemma lem3909274 (_45439 : int) : (term146 _45439) = (term146 _45439).
Proof. exact (eq_refl (term146 _45439)). Qed.
Lemma lem3909275 (_45439 : int) (_45438 : int) : ((real_of_int _45439) = (term137 _45438)) = ((real_of_int _45439) = (term145 _45438)).
Proof. exact (MK_COMB (@lem3909274 _45439) (@lem3909273 _45438)). Qed.
Lemma lem3909277 (_45439 : int) (_45438 : int) : (_45439 = (term76 _45438)) = ((real_of_int _45439) = (term145 _45438)).
Proof. exact (TRANS (@lem3909262 _45439 _45438) (@lem3909275 _45439 _45438)). Qed.
Lemma lem3909279 (x : int) (y : int) : (int_lt x y) = (term147 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem3909280 (_45439 : int) : (term78 _45439) = (term148 _45439).
Proof. exact (@lem3909279 _45439 term141). Qed.
Lemma lem3909282 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3909283 (_45439 : int) : (term148 _45439) = (term149 _45439).
Proof. exact (@lem3909282 (term76 _45439) term141). Qed.
Lemma lem3909285 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3909286 (_45439 : int) : (term137 _45439) = (term140 _45439).
Proof. exact (@lem3909285 _45439 term141). Qed.
Lemma lem3909288 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909289 : term142 = term143.
Proof. exact (@lem3909288 term11). Qed.
Lemma lem3909290 (_45439 : int) : (term144 _45439) = (term144 _45439).
Proof. exact (eq_refl (term144 _45439)). Qed.
Lemma lem3909291 (_45439 : int) : (term140 _45439) = (term145 _45439).
Proof. exact (MK_COMB (@lem3909290 _45439) (@lem3909289)). Qed.
Lemma lem3909292 (_45439 : int) : (term137 _45439) = (term145 _45439).
Proof. exact (TRANS (@lem3909286 _45439) (@lem3909291 _45439)). Qed.
Lemma lem3909293 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3909294 (_45439 : int) : (term150 _45439) = (term151 _45439).
Proof. exact (MK_COMB (@lem3909293) (@lem3909292 _45439)). Qed.
Lemma lem3909296 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909297 : term142 = term143.
Proof. exact (@lem3909296 term11). Qed.
Lemma lem3909298 (_45439 : int) : (term149 _45439) = (term152 _45439).
Proof. exact (MK_COMB (@lem3909294 _45439) (@lem3909297)). Qed.
Lemma lem3909299 (_45439 : int) : (term148 _45439) = (term152 _45439).
Proof. exact (TRANS (@lem3909283 _45439) (@lem3909298 _45439)). Qed.
Lemma lem3909300 (_45439 : int) : (term78 _45439) = (term152 _45439).
Proof. exact (TRANS (@lem3909280 _45439) (@lem3909299 _45439)). Qed.
Lemma lem3909303 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3909304 (_45438 : int) : (_45438 = term50) = ((real_of_int _45438) = term132).
Proof. exact (@lem3909303 _45438 term50). Qed.
Lemma lem3909308 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909309 : term132 = term133.
Proof. exact (@lem3909308 (NUMERAL 0)). Qed.
Lemma lem3909310 (_45438 : int) : (term146 _45438) = (term146 _45438).
Proof. exact (eq_refl (term146 _45438)). Qed.
Lemma lem3909311 (_45438 : int) : ((real_of_int _45438) = term132) = ((real_of_int _45438) = term133).
Proof. exact (MK_COMB (@lem3909310 _45438) (@lem3909309)). Qed.
Lemma lem3909313 (_45438 : int) : (_45438 = term50) = ((real_of_int _45438) = term133).
Proof. exact (TRANS (@lem3909304 _45438) (@lem3909311 _45438)). Qed.
Lemma lem3909314 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909315 (_45439 : int) : (term81 _45439) = (term153 _45439).
Proof. exact (MK_COMB (@lem3909314) (@lem3909300 _45439)). Qed.
Lemma lem3909316 (_45439 : int) (_45438 : int) : (term83 _45439 _45438) = (term154 _45439 _45438).
Proof. exact (MK_COMB (@lem3909315 _45439) (@lem3909313 _45438)). Qed.
Lemma lem3909317 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909318 (_45439 : int) (_45438 : int) : (term88 _45439 _45438) = (term155 _45439 _45438).
Proof. exact (MK_COMB (@lem3909317) (@lem3909277 _45439 _45438)). Qed.
Lemma lem3909319 (_45439 : int) (_45438 : int) : (term90 _45439 _45438) = (term156 _45439 _45438).
Proof. exact (MK_COMB (@lem3909318 _45439 _45438) (@lem3909316 _45439 _45438)). Qed.
Lemma lem3909321 (y : int) (x : int) : (term104 x y) = (int_le y x).
Proof. exact (proj1 (@lem2318496 x y)). Qed.
Lemma lem3909322 (_45439 : int) (_45438 : int) : (term104 _45438 _45439) = (int_le _45439 _45438).
Proof. exact (@lem3909321 _45439 _45438). Qed.
Lemma lem3909324 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3909325 (_45439 : int) (_45438 : int) : (int_le _45439 _45438) = (term129 _45439 _45438).
Proof. exact (@lem3909324 _45439 _45438). Qed.
Lemma lem3909326 (_45439 : int) (_45438 : int) : (term104 _45438 _45439) = (term129 _45439 _45438).
Proof. exact (TRANS (@lem3909322 _45439 _45438) (@lem3909325 _45439 _45438)). Qed.
Lemma lem3909329 (x : int) (y : int) : (x = y) = ((real_of_int x) = (real_of_int y)).
Proof. exact (EQ_MP (@lem2318575 x y) (@lem2318574 x y)). Qed.
Lemma lem3909330 (_45439 : int) : (_45439 = term50) = ((real_of_int _45439) = term132).
Proof. exact (@lem3909329 _45439 term50). Qed.
Lemma lem3909334 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909335 : term132 = term133.
Proof. exact (@lem3909334 (NUMERAL 0)). Qed.
Lemma lem3909336 (_45439 : int) : (term146 _45439) = (term146 _45439).
Proof. exact (eq_refl (term146 _45439)). Qed.
Lemma lem3909337 (_45439 : int) : ((real_of_int _45439) = term132) = ((real_of_int _45439) = term133).
Proof. exact (MK_COMB (@lem3909336 _45439) (@lem3909335)). Qed.
Lemma lem3909339 (_45439 : int) : (_45439 = term50) = ((real_of_int _45439) = term133).
Proof. exact (TRANS (@lem3909330 _45439) (@lem3909337 _45439)). Qed.
Lemma lem3909340 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909341 (_45439 : int) (_45438 : int) : (term94 _45438 _45439) = (term157 _45439 _45438).
Proof. exact (MK_COMB (@lem3909340) (@lem3909326 _45439 _45438)). Qed.
Lemma lem3909342 (_45438 : int) (_45439 : int) : (term96 _45438 _45439) = (term158 _45438 _45439).
Proof. exact (MK_COMB (@lem3909341 _45439 _45438) (@lem3909339 _45439)). Qed.
Lemma lem3909344 (x : int) (y : int) : (int_lt x y) = (term147 x y).
Proof. exact (proj2 (@lem2318497 x y)). Qed.
Lemma lem3909345 (_45438 : int) (_45439 : int) : (int_lt _45438 _45439) = (term147 _45438 _45439).
Proof. exact (@lem3909344 _45438 _45439). Qed.
Lemma lem3909347 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3909348 (_45438 : int) (_45439 : int) : (term147 _45438 _45439) = (term159 _45438 _45439).
Proof. exact (@lem3909347 (term76 _45438) _45439). Qed.
Lemma lem3909350 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3909351 (_45438 : int) : (term137 _45438) = (term140 _45438).
Proof. exact (@lem3909350 _45438 term141). Qed.
Lemma lem3909353 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909354 : term142 = term143.
Proof. exact (@lem3909353 term11). Qed.
Lemma lem3909355 (_45438 : int) : (term144 _45438) = (term144 _45438).
Proof. exact (eq_refl (term144 _45438)). Qed.
Lemma lem3909356 (_45438 : int) : (term140 _45438) = (term145 _45438).
Proof. exact (MK_COMB (@lem3909355 _45438) (@lem3909354)). Qed.
Lemma lem3909357 (_45438 : int) : (term137 _45438) = (term145 _45438).
Proof. exact (TRANS (@lem3909351 _45438) (@lem3909356 _45438)). Qed.
Lemma lem3909358 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3909359 (_45438 : int) : (term150 _45438) = (term151 _45438).
Proof. exact (MK_COMB (@lem3909358) (@lem3909357 _45438)). Qed.
Lemma lem3909360 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3909361 (_45438 : int) (_45439 : int) : (term159 _45438 _45439) = (term160 _45438 _45439).
Proof. exact (MK_COMB (@lem3909359 _45438) (@lem3909360 _45439)). Qed.
Lemma lem3909362 (_45438 : int) (_45439 : int) : (term147 _45438 _45439) = (term160 _45438 _45439).
Proof. exact (TRANS (@lem3909348 _45438 _45439) (@lem3909361 _45438 _45439)). Qed.
Lemma lem3909363 (_45438 : int) (_45439 : int) : (int_lt _45438 _45439) = (term160 _45438 _45439).
Proof. exact (TRANS (@lem3909345 _45438 _45439) (@lem3909362 _45438 _45439)). Qed.
Lemma lem3909365 (y : int) (x : int) : (term161 x y) = (term162 y x).
Proof. exact (proj1 (@lem2318497 x y)). Qed.
Lemma lem3909366 (_45439 : int) : (term86 _45439) = (term163 _45439).
Proof. exact (@lem3909365 term50 _45439). Qed.
Lemma lem3909368 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3909369 (_45439 : int) : (term164 _45439) = (term165 _45439).
Proof. exact (@lem3909368 (term76 _45439) term50). Qed.
Lemma lem3909371 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3909372 (_45439 : int) : (term137 _45439) = (term140 _45439).
Proof. exact (@lem3909371 _45439 term141). Qed.
Lemma lem3909374 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909375 : term142 = term143.
Proof. exact (@lem3909374 term11). Qed.
Lemma lem3909376 (_45439 : int) : (term144 _45439) = (term144 _45439).
Proof. exact (eq_refl (term144 _45439)). Qed.
Lemma lem3909377 (_45439 : int) : (term140 _45439) = (term145 _45439).
Proof. exact (MK_COMB (@lem3909376 _45439) (@lem3909375)). Qed.
Lemma lem3909378 (_45439 : int) : (term137 _45439) = (term145 _45439).
Proof. exact (TRANS (@lem3909372 _45439) (@lem3909377 _45439)). Qed.
Lemma lem3909379 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3909380 (_45439 : int) : (term150 _45439) = (term151 _45439).
Proof. exact (MK_COMB (@lem3909379) (@lem3909378 _45439)). Qed.
Lemma lem3909382 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909383 : term132 = term133.
Proof. exact (@lem3909382 (NUMERAL 0)). Qed.
Lemma lem3909384 (_45439 : int) : (term165 _45439) = (term166 _45439).
Proof. exact (MK_COMB (@lem3909380 _45439) (@lem3909383)). Qed.
Lemma lem3909385 (_45439 : int) : (term164 _45439) = (term166 _45439).
Proof. exact (TRANS (@lem3909369 _45439) (@lem3909384 _45439)). Qed.
Lemma lem3909386 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909387 (_45439 : int) : (term167 _45439) = (term168 _45439).
Proof. exact (MK_COMB (@lem3909386) (@lem3909385 _45439)). Qed.
Lemma lem3909389 (x : int) (y : int) : (int_le x y) = (term129 x y).
Proof. exact (EQ_MP (@lem2318569 x y) (@lem2318568 x y)). Qed.
Lemma lem3909390 (_45439 : int) : (term169 _45439) = (term170 _45439).
Proof. exact (@lem3909389 term171 _45439). Qed.
Lemma lem3909392 (x : int) (y : int) : (term138 x y) = (term139 x y).
Proof. exact (EQ_MP (@lem2318539 x y) (@lem2318538 x y)). Qed.
Lemma lem3909393 : term172 = term173.
Proof. exact (@lem3909392 term50 term141). Qed.
Lemma lem3909395 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909396 : term132 = term133.
Proof. exact (@lem3909395 (NUMERAL 0)). Qed.
Lemma lem3909397 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3909398 : term174 = term175.
Proof. exact (MK_COMB (@lem3909397) (@lem3909396)). Qed.
Lemma lem3909400 (n : nat) : (term131 n) = (real_of_num n).
Proof. exact (EQ_MP (@lem2318545 n) (@lem2318544 n)). Qed.
Lemma lem3909401 : term142 = term143.
Proof. exact (@lem3909400 term11). Qed.
Lemma lem3909402 : term173 = term176.
Proof. exact (MK_COMB (@lem3909398) (@lem3909401)). Qed.
Lemma lem3909403 : term172 = term176.
Proof. exact (TRANS (@lem3909393) (@lem3909402)). Qed.
Lemma lem3909404 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3909405 : term177 = term178.
Proof. exact (MK_COMB (@lem3909404) (@lem3909403)). Qed.
Lemma lem3909406 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3909407 (_45439 : int) : (term170 _45439) = (term179 _45439).
Proof. exact (MK_COMB (@lem3909405) (@lem3909406 _45439)). Qed.
Lemma lem3909408 (_45439 : int) : (term169 _45439) = (term179 _45439).
Proof. exact (TRANS (@lem3909390 _45439) (@lem3909407 _45439)). Qed.
Lemma lem3909409 (_45439 : int) : (term163 _45439) = (term180 _45439).
Proof. exact (MK_COMB (@lem3909387 _45439) (@lem3909408 _45439)). Qed.
Lemma lem3909410 (_45439 : int) : (term86 _45439) = (term180 _45439).
Proof. exact (TRANS (@lem3909366 _45439) (@lem3909409 _45439)). Qed.
Lemma lem3909411 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909412 (_45438 : int) (_45439 : int) : (term100 _45438 _45439) = (term181 _45438 _45439).
Proof. exact (MK_COMB (@lem3909411) (@lem3909363 _45438 _45439)). Qed.
Lemma lem3909413 (_45438 : int) (_45439 : int) : (term102 _45438 _45439) = (term182 _45438 _45439).
Proof. exact (MK_COMB (@lem3909412 _45438 _45439) (@lem3909410 _45439)). Qed.
Lemma lem3909414 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909415 (_45438 : int) (_45439 : int) : (term106 _45438 _45439) = (term183 _45438 _45439).
Proof. exact (MK_COMB (@lem3909414) (@lem3909342 _45438 _45439)). Qed.
Lemma lem3909416 (_45438 : int) (_45439 : int) : (term108 _45438 _45439) = (term184 _45438 _45439).
Proof. exact (MK_COMB (@lem3909415 _45438 _45439) (@lem3909413 _45438 _45439)). Qed.
Lemma lem3909417 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909418 (_45439 : int) (_45438 : int) : (term113 _45439 _45438) = (term185 _45439 _45438).
Proof. exact (MK_COMB (@lem3909417) (@lem3909319 _45439 _45438)). Qed.
Lemma lem3909419 (_45438 : int) (_45439 : int) : (term115 _45438 _45439) = (term186 _45438 _45439).
Proof. exact (MK_COMB (@lem3909418 _45439 _45438) (@lem3909416 _45438 _45439)). Qed.
Lemma lem3909420 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909421 (_45439 : int) : (term119 _45439) = (term187 _45439).
Proof. exact (MK_COMB (@lem3909420) (@lem3909258 _45439)). Qed.
Lemma lem3909422 (_45438 : int) (_45439 : int) : (term121 _45438 _45439) = (term188 _45438 _45439).
Proof. exact (MK_COMB (@lem3909421 _45439) (@lem3909419 _45438 _45439)). Qed.
Lemma lem3909423 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909424 (_45438 : int) : (term119 _45438) = (term187 _45438).
Proof. exact (MK_COMB (@lem3909423) (@lem3909245 _45438)). Qed.
Lemma lem3909425 (_45438 : int) (_45439 : int) : (term126 _45438 _45439) = (term189 _45438 _45439).
Proof. exact (MK_COMB (@lem3909424 _45438) (@lem3909422 _45438 _45439)). Qed.
Lemma lem3909426 (_45438 : int) (_45439 : int) : (term127 _45438 _45439) = (term189 _45438 _45439).
Proof. exact (TRANS (@lem3909232 _45438 _45439) (@lem3909425 _45438 _45439)). Qed.
Lemma lem3909430 (t : Prop) : (term190 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3909526 (_45438 : int) (_45439 : int) : (term191 _45438 _45439) = (term189 _45438 _45439).
Proof. exact (@lem3909430 (term189 _45438 _45439)). Qed.
Lemma lem3909527 (_45438 : int) : (term136 _45438) = (term192 _45438).
Proof. exact (@lem1988287 (real_of_int _45438) term133). Qed.
Lemma lem3909533 (_45438 : int) : (term193 _45438) = (term194 _45438).
Proof. exact (@lem1982792 (real_of_int _45438) term133). Qed.
Lemma lem3909535 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3909536 : term133 = term196.
Proof. exact (@lem3909535 (NUMERAL 0)). Qed.
Lemma lem3909538 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3909539 : term199 = term200.
Proof. exact (@lem3909538 term11). Qed.
Lemma lem3909540 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3909541 : term201 = term202.
Proof. exact (MK_COMB (@lem3909540) (@lem3909539)). Qed.
Lemma lem3909542 : term203 = term204.
Proof. exact (MK_COMB (@lem3909541) (@lem3909536)). Qed.
Lemma lem3909543 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3909545 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909546 : term208 = term209.
Proof. exact (@lem3909545 term11 term11). Qed.
Lemma lem3909547 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909548 : term211 = term11.
Proof. exact (EQ_MP (@lem3909547) (@lem940073)). Qed.
Lemma lem3909549 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909550 : term209 = term143.
Proof. exact (MK_COMB (@lem3909549) (@lem3909548)). Qed.
Lemma lem3909551 : term208 = term143.
Proof. exact (TRANS (@lem3909546) (@lem3909550)). Qed.
Lemma lem3909553 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3909554 : term203 = term133.
Proof. exact (@lem3909553 term11). Qed.
Lemma lem3909555 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3909556 : term213 = term214.
Proof. exact (MK_COMB (@lem3909555) (@lem3909554)). Qed.
Lemma lem3909557 : term205 = term196.
Proof. exact (MK_COMB (@lem3909556) (@lem3909551)). Qed.
Lemma lem3909558 : term204 = term196.
Proof. exact (TRANS (@lem3909543) (@lem3909557)). Qed.
Lemma lem3909559 : term203 = term196.
Proof. exact (TRANS (@lem3909542) (@lem3909558)). Qed.
Lemma lem3909561 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3909562 : term196 = term133.
Proof. exact (@lem3909561 term133). Qed.
Lemma lem3909563 : term203 = term133.
Proof. exact (TRANS (@lem3909559) (@lem3909562)). Qed.
Lemma lem3909564 (_45438 : int) : (term144 _45438) = (term144 _45438).
Proof. exact (eq_refl (term144 _45438)). Qed.
Lemma lem3909565 (_45438 : int) : (term194 _45438) = (term216 _45438).
Proof. exact (MK_COMB (@lem3909564 _45438) (@lem3909563)). Qed.
Lemma lem3909566 (_45438 : int) : (term216 _45438) = (real_of_int _45438).
Proof. exact (@lem1982723 (real_of_int _45438)). Qed.
Lemma lem3909567 (_45438 : int) : (term194 _45438) = (real_of_int _45438).
Proof. exact (TRANS (@lem3909565 _45438) (@lem3909566 _45438)). Qed.
Lemma lem3909569 (_45438 : int) : (term193 _45438) = (real_of_int _45438).
Proof. exact (TRANS (@lem3909533 _45438) (@lem3909567 _45438)). Qed.
Lemma lem3909570 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3909571 (_45438 : int) : (term217 _45438) = (term218 _45438).
Proof. exact (MK_COMB (@lem3909570) (@lem3909569 _45438)). Qed.
Lemma lem3909572 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3909573 (_45438 : int) : (term192 _45438) = (term219 _45438).
Proof. exact (MK_COMB (@lem3909571 _45438) (@lem3909572)). Qed.
Lemma lem3909574 (_45438 : int) : (term136 _45438) = (term219 _45438).
Proof. exact (TRANS (@lem3909527 _45438) (@lem3909573 _45438)). Qed.
Lemma lem3909575 (_45439 : int) : (term136 _45439) = (term192 _45439).
Proof. exact (@lem1988287 (real_of_int _45439) term133). Qed.
Lemma lem3909581 (_45439 : int) : (term193 _45439) = (term194 _45439).
Proof. exact (@lem1982792 (real_of_int _45439) term133). Qed.
Lemma lem3909583 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3909584 : term133 = term196.
Proof. exact (@lem3909583 (NUMERAL 0)). Qed.
Lemma lem3909586 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3909587 : term199 = term200.
Proof. exact (@lem3909586 term11). Qed.
Lemma lem3909588 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3909589 : term201 = term202.
Proof. exact (MK_COMB (@lem3909588) (@lem3909587)). Qed.
Lemma lem3909590 : term203 = term204.
Proof. exact (MK_COMB (@lem3909589) (@lem3909584)). Qed.
Lemma lem3909591 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3909593 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909594 : term208 = term209.
Proof. exact (@lem3909593 term11 term11). Qed.
Lemma lem3909595 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909596 : term211 = term11.
Proof. exact (EQ_MP (@lem3909595) (@lem940073)). Qed.
Lemma lem3909597 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909598 : term209 = term143.
Proof. exact (MK_COMB (@lem3909597) (@lem3909596)). Qed.
Lemma lem3909599 : term208 = term143.
Proof. exact (TRANS (@lem3909594) (@lem3909598)). Qed.
Lemma lem3909601 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3909602 : term203 = term133.
Proof. exact (@lem3909601 term11). Qed.
Lemma lem3909603 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3909604 : term213 = term214.
Proof. exact (MK_COMB (@lem3909603) (@lem3909602)). Qed.
Lemma lem3909605 : term205 = term196.
Proof. exact (MK_COMB (@lem3909604) (@lem3909599)). Qed.
Lemma lem3909606 : term204 = term196.
Proof. exact (TRANS (@lem3909591) (@lem3909605)). Qed.
Lemma lem3909607 : term203 = term196.
Proof. exact (TRANS (@lem3909590) (@lem3909606)). Qed.
Lemma lem3909609 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3909610 : term196 = term133.
Proof. exact (@lem3909609 term133). Qed.
Lemma lem3909611 : term203 = term133.
Proof. exact (TRANS (@lem3909607) (@lem3909610)). Qed.
Lemma lem3909612 (_45439 : int) : (term144 _45439) = (term144 _45439).
Proof. exact (eq_refl (term144 _45439)). Qed.
Lemma lem3909613 (_45439 : int) : (term194 _45439) = (term216 _45439).
Proof. exact (MK_COMB (@lem3909612 _45439) (@lem3909611)). Qed.
Lemma lem3909614 (_45439 : int) : (term216 _45439) = (real_of_int _45439).
Proof. exact (@lem1982723 (real_of_int _45439)). Qed.
Lemma lem3909615 (_45439 : int) : (term194 _45439) = (real_of_int _45439).
Proof. exact (TRANS (@lem3909613 _45439) (@lem3909614 _45439)). Qed.
Lemma lem3909617 (_45439 : int) : (term193 _45439) = (real_of_int _45439).
Proof. exact (TRANS (@lem3909581 _45439) (@lem3909615 _45439)). Qed.
Lemma lem3909618 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3909619 (_45439 : int) : (term217 _45439) = (term218 _45439).
Proof. exact (MK_COMB (@lem3909618) (@lem3909617 _45439)). Qed.
Lemma lem3909620 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3909621 (_45439 : int) : (term192 _45439) = (term219 _45439).
Proof. exact (MK_COMB (@lem3909619 _45439) (@lem3909620)). Qed.
Lemma lem3909622 (_45439 : int) : (term136 _45439) = (term219 _45439).
Proof. exact (TRANS (@lem3909575 _45439) (@lem3909621 _45439)). Qed.
Lemma lem3909623 (_45439 : int) (_45438 : int) : ((real_of_int _45439) = (term145 _45438)) = ((term220 _45439 _45438) = term133).
Proof. exact (@lem1988293 (real_of_int _45439) (term145 _45438)). Qed.
Lemma lem3909635 (_45439 : int) (_45438 : int) : (term220 _45439 _45438) = (term221 _45439 _45438).
Proof. exact (@lem1982792 (real_of_int _45439) (term145 _45438)). Qed.
Lemma lem3909636 (_45438 : int) : (term222 _45438) = (term223 _45438).
Proof. exact (@lem1982781 (real_of_int _45438) term199 term143). Qed.
Lemma lem3909638 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3909639 : term143 = term224.
Proof. exact (@lem3909638 term11). Qed.
Lemma lem3909641 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3909642 : term199 = term200.
Proof. exact (@lem3909641 term11). Qed.
Lemma lem3909643 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3909644 : term201 = term202.
Proof. exact (MK_COMB (@lem3909643) (@lem3909642)). Qed.
Lemma lem3909645 : term225 = term226.
Proof. exact (MK_COMB (@lem3909644) (@lem3909639)). Qed.
Lemma lem3909646 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3909648 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909649 : term208 = term209.
Proof. exact (@lem3909648 term11 term11). Qed.
Lemma lem3909650 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909651 : term211 = term11.
Proof. exact (EQ_MP (@lem3909650) (@lem940073)). Qed.
Lemma lem3909652 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909653 : term209 = term143.
Proof. exact (MK_COMB (@lem3909652) (@lem3909651)). Qed.
Lemma lem3909654 : term208 = term143.
Proof. exact (TRANS (@lem3909649) (@lem3909653)). Qed.
Lemma lem3909656 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3909657 : term225 = term230.
Proof. exact (@lem3909656 term11 term11). Qed.
Lemma lem3909658 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909659 : term211 = term11.
Proof. exact (EQ_MP (@lem3909658) (@lem940073)). Qed.
Lemma lem3909660 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909661 : term209 = term143.
Proof. exact (MK_COMB (@lem3909660) (@lem3909659)). Qed.
Lemma lem3909662 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3909663 : term230 = term199.
Proof. exact (MK_COMB (@lem3909662) (@lem3909661)). Qed.
Lemma lem3909664 : term225 = term199.
Proof. exact (TRANS (@lem3909657) (@lem3909663)). Qed.
Lemma lem3909665 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3909666 : term231 = term232.
Proof. exact (MK_COMB (@lem3909665) (@lem3909664)). Qed.
Lemma lem3909667 : term227 = term200.
Proof. exact (MK_COMB (@lem3909666) (@lem3909654)). Qed.
Lemma lem3909668 : term226 = term200.
Proof. exact (TRANS (@lem3909646) (@lem3909667)). Qed.
Lemma lem3909669 : term225 = term200.
Proof. exact (TRANS (@lem3909645) (@lem3909668)). Qed.
Lemma lem3909671 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3909672 : term200 = term199.
Proof. exact (@lem3909671 term199). Qed.
Lemma lem3909673 : term225 = term199.
Proof. exact (TRANS (@lem3909669) (@lem3909672)). Qed.
Lemma lem3909676 (_45438 : int) : (term233 _45438) = (term233 _45438).
Proof. exact (eq_refl (term233 _45438)). Qed.
Lemma lem3909677 (_45438 : int) : (term223 _45438) = (term234 _45438).
Proof. exact (MK_COMB (@lem3909676 _45438) (@lem3909673)). Qed.
Lemma lem3909678 (_45438 : int) : (term222 _45438) = (term234 _45438).
Proof. exact (TRANS (@lem3909636 _45438) (@lem3909677 _45438)). Qed.
Lemma lem3909679 (_45439 : int) : (term144 _45439) = (term144 _45439).
Proof. exact (eq_refl (term144 _45439)). Qed.
Lemma lem3909680 (_45439 : int) (_45438 : int) : (term221 _45439 _45438) = (term235 _45439 _45438).
Proof. exact (MK_COMB (@lem3909679 _45439) (@lem3909678 _45438)). Qed.
Lemma lem3909685 (_45438 : int) (_45439 : int) : (term235 _45439 _45438) = (term236 _45438 _45439).
Proof. exact (@lem1982757 (term237 _45438) (real_of_int _45439) term199). Qed.
Lemma lem3909686 (_45438 : int) (_45439 : int) : (term221 _45439 _45438) = (term236 _45438 _45439).
Proof. exact (TRANS (@lem3909680 _45439 _45438) (@lem3909685 _45438 _45439)). Qed.
Lemma lem3909688 (_45438 : int) (_45439 : int) : (term220 _45439 _45438) = (term236 _45438 _45439).
Proof. exact (TRANS (@lem3909635 _45439 _45438) (@lem3909686 _45438 _45439)). Qed.
Lemma lem3909689 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3909690 (_45438 : int) (_45439 : int) : (term238 _45439 _45438) = (term239 _45438 _45439).
Proof. exact (MK_COMB (@lem3909689) (@lem3909688 _45438 _45439)). Qed.
Lemma lem3909691 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3909692 (_45438 : int) (_45439 : int) : ((term220 _45439 _45438) = term133) = ((term236 _45438 _45439) = term133).
Proof. exact (MK_COMB (@lem3909690 _45438 _45439) (@lem3909691)). Qed.
Lemma lem3909693 (_45438 : int) (_45439 : int) : ((real_of_int _45439) = (term145 _45438)) = ((term236 _45438 _45439) = term133).
Proof. exact (TRANS (@lem3909623 _45439 _45438) (@lem3909692 _45438 _45439)). Qed.
Lemma lem3909694 (_45439 : int) : (term152 _45439) = (term240 _45439).
Proof. exact (@lem1988287 term143 (term145 _45439)). Qed.
Lemma lem3909706 (_45439 : int) : (term241 _45439) = (term242 _45439).
Proof. exact (@lem1982792 term143 (term145 _45439)). Qed.
Lemma lem3909707 (_45439 : int) : (term222 _45439) = (term223 _45439).
Proof. exact (@lem1982781 (real_of_int _45439) term199 term143). Qed.
Lemma lem3909709 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3909710 : term143 = term224.
Proof. exact (@lem3909709 term11). Qed.
Lemma lem3909712 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3909713 : term199 = term200.
Proof. exact (@lem3909712 term11). Qed.
Lemma lem3909714 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3909715 : term201 = term202.
Proof. exact (MK_COMB (@lem3909714) (@lem3909713)). Qed.
Lemma lem3909716 : term225 = term226.
Proof. exact (MK_COMB (@lem3909715) (@lem3909710)). Qed.
Lemma lem3909717 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3909719 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909720 : term208 = term209.
Proof. exact (@lem3909719 term11 term11). Qed.
Lemma lem3909721 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909722 : term211 = term11.
Proof. exact (EQ_MP (@lem3909721) (@lem940073)). Qed.
Lemma lem3909723 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909724 : term209 = term143.
Proof. exact (MK_COMB (@lem3909723) (@lem3909722)). Qed.
Lemma lem3909725 : term208 = term143.
Proof. exact (TRANS (@lem3909720) (@lem3909724)). Qed.
Lemma lem3909727 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3909728 : term225 = term230.
Proof. exact (@lem3909727 term11 term11). Qed.
Lemma lem3909729 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909730 : term211 = term11.
Proof. exact (EQ_MP (@lem3909729) (@lem940073)). Qed.
Lemma lem3909731 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909732 : term209 = term143.
Proof. exact (MK_COMB (@lem3909731) (@lem3909730)). Qed.
Lemma lem3909733 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3909734 : term230 = term199.
Proof. exact (MK_COMB (@lem3909733) (@lem3909732)). Qed.
Lemma lem3909735 : term225 = term199.
Proof. exact (TRANS (@lem3909728) (@lem3909734)). Qed.
Lemma lem3909736 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3909737 : term231 = term232.
Proof. exact (MK_COMB (@lem3909736) (@lem3909735)). Qed.
Lemma lem3909738 : term227 = term200.
Proof. exact (MK_COMB (@lem3909737) (@lem3909725)). Qed.
Lemma lem3909739 : term226 = term200.
Proof. exact (TRANS (@lem3909717) (@lem3909738)). Qed.
Lemma lem3909740 : term225 = term200.
Proof. exact (TRANS (@lem3909716) (@lem3909739)). Qed.
Lemma lem3909742 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3909743 : term200 = term199.
Proof. exact (@lem3909742 term199). Qed.
Lemma lem3909744 : term225 = term199.
Proof. exact (TRANS (@lem3909740) (@lem3909743)). Qed.
Lemma lem3909747 (_45439 : int) : (term233 _45439) = (term233 _45439).
Proof. exact (eq_refl (term233 _45439)). Qed.
Lemma lem3909748 (_45439 : int) : (term223 _45439) = (term234 _45439).
Proof. exact (MK_COMB (@lem3909747 _45439) (@lem3909744)). Qed.
Lemma lem3909749 (_45439 : int) : (term222 _45439) = (term234 _45439).
Proof. exact (TRANS (@lem3909707 _45439) (@lem3909748 _45439)). Qed.
Lemma lem3909750 : term243 = term243.
Proof. exact (eq_refl term243). Qed.
Lemma lem3909751 (_45439 : int) : (term242 _45439) = (term244 _45439).
Proof. exact (MK_COMB (@lem3909750) (@lem3909749 _45439)). Qed.
Lemma lem3909752 (_45439 : int) : (term244 _45439) = (term245 _45439).
Proof. exact (@lem1982757 (term237 _45439) term143 term199). Qed.
Lemma lem3909754 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3909755 : term199 = term200.
Proof. exact (@lem3909754 term11). Qed.
Lemma lem3909757 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3909758 : term143 = term224.
Proof. exact (@lem3909757 term11). Qed.
Lemma lem3909759 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3909760 : term243 = term246.
Proof. exact (MK_COMB (@lem3909759) (@lem3909758)). Qed.
Lemma lem3909761 : term247 = term248.
Proof. exact (MK_COMB (@lem3909760) (@lem3909755)). Qed.
Lemma lem3909762 : term249.
Proof. exact (@lem1981473 term143 term143 term199 term143 term133 term143). Qed.
Lemma lem3909764 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3909765 : term251 = term252.
Proof. exact (@lem3909764 (NUMERAL 0) term11). Qed.
Lemma lem3909766 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3909767 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3909768 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3909767 h1) (fun h1 : term252 = True => @lem3909766)). Qed.
Lemma lem3909769 : term252 = True.
Proof. exact (EQ_MP (@lem3909768) (@lem3909766)). Qed.
Lemma lem3909770 : term251 = True.
Proof. exact (TRANS (@lem3909765) (@lem3909769)). Qed.
Lemma lem3909771 : True = term251.
Proof. exact (SYM (@lem3909770)). Qed.
Lemma lem3909772 : term251.
Proof. exact (EQ_MP (@lem3909771) (@lem0)). Qed.
Lemma lem3909773 : term254.
Proof. exact (@lem3909762 (@lem3909772)). Qed.
Lemma lem3909775 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3909776 : term251 = term252.
Proof. exact (@lem3909775 (NUMERAL 0) term11). Qed.
Lemma lem3909777 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3909778 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3909779 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3909778 h1) (fun h1 : term252 = True => @lem3909777)). Qed.
Lemma lem3909780 : term252 = True.
Proof. exact (EQ_MP (@lem3909779) (@lem3909777)). Qed.
Lemma lem3909781 : term251 = True.
Proof. exact (TRANS (@lem3909776) (@lem3909780)). Qed.
Lemma lem3909782 : True = term251.
Proof. exact (SYM (@lem3909781)). Qed.
Lemma lem3909783 : term251.
Proof. exact (EQ_MP (@lem3909782) (@lem0)). Qed.
Lemma lem3909784 : term255.
Proof. exact (@lem3909773 (@lem3909783)). Qed.
Lemma lem3909786 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3909787 : term251 = term252.
Proof. exact (@lem3909786 (NUMERAL 0) term11). Qed.
Lemma lem3909788 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3909789 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3909790 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3909789 h1) (fun h1 : term252 = True => @lem3909788)). Qed.
Lemma lem3909791 : term252 = True.
Proof. exact (EQ_MP (@lem3909790) (@lem3909788)). Qed.
Lemma lem3909792 : term251 = True.
Proof. exact (TRANS (@lem3909787) (@lem3909791)). Qed.
Lemma lem3909793 : True = term251.
Proof. exact (SYM (@lem3909792)). Qed.
Lemma lem3909794 : term251.
Proof. exact (EQ_MP (@lem3909793) (@lem0)). Qed.
Lemma lem3909795 : term256.
Proof. exact (@lem3909784 (@lem3909794)). Qed.
Lemma lem3909797 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3909798 : term225 = term230.
Proof. exact (@lem3909797 term11 term11). Qed.
Lemma lem3909799 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909800 : term211 = term11.
Proof. exact (EQ_MP (@lem3909799) (@lem940073)). Qed.
Lemma lem3909801 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909802 : term209 = term143.
Proof. exact (MK_COMB (@lem3909801) (@lem3909800)). Qed.
Lemma lem3909803 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3909804 : term230 = term199.
Proof. exact (MK_COMB (@lem3909803) (@lem3909802)). Qed.
Lemma lem3909805 : term225 = term199.
Proof. exact (TRANS (@lem3909798) (@lem3909804)). Qed.
Lemma lem3909807 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909808 : term208 = term209.
Proof. exact (@lem3909807 term11 term11). Qed.
Lemma lem3909809 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909810 : term211 = term11.
Proof. exact (EQ_MP (@lem3909809) (@lem940073)). Qed.
Lemma lem3909811 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909812 : term209 = term143.
Proof. exact (MK_COMB (@lem3909811) (@lem3909810)). Qed.
Lemma lem3909813 : term208 = term143.
Proof. exact (TRANS (@lem3909808) (@lem3909812)). Qed.
Lemma lem3909814 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3909815 : term257 = term243.
Proof. exact (MK_COMB (@lem3909814) (@lem3909813)). Qed.
Lemma lem3909816 : term258 = term247.
Proof. exact (MK_COMB (@lem3909815) (@lem3909805)). Qed.
Lemma lem3909818 (m : nat) : (term259 m) = term133.
Proof. exact (proj2 (@lem1367303 m)). Qed.
Lemma lem3909819 : term247 = term133.
Proof. exact (@lem3909818 term11). Qed.
Lemma lem3909820 : term258 = term133.
Proof. exact (TRANS (@lem3909816) (@lem3909819)). Qed.
Lemma lem3909821 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3909822 : term260 = term261.
Proof. exact (MK_COMB (@lem3909821) (@lem3909820)). Qed.
Lemma lem3909823 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3909824 : term262 = term263.
Proof. exact (MK_COMB (@lem3909822) (@lem3909823)). Qed.
Lemma lem3909826 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3909827 : term263 = term133.
Proof. exact (@lem3909826 term11). Qed.
Lemma lem3909828 : term262 = term133.
Proof. exact (TRANS (@lem3909824) (@lem3909827)). Qed.
Lemma lem3909830 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909831 : term208 = term209.
Proof. exact (@lem3909830 term11 term11). Qed.
Lemma lem3909832 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909833 : term211 = term11.
Proof. exact (EQ_MP (@lem3909832) (@lem940073)). Qed.
Lemma lem3909834 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909835 : term209 = term143.
Proof. exact (MK_COMB (@lem3909834) (@lem3909833)). Qed.
Lemma lem3909836 : term208 = term143.
Proof. exact (TRANS (@lem3909831) (@lem3909835)). Qed.
Lemma lem3909837 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3909838 : term265 = term263.
Proof. exact (MK_COMB (@lem3909837) (@lem3909836)). Qed.
Lemma lem3909840 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3909841 : term263 = term133.
Proof. exact (@lem3909840 term11). Qed.
Lemma lem3909842 : term265 = term133.
Proof. exact (TRANS (@lem3909838) (@lem3909841)). Qed.
Lemma lem3909843 : term133 = term265.
Proof. exact (SYM (@lem3909842)). Qed.
Lemma lem3909844 : term262 = term265.
Proof. exact (TRANS (@lem3909828) (@lem3909843)). Qed.
Lemma lem3909845 : term248 = term196.
Proof. exact (@lem3909795 (@lem3909844)). Qed.
Lemma lem3909846 : term247 = term196.
Proof. exact (TRANS (@lem3909761) (@lem3909845)). Qed.
Lemma lem3909848 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3909849 : term196 = term133.
Proof. exact (@lem3909848 term133). Qed.
Lemma lem3909850 : term247 = term133.
Proof. exact (TRANS (@lem3909846) (@lem3909849)). Qed.
Lemma lem3909851 (_45439 : int) : (term233 _45439) = (term233 _45439).
Proof. exact (eq_refl (term233 _45439)). Qed.
Lemma lem3909852 (_45439 : int) : (term245 _45439) = (term266 _45439).
Proof. exact (MK_COMB (@lem3909851 _45439) (@lem3909850)). Qed.
Lemma lem3909853 (_45439 : int) : (term244 _45439) = (term266 _45439).
Proof. exact (TRANS (@lem3909752 _45439) (@lem3909852 _45439)). Qed.
Lemma lem3909854 (_45439 : int) : (term266 _45439) = (term237 _45439).
Proof. exact (@lem1982723 (term237 _45439)). Qed.
Lemma lem3909855 (_45439 : int) : (term244 _45439) = (term237 _45439).
Proof. exact (TRANS (@lem3909853 _45439) (@lem3909854 _45439)). Qed.
Lemma lem3909856 (_45439 : int) : (term242 _45439) = (term237 _45439).
Proof. exact (TRANS (@lem3909751 _45439) (@lem3909855 _45439)). Qed.
Lemma lem3909858 (_45439 : int) : (term241 _45439) = (term237 _45439).
Proof. exact (TRANS (@lem3909706 _45439) (@lem3909856 _45439)). Qed.
Lemma lem3909859 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3909860 (_45439 : int) : (term267 _45439) = (term268 _45439).
Proof. exact (MK_COMB (@lem3909859) (@lem3909858 _45439)). Qed.
Lemma lem3909861 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3909862 (_45439 : int) : (term240 _45439) = (term269 _45439).
Proof. exact (MK_COMB (@lem3909860 _45439) (@lem3909861)). Qed.
Lemma lem3909863 (_45439 : int) : (term152 _45439) = (term269 _45439).
Proof. exact (TRANS (@lem3909694 _45439) (@lem3909862 _45439)). Qed.
Lemma lem3909864 (_45438 : int) : ((real_of_int _45438) = term133) = ((term193 _45438) = term133).
Proof. exact (@lem1988293 (real_of_int _45438) term133). Qed.
Lemma lem3909870 (_45438 : int) : (term193 _45438) = (term194 _45438).
Proof. exact (@lem1982792 (real_of_int _45438) term133). Qed.
Lemma lem3909872 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3909873 : term133 = term196.
Proof. exact (@lem3909872 (NUMERAL 0)). Qed.
Lemma lem3909875 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3909876 : term199 = term200.
Proof. exact (@lem3909875 term11). Qed.
Lemma lem3909877 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3909878 : term201 = term202.
Proof. exact (MK_COMB (@lem3909877) (@lem3909876)). Qed.
Lemma lem3909879 : term203 = term204.
Proof. exact (MK_COMB (@lem3909878) (@lem3909873)). Qed.
Lemma lem3909880 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3909882 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909883 : term208 = term209.
Proof. exact (@lem3909882 term11 term11). Qed.
Lemma lem3909884 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909885 : term211 = term11.
Proof. exact (EQ_MP (@lem3909884) (@lem940073)). Qed.
Lemma lem3909886 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909887 : term209 = term143.
Proof. exact (MK_COMB (@lem3909886) (@lem3909885)). Qed.
Lemma lem3909888 : term208 = term143.
Proof. exact (TRANS (@lem3909883) (@lem3909887)). Qed.
Lemma lem3909890 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3909891 : term203 = term133.
Proof. exact (@lem3909890 term11). Qed.
Lemma lem3909892 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3909893 : term213 = term214.
Proof. exact (MK_COMB (@lem3909892) (@lem3909891)). Qed.
Lemma lem3909894 : term205 = term196.
Proof. exact (MK_COMB (@lem3909893) (@lem3909888)). Qed.
Lemma lem3909895 : term204 = term196.
Proof. exact (TRANS (@lem3909880) (@lem3909894)). Qed.
Lemma lem3909896 : term203 = term196.
Proof. exact (TRANS (@lem3909879) (@lem3909895)). Qed.
Lemma lem3909898 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3909899 : term196 = term133.
Proof. exact (@lem3909898 term133). Qed.
Lemma lem3909900 : term203 = term133.
Proof. exact (TRANS (@lem3909896) (@lem3909899)). Qed.
Lemma lem3909901 (_45438 : int) : (term144 _45438) = (term144 _45438).
Proof. exact (eq_refl (term144 _45438)). Qed.
Lemma lem3909902 (_45438 : int) : (term194 _45438) = (term216 _45438).
Proof. exact (MK_COMB (@lem3909901 _45438) (@lem3909900)). Qed.
Lemma lem3909903 (_45438 : int) : (term216 _45438) = (real_of_int _45438).
Proof. exact (@lem1982723 (real_of_int _45438)). Qed.
Lemma lem3909904 (_45438 : int) : (term194 _45438) = (real_of_int _45438).
Proof. exact (TRANS (@lem3909902 _45438) (@lem3909903 _45438)). Qed.
Lemma lem3909906 (_45438 : int) : (term193 _45438) = (real_of_int _45438).
Proof. exact (TRANS (@lem3909870 _45438) (@lem3909904 _45438)). Qed.
Lemma lem3909907 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3909908 (_45438 : int) : (term270 _45438) = (term146 _45438).
Proof. exact (MK_COMB (@lem3909907) (@lem3909906 _45438)). Qed.
Lemma lem3909909 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3909910 (_45438 : int) : ((term193 _45438) = term133) = ((real_of_int _45438) = term133).
Proof. exact (MK_COMB (@lem3909908 _45438) (@lem3909909)). Qed.
Lemma lem3909911 (_45438 : int) : ((real_of_int _45438) = term133) = ((real_of_int _45438) = term133).
Proof. exact (TRANS (@lem3909864 _45438) (@lem3909910 _45438)). Qed.
Lemma lem3909912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3909913 (_45439 : int) : (term153 _45439) = (term271 _45439).
Proof. exact (MK_COMB (@lem3909912) (@lem3909863 _45439)). Qed.
Lemma lem3909914 (_45439 : int) (_45438 : int) : (term154 _45439 _45438) = (term272 _45439 _45438).
Proof. exact (MK_COMB (@lem3909913 _45439) (@lem3909911 _45438)). Qed.
Lemma lem3909915 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909916 (_45438 : int) (_45439 : int) : (term155 _45439 _45438) = (term273 _45438 _45439).
Proof. exact (MK_COMB (@lem3909915) (@lem3909693 _45438 _45439)). Qed.
Lemma lem3909917 (_45439 : int) (_45438 : int) : (term156 _45439 _45438) = (term274 _45439 _45438).
Proof. exact (MK_COMB (@lem3909916 _45438 _45439) (@lem3909914 _45439 _45438)). Qed.
Lemma lem3909918 (_45438 : int) (_45439 : int) : (term129 _45439 _45438) = (term275 _45438 _45439).
Proof. exact (@lem1988287 (real_of_int _45438) (real_of_int _45439)). Qed.
Lemma lem3909931 (_45438 : int) (_45439 : int) : (term276 _45438 _45439) = (term277 _45438 _45439).
Proof. exact (@lem1982792 (real_of_int _45438) (real_of_int _45439)). Qed.
Lemma lem3909932 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3909933 (_45438 : int) (_45439 : int) : (term278 _45438 _45439) = (term279 _45438 _45439).
Proof. exact (MK_COMB (@lem3909932) (@lem3909931 _45438 _45439)). Qed.
Lemma lem3909934 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3909935 (_45438 : int) (_45439 : int) : (term275 _45438 _45439) = (term280 _45438 _45439).
Proof. exact (MK_COMB (@lem3909933 _45438 _45439) (@lem3909934)). Qed.
Lemma lem3909936 (_45438 : int) (_45439 : int) : (term129 _45439 _45438) = (term280 _45438 _45439).
Proof. exact (TRANS (@lem3909918 _45438 _45439) (@lem3909935 _45438 _45439)). Qed.
Lemma lem3909937 (_45439 : int) : ((real_of_int _45439) = term133) = ((term193 _45439) = term133).
Proof. exact (@lem1988293 (real_of_int _45439) term133). Qed.
Lemma lem3909943 (_45439 : int) : (term193 _45439) = (term194 _45439).
Proof. exact (@lem1982792 (real_of_int _45439) term133). Qed.
Lemma lem3909945 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3909946 : term133 = term196.
Proof. exact (@lem3909945 (NUMERAL 0)). Qed.
Lemma lem3909948 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3909949 : term199 = term200.
Proof. exact (@lem3909948 term11). Qed.
Lemma lem3909950 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3909951 : term201 = term202.
Proof. exact (MK_COMB (@lem3909950) (@lem3909949)). Qed.
Lemma lem3909952 : term203 = term204.
Proof. exact (MK_COMB (@lem3909951) (@lem3909946)). Qed.
Lemma lem3909953 : term204 = term205.
Proof. exact (@lem1981613 term199 term133 term143 term143). Qed.
Lemma lem3909955 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3909956 : term208 = term209.
Proof. exact (@lem3909955 term11 term11). Qed.
Lemma lem3909957 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3909958 : term211 = term11.
Proof. exact (EQ_MP (@lem3909957) (@lem940073)). Qed.
Lemma lem3909959 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3909960 : term209 = term143.
Proof. exact (MK_COMB (@lem3909959) (@lem3909958)). Qed.
Lemma lem3909961 : term208 = term143.
Proof. exact (TRANS (@lem3909956) (@lem3909960)). Qed.
Lemma lem3909963 (x : nat) : (term212 x) = term133.
Proof. exact (proj2 (@lem1367254 x)). Qed.
Lemma lem3909964 : term203 = term133.
Proof. exact (@lem3909963 term11). Qed.
Lemma lem3909965 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3909966 : term213 = term214.
Proof. exact (MK_COMB (@lem3909965) (@lem3909964)). Qed.
Lemma lem3909967 : term205 = term196.
Proof. exact (MK_COMB (@lem3909966) (@lem3909961)). Qed.
Lemma lem3909968 : term204 = term196.
Proof. exact (TRANS (@lem3909953) (@lem3909967)). Qed.
Lemma lem3909969 : term203 = term196.
Proof. exact (TRANS (@lem3909952) (@lem3909968)). Qed.
Lemma lem3909971 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3909972 : term196 = term133.
Proof. exact (@lem3909971 term133). Qed.
Lemma lem3909973 : term203 = term133.
Proof. exact (TRANS (@lem3909969) (@lem3909972)). Qed.
Lemma lem3909974 (_45439 : int) : (term144 _45439) = (term144 _45439).
Proof. exact (eq_refl (term144 _45439)). Qed.
Lemma lem3909975 (_45439 : int) : (term194 _45439) = (term216 _45439).
Proof. exact (MK_COMB (@lem3909974 _45439) (@lem3909973)). Qed.
Lemma lem3909976 (_45439 : int) : (term216 _45439) = (real_of_int _45439).
Proof. exact (@lem1982723 (real_of_int _45439)). Qed.
Lemma lem3909977 (_45439 : int) : (term194 _45439) = (real_of_int _45439).
Proof. exact (TRANS (@lem3909975 _45439) (@lem3909976 _45439)). Qed.
Lemma lem3909979 (_45439 : int) : (term193 _45439) = (real_of_int _45439).
Proof. exact (TRANS (@lem3909943 _45439) (@lem3909977 _45439)). Qed.
Lemma lem3909980 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3909981 (_45439 : int) : (term270 _45439) = (term146 _45439).
Proof. exact (MK_COMB (@lem3909980) (@lem3909979 _45439)). Qed.
Lemma lem3909982 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3909983 (_45439 : int) : ((term193 _45439) = term133) = ((real_of_int _45439) = term133).
Proof. exact (MK_COMB (@lem3909981 _45439) (@lem3909982)). Qed.
Lemma lem3909984 (_45439 : int) : ((real_of_int _45439) = term133) = ((real_of_int _45439) = term133).
Proof. exact (TRANS (@lem3909937 _45439) (@lem3909983 _45439)). Qed.
Lemma lem3909985 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3909986 (_45438 : int) (_45439 : int) : (term157 _45439 _45438) = (term281 _45438 _45439).
Proof. exact (MK_COMB (@lem3909985) (@lem3909936 _45438 _45439)). Qed.
Lemma lem3909987 (_45438 : int) (_45439 : int) : (term158 _45438 _45439) = (term282 _45438 _45439).
Proof. exact (MK_COMB (@lem3909986 _45438 _45439) (@lem3909984 _45439)). Qed.
Lemma lem3909988 (_45439 : int) (_45438 : int) : (term160 _45438 _45439) = (term283 _45439 _45438).
Proof. exact (@lem1988287 (real_of_int _45439) (term145 _45438)). Qed.
Lemma lem3910000 (_45439 : int) (_45438 : int) : (term220 _45439 _45438) = (term221 _45439 _45438).
Proof. exact (@lem1982792 (real_of_int _45439) (term145 _45438)). Qed.
Lemma lem3910001 (_45438 : int) : (term222 _45438) = (term223 _45438).
Proof. exact (@lem1982781 (real_of_int _45438) term199 term143). Qed.
Lemma lem3910003 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910004 : term143 = term224.
Proof. exact (@lem3910003 term11). Qed.
Lemma lem3910006 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3910007 : term199 = term200.
Proof. exact (@lem3910006 term11). Qed.
Lemma lem3910008 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3910009 : term201 = term202.
Proof. exact (MK_COMB (@lem3910008) (@lem3910007)). Qed.
Lemma lem3910010 : term225 = term226.
Proof. exact (MK_COMB (@lem3910009) (@lem3910004)). Qed.
Lemma lem3910011 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3910013 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910014 : term208 = term209.
Proof. exact (@lem3910013 term11 term11). Qed.
Lemma lem3910015 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910016 : term211 = term11.
Proof. exact (EQ_MP (@lem3910015) (@lem940073)). Qed.
Lemma lem3910017 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910018 : term209 = term143.
Proof. exact (MK_COMB (@lem3910017) (@lem3910016)). Qed.
Lemma lem3910019 : term208 = term143.
Proof. exact (TRANS (@lem3910014) (@lem3910018)). Qed.
Lemma lem3910021 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3910022 : term225 = term230.
Proof. exact (@lem3910021 term11 term11). Qed.
Lemma lem3910023 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910024 : term211 = term11.
Proof. exact (EQ_MP (@lem3910023) (@lem940073)). Qed.
Lemma lem3910025 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910026 : term209 = term143.
Proof. exact (MK_COMB (@lem3910025) (@lem3910024)). Qed.
Lemma lem3910027 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3910028 : term230 = term199.
Proof. exact (MK_COMB (@lem3910027) (@lem3910026)). Qed.
Lemma lem3910029 : term225 = term199.
Proof. exact (TRANS (@lem3910022) (@lem3910028)). Qed.
Lemma lem3910030 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3910031 : term231 = term232.
Proof. exact (MK_COMB (@lem3910030) (@lem3910029)). Qed.
Lemma lem3910032 : term227 = term200.
Proof. exact (MK_COMB (@lem3910031) (@lem3910019)). Qed.
Lemma lem3910033 : term226 = term200.
Proof. exact (TRANS (@lem3910011) (@lem3910032)). Qed.
Lemma lem3910034 : term225 = term200.
Proof. exact (TRANS (@lem3910010) (@lem3910033)). Qed.
Lemma lem3910036 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3910037 : term200 = term199.
Proof. exact (@lem3910036 term199). Qed.
Lemma lem3910038 : term225 = term199.
Proof. exact (TRANS (@lem3910034) (@lem3910037)). Qed.
Lemma lem3910041 (_45438 : int) : (term233 _45438) = (term233 _45438).
Proof. exact (eq_refl (term233 _45438)). Qed.
Lemma lem3910042 (_45438 : int) : (term223 _45438) = (term234 _45438).
Proof. exact (MK_COMB (@lem3910041 _45438) (@lem3910038)). Qed.
Lemma lem3910043 (_45438 : int) : (term222 _45438) = (term234 _45438).
Proof. exact (TRANS (@lem3910001 _45438) (@lem3910042 _45438)). Qed.
Lemma lem3910044 (_45439 : int) : (term144 _45439) = (term144 _45439).
Proof. exact (eq_refl (term144 _45439)). Qed.
Lemma lem3910045 (_45439 : int) (_45438 : int) : (term221 _45439 _45438) = (term235 _45439 _45438).
Proof. exact (MK_COMB (@lem3910044 _45439) (@lem3910043 _45438)). Qed.
Lemma lem3910050 (_45438 : int) (_45439 : int) : (term235 _45439 _45438) = (term236 _45438 _45439).
Proof. exact (@lem1982757 (term237 _45438) (real_of_int _45439) term199). Qed.
Lemma lem3910051 (_45438 : int) (_45439 : int) : (term221 _45439 _45438) = (term236 _45438 _45439).
Proof. exact (TRANS (@lem3910045 _45439 _45438) (@lem3910050 _45438 _45439)). Qed.
Lemma lem3910053 (_45438 : int) (_45439 : int) : (term220 _45439 _45438) = (term236 _45438 _45439).
Proof. exact (TRANS (@lem3910000 _45439 _45438) (@lem3910051 _45438 _45439)). Qed.
Lemma lem3910054 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3910055 (_45438 : int) (_45439 : int) : (term284 _45439 _45438) = (term285 _45438 _45439).
Proof. exact (MK_COMB (@lem3910054) (@lem3910053 _45438 _45439)). Qed.
Lemma lem3910056 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3910057 (_45438 : int) (_45439 : int) : (term283 _45439 _45438) = (term286 _45438 _45439).
Proof. exact (MK_COMB (@lem3910055 _45438 _45439) (@lem3910056)). Qed.
Lemma lem3910058 (_45438 : int) (_45439 : int) : (term160 _45438 _45439) = (term286 _45438 _45439).
Proof. exact (TRANS (@lem3909988 _45439 _45438) (@lem3910057 _45438 _45439)). Qed.
Lemma lem3910059 (_45439 : int) : (term166 _45439) = (term287 _45439).
Proof. exact (@lem1988287 term133 (term145 _45439)). Qed.
Lemma lem3910071 (_45439 : int) : (term288 _45439) = (term289 _45439).
Proof. exact (@lem1982792 term133 (term145 _45439)). Qed.
Lemma lem3910072 (_45439 : int) : (term222 _45439) = (term223 _45439).
Proof. exact (@lem1982781 (real_of_int _45439) term199 term143). Qed.
Lemma lem3910074 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910075 : term143 = term224.
Proof. exact (@lem3910074 term11). Qed.
Lemma lem3910077 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3910078 : term199 = term200.
Proof. exact (@lem3910077 term11). Qed.
Lemma lem3910079 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3910080 : term201 = term202.
Proof. exact (MK_COMB (@lem3910079) (@lem3910078)). Qed.
Lemma lem3910081 : term225 = term226.
Proof. exact (MK_COMB (@lem3910080) (@lem3910075)). Qed.
Lemma lem3910082 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3910084 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910085 : term208 = term209.
Proof. exact (@lem3910084 term11 term11). Qed.
Lemma lem3910086 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910087 : term211 = term11.
Proof. exact (EQ_MP (@lem3910086) (@lem940073)). Qed.
Lemma lem3910088 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910089 : term209 = term143.
Proof. exact (MK_COMB (@lem3910088) (@lem3910087)). Qed.
Lemma lem3910090 : term208 = term143.
Proof. exact (TRANS (@lem3910085) (@lem3910089)). Qed.
Lemma lem3910092 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3910093 : term225 = term230.
Proof. exact (@lem3910092 term11 term11). Qed.
Lemma lem3910094 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910095 : term211 = term11.
Proof. exact (EQ_MP (@lem3910094) (@lem940073)). Qed.
Lemma lem3910096 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910097 : term209 = term143.
Proof. exact (MK_COMB (@lem3910096) (@lem3910095)). Qed.
Lemma lem3910098 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3910099 : term230 = term199.
Proof. exact (MK_COMB (@lem3910098) (@lem3910097)). Qed.
Lemma lem3910100 : term225 = term199.
Proof. exact (TRANS (@lem3910093) (@lem3910099)). Qed.
Lemma lem3910101 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3910102 : term231 = term232.
Proof. exact (MK_COMB (@lem3910101) (@lem3910100)). Qed.
Lemma lem3910103 : term227 = term200.
Proof. exact (MK_COMB (@lem3910102) (@lem3910090)). Qed.
Lemma lem3910104 : term226 = term200.
Proof. exact (TRANS (@lem3910082) (@lem3910103)). Qed.
Lemma lem3910105 : term225 = term200.
Proof. exact (TRANS (@lem3910081) (@lem3910104)). Qed.
Lemma lem3910107 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3910108 : term200 = term199.
Proof. exact (@lem3910107 term199). Qed.
Lemma lem3910109 : term225 = term199.
Proof. exact (TRANS (@lem3910105) (@lem3910108)). Qed.
Lemma lem3910112 (_45439 : int) : (term233 _45439) = (term233 _45439).
Proof. exact (eq_refl (term233 _45439)). Qed.
Lemma lem3910113 (_45439 : int) : (term223 _45439) = (term234 _45439).
Proof. exact (MK_COMB (@lem3910112 _45439) (@lem3910109)). Qed.
Lemma lem3910114 (_45439 : int) : (term222 _45439) = (term234 _45439).
Proof. exact (TRANS (@lem3910072 _45439) (@lem3910113 _45439)). Qed.
Lemma lem3910115 : term175 = term175.
Proof. exact (eq_refl term175). Qed.
Lemma lem3910116 (_45439 : int) : (term289 _45439) = (term290 _45439).
Proof. exact (MK_COMB (@lem3910115) (@lem3910114 _45439)). Qed.
Lemma lem3910117 (_45439 : int) : (term290 _45439) = (term234 _45439).
Proof. exact (@lem1982721 (term234 _45439)). Qed.
Lemma lem3910118 (_45439 : int) : (term289 _45439) = (term234 _45439).
Proof. exact (TRANS (@lem3910116 _45439) (@lem3910117 _45439)). Qed.
Lemma lem3910120 (_45439 : int) : (term288 _45439) = (term234 _45439).
Proof. exact (TRANS (@lem3910071 _45439) (@lem3910118 _45439)). Qed.
Lemma lem3910121 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3910122 (_45439 : int) : (term291 _45439) = (term292 _45439).
Proof. exact (MK_COMB (@lem3910121) (@lem3910120 _45439)). Qed.
Lemma lem3910123 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3910124 (_45439 : int) : (term287 _45439) = (term293 _45439).
Proof. exact (MK_COMB (@lem3910122 _45439) (@lem3910123)). Qed.
Lemma lem3910125 (_45439 : int) : (term166 _45439) = (term293 _45439).
Proof. exact (TRANS (@lem3910059 _45439) (@lem3910124 _45439)). Qed.
Lemma lem3910126 (_45439 : int) : (term179 _45439) = (term294 _45439).
Proof. exact (@lem1988287 (real_of_int _45439) term176). Qed.
Lemma lem3910133 : term176 = term143.
Proof. exact (@lem1982721 term143). Qed.
Lemma lem3910136 (_45439 : int) : (term295 _45439) = (term295 _45439).
Proof. exact (eq_refl (term295 _45439)). Qed.
Lemma lem3910137 (_45439 : int) : (term296 _45439) = (term297 _45439).
Proof. exact (MK_COMB (@lem3910136 _45439) (@lem3910133)). Qed.
Lemma lem3910138 (_45439 : int) : (term297 _45439) = (term298 _45439).
Proof. exact (@lem1982792 (real_of_int _45439) term143). Qed.
Lemma lem3910140 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910141 : term143 = term224.
Proof. exact (@lem3910140 term11). Qed.
Lemma lem3910143 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3910144 : term199 = term200.
Proof. exact (@lem3910143 term11). Qed.
Lemma lem3910145 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3910146 : term201 = term202.
Proof. exact (MK_COMB (@lem3910145) (@lem3910144)). Qed.
Lemma lem3910147 : term225 = term226.
Proof. exact (MK_COMB (@lem3910146) (@lem3910141)). Qed.
Lemma lem3910148 : term226 = term227.
Proof. exact (@lem1981613 term199 term143 term143 term143). Qed.
Lemma lem3910150 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910151 : term208 = term209.
Proof. exact (@lem3910150 term11 term11). Qed.
Lemma lem3910152 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910153 : term211 = term11.
Proof. exact (EQ_MP (@lem3910152) (@lem940073)). Qed.
Lemma lem3910154 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910155 : term209 = term143.
Proof. exact (MK_COMB (@lem3910154) (@lem3910153)). Qed.
Lemma lem3910156 : term208 = term143.
Proof. exact (TRANS (@lem3910151) (@lem3910155)). Qed.
Lemma lem3910158 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3910159 : term225 = term230.
Proof. exact (@lem3910158 term11 term11). Qed.
Lemma lem3910160 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910161 : term211 = term11.
Proof. exact (EQ_MP (@lem3910160) (@lem940073)). Qed.
Lemma lem3910162 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910163 : term209 = term143.
Proof. exact (MK_COMB (@lem3910162) (@lem3910161)). Qed.
Lemma lem3910164 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3910165 : term230 = term199.
Proof. exact (MK_COMB (@lem3910164) (@lem3910163)). Qed.
Lemma lem3910166 : term225 = term199.
Proof. exact (TRANS (@lem3910159) (@lem3910165)). Qed.
Lemma lem3910167 : real_div = real_div.
Proof. exact (eq_refl real_div). Qed.
Lemma lem3910168 : term231 = term232.
Proof. exact (MK_COMB (@lem3910167) (@lem3910166)). Qed.
Lemma lem3910169 : term227 = term200.
Proof. exact (MK_COMB (@lem3910168) (@lem3910156)). Qed.
Lemma lem3910170 : term226 = term200.
Proof. exact (TRANS (@lem3910148) (@lem3910169)). Qed.
Lemma lem3910171 : term225 = term200.
Proof. exact (TRANS (@lem3910147) (@lem3910170)). Qed.
Lemma lem3910173 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1982628 x) (@lem1982627 x)). Qed.
Lemma lem3910174 : term200 = term199.
Proof. exact (@lem3910173 term199). Qed.
Lemma lem3910175 : term225 = term199.
Proof. exact (TRANS (@lem3910171) (@lem3910174)). Qed.
Lemma lem3910176 (_45439 : int) : (term144 _45439) = (term144 _45439).
Proof. exact (eq_refl (term144 _45439)). Qed.
Lemma lem3910179 (_45439 : int) : (term298 _45439) = (term299 _45439).
Proof. exact (MK_COMB (@lem3910176 _45439) (@lem3910175)). Qed.
Lemma lem3910180 (_45439 : int) : (term297 _45439) = (term299 _45439).
Proof. exact (TRANS (@lem3910138 _45439) (@lem3910179 _45439)). Qed.
Lemma lem3910181 (_45439 : int) : (term296 _45439) = (term299 _45439).
Proof. exact (TRANS (@lem3910137 _45439) (@lem3910180 _45439)). Qed.
Lemma lem3910182 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3910183 (_45439 : int) : (term300 _45439) = (term301 _45439).
Proof. exact (MK_COMB (@lem3910182) (@lem3910181 _45439)). Qed.
Lemma lem3910184 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3910185 (_45439 : int) : (term294 _45439) = (term302 _45439).
Proof. exact (MK_COMB (@lem3910183 _45439) (@lem3910184)). Qed.
Lemma lem3910186 (_45439 : int) : (term179 _45439) = (term302 _45439).
Proof. exact (TRANS (@lem3910126 _45439) (@lem3910185 _45439)). Qed.
Lemma lem3910187 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910188 (_45439 : int) : (term168 _45439) = (term303 _45439).
Proof. exact (MK_COMB (@lem3910187) (@lem3910125 _45439)). Qed.
Lemma lem3910189 (_45439 : int) : (term180 _45439) = (term304 _45439).
Proof. exact (MK_COMB (@lem3910188 _45439) (@lem3910186 _45439)). Qed.
Lemma lem3910190 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910191 (_45438 : int) (_45439 : int) : (term181 _45438 _45439) = (term305 _45438 _45439).
Proof. exact (MK_COMB (@lem3910190) (@lem3910058 _45438 _45439)). Qed.
Lemma lem3910192 (_45438 : int) (_45439 : int) : (term182 _45438 _45439) = (term306 _45438 _45439).
Proof. exact (MK_COMB (@lem3910191 _45438 _45439) (@lem3910189 _45439)). Qed.
Lemma lem3910193 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3910194 (_45438 : int) (_45439 : int) : (term183 _45438 _45439) = (term307 _45438 _45439).
Proof. exact (MK_COMB (@lem3910193) (@lem3909987 _45438 _45439)). Qed.
Lemma lem3910195 (_45438 : int) (_45439 : int) : (term184 _45438 _45439) = (term308 _45438 _45439).
Proof. exact (MK_COMB (@lem3910194 _45438 _45439) (@lem3910192 _45438 _45439)). Qed.
Lemma lem3910196 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3910197 (_45439 : int) (_45438 : int) : (term185 _45439 _45438) = (term309 _45439 _45438).
Proof. exact (MK_COMB (@lem3910196) (@lem3909917 _45439 _45438)). Qed.
Lemma lem3910198 (_45438 : int) (_45439 : int) : (term186 _45438 _45439) = (term310 _45438 _45439).
Proof. exact (MK_COMB (@lem3910197 _45439 _45438) (@lem3910195 _45438 _45439)). Qed.
Lemma lem3910199 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3910200 (_45439 : int) : (term187 _45439) = (term311 _45439).
Proof. exact (MK_COMB (@lem3910199) (@lem3909622 _45439)). Qed.
Lemma lem3910201 (_45438 : int) (_45439 : int) : (term188 _45438 _45439) = (term312 _45438 _45439).
Proof. exact (MK_COMB (@lem3910200 _45439) (@lem3910198 _45438 _45439)). Qed.
Lemma lem3910202 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3910203 (_45438 : int) : (term187 _45438) = (term311 _45438).
Proof. exact (MK_COMB (@lem3910202) (@lem3909574 _45438)). Qed.
Lemma lem3910204 (_45438 : int) (_45439 : int) : (term189 _45438 _45439) = (term313 _45438 _45439).
Proof. exact (MK_COMB (@lem3910203 _45438) (@lem3910201 _45438 _45439)). Qed.
Lemma lem3910211 (_45438 : int) (_45439 : int) : (term191 _45438 _45439) = (term313 _45438 _45439).
Proof. exact (TRANS (@lem3909526 _45438 _45439) (@lem3910204 _45438 _45439)). Qed.
Lemma lem3910229 (_45438 : int) (_45439 : int) : (term308 _45438 _45439) = (term314 _45438 _45439).
Proof. exact (@lem19158 (term286 _45438 _45439) (term282 _45438 _45439) (term304 _45439)). Qed.
Lemma lem3910230 (_45438 : int) (_45439 : int) : (term315 _45438 _45439) = (term316 _45438 _45439).
Proof. exact (@lem19158 (term293 _45439) (term282 _45438 _45439) (term302 _45439)). Qed.
Lemma lem3910237 (_45438 : int) (_45439 : int) : (term317 _45438 _45439) = (term318 _45438 _45439).
Proof. exact (@lem19367 (term280 _45438 _45439) ((real_of_int _45439) = term133) (term302 _45439)). Qed.
Lemma lem3910244 (_45438 : int) (_45439 : int) : (term319 _45438 _45439) = (term320 _45438 _45439).
Proof. exact (@lem19367 (term280 _45438 _45439) ((real_of_int _45439) = term133) (term293 _45439)). Qed.
Lemma lem3910245 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910246 (_45438 : int) (_45439 : int) : (term321 _45438 _45439) = (term322 _45438 _45439).
Proof. exact (MK_COMB (@lem3910245) (@lem3910244 _45438 _45439)). Qed.
Lemma lem3910247 (_45438 : int) (_45439 : int) : (term316 _45438 _45439) = (term323 _45438 _45439).
Proof. exact (MK_COMB (@lem3910246 _45438 _45439) (@lem3910237 _45438 _45439)). Qed.
Lemma lem3910248 (_45438 : int) (_45439 : int) : (term315 _45438 _45439) = (term323 _45438 _45439).
Proof. exact (TRANS (@lem3910230 _45438 _45439) (@lem3910247 _45438 _45439)). Qed.
Lemma lem3910255 (_45438 : int) (_45439 : int) : (term324 _45438 _45439) = (term325 _45438 _45439).
Proof. exact (@lem19367 (term280 _45438 _45439) ((real_of_int _45439) = term133) (term286 _45438 _45439)). Qed.
Lemma lem3910256 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910257 (_45438 : int) (_45439 : int) : (term326 _45438 _45439) = (term327 _45438 _45439).
Proof. exact (MK_COMB (@lem3910256) (@lem3910255 _45438 _45439)). Qed.
Lemma lem3910258 (_45438 : int) (_45439 : int) : (term314 _45438 _45439) = (term328 _45438 _45439).
Proof. exact (MK_COMB (@lem3910257 _45438 _45439) (@lem3910248 _45438 _45439)). Qed.
Lemma lem3910260 (_45438 : int) (_45439 : int) : (term308 _45438 _45439) = (term328 _45438 _45439).
Proof. exact (TRANS (@lem3910229 _45438 _45439) (@lem3910258 _45438 _45439)). Qed.
Lemma lem3910273 (_45439 : int) (_45438 : int) : (term309 _45439 _45438) = (term309 _45439 _45438).
Proof. exact (eq_refl (term309 _45439 _45438)). Qed.
Lemma lem3910274 (_45438 : int) (_45439 : int) : (term310 _45438 _45439) = (term329 _45438 _45439).
Proof. exact (MK_COMB (@lem3910273 _45439 _45438) (@lem3910260 _45438 _45439)). Qed.
Lemma lem3910275 (_45438 : int) (_45439 : int) : (term329 _45438 _45439) = (term330 _45438 _45439).
Proof. exact (@lem19158 (term325 _45438 _45439) (term274 _45439 _45438) (term323 _45438 _45439)). Qed.
Lemma lem3910276 (_45438 : int) (_45439 : int) : (term331 _45438 _45439) = (term332 _45438 _45439).
Proof. exact (@lem19158 (term320 _45438 _45439) (term274 _45439 _45438) (term318 _45438 _45439)). Qed.
Lemma lem3910277 (_45438 : int) (_45439 : int) : (term333 _45438 _45439) = (term334 _45438 _45439).
Proof. exact (@lem19158 (term335 _45438 _45439) (term274 _45439 _45438) (term336 _45439)). Qed.
Lemma lem3910284 (_45438 : int) (_45439 : int) : (term337 _45438 _45439) = (term338 _45438 _45439).
Proof. exact (@lem19367 ((term236 _45438 _45439) = term133) (term272 _45439 _45438) (term336 _45439)). Qed.
Lemma lem3910291 (_45438 : int) (_45439 : int) : (term339 _45438 _45439) = (term340 _45438 _45439).
Proof. exact (@lem19367 ((term236 _45438 _45439) = term133) (term272 _45439 _45438) (term335 _45438 _45439)). Qed.
Lemma lem3910292 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910293 (_45438 : int) (_45439 : int) : (term341 _45438 _45439) = (term342 _45438 _45439).
Proof. exact (MK_COMB (@lem3910292) (@lem3910291 _45438 _45439)). Qed.
Lemma lem3910294 (_45438 : int) (_45439 : int) : (term334 _45438 _45439) = (term343 _45438 _45439).
Proof. exact (MK_COMB (@lem3910293 _45438 _45439) (@lem3910284 _45438 _45439)). Qed.
Lemma lem3910295 (_45438 : int) (_45439 : int) : (term333 _45438 _45439) = (term343 _45438 _45439).
Proof. exact (TRANS (@lem3910277 _45438 _45439) (@lem3910294 _45438 _45439)). Qed.
Lemma lem3910296 (_45438 : int) (_45439 : int) : (term344 _45438 _45439) = (term345 _45438 _45439).
Proof. exact (@lem19158 (term346 _45438 _45439) (term274 _45439 _45438) (term347 _45439)). Qed.
Lemma lem3910303 (_45438 : int) (_45439 : int) : (term348 _45438 _45439) = (term349 _45438 _45439).
Proof. exact (@lem19367 ((term236 _45438 _45439) = term133) (term272 _45439 _45438) (term347 _45439)). Qed.
Lemma lem3910310 (_45438 : int) (_45439 : int) : (term350 _45438 _45439) = (term351 _45438 _45439).
Proof. exact (@lem19367 ((term236 _45438 _45439) = term133) (term272 _45439 _45438) (term346 _45438 _45439)). Qed.
Lemma lem3910311 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910312 (_45438 : int) (_45439 : int) : (term352 _45438 _45439) = (term353 _45438 _45439).
Proof. exact (MK_COMB (@lem3910311) (@lem3910310 _45438 _45439)). Qed.
Lemma lem3910313 (_45438 : int) (_45439 : int) : (term345 _45438 _45439) = (term354 _45438 _45439).
Proof. exact (MK_COMB (@lem3910312 _45438 _45439) (@lem3910303 _45438 _45439)). Qed.
Lemma lem3910314 (_45438 : int) (_45439 : int) : (term344 _45438 _45439) = (term354 _45438 _45439).
Proof. exact (TRANS (@lem3910296 _45438 _45439) (@lem3910313 _45438 _45439)). Qed.
Lemma lem3910315 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910316 (_45438 : int) (_45439 : int) : (term355 _45438 _45439) = (term356 _45438 _45439).
Proof. exact (MK_COMB (@lem3910315) (@lem3910314 _45438 _45439)). Qed.
Lemma lem3910317 (_45438 : int) (_45439 : int) : (term332 _45438 _45439) = (term357 _45438 _45439).
Proof. exact (MK_COMB (@lem3910316 _45438 _45439) (@lem3910295 _45438 _45439)). Qed.
Lemma lem3910318 (_45438 : int) (_45439 : int) : (term331 _45438 _45439) = (term357 _45438 _45439).
Proof. exact (TRANS (@lem3910276 _45438 _45439) (@lem3910317 _45438 _45439)). Qed.
Lemma lem3910319 (_45438 : int) (_45439 : int) : (term358 _45438 _45439) = (term359 _45438 _45439).
Proof. exact (@lem19158 (term360 _45438 _45439) (term274 _45439 _45438) (term361 _45438 _45439)). Qed.
Lemma lem3910326 (_45438 : int) (_45439 : int) : (term362 _45438 _45439) = (term363 _45438 _45439).
Proof. exact (@lem19367 ((term236 _45438 _45439) = term133) (term272 _45439 _45438) (term361 _45438 _45439)). Qed.
Lemma lem3910333 (_45438 : int) (_45439 : int) : (term364 _45438 _45439) = (term365 _45438 _45439).
Proof. exact (@lem19367 ((term236 _45438 _45439) = term133) (term272 _45439 _45438) (term360 _45438 _45439)). Qed.
Lemma lem3910334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910335 (_45438 : int) (_45439 : int) : (term366 _45438 _45439) = (term367 _45438 _45439).
Proof. exact (MK_COMB (@lem3910334) (@lem3910333 _45438 _45439)). Qed.
Lemma lem3910336 (_45438 : int) (_45439 : int) : (term359 _45438 _45439) = (term368 _45438 _45439).
Proof. exact (MK_COMB (@lem3910335 _45438 _45439) (@lem3910326 _45438 _45439)). Qed.
Lemma lem3910337 (_45438 : int) (_45439 : int) : (term358 _45438 _45439) = (term368 _45438 _45439).
Proof. exact (TRANS (@lem3910319 _45438 _45439) (@lem3910336 _45438 _45439)). Qed.
Lemma lem3910338 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910339 (_45438 : int) (_45439 : int) : (term369 _45438 _45439) = (term370 _45438 _45439).
Proof. exact (MK_COMB (@lem3910338) (@lem3910337 _45438 _45439)). Qed.
Lemma lem3910340 (_45438 : int) (_45439 : int) : (term330 _45438 _45439) = (term371 _45438 _45439).
Proof. exact (MK_COMB (@lem3910339 _45438 _45439) (@lem3910318 _45438 _45439)). Qed.
Lemma lem3910341 (_45438 : int) (_45439 : int) : (term329 _45438 _45439) = (term371 _45438 _45439).
Proof. exact (TRANS (@lem3910275 _45438 _45439) (@lem3910340 _45438 _45439)). Qed.
Lemma lem3910342 (_45438 : int) (_45439 : int) : (term310 _45438 _45439) = (term371 _45438 _45439).
Proof. exact (TRANS (@lem3910274 _45438 _45439) (@lem3910341 _45438 _45439)). Qed.
Lemma lem3910345 (_45439 : int) : (term311 _45439) = (term311 _45439).
Proof. exact (eq_refl (term311 _45439)). Qed.
Lemma lem3910346 (_45438 : int) (_45439 : int) : (term312 _45438 _45439) = (term372 _45438 _45439).
Proof. exact (MK_COMB (@lem3910345 _45439) (@lem3910342 _45438 _45439)). Qed.
Lemma lem3910347 (_45438 : int) (_45439 : int) : (term372 _45438 _45439) = (term373 _45438 _45439).
Proof. exact (@lem19158 (term368 _45438 _45439) (term219 _45439) (term357 _45438 _45439)). Qed.
Lemma lem3910348 (_45438 : int) (_45439 : int) : (term374 _45438 _45439) = (term375 _45438 _45439).
Proof. exact (@lem19158 (term354 _45438 _45439) (term219 _45439) (term343 _45438 _45439)). Qed.
Lemma lem3910349 (_45438 : int) (_45439 : int) : (term376 _45438 _45439) = (term377 _45438 _45439).
Proof. exact (@lem19158 (term340 _45438 _45439) (term219 _45439) (term338 _45438 _45439)). Qed.
Lemma lem3910356 (_45438 : int) (_45439 : int) : (term378 _45438 _45439) = (term379 _45438 _45439).
Proof. exact (@lem19158 (term380 _45438 _45439) (term219 _45439) (term381 _45438 _45439)). Qed.
Lemma lem3910363 (_45438 : int) (_45439 : int) : (term382 _45438 _45439) = (term383 _45438 _45439).
Proof. exact (@lem19158 (term384 _45438 _45439) (term219 _45439) (term385 _45438 _45439)). Qed.
Lemma lem3910364 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910365 (_45438 : int) (_45439 : int) : (term386 _45438 _45439) = (term387 _45438 _45439).
Proof. exact (MK_COMB (@lem3910364) (@lem3910363 _45438 _45439)). Qed.
Lemma lem3910366 (_45438 : int) (_45439 : int) : (term377 _45438 _45439) = (term388 _45438 _45439).
Proof. exact (MK_COMB (@lem3910365 _45438 _45439) (@lem3910356 _45438 _45439)). Qed.
Lemma lem3910367 (_45438 : int) (_45439 : int) : (term376 _45438 _45439) = (term388 _45438 _45439).
Proof. exact (TRANS (@lem3910349 _45438 _45439) (@lem3910366 _45438 _45439)). Qed.
Lemma lem3910368 (_45438 : int) (_45439 : int) : (term389 _45438 _45439) = (term390 _45438 _45439).
Proof. exact (@lem19158 (term351 _45438 _45439) (term219 _45439) (term349 _45438 _45439)). Qed.
Lemma lem3910375 (_45438 : int) (_45439 : int) : (term391 _45438 _45439) = (term392 _45438 _45439).
Proof. exact (@lem19158 (term393 _45438 _45439) (term219 _45439) (term394 _45438 _45439)). Qed.
Lemma lem3910382 (_45438 : int) (_45439 : int) : (term395 _45438 _45439) = (term396 _45438 _45439).
Proof. exact (@lem19158 (term397 _45438 _45439) (term219 _45439) (term398 _45438 _45439)). Qed.
Lemma lem3910383 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910384 (_45438 : int) (_45439 : int) : (term399 _45438 _45439) = (term400 _45438 _45439).
Proof. exact (MK_COMB (@lem3910383) (@lem3910382 _45438 _45439)). Qed.
Lemma lem3910385 (_45438 : int) (_45439 : int) : (term390 _45438 _45439) = (term401 _45438 _45439).
Proof. exact (MK_COMB (@lem3910384 _45438 _45439) (@lem3910375 _45438 _45439)). Qed.
Lemma lem3910386 (_45438 : int) (_45439 : int) : (term389 _45438 _45439) = (term401 _45438 _45439).
Proof. exact (TRANS (@lem3910368 _45438 _45439) (@lem3910385 _45438 _45439)). Qed.
Lemma lem3910387 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910388 (_45438 : int) (_45439 : int) : (term402 _45438 _45439) = (term403 _45438 _45439).
Proof. exact (MK_COMB (@lem3910387) (@lem3910386 _45438 _45439)). Qed.
Lemma lem3910389 (_45438 : int) (_45439 : int) : (term375 _45438 _45439) = (term404 _45438 _45439).
Proof. exact (MK_COMB (@lem3910388 _45438 _45439) (@lem3910367 _45438 _45439)). Qed.
Lemma lem3910390 (_45438 : int) (_45439 : int) : (term374 _45438 _45439) = (term404 _45438 _45439).
Proof. exact (TRANS (@lem3910348 _45438 _45439) (@lem3910389 _45438 _45439)). Qed.
Lemma lem3910391 (_45438 : int) (_45439 : int) : (term405 _45438 _45439) = (term406 _45438 _45439).
Proof. exact (@lem19158 (term365 _45438 _45439) (term219 _45439) (term363 _45438 _45439)). Qed.
Lemma lem3910398 (_45438 : int) (_45439 : int) : (term407 _45438 _45439) = (term408 _45438 _45439).
Proof. exact (@lem19158 (term409 _45438 _45439) (term219 _45439) (term410 _45438 _45439)). Qed.
Lemma lem3910405 (_45438 : int) (_45439 : int) : (term411 _45438 _45439) = (term412 _45438 _45439).
Proof. exact (@lem19158 (term413 _45438 _45439) (term219 _45439) (term414 _45438 _45439)). Qed.
Lemma lem3910406 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910407 (_45438 : int) (_45439 : int) : (term415 _45438 _45439) = (term416 _45438 _45439).
Proof. exact (MK_COMB (@lem3910406) (@lem3910405 _45438 _45439)). Qed.
Lemma lem3910408 (_45438 : int) (_45439 : int) : (term406 _45438 _45439) = (term417 _45438 _45439).
Proof. exact (MK_COMB (@lem3910407 _45438 _45439) (@lem3910398 _45438 _45439)). Qed.
Lemma lem3910409 (_45438 : int) (_45439 : int) : (term405 _45438 _45439) = (term417 _45438 _45439).
Proof. exact (TRANS (@lem3910391 _45438 _45439) (@lem3910408 _45438 _45439)). Qed.
Lemma lem3910410 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910411 (_45438 : int) (_45439 : int) : (term418 _45438 _45439) = (term419 _45438 _45439).
Proof. exact (MK_COMB (@lem3910410) (@lem3910409 _45438 _45439)). Qed.
Lemma lem3910412 (_45438 : int) (_45439 : int) : (term373 _45438 _45439) = (term420 _45438 _45439).
Proof. exact (MK_COMB (@lem3910411 _45438 _45439) (@lem3910390 _45438 _45439)). Qed.
Lemma lem3910413 (_45438 : int) (_45439 : int) : (term372 _45438 _45439) = (term420 _45438 _45439).
Proof. exact (TRANS (@lem3910347 _45438 _45439) (@lem3910412 _45438 _45439)). Qed.
Lemma lem3910414 (_45438 : int) (_45439 : int) : (term312 _45438 _45439) = (term420 _45438 _45439).
Proof. exact (TRANS (@lem3910346 _45438 _45439) (@lem3910413 _45438 _45439)). Qed.
Lemma lem3910417 (_45438 : int) : (term311 _45438) = (term311 _45438).
Proof. exact (eq_refl (term311 _45438)). Qed.
Lemma lem3910418 (_45438 : int) (_45439 : int) : (term313 _45438 _45439) = (term421 _45438 _45439).
Proof. exact (MK_COMB (@lem3910417 _45438) (@lem3910414 _45438 _45439)). Qed.
Lemma lem3910419 (_45438 : int) (_45439 : int) : (term421 _45438 _45439) = (term422 _45438 _45439).
Proof. exact (@lem19158 (term417 _45438 _45439) (term219 _45438) (term404 _45438 _45439)). Qed.
Lemma lem3910420 (_45438 : int) (_45439 : int) : (term423 _45438 _45439) = (term424 _45438 _45439).
Proof. exact (@lem19158 (term401 _45438 _45439) (term219 _45438) (term388 _45438 _45439)). Qed.
Lemma lem3910421 (_45438 : int) (_45439 : int) : (term425 _45438 _45439) = (term426 _45438 _45439).
Proof. exact (@lem19158 (term383 _45438 _45439) (term219 _45438) (term379 _45438 _45439)). Qed.
Lemma lem3910428 (_45438 : int) (_45439 : int) : (term427 _45438 _45439) = (term428 _45438 _45439).
Proof. exact (@lem19158 (term429 _45438 _45439) (term219 _45438) (term430 _45438 _45439)). Qed.
Lemma lem3910435 (_45438 : int) (_45439 : int) : (term431 _45438 _45439) = (term432 _45438 _45439).
Proof. exact (@lem19158 (term433 _45438 _45439) (term219 _45438) (term434 _45438 _45439)). Qed.
Lemma lem3910436 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910437 (_45438 : int) (_45439 : int) : (term435 _45438 _45439) = (term436 _45438 _45439).
Proof. exact (MK_COMB (@lem3910436) (@lem3910435 _45438 _45439)). Qed.
Lemma lem3910438 (_45438 : int) (_45439 : int) : (term426 _45438 _45439) = (term437 _45438 _45439).
Proof. exact (MK_COMB (@lem3910437 _45438 _45439) (@lem3910428 _45438 _45439)). Qed.
Lemma lem3910439 (_45438 : int) (_45439 : int) : (term425 _45438 _45439) = (term437 _45438 _45439).
Proof. exact (TRANS (@lem3910421 _45438 _45439) (@lem3910438 _45438 _45439)). Qed.
Lemma lem3910440 (_45438 : int) (_45439 : int) : (term438 _45438 _45439) = (term439 _45438 _45439).
Proof. exact (@lem19158 (term396 _45438 _45439) (term219 _45438) (term392 _45438 _45439)). Qed.
Lemma lem3910447 (_45438 : int) (_45439 : int) : (term440 _45438 _45439) = (term441 _45438 _45439).
Proof. exact (@lem19158 (term442 _45438 _45439) (term219 _45438) (term443 _45438 _45439)). Qed.
Lemma lem3910454 (_45438 : int) (_45439 : int) : (term444 _45438 _45439) = (term445 _45438 _45439).
Proof. exact (@lem19158 (term446 _45438 _45439) (term219 _45438) (term447 _45438 _45439)). Qed.
Lemma lem3910455 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910456 (_45438 : int) (_45439 : int) : (term448 _45438 _45439) = (term449 _45438 _45439).
Proof. exact (MK_COMB (@lem3910455) (@lem3910454 _45438 _45439)). Qed.
Lemma lem3910457 (_45438 : int) (_45439 : int) : (term439 _45438 _45439) = (term450 _45438 _45439).
Proof. exact (MK_COMB (@lem3910456 _45438 _45439) (@lem3910447 _45438 _45439)). Qed.
Lemma lem3910458 (_45438 : int) (_45439 : int) : (term438 _45438 _45439) = (term450 _45438 _45439).
Proof. exact (TRANS (@lem3910440 _45438 _45439) (@lem3910457 _45438 _45439)). Qed.
Lemma lem3910459 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910460 (_45438 : int) (_45439 : int) : (term451 _45438 _45439) = (term452 _45438 _45439).
Proof. exact (MK_COMB (@lem3910459) (@lem3910458 _45438 _45439)). Qed.
Lemma lem3910461 (_45438 : int) (_45439 : int) : (term424 _45438 _45439) = (term453 _45438 _45439).
Proof. exact (MK_COMB (@lem3910460 _45438 _45439) (@lem3910439 _45438 _45439)). Qed.
Lemma lem3910462 (_45438 : int) (_45439 : int) : (term423 _45438 _45439) = (term453 _45438 _45439).
Proof. exact (TRANS (@lem3910420 _45438 _45439) (@lem3910461 _45438 _45439)). Qed.
Lemma lem3910463 (_45438 : int) (_45439 : int) : (term454 _45438 _45439) = (term455 _45438 _45439).
Proof. exact (@lem19158 (term412 _45438 _45439) (term219 _45438) (term408 _45438 _45439)). Qed.
Lemma lem3910470 (_45438 : int) (_45439 : int) : (term456 _45438 _45439) = (term457 _45438 _45439).
Proof. exact (@lem19158 (term458 _45438 _45439) (term219 _45438) (term459 _45438 _45439)). Qed.
Lemma lem3910477 (_45438 : int) (_45439 : int) : (term460 _45438 _45439) = (term461 _45438 _45439).
Proof. exact (@lem19158 (term462 _45438 _45439) (term219 _45438) (term463 _45438 _45439)). Qed.
Lemma lem3910478 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910479 (_45438 : int) (_45439 : int) : (term464 _45438 _45439) = (term465 _45438 _45439).
Proof. exact (MK_COMB (@lem3910478) (@lem3910477 _45438 _45439)). Qed.
Lemma lem3910480 (_45438 : int) (_45439 : int) : (term455 _45438 _45439) = (term466 _45438 _45439).
Proof. exact (MK_COMB (@lem3910479 _45438 _45439) (@lem3910470 _45438 _45439)). Qed.
Lemma lem3910481 (_45438 : int) (_45439 : int) : (term454 _45438 _45439) = (term466 _45438 _45439).
Proof. exact (TRANS (@lem3910463 _45438 _45439) (@lem3910480 _45438 _45439)). Qed.
Lemma lem3910482 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3910483 (_45438 : int) (_45439 : int) : (term467 _45438 _45439) = (term468 _45438 _45439).
Proof. exact (MK_COMB (@lem3910482) (@lem3910481 _45438 _45439)). Qed.
Lemma lem3910484 (_45438 : int) (_45439 : int) : (term422 _45438 _45439) = (term469 _45438 _45439).
Proof. exact (MK_COMB (@lem3910483 _45438 _45439) (@lem3910462 _45438 _45439)). Qed.
Lemma lem3910485 (_45438 : int) (_45439 : int) : (term421 _45438 _45439) = (term469 _45438 _45439).
Proof. exact (TRANS (@lem3910419 _45438 _45439) (@lem3910484 _45438 _45439)). Qed.
Lemma lem3910486 (_45438 : int) (_45439 : int) : (term313 _45438 _45439) = (term469 _45438 _45439).
Proof. exact (TRANS (@lem3910418 _45438 _45439) (@lem3910485 _45438 _45439)). Qed.
Lemma lem3910487 (_45438 : int) (_45439 : int) : (term191 _45438 _45439) = (term469 _45438 _45439).
Proof. exact (TRANS (@lem3910211 _45438 _45439) (@lem3910486 _45438 _45439)). Qed.
Lemma lem3910557 (_45438 : int) (_45439 : int) (h1 : term469 _45438 _45439) : term469 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3910558 (_45438 : int) (_45439 : int) (h1 : term466 _45438 _45439) : term466 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3910559 (_45438 : int) (_45439 : int) (h1 : term461 _45438 _45439) : term461 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3910560 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term470 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3910561 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term462 _45438 _45439.
Proof. exact (proj2 (@lem3910560 _45438 _45439 h1)). Qed.
Lemma lem3910563 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term413 _45438 _45439.
Proof. exact (proj2 (@lem3910561 _45438 _45439 h1)). Qed.
Lemma lem3910565 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term360 _45438 _45439.
Proof. exact (proj2 (@lem3910563 _45438 _45439 h1)). Qed.
Lemma lem3910566 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (proj1 (@lem3910563 _45438 _45439 h1)). Qed.
Lemma lem3910568 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term280 _45438 _45439.
Proof. exact (proj1 (@lem3910565 _45438 _45439 h1)). Qed.
Lemma lem3910570 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3910571 : term471 = term251.
Proof. exact (@lem3910570 term133 term143). Qed.
Lemma lem3910573 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910574 : term143 = term224.
Proof. exact (@lem3910573 term11). Qed.
Lemma lem3910576 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910577 : term133 = term196.
Proof. exact (@lem3910576 (NUMERAL 0)). Qed.
Lemma lem3910578 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3910579 : term472 = term473.
Proof. exact (MK_COMB (@lem3910578) (@lem3910577)). Qed.
Lemma lem3910580 : term251 = term474.
Proof. exact (MK_COMB (@lem3910579) (@lem3910574)). Qed.
Lemma lem3910581 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3910583 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910584 : term251 = term252.
Proof. exact (@lem3910583 (NUMERAL 0) term11). Qed.
Lemma lem3910585 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910586 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910587 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910586 h1) (fun h1 : term252 = True => @lem3910585)). Qed.
Lemma lem3910588 : term252 = True.
Proof. exact (EQ_MP (@lem3910587) (@lem3910585)). Qed.
Lemma lem3910589 : term251 = True.
Proof. exact (TRANS (@lem3910584) (@lem3910588)). Qed.
Lemma lem3910590 : True = term251.
Proof. exact (SYM (@lem3910589)). Qed.
Lemma lem3910591 : term251.
Proof. exact (EQ_MP (@lem3910590) (@lem0)). Qed.
Lemma lem3910592 : term476.
Proof. exact (@lem3910581 (@lem3910591)). Qed.
Lemma lem3910594 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910595 : term251 = term252.
Proof. exact (@lem3910594 (NUMERAL 0) term11). Qed.
Lemma lem3910596 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910597 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910598 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910597 h1) (fun h1 : term252 = True => @lem3910596)). Qed.
Lemma lem3910599 : term252 = True.
Proof. exact (EQ_MP (@lem3910598) (@lem3910596)). Qed.
Lemma lem3910600 : term251 = True.
Proof. exact (TRANS (@lem3910595) (@lem3910599)). Qed.
Lemma lem3910601 : True = term251.
Proof. exact (SYM (@lem3910600)). Qed.
Lemma lem3910602 : term251.
Proof. exact (EQ_MP (@lem3910601) (@lem0)). Qed.
Lemma lem3910603 : term474 = term477.
Proof. exact (@lem3910592 (@lem3910602)). Qed.
Lemma lem3910605 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910606 : term208 = term209.
Proof. exact (@lem3910605 term11 term11). Qed.
Lemma lem3910607 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910608 : term211 = term11.
Proof. exact (EQ_MP (@lem3910607) (@lem940073)). Qed.
Lemma lem3910609 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910610 : term209 = term143.
Proof. exact (MK_COMB (@lem3910609) (@lem3910608)). Qed.
Lemma lem3910611 : term208 = term143.
Proof. exact (TRANS (@lem3910606) (@lem3910610)). Qed.
Lemma lem3910613 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3910614 : term263 = term133.
Proof. exact (@lem3910613 term11). Qed.
Lemma lem3910615 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3910616 : term478 = term472.
Proof. exact (MK_COMB (@lem3910615) (@lem3910614)). Qed.
Lemma lem3910617 : term477 = term251.
Proof. exact (MK_COMB (@lem3910616) (@lem3910611)). Qed.
Lemma lem3910619 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910620 : term251 = term252.
Proof. exact (@lem3910619 (NUMERAL 0) term11). Qed.
Lemma lem3910621 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910622 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910623 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910622 h1) (fun h1 : term252 = True => @lem3910621)). Qed.
Lemma lem3910624 : term252 = True.
Proof. exact (EQ_MP (@lem3910623) (@lem3910621)). Qed.
Lemma lem3910625 : term251 = True.
Proof. exact (TRANS (@lem3910620) (@lem3910624)). Qed.
Lemma lem3910626 : term477 = True.
Proof. exact (TRANS (@lem3910617) (@lem3910625)). Qed.
Lemma lem3910627 : term474 = True.
Proof. exact (TRANS (@lem3910603) (@lem3910626)). Qed.
Lemma lem3910628 : term251 = True.
Proof. exact (TRANS (@lem3910580) (@lem3910627)). Qed.
Lemma lem3910629 : term471 = True.
Proof. exact (TRANS (@lem3910571) (@lem3910628)). Qed.
Lemma lem3910630 : True = term471.
Proof. exact (SYM (@lem3910629)). Qed.
Lemma lem3910631 : term471.
Proof. exact (EQ_MP (@lem3910630) (@lem0)). Qed.
Lemma lem3910632 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term479 _45438 _45439.
Proof. exact (conj (@lem3910631) (@lem3910568 _45438 _45439 h1)). Qed.
Lemma lem3910634 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3910635 (_45438 : int) (_45439 : int) : term481 _45438 _45439.
Proof. exact (@lem3910634 term143 (term277 _45438 _45439)). Qed.
Lemma lem3910636 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term482 _45438 _45439.
Proof. exact (@lem3910635 _45438 _45439 (@lem3910632 _45438 _45439 h1)). Qed.
Lemma lem3910637 (_45438 : int) (_45439 : int) : (term483 _45438 _45439) = (term277 _45438 _45439).
Proof. exact (@lem1982733 (term277 _45438 _45439)). Qed.
Lemma lem3910638 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3910639 (_45438 : int) (_45439 : int) : (term484 _45438 _45439) = (term279 _45438 _45439).
Proof. exact (MK_COMB (@lem3910638) (@lem3910637 _45438 _45439)). Qed.
Lemma lem3910640 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3910641 (_45438 : int) (_45439 : int) : (term482 _45438 _45439) = (term280 _45438 _45439).
Proof. exact (MK_COMB (@lem3910639 _45438 _45439) (@lem3910640)). Qed.
Lemma lem3910642 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term280 _45438 _45439.
Proof. exact (EQ_MP (@lem3910641 _45438 _45439) (@lem3910636 _45438 _45439 h1)). Qed.
Lemma lem3910644 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3910645 (_45438 : int) (_45439 : int) : term486 _45438 _45439.
Proof. exact (@lem3910644 (term236 _45438 _45439)). Qed.
Lemma lem3910646 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term487 _45438 _45439.
Proof. exact (@lem3910645 _45438 _45439 (@lem3910566 _45438 _45439 h1)). Qed.
Lemma lem3910647 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term488 _45438 _45439.
Proof. exact (@lem3910646 _45438 _45439 h1 term143). Qed.
Lemma lem3910648 (_45438 : int) (_45439 : int) : (term488 _45438 _45439) = ((term489 _45438 _45439) = term133).
Proof. exact (eq_refl (term488 _45438 _45439)). Qed.
Lemma lem3910649 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : (term489 _45438 _45439) = term133.
Proof. exact (EQ_MP (@lem3910648 _45438 _45439) (@lem3910647 _45438 _45439 h1)). Qed.
Lemma lem3910650 (_45438 : int) (_45439 : int) : (term489 _45438 _45439) = (term236 _45438 _45439).
Proof. exact (@lem1982733 (term236 _45438 _45439)). Qed.
Lemma lem3910651 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3910652 (_45438 : int) (_45439 : int) : (term490 _45438 _45439) = (term239 _45438 _45439).
Proof. exact (MK_COMB (@lem3910651) (@lem3910650 _45438 _45439)). Qed.
Lemma lem3910653 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3910654 (_45438 : int) (_45439 : int) : ((term489 _45438 _45439) = term133) = ((term236 _45438 _45439) = term133).
Proof. exact (MK_COMB (@lem3910652 _45438 _45439) (@lem3910653)). Qed.
Lemma lem3910655 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (EQ_MP (@lem3910654 _45438 _45439) (@lem3910649 _45438 _45439 h1)). Qed.
Lemma lem3910656 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term491 _45438 _45439.
Proof. exact (conj (@lem3910655 _45438 _45439 h1) (@lem3910642 _45438 _45439 h1)). Qed.
Lemma lem3910658 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3910659 (_45438 : int) (_45439 : int) : term493 _45438 _45439.
Proof. exact (@lem3910658 (term236 _45438 _45439) (term277 _45438 _45439)). Qed.
Lemma lem3910660 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term494 _45438 _45439.
Proof. exact (@lem3910659 _45438 _45439 (@lem3910656 _45438 _45439 h1)). Qed.
Lemma lem3910661 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = (term496 _45438 _45439).
Proof. exact (@lem1982753 (term237 _45438) (real_of_int _45438) (term299 _45439) (term237 _45439)). Qed.
Lemma lem3910662 (_45438 : int) : (term497 _45438) = (term498 _45438).
Proof. exact (@lem1982713 term199 (real_of_int _45438)). Qed.
Lemma lem3910664 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910665 : term143 = term224.
Proof. exact (@lem3910664 term11). Qed.
Lemma lem3910667 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3910668 : term199 = term200.
Proof. exact (@lem3910667 term11). Qed.
Lemma lem3910669 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3910670 : term499 = term500.
Proof. exact (MK_COMB (@lem3910669) (@lem3910668)). Qed.
Lemma lem3910671 : term501 = term502.
Proof. exact (MK_COMB (@lem3910670) (@lem3910665)). Qed.
Lemma lem3910672 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3910674 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910675 : term251 = term252.
Proof. exact (@lem3910674 (NUMERAL 0) term11). Qed.
Lemma lem3910676 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910677 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910678 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910677 h1) (fun h1 : term252 = True => @lem3910676)). Qed.
Lemma lem3910679 : term252 = True.
Proof. exact (EQ_MP (@lem3910678) (@lem3910676)). Qed.
Lemma lem3910680 : term251 = True.
Proof. exact (TRANS (@lem3910675) (@lem3910679)). Qed.
Lemma lem3910681 : True = term251.
Proof. exact (SYM (@lem3910680)). Qed.
Lemma lem3910682 : term251.
Proof. exact (EQ_MP (@lem3910681) (@lem0)). Qed.
Lemma lem3910683 : term504.
Proof. exact (@lem3910672 (@lem3910682)). Qed.
Lemma lem3910685 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910686 : term251 = term252.
Proof. exact (@lem3910685 (NUMERAL 0) term11). Qed.
Lemma lem3910687 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910688 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910689 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910688 h1) (fun h1 : term252 = True => @lem3910687)). Qed.
Lemma lem3910690 : term252 = True.
Proof. exact (EQ_MP (@lem3910689) (@lem3910687)). Qed.
Lemma lem3910691 : term251 = True.
Proof. exact (TRANS (@lem3910686) (@lem3910690)). Qed.
Lemma lem3910692 : True = term251.
Proof. exact (SYM (@lem3910691)). Qed.
Lemma lem3910693 : term251.
Proof. exact (EQ_MP (@lem3910692) (@lem0)). Qed.
Lemma lem3910694 : term505.
Proof. exact (@lem3910683 (@lem3910693)). Qed.
Lemma lem3910696 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910697 : term251 = term252.
Proof. exact (@lem3910696 (NUMERAL 0) term11). Qed.
Lemma lem3910698 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910699 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910700 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910699 h1) (fun h1 : term252 = True => @lem3910698)). Qed.
Lemma lem3910701 : term252 = True.
Proof. exact (EQ_MP (@lem3910700) (@lem3910698)). Qed.
Lemma lem3910702 : term251 = True.
Proof. exact (TRANS (@lem3910697) (@lem3910701)). Qed.
Lemma lem3910703 : True = term251.
Proof. exact (SYM (@lem3910702)). Qed.
Lemma lem3910704 : term251.
Proof. exact (EQ_MP (@lem3910703) (@lem0)). Qed.
Lemma lem3910705 : term506.
Proof. exact (@lem3910694 (@lem3910704)). Qed.
Lemma lem3910707 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910708 : term208 = term209.
Proof. exact (@lem3910707 term11 term11). Qed.
Lemma lem3910709 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910710 : term211 = term11.
Proof. exact (EQ_MP (@lem3910709) (@lem940073)). Qed.
Lemma lem3910711 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910712 : term209 = term143.
Proof. exact (MK_COMB (@lem3910711) (@lem3910710)). Qed.
Lemma lem3910713 : term208 = term143.
Proof. exact (TRANS (@lem3910708) (@lem3910712)). Qed.
Lemma lem3910715 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3910716 : term225 = term230.
Proof. exact (@lem3910715 term11 term11). Qed.
Lemma lem3910717 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910718 : term211 = term11.
Proof. exact (EQ_MP (@lem3910717) (@lem940073)). Qed.
Lemma lem3910719 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910720 : term209 = term143.
Proof. exact (MK_COMB (@lem3910719) (@lem3910718)). Qed.
Lemma lem3910721 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3910722 : term230 = term199.
Proof. exact (MK_COMB (@lem3910721) (@lem3910720)). Qed.
Lemma lem3910723 : term225 = term199.
Proof. exact (TRANS (@lem3910716) (@lem3910722)). Qed.
Lemma lem3910724 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3910725 : term507 = term499.
Proof. exact (MK_COMB (@lem3910724) (@lem3910723)). Qed.
Lemma lem3910726 : term508 = term501.
Proof. exact (MK_COMB (@lem3910725) (@lem3910713)). Qed.
Lemma lem3910728 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3910729 : term501 = term133.
Proof. exact (@lem3910728 term11). Qed.
Lemma lem3910730 : term508 = term133.
Proof. exact (TRANS (@lem3910726) (@lem3910729)). Qed.
Lemma lem3910731 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3910732 : term510 = term261.
Proof. exact (MK_COMB (@lem3910731) (@lem3910730)). Qed.
Lemma lem3910733 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3910734 : term511 = term263.
Proof. exact (MK_COMB (@lem3910732) (@lem3910733)). Qed.
Lemma lem3910736 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3910737 : term263 = term133.
Proof. exact (@lem3910736 term11). Qed.
Lemma lem3910738 : term511 = term133.
Proof. exact (TRANS (@lem3910734) (@lem3910737)). Qed.
Lemma lem3910740 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910741 : term208 = term209.
Proof. exact (@lem3910740 term11 term11). Qed.
Lemma lem3910742 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910743 : term211 = term11.
Proof. exact (EQ_MP (@lem3910742) (@lem940073)). Qed.
Lemma lem3910744 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910745 : term209 = term143.
Proof. exact (MK_COMB (@lem3910744) (@lem3910743)). Qed.
Lemma lem3910746 : term208 = term143.
Proof. exact (TRANS (@lem3910741) (@lem3910745)). Qed.
Lemma lem3910747 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3910748 : term265 = term263.
Proof. exact (MK_COMB (@lem3910747) (@lem3910746)). Qed.
Lemma lem3910750 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3910751 : term263 = term133.
Proof. exact (@lem3910750 term11). Qed.
Lemma lem3910752 : term265 = term133.
Proof. exact (TRANS (@lem3910748) (@lem3910751)). Qed.
Lemma lem3910753 : term133 = term265.
Proof. exact (SYM (@lem3910752)). Qed.
Lemma lem3910754 : term511 = term265.
Proof. exact (TRANS (@lem3910738) (@lem3910753)). Qed.
Lemma lem3910755 : term502 = term196.
Proof. exact (@lem3910705 (@lem3910754)). Qed.
Lemma lem3910756 : term501 = term196.
Proof. exact (TRANS (@lem3910671) (@lem3910755)). Qed.
Lemma lem3910758 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3910759 : term196 = term133.
Proof. exact (@lem3910758 term133). Qed.
Lemma lem3910760 : term501 = term133.
Proof. exact (TRANS (@lem3910756) (@lem3910759)). Qed.
Lemma lem3910761 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3910762 : term512 = term261.
Proof. exact (MK_COMB (@lem3910761) (@lem3910760)). Qed.
Lemma lem3910763 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3910764 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3910762) (@lem3910763 _45438)). Qed.
Lemma lem3910765 (_45438 : int) : (term497 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3910662 _45438) (@lem3910764 _45438)). Qed.
Lemma lem3910766 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3910767 (_45438 : int) : (term497 _45438) = term133.
Proof. exact (TRANS (@lem3910765 _45438) (@lem3910766 _45438)). Qed.
Lemma lem3910768 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3910769 (_45438 : int) : (term514 _45438) = term175.
Proof. exact (MK_COMB (@lem3910768) (@lem3910767 _45438)). Qed.
Lemma lem3910770 (_45439 : int) : (term515 _45439) = (term516 _45439).
Proof. exact (@lem1982759 (real_of_int _45439) (term237 _45439) term199). Qed.
Lemma lem3910771 (_45439 : int) : (term517 _45439) = (term498 _45439).
Proof. exact (@lem1982715 term199 (real_of_int _45439)). Qed.
Lemma lem3910773 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910774 : term143 = term224.
Proof. exact (@lem3910773 term11). Qed.
Lemma lem3910776 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3910777 : term199 = term200.
Proof. exact (@lem3910776 term11). Qed.
Lemma lem3910778 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3910779 : term499 = term500.
Proof. exact (MK_COMB (@lem3910778) (@lem3910777)). Qed.
Lemma lem3910780 : term501 = term502.
Proof. exact (MK_COMB (@lem3910779) (@lem3910774)). Qed.
Lemma lem3910781 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3910783 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910784 : term251 = term252.
Proof. exact (@lem3910783 (NUMERAL 0) term11). Qed.
Lemma lem3910785 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910786 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910787 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910786 h1) (fun h1 : term252 = True => @lem3910785)). Qed.
Lemma lem3910788 : term252 = True.
Proof. exact (EQ_MP (@lem3910787) (@lem3910785)). Qed.
Lemma lem3910789 : term251 = True.
Proof. exact (TRANS (@lem3910784) (@lem3910788)). Qed.
Lemma lem3910790 : True = term251.
Proof. exact (SYM (@lem3910789)). Qed.
Lemma lem3910791 : term251.
Proof. exact (EQ_MP (@lem3910790) (@lem0)). Qed.
Lemma lem3910792 : term504.
Proof. exact (@lem3910781 (@lem3910791)). Qed.
Lemma lem3910794 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910795 : term251 = term252.
Proof. exact (@lem3910794 (NUMERAL 0) term11). Qed.
Lemma lem3910796 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910797 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910798 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910797 h1) (fun h1 : term252 = True => @lem3910796)). Qed.
Lemma lem3910799 : term252 = True.
Proof. exact (EQ_MP (@lem3910798) (@lem3910796)). Qed.
Lemma lem3910800 : term251 = True.
Proof. exact (TRANS (@lem3910795) (@lem3910799)). Qed.
Lemma lem3910801 : True = term251.
Proof. exact (SYM (@lem3910800)). Qed.
Lemma lem3910802 : term251.
Proof. exact (EQ_MP (@lem3910801) (@lem0)). Qed.
Lemma lem3910803 : term505.
Proof. exact (@lem3910792 (@lem3910802)). Qed.
Lemma lem3910805 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910806 : term251 = term252.
Proof. exact (@lem3910805 (NUMERAL 0) term11). Qed.
Lemma lem3910807 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910808 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910809 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910808 h1) (fun h1 : term252 = True => @lem3910807)). Qed.
Lemma lem3910810 : term252 = True.
Proof. exact (EQ_MP (@lem3910809) (@lem3910807)). Qed.
Lemma lem3910811 : term251 = True.
Proof. exact (TRANS (@lem3910806) (@lem3910810)). Qed.
Lemma lem3910812 : True = term251.
Proof. exact (SYM (@lem3910811)). Qed.
Lemma lem3910813 : term251.
Proof. exact (EQ_MP (@lem3910812) (@lem0)). Qed.
Lemma lem3910814 : term506.
Proof. exact (@lem3910803 (@lem3910813)). Qed.
Lemma lem3910816 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910817 : term208 = term209.
Proof. exact (@lem3910816 term11 term11). Qed.
Lemma lem3910818 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910819 : term211 = term11.
Proof. exact (EQ_MP (@lem3910818) (@lem940073)). Qed.
Lemma lem3910820 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910821 : term209 = term143.
Proof. exact (MK_COMB (@lem3910820) (@lem3910819)). Qed.
Lemma lem3910822 : term208 = term143.
Proof. exact (TRANS (@lem3910817) (@lem3910821)). Qed.
Lemma lem3910824 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3910825 : term225 = term230.
Proof. exact (@lem3910824 term11 term11). Qed.
Lemma lem3910826 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910827 : term211 = term11.
Proof. exact (EQ_MP (@lem3910826) (@lem940073)). Qed.
Lemma lem3910828 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910829 : term209 = term143.
Proof. exact (MK_COMB (@lem3910828) (@lem3910827)). Qed.
Lemma lem3910830 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3910831 : term230 = term199.
Proof. exact (MK_COMB (@lem3910830) (@lem3910829)). Qed.
Lemma lem3910832 : term225 = term199.
Proof. exact (TRANS (@lem3910825) (@lem3910831)). Qed.
Lemma lem3910833 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3910834 : term507 = term499.
Proof. exact (MK_COMB (@lem3910833) (@lem3910832)). Qed.
Lemma lem3910835 : term508 = term501.
Proof. exact (MK_COMB (@lem3910834) (@lem3910822)). Qed.
Lemma lem3910837 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3910838 : term501 = term133.
Proof. exact (@lem3910837 term11). Qed.
Lemma lem3910839 : term508 = term133.
Proof. exact (TRANS (@lem3910835) (@lem3910838)). Qed.
Lemma lem3910840 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3910841 : term510 = term261.
Proof. exact (MK_COMB (@lem3910840) (@lem3910839)). Qed.
Lemma lem3910842 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3910843 : term511 = term263.
Proof. exact (MK_COMB (@lem3910841) (@lem3910842)). Qed.
Lemma lem3910845 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3910846 : term263 = term133.
Proof. exact (@lem3910845 term11). Qed.
Lemma lem3910847 : term511 = term133.
Proof. exact (TRANS (@lem3910843) (@lem3910846)). Qed.
Lemma lem3910849 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3910850 : term208 = term209.
Proof. exact (@lem3910849 term11 term11). Qed.
Lemma lem3910851 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910852 : term211 = term11.
Proof. exact (EQ_MP (@lem3910851) (@lem940073)). Qed.
Lemma lem3910853 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910854 : term209 = term143.
Proof. exact (MK_COMB (@lem3910853) (@lem3910852)). Qed.
Lemma lem3910855 : term208 = term143.
Proof. exact (TRANS (@lem3910850) (@lem3910854)). Qed.
Lemma lem3910856 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3910857 : term265 = term263.
Proof. exact (MK_COMB (@lem3910856) (@lem3910855)). Qed.
Lemma lem3910859 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3910860 : term263 = term133.
Proof. exact (@lem3910859 term11). Qed.
Lemma lem3910861 : term265 = term133.
Proof. exact (TRANS (@lem3910857) (@lem3910860)). Qed.
Lemma lem3910862 : term133 = term265.
Proof. exact (SYM (@lem3910861)). Qed.
Lemma lem3910863 : term511 = term265.
Proof. exact (TRANS (@lem3910847) (@lem3910862)). Qed.
Lemma lem3910864 : term502 = term196.
Proof. exact (@lem3910814 (@lem3910863)). Qed.
Lemma lem3910865 : term501 = term196.
Proof. exact (TRANS (@lem3910780) (@lem3910864)). Qed.
Lemma lem3910867 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3910868 : term196 = term133.
Proof. exact (@lem3910867 term133). Qed.
Lemma lem3910869 : term501 = term133.
Proof. exact (TRANS (@lem3910865) (@lem3910868)). Qed.
Lemma lem3910870 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3910871 : term512 = term261.
Proof. exact (MK_COMB (@lem3910870) (@lem3910869)). Qed.
Lemma lem3910872 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3910873 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3910871) (@lem3910872 _45439)). Qed.
Lemma lem3910874 (_45439 : int) : (term517 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3910771 _45439) (@lem3910873 _45439)). Qed.
Lemma lem3910875 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3910876 (_45439 : int) : (term517 _45439) = term133.
Proof. exact (TRANS (@lem3910874 _45439) (@lem3910875 _45439)). Qed.
Lemma lem3910877 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3910878 (_45439 : int) : (term518 _45439) = term175.
Proof. exact (MK_COMB (@lem3910877) (@lem3910876 _45439)). Qed.
Lemma lem3910879 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3910880 (_45439 : int) : (term516 _45439) = term519.
Proof. exact (MK_COMB (@lem3910878 _45439) (@lem3910879)). Qed.
Lemma lem3910881 (_45439 : int) : (term515 _45439) = term519.
Proof. exact (TRANS (@lem3910770 _45439) (@lem3910880 _45439)). Qed.
Lemma lem3910882 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3910883 (_45439 : int) : (term515 _45439) = term199.
Proof. exact (TRANS (@lem3910881 _45439) (@lem3910882)). Qed.
Lemma lem3910884 (_45438 : int) (_45439 : int) : (term496 _45438 _45439) = term519.
Proof. exact (MK_COMB (@lem3910769 _45438) (@lem3910883 _45439)). Qed.
Lemma lem3910885 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = term519.
Proof. exact (TRANS (@lem3910661 _45438 _45439) (@lem3910884 _45438 _45439)). Qed.
Lemma lem3910886 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3910887 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = term199.
Proof. exact (TRANS (@lem3910885 _45438 _45439) (@lem3910886)). Qed.
Lemma lem3910888 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3910889 (_45438 : int) (_45439 : int) : (term520 _45438 _45439) = term521.
Proof. exact (MK_COMB (@lem3910888) (@lem3910887 _45438 _45439)). Qed.
Lemma lem3910890 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3910891 (_45438 : int) (_45439 : int) : (term494 _45438 _45439) = term522.
Proof. exact (MK_COMB (@lem3910889 _45438 _45439) (@lem3910890)). Qed.
Lemma lem3910892 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3910891 _45438 _45439) (@lem3910660 _45438 _45439 h1)). Qed.
Lemma lem3910894 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3910895 : term522 = term523.
Proof. exact (@lem3910894 term133 term199). Qed.
Lemma lem3910897 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3910898 : term199 = term200.
Proof. exact (@lem3910897 term11). Qed.
Lemma lem3910900 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910901 : term133 = term196.
Proof. exact (@lem3910900 (NUMERAL 0)). Qed.
Lemma lem3910902 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3910903 : term135 = term524.
Proof. exact (MK_COMB (@lem3910902) (@lem3910901)). Qed.
Lemma lem3910904 : term523 = term525.
Proof. exact (MK_COMB (@lem3910903) (@lem3910898)). Qed.
Lemma lem3910905 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3910907 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910908 : term251 = term252.
Proof. exact (@lem3910907 (NUMERAL 0) term11). Qed.
Lemma lem3910909 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910910 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910911 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910910 h1) (fun h1 : term252 = True => @lem3910909)). Qed.
Lemma lem3910912 : term252 = True.
Proof. exact (EQ_MP (@lem3910911) (@lem3910909)). Qed.
Lemma lem3910913 : term251 = True.
Proof. exact (TRANS (@lem3910908) (@lem3910912)). Qed.
Lemma lem3910914 : True = term251.
Proof. exact (SYM (@lem3910913)). Qed.
Lemma lem3910915 : term251.
Proof. exact (EQ_MP (@lem3910914) (@lem0)). Qed.
Lemma lem3910916 : term527.
Proof. exact (@lem3910905 (@lem3910915)). Qed.
Lemma lem3910918 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910919 : term251 = term252.
Proof. exact (@lem3910918 (NUMERAL 0) term11). Qed.
Lemma lem3910920 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910921 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910922 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910921 h1) (fun h1 : term252 = True => @lem3910920)). Qed.
Lemma lem3910923 : term252 = True.
Proof. exact (EQ_MP (@lem3910922) (@lem3910920)). Qed.
Lemma lem3910924 : term251 = True.
Proof. exact (TRANS (@lem3910919) (@lem3910923)). Qed.
Lemma lem3910925 : True = term251.
Proof. exact (SYM (@lem3910924)). Qed.
Lemma lem3910926 : term251.
Proof. exact (EQ_MP (@lem3910925) (@lem0)). Qed.
Lemma lem3910927 : term525 = term528.
Proof. exact (@lem3910916 (@lem3910926)). Qed.
Lemma lem3910929 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3910930 : term225 = term230.
Proof. exact (@lem3910929 term11 term11). Qed.
Lemma lem3910931 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3910932 : term211 = term11.
Proof. exact (EQ_MP (@lem3910931) (@lem940073)). Qed.
Lemma lem3910933 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3910934 : term209 = term143.
Proof. exact (MK_COMB (@lem3910933) (@lem3910932)). Qed.
Lemma lem3910935 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3910936 : term230 = term199.
Proof. exact (MK_COMB (@lem3910935) (@lem3910934)). Qed.
Lemma lem3910937 : term225 = term199.
Proof. exact (TRANS (@lem3910930) (@lem3910936)). Qed.
Lemma lem3910939 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3910940 : term263 = term133.
Proof. exact (@lem3910939 term11). Qed.
Lemma lem3910941 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3910942 : term529 = term135.
Proof. exact (MK_COMB (@lem3910941) (@lem3910940)). Qed.
Lemma lem3910943 : term528 = term523.
Proof. exact (MK_COMB (@lem3910942) (@lem3910937)). Qed.
Lemma lem3910945 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3910946 : term523 = term532.
Proof. exact (@lem3910945 (NUMERAL 0) term11). Qed.
Lemma lem3910947 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910948 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3910949 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910948 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3910947)). Qed.
Lemma lem3910950 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3910949) (@lem3910947)). Qed.
Lemma lem3910951 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3910952 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3910953 : term533 = (and True).
Proof. exact (MK_COMB (@lem3910952) (@lem3910951)). Qed.
Lemma lem3910954 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3910953) (@lem3910950)). Qed.
Lemma lem3910956 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3910957 : term532 = False.
Proof. exact (TRANS (@lem3910954) (@lem3910956)). Qed.
Lemma lem3910958 : term523 = False.
Proof. exact (TRANS (@lem3910946) (@lem3910957)). Qed.
Lemma lem3910959 : term528 = False.
Proof. exact (TRANS (@lem3910943) (@lem3910958)). Qed.
Lemma lem3910960 : term525 = False.
Proof. exact (TRANS (@lem3910927) (@lem3910959)). Qed.
Lemma lem3910961 : term523 = False.
Proof. exact (TRANS (@lem3910904) (@lem3910960)). Qed.
Lemma lem3910962 : term522 = False.
Proof. exact (TRANS (@lem3910895) (@lem3910961)). Qed.
Lemma lem3910963 (_45438 : int) (_45439 : int) (h1 : term470 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3910962) (@lem3910892 _45438 _45439 h1)). Qed.
Lemma lem3910964 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term534 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3910965 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term463 _45438 _45439.
Proof. exact (proj2 (@lem3910964 _45438 _45439 h1)). Qed.
Lemma lem3910967 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term414 _45438 _45439.
Proof. exact (proj2 (@lem3910965 _45438 _45439 h1)). Qed.
Lemma lem3910969 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term360 _45438 _45439.
Proof. exact (proj2 (@lem3910967 _45438 _45439 h1)). Qed.
Lemma lem3910970 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term272 _45439 _45438.
Proof. exact (proj1 (@lem3910967 _45438 _45439 h1)). Qed.
Lemma lem3910971 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : (real_of_int _45438) = term133.
Proof. exact (proj2 (@lem3910970 _45438 _45439 h1)). Qed.
Lemma lem3910973 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term286 _45438 _45439.
Proof. exact (proj2 (@lem3910969 _45438 _45439 h1)). Qed.
Lemma lem3910974 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term280 _45438 _45439.
Proof. exact (proj1 (@lem3910969 _45438 _45439 h1)). Qed.
Lemma lem3910976 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3910977 : term471 = term251.
Proof. exact (@lem3910976 term133 term143). Qed.
Lemma lem3910979 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910980 : term143 = term224.
Proof. exact (@lem3910979 term11). Qed.
Lemma lem3910982 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3910983 : term133 = term196.
Proof. exact (@lem3910982 (NUMERAL 0)). Qed.
Lemma lem3910984 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3910985 : term472 = term473.
Proof. exact (MK_COMB (@lem3910984) (@lem3910983)). Qed.
Lemma lem3910986 : term251 = term474.
Proof. exact (MK_COMB (@lem3910985) (@lem3910980)). Qed.
Lemma lem3910987 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3910989 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3910990 : term251 = term252.
Proof. exact (@lem3910989 (NUMERAL 0) term11). Qed.
Lemma lem3910991 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3910992 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3910993 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3910992 h1) (fun h1 : term252 = True => @lem3910991)). Qed.
Lemma lem3910994 : term252 = True.
Proof. exact (EQ_MP (@lem3910993) (@lem3910991)). Qed.
Lemma lem3910995 : term251 = True.
Proof. exact (TRANS (@lem3910990) (@lem3910994)). Qed.
Lemma lem3910996 : True = term251.
Proof. exact (SYM (@lem3910995)). Qed.
Lemma lem3910997 : term251.
Proof. exact (EQ_MP (@lem3910996) (@lem0)). Qed.
Lemma lem3910998 : term476.
Proof. exact (@lem3910987 (@lem3910997)). Qed.
Lemma lem3911000 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911001 : term251 = term252.
Proof. exact (@lem3911000 (NUMERAL 0) term11). Qed.
Lemma lem3911002 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911003 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911004 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911003 h1) (fun h1 : term252 = True => @lem3911002)). Qed.
Lemma lem3911005 : term252 = True.
Proof. exact (EQ_MP (@lem3911004) (@lem3911002)). Qed.
Lemma lem3911006 : term251 = True.
Proof. exact (TRANS (@lem3911001) (@lem3911005)). Qed.
Lemma lem3911007 : True = term251.
Proof. exact (SYM (@lem3911006)). Qed.
Lemma lem3911008 : term251.
Proof. exact (EQ_MP (@lem3911007) (@lem0)). Qed.
Lemma lem3911009 : term474 = term477.
Proof. exact (@lem3910998 (@lem3911008)). Qed.
Lemma lem3911011 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911012 : term208 = term209.
Proof. exact (@lem3911011 term11 term11). Qed.
Lemma lem3911013 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911014 : term211 = term11.
Proof. exact (EQ_MP (@lem3911013) (@lem940073)). Qed.
Lemma lem3911015 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911016 : term209 = term143.
Proof. exact (MK_COMB (@lem3911015) (@lem3911014)). Qed.
Lemma lem3911017 : term208 = term143.
Proof. exact (TRANS (@lem3911012) (@lem3911016)). Qed.
Lemma lem3911019 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911020 : term263 = term133.
Proof. exact (@lem3911019 term11). Qed.
Lemma lem3911021 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911022 : term478 = term472.
Proof. exact (MK_COMB (@lem3911021) (@lem3911020)). Qed.
Lemma lem3911023 : term477 = term251.
Proof. exact (MK_COMB (@lem3911022) (@lem3911017)). Qed.
Lemma lem3911025 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911026 : term251 = term252.
Proof. exact (@lem3911025 (NUMERAL 0) term11). Qed.
Lemma lem3911027 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911028 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911029 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911028 h1) (fun h1 : term252 = True => @lem3911027)). Qed.
Lemma lem3911030 : term252 = True.
Proof. exact (EQ_MP (@lem3911029) (@lem3911027)). Qed.
Lemma lem3911031 : term251 = True.
Proof. exact (TRANS (@lem3911026) (@lem3911030)). Qed.
Lemma lem3911032 : term477 = True.
Proof. exact (TRANS (@lem3911023) (@lem3911031)). Qed.
Lemma lem3911033 : term474 = True.
Proof. exact (TRANS (@lem3911009) (@lem3911032)). Qed.
Lemma lem3911034 : term251 = True.
Proof. exact (TRANS (@lem3910986) (@lem3911033)). Qed.
Lemma lem3911035 : term471 = True.
Proof. exact (TRANS (@lem3910977) (@lem3911034)). Qed.
Lemma lem3911036 : True = term471.
Proof. exact (SYM (@lem3911035)). Qed.
Lemma lem3911037 : term471.
Proof. exact (EQ_MP (@lem3911036) (@lem0)). Qed.
Lemma lem3911038 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term535 _45438 _45439.
Proof. exact (conj (@lem3911037) (@lem3910973 _45438 _45439 h1)). Qed.
Lemma lem3911040 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3911041 (_45438 : int) (_45439 : int) : term536 _45438 _45439.
Proof. exact (@lem3911040 term143 (term236 _45438 _45439)). Qed.
Lemma lem3911042 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term537 _45438 _45439.
Proof. exact (@lem3911041 _45438 _45439 (@lem3911038 _45438 _45439 h1)). Qed.
Lemma lem3911043 (_45438 : int) (_45439 : int) : (term489 _45438 _45439) = (term236 _45438 _45439).
Proof. exact (@lem1982733 (term236 _45438 _45439)). Qed.
Lemma lem3911044 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911045 (_45438 : int) (_45439 : int) : (term538 _45438 _45439) = (term285 _45438 _45439).
Proof. exact (MK_COMB (@lem3911044) (@lem3911043 _45438 _45439)). Qed.
Lemma lem3911046 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911047 (_45438 : int) (_45439 : int) : (term537 _45438 _45439) = (term286 _45438 _45439).
Proof. exact (MK_COMB (@lem3911045 _45438 _45439) (@lem3911046)). Qed.
Lemma lem3911048 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term286 _45438 _45439.
Proof. exact (EQ_MP (@lem3911047 _45438 _45439) (@lem3911042 _45438 _45439 h1)). Qed.
Lemma lem3911050 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3911051 (_45438 : int) : term539 _45438.
Proof. exact (@lem3911050 (real_of_int _45438)). Qed.
Lemma lem3911052 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term540 _45438.
Proof. exact (@lem3911051 _45438 (@lem3910971 _45438 _45439 h1)). Qed.
Lemma lem3911053 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term541 _45438.
Proof. exact (@lem3911052 _45438 _45439 h1 term143). Qed.
Lemma lem3911054 (_45438 : int) : (term541 _45438) = ((term542 _45438) = term133).
Proof. exact (eq_refl (term541 _45438)). Qed.
Lemma lem3911055 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : (term542 _45438) = term133.
Proof. exact (EQ_MP (@lem3911054 _45438) (@lem3911053 _45438 _45439 h1)). Qed.
Lemma lem3911056 (_45438 : int) : (term542 _45438) = (real_of_int _45438).
Proof. exact (@lem1982733 (real_of_int _45438)). Qed.
Lemma lem3911057 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3911058 (_45438 : int) : (term543 _45438) = (term146 _45438).
Proof. exact (MK_COMB (@lem3911057) (@lem3911056 _45438)). Qed.
Lemma lem3911059 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911060 (_45438 : int) : ((term542 _45438) = term133) = ((real_of_int _45438) = term133).
Proof. exact (MK_COMB (@lem3911058 _45438) (@lem3911059)). Qed.
Lemma lem3911061 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : (real_of_int _45438) = term133.
Proof. exact (EQ_MP (@lem3911060 _45438) (@lem3911055 _45438 _45439 h1)). Qed.
Lemma lem3911062 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term544 _45438 _45439.
Proof. exact (conj (@lem3911061 _45438 _45439 h1) (@lem3911048 _45438 _45439 h1)). Qed.
Lemma lem3911064 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3911065 (_45438 : int) (_45439 : int) : term545 _45438 _45439.
Proof. exact (@lem3911064 (real_of_int _45438) (term236 _45438 _45439)). Qed.
Lemma lem3911066 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term546 _45438 _45439.
Proof. exact (@lem3911065 _45438 _45439 (@lem3911062 _45438 _45439 h1)). Qed.
Lemma lem3911067 (_45438 : int) (_45439 : int) : (term547 _45438 _45439) = (term548 _45438 _45439).
Proof. exact (@lem1982763 (real_of_int _45438) (term237 _45438) (term299 _45439)). Qed.
Lemma lem3911068 (_45438 : int) : (term517 _45438) = (term498 _45438).
Proof. exact (@lem1982715 term199 (real_of_int _45438)). Qed.
Lemma lem3911070 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911071 : term143 = term224.
Proof. exact (@lem3911070 term11). Qed.
Lemma lem3911073 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3911074 : term199 = term200.
Proof. exact (@lem3911073 term11). Qed.
Lemma lem3911075 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911076 : term499 = term500.
Proof. exact (MK_COMB (@lem3911075) (@lem3911074)). Qed.
Lemma lem3911077 : term501 = term502.
Proof. exact (MK_COMB (@lem3911076) (@lem3911071)). Qed.
Lemma lem3911078 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3911080 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911081 : term251 = term252.
Proof. exact (@lem3911080 (NUMERAL 0) term11). Qed.
Lemma lem3911082 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911083 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911084 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911083 h1) (fun h1 : term252 = True => @lem3911082)). Qed.
Lemma lem3911085 : term252 = True.
Proof. exact (EQ_MP (@lem3911084) (@lem3911082)). Qed.
Lemma lem3911086 : term251 = True.
Proof. exact (TRANS (@lem3911081) (@lem3911085)). Qed.
Lemma lem3911087 : True = term251.
Proof. exact (SYM (@lem3911086)). Qed.
Lemma lem3911088 : term251.
Proof. exact (EQ_MP (@lem3911087) (@lem0)). Qed.
Lemma lem3911089 : term504.
Proof. exact (@lem3911078 (@lem3911088)). Qed.
Lemma lem3911091 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911092 : term251 = term252.
Proof. exact (@lem3911091 (NUMERAL 0) term11). Qed.
Lemma lem3911093 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911094 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911095 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911094 h1) (fun h1 : term252 = True => @lem3911093)). Qed.
Lemma lem3911096 : term252 = True.
Proof. exact (EQ_MP (@lem3911095) (@lem3911093)). Qed.
Lemma lem3911097 : term251 = True.
Proof. exact (TRANS (@lem3911092) (@lem3911096)). Qed.
Lemma lem3911098 : True = term251.
Proof. exact (SYM (@lem3911097)). Qed.
Lemma lem3911099 : term251.
Proof. exact (EQ_MP (@lem3911098) (@lem0)). Qed.
Lemma lem3911100 : term505.
Proof. exact (@lem3911089 (@lem3911099)). Qed.
Lemma lem3911102 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911103 : term251 = term252.
Proof. exact (@lem3911102 (NUMERAL 0) term11). Qed.
Lemma lem3911104 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911105 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911106 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911105 h1) (fun h1 : term252 = True => @lem3911104)). Qed.
Lemma lem3911107 : term252 = True.
Proof. exact (EQ_MP (@lem3911106) (@lem3911104)). Qed.
Lemma lem3911108 : term251 = True.
Proof. exact (TRANS (@lem3911103) (@lem3911107)). Qed.
Lemma lem3911109 : True = term251.
Proof. exact (SYM (@lem3911108)). Qed.
Lemma lem3911110 : term251.
Proof. exact (EQ_MP (@lem3911109) (@lem0)). Qed.
Lemma lem3911111 : term506.
Proof. exact (@lem3911100 (@lem3911110)). Qed.
Lemma lem3911113 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911114 : term208 = term209.
Proof. exact (@lem3911113 term11 term11). Qed.
Lemma lem3911115 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911116 : term211 = term11.
Proof. exact (EQ_MP (@lem3911115) (@lem940073)). Qed.
Lemma lem3911117 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911118 : term209 = term143.
Proof. exact (MK_COMB (@lem3911117) (@lem3911116)). Qed.
Lemma lem3911119 : term208 = term143.
Proof. exact (TRANS (@lem3911114) (@lem3911118)). Qed.
Lemma lem3911121 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3911122 : term225 = term230.
Proof. exact (@lem3911121 term11 term11). Qed.
Lemma lem3911123 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911124 : term211 = term11.
Proof. exact (EQ_MP (@lem3911123) (@lem940073)). Qed.
Lemma lem3911125 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911126 : term209 = term143.
Proof. exact (MK_COMB (@lem3911125) (@lem3911124)). Qed.
Lemma lem3911127 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3911128 : term230 = term199.
Proof. exact (MK_COMB (@lem3911127) (@lem3911126)). Qed.
Lemma lem3911129 : term225 = term199.
Proof. exact (TRANS (@lem3911122) (@lem3911128)). Qed.
Lemma lem3911130 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911131 : term507 = term499.
Proof. exact (MK_COMB (@lem3911130) (@lem3911129)). Qed.
Lemma lem3911132 : term508 = term501.
Proof. exact (MK_COMB (@lem3911131) (@lem3911119)). Qed.
Lemma lem3911134 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3911135 : term501 = term133.
Proof. exact (@lem3911134 term11). Qed.
Lemma lem3911136 : term508 = term133.
Proof. exact (TRANS (@lem3911132) (@lem3911135)). Qed.
Lemma lem3911137 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3911138 : term510 = term261.
Proof. exact (MK_COMB (@lem3911137) (@lem3911136)). Qed.
Lemma lem3911139 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3911140 : term511 = term263.
Proof. exact (MK_COMB (@lem3911138) (@lem3911139)). Qed.
Lemma lem3911142 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911143 : term263 = term133.
Proof. exact (@lem3911142 term11). Qed.
Lemma lem3911144 : term511 = term133.
Proof. exact (TRANS (@lem3911140) (@lem3911143)). Qed.
Lemma lem3911146 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911147 : term208 = term209.
Proof. exact (@lem3911146 term11 term11). Qed.
Lemma lem3911148 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911149 : term211 = term11.
Proof. exact (EQ_MP (@lem3911148) (@lem940073)). Qed.
Lemma lem3911150 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911151 : term209 = term143.
Proof. exact (MK_COMB (@lem3911150) (@lem3911149)). Qed.
Lemma lem3911152 : term208 = term143.
Proof. exact (TRANS (@lem3911147) (@lem3911151)). Qed.
Lemma lem3911153 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3911154 : term265 = term263.
Proof. exact (MK_COMB (@lem3911153) (@lem3911152)). Qed.
Lemma lem3911156 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911157 : term263 = term133.
Proof. exact (@lem3911156 term11). Qed.
Lemma lem3911158 : term265 = term133.
Proof. exact (TRANS (@lem3911154) (@lem3911157)). Qed.
Lemma lem3911159 : term133 = term265.
Proof. exact (SYM (@lem3911158)). Qed.
Lemma lem3911160 : term511 = term265.
Proof. exact (TRANS (@lem3911144) (@lem3911159)). Qed.
Lemma lem3911161 : term502 = term196.
Proof. exact (@lem3911111 (@lem3911160)). Qed.
Lemma lem3911162 : term501 = term196.
Proof. exact (TRANS (@lem3911077) (@lem3911161)). Qed.
Lemma lem3911164 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3911165 : term196 = term133.
Proof. exact (@lem3911164 term133). Qed.
Lemma lem3911166 : term501 = term133.
Proof. exact (TRANS (@lem3911162) (@lem3911165)). Qed.
Lemma lem3911167 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3911168 : term512 = term261.
Proof. exact (MK_COMB (@lem3911167) (@lem3911166)). Qed.
Lemma lem3911169 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3911170 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3911168) (@lem3911169 _45438)). Qed.
Lemma lem3911171 (_45438 : int) : (term517 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3911068 _45438) (@lem3911170 _45438)). Qed.
Lemma lem3911172 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3911173 (_45438 : int) : (term517 _45438) = term133.
Proof. exact (TRANS (@lem3911171 _45438) (@lem3911172 _45438)). Qed.
Lemma lem3911174 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911175 (_45438 : int) : (term518 _45438) = term175.
Proof. exact (MK_COMB (@lem3911174) (@lem3911173 _45438)). Qed.
Lemma lem3911176 (_45439 : int) : (term299 _45439) = (term299 _45439).
Proof. exact (eq_refl (term299 _45439)). Qed.
Lemma lem3911177 (_45438 : int) (_45439 : int) : (term548 _45438 _45439) = (term549 _45439).
Proof. exact (MK_COMB (@lem3911175 _45438) (@lem3911176 _45439)). Qed.
Lemma lem3911178 (_45438 : int) (_45439 : int) : (term547 _45438 _45439) = (term549 _45439).
Proof. exact (TRANS (@lem3911067 _45438 _45439) (@lem3911177 _45438 _45439)). Qed.
Lemma lem3911179 (_45439 : int) : (term549 _45439) = (term299 _45439).
Proof. exact (@lem1982721 (term299 _45439)). Qed.
Lemma lem3911180 (_45438 : int) (_45439 : int) : (term547 _45438 _45439) = (term299 _45439).
Proof. exact (TRANS (@lem3911178 _45438 _45439) (@lem3911179 _45439)). Qed.
Lemma lem3911181 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911182 (_45438 : int) (_45439 : int) : (term550 _45438 _45439) = (term301 _45439).
Proof. exact (MK_COMB (@lem3911181) (@lem3911180 _45438 _45439)). Qed.
Lemma lem3911183 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911184 (_45438 : int) (_45439 : int) : (term546 _45438 _45439) = (term302 _45439).
Proof. exact (MK_COMB (@lem3911182 _45438 _45439) (@lem3911183)). Qed.
Lemma lem3911185 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term302 _45439.
Proof. exact (EQ_MP (@lem3911184 _45438 _45439) (@lem3911066 _45438 _45439 h1)). Qed.
Lemma lem3911187 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3911188 : term471 = term251.
Proof. exact (@lem3911187 term133 term143). Qed.
Lemma lem3911190 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911191 : term143 = term224.
Proof. exact (@lem3911190 term11). Qed.
Lemma lem3911193 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911194 : term133 = term196.
Proof. exact (@lem3911193 (NUMERAL 0)). Qed.
Lemma lem3911195 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911196 : term472 = term473.
Proof. exact (MK_COMB (@lem3911195) (@lem3911194)). Qed.
Lemma lem3911197 : term251 = term474.
Proof. exact (MK_COMB (@lem3911196) (@lem3911191)). Qed.
Lemma lem3911198 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3911200 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911201 : term251 = term252.
Proof. exact (@lem3911200 (NUMERAL 0) term11). Qed.
Lemma lem3911202 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911203 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911204 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911203 h1) (fun h1 : term252 = True => @lem3911202)). Qed.
Lemma lem3911205 : term252 = True.
Proof. exact (EQ_MP (@lem3911204) (@lem3911202)). Qed.
Lemma lem3911206 : term251 = True.
Proof. exact (TRANS (@lem3911201) (@lem3911205)). Qed.
Lemma lem3911207 : True = term251.
Proof. exact (SYM (@lem3911206)). Qed.
Lemma lem3911208 : term251.
Proof. exact (EQ_MP (@lem3911207) (@lem0)). Qed.
Lemma lem3911209 : term476.
Proof. exact (@lem3911198 (@lem3911208)). Qed.
Lemma lem3911211 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911212 : term251 = term252.
Proof. exact (@lem3911211 (NUMERAL 0) term11). Qed.
Lemma lem3911213 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911214 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911215 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911214 h1) (fun h1 : term252 = True => @lem3911213)). Qed.
Lemma lem3911216 : term252 = True.
Proof. exact (EQ_MP (@lem3911215) (@lem3911213)). Qed.
Lemma lem3911217 : term251 = True.
Proof. exact (TRANS (@lem3911212) (@lem3911216)). Qed.
Lemma lem3911218 : True = term251.
Proof. exact (SYM (@lem3911217)). Qed.
Lemma lem3911219 : term251.
Proof. exact (EQ_MP (@lem3911218) (@lem0)). Qed.
Lemma lem3911220 : term474 = term477.
Proof. exact (@lem3911209 (@lem3911219)). Qed.
Lemma lem3911222 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911223 : term208 = term209.
Proof. exact (@lem3911222 term11 term11). Qed.
Lemma lem3911224 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911225 : term211 = term11.
Proof. exact (EQ_MP (@lem3911224) (@lem940073)). Qed.
Lemma lem3911226 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911227 : term209 = term143.
Proof. exact (MK_COMB (@lem3911226) (@lem3911225)). Qed.
Lemma lem3911228 : term208 = term143.
Proof. exact (TRANS (@lem3911223) (@lem3911227)). Qed.
Lemma lem3911230 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911231 : term263 = term133.
Proof. exact (@lem3911230 term11). Qed.
Lemma lem3911232 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911233 : term478 = term472.
Proof. exact (MK_COMB (@lem3911232) (@lem3911231)). Qed.
Lemma lem3911234 : term477 = term251.
Proof. exact (MK_COMB (@lem3911233) (@lem3911228)). Qed.
Lemma lem3911236 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911237 : term251 = term252.
Proof. exact (@lem3911236 (NUMERAL 0) term11). Qed.
Lemma lem3911238 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911239 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911240 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911239 h1) (fun h1 : term252 = True => @lem3911238)). Qed.
Lemma lem3911241 : term252 = True.
Proof. exact (EQ_MP (@lem3911240) (@lem3911238)). Qed.
Lemma lem3911242 : term251 = True.
Proof. exact (TRANS (@lem3911237) (@lem3911241)). Qed.
Lemma lem3911243 : term477 = True.
Proof. exact (TRANS (@lem3911234) (@lem3911242)). Qed.
Lemma lem3911244 : term474 = True.
Proof. exact (TRANS (@lem3911220) (@lem3911243)). Qed.
Lemma lem3911245 : term251 = True.
Proof. exact (TRANS (@lem3911197) (@lem3911244)). Qed.
Lemma lem3911246 : term471 = True.
Proof. exact (TRANS (@lem3911188) (@lem3911245)). Qed.
Lemma lem3911247 : True = term471.
Proof. exact (SYM (@lem3911246)). Qed.
Lemma lem3911248 : term471.
Proof. exact (EQ_MP (@lem3911247) (@lem0)). Qed.
Lemma lem3911249 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term551 _45439.
Proof. exact (conj (@lem3911248) (@lem3911185 _45438 _45439 h1)). Qed.
Lemma lem3911251 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3911252 (_45439 : int) : term552 _45439.
Proof. exact (@lem3911251 term143 (term299 _45439)). Qed.
Lemma lem3911253 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term553 _45439.
Proof. exact (@lem3911252 _45439 (@lem3911249 _45438 _45439 h1)). Qed.
Lemma lem3911254 (_45439 : int) : (term554 _45439) = (term299 _45439).
Proof. exact (@lem1982733 (term299 _45439)). Qed.
Lemma lem3911255 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911256 (_45439 : int) : (term555 _45439) = (term301 _45439).
Proof. exact (MK_COMB (@lem3911255) (@lem3911254 _45439)). Qed.
Lemma lem3911257 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911258 (_45439 : int) : (term553 _45439) = (term302 _45439).
Proof. exact (MK_COMB (@lem3911256 _45439) (@lem3911257)). Qed.
Lemma lem3911259 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term302 _45439.
Proof. exact (EQ_MP (@lem3911258 _45439) (@lem3911253 _45438 _45439 h1)). Qed.
Lemma lem3911261 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3911262 : term471 = term251.
Proof. exact (@lem3911261 term133 term143). Qed.
Lemma lem3911264 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911265 : term143 = term224.
Proof. exact (@lem3911264 term11). Qed.
Lemma lem3911267 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911268 : term133 = term196.
Proof. exact (@lem3911267 (NUMERAL 0)). Qed.
Lemma lem3911269 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911270 : term472 = term473.
Proof. exact (MK_COMB (@lem3911269) (@lem3911268)). Qed.
Lemma lem3911271 : term251 = term474.
Proof. exact (MK_COMB (@lem3911270) (@lem3911265)). Qed.
Lemma lem3911272 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3911274 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911275 : term251 = term252.
Proof. exact (@lem3911274 (NUMERAL 0) term11). Qed.
Lemma lem3911276 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911277 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911278 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911277 h1) (fun h1 : term252 = True => @lem3911276)). Qed.
Lemma lem3911279 : term252 = True.
Proof. exact (EQ_MP (@lem3911278) (@lem3911276)). Qed.
Lemma lem3911280 : term251 = True.
Proof. exact (TRANS (@lem3911275) (@lem3911279)). Qed.
Lemma lem3911281 : True = term251.
Proof. exact (SYM (@lem3911280)). Qed.
Lemma lem3911282 : term251.
Proof. exact (EQ_MP (@lem3911281) (@lem0)). Qed.
Lemma lem3911283 : term476.
Proof. exact (@lem3911272 (@lem3911282)). Qed.
Lemma lem3911285 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911286 : term251 = term252.
Proof. exact (@lem3911285 (NUMERAL 0) term11). Qed.
Lemma lem3911287 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911288 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911289 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911288 h1) (fun h1 : term252 = True => @lem3911287)). Qed.
Lemma lem3911290 : term252 = True.
Proof. exact (EQ_MP (@lem3911289) (@lem3911287)). Qed.
Lemma lem3911291 : term251 = True.
Proof. exact (TRANS (@lem3911286) (@lem3911290)). Qed.
Lemma lem3911292 : True = term251.
Proof. exact (SYM (@lem3911291)). Qed.
Lemma lem3911293 : term251.
Proof. exact (EQ_MP (@lem3911292) (@lem0)). Qed.
Lemma lem3911294 : term474 = term477.
Proof. exact (@lem3911283 (@lem3911293)). Qed.
Lemma lem3911296 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911297 : term208 = term209.
Proof. exact (@lem3911296 term11 term11). Qed.
Lemma lem3911298 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911299 : term211 = term11.
Proof. exact (EQ_MP (@lem3911298) (@lem940073)). Qed.
Lemma lem3911300 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911301 : term209 = term143.
Proof. exact (MK_COMB (@lem3911300) (@lem3911299)). Qed.
Lemma lem3911302 : term208 = term143.
Proof. exact (TRANS (@lem3911297) (@lem3911301)). Qed.
Lemma lem3911304 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911305 : term263 = term133.
Proof. exact (@lem3911304 term11). Qed.
Lemma lem3911306 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911307 : term478 = term472.
Proof. exact (MK_COMB (@lem3911306) (@lem3911305)). Qed.
Lemma lem3911308 : term477 = term251.
Proof. exact (MK_COMB (@lem3911307) (@lem3911302)). Qed.
Lemma lem3911310 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911311 : term251 = term252.
Proof. exact (@lem3911310 (NUMERAL 0) term11). Qed.
Lemma lem3911312 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911313 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911314 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911313 h1) (fun h1 : term252 = True => @lem3911312)). Qed.
Lemma lem3911315 : term252 = True.
Proof. exact (EQ_MP (@lem3911314) (@lem3911312)). Qed.
Lemma lem3911316 : term251 = True.
Proof. exact (TRANS (@lem3911311) (@lem3911315)). Qed.
Lemma lem3911317 : term477 = True.
Proof. exact (TRANS (@lem3911308) (@lem3911316)). Qed.
Lemma lem3911318 : term474 = True.
Proof. exact (TRANS (@lem3911294) (@lem3911317)). Qed.
Lemma lem3911319 : term251 = True.
Proof. exact (TRANS (@lem3911271) (@lem3911318)). Qed.
Lemma lem3911320 : term471 = True.
Proof. exact (TRANS (@lem3911262) (@lem3911319)). Qed.
Lemma lem3911321 : True = term471.
Proof. exact (SYM (@lem3911320)). Qed.
Lemma lem3911322 : term471.
Proof. exact (EQ_MP (@lem3911321) (@lem0)). Qed.
Lemma lem3911323 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term479 _45438 _45439.
Proof. exact (conj (@lem3911322) (@lem3910974 _45438 _45439 h1)). Qed.
Lemma lem3911325 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3911326 (_45438 : int) (_45439 : int) : term481 _45438 _45439.
Proof. exact (@lem3911325 term143 (term277 _45438 _45439)). Qed.
Lemma lem3911327 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term482 _45438 _45439.
Proof. exact (@lem3911326 _45438 _45439 (@lem3911323 _45438 _45439 h1)). Qed.
Lemma lem3911328 (_45438 : int) (_45439 : int) : (term483 _45438 _45439) = (term277 _45438 _45439).
Proof. exact (@lem1982733 (term277 _45438 _45439)). Qed.
Lemma lem3911329 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911330 (_45438 : int) (_45439 : int) : (term484 _45438 _45439) = (term279 _45438 _45439).
Proof. exact (MK_COMB (@lem3911329) (@lem3911328 _45438 _45439)). Qed.
Lemma lem3911331 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911332 (_45438 : int) (_45439 : int) : (term482 _45438 _45439) = (term280 _45438 _45439).
Proof. exact (MK_COMB (@lem3911330 _45438 _45439) (@lem3911331)). Qed.
Lemma lem3911333 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term280 _45438 _45439.
Proof. exact (EQ_MP (@lem3911332 _45438 _45439) (@lem3911327 _45438 _45439 h1)). Qed.
Lemma lem3911335 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3911336 (_45438 : int) : term539 _45438.
Proof. exact (@lem3911335 (real_of_int _45438)). Qed.
Lemma lem3911337 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term540 _45438.
Proof. exact (@lem3911336 _45438 (@lem3910971 _45438 _45439 h1)). Qed.
Lemma lem3911338 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term556 _45438.
Proof. exact (@lem3911337 _45438 _45439 h1 term199). Qed.
Lemma lem3911339 (_45438 : int) : (term556 _45438) = ((term237 _45438) = term133).
Proof. exact (eq_refl (term556 _45438)). Qed.
Lemma lem3911346 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : (term237 _45438) = term133.
Proof. exact (EQ_MP (@lem3911339 _45438) (@lem3911338 _45438 _45439 h1)). Qed.
Lemma lem3911347 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term557 _45438 _45439.
Proof. exact (conj (@lem3911346 _45438 _45439 h1) (@lem3911333 _45438 _45439 h1)). Qed.
Lemma lem3911349 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3911350 (_45438 : int) (_45439 : int) : term558 _45438 _45439.
Proof. exact (@lem3911349 (term237 _45438) (term277 _45438 _45439)). Qed.
Lemma lem3911351 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term559 _45438 _45439.
Proof. exact (@lem3911350 _45438 _45439 (@lem3911347 _45438 _45439 h1)). Qed.
Lemma lem3911352 (_45438 : int) (_45439 : int) : (term560 _45438 _45439) = (term561 _45438 _45439).
Proof. exact (@lem1982763 (term237 _45438) (real_of_int _45438) (term237 _45439)). Qed.
Lemma lem3911353 (_45438 : int) : (term497 _45438) = (term498 _45438).
Proof. exact (@lem1982713 term199 (real_of_int _45438)). Qed.
Lemma lem3911355 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911356 : term143 = term224.
Proof. exact (@lem3911355 term11). Qed.
Lemma lem3911358 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3911359 : term199 = term200.
Proof. exact (@lem3911358 term11). Qed.
Lemma lem3911360 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911361 : term499 = term500.
Proof. exact (MK_COMB (@lem3911360) (@lem3911359)). Qed.
Lemma lem3911362 : term501 = term502.
Proof. exact (MK_COMB (@lem3911361) (@lem3911356)). Qed.
Lemma lem3911363 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3911365 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911366 : term251 = term252.
Proof. exact (@lem3911365 (NUMERAL 0) term11). Qed.
Lemma lem3911367 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911368 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911369 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911368 h1) (fun h1 : term252 = True => @lem3911367)). Qed.
Lemma lem3911370 : term252 = True.
Proof. exact (EQ_MP (@lem3911369) (@lem3911367)). Qed.
Lemma lem3911371 : term251 = True.
Proof. exact (TRANS (@lem3911366) (@lem3911370)). Qed.
Lemma lem3911372 : True = term251.
Proof. exact (SYM (@lem3911371)). Qed.
Lemma lem3911373 : term251.
Proof. exact (EQ_MP (@lem3911372) (@lem0)). Qed.
Lemma lem3911374 : term504.
Proof. exact (@lem3911363 (@lem3911373)). Qed.
Lemma lem3911376 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911377 : term251 = term252.
Proof. exact (@lem3911376 (NUMERAL 0) term11). Qed.
Lemma lem3911378 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911379 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911380 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911379 h1) (fun h1 : term252 = True => @lem3911378)). Qed.
Lemma lem3911381 : term252 = True.
Proof. exact (EQ_MP (@lem3911380) (@lem3911378)). Qed.
Lemma lem3911382 : term251 = True.
Proof. exact (TRANS (@lem3911377) (@lem3911381)). Qed.
Lemma lem3911383 : True = term251.
Proof. exact (SYM (@lem3911382)). Qed.
Lemma lem3911384 : term251.
Proof. exact (EQ_MP (@lem3911383) (@lem0)). Qed.
Lemma lem3911385 : term505.
Proof. exact (@lem3911374 (@lem3911384)). Qed.
Lemma lem3911387 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911388 : term251 = term252.
Proof. exact (@lem3911387 (NUMERAL 0) term11). Qed.
Lemma lem3911389 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911390 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911391 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911390 h1) (fun h1 : term252 = True => @lem3911389)). Qed.
Lemma lem3911392 : term252 = True.
Proof. exact (EQ_MP (@lem3911391) (@lem3911389)). Qed.
Lemma lem3911393 : term251 = True.
Proof. exact (TRANS (@lem3911388) (@lem3911392)). Qed.
Lemma lem3911394 : True = term251.
Proof. exact (SYM (@lem3911393)). Qed.
Lemma lem3911395 : term251.
Proof. exact (EQ_MP (@lem3911394) (@lem0)). Qed.
Lemma lem3911396 : term506.
Proof. exact (@lem3911385 (@lem3911395)). Qed.
Lemma lem3911398 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911399 : term208 = term209.
Proof. exact (@lem3911398 term11 term11). Qed.
Lemma lem3911400 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911401 : term211 = term11.
Proof. exact (EQ_MP (@lem3911400) (@lem940073)). Qed.
Lemma lem3911402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911403 : term209 = term143.
Proof. exact (MK_COMB (@lem3911402) (@lem3911401)). Qed.
Lemma lem3911404 : term208 = term143.
Proof. exact (TRANS (@lem3911399) (@lem3911403)). Qed.
Lemma lem3911406 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3911407 : term225 = term230.
Proof. exact (@lem3911406 term11 term11). Qed.
Lemma lem3911408 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911409 : term211 = term11.
Proof. exact (EQ_MP (@lem3911408) (@lem940073)). Qed.
Lemma lem3911410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911411 : term209 = term143.
Proof. exact (MK_COMB (@lem3911410) (@lem3911409)). Qed.
Lemma lem3911412 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3911413 : term230 = term199.
Proof. exact (MK_COMB (@lem3911412) (@lem3911411)). Qed.
Lemma lem3911414 : term225 = term199.
Proof. exact (TRANS (@lem3911407) (@lem3911413)). Qed.
Lemma lem3911415 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911416 : term507 = term499.
Proof. exact (MK_COMB (@lem3911415) (@lem3911414)). Qed.
Lemma lem3911417 : term508 = term501.
Proof. exact (MK_COMB (@lem3911416) (@lem3911404)). Qed.
Lemma lem3911419 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3911420 : term501 = term133.
Proof. exact (@lem3911419 term11). Qed.
Lemma lem3911421 : term508 = term133.
Proof. exact (TRANS (@lem3911417) (@lem3911420)). Qed.
Lemma lem3911422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3911423 : term510 = term261.
Proof. exact (MK_COMB (@lem3911422) (@lem3911421)). Qed.
Lemma lem3911424 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3911425 : term511 = term263.
Proof. exact (MK_COMB (@lem3911423) (@lem3911424)). Qed.
Lemma lem3911427 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911428 : term263 = term133.
Proof. exact (@lem3911427 term11). Qed.
Lemma lem3911429 : term511 = term133.
Proof. exact (TRANS (@lem3911425) (@lem3911428)). Qed.
Lemma lem3911431 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911432 : term208 = term209.
Proof. exact (@lem3911431 term11 term11). Qed.
Lemma lem3911433 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911434 : term211 = term11.
Proof. exact (EQ_MP (@lem3911433) (@lem940073)). Qed.
Lemma lem3911435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911436 : term209 = term143.
Proof. exact (MK_COMB (@lem3911435) (@lem3911434)). Qed.
Lemma lem3911437 : term208 = term143.
Proof. exact (TRANS (@lem3911432) (@lem3911436)). Qed.
Lemma lem3911438 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3911439 : term265 = term263.
Proof. exact (MK_COMB (@lem3911438) (@lem3911437)). Qed.
Lemma lem3911441 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911442 : term263 = term133.
Proof. exact (@lem3911441 term11). Qed.
Lemma lem3911443 : term265 = term133.
Proof. exact (TRANS (@lem3911439) (@lem3911442)). Qed.
Lemma lem3911444 : term133 = term265.
Proof. exact (SYM (@lem3911443)). Qed.
Lemma lem3911445 : term511 = term265.
Proof. exact (TRANS (@lem3911429) (@lem3911444)). Qed.
Lemma lem3911446 : term502 = term196.
Proof. exact (@lem3911396 (@lem3911445)). Qed.
Lemma lem3911447 : term501 = term196.
Proof. exact (TRANS (@lem3911362) (@lem3911446)). Qed.
Lemma lem3911449 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3911450 : term196 = term133.
Proof. exact (@lem3911449 term133). Qed.
Lemma lem3911451 : term501 = term133.
Proof. exact (TRANS (@lem3911447) (@lem3911450)). Qed.
Lemma lem3911452 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3911453 : term512 = term261.
Proof. exact (MK_COMB (@lem3911452) (@lem3911451)). Qed.
Lemma lem3911454 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3911455 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3911453) (@lem3911454 _45438)). Qed.
Lemma lem3911456 (_45438 : int) : (term497 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3911353 _45438) (@lem3911455 _45438)). Qed.
Lemma lem3911457 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3911458 (_45438 : int) : (term497 _45438) = term133.
Proof. exact (TRANS (@lem3911456 _45438) (@lem3911457 _45438)). Qed.
Lemma lem3911459 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911460 (_45438 : int) : (term514 _45438) = term175.
Proof. exact (MK_COMB (@lem3911459) (@lem3911458 _45438)). Qed.
Lemma lem3911461 (_45439 : int) : (term237 _45439) = (term237 _45439).
Proof. exact (eq_refl (term237 _45439)). Qed.
Lemma lem3911462 (_45438 : int) (_45439 : int) : (term561 _45438 _45439) = (term562 _45439).
Proof. exact (MK_COMB (@lem3911460 _45438) (@lem3911461 _45439)). Qed.
Lemma lem3911463 (_45438 : int) (_45439 : int) : (term560 _45438 _45439) = (term562 _45439).
Proof. exact (TRANS (@lem3911352 _45438 _45439) (@lem3911462 _45438 _45439)). Qed.
Lemma lem3911464 (_45439 : int) : (term562 _45439) = (term237 _45439).
Proof. exact (@lem1982721 (term237 _45439)). Qed.
Lemma lem3911465 (_45438 : int) (_45439 : int) : (term560 _45438 _45439) = (term237 _45439).
Proof. exact (TRANS (@lem3911463 _45438 _45439) (@lem3911464 _45439)). Qed.
Lemma lem3911466 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911467 (_45438 : int) (_45439 : int) : (term563 _45438 _45439) = (term268 _45439).
Proof. exact (MK_COMB (@lem3911466) (@lem3911465 _45438 _45439)). Qed.
Lemma lem3911468 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911469 (_45438 : int) (_45439 : int) : (term559 _45438 _45439) = (term269 _45439).
Proof. exact (MK_COMB (@lem3911467 _45438 _45439) (@lem3911468)). Qed.
Lemma lem3911470 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term269 _45439.
Proof. exact (EQ_MP (@lem3911469 _45438 _45439) (@lem3911351 _45438 _45439 h1)). Qed.
Lemma lem3911472 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3911473 : term471 = term251.
Proof. exact (@lem3911472 term133 term143). Qed.
Lemma lem3911475 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911476 : term143 = term224.
Proof. exact (@lem3911475 term11). Qed.
Lemma lem3911478 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911479 : term133 = term196.
Proof. exact (@lem3911478 (NUMERAL 0)). Qed.
Lemma lem3911480 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911481 : term472 = term473.
Proof. exact (MK_COMB (@lem3911480) (@lem3911479)). Qed.
Lemma lem3911482 : term251 = term474.
Proof. exact (MK_COMB (@lem3911481) (@lem3911476)). Qed.
Lemma lem3911483 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3911485 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911486 : term251 = term252.
Proof. exact (@lem3911485 (NUMERAL 0) term11). Qed.
Lemma lem3911487 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911488 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911489 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911488 h1) (fun h1 : term252 = True => @lem3911487)). Qed.
Lemma lem3911490 : term252 = True.
Proof. exact (EQ_MP (@lem3911489) (@lem3911487)). Qed.
Lemma lem3911491 : term251 = True.
Proof. exact (TRANS (@lem3911486) (@lem3911490)). Qed.
Lemma lem3911492 : True = term251.
Proof. exact (SYM (@lem3911491)). Qed.
Lemma lem3911493 : term251.
Proof. exact (EQ_MP (@lem3911492) (@lem0)). Qed.
Lemma lem3911494 : term476.
Proof. exact (@lem3911483 (@lem3911493)). Qed.
Lemma lem3911496 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911497 : term251 = term252.
Proof. exact (@lem3911496 (NUMERAL 0) term11). Qed.
Lemma lem3911498 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911499 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911500 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911499 h1) (fun h1 : term252 = True => @lem3911498)). Qed.
Lemma lem3911501 : term252 = True.
Proof. exact (EQ_MP (@lem3911500) (@lem3911498)). Qed.
Lemma lem3911502 : term251 = True.
Proof. exact (TRANS (@lem3911497) (@lem3911501)). Qed.
Lemma lem3911503 : True = term251.
Proof. exact (SYM (@lem3911502)). Qed.
Lemma lem3911504 : term251.
Proof. exact (EQ_MP (@lem3911503) (@lem0)). Qed.
Lemma lem3911505 : term474 = term477.
Proof. exact (@lem3911494 (@lem3911504)). Qed.
Lemma lem3911507 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911508 : term208 = term209.
Proof. exact (@lem3911507 term11 term11). Qed.
Lemma lem3911509 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911510 : term211 = term11.
Proof. exact (EQ_MP (@lem3911509) (@lem940073)). Qed.
Lemma lem3911511 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911512 : term209 = term143.
Proof. exact (MK_COMB (@lem3911511) (@lem3911510)). Qed.
Lemma lem3911513 : term208 = term143.
Proof. exact (TRANS (@lem3911508) (@lem3911512)). Qed.
Lemma lem3911515 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911516 : term263 = term133.
Proof. exact (@lem3911515 term11). Qed.
Lemma lem3911517 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911518 : term478 = term472.
Proof. exact (MK_COMB (@lem3911517) (@lem3911516)). Qed.
Lemma lem3911519 : term477 = term251.
Proof. exact (MK_COMB (@lem3911518) (@lem3911513)). Qed.
Lemma lem3911521 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911522 : term251 = term252.
Proof. exact (@lem3911521 (NUMERAL 0) term11). Qed.
Lemma lem3911523 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911524 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911525 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911524 h1) (fun h1 : term252 = True => @lem3911523)). Qed.
Lemma lem3911526 : term252 = True.
Proof. exact (EQ_MP (@lem3911525) (@lem3911523)). Qed.
Lemma lem3911527 : term251 = True.
Proof. exact (TRANS (@lem3911522) (@lem3911526)). Qed.
Lemma lem3911528 : term477 = True.
Proof. exact (TRANS (@lem3911519) (@lem3911527)). Qed.
Lemma lem3911529 : term474 = True.
Proof. exact (TRANS (@lem3911505) (@lem3911528)). Qed.
Lemma lem3911530 : term251 = True.
Proof. exact (TRANS (@lem3911482) (@lem3911529)). Qed.
Lemma lem3911531 : term471 = True.
Proof. exact (TRANS (@lem3911473) (@lem3911530)). Qed.
Lemma lem3911532 : True = term471.
Proof. exact (SYM (@lem3911531)). Qed.
Lemma lem3911533 : term471.
Proof. exact (EQ_MP (@lem3911532) (@lem0)). Qed.
Lemma lem3911534 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term564 _45439.
Proof. exact (conj (@lem3911533) (@lem3911470 _45438 _45439 h1)). Qed.
Lemma lem3911536 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3911537 (_45439 : int) : term565 _45439.
Proof. exact (@lem3911536 term143 (term237 _45439)). Qed.
Lemma lem3911538 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term566 _45439.
Proof. exact (@lem3911537 _45439 (@lem3911534 _45438 _45439 h1)). Qed.
Lemma lem3911539 (_45439 : int) : (term567 _45439) = (term237 _45439).
Proof. exact (@lem1982733 (term237 _45439)). Qed.
Lemma lem3911540 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911541 (_45439 : int) : (term568 _45439) = (term268 _45439).
Proof. exact (MK_COMB (@lem3911540) (@lem3911539 _45439)). Qed.
Lemma lem3911542 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911543 (_45439 : int) : (term566 _45439) = (term269 _45439).
Proof. exact (MK_COMB (@lem3911541 _45439) (@lem3911542)). Qed.
Lemma lem3911544 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term269 _45439.
Proof. exact (EQ_MP (@lem3911543 _45439) (@lem3911538 _45438 _45439 h1)). Qed.
Lemma lem3911545 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term569 _45439.
Proof. exact (conj (@lem3911544 _45438 _45439 h1) (@lem3911259 _45438 _45439 h1)). Qed.
Lemma lem3911547 (x : real) (y : real) : term570 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3911548 (_45439 : int) : term571 _45439.
Proof. exact (@lem3911547 (term237 _45439) (term299 _45439)). Qed.
Lemma lem3911549 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term572 _45439.
Proof. exact (@lem3911548 _45439 (@lem3911545 _45438 _45439 h1)). Qed.
Lemma lem3911550 (_45439 : int) : (term573 _45439) = (term574 _45439).
Proof. exact (@lem1982763 (term237 _45439) (real_of_int _45439) term199). Qed.
Lemma lem3911551 (_45439 : int) : (term497 _45439) = (term498 _45439).
Proof. exact (@lem1982713 term199 (real_of_int _45439)). Qed.
Lemma lem3911553 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911554 : term143 = term224.
Proof. exact (@lem3911553 term11). Qed.
Lemma lem3911556 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3911557 : term199 = term200.
Proof. exact (@lem3911556 term11). Qed.
Lemma lem3911558 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911559 : term499 = term500.
Proof. exact (MK_COMB (@lem3911558) (@lem3911557)). Qed.
Lemma lem3911560 : term501 = term502.
Proof. exact (MK_COMB (@lem3911559) (@lem3911554)). Qed.
Lemma lem3911561 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3911563 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911564 : term251 = term252.
Proof. exact (@lem3911563 (NUMERAL 0) term11). Qed.
Lemma lem3911565 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911566 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911567 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911566 h1) (fun h1 : term252 = True => @lem3911565)). Qed.
Lemma lem3911568 : term252 = True.
Proof. exact (EQ_MP (@lem3911567) (@lem3911565)). Qed.
Lemma lem3911569 : term251 = True.
Proof. exact (TRANS (@lem3911564) (@lem3911568)). Qed.
Lemma lem3911570 : True = term251.
Proof. exact (SYM (@lem3911569)). Qed.
Lemma lem3911571 : term251.
Proof. exact (EQ_MP (@lem3911570) (@lem0)). Qed.
Lemma lem3911572 : term504.
Proof. exact (@lem3911561 (@lem3911571)). Qed.
Lemma lem3911574 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911575 : term251 = term252.
Proof. exact (@lem3911574 (NUMERAL 0) term11). Qed.
Lemma lem3911576 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911577 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911578 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911577 h1) (fun h1 : term252 = True => @lem3911576)). Qed.
Lemma lem3911579 : term252 = True.
Proof. exact (EQ_MP (@lem3911578) (@lem3911576)). Qed.
Lemma lem3911580 : term251 = True.
Proof. exact (TRANS (@lem3911575) (@lem3911579)). Qed.
Lemma lem3911581 : True = term251.
Proof. exact (SYM (@lem3911580)). Qed.
Lemma lem3911582 : term251.
Proof. exact (EQ_MP (@lem3911581) (@lem0)). Qed.
Lemma lem3911583 : term505.
Proof. exact (@lem3911572 (@lem3911582)). Qed.
Lemma lem3911585 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911586 : term251 = term252.
Proof. exact (@lem3911585 (NUMERAL 0) term11). Qed.
Lemma lem3911587 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911588 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911589 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911588 h1) (fun h1 : term252 = True => @lem3911587)). Qed.
Lemma lem3911590 : term252 = True.
Proof. exact (EQ_MP (@lem3911589) (@lem3911587)). Qed.
Lemma lem3911591 : term251 = True.
Proof. exact (TRANS (@lem3911586) (@lem3911590)). Qed.
Lemma lem3911592 : True = term251.
Proof. exact (SYM (@lem3911591)). Qed.
Lemma lem3911593 : term251.
Proof. exact (EQ_MP (@lem3911592) (@lem0)). Qed.
Lemma lem3911594 : term506.
Proof. exact (@lem3911583 (@lem3911593)). Qed.
Lemma lem3911596 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911597 : term208 = term209.
Proof. exact (@lem3911596 term11 term11). Qed.
Lemma lem3911598 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911599 : term211 = term11.
Proof. exact (EQ_MP (@lem3911598) (@lem940073)). Qed.
Lemma lem3911600 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911601 : term209 = term143.
Proof. exact (MK_COMB (@lem3911600) (@lem3911599)). Qed.
Lemma lem3911602 : term208 = term143.
Proof. exact (TRANS (@lem3911597) (@lem3911601)). Qed.
Lemma lem3911604 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3911605 : term225 = term230.
Proof. exact (@lem3911604 term11 term11). Qed.
Lemma lem3911606 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911607 : term211 = term11.
Proof. exact (EQ_MP (@lem3911606) (@lem940073)). Qed.
Lemma lem3911608 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911609 : term209 = term143.
Proof. exact (MK_COMB (@lem3911608) (@lem3911607)). Qed.
Lemma lem3911610 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3911611 : term230 = term199.
Proof. exact (MK_COMB (@lem3911610) (@lem3911609)). Qed.
Lemma lem3911612 : term225 = term199.
Proof. exact (TRANS (@lem3911605) (@lem3911611)). Qed.
Lemma lem3911613 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911614 : term507 = term499.
Proof. exact (MK_COMB (@lem3911613) (@lem3911612)). Qed.
Lemma lem3911615 : term508 = term501.
Proof. exact (MK_COMB (@lem3911614) (@lem3911602)). Qed.
Lemma lem3911617 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3911618 : term501 = term133.
Proof. exact (@lem3911617 term11). Qed.
Lemma lem3911619 : term508 = term133.
Proof. exact (TRANS (@lem3911615) (@lem3911618)). Qed.
Lemma lem3911620 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3911621 : term510 = term261.
Proof. exact (MK_COMB (@lem3911620) (@lem3911619)). Qed.
Lemma lem3911622 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3911623 : term511 = term263.
Proof. exact (MK_COMB (@lem3911621) (@lem3911622)). Qed.
Lemma lem3911625 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911626 : term263 = term133.
Proof. exact (@lem3911625 term11). Qed.
Lemma lem3911627 : term511 = term133.
Proof. exact (TRANS (@lem3911623) (@lem3911626)). Qed.
Lemma lem3911629 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911630 : term208 = term209.
Proof. exact (@lem3911629 term11 term11). Qed.
Lemma lem3911631 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911632 : term211 = term11.
Proof. exact (EQ_MP (@lem3911631) (@lem940073)). Qed.
Lemma lem3911633 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911634 : term209 = term143.
Proof. exact (MK_COMB (@lem3911633) (@lem3911632)). Qed.
Lemma lem3911635 : term208 = term143.
Proof. exact (TRANS (@lem3911630) (@lem3911634)). Qed.
Lemma lem3911636 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3911637 : term265 = term263.
Proof. exact (MK_COMB (@lem3911636) (@lem3911635)). Qed.
Lemma lem3911639 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911640 : term263 = term133.
Proof. exact (@lem3911639 term11). Qed.
Lemma lem3911641 : term265 = term133.
Proof. exact (TRANS (@lem3911637) (@lem3911640)). Qed.
Lemma lem3911642 : term133 = term265.
Proof. exact (SYM (@lem3911641)). Qed.
Lemma lem3911643 : term511 = term265.
Proof. exact (TRANS (@lem3911627) (@lem3911642)). Qed.
Lemma lem3911644 : term502 = term196.
Proof. exact (@lem3911594 (@lem3911643)). Qed.
Lemma lem3911645 : term501 = term196.
Proof. exact (TRANS (@lem3911560) (@lem3911644)). Qed.
Lemma lem3911647 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3911648 : term196 = term133.
Proof. exact (@lem3911647 term133). Qed.
Lemma lem3911649 : term501 = term133.
Proof. exact (TRANS (@lem3911645) (@lem3911648)). Qed.
Lemma lem3911650 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3911651 : term512 = term261.
Proof. exact (MK_COMB (@lem3911650) (@lem3911649)). Qed.
Lemma lem3911652 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3911653 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3911651) (@lem3911652 _45439)). Qed.
Lemma lem3911654 (_45439 : int) : (term497 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3911551 _45439) (@lem3911653 _45439)). Qed.
Lemma lem3911655 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3911656 (_45439 : int) : (term497 _45439) = term133.
Proof. exact (TRANS (@lem3911654 _45439) (@lem3911655 _45439)). Qed.
Lemma lem3911657 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911658 (_45439 : int) : (term514 _45439) = term175.
Proof. exact (MK_COMB (@lem3911657) (@lem3911656 _45439)). Qed.
Lemma lem3911659 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3911660 (_45439 : int) : (term574 _45439) = term519.
Proof. exact (MK_COMB (@lem3911658 _45439) (@lem3911659)). Qed.
Lemma lem3911661 (_45439 : int) : (term573 _45439) = term519.
Proof. exact (TRANS (@lem3911550 _45439) (@lem3911660 _45439)). Qed.
Lemma lem3911662 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3911663 (_45439 : int) : (term573 _45439) = term199.
Proof. exact (TRANS (@lem3911661 _45439) (@lem3911662)). Qed.
Lemma lem3911664 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911665 (_45439 : int) : (term575 _45439) = term521.
Proof. exact (MK_COMB (@lem3911664) (@lem3911663 _45439)). Qed.
Lemma lem3911666 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911667 (_45439 : int) : (term572 _45439) = term522.
Proof. exact (MK_COMB (@lem3911665 _45439) (@lem3911666)). Qed.
Lemma lem3911668 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3911667 _45439) (@lem3911549 _45438 _45439 h1)). Qed.
Lemma lem3911670 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3911671 : term522 = term523.
Proof. exact (@lem3911670 term133 term199). Qed.
Lemma lem3911673 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3911674 : term199 = term200.
Proof. exact (@lem3911673 term11). Qed.
Lemma lem3911676 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911677 : term133 = term196.
Proof. exact (@lem3911676 (NUMERAL 0)). Qed.
Lemma lem3911678 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3911679 : term135 = term524.
Proof. exact (MK_COMB (@lem3911678) (@lem3911677)). Qed.
Lemma lem3911680 : term523 = term525.
Proof. exact (MK_COMB (@lem3911679) (@lem3911674)). Qed.
Lemma lem3911681 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3911683 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911684 : term251 = term252.
Proof. exact (@lem3911683 (NUMERAL 0) term11). Qed.
Lemma lem3911685 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911686 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911687 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911686 h1) (fun h1 : term252 = True => @lem3911685)). Qed.
Lemma lem3911688 : term252 = True.
Proof. exact (EQ_MP (@lem3911687) (@lem3911685)). Qed.
Lemma lem3911689 : term251 = True.
Proof. exact (TRANS (@lem3911684) (@lem3911688)). Qed.
Lemma lem3911690 : True = term251.
Proof. exact (SYM (@lem3911689)). Qed.
Lemma lem3911691 : term251.
Proof. exact (EQ_MP (@lem3911690) (@lem0)). Qed.
Lemma lem3911692 : term527.
Proof. exact (@lem3911681 (@lem3911691)). Qed.
Lemma lem3911694 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911695 : term251 = term252.
Proof. exact (@lem3911694 (NUMERAL 0) term11). Qed.
Lemma lem3911696 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911697 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911698 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911697 h1) (fun h1 : term252 = True => @lem3911696)). Qed.
Lemma lem3911699 : term252 = True.
Proof. exact (EQ_MP (@lem3911698) (@lem3911696)). Qed.
Lemma lem3911700 : term251 = True.
Proof. exact (TRANS (@lem3911695) (@lem3911699)). Qed.
Lemma lem3911701 : True = term251.
Proof. exact (SYM (@lem3911700)). Qed.
Lemma lem3911702 : term251.
Proof. exact (EQ_MP (@lem3911701) (@lem0)). Qed.
Lemma lem3911703 : term525 = term528.
Proof. exact (@lem3911692 (@lem3911702)). Qed.
Lemma lem3911705 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3911706 : term225 = term230.
Proof. exact (@lem3911705 term11 term11). Qed.
Lemma lem3911707 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911708 : term211 = term11.
Proof. exact (EQ_MP (@lem3911707) (@lem940073)). Qed.
Lemma lem3911709 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911710 : term209 = term143.
Proof. exact (MK_COMB (@lem3911709) (@lem3911708)). Qed.
Lemma lem3911711 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3911712 : term230 = term199.
Proof. exact (MK_COMB (@lem3911711) (@lem3911710)). Qed.
Lemma lem3911713 : term225 = term199.
Proof. exact (TRANS (@lem3911706) (@lem3911712)). Qed.
Lemma lem3911715 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911716 : term263 = term133.
Proof. exact (@lem3911715 term11). Qed.
Lemma lem3911717 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3911718 : term529 = term135.
Proof. exact (MK_COMB (@lem3911717) (@lem3911716)). Qed.
Lemma lem3911719 : term528 = term523.
Proof. exact (MK_COMB (@lem3911718) (@lem3911713)). Qed.
Lemma lem3911721 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3911722 : term523 = term532.
Proof. exact (@lem3911721 (NUMERAL 0) term11). Qed.
Lemma lem3911723 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911724 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3911725 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911724 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3911723)). Qed.
Lemma lem3911726 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3911725) (@lem3911723)). Qed.
Lemma lem3911727 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3911728 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3911729 : term533 = (and True).
Proof. exact (MK_COMB (@lem3911728) (@lem3911727)). Qed.
Lemma lem3911730 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3911729) (@lem3911726)). Qed.
Lemma lem3911732 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3911733 : term532 = False.
Proof. exact (TRANS (@lem3911730) (@lem3911732)). Qed.
Lemma lem3911734 : term523 = False.
Proof. exact (TRANS (@lem3911722) (@lem3911733)). Qed.
Lemma lem3911735 : term528 = False.
Proof. exact (TRANS (@lem3911719) (@lem3911734)). Qed.
Lemma lem3911736 : term525 = False.
Proof. exact (TRANS (@lem3911703) (@lem3911735)). Qed.
Lemma lem3911737 : term523 = False.
Proof. exact (TRANS (@lem3911680) (@lem3911736)). Qed.
Lemma lem3911738 : term522 = False.
Proof. exact (TRANS (@lem3911671) (@lem3911737)). Qed.
Lemma lem3911739 (_45438 : int) (_45439 : int) (h1 : term534 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3911738) (@lem3911668 _45438 _45439 h1)). Qed.
Lemma lem3911740 (_45438 : int) (_45439 : int) (h1 : term461 _45438 _45439) : False.
Proof. exact (or_elim (@lem3910559 _45438 _45439 h1) (fun h0 : term470 _45438 _45439 => @lem3910963 _45438 _45439 h0) (fun h0 : term534 _45438 _45439 => @lem3911739 _45438 _45439 h0)). Qed.
Lemma lem3911741 (_45438 : int) (_45439 : int) (h1 : term457 _45438 _45439) : term457 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3911742 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term576 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3911743 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term458 _45438 _45439.
Proof. exact (proj2 (@lem3911742 _45438 _45439 h1)). Qed.
Lemma lem3911744 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term219 _45438.
Proof. exact (proj1 (@lem3911742 _45438 _45439 h1)). Qed.
Lemma lem3911745 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term409 _45438 _45439.
Proof. exact (proj2 (@lem3911743 _45438 _45439 h1)). Qed.
Lemma lem3911747 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term361 _45438 _45439.
Proof. exact (proj2 (@lem3911745 _45438 _45439 h1)). Qed.
Lemma lem3911748 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (proj1 (@lem3911745 _45438 _45439 h1)). Qed.
Lemma lem3911750 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (proj1 (@lem3911747 _45438 _45439 h1)). Qed.
Lemma lem3911752 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3911753 : term471 = term251.
Proof. exact (@lem3911752 term133 term143). Qed.
Lemma lem3911755 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911756 : term143 = term224.
Proof. exact (@lem3911755 term11). Qed.
Lemma lem3911758 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911759 : term133 = term196.
Proof. exact (@lem3911758 (NUMERAL 0)). Qed.
Lemma lem3911760 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911761 : term472 = term473.
Proof. exact (MK_COMB (@lem3911760) (@lem3911759)). Qed.
Lemma lem3911762 : term251 = term474.
Proof. exact (MK_COMB (@lem3911761) (@lem3911756)). Qed.
Lemma lem3911763 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3911765 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911766 : term251 = term252.
Proof. exact (@lem3911765 (NUMERAL 0) term11). Qed.
Lemma lem3911767 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911768 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911769 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911768 h1) (fun h1 : term252 = True => @lem3911767)). Qed.
Lemma lem3911770 : term252 = True.
Proof. exact (EQ_MP (@lem3911769) (@lem3911767)). Qed.
Lemma lem3911771 : term251 = True.
Proof. exact (TRANS (@lem3911766) (@lem3911770)). Qed.
Lemma lem3911772 : True = term251.
Proof. exact (SYM (@lem3911771)). Qed.
Lemma lem3911773 : term251.
Proof. exact (EQ_MP (@lem3911772) (@lem0)). Qed.
Lemma lem3911774 : term476.
Proof. exact (@lem3911763 (@lem3911773)). Qed.
Lemma lem3911776 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911777 : term251 = term252.
Proof. exact (@lem3911776 (NUMERAL 0) term11). Qed.
Lemma lem3911778 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911779 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911780 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911779 h1) (fun h1 : term252 = True => @lem3911778)). Qed.
Lemma lem3911781 : term252 = True.
Proof. exact (EQ_MP (@lem3911780) (@lem3911778)). Qed.
Lemma lem3911782 : term251 = True.
Proof. exact (TRANS (@lem3911777) (@lem3911781)). Qed.
Lemma lem3911783 : True = term251.
Proof. exact (SYM (@lem3911782)). Qed.
Lemma lem3911784 : term251.
Proof. exact (EQ_MP (@lem3911783) (@lem0)). Qed.
Lemma lem3911785 : term474 = term477.
Proof. exact (@lem3911774 (@lem3911784)). Qed.
Lemma lem3911787 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911788 : term208 = term209.
Proof. exact (@lem3911787 term11 term11). Qed.
Lemma lem3911789 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911790 : term211 = term11.
Proof. exact (EQ_MP (@lem3911789) (@lem940073)). Qed.
Lemma lem3911791 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911792 : term209 = term143.
Proof. exact (MK_COMB (@lem3911791) (@lem3911790)). Qed.
Lemma lem3911793 : term208 = term143.
Proof. exact (TRANS (@lem3911788) (@lem3911792)). Qed.
Lemma lem3911795 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911796 : term263 = term133.
Proof. exact (@lem3911795 term11). Qed.
Lemma lem3911797 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911798 : term478 = term472.
Proof. exact (MK_COMB (@lem3911797) (@lem3911796)). Qed.
Lemma lem3911799 : term477 = term251.
Proof. exact (MK_COMB (@lem3911798) (@lem3911793)). Qed.
Lemma lem3911801 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911802 : term251 = term252.
Proof. exact (@lem3911801 (NUMERAL 0) term11). Qed.
Lemma lem3911803 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911804 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911805 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911804 h1) (fun h1 : term252 = True => @lem3911803)). Qed.
Lemma lem3911806 : term252 = True.
Proof. exact (EQ_MP (@lem3911805) (@lem3911803)). Qed.
Lemma lem3911807 : term251 = True.
Proof. exact (TRANS (@lem3911802) (@lem3911806)). Qed.
Lemma lem3911808 : term477 = True.
Proof. exact (TRANS (@lem3911799) (@lem3911807)). Qed.
Lemma lem3911809 : term474 = True.
Proof. exact (TRANS (@lem3911785) (@lem3911808)). Qed.
Lemma lem3911810 : term251 = True.
Proof. exact (TRANS (@lem3911762) (@lem3911809)). Qed.
Lemma lem3911811 : term471 = True.
Proof. exact (TRANS (@lem3911753) (@lem3911810)). Qed.
Lemma lem3911812 : True = term471.
Proof. exact (SYM (@lem3911811)). Qed.
Lemma lem3911813 : term471.
Proof. exact (EQ_MP (@lem3911812) (@lem0)). Qed.
Lemma lem3911814 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term577 _45438.
Proof. exact (conj (@lem3911813) (@lem3911744 _45438 _45439 h1)). Qed.
Lemma lem3911816 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3911817 (_45438 : int) : term578 _45438.
Proof. exact (@lem3911816 term143 (real_of_int _45438)). Qed.
Lemma lem3911818 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term579 _45438.
Proof. exact (@lem3911817 _45438 (@lem3911814 _45438 _45439 h1)). Qed.
Lemma lem3911819 (_45438 : int) : (term542 _45438) = (real_of_int _45438).
Proof. exact (@lem1982733 (real_of_int _45438)). Qed.
Lemma lem3911820 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3911821 (_45438 : int) : (term580 _45438) = (term218 _45438).
Proof. exact (MK_COMB (@lem3911820) (@lem3911819 _45438)). Qed.
Lemma lem3911822 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911823 (_45438 : int) : (term579 _45438) = (term219 _45438).
Proof. exact (MK_COMB (@lem3911821 _45438) (@lem3911822)). Qed.
Lemma lem3911824 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term219 _45438.
Proof. exact (EQ_MP (@lem3911823 _45438) (@lem3911818 _45438 _45439 h1)). Qed.
Lemma lem3911826 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3911827 : term471 = term251.
Proof. exact (@lem3911826 term133 term143). Qed.
Lemma lem3911829 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911830 : term143 = term224.
Proof. exact (@lem3911829 term11). Qed.
Lemma lem3911832 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911833 : term133 = term196.
Proof. exact (@lem3911832 (NUMERAL 0)). Qed.
Lemma lem3911834 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911835 : term472 = term473.
Proof. exact (MK_COMB (@lem3911834) (@lem3911833)). Qed.
Lemma lem3911836 : term251 = term474.
Proof. exact (MK_COMB (@lem3911835) (@lem3911830)). Qed.
Lemma lem3911837 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3911839 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911840 : term251 = term252.
Proof. exact (@lem3911839 (NUMERAL 0) term11). Qed.
Lemma lem3911841 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911842 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911843 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911842 h1) (fun h1 : term252 = True => @lem3911841)). Qed.
Lemma lem3911844 : term252 = True.
Proof. exact (EQ_MP (@lem3911843) (@lem3911841)). Qed.
Lemma lem3911845 : term251 = True.
Proof. exact (TRANS (@lem3911840) (@lem3911844)). Qed.
Lemma lem3911846 : True = term251.
Proof. exact (SYM (@lem3911845)). Qed.
Lemma lem3911847 : term251.
Proof. exact (EQ_MP (@lem3911846) (@lem0)). Qed.
Lemma lem3911848 : term476.
Proof. exact (@lem3911837 (@lem3911847)). Qed.
Lemma lem3911850 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911851 : term251 = term252.
Proof. exact (@lem3911850 (NUMERAL 0) term11). Qed.
Lemma lem3911852 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911853 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911854 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911853 h1) (fun h1 : term252 = True => @lem3911852)). Qed.
Lemma lem3911855 : term252 = True.
Proof. exact (EQ_MP (@lem3911854) (@lem3911852)). Qed.
Lemma lem3911856 : term251 = True.
Proof. exact (TRANS (@lem3911851) (@lem3911855)). Qed.
Lemma lem3911857 : True = term251.
Proof. exact (SYM (@lem3911856)). Qed.
Lemma lem3911858 : term251.
Proof. exact (EQ_MP (@lem3911857) (@lem0)). Qed.
Lemma lem3911859 : term474 = term477.
Proof. exact (@lem3911848 (@lem3911858)). Qed.
Lemma lem3911861 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911862 : term208 = term209.
Proof. exact (@lem3911861 term11 term11). Qed.
Lemma lem3911863 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911864 : term211 = term11.
Proof. exact (EQ_MP (@lem3911863) (@lem940073)). Qed.
Lemma lem3911865 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911866 : term209 = term143.
Proof. exact (MK_COMB (@lem3911865) (@lem3911864)). Qed.
Lemma lem3911867 : term208 = term143.
Proof. exact (TRANS (@lem3911862) (@lem3911866)). Qed.
Lemma lem3911869 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911870 : term263 = term133.
Proof. exact (@lem3911869 term11). Qed.
Lemma lem3911871 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3911872 : term478 = term472.
Proof. exact (MK_COMB (@lem3911871) (@lem3911870)). Qed.
Lemma lem3911873 : term477 = term251.
Proof. exact (MK_COMB (@lem3911872) (@lem3911867)). Qed.
Lemma lem3911875 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911876 : term251 = term252.
Proof. exact (@lem3911875 (NUMERAL 0) term11). Qed.
Lemma lem3911877 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911878 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911879 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911878 h1) (fun h1 : term252 = True => @lem3911877)). Qed.
Lemma lem3911880 : term252 = True.
Proof. exact (EQ_MP (@lem3911879) (@lem3911877)). Qed.
Lemma lem3911881 : term251 = True.
Proof. exact (TRANS (@lem3911876) (@lem3911880)). Qed.
Lemma lem3911882 : term477 = True.
Proof. exact (TRANS (@lem3911873) (@lem3911881)). Qed.
Lemma lem3911883 : term474 = True.
Proof. exact (TRANS (@lem3911859) (@lem3911882)). Qed.
Lemma lem3911884 : term251 = True.
Proof. exact (TRANS (@lem3911836) (@lem3911883)). Qed.
Lemma lem3911885 : term471 = True.
Proof. exact (TRANS (@lem3911827) (@lem3911884)). Qed.
Lemma lem3911886 : True = term471.
Proof. exact (SYM (@lem3911885)). Qed.
Lemma lem3911887 : term471.
Proof. exact (EQ_MP (@lem3911886) (@lem0)). Qed.
Lemma lem3911888 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term581 _45438 _45439.
Proof. exact (conj (@lem3911887) (@lem3911748 _45438 _45439 h1)). Qed.
Lemma lem3911890 (x : real) (y : real) : term582 x y.
Proof. exact (proj1 (@lem1988330 x y)). Qed.
Lemma lem3911891 (_45438 : int) (_45439 : int) : term583 _45438 _45439.
Proof. exact (@lem3911890 term143 (term236 _45438 _45439)). Qed.
Lemma lem3911892 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term489 _45438 _45439) = term133.
Proof. exact (@lem3911891 _45438 _45439 (@lem3911888 _45438 _45439 h1)). Qed.
Lemma lem3911893 (_45438 : int) (_45439 : int) : (term489 _45438 _45439) = (term236 _45438 _45439).
Proof. exact (@lem1982733 (term236 _45438 _45439)). Qed.
Lemma lem3911894 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3911895 (_45438 : int) (_45439 : int) : (term490 _45438 _45439) = (term239 _45438 _45439).
Proof. exact (MK_COMB (@lem3911894) (@lem3911893 _45438 _45439)). Qed.
Lemma lem3911896 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3911897 (_45438 : int) (_45439 : int) : ((term489 _45438 _45439) = term133) = ((term236 _45438 _45439) = term133).
Proof. exact (MK_COMB (@lem3911895 _45438 _45439) (@lem3911896)). Qed.
Lemma lem3911898 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (EQ_MP (@lem3911897 _45438 _45439) (@lem3911892 _45438 _45439 h1)). Qed.
Lemma lem3911900 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3911901 (_45439 : int) : term539 _45439.
Proof. exact (@lem3911900 (real_of_int _45439)). Qed.
Lemma lem3911902 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term540 _45439.
Proof. exact (@lem3911901 _45439 (@lem3911750 _45438 _45439 h1)). Qed.
Lemma lem3911903 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term556 _45439.
Proof. exact (@lem3911902 _45438 _45439 h1 term199). Qed.
Lemma lem3911904 (_45439 : int) : (term556 _45439) = ((term237 _45439) = term133).
Proof. exact (eq_refl (term556 _45439)). Qed.
Lemma lem3911911 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term237 _45439) = term133.
Proof. exact (EQ_MP (@lem3911904 _45439) (@lem3911903 _45438 _45439 h1)). Qed.
Lemma lem3911912 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term584 _45438 _45439.
Proof. exact (conj (@lem3911911 _45438 _45439 h1) (@lem3911898 _45438 _45439 h1)). Qed.
Lemma lem3911914 (x : real) (y : real) : term585 x y.
Proof. exact (proj1 (@lem1393126 x y)). Qed.
Lemma lem3911915 (_45438 : int) (_45439 : int) : term586 _45438 _45439.
Proof. exact (@lem3911914 (term237 _45439) (term236 _45438 _45439)). Qed.
Lemma lem3911916 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term587 _45438 _45439) = term133.
Proof. exact (@lem3911915 _45438 _45439 (@lem3911912 _45438 _45439 h1)). Qed.
Lemma lem3911917 (_45438 : int) (_45439 : int) : (term587 _45438 _45439) = (term588 _45438 _45439).
Proof. exact (@lem1982757 (term237 _45438) (term237 _45439) (term299 _45439)). Qed.
Lemma lem3911918 (_45439 : int) : (term573 _45439) = (term574 _45439).
Proof. exact (@lem1982763 (term237 _45439) (real_of_int _45439) term199). Qed.
Lemma lem3911919 (_45439 : int) : (term497 _45439) = (term498 _45439).
Proof. exact (@lem1982713 term199 (real_of_int _45439)). Qed.
Lemma lem3911921 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3911922 : term143 = term224.
Proof. exact (@lem3911921 term11). Qed.
Lemma lem3911924 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3911925 : term199 = term200.
Proof. exact (@lem3911924 term11). Qed.
Lemma lem3911926 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911927 : term499 = term500.
Proof. exact (MK_COMB (@lem3911926) (@lem3911925)). Qed.
Lemma lem3911928 : term501 = term502.
Proof. exact (MK_COMB (@lem3911927) (@lem3911922)). Qed.
Lemma lem3911929 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3911931 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911932 : term251 = term252.
Proof. exact (@lem3911931 (NUMERAL 0) term11). Qed.
Lemma lem3911933 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911934 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911935 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911934 h1) (fun h1 : term252 = True => @lem3911933)). Qed.
Lemma lem3911936 : term252 = True.
Proof. exact (EQ_MP (@lem3911935) (@lem3911933)). Qed.
Lemma lem3911937 : term251 = True.
Proof. exact (TRANS (@lem3911932) (@lem3911936)). Qed.
Lemma lem3911938 : True = term251.
Proof. exact (SYM (@lem3911937)). Qed.
Lemma lem3911939 : term251.
Proof. exact (EQ_MP (@lem3911938) (@lem0)). Qed.
Lemma lem3911940 : term504.
Proof. exact (@lem3911929 (@lem3911939)). Qed.
Lemma lem3911942 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911943 : term251 = term252.
Proof. exact (@lem3911942 (NUMERAL 0) term11). Qed.
Lemma lem3911944 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911945 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911946 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911945 h1) (fun h1 : term252 = True => @lem3911944)). Qed.
Lemma lem3911947 : term252 = True.
Proof. exact (EQ_MP (@lem3911946) (@lem3911944)). Qed.
Lemma lem3911948 : term251 = True.
Proof. exact (TRANS (@lem3911943) (@lem3911947)). Qed.
Lemma lem3911949 : True = term251.
Proof. exact (SYM (@lem3911948)). Qed.
Lemma lem3911950 : term251.
Proof. exact (EQ_MP (@lem3911949) (@lem0)). Qed.
Lemma lem3911951 : term505.
Proof. exact (@lem3911940 (@lem3911950)). Qed.
Lemma lem3911953 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3911954 : term251 = term252.
Proof. exact (@lem3911953 (NUMERAL 0) term11). Qed.
Lemma lem3911955 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3911956 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3911957 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3911956 h1) (fun h1 : term252 = True => @lem3911955)). Qed.
Lemma lem3911958 : term252 = True.
Proof. exact (EQ_MP (@lem3911957) (@lem3911955)). Qed.
Lemma lem3911959 : term251 = True.
Proof. exact (TRANS (@lem3911954) (@lem3911958)). Qed.
Lemma lem3911960 : True = term251.
Proof. exact (SYM (@lem3911959)). Qed.
Lemma lem3911961 : term251.
Proof. exact (EQ_MP (@lem3911960) (@lem0)). Qed.
Lemma lem3911962 : term506.
Proof. exact (@lem3911951 (@lem3911961)). Qed.
Lemma lem3911964 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911965 : term208 = term209.
Proof. exact (@lem3911964 term11 term11). Qed.
Lemma lem3911966 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911967 : term211 = term11.
Proof. exact (EQ_MP (@lem3911966) (@lem940073)). Qed.
Lemma lem3911968 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911969 : term209 = term143.
Proof. exact (MK_COMB (@lem3911968) (@lem3911967)). Qed.
Lemma lem3911970 : term208 = term143.
Proof. exact (TRANS (@lem3911965) (@lem3911969)). Qed.
Lemma lem3911972 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3911973 : term225 = term230.
Proof. exact (@lem3911972 term11 term11). Qed.
Lemma lem3911974 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3911975 : term211 = term11.
Proof. exact (EQ_MP (@lem3911974) (@lem940073)). Qed.
Lemma lem3911976 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3911977 : term209 = term143.
Proof. exact (MK_COMB (@lem3911976) (@lem3911975)). Qed.
Lemma lem3911978 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3911979 : term230 = term199.
Proof. exact (MK_COMB (@lem3911978) (@lem3911977)). Qed.
Lemma lem3911980 : term225 = term199.
Proof. exact (TRANS (@lem3911973) (@lem3911979)). Qed.
Lemma lem3911981 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3911982 : term507 = term499.
Proof. exact (MK_COMB (@lem3911981) (@lem3911980)). Qed.
Lemma lem3911983 : term508 = term501.
Proof. exact (MK_COMB (@lem3911982) (@lem3911970)). Qed.
Lemma lem3911985 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3911986 : term501 = term133.
Proof. exact (@lem3911985 term11). Qed.
Lemma lem3911987 : term508 = term133.
Proof. exact (TRANS (@lem3911983) (@lem3911986)). Qed.
Lemma lem3911988 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3911989 : term510 = term261.
Proof. exact (MK_COMB (@lem3911988) (@lem3911987)). Qed.
Lemma lem3911990 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3911991 : term511 = term263.
Proof. exact (MK_COMB (@lem3911989) (@lem3911990)). Qed.
Lemma lem3911993 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3911994 : term263 = term133.
Proof. exact (@lem3911993 term11). Qed.
Lemma lem3911995 : term511 = term133.
Proof. exact (TRANS (@lem3911991) (@lem3911994)). Qed.
Lemma lem3911997 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3911998 : term208 = term209.
Proof. exact (@lem3911997 term11 term11). Qed.
Lemma lem3911999 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912000 : term211 = term11.
Proof. exact (EQ_MP (@lem3911999) (@lem940073)). Qed.
Lemma lem3912001 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912002 : term209 = term143.
Proof. exact (MK_COMB (@lem3912001) (@lem3912000)). Qed.
Lemma lem3912003 : term208 = term143.
Proof. exact (TRANS (@lem3911998) (@lem3912002)). Qed.
Lemma lem3912004 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3912005 : term265 = term263.
Proof. exact (MK_COMB (@lem3912004) (@lem3912003)). Qed.
Lemma lem3912007 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912008 : term263 = term133.
Proof. exact (@lem3912007 term11). Qed.
Lemma lem3912009 : term265 = term133.
Proof. exact (TRANS (@lem3912005) (@lem3912008)). Qed.
Lemma lem3912010 : term133 = term265.
Proof. exact (SYM (@lem3912009)). Qed.
Lemma lem3912011 : term511 = term265.
Proof. exact (TRANS (@lem3911995) (@lem3912010)). Qed.
Lemma lem3912012 : term502 = term196.
Proof. exact (@lem3911962 (@lem3912011)). Qed.
Lemma lem3912013 : term501 = term196.
Proof. exact (TRANS (@lem3911928) (@lem3912012)). Qed.
Lemma lem3912015 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3912016 : term196 = term133.
Proof. exact (@lem3912015 term133). Qed.
Lemma lem3912017 : term501 = term133.
Proof. exact (TRANS (@lem3912013) (@lem3912016)). Qed.
Lemma lem3912018 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912019 : term512 = term261.
Proof. exact (MK_COMB (@lem3912018) (@lem3912017)). Qed.
Lemma lem3912020 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3912021 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3912019) (@lem3912020 _45439)). Qed.
Lemma lem3912022 (_45439 : int) : (term497 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3911919 _45439) (@lem3912021 _45439)). Qed.
Lemma lem3912023 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3912024 (_45439 : int) : (term497 _45439) = term133.
Proof. exact (TRANS (@lem3912022 _45439) (@lem3912023 _45439)). Qed.
Lemma lem3912025 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912026 (_45439 : int) : (term514 _45439) = term175.
Proof. exact (MK_COMB (@lem3912025) (@lem3912024 _45439)). Qed.
Lemma lem3912027 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3912028 (_45439 : int) : (term574 _45439) = term519.
Proof. exact (MK_COMB (@lem3912026 _45439) (@lem3912027)). Qed.
Lemma lem3912029 (_45439 : int) : (term573 _45439) = term519.
Proof. exact (TRANS (@lem3911918 _45439) (@lem3912028 _45439)). Qed.
Lemma lem3912030 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3912031 (_45439 : int) : (term573 _45439) = term199.
Proof. exact (TRANS (@lem3912029 _45439) (@lem3912030)). Qed.
Lemma lem3912032 (_45438 : int) : (term233 _45438) = (term233 _45438).
Proof. exact (eq_refl (term233 _45438)). Qed.
Lemma lem3912033 (_45439 : int) (_45438 : int) : (term588 _45438 _45439) = (term234 _45438).
Proof. exact (MK_COMB (@lem3912032 _45438) (@lem3912031 _45439)). Qed.
Lemma lem3912034 (_45439 : int) (_45438 : int) : (term587 _45438 _45439) = (term234 _45438).
Proof. exact (TRANS (@lem3911917 _45438 _45439) (@lem3912033 _45439 _45438)). Qed.
Lemma lem3912035 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3912036 (_45439 : int) (_45438 : int) : (term589 _45438 _45439) = (term590 _45438).
Proof. exact (MK_COMB (@lem3912035) (@lem3912034 _45439 _45438)). Qed.
Lemma lem3912037 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912038 (_45439 : int) (_45438 : int) : ((term587 _45438 _45439) = term133) = ((term234 _45438) = term133).
Proof. exact (MK_COMB (@lem3912036 _45439 _45438) (@lem3912037)). Qed.
Lemma lem3912039 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term234 _45438) = term133.
Proof. exact (EQ_MP (@lem3912038 _45439 _45438) (@lem3911916 _45438 _45439 h1)). Qed.
Lemma lem3912041 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3912042 (_45438 : int) : term591 _45438.
Proof. exact (@lem3912041 (term234 _45438)). Qed.
Lemma lem3912043 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term592 _45438.
Proof. exact (@lem3912042 _45438 (@lem3912039 _45438 _45439 h1)). Qed.
Lemma lem3912044 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term593 _45438.
Proof. exact (@lem3912043 _45438 _45439 h1 term143). Qed.
Lemma lem3912045 (_45438 : int) : (term593 _45438) = ((term594 _45438) = term133).
Proof. exact (eq_refl (term593 _45438)). Qed.
Lemma lem3912046 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term594 _45438) = term133.
Proof. exact (EQ_MP (@lem3912045 _45438) (@lem3912044 _45438 _45439 h1)). Qed.
Lemma lem3912047 (_45438 : int) : (term594 _45438) = (term234 _45438).
Proof. exact (@lem1982733 (term234 _45438)). Qed.
Lemma lem3912048 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3912049 (_45438 : int) : (term595 _45438) = (term590 _45438).
Proof. exact (MK_COMB (@lem3912048) (@lem3912047 _45438)). Qed.
Lemma lem3912050 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912051 (_45438 : int) : ((term594 _45438) = term133) = ((term234 _45438) = term133).
Proof. exact (MK_COMB (@lem3912049 _45438) (@lem3912050)). Qed.
Lemma lem3912052 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : (term234 _45438) = term133.
Proof. exact (EQ_MP (@lem3912051 _45438) (@lem3912046 _45438 _45439 h1)). Qed.
Lemma lem3912053 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term596 _45438.
Proof. exact (conj (@lem3912052 _45438 _45439 h1) (@lem3911824 _45438 _45439 h1)). Qed.
Lemma lem3912055 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3912056 (_45438 : int) : term597 _45438.
Proof. exact (@lem3912055 (term234 _45438) (real_of_int _45438)). Qed.
Lemma lem3912057 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term598 _45438.
Proof. exact (@lem3912056 _45438 (@lem3912053 _45438 _45439 h1)). Qed.
Lemma lem3912058 (_45438 : int) : (term599 _45438) = (term574 _45438).
Proof. exact (@lem1982759 (term237 _45438) (real_of_int _45438) term199). Qed.
Lemma lem3912059 (_45438 : int) : (term497 _45438) = (term498 _45438).
Proof. exact (@lem1982713 term199 (real_of_int _45438)). Qed.
Lemma lem3912061 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912062 : term143 = term224.
Proof. exact (@lem3912061 term11). Qed.
Lemma lem3912064 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3912065 : term199 = term200.
Proof. exact (@lem3912064 term11). Qed.
Lemma lem3912066 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912067 : term499 = term500.
Proof. exact (MK_COMB (@lem3912066) (@lem3912065)). Qed.
Lemma lem3912068 : term501 = term502.
Proof. exact (MK_COMB (@lem3912067) (@lem3912062)). Qed.
Lemma lem3912069 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3912071 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912072 : term251 = term252.
Proof. exact (@lem3912071 (NUMERAL 0) term11). Qed.
Lemma lem3912073 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912074 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912075 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912074 h1) (fun h1 : term252 = True => @lem3912073)). Qed.
Lemma lem3912076 : term252 = True.
Proof. exact (EQ_MP (@lem3912075) (@lem3912073)). Qed.
Lemma lem3912077 : term251 = True.
Proof. exact (TRANS (@lem3912072) (@lem3912076)). Qed.
Lemma lem3912078 : True = term251.
Proof. exact (SYM (@lem3912077)). Qed.
Lemma lem3912079 : term251.
Proof. exact (EQ_MP (@lem3912078) (@lem0)). Qed.
Lemma lem3912080 : term504.
Proof. exact (@lem3912069 (@lem3912079)). Qed.
Lemma lem3912082 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912083 : term251 = term252.
Proof. exact (@lem3912082 (NUMERAL 0) term11). Qed.
Lemma lem3912084 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912085 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912086 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912085 h1) (fun h1 : term252 = True => @lem3912084)). Qed.
Lemma lem3912087 : term252 = True.
Proof. exact (EQ_MP (@lem3912086) (@lem3912084)). Qed.
Lemma lem3912088 : term251 = True.
Proof. exact (TRANS (@lem3912083) (@lem3912087)). Qed.
Lemma lem3912089 : True = term251.
Proof. exact (SYM (@lem3912088)). Qed.
Lemma lem3912090 : term251.
Proof. exact (EQ_MP (@lem3912089) (@lem0)). Qed.
Lemma lem3912091 : term505.
Proof. exact (@lem3912080 (@lem3912090)). Qed.
Lemma lem3912093 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912094 : term251 = term252.
Proof. exact (@lem3912093 (NUMERAL 0) term11). Qed.
Lemma lem3912095 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912096 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912097 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912096 h1) (fun h1 : term252 = True => @lem3912095)). Qed.
Lemma lem3912098 : term252 = True.
Proof. exact (EQ_MP (@lem3912097) (@lem3912095)). Qed.
Lemma lem3912099 : term251 = True.
Proof. exact (TRANS (@lem3912094) (@lem3912098)). Qed.
Lemma lem3912100 : True = term251.
Proof. exact (SYM (@lem3912099)). Qed.
Lemma lem3912101 : term251.
Proof. exact (EQ_MP (@lem3912100) (@lem0)). Qed.
Lemma lem3912102 : term506.
Proof. exact (@lem3912091 (@lem3912101)). Qed.
Lemma lem3912104 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912105 : term208 = term209.
Proof. exact (@lem3912104 term11 term11). Qed.
Lemma lem3912106 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912107 : term211 = term11.
Proof. exact (EQ_MP (@lem3912106) (@lem940073)). Qed.
Lemma lem3912108 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912109 : term209 = term143.
Proof. exact (MK_COMB (@lem3912108) (@lem3912107)). Qed.
Lemma lem3912110 : term208 = term143.
Proof. exact (TRANS (@lem3912105) (@lem3912109)). Qed.
Lemma lem3912112 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3912113 : term225 = term230.
Proof. exact (@lem3912112 term11 term11). Qed.
Lemma lem3912114 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912115 : term211 = term11.
Proof. exact (EQ_MP (@lem3912114) (@lem940073)). Qed.
Lemma lem3912116 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912117 : term209 = term143.
Proof. exact (MK_COMB (@lem3912116) (@lem3912115)). Qed.
Lemma lem3912118 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3912119 : term230 = term199.
Proof. exact (MK_COMB (@lem3912118) (@lem3912117)). Qed.
Lemma lem3912120 : term225 = term199.
Proof. exact (TRANS (@lem3912113) (@lem3912119)). Qed.
Lemma lem3912121 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912122 : term507 = term499.
Proof. exact (MK_COMB (@lem3912121) (@lem3912120)). Qed.
Lemma lem3912123 : term508 = term501.
Proof. exact (MK_COMB (@lem3912122) (@lem3912110)). Qed.
Lemma lem3912125 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3912126 : term501 = term133.
Proof. exact (@lem3912125 term11). Qed.
Lemma lem3912127 : term508 = term133.
Proof. exact (TRANS (@lem3912123) (@lem3912126)). Qed.
Lemma lem3912128 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912129 : term510 = term261.
Proof. exact (MK_COMB (@lem3912128) (@lem3912127)). Qed.
Lemma lem3912130 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3912131 : term511 = term263.
Proof. exact (MK_COMB (@lem3912129) (@lem3912130)). Qed.
Lemma lem3912133 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912134 : term263 = term133.
Proof. exact (@lem3912133 term11). Qed.
Lemma lem3912135 : term511 = term133.
Proof. exact (TRANS (@lem3912131) (@lem3912134)). Qed.
Lemma lem3912137 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912138 : term208 = term209.
Proof. exact (@lem3912137 term11 term11). Qed.
Lemma lem3912139 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912140 : term211 = term11.
Proof. exact (EQ_MP (@lem3912139) (@lem940073)). Qed.
Lemma lem3912141 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912142 : term209 = term143.
Proof. exact (MK_COMB (@lem3912141) (@lem3912140)). Qed.
Lemma lem3912143 : term208 = term143.
Proof. exact (TRANS (@lem3912138) (@lem3912142)). Qed.
Lemma lem3912144 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3912145 : term265 = term263.
Proof. exact (MK_COMB (@lem3912144) (@lem3912143)). Qed.
Lemma lem3912147 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912148 : term263 = term133.
Proof. exact (@lem3912147 term11). Qed.
Lemma lem3912149 : term265 = term133.
Proof. exact (TRANS (@lem3912145) (@lem3912148)). Qed.
Lemma lem3912150 : term133 = term265.
Proof. exact (SYM (@lem3912149)). Qed.
Lemma lem3912151 : term511 = term265.
Proof. exact (TRANS (@lem3912135) (@lem3912150)). Qed.
Lemma lem3912152 : term502 = term196.
Proof. exact (@lem3912102 (@lem3912151)). Qed.
Lemma lem3912153 : term501 = term196.
Proof. exact (TRANS (@lem3912068) (@lem3912152)). Qed.
Lemma lem3912155 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3912156 : term196 = term133.
Proof. exact (@lem3912155 term133). Qed.
Lemma lem3912157 : term501 = term133.
Proof. exact (TRANS (@lem3912153) (@lem3912156)). Qed.
Lemma lem3912158 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912159 : term512 = term261.
Proof. exact (MK_COMB (@lem3912158) (@lem3912157)). Qed.
Lemma lem3912160 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3912161 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3912159) (@lem3912160 _45438)). Qed.
Lemma lem3912162 (_45438 : int) : (term497 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3912059 _45438) (@lem3912161 _45438)). Qed.
Lemma lem3912163 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3912164 (_45438 : int) : (term497 _45438) = term133.
Proof. exact (TRANS (@lem3912162 _45438) (@lem3912163 _45438)). Qed.
Lemma lem3912165 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912166 (_45438 : int) : (term514 _45438) = term175.
Proof. exact (MK_COMB (@lem3912165) (@lem3912164 _45438)). Qed.
Lemma lem3912167 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3912168 (_45438 : int) : (term574 _45438) = term519.
Proof. exact (MK_COMB (@lem3912166 _45438) (@lem3912167)). Qed.
Lemma lem3912169 (_45438 : int) : (term599 _45438) = term519.
Proof. exact (TRANS (@lem3912058 _45438) (@lem3912168 _45438)). Qed.
Lemma lem3912170 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3912171 (_45438 : int) : (term599 _45438) = term199.
Proof. exact (TRANS (@lem3912169 _45438) (@lem3912170)). Qed.
Lemma lem3912172 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3912173 (_45438 : int) : (term600 _45438) = term521.
Proof. exact (MK_COMB (@lem3912172) (@lem3912171 _45438)). Qed.
Lemma lem3912174 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912175 (_45438 : int) : (term598 _45438) = term522.
Proof. exact (MK_COMB (@lem3912173 _45438) (@lem3912174)). Qed.
Lemma lem3912176 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3912175 _45438) (@lem3912057 _45438 _45439 h1)). Qed.
Lemma lem3912178 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3912179 : term522 = term523.
Proof. exact (@lem3912178 term133 term199). Qed.
Lemma lem3912181 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3912182 : term199 = term200.
Proof. exact (@lem3912181 term11). Qed.
Lemma lem3912184 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912185 : term133 = term196.
Proof. exact (@lem3912184 (NUMERAL 0)). Qed.
Lemma lem3912186 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3912187 : term135 = term524.
Proof. exact (MK_COMB (@lem3912186) (@lem3912185)). Qed.
Lemma lem3912188 : term523 = term525.
Proof. exact (MK_COMB (@lem3912187) (@lem3912182)). Qed.
Lemma lem3912189 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3912191 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912192 : term251 = term252.
Proof. exact (@lem3912191 (NUMERAL 0) term11). Qed.
Lemma lem3912193 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912194 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912195 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912194 h1) (fun h1 : term252 = True => @lem3912193)). Qed.
Lemma lem3912196 : term252 = True.
Proof. exact (EQ_MP (@lem3912195) (@lem3912193)). Qed.
Lemma lem3912197 : term251 = True.
Proof. exact (TRANS (@lem3912192) (@lem3912196)). Qed.
Lemma lem3912198 : True = term251.
Proof. exact (SYM (@lem3912197)). Qed.
Lemma lem3912199 : term251.
Proof. exact (EQ_MP (@lem3912198) (@lem0)). Qed.
Lemma lem3912200 : term527.
Proof. exact (@lem3912189 (@lem3912199)). Qed.
Lemma lem3912202 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912203 : term251 = term252.
Proof. exact (@lem3912202 (NUMERAL 0) term11). Qed.
Lemma lem3912204 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912205 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912206 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912205 h1) (fun h1 : term252 = True => @lem3912204)). Qed.
Lemma lem3912207 : term252 = True.
Proof. exact (EQ_MP (@lem3912206) (@lem3912204)). Qed.
Lemma lem3912208 : term251 = True.
Proof. exact (TRANS (@lem3912203) (@lem3912207)). Qed.
Lemma lem3912209 : True = term251.
Proof. exact (SYM (@lem3912208)). Qed.
Lemma lem3912210 : term251.
Proof. exact (EQ_MP (@lem3912209) (@lem0)). Qed.
Lemma lem3912211 : term525 = term528.
Proof. exact (@lem3912200 (@lem3912210)). Qed.
Lemma lem3912213 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3912214 : term225 = term230.
Proof. exact (@lem3912213 term11 term11). Qed.
Lemma lem3912215 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912216 : term211 = term11.
Proof. exact (EQ_MP (@lem3912215) (@lem940073)). Qed.
Lemma lem3912217 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912218 : term209 = term143.
Proof. exact (MK_COMB (@lem3912217) (@lem3912216)). Qed.
Lemma lem3912219 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3912220 : term230 = term199.
Proof. exact (MK_COMB (@lem3912219) (@lem3912218)). Qed.
Lemma lem3912221 : term225 = term199.
Proof. exact (TRANS (@lem3912214) (@lem3912220)). Qed.
Lemma lem3912223 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912224 : term263 = term133.
Proof. exact (@lem3912223 term11). Qed.
Lemma lem3912225 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3912226 : term529 = term135.
Proof. exact (MK_COMB (@lem3912225) (@lem3912224)). Qed.
Lemma lem3912227 : term528 = term523.
Proof. exact (MK_COMB (@lem3912226) (@lem3912221)). Qed.
Lemma lem3912229 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3912230 : term523 = term532.
Proof. exact (@lem3912229 (NUMERAL 0) term11). Qed.
Lemma lem3912231 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912232 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3912233 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912232 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3912231)). Qed.
Lemma lem3912234 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3912233) (@lem3912231)). Qed.
Lemma lem3912235 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3912236 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3912237 : term533 = (and True).
Proof. exact (MK_COMB (@lem3912236) (@lem3912235)). Qed.
Lemma lem3912238 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3912237) (@lem3912234)). Qed.
Lemma lem3912240 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3912241 : term532 = False.
Proof. exact (TRANS (@lem3912238) (@lem3912240)). Qed.
Lemma lem3912242 : term523 = False.
Proof. exact (TRANS (@lem3912230) (@lem3912241)). Qed.
Lemma lem3912243 : term528 = False.
Proof. exact (TRANS (@lem3912227) (@lem3912242)). Qed.
Lemma lem3912244 : term525 = False.
Proof. exact (TRANS (@lem3912211) (@lem3912243)). Qed.
Lemma lem3912245 : term523 = False.
Proof. exact (TRANS (@lem3912188) (@lem3912244)). Qed.
Lemma lem3912246 : term522 = False.
Proof. exact (TRANS (@lem3912179) (@lem3912245)). Qed.
Lemma lem3912247 (_45438 : int) (_45439 : int) (h1 : term576 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3912246) (@lem3912176 _45438 _45439 h1)). Qed.
Lemma lem3912248 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term601 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3912249 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term459 _45438 _45439.
Proof. exact (proj2 (@lem3912248 _45438 _45439 h1)). Qed.
Lemma lem3912251 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term410 _45438 _45439.
Proof. exact (proj2 (@lem3912249 _45438 _45439 h1)). Qed.
Lemma lem3912253 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term361 _45438 _45439.
Proof. exact (proj2 (@lem3912251 _45438 _45439 h1)). Qed.
Lemma lem3912254 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term272 _45439 _45438.
Proof. exact (proj1 (@lem3912251 _45438 _45439 h1)). Qed.
Lemma lem3912255 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : (real_of_int _45438) = term133.
Proof. exact (proj2 (@lem3912254 _45438 _45439 h1)). Qed.
Lemma lem3912257 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term286 _45438 _45439.
Proof. exact (proj2 (@lem3912253 _45438 _45439 h1)). Qed.
Lemma lem3912258 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (proj1 (@lem3912253 _45438 _45439 h1)). Qed.
Lemma lem3912260 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3912261 : term471 = term251.
Proof. exact (@lem3912260 term133 term143). Qed.
Lemma lem3912263 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912264 : term143 = term224.
Proof. exact (@lem3912263 term11). Qed.
Lemma lem3912266 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912267 : term133 = term196.
Proof. exact (@lem3912266 (NUMERAL 0)). Qed.
Lemma lem3912268 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3912269 : term472 = term473.
Proof. exact (MK_COMB (@lem3912268) (@lem3912267)). Qed.
Lemma lem3912270 : term251 = term474.
Proof. exact (MK_COMB (@lem3912269) (@lem3912264)). Qed.
Lemma lem3912271 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3912273 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912274 : term251 = term252.
Proof. exact (@lem3912273 (NUMERAL 0) term11). Qed.
Lemma lem3912275 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912276 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912277 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912276 h1) (fun h1 : term252 = True => @lem3912275)). Qed.
Lemma lem3912278 : term252 = True.
Proof. exact (EQ_MP (@lem3912277) (@lem3912275)). Qed.
Lemma lem3912279 : term251 = True.
Proof. exact (TRANS (@lem3912274) (@lem3912278)). Qed.
Lemma lem3912280 : True = term251.
Proof. exact (SYM (@lem3912279)). Qed.
Lemma lem3912281 : term251.
Proof. exact (EQ_MP (@lem3912280) (@lem0)). Qed.
Lemma lem3912282 : term476.
Proof. exact (@lem3912271 (@lem3912281)). Qed.
Lemma lem3912284 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912285 : term251 = term252.
Proof. exact (@lem3912284 (NUMERAL 0) term11). Qed.
Lemma lem3912286 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912287 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912288 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912287 h1) (fun h1 : term252 = True => @lem3912286)). Qed.
Lemma lem3912289 : term252 = True.
Proof. exact (EQ_MP (@lem3912288) (@lem3912286)). Qed.
Lemma lem3912290 : term251 = True.
Proof. exact (TRANS (@lem3912285) (@lem3912289)). Qed.
Lemma lem3912291 : True = term251.
Proof. exact (SYM (@lem3912290)). Qed.
Lemma lem3912292 : term251.
Proof. exact (EQ_MP (@lem3912291) (@lem0)). Qed.
Lemma lem3912293 : term474 = term477.
Proof. exact (@lem3912282 (@lem3912292)). Qed.
Lemma lem3912295 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912296 : term208 = term209.
Proof. exact (@lem3912295 term11 term11). Qed.
Lemma lem3912297 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912298 : term211 = term11.
Proof. exact (EQ_MP (@lem3912297) (@lem940073)). Qed.
Lemma lem3912299 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912300 : term209 = term143.
Proof. exact (MK_COMB (@lem3912299) (@lem3912298)). Qed.
Lemma lem3912301 : term208 = term143.
Proof. exact (TRANS (@lem3912296) (@lem3912300)). Qed.
Lemma lem3912303 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912304 : term263 = term133.
Proof. exact (@lem3912303 term11). Qed.
Lemma lem3912305 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3912306 : term478 = term472.
Proof. exact (MK_COMB (@lem3912305) (@lem3912304)). Qed.
Lemma lem3912307 : term477 = term251.
Proof. exact (MK_COMB (@lem3912306) (@lem3912301)). Qed.
Lemma lem3912309 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912310 : term251 = term252.
Proof. exact (@lem3912309 (NUMERAL 0) term11). Qed.
Lemma lem3912311 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912312 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912313 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912312 h1) (fun h1 : term252 = True => @lem3912311)). Qed.
Lemma lem3912314 : term252 = True.
Proof. exact (EQ_MP (@lem3912313) (@lem3912311)). Qed.
Lemma lem3912315 : term251 = True.
Proof. exact (TRANS (@lem3912310) (@lem3912314)). Qed.
Lemma lem3912316 : term477 = True.
Proof. exact (TRANS (@lem3912307) (@lem3912315)). Qed.
Lemma lem3912317 : term474 = True.
Proof. exact (TRANS (@lem3912293) (@lem3912316)). Qed.
Lemma lem3912318 : term251 = True.
Proof. exact (TRANS (@lem3912270) (@lem3912317)). Qed.
Lemma lem3912319 : term471 = True.
Proof. exact (TRANS (@lem3912261) (@lem3912318)). Qed.
Lemma lem3912320 : True = term471.
Proof. exact (SYM (@lem3912319)). Qed.
Lemma lem3912321 : term471.
Proof. exact (EQ_MP (@lem3912320) (@lem0)). Qed.
Lemma lem3912322 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term535 _45438 _45439.
Proof. exact (conj (@lem3912321) (@lem3912257 _45438 _45439 h1)). Qed.
Lemma lem3912324 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3912325 (_45438 : int) (_45439 : int) : term536 _45438 _45439.
Proof. exact (@lem3912324 term143 (term236 _45438 _45439)). Qed.
Lemma lem3912326 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term537 _45438 _45439.
Proof. exact (@lem3912325 _45438 _45439 (@lem3912322 _45438 _45439 h1)). Qed.
Lemma lem3912327 (_45438 : int) (_45439 : int) : (term489 _45438 _45439) = (term236 _45438 _45439).
Proof. exact (@lem1982733 (term236 _45438 _45439)). Qed.
Lemma lem3912328 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3912329 (_45438 : int) (_45439 : int) : (term538 _45438 _45439) = (term285 _45438 _45439).
Proof. exact (MK_COMB (@lem3912328) (@lem3912327 _45438 _45439)). Qed.
Lemma lem3912330 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912331 (_45438 : int) (_45439 : int) : (term537 _45438 _45439) = (term286 _45438 _45439).
Proof. exact (MK_COMB (@lem3912329 _45438 _45439) (@lem3912330)). Qed.
Lemma lem3912332 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term286 _45438 _45439.
Proof. exact (EQ_MP (@lem3912331 _45438 _45439) (@lem3912326 _45438 _45439 h1)). Qed.
Lemma lem3912334 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3912335 (_45439 : int) : term539 _45439.
Proof. exact (@lem3912334 (real_of_int _45439)). Qed.
Lemma lem3912336 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term540 _45439.
Proof. exact (@lem3912335 _45439 (@lem3912258 _45438 _45439 h1)). Qed.
Lemma lem3912337 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term556 _45439.
Proof. exact (@lem3912336 _45438 _45439 h1 term199). Qed.
Lemma lem3912338 (_45439 : int) : (term556 _45439) = ((term237 _45439) = term133).
Proof. exact (eq_refl (term556 _45439)). Qed.
Lemma lem3912345 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : (term237 _45439) = term133.
Proof. exact (EQ_MP (@lem3912338 _45439) (@lem3912337 _45438 _45439 h1)). Qed.
Lemma lem3912346 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term602 _45438 _45439.
Proof. exact (conj (@lem3912345 _45438 _45439 h1) (@lem3912332 _45438 _45439 h1)). Qed.
Lemma lem3912348 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3912349 (_45438 : int) (_45439 : int) : term603 _45438 _45439.
Proof. exact (@lem3912348 (term237 _45439) (term236 _45438 _45439)). Qed.
Lemma lem3912350 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term604 _45438 _45439.
Proof. exact (@lem3912349 _45438 _45439 (@lem3912346 _45438 _45439 h1)). Qed.
Lemma lem3912351 (_45438 : int) (_45439 : int) : (term587 _45438 _45439) = (term588 _45438 _45439).
Proof. exact (@lem1982757 (term237 _45438) (term237 _45439) (term299 _45439)). Qed.
Lemma lem3912352 (_45439 : int) : (term573 _45439) = (term574 _45439).
Proof. exact (@lem1982763 (term237 _45439) (real_of_int _45439) term199). Qed.
Lemma lem3912353 (_45439 : int) : (term497 _45439) = (term498 _45439).
Proof. exact (@lem1982713 term199 (real_of_int _45439)). Qed.
Lemma lem3912355 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912356 : term143 = term224.
Proof. exact (@lem3912355 term11). Qed.
Lemma lem3912358 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3912359 : term199 = term200.
Proof. exact (@lem3912358 term11). Qed.
Lemma lem3912360 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912361 : term499 = term500.
Proof. exact (MK_COMB (@lem3912360) (@lem3912359)). Qed.
Lemma lem3912362 : term501 = term502.
Proof. exact (MK_COMB (@lem3912361) (@lem3912356)). Qed.
Lemma lem3912363 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3912365 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912366 : term251 = term252.
Proof. exact (@lem3912365 (NUMERAL 0) term11). Qed.
Lemma lem3912367 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912368 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912369 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912368 h1) (fun h1 : term252 = True => @lem3912367)). Qed.
Lemma lem3912370 : term252 = True.
Proof. exact (EQ_MP (@lem3912369) (@lem3912367)). Qed.
Lemma lem3912371 : term251 = True.
Proof. exact (TRANS (@lem3912366) (@lem3912370)). Qed.
Lemma lem3912372 : True = term251.
Proof. exact (SYM (@lem3912371)). Qed.
Lemma lem3912373 : term251.
Proof. exact (EQ_MP (@lem3912372) (@lem0)). Qed.
Lemma lem3912374 : term504.
Proof. exact (@lem3912363 (@lem3912373)). Qed.
Lemma lem3912376 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912377 : term251 = term252.
Proof. exact (@lem3912376 (NUMERAL 0) term11). Qed.
Lemma lem3912378 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912379 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912380 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912379 h1) (fun h1 : term252 = True => @lem3912378)). Qed.
Lemma lem3912381 : term252 = True.
Proof. exact (EQ_MP (@lem3912380) (@lem3912378)). Qed.
Lemma lem3912382 : term251 = True.
Proof. exact (TRANS (@lem3912377) (@lem3912381)). Qed.
Lemma lem3912383 : True = term251.
Proof. exact (SYM (@lem3912382)). Qed.
Lemma lem3912384 : term251.
Proof. exact (EQ_MP (@lem3912383) (@lem0)). Qed.
Lemma lem3912385 : term505.
Proof. exact (@lem3912374 (@lem3912384)). Qed.
Lemma lem3912387 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912388 : term251 = term252.
Proof. exact (@lem3912387 (NUMERAL 0) term11). Qed.
Lemma lem3912389 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912390 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912391 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912390 h1) (fun h1 : term252 = True => @lem3912389)). Qed.
Lemma lem3912392 : term252 = True.
Proof. exact (EQ_MP (@lem3912391) (@lem3912389)). Qed.
Lemma lem3912393 : term251 = True.
Proof. exact (TRANS (@lem3912388) (@lem3912392)). Qed.
Lemma lem3912394 : True = term251.
Proof. exact (SYM (@lem3912393)). Qed.
Lemma lem3912395 : term251.
Proof. exact (EQ_MP (@lem3912394) (@lem0)). Qed.
Lemma lem3912396 : term506.
Proof. exact (@lem3912385 (@lem3912395)). Qed.
Lemma lem3912398 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912399 : term208 = term209.
Proof. exact (@lem3912398 term11 term11). Qed.
Lemma lem3912400 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912401 : term211 = term11.
Proof. exact (EQ_MP (@lem3912400) (@lem940073)). Qed.
Lemma lem3912402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912403 : term209 = term143.
Proof. exact (MK_COMB (@lem3912402) (@lem3912401)). Qed.
Lemma lem3912404 : term208 = term143.
Proof. exact (TRANS (@lem3912399) (@lem3912403)). Qed.
Lemma lem3912406 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3912407 : term225 = term230.
Proof. exact (@lem3912406 term11 term11). Qed.
Lemma lem3912408 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912409 : term211 = term11.
Proof. exact (EQ_MP (@lem3912408) (@lem940073)). Qed.
Lemma lem3912410 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912411 : term209 = term143.
Proof. exact (MK_COMB (@lem3912410) (@lem3912409)). Qed.
Lemma lem3912412 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3912413 : term230 = term199.
Proof. exact (MK_COMB (@lem3912412) (@lem3912411)). Qed.
Lemma lem3912414 : term225 = term199.
Proof. exact (TRANS (@lem3912407) (@lem3912413)). Qed.
Lemma lem3912415 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912416 : term507 = term499.
Proof. exact (MK_COMB (@lem3912415) (@lem3912414)). Qed.
Lemma lem3912417 : term508 = term501.
Proof. exact (MK_COMB (@lem3912416) (@lem3912404)). Qed.
Lemma lem3912419 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3912420 : term501 = term133.
Proof. exact (@lem3912419 term11). Qed.
Lemma lem3912421 : term508 = term133.
Proof. exact (TRANS (@lem3912417) (@lem3912420)). Qed.
Lemma lem3912422 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912423 : term510 = term261.
Proof. exact (MK_COMB (@lem3912422) (@lem3912421)). Qed.
Lemma lem3912424 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3912425 : term511 = term263.
Proof. exact (MK_COMB (@lem3912423) (@lem3912424)). Qed.
Lemma lem3912427 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912428 : term263 = term133.
Proof. exact (@lem3912427 term11). Qed.
Lemma lem3912429 : term511 = term133.
Proof. exact (TRANS (@lem3912425) (@lem3912428)). Qed.
Lemma lem3912431 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912432 : term208 = term209.
Proof. exact (@lem3912431 term11 term11). Qed.
Lemma lem3912433 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912434 : term211 = term11.
Proof. exact (EQ_MP (@lem3912433) (@lem940073)). Qed.
Lemma lem3912435 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912436 : term209 = term143.
Proof. exact (MK_COMB (@lem3912435) (@lem3912434)). Qed.
Lemma lem3912437 : term208 = term143.
Proof. exact (TRANS (@lem3912432) (@lem3912436)). Qed.
Lemma lem3912438 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3912439 : term265 = term263.
Proof. exact (MK_COMB (@lem3912438) (@lem3912437)). Qed.
Lemma lem3912441 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912442 : term263 = term133.
Proof. exact (@lem3912441 term11). Qed.
Lemma lem3912443 : term265 = term133.
Proof. exact (TRANS (@lem3912439) (@lem3912442)). Qed.
Lemma lem3912444 : term133 = term265.
Proof. exact (SYM (@lem3912443)). Qed.
Lemma lem3912445 : term511 = term265.
Proof. exact (TRANS (@lem3912429) (@lem3912444)). Qed.
Lemma lem3912446 : term502 = term196.
Proof. exact (@lem3912396 (@lem3912445)). Qed.
Lemma lem3912447 : term501 = term196.
Proof. exact (TRANS (@lem3912362) (@lem3912446)). Qed.
Lemma lem3912449 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3912450 : term196 = term133.
Proof. exact (@lem3912449 term133). Qed.
Lemma lem3912451 : term501 = term133.
Proof. exact (TRANS (@lem3912447) (@lem3912450)). Qed.
Lemma lem3912452 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912453 : term512 = term261.
Proof. exact (MK_COMB (@lem3912452) (@lem3912451)). Qed.
Lemma lem3912454 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3912455 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3912453) (@lem3912454 _45439)). Qed.
Lemma lem3912456 (_45439 : int) : (term497 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3912353 _45439) (@lem3912455 _45439)). Qed.
Lemma lem3912457 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3912458 (_45439 : int) : (term497 _45439) = term133.
Proof. exact (TRANS (@lem3912456 _45439) (@lem3912457 _45439)). Qed.
Lemma lem3912459 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912460 (_45439 : int) : (term514 _45439) = term175.
Proof. exact (MK_COMB (@lem3912459) (@lem3912458 _45439)). Qed.
Lemma lem3912461 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3912462 (_45439 : int) : (term574 _45439) = term519.
Proof. exact (MK_COMB (@lem3912460 _45439) (@lem3912461)). Qed.
Lemma lem3912463 (_45439 : int) : (term573 _45439) = term519.
Proof. exact (TRANS (@lem3912352 _45439) (@lem3912462 _45439)). Qed.
Lemma lem3912464 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3912465 (_45439 : int) : (term573 _45439) = term199.
Proof. exact (TRANS (@lem3912463 _45439) (@lem3912464)). Qed.
Lemma lem3912466 (_45438 : int) : (term233 _45438) = (term233 _45438).
Proof. exact (eq_refl (term233 _45438)). Qed.
Lemma lem3912467 (_45439 : int) (_45438 : int) : (term588 _45438 _45439) = (term234 _45438).
Proof. exact (MK_COMB (@lem3912466 _45438) (@lem3912465 _45439)). Qed.
Lemma lem3912468 (_45439 : int) (_45438 : int) : (term587 _45438 _45439) = (term234 _45438).
Proof. exact (TRANS (@lem3912351 _45438 _45439) (@lem3912467 _45439 _45438)). Qed.
Lemma lem3912469 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3912470 (_45439 : int) (_45438 : int) : (term605 _45438 _45439) = (term292 _45438).
Proof. exact (MK_COMB (@lem3912469) (@lem3912468 _45439 _45438)). Qed.
Lemma lem3912471 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912472 (_45439 : int) (_45438 : int) : (term604 _45438 _45439) = (term293 _45438).
Proof. exact (MK_COMB (@lem3912470 _45439 _45438) (@lem3912471)). Qed.
Lemma lem3912473 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term293 _45438.
Proof. exact (EQ_MP (@lem3912472 _45439 _45438) (@lem3912350 _45438 _45439 h1)). Qed.
Lemma lem3912475 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3912476 : term471 = term251.
Proof. exact (@lem3912475 term133 term143). Qed.
Lemma lem3912478 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912479 : term143 = term224.
Proof. exact (@lem3912478 term11). Qed.
Lemma lem3912481 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912482 : term133 = term196.
Proof. exact (@lem3912481 (NUMERAL 0)). Qed.
Lemma lem3912483 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3912484 : term472 = term473.
Proof. exact (MK_COMB (@lem3912483) (@lem3912482)). Qed.
Lemma lem3912485 : term251 = term474.
Proof. exact (MK_COMB (@lem3912484) (@lem3912479)). Qed.
Lemma lem3912486 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3912488 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912489 : term251 = term252.
Proof. exact (@lem3912488 (NUMERAL 0) term11). Qed.
Lemma lem3912490 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912491 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912492 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912491 h1) (fun h1 : term252 = True => @lem3912490)). Qed.
Lemma lem3912493 : term252 = True.
Proof. exact (EQ_MP (@lem3912492) (@lem3912490)). Qed.
Lemma lem3912494 : term251 = True.
Proof. exact (TRANS (@lem3912489) (@lem3912493)). Qed.
Lemma lem3912495 : True = term251.
Proof. exact (SYM (@lem3912494)). Qed.
Lemma lem3912496 : term251.
Proof. exact (EQ_MP (@lem3912495) (@lem0)). Qed.
Lemma lem3912497 : term476.
Proof. exact (@lem3912486 (@lem3912496)). Qed.
Lemma lem3912499 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912500 : term251 = term252.
Proof. exact (@lem3912499 (NUMERAL 0) term11). Qed.
Lemma lem3912501 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912502 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912503 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912502 h1) (fun h1 : term252 = True => @lem3912501)). Qed.
Lemma lem3912504 : term252 = True.
Proof. exact (EQ_MP (@lem3912503) (@lem3912501)). Qed.
Lemma lem3912505 : term251 = True.
Proof. exact (TRANS (@lem3912500) (@lem3912504)). Qed.
Lemma lem3912506 : True = term251.
Proof. exact (SYM (@lem3912505)). Qed.
Lemma lem3912507 : term251.
Proof. exact (EQ_MP (@lem3912506) (@lem0)). Qed.
Lemma lem3912508 : term474 = term477.
Proof. exact (@lem3912497 (@lem3912507)). Qed.
Lemma lem3912510 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912511 : term208 = term209.
Proof. exact (@lem3912510 term11 term11). Qed.
Lemma lem3912512 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912513 : term211 = term11.
Proof. exact (EQ_MP (@lem3912512) (@lem940073)). Qed.
Lemma lem3912514 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912515 : term209 = term143.
Proof. exact (MK_COMB (@lem3912514) (@lem3912513)). Qed.
Lemma lem3912516 : term208 = term143.
Proof. exact (TRANS (@lem3912511) (@lem3912515)). Qed.
Lemma lem3912518 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912519 : term263 = term133.
Proof. exact (@lem3912518 term11). Qed.
Lemma lem3912520 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3912521 : term478 = term472.
Proof. exact (MK_COMB (@lem3912520) (@lem3912519)). Qed.
Lemma lem3912522 : term477 = term251.
Proof. exact (MK_COMB (@lem3912521) (@lem3912516)). Qed.
Lemma lem3912524 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912525 : term251 = term252.
Proof. exact (@lem3912524 (NUMERAL 0) term11). Qed.
Lemma lem3912526 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912527 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912528 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912527 h1) (fun h1 : term252 = True => @lem3912526)). Qed.
Lemma lem3912529 : term252 = True.
Proof. exact (EQ_MP (@lem3912528) (@lem3912526)). Qed.
Lemma lem3912530 : term251 = True.
Proof. exact (TRANS (@lem3912525) (@lem3912529)). Qed.
Lemma lem3912531 : term477 = True.
Proof. exact (TRANS (@lem3912522) (@lem3912530)). Qed.
Lemma lem3912532 : term474 = True.
Proof. exact (TRANS (@lem3912508) (@lem3912531)). Qed.
Lemma lem3912533 : term251 = True.
Proof. exact (TRANS (@lem3912485) (@lem3912532)). Qed.
Lemma lem3912534 : term471 = True.
Proof. exact (TRANS (@lem3912476) (@lem3912533)). Qed.
Lemma lem3912535 : True = term471.
Proof. exact (SYM (@lem3912534)). Qed.
Lemma lem3912536 : term471.
Proof. exact (EQ_MP (@lem3912535) (@lem0)). Qed.
Lemma lem3912537 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term606 _45438.
Proof. exact (conj (@lem3912536) (@lem3912473 _45438 _45439 h1)). Qed.
Lemma lem3912539 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3912540 (_45438 : int) : term607 _45438.
Proof. exact (@lem3912539 term143 (term234 _45438)). Qed.
Lemma lem3912541 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term608 _45438.
Proof. exact (@lem3912540 _45438 (@lem3912537 _45438 _45439 h1)). Qed.
Lemma lem3912542 (_45438 : int) : (term594 _45438) = (term234 _45438).
Proof. exact (@lem1982733 (term234 _45438)). Qed.
Lemma lem3912543 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3912544 (_45438 : int) : (term609 _45438) = (term292 _45438).
Proof. exact (MK_COMB (@lem3912543) (@lem3912542 _45438)). Qed.
Lemma lem3912545 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912546 (_45438 : int) : (term608 _45438) = (term293 _45438).
Proof. exact (MK_COMB (@lem3912544 _45438) (@lem3912545)). Qed.
Lemma lem3912547 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term293 _45438.
Proof. exact (EQ_MP (@lem3912546 _45438) (@lem3912541 _45438 _45439 h1)). Qed.
Lemma lem3912549 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3912550 (_45438 : int) : term539 _45438.
Proof. exact (@lem3912549 (real_of_int _45438)). Qed.
Lemma lem3912551 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term540 _45438.
Proof. exact (@lem3912550 _45438 (@lem3912255 _45438 _45439 h1)). Qed.
Lemma lem3912552 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term541 _45438.
Proof. exact (@lem3912551 _45438 _45439 h1 term143). Qed.
Lemma lem3912553 (_45438 : int) : (term541 _45438) = ((term542 _45438) = term133).
Proof. exact (eq_refl (term541 _45438)). Qed.
Lemma lem3912554 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : (term542 _45438) = term133.
Proof. exact (EQ_MP (@lem3912553 _45438) (@lem3912552 _45438 _45439 h1)). Qed.
Lemma lem3912555 (_45438 : int) : (term542 _45438) = (real_of_int _45438).
Proof. exact (@lem1982733 (real_of_int _45438)). Qed.
Lemma lem3912556 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3912557 (_45438 : int) : (term543 _45438) = (term146 _45438).
Proof. exact (MK_COMB (@lem3912556) (@lem3912555 _45438)). Qed.
Lemma lem3912558 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912559 (_45438 : int) : ((term542 _45438) = term133) = ((real_of_int _45438) = term133).
Proof. exact (MK_COMB (@lem3912557 _45438) (@lem3912558)). Qed.
Lemma lem3912560 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : (real_of_int _45438) = term133.
Proof. exact (EQ_MP (@lem3912559 _45438) (@lem3912554 _45438 _45439 h1)). Qed.
Lemma lem3912561 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term347 _45438.
Proof. exact (conj (@lem3912560 _45438 _45439 h1) (@lem3912547 _45438 _45439 h1)). Qed.
Lemma lem3912563 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3912564 (_45438 : int) : term610 _45438.
Proof. exact (@lem3912563 (real_of_int _45438) (term234 _45438)). Qed.
Lemma lem3912565 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term611 _45438.
Proof. exact (@lem3912564 _45438 (@lem3912561 _45438 _45439 h1)). Qed.
Lemma lem3912566 (_45438 : int) : (term612 _45438) = (term516 _45438).
Proof. exact (@lem1982763 (real_of_int _45438) (term237 _45438) term199). Qed.
Lemma lem3912567 (_45438 : int) : (term517 _45438) = (term498 _45438).
Proof. exact (@lem1982715 term199 (real_of_int _45438)). Qed.
Lemma lem3912569 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912570 : term143 = term224.
Proof. exact (@lem3912569 term11). Qed.
Lemma lem3912572 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3912573 : term199 = term200.
Proof. exact (@lem3912572 term11). Qed.
Lemma lem3912574 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912575 : term499 = term500.
Proof. exact (MK_COMB (@lem3912574) (@lem3912573)). Qed.
Lemma lem3912576 : term501 = term502.
Proof. exact (MK_COMB (@lem3912575) (@lem3912570)). Qed.
Lemma lem3912577 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3912579 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912580 : term251 = term252.
Proof. exact (@lem3912579 (NUMERAL 0) term11). Qed.
Lemma lem3912581 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912582 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912583 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912582 h1) (fun h1 : term252 = True => @lem3912581)). Qed.
Lemma lem3912584 : term252 = True.
Proof. exact (EQ_MP (@lem3912583) (@lem3912581)). Qed.
Lemma lem3912585 : term251 = True.
Proof. exact (TRANS (@lem3912580) (@lem3912584)). Qed.
Lemma lem3912586 : True = term251.
Proof. exact (SYM (@lem3912585)). Qed.
Lemma lem3912587 : term251.
Proof. exact (EQ_MP (@lem3912586) (@lem0)). Qed.
Lemma lem3912588 : term504.
Proof. exact (@lem3912577 (@lem3912587)). Qed.
Lemma lem3912590 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912591 : term251 = term252.
Proof. exact (@lem3912590 (NUMERAL 0) term11). Qed.
Lemma lem3912592 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912593 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912594 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912593 h1) (fun h1 : term252 = True => @lem3912592)). Qed.
Lemma lem3912595 : term252 = True.
Proof. exact (EQ_MP (@lem3912594) (@lem3912592)). Qed.
Lemma lem3912596 : term251 = True.
Proof. exact (TRANS (@lem3912591) (@lem3912595)). Qed.
Lemma lem3912597 : True = term251.
Proof. exact (SYM (@lem3912596)). Qed.
Lemma lem3912598 : term251.
Proof. exact (EQ_MP (@lem3912597) (@lem0)). Qed.
Lemma lem3912599 : term505.
Proof. exact (@lem3912588 (@lem3912598)). Qed.
Lemma lem3912601 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912602 : term251 = term252.
Proof. exact (@lem3912601 (NUMERAL 0) term11). Qed.
Lemma lem3912603 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912604 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912605 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912604 h1) (fun h1 : term252 = True => @lem3912603)). Qed.
Lemma lem3912606 : term252 = True.
Proof. exact (EQ_MP (@lem3912605) (@lem3912603)). Qed.
Lemma lem3912607 : term251 = True.
Proof. exact (TRANS (@lem3912602) (@lem3912606)). Qed.
Lemma lem3912608 : True = term251.
Proof. exact (SYM (@lem3912607)). Qed.
Lemma lem3912609 : term251.
Proof. exact (EQ_MP (@lem3912608) (@lem0)). Qed.
Lemma lem3912610 : term506.
Proof. exact (@lem3912599 (@lem3912609)). Qed.
Lemma lem3912612 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912613 : term208 = term209.
Proof. exact (@lem3912612 term11 term11). Qed.
Lemma lem3912614 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912615 : term211 = term11.
Proof. exact (EQ_MP (@lem3912614) (@lem940073)). Qed.
Lemma lem3912616 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912617 : term209 = term143.
Proof. exact (MK_COMB (@lem3912616) (@lem3912615)). Qed.
Lemma lem3912618 : term208 = term143.
Proof. exact (TRANS (@lem3912613) (@lem3912617)). Qed.
Lemma lem3912620 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3912621 : term225 = term230.
Proof. exact (@lem3912620 term11 term11). Qed.
Lemma lem3912622 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912623 : term211 = term11.
Proof. exact (EQ_MP (@lem3912622) (@lem940073)). Qed.
Lemma lem3912624 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912625 : term209 = term143.
Proof. exact (MK_COMB (@lem3912624) (@lem3912623)). Qed.
Lemma lem3912626 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3912627 : term230 = term199.
Proof. exact (MK_COMB (@lem3912626) (@lem3912625)). Qed.
Lemma lem3912628 : term225 = term199.
Proof. exact (TRANS (@lem3912621) (@lem3912627)). Qed.
Lemma lem3912629 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912630 : term507 = term499.
Proof. exact (MK_COMB (@lem3912629) (@lem3912628)). Qed.
Lemma lem3912631 : term508 = term501.
Proof. exact (MK_COMB (@lem3912630) (@lem3912618)). Qed.
Lemma lem3912633 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3912634 : term501 = term133.
Proof. exact (@lem3912633 term11). Qed.
Lemma lem3912635 : term508 = term133.
Proof. exact (TRANS (@lem3912631) (@lem3912634)). Qed.
Lemma lem3912636 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912637 : term510 = term261.
Proof. exact (MK_COMB (@lem3912636) (@lem3912635)). Qed.
Lemma lem3912638 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3912639 : term511 = term263.
Proof. exact (MK_COMB (@lem3912637) (@lem3912638)). Qed.
Lemma lem3912641 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912642 : term263 = term133.
Proof. exact (@lem3912641 term11). Qed.
Lemma lem3912643 : term511 = term133.
Proof. exact (TRANS (@lem3912639) (@lem3912642)). Qed.
Lemma lem3912645 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912646 : term208 = term209.
Proof. exact (@lem3912645 term11 term11). Qed.
Lemma lem3912647 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912648 : term211 = term11.
Proof. exact (EQ_MP (@lem3912647) (@lem940073)). Qed.
Lemma lem3912649 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912650 : term209 = term143.
Proof. exact (MK_COMB (@lem3912649) (@lem3912648)). Qed.
Lemma lem3912651 : term208 = term143.
Proof. exact (TRANS (@lem3912646) (@lem3912650)). Qed.
Lemma lem3912652 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3912653 : term265 = term263.
Proof. exact (MK_COMB (@lem3912652) (@lem3912651)). Qed.
Lemma lem3912655 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912656 : term263 = term133.
Proof. exact (@lem3912655 term11). Qed.
Lemma lem3912657 : term265 = term133.
Proof. exact (TRANS (@lem3912653) (@lem3912656)). Qed.
Lemma lem3912658 : term133 = term265.
Proof. exact (SYM (@lem3912657)). Qed.
Lemma lem3912659 : term511 = term265.
Proof. exact (TRANS (@lem3912643) (@lem3912658)). Qed.
Lemma lem3912660 : term502 = term196.
Proof. exact (@lem3912610 (@lem3912659)). Qed.
Lemma lem3912661 : term501 = term196.
Proof. exact (TRANS (@lem3912576) (@lem3912660)). Qed.
Lemma lem3912663 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3912664 : term196 = term133.
Proof. exact (@lem3912663 term133). Qed.
Lemma lem3912665 : term501 = term133.
Proof. exact (TRANS (@lem3912661) (@lem3912664)). Qed.
Lemma lem3912666 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912667 : term512 = term261.
Proof. exact (MK_COMB (@lem3912666) (@lem3912665)). Qed.
Lemma lem3912668 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3912669 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3912667) (@lem3912668 _45438)). Qed.
Lemma lem3912670 (_45438 : int) : (term517 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3912567 _45438) (@lem3912669 _45438)). Qed.
Lemma lem3912671 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3912672 (_45438 : int) : (term517 _45438) = term133.
Proof. exact (TRANS (@lem3912670 _45438) (@lem3912671 _45438)). Qed.
Lemma lem3912673 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912674 (_45438 : int) : (term518 _45438) = term175.
Proof. exact (MK_COMB (@lem3912673) (@lem3912672 _45438)). Qed.
Lemma lem3912675 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3912676 (_45438 : int) : (term516 _45438) = term519.
Proof. exact (MK_COMB (@lem3912674 _45438) (@lem3912675)). Qed.
Lemma lem3912677 (_45438 : int) : (term612 _45438) = term519.
Proof. exact (TRANS (@lem3912566 _45438) (@lem3912676 _45438)). Qed.
Lemma lem3912678 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3912679 (_45438 : int) : (term612 _45438) = term199.
Proof. exact (TRANS (@lem3912677 _45438) (@lem3912678)). Qed.
Lemma lem3912680 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3912681 (_45438 : int) : (term613 _45438) = term521.
Proof. exact (MK_COMB (@lem3912680) (@lem3912679 _45438)). Qed.
Lemma lem3912682 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912683 (_45438 : int) : (term611 _45438) = term522.
Proof. exact (MK_COMB (@lem3912681 _45438) (@lem3912682)). Qed.
Lemma lem3912684 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3912683 _45438) (@lem3912565 _45438 _45439 h1)). Qed.
Lemma lem3912686 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3912687 : term522 = term523.
Proof. exact (@lem3912686 term133 term199). Qed.
Lemma lem3912689 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3912690 : term199 = term200.
Proof. exact (@lem3912689 term11). Qed.
Lemma lem3912692 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912693 : term133 = term196.
Proof. exact (@lem3912692 (NUMERAL 0)). Qed.
Lemma lem3912694 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3912695 : term135 = term524.
Proof. exact (MK_COMB (@lem3912694) (@lem3912693)). Qed.
Lemma lem3912696 : term523 = term525.
Proof. exact (MK_COMB (@lem3912695) (@lem3912690)). Qed.
Lemma lem3912697 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3912699 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912700 : term251 = term252.
Proof. exact (@lem3912699 (NUMERAL 0) term11). Qed.
Lemma lem3912701 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912702 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912703 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912702 h1) (fun h1 : term252 = True => @lem3912701)). Qed.
Lemma lem3912704 : term252 = True.
Proof. exact (EQ_MP (@lem3912703) (@lem3912701)). Qed.
Lemma lem3912705 : term251 = True.
Proof. exact (TRANS (@lem3912700) (@lem3912704)). Qed.
Lemma lem3912706 : True = term251.
Proof. exact (SYM (@lem3912705)). Qed.
Lemma lem3912707 : term251.
Proof. exact (EQ_MP (@lem3912706) (@lem0)). Qed.
Lemma lem3912708 : term527.
Proof. exact (@lem3912697 (@lem3912707)). Qed.
Lemma lem3912710 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912711 : term251 = term252.
Proof. exact (@lem3912710 (NUMERAL 0) term11). Qed.
Lemma lem3912712 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912713 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912714 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912713 h1) (fun h1 : term252 = True => @lem3912712)). Qed.
Lemma lem3912715 : term252 = True.
Proof. exact (EQ_MP (@lem3912714) (@lem3912712)). Qed.
Lemma lem3912716 : term251 = True.
Proof. exact (TRANS (@lem3912711) (@lem3912715)). Qed.
Lemma lem3912717 : True = term251.
Proof. exact (SYM (@lem3912716)). Qed.
Lemma lem3912718 : term251.
Proof. exact (EQ_MP (@lem3912717) (@lem0)). Qed.
Lemma lem3912719 : term525 = term528.
Proof. exact (@lem3912708 (@lem3912718)). Qed.
Lemma lem3912721 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3912722 : term225 = term230.
Proof. exact (@lem3912721 term11 term11). Qed.
Lemma lem3912723 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912724 : term211 = term11.
Proof. exact (EQ_MP (@lem3912723) (@lem940073)). Qed.
Lemma lem3912725 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912726 : term209 = term143.
Proof. exact (MK_COMB (@lem3912725) (@lem3912724)). Qed.
Lemma lem3912727 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3912728 : term230 = term199.
Proof. exact (MK_COMB (@lem3912727) (@lem3912726)). Qed.
Lemma lem3912729 : term225 = term199.
Proof. exact (TRANS (@lem3912722) (@lem3912728)). Qed.
Lemma lem3912731 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912732 : term263 = term133.
Proof. exact (@lem3912731 term11). Qed.
Lemma lem3912733 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3912734 : term529 = term135.
Proof. exact (MK_COMB (@lem3912733) (@lem3912732)). Qed.
Lemma lem3912735 : term528 = term523.
Proof. exact (MK_COMB (@lem3912734) (@lem3912729)). Qed.
Lemma lem3912737 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3912738 : term523 = term532.
Proof. exact (@lem3912737 (NUMERAL 0) term11). Qed.
Lemma lem3912739 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912740 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3912741 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912740 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3912739)). Qed.
Lemma lem3912742 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3912741) (@lem3912739)). Qed.
Lemma lem3912743 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3912744 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3912745 : term533 = (and True).
Proof. exact (MK_COMB (@lem3912744) (@lem3912743)). Qed.
Lemma lem3912746 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3912745) (@lem3912742)). Qed.
Lemma lem3912748 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3912749 : term532 = False.
Proof. exact (TRANS (@lem3912746) (@lem3912748)). Qed.
Lemma lem3912750 : term523 = False.
Proof. exact (TRANS (@lem3912738) (@lem3912749)). Qed.
Lemma lem3912751 : term528 = False.
Proof. exact (TRANS (@lem3912735) (@lem3912750)). Qed.
Lemma lem3912752 : term525 = False.
Proof. exact (TRANS (@lem3912719) (@lem3912751)). Qed.
Lemma lem3912753 : term523 = False.
Proof. exact (TRANS (@lem3912696) (@lem3912752)). Qed.
Lemma lem3912754 : term522 = False.
Proof. exact (TRANS (@lem3912687) (@lem3912753)). Qed.
Lemma lem3912755 (_45438 : int) (_45439 : int) (h1 : term601 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3912754) (@lem3912684 _45438 _45439 h1)). Qed.
Lemma lem3912756 (_45438 : int) (_45439 : int) (h1 : term457 _45438 _45439) : False.
Proof. exact (or_elim (@lem3911741 _45438 _45439 h1) (fun h0 : term576 _45438 _45439 => @lem3912247 _45438 _45439 h0) (fun h0 : term601 _45438 _45439 => @lem3912755 _45438 _45439 h0)). Qed.
Lemma lem3912757 (_45438 : int) (_45439 : int) (h1 : term466 _45438 _45439) : False.
Proof. exact (or_elim (@lem3910558 _45438 _45439 h1) (fun h0 : term461 _45438 _45439 => @lem3911740 _45438 _45439 h0) (fun h0 : term457 _45438 _45439 => @lem3912756 _45438 _45439 h0)). Qed.
Lemma lem3912758 (_45438 : int) (_45439 : int) (h1 : term453 _45438 _45439) : term453 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3912759 (_45438 : int) (_45439 : int) (h1 : term450 _45438 _45439) : term450 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3912760 (_45438 : int) (_45439 : int) (h1 : term445 _45438 _45439) : term445 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3912761 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term614 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3912762 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term446 _45438 _45439.
Proof. exact (proj2 (@lem3912761 _45438 _45439 h1)). Qed.
Lemma lem3912764 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term397 _45438 _45439.
Proof. exact (proj2 (@lem3912762 _45438 _45439 h1)). Qed.
Lemma lem3912766 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term346 _45438 _45439.
Proof. exact (proj2 (@lem3912764 _45438 _45439 h1)). Qed.
Lemma lem3912767 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (proj1 (@lem3912764 _45438 _45439 h1)). Qed.
Lemma lem3912769 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term280 _45438 _45439.
Proof. exact (proj1 (@lem3912766 _45438 _45439 h1)). Qed.
Lemma lem3912771 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3912772 : term471 = term251.
Proof. exact (@lem3912771 term133 term143). Qed.
Lemma lem3912774 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912775 : term143 = term224.
Proof. exact (@lem3912774 term11). Qed.
Lemma lem3912777 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912778 : term133 = term196.
Proof. exact (@lem3912777 (NUMERAL 0)). Qed.
Lemma lem3912779 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3912780 : term472 = term473.
Proof. exact (MK_COMB (@lem3912779) (@lem3912778)). Qed.
Lemma lem3912781 : term251 = term474.
Proof. exact (MK_COMB (@lem3912780) (@lem3912775)). Qed.
Lemma lem3912782 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3912784 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912785 : term251 = term252.
Proof. exact (@lem3912784 (NUMERAL 0) term11). Qed.
Lemma lem3912786 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912787 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912788 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912787 h1) (fun h1 : term252 = True => @lem3912786)). Qed.
Lemma lem3912789 : term252 = True.
Proof. exact (EQ_MP (@lem3912788) (@lem3912786)). Qed.
Lemma lem3912790 : term251 = True.
Proof. exact (TRANS (@lem3912785) (@lem3912789)). Qed.
Lemma lem3912791 : True = term251.
Proof. exact (SYM (@lem3912790)). Qed.
Lemma lem3912792 : term251.
Proof. exact (EQ_MP (@lem3912791) (@lem0)). Qed.
Lemma lem3912793 : term476.
Proof. exact (@lem3912782 (@lem3912792)). Qed.
Lemma lem3912795 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912796 : term251 = term252.
Proof. exact (@lem3912795 (NUMERAL 0) term11). Qed.
Lemma lem3912797 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912798 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912799 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912798 h1) (fun h1 : term252 = True => @lem3912797)). Qed.
Lemma lem3912800 : term252 = True.
Proof. exact (EQ_MP (@lem3912799) (@lem3912797)). Qed.
Lemma lem3912801 : term251 = True.
Proof. exact (TRANS (@lem3912796) (@lem3912800)). Qed.
Lemma lem3912802 : True = term251.
Proof. exact (SYM (@lem3912801)). Qed.
Lemma lem3912803 : term251.
Proof. exact (EQ_MP (@lem3912802) (@lem0)). Qed.
Lemma lem3912804 : term474 = term477.
Proof. exact (@lem3912793 (@lem3912803)). Qed.
Lemma lem3912806 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912807 : term208 = term209.
Proof. exact (@lem3912806 term11 term11). Qed.
Lemma lem3912808 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912809 : term211 = term11.
Proof. exact (EQ_MP (@lem3912808) (@lem940073)). Qed.
Lemma lem3912810 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912811 : term209 = term143.
Proof. exact (MK_COMB (@lem3912810) (@lem3912809)). Qed.
Lemma lem3912812 : term208 = term143.
Proof. exact (TRANS (@lem3912807) (@lem3912811)). Qed.
Lemma lem3912814 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912815 : term263 = term133.
Proof. exact (@lem3912814 term11). Qed.
Lemma lem3912816 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3912817 : term478 = term472.
Proof. exact (MK_COMB (@lem3912816) (@lem3912815)). Qed.
Lemma lem3912818 : term477 = term251.
Proof. exact (MK_COMB (@lem3912817) (@lem3912812)). Qed.
Lemma lem3912820 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912821 : term251 = term252.
Proof. exact (@lem3912820 (NUMERAL 0) term11). Qed.
Lemma lem3912822 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912823 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912824 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912823 h1) (fun h1 : term252 = True => @lem3912822)). Qed.
Lemma lem3912825 : term252 = True.
Proof. exact (EQ_MP (@lem3912824) (@lem3912822)). Qed.
Lemma lem3912826 : term251 = True.
Proof. exact (TRANS (@lem3912821) (@lem3912825)). Qed.
Lemma lem3912827 : term477 = True.
Proof. exact (TRANS (@lem3912818) (@lem3912826)). Qed.
Lemma lem3912828 : term474 = True.
Proof. exact (TRANS (@lem3912804) (@lem3912827)). Qed.
Lemma lem3912829 : term251 = True.
Proof. exact (TRANS (@lem3912781) (@lem3912828)). Qed.
Lemma lem3912830 : term471 = True.
Proof. exact (TRANS (@lem3912772) (@lem3912829)). Qed.
Lemma lem3912831 : True = term471.
Proof. exact (SYM (@lem3912830)). Qed.
Lemma lem3912832 : term471.
Proof. exact (EQ_MP (@lem3912831) (@lem0)). Qed.
Lemma lem3912833 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term479 _45438 _45439.
Proof. exact (conj (@lem3912832) (@lem3912769 _45438 _45439 h1)). Qed.
Lemma lem3912835 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3912836 (_45438 : int) (_45439 : int) : term481 _45438 _45439.
Proof. exact (@lem3912835 term143 (term277 _45438 _45439)). Qed.
Lemma lem3912837 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term482 _45438 _45439.
Proof. exact (@lem3912836 _45438 _45439 (@lem3912833 _45438 _45439 h1)). Qed.
Lemma lem3912838 (_45438 : int) (_45439 : int) : (term483 _45438 _45439) = (term277 _45438 _45439).
Proof. exact (@lem1982733 (term277 _45438 _45439)). Qed.
Lemma lem3912839 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3912840 (_45438 : int) (_45439 : int) : (term484 _45438 _45439) = (term279 _45438 _45439).
Proof. exact (MK_COMB (@lem3912839) (@lem3912838 _45438 _45439)). Qed.
Lemma lem3912841 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912842 (_45438 : int) (_45439 : int) : (term482 _45438 _45439) = (term280 _45438 _45439).
Proof. exact (MK_COMB (@lem3912840 _45438 _45439) (@lem3912841)). Qed.
Lemma lem3912843 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term280 _45438 _45439.
Proof. exact (EQ_MP (@lem3912842 _45438 _45439) (@lem3912837 _45438 _45439 h1)). Qed.
Lemma lem3912845 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3912846 (_45438 : int) (_45439 : int) : term486 _45438 _45439.
Proof. exact (@lem3912845 (term236 _45438 _45439)). Qed.
Lemma lem3912847 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term487 _45438 _45439.
Proof. exact (@lem3912846 _45438 _45439 (@lem3912767 _45438 _45439 h1)). Qed.
Lemma lem3912848 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term488 _45438 _45439.
Proof. exact (@lem3912847 _45438 _45439 h1 term143). Qed.
Lemma lem3912849 (_45438 : int) (_45439 : int) : (term488 _45438 _45439) = ((term489 _45438 _45439) = term133).
Proof. exact (eq_refl (term488 _45438 _45439)). Qed.
Lemma lem3912850 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : (term489 _45438 _45439) = term133.
Proof. exact (EQ_MP (@lem3912849 _45438 _45439) (@lem3912848 _45438 _45439 h1)). Qed.
Lemma lem3912851 (_45438 : int) (_45439 : int) : (term489 _45438 _45439) = (term236 _45438 _45439).
Proof. exact (@lem1982733 (term236 _45438 _45439)). Qed.
Lemma lem3912852 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3912853 (_45438 : int) (_45439 : int) : (term490 _45438 _45439) = (term239 _45438 _45439).
Proof. exact (MK_COMB (@lem3912852) (@lem3912851 _45438 _45439)). Qed.
Lemma lem3912854 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3912855 (_45438 : int) (_45439 : int) : ((term489 _45438 _45439) = term133) = ((term236 _45438 _45439) = term133).
Proof. exact (MK_COMB (@lem3912853 _45438 _45439) (@lem3912854)). Qed.
Lemma lem3912856 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (EQ_MP (@lem3912855 _45438 _45439) (@lem3912850 _45438 _45439 h1)). Qed.
Lemma lem3912857 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term491 _45438 _45439.
Proof. exact (conj (@lem3912856 _45438 _45439 h1) (@lem3912843 _45438 _45439 h1)). Qed.
Lemma lem3912859 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3912860 (_45438 : int) (_45439 : int) : term493 _45438 _45439.
Proof. exact (@lem3912859 (term236 _45438 _45439) (term277 _45438 _45439)). Qed.
Lemma lem3912861 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term494 _45438 _45439.
Proof. exact (@lem3912860 _45438 _45439 (@lem3912857 _45438 _45439 h1)). Qed.
Lemma lem3912862 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = (term496 _45438 _45439).
Proof. exact (@lem1982753 (term237 _45438) (real_of_int _45438) (term299 _45439) (term237 _45439)). Qed.
Lemma lem3912863 (_45438 : int) : (term497 _45438) = (term498 _45438).
Proof. exact (@lem1982713 term199 (real_of_int _45438)). Qed.
Lemma lem3912865 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912866 : term143 = term224.
Proof. exact (@lem3912865 term11). Qed.
Lemma lem3912868 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3912869 : term199 = term200.
Proof. exact (@lem3912868 term11). Qed.
Lemma lem3912870 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912871 : term499 = term500.
Proof. exact (MK_COMB (@lem3912870) (@lem3912869)). Qed.
Lemma lem3912872 : term501 = term502.
Proof. exact (MK_COMB (@lem3912871) (@lem3912866)). Qed.
Lemma lem3912873 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3912875 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912876 : term251 = term252.
Proof. exact (@lem3912875 (NUMERAL 0) term11). Qed.
Lemma lem3912877 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912878 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912879 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912878 h1) (fun h1 : term252 = True => @lem3912877)). Qed.
Lemma lem3912880 : term252 = True.
Proof. exact (EQ_MP (@lem3912879) (@lem3912877)). Qed.
Lemma lem3912881 : term251 = True.
Proof. exact (TRANS (@lem3912876) (@lem3912880)). Qed.
Lemma lem3912882 : True = term251.
Proof. exact (SYM (@lem3912881)). Qed.
Lemma lem3912883 : term251.
Proof. exact (EQ_MP (@lem3912882) (@lem0)). Qed.
Lemma lem3912884 : term504.
Proof. exact (@lem3912873 (@lem3912883)). Qed.
Lemma lem3912886 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912887 : term251 = term252.
Proof. exact (@lem3912886 (NUMERAL 0) term11). Qed.
Lemma lem3912888 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912889 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912890 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912889 h1) (fun h1 : term252 = True => @lem3912888)). Qed.
Lemma lem3912891 : term252 = True.
Proof. exact (EQ_MP (@lem3912890) (@lem3912888)). Qed.
Lemma lem3912892 : term251 = True.
Proof. exact (TRANS (@lem3912887) (@lem3912891)). Qed.
Lemma lem3912893 : True = term251.
Proof. exact (SYM (@lem3912892)). Qed.
Lemma lem3912894 : term251.
Proof. exact (EQ_MP (@lem3912893) (@lem0)). Qed.
Lemma lem3912895 : term505.
Proof. exact (@lem3912884 (@lem3912894)). Qed.
Lemma lem3912897 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912898 : term251 = term252.
Proof. exact (@lem3912897 (NUMERAL 0) term11). Qed.
Lemma lem3912899 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912900 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912901 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912900 h1) (fun h1 : term252 = True => @lem3912899)). Qed.
Lemma lem3912902 : term252 = True.
Proof. exact (EQ_MP (@lem3912901) (@lem3912899)). Qed.
Lemma lem3912903 : term251 = True.
Proof. exact (TRANS (@lem3912898) (@lem3912902)). Qed.
Lemma lem3912904 : True = term251.
Proof. exact (SYM (@lem3912903)). Qed.
Lemma lem3912905 : term251.
Proof. exact (EQ_MP (@lem3912904) (@lem0)). Qed.
Lemma lem3912906 : term506.
Proof. exact (@lem3912895 (@lem3912905)). Qed.
Lemma lem3912908 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912909 : term208 = term209.
Proof. exact (@lem3912908 term11 term11). Qed.
Lemma lem3912910 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912911 : term211 = term11.
Proof. exact (EQ_MP (@lem3912910) (@lem940073)). Qed.
Lemma lem3912912 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912913 : term209 = term143.
Proof. exact (MK_COMB (@lem3912912) (@lem3912911)). Qed.
Lemma lem3912914 : term208 = term143.
Proof. exact (TRANS (@lem3912909) (@lem3912913)). Qed.
Lemma lem3912916 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3912917 : term225 = term230.
Proof. exact (@lem3912916 term11 term11). Qed.
Lemma lem3912918 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912919 : term211 = term11.
Proof. exact (EQ_MP (@lem3912918) (@lem940073)). Qed.
Lemma lem3912920 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912921 : term209 = term143.
Proof. exact (MK_COMB (@lem3912920) (@lem3912919)). Qed.
Lemma lem3912922 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3912923 : term230 = term199.
Proof. exact (MK_COMB (@lem3912922) (@lem3912921)). Qed.
Lemma lem3912924 : term225 = term199.
Proof. exact (TRANS (@lem3912917) (@lem3912923)). Qed.
Lemma lem3912925 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912926 : term507 = term499.
Proof. exact (MK_COMB (@lem3912925) (@lem3912924)). Qed.
Lemma lem3912927 : term508 = term501.
Proof. exact (MK_COMB (@lem3912926) (@lem3912914)). Qed.
Lemma lem3912929 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3912930 : term501 = term133.
Proof. exact (@lem3912929 term11). Qed.
Lemma lem3912931 : term508 = term133.
Proof. exact (TRANS (@lem3912927) (@lem3912930)). Qed.
Lemma lem3912932 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912933 : term510 = term261.
Proof. exact (MK_COMB (@lem3912932) (@lem3912931)). Qed.
Lemma lem3912934 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3912935 : term511 = term263.
Proof. exact (MK_COMB (@lem3912933) (@lem3912934)). Qed.
Lemma lem3912937 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912938 : term263 = term133.
Proof. exact (@lem3912937 term11). Qed.
Lemma lem3912939 : term511 = term133.
Proof. exact (TRANS (@lem3912935) (@lem3912938)). Qed.
Lemma lem3912941 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3912942 : term208 = term209.
Proof. exact (@lem3912941 term11 term11). Qed.
Lemma lem3912943 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3912944 : term211 = term11.
Proof. exact (EQ_MP (@lem3912943) (@lem940073)). Qed.
Lemma lem3912945 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3912946 : term209 = term143.
Proof. exact (MK_COMB (@lem3912945) (@lem3912944)). Qed.
Lemma lem3912947 : term208 = term143.
Proof. exact (TRANS (@lem3912942) (@lem3912946)). Qed.
Lemma lem3912948 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3912949 : term265 = term263.
Proof. exact (MK_COMB (@lem3912948) (@lem3912947)). Qed.
Lemma lem3912951 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3912952 : term263 = term133.
Proof. exact (@lem3912951 term11). Qed.
Lemma lem3912953 : term265 = term133.
Proof. exact (TRANS (@lem3912949) (@lem3912952)). Qed.
Lemma lem3912954 : term133 = term265.
Proof. exact (SYM (@lem3912953)). Qed.
Lemma lem3912955 : term511 = term265.
Proof. exact (TRANS (@lem3912939) (@lem3912954)). Qed.
Lemma lem3912956 : term502 = term196.
Proof. exact (@lem3912906 (@lem3912955)). Qed.
Lemma lem3912957 : term501 = term196.
Proof. exact (TRANS (@lem3912872) (@lem3912956)). Qed.
Lemma lem3912959 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3912960 : term196 = term133.
Proof. exact (@lem3912959 term133). Qed.
Lemma lem3912961 : term501 = term133.
Proof. exact (TRANS (@lem3912957) (@lem3912960)). Qed.
Lemma lem3912962 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3912963 : term512 = term261.
Proof. exact (MK_COMB (@lem3912962) (@lem3912961)). Qed.
Lemma lem3912964 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3912965 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3912963) (@lem3912964 _45438)). Qed.
Lemma lem3912966 (_45438 : int) : (term497 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3912863 _45438) (@lem3912965 _45438)). Qed.
Lemma lem3912967 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3912968 (_45438 : int) : (term497 _45438) = term133.
Proof. exact (TRANS (@lem3912966 _45438) (@lem3912967 _45438)). Qed.
Lemma lem3912969 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912970 (_45438 : int) : (term514 _45438) = term175.
Proof. exact (MK_COMB (@lem3912969) (@lem3912968 _45438)). Qed.
Lemma lem3912971 (_45439 : int) : (term515 _45439) = (term516 _45439).
Proof. exact (@lem1982759 (real_of_int _45439) (term237 _45439) term199). Qed.
Lemma lem3912972 (_45439 : int) : (term517 _45439) = (term498 _45439).
Proof. exact (@lem1982715 term199 (real_of_int _45439)). Qed.
Lemma lem3912974 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3912975 : term143 = term224.
Proof. exact (@lem3912974 term11). Qed.
Lemma lem3912977 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3912978 : term199 = term200.
Proof. exact (@lem3912977 term11). Qed.
Lemma lem3912979 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3912980 : term499 = term500.
Proof. exact (MK_COMB (@lem3912979) (@lem3912978)). Qed.
Lemma lem3912981 : term501 = term502.
Proof. exact (MK_COMB (@lem3912980) (@lem3912975)). Qed.
Lemma lem3912982 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3912984 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912985 : term251 = term252.
Proof. exact (@lem3912984 (NUMERAL 0) term11). Qed.
Lemma lem3912986 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912987 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912988 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912987 h1) (fun h1 : term252 = True => @lem3912986)). Qed.
Lemma lem3912989 : term252 = True.
Proof. exact (EQ_MP (@lem3912988) (@lem3912986)). Qed.
Lemma lem3912990 : term251 = True.
Proof. exact (TRANS (@lem3912985) (@lem3912989)). Qed.
Lemma lem3912991 : True = term251.
Proof. exact (SYM (@lem3912990)). Qed.
Lemma lem3912992 : term251.
Proof. exact (EQ_MP (@lem3912991) (@lem0)). Qed.
Lemma lem3912993 : term504.
Proof. exact (@lem3912982 (@lem3912992)). Qed.
Lemma lem3912995 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3912996 : term251 = term252.
Proof. exact (@lem3912995 (NUMERAL 0) term11). Qed.
Lemma lem3912997 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3912998 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3912999 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3912998 h1) (fun h1 : term252 = True => @lem3912997)). Qed.
Lemma lem3913000 : term252 = True.
Proof. exact (EQ_MP (@lem3912999) (@lem3912997)). Qed.
Lemma lem3913001 : term251 = True.
Proof. exact (TRANS (@lem3912996) (@lem3913000)). Qed.
Lemma lem3913002 : True = term251.
Proof. exact (SYM (@lem3913001)). Qed.
Lemma lem3913003 : term251.
Proof. exact (EQ_MP (@lem3913002) (@lem0)). Qed.
Lemma lem3913004 : term505.
Proof. exact (@lem3912993 (@lem3913003)). Qed.
Lemma lem3913006 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913007 : term251 = term252.
Proof. exact (@lem3913006 (NUMERAL 0) term11). Qed.
Lemma lem3913008 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913009 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913010 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913009 h1) (fun h1 : term252 = True => @lem3913008)). Qed.
Lemma lem3913011 : term252 = True.
Proof. exact (EQ_MP (@lem3913010) (@lem3913008)). Qed.
Lemma lem3913012 : term251 = True.
Proof. exact (TRANS (@lem3913007) (@lem3913011)). Qed.
Lemma lem3913013 : True = term251.
Proof. exact (SYM (@lem3913012)). Qed.
Lemma lem3913014 : term251.
Proof. exact (EQ_MP (@lem3913013) (@lem0)). Qed.
Lemma lem3913015 : term506.
Proof. exact (@lem3913004 (@lem3913014)). Qed.
Lemma lem3913017 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913018 : term208 = term209.
Proof. exact (@lem3913017 term11 term11). Qed.
Lemma lem3913019 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913020 : term211 = term11.
Proof. exact (EQ_MP (@lem3913019) (@lem940073)). Qed.
Lemma lem3913021 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913022 : term209 = term143.
Proof. exact (MK_COMB (@lem3913021) (@lem3913020)). Qed.
Lemma lem3913023 : term208 = term143.
Proof. exact (TRANS (@lem3913018) (@lem3913022)). Qed.
Lemma lem3913025 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3913026 : term225 = term230.
Proof. exact (@lem3913025 term11 term11). Qed.
Lemma lem3913027 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913028 : term211 = term11.
Proof. exact (EQ_MP (@lem3913027) (@lem940073)). Qed.
Lemma lem3913029 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913030 : term209 = term143.
Proof. exact (MK_COMB (@lem3913029) (@lem3913028)). Qed.
Lemma lem3913031 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3913032 : term230 = term199.
Proof. exact (MK_COMB (@lem3913031) (@lem3913030)). Qed.
Lemma lem3913033 : term225 = term199.
Proof. exact (TRANS (@lem3913026) (@lem3913032)). Qed.
Lemma lem3913034 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913035 : term507 = term499.
Proof. exact (MK_COMB (@lem3913034) (@lem3913033)). Qed.
Lemma lem3913036 : term508 = term501.
Proof. exact (MK_COMB (@lem3913035) (@lem3913023)). Qed.
Lemma lem3913038 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3913039 : term501 = term133.
Proof. exact (@lem3913038 term11). Qed.
Lemma lem3913040 : term508 = term133.
Proof. exact (TRANS (@lem3913036) (@lem3913039)). Qed.
Lemma lem3913041 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3913042 : term510 = term261.
Proof. exact (MK_COMB (@lem3913041) (@lem3913040)). Qed.
Lemma lem3913043 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3913044 : term511 = term263.
Proof. exact (MK_COMB (@lem3913042) (@lem3913043)). Qed.
Lemma lem3913046 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913047 : term263 = term133.
Proof. exact (@lem3913046 term11). Qed.
Lemma lem3913048 : term511 = term133.
Proof. exact (TRANS (@lem3913044) (@lem3913047)). Qed.
Lemma lem3913050 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913051 : term208 = term209.
Proof. exact (@lem3913050 term11 term11). Qed.
Lemma lem3913052 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913053 : term211 = term11.
Proof. exact (EQ_MP (@lem3913052) (@lem940073)). Qed.
Lemma lem3913054 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913055 : term209 = term143.
Proof. exact (MK_COMB (@lem3913054) (@lem3913053)). Qed.
Lemma lem3913056 : term208 = term143.
Proof. exact (TRANS (@lem3913051) (@lem3913055)). Qed.
Lemma lem3913057 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3913058 : term265 = term263.
Proof. exact (MK_COMB (@lem3913057) (@lem3913056)). Qed.
Lemma lem3913060 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913061 : term263 = term133.
Proof. exact (@lem3913060 term11). Qed.
Lemma lem3913062 : term265 = term133.
Proof. exact (TRANS (@lem3913058) (@lem3913061)). Qed.
Lemma lem3913063 : term133 = term265.
Proof. exact (SYM (@lem3913062)). Qed.
Lemma lem3913064 : term511 = term265.
Proof. exact (TRANS (@lem3913048) (@lem3913063)). Qed.
Lemma lem3913065 : term502 = term196.
Proof. exact (@lem3913015 (@lem3913064)). Qed.
Lemma lem3913066 : term501 = term196.
Proof. exact (TRANS (@lem3912981) (@lem3913065)). Qed.
Lemma lem3913068 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3913069 : term196 = term133.
Proof. exact (@lem3913068 term133). Qed.
Lemma lem3913070 : term501 = term133.
Proof. exact (TRANS (@lem3913066) (@lem3913069)). Qed.
Lemma lem3913071 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3913072 : term512 = term261.
Proof. exact (MK_COMB (@lem3913071) (@lem3913070)). Qed.
Lemma lem3913073 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3913074 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3913072) (@lem3913073 _45439)). Qed.
Lemma lem3913075 (_45439 : int) : (term517 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3912972 _45439) (@lem3913074 _45439)). Qed.
Lemma lem3913076 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3913077 (_45439 : int) : (term517 _45439) = term133.
Proof. exact (TRANS (@lem3913075 _45439) (@lem3913076 _45439)). Qed.
Lemma lem3913078 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913079 (_45439 : int) : (term518 _45439) = term175.
Proof. exact (MK_COMB (@lem3913078) (@lem3913077 _45439)). Qed.
Lemma lem3913080 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3913081 (_45439 : int) : (term516 _45439) = term519.
Proof. exact (MK_COMB (@lem3913079 _45439) (@lem3913080)). Qed.
Lemma lem3913082 (_45439 : int) : (term515 _45439) = term519.
Proof. exact (TRANS (@lem3912971 _45439) (@lem3913081 _45439)). Qed.
Lemma lem3913083 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3913084 (_45439 : int) : (term515 _45439) = term199.
Proof. exact (TRANS (@lem3913082 _45439) (@lem3913083)). Qed.
Lemma lem3913085 (_45438 : int) (_45439 : int) : (term496 _45438 _45439) = term519.
Proof. exact (MK_COMB (@lem3912970 _45438) (@lem3913084 _45439)). Qed.
Lemma lem3913086 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = term519.
Proof. exact (TRANS (@lem3912862 _45438 _45439) (@lem3913085 _45438 _45439)). Qed.
Lemma lem3913087 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3913088 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = term199.
Proof. exact (TRANS (@lem3913086 _45438 _45439) (@lem3913087)). Qed.
Lemma lem3913089 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3913090 (_45438 : int) (_45439 : int) : (term520 _45438 _45439) = term521.
Proof. exact (MK_COMB (@lem3913089) (@lem3913088 _45438 _45439)). Qed.
Lemma lem3913091 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913092 (_45438 : int) (_45439 : int) : (term494 _45438 _45439) = term522.
Proof. exact (MK_COMB (@lem3913090 _45438 _45439) (@lem3913091)). Qed.
Lemma lem3913093 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3913092 _45438 _45439) (@lem3912861 _45438 _45439 h1)). Qed.
Lemma lem3913095 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3913096 : term522 = term523.
Proof. exact (@lem3913095 term133 term199). Qed.
Lemma lem3913098 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3913099 : term199 = term200.
Proof. exact (@lem3913098 term11). Qed.
Lemma lem3913101 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913102 : term133 = term196.
Proof. exact (@lem3913101 (NUMERAL 0)). Qed.
Lemma lem3913103 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3913104 : term135 = term524.
Proof. exact (MK_COMB (@lem3913103) (@lem3913102)). Qed.
Lemma lem3913105 : term523 = term525.
Proof. exact (MK_COMB (@lem3913104) (@lem3913099)). Qed.
Lemma lem3913106 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3913108 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913109 : term251 = term252.
Proof. exact (@lem3913108 (NUMERAL 0) term11). Qed.
Lemma lem3913110 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913111 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913112 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913111 h1) (fun h1 : term252 = True => @lem3913110)). Qed.
Lemma lem3913113 : term252 = True.
Proof. exact (EQ_MP (@lem3913112) (@lem3913110)). Qed.
Lemma lem3913114 : term251 = True.
Proof. exact (TRANS (@lem3913109) (@lem3913113)). Qed.
Lemma lem3913115 : True = term251.
Proof. exact (SYM (@lem3913114)). Qed.
Lemma lem3913116 : term251.
Proof. exact (EQ_MP (@lem3913115) (@lem0)). Qed.
Lemma lem3913117 : term527.
Proof. exact (@lem3913106 (@lem3913116)). Qed.
Lemma lem3913119 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913120 : term251 = term252.
Proof. exact (@lem3913119 (NUMERAL 0) term11). Qed.
Lemma lem3913121 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913122 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913123 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913122 h1) (fun h1 : term252 = True => @lem3913121)). Qed.
Lemma lem3913124 : term252 = True.
Proof. exact (EQ_MP (@lem3913123) (@lem3913121)). Qed.
Lemma lem3913125 : term251 = True.
Proof. exact (TRANS (@lem3913120) (@lem3913124)). Qed.
Lemma lem3913126 : True = term251.
Proof. exact (SYM (@lem3913125)). Qed.
Lemma lem3913127 : term251.
Proof. exact (EQ_MP (@lem3913126) (@lem0)). Qed.
Lemma lem3913128 : term525 = term528.
Proof. exact (@lem3913117 (@lem3913127)). Qed.
Lemma lem3913130 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3913131 : term225 = term230.
Proof. exact (@lem3913130 term11 term11). Qed.
Lemma lem3913132 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913133 : term211 = term11.
Proof. exact (EQ_MP (@lem3913132) (@lem940073)). Qed.
Lemma lem3913134 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913135 : term209 = term143.
Proof. exact (MK_COMB (@lem3913134) (@lem3913133)). Qed.
Lemma lem3913136 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3913137 : term230 = term199.
Proof. exact (MK_COMB (@lem3913136) (@lem3913135)). Qed.
Lemma lem3913138 : term225 = term199.
Proof. exact (TRANS (@lem3913131) (@lem3913137)). Qed.
Lemma lem3913140 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913141 : term263 = term133.
Proof. exact (@lem3913140 term11). Qed.
Lemma lem3913142 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3913143 : term529 = term135.
Proof. exact (MK_COMB (@lem3913142) (@lem3913141)). Qed.
Lemma lem3913144 : term528 = term523.
Proof. exact (MK_COMB (@lem3913143) (@lem3913138)). Qed.
Lemma lem3913146 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3913147 : term523 = term532.
Proof. exact (@lem3913146 (NUMERAL 0) term11). Qed.
Lemma lem3913148 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913149 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3913150 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913149 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3913148)). Qed.
Lemma lem3913151 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3913150) (@lem3913148)). Qed.
Lemma lem3913152 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3913153 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3913154 : term533 = (and True).
Proof. exact (MK_COMB (@lem3913153) (@lem3913152)). Qed.
Lemma lem3913155 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3913154) (@lem3913151)). Qed.
Lemma lem3913157 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3913158 : term532 = False.
Proof. exact (TRANS (@lem3913155) (@lem3913157)). Qed.
Lemma lem3913159 : term523 = False.
Proof. exact (TRANS (@lem3913147) (@lem3913158)). Qed.
Lemma lem3913160 : term528 = False.
Proof. exact (TRANS (@lem3913144) (@lem3913159)). Qed.
Lemma lem3913161 : term525 = False.
Proof. exact (TRANS (@lem3913128) (@lem3913160)). Qed.
Lemma lem3913162 : term523 = False.
Proof. exact (TRANS (@lem3913105) (@lem3913161)). Qed.
Lemma lem3913163 : term522 = False.
Proof. exact (TRANS (@lem3913096) (@lem3913162)). Qed.
Lemma lem3913164 (_45438 : int) (_45439 : int) (h1 : term614 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3913163) (@lem3913093 _45438 _45439 h1)). Qed.
Lemma lem3913165 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term615 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3913166 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term447 _45438 _45439.
Proof. exact (proj2 (@lem3913165 _45438 _45439 h1)). Qed.
Lemma lem3913168 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term398 _45438 _45439.
Proof. exact (proj2 (@lem3913166 _45438 _45439 h1)). Qed.
Lemma lem3913169 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term219 _45439.
Proof. exact (proj1 (@lem3913166 _45438 _45439 h1)). Qed.
Lemma lem3913170 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term346 _45438 _45439.
Proof. exact (proj2 (@lem3913168 _45438 _45439 h1)). Qed.
Lemma lem3913174 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term293 _45439.
Proof. exact (proj2 (@lem3913170 _45438 _45439 h1)). Qed.
Lemma lem3913177 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3913178 : term471 = term251.
Proof. exact (@lem3913177 term133 term143). Qed.
Lemma lem3913180 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913181 : term143 = term224.
Proof. exact (@lem3913180 term11). Qed.
Lemma lem3913183 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913184 : term133 = term196.
Proof. exact (@lem3913183 (NUMERAL 0)). Qed.
Lemma lem3913185 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913186 : term472 = term473.
Proof. exact (MK_COMB (@lem3913185) (@lem3913184)). Qed.
Lemma lem3913187 : term251 = term474.
Proof. exact (MK_COMB (@lem3913186) (@lem3913181)). Qed.
Lemma lem3913188 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3913190 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913191 : term251 = term252.
Proof. exact (@lem3913190 (NUMERAL 0) term11). Qed.
Lemma lem3913192 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913193 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913194 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913193 h1) (fun h1 : term252 = True => @lem3913192)). Qed.
Lemma lem3913195 : term252 = True.
Proof. exact (EQ_MP (@lem3913194) (@lem3913192)). Qed.
Lemma lem3913196 : term251 = True.
Proof. exact (TRANS (@lem3913191) (@lem3913195)). Qed.
Lemma lem3913197 : True = term251.
Proof. exact (SYM (@lem3913196)). Qed.
Lemma lem3913198 : term251.
Proof. exact (EQ_MP (@lem3913197) (@lem0)). Qed.
Lemma lem3913199 : term476.
Proof. exact (@lem3913188 (@lem3913198)). Qed.
Lemma lem3913201 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913202 : term251 = term252.
Proof. exact (@lem3913201 (NUMERAL 0) term11). Qed.
Lemma lem3913203 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913204 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913205 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913204 h1) (fun h1 : term252 = True => @lem3913203)). Qed.
Lemma lem3913206 : term252 = True.
Proof. exact (EQ_MP (@lem3913205) (@lem3913203)). Qed.
Lemma lem3913207 : term251 = True.
Proof. exact (TRANS (@lem3913202) (@lem3913206)). Qed.
Lemma lem3913208 : True = term251.
Proof. exact (SYM (@lem3913207)). Qed.
Lemma lem3913209 : term251.
Proof. exact (EQ_MP (@lem3913208) (@lem0)). Qed.
Lemma lem3913210 : term474 = term477.
Proof. exact (@lem3913199 (@lem3913209)). Qed.
Lemma lem3913212 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913213 : term208 = term209.
Proof. exact (@lem3913212 term11 term11). Qed.
Lemma lem3913214 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913215 : term211 = term11.
Proof. exact (EQ_MP (@lem3913214) (@lem940073)). Qed.
Lemma lem3913216 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913217 : term209 = term143.
Proof. exact (MK_COMB (@lem3913216) (@lem3913215)). Qed.
Lemma lem3913218 : term208 = term143.
Proof. exact (TRANS (@lem3913213) (@lem3913217)). Qed.
Lemma lem3913220 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913221 : term263 = term133.
Proof. exact (@lem3913220 term11). Qed.
Lemma lem3913222 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913223 : term478 = term472.
Proof. exact (MK_COMB (@lem3913222) (@lem3913221)). Qed.
Lemma lem3913224 : term477 = term251.
Proof. exact (MK_COMB (@lem3913223) (@lem3913218)). Qed.
Lemma lem3913226 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913227 : term251 = term252.
Proof. exact (@lem3913226 (NUMERAL 0) term11). Qed.
Lemma lem3913228 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913229 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913230 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913229 h1) (fun h1 : term252 = True => @lem3913228)). Qed.
Lemma lem3913231 : term252 = True.
Proof. exact (EQ_MP (@lem3913230) (@lem3913228)). Qed.
Lemma lem3913232 : term251 = True.
Proof. exact (TRANS (@lem3913227) (@lem3913231)). Qed.
Lemma lem3913233 : term477 = True.
Proof. exact (TRANS (@lem3913224) (@lem3913232)). Qed.
Lemma lem3913234 : term474 = True.
Proof. exact (TRANS (@lem3913210) (@lem3913233)). Qed.
Lemma lem3913235 : term251 = True.
Proof. exact (TRANS (@lem3913187) (@lem3913234)). Qed.
Lemma lem3913236 : term471 = True.
Proof. exact (TRANS (@lem3913178) (@lem3913235)). Qed.
Lemma lem3913237 : True = term471.
Proof. exact (SYM (@lem3913236)). Qed.
Lemma lem3913238 : term471.
Proof. exact (EQ_MP (@lem3913237) (@lem0)). Qed.
Lemma lem3913239 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term577 _45439.
Proof. exact (conj (@lem3913238) (@lem3913169 _45438 _45439 h1)). Qed.
Lemma lem3913241 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3913242 (_45439 : int) : term578 _45439.
Proof. exact (@lem3913241 term143 (real_of_int _45439)). Qed.
Lemma lem3913243 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term579 _45439.
Proof. exact (@lem3913242 _45439 (@lem3913239 _45438 _45439 h1)). Qed.
Lemma lem3913244 (_45439 : int) : (term542 _45439) = (real_of_int _45439).
Proof. exact (@lem1982733 (real_of_int _45439)). Qed.
Lemma lem3913245 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3913246 (_45439 : int) : (term580 _45439) = (term218 _45439).
Proof. exact (MK_COMB (@lem3913245) (@lem3913244 _45439)). Qed.
Lemma lem3913247 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913248 (_45439 : int) : (term579 _45439) = (term219 _45439).
Proof. exact (MK_COMB (@lem3913246 _45439) (@lem3913247)). Qed.
Lemma lem3913249 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term219 _45439.
Proof. exact (EQ_MP (@lem3913248 _45439) (@lem3913243 _45438 _45439 h1)). Qed.
Lemma lem3913251 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3913252 : term471 = term251.
Proof. exact (@lem3913251 term133 term143). Qed.
Lemma lem3913254 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913255 : term143 = term224.
Proof. exact (@lem3913254 term11). Qed.
Lemma lem3913257 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913258 : term133 = term196.
Proof. exact (@lem3913257 (NUMERAL 0)). Qed.
Lemma lem3913259 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913260 : term472 = term473.
Proof. exact (MK_COMB (@lem3913259) (@lem3913258)). Qed.
Lemma lem3913261 : term251 = term474.
Proof. exact (MK_COMB (@lem3913260) (@lem3913255)). Qed.
Lemma lem3913262 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3913264 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913265 : term251 = term252.
Proof. exact (@lem3913264 (NUMERAL 0) term11). Qed.
Lemma lem3913266 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913267 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913268 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913267 h1) (fun h1 : term252 = True => @lem3913266)). Qed.
Lemma lem3913269 : term252 = True.
Proof. exact (EQ_MP (@lem3913268) (@lem3913266)). Qed.
Lemma lem3913270 : term251 = True.
Proof. exact (TRANS (@lem3913265) (@lem3913269)). Qed.
Lemma lem3913271 : True = term251.
Proof. exact (SYM (@lem3913270)). Qed.
Lemma lem3913272 : term251.
Proof. exact (EQ_MP (@lem3913271) (@lem0)). Qed.
Lemma lem3913273 : term476.
Proof. exact (@lem3913262 (@lem3913272)). Qed.
Lemma lem3913275 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913276 : term251 = term252.
Proof. exact (@lem3913275 (NUMERAL 0) term11). Qed.
Lemma lem3913277 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913278 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913279 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913278 h1) (fun h1 : term252 = True => @lem3913277)). Qed.
Lemma lem3913280 : term252 = True.
Proof. exact (EQ_MP (@lem3913279) (@lem3913277)). Qed.
Lemma lem3913281 : term251 = True.
Proof. exact (TRANS (@lem3913276) (@lem3913280)). Qed.
Lemma lem3913282 : True = term251.
Proof. exact (SYM (@lem3913281)). Qed.
Lemma lem3913283 : term251.
Proof. exact (EQ_MP (@lem3913282) (@lem0)). Qed.
Lemma lem3913284 : term474 = term477.
Proof. exact (@lem3913273 (@lem3913283)). Qed.
Lemma lem3913286 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913287 : term208 = term209.
Proof. exact (@lem3913286 term11 term11). Qed.
Lemma lem3913288 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913289 : term211 = term11.
Proof. exact (EQ_MP (@lem3913288) (@lem940073)). Qed.
Lemma lem3913290 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913291 : term209 = term143.
Proof. exact (MK_COMB (@lem3913290) (@lem3913289)). Qed.
Lemma lem3913292 : term208 = term143.
Proof. exact (TRANS (@lem3913287) (@lem3913291)). Qed.
Lemma lem3913294 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913295 : term263 = term133.
Proof. exact (@lem3913294 term11). Qed.
Lemma lem3913296 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913297 : term478 = term472.
Proof. exact (MK_COMB (@lem3913296) (@lem3913295)). Qed.
Lemma lem3913298 : term477 = term251.
Proof. exact (MK_COMB (@lem3913297) (@lem3913292)). Qed.
Lemma lem3913300 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913301 : term251 = term252.
Proof. exact (@lem3913300 (NUMERAL 0) term11). Qed.
Lemma lem3913302 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913303 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913304 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913303 h1) (fun h1 : term252 = True => @lem3913302)). Qed.
Lemma lem3913305 : term252 = True.
Proof. exact (EQ_MP (@lem3913304) (@lem3913302)). Qed.
Lemma lem3913306 : term251 = True.
Proof. exact (TRANS (@lem3913301) (@lem3913305)). Qed.
Lemma lem3913307 : term477 = True.
Proof. exact (TRANS (@lem3913298) (@lem3913306)). Qed.
Lemma lem3913308 : term474 = True.
Proof. exact (TRANS (@lem3913284) (@lem3913307)). Qed.
Lemma lem3913309 : term251 = True.
Proof. exact (TRANS (@lem3913261) (@lem3913308)). Qed.
Lemma lem3913310 : term471 = True.
Proof. exact (TRANS (@lem3913252) (@lem3913309)). Qed.
Lemma lem3913311 : True = term471.
Proof. exact (SYM (@lem3913310)). Qed.
Lemma lem3913312 : term471.
Proof. exact (EQ_MP (@lem3913311) (@lem0)). Qed.
Lemma lem3913313 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term606 _45439.
Proof. exact (conj (@lem3913312) (@lem3913174 _45438 _45439 h1)). Qed.
Lemma lem3913315 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3913316 (_45439 : int) : term607 _45439.
Proof. exact (@lem3913315 term143 (term234 _45439)). Qed.
Lemma lem3913317 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term608 _45439.
Proof. exact (@lem3913316 _45439 (@lem3913313 _45438 _45439 h1)). Qed.
Lemma lem3913318 (_45439 : int) : (term594 _45439) = (term234 _45439).
Proof. exact (@lem1982733 (term234 _45439)). Qed.
Lemma lem3913319 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3913320 (_45439 : int) : (term609 _45439) = (term292 _45439).
Proof. exact (MK_COMB (@lem3913319) (@lem3913318 _45439)). Qed.
Lemma lem3913321 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913322 (_45439 : int) : (term608 _45439) = (term293 _45439).
Proof. exact (MK_COMB (@lem3913320 _45439) (@lem3913321)). Qed.
Lemma lem3913323 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term293 _45439.
Proof. exact (EQ_MP (@lem3913322 _45439) (@lem3913317 _45438 _45439 h1)). Qed.
Lemma lem3913324 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term616 _45439.
Proof. exact (conj (@lem3913323 _45438 _45439 h1) (@lem3913249 _45438 _45439 h1)). Qed.
Lemma lem3913326 (x : real) (y : real) : term570 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3913327 (_45439 : int) : term617 _45439.
Proof. exact (@lem3913326 (term234 _45439) (real_of_int _45439)). Qed.
Lemma lem3913328 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term598 _45439.
Proof. exact (@lem3913327 _45439 (@lem3913324 _45438 _45439 h1)). Qed.
Lemma lem3913329 (_45439 : int) : (term599 _45439) = (term574 _45439).
Proof. exact (@lem1982759 (term237 _45439) (real_of_int _45439) term199). Qed.
Lemma lem3913330 (_45439 : int) : (term497 _45439) = (term498 _45439).
Proof. exact (@lem1982713 term199 (real_of_int _45439)). Qed.
Lemma lem3913332 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913333 : term143 = term224.
Proof. exact (@lem3913332 term11). Qed.
Lemma lem3913335 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3913336 : term199 = term200.
Proof. exact (@lem3913335 term11). Qed.
Lemma lem3913337 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913338 : term499 = term500.
Proof. exact (MK_COMB (@lem3913337) (@lem3913336)). Qed.
Lemma lem3913339 : term501 = term502.
Proof. exact (MK_COMB (@lem3913338) (@lem3913333)). Qed.
Lemma lem3913340 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3913342 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913343 : term251 = term252.
Proof. exact (@lem3913342 (NUMERAL 0) term11). Qed.
Lemma lem3913344 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913345 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913346 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913345 h1) (fun h1 : term252 = True => @lem3913344)). Qed.
Lemma lem3913347 : term252 = True.
Proof. exact (EQ_MP (@lem3913346) (@lem3913344)). Qed.
Lemma lem3913348 : term251 = True.
Proof. exact (TRANS (@lem3913343) (@lem3913347)). Qed.
Lemma lem3913349 : True = term251.
Proof. exact (SYM (@lem3913348)). Qed.
Lemma lem3913350 : term251.
Proof. exact (EQ_MP (@lem3913349) (@lem0)). Qed.
Lemma lem3913351 : term504.
Proof. exact (@lem3913340 (@lem3913350)). Qed.
Lemma lem3913353 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913354 : term251 = term252.
Proof. exact (@lem3913353 (NUMERAL 0) term11). Qed.
Lemma lem3913355 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913356 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913357 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913356 h1) (fun h1 : term252 = True => @lem3913355)). Qed.
Lemma lem3913358 : term252 = True.
Proof. exact (EQ_MP (@lem3913357) (@lem3913355)). Qed.
Lemma lem3913359 : term251 = True.
Proof. exact (TRANS (@lem3913354) (@lem3913358)). Qed.
Lemma lem3913360 : True = term251.
Proof. exact (SYM (@lem3913359)). Qed.
Lemma lem3913361 : term251.
Proof. exact (EQ_MP (@lem3913360) (@lem0)). Qed.
Lemma lem3913362 : term505.
Proof. exact (@lem3913351 (@lem3913361)). Qed.
Lemma lem3913364 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913365 : term251 = term252.
Proof. exact (@lem3913364 (NUMERAL 0) term11). Qed.
Lemma lem3913366 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913367 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913368 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913367 h1) (fun h1 : term252 = True => @lem3913366)). Qed.
Lemma lem3913369 : term252 = True.
Proof. exact (EQ_MP (@lem3913368) (@lem3913366)). Qed.
Lemma lem3913370 : term251 = True.
Proof. exact (TRANS (@lem3913365) (@lem3913369)). Qed.
Lemma lem3913371 : True = term251.
Proof. exact (SYM (@lem3913370)). Qed.
Lemma lem3913372 : term251.
Proof. exact (EQ_MP (@lem3913371) (@lem0)). Qed.
Lemma lem3913373 : term506.
Proof. exact (@lem3913362 (@lem3913372)). Qed.
Lemma lem3913375 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913376 : term208 = term209.
Proof. exact (@lem3913375 term11 term11). Qed.
Lemma lem3913377 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913378 : term211 = term11.
Proof. exact (EQ_MP (@lem3913377) (@lem940073)). Qed.
Lemma lem3913379 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913380 : term209 = term143.
Proof. exact (MK_COMB (@lem3913379) (@lem3913378)). Qed.
Lemma lem3913381 : term208 = term143.
Proof. exact (TRANS (@lem3913376) (@lem3913380)). Qed.
Lemma lem3913383 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3913384 : term225 = term230.
Proof. exact (@lem3913383 term11 term11). Qed.
Lemma lem3913385 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913386 : term211 = term11.
Proof. exact (EQ_MP (@lem3913385) (@lem940073)). Qed.
Lemma lem3913387 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913388 : term209 = term143.
Proof. exact (MK_COMB (@lem3913387) (@lem3913386)). Qed.
Lemma lem3913389 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3913390 : term230 = term199.
Proof. exact (MK_COMB (@lem3913389) (@lem3913388)). Qed.
Lemma lem3913391 : term225 = term199.
Proof. exact (TRANS (@lem3913384) (@lem3913390)). Qed.
Lemma lem3913392 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913393 : term507 = term499.
Proof. exact (MK_COMB (@lem3913392) (@lem3913391)). Qed.
Lemma lem3913394 : term508 = term501.
Proof. exact (MK_COMB (@lem3913393) (@lem3913381)). Qed.
Lemma lem3913396 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3913397 : term501 = term133.
Proof. exact (@lem3913396 term11). Qed.
Lemma lem3913398 : term508 = term133.
Proof. exact (TRANS (@lem3913394) (@lem3913397)). Qed.
Lemma lem3913399 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3913400 : term510 = term261.
Proof. exact (MK_COMB (@lem3913399) (@lem3913398)). Qed.
Lemma lem3913401 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3913402 : term511 = term263.
Proof. exact (MK_COMB (@lem3913400) (@lem3913401)). Qed.
Lemma lem3913404 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913405 : term263 = term133.
Proof. exact (@lem3913404 term11). Qed.
Lemma lem3913406 : term511 = term133.
Proof. exact (TRANS (@lem3913402) (@lem3913405)). Qed.
Lemma lem3913408 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913409 : term208 = term209.
Proof. exact (@lem3913408 term11 term11). Qed.
Lemma lem3913410 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913411 : term211 = term11.
Proof. exact (EQ_MP (@lem3913410) (@lem940073)). Qed.
Lemma lem3913412 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913413 : term209 = term143.
Proof. exact (MK_COMB (@lem3913412) (@lem3913411)). Qed.
Lemma lem3913414 : term208 = term143.
Proof. exact (TRANS (@lem3913409) (@lem3913413)). Qed.
Lemma lem3913415 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3913416 : term265 = term263.
Proof. exact (MK_COMB (@lem3913415) (@lem3913414)). Qed.
Lemma lem3913418 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913419 : term263 = term133.
Proof. exact (@lem3913418 term11). Qed.
Lemma lem3913420 : term265 = term133.
Proof. exact (TRANS (@lem3913416) (@lem3913419)). Qed.
Lemma lem3913421 : term133 = term265.
Proof. exact (SYM (@lem3913420)). Qed.
Lemma lem3913422 : term511 = term265.
Proof. exact (TRANS (@lem3913406) (@lem3913421)). Qed.
Lemma lem3913423 : term502 = term196.
Proof. exact (@lem3913373 (@lem3913422)). Qed.
Lemma lem3913424 : term501 = term196.
Proof. exact (TRANS (@lem3913339) (@lem3913423)). Qed.
Lemma lem3913426 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3913427 : term196 = term133.
Proof. exact (@lem3913426 term133). Qed.
Lemma lem3913428 : term501 = term133.
Proof. exact (TRANS (@lem3913424) (@lem3913427)). Qed.
Lemma lem3913429 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3913430 : term512 = term261.
Proof. exact (MK_COMB (@lem3913429) (@lem3913428)). Qed.
Lemma lem3913431 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3913432 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3913430) (@lem3913431 _45439)). Qed.
Lemma lem3913433 (_45439 : int) : (term497 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3913330 _45439) (@lem3913432 _45439)). Qed.
Lemma lem3913434 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3913435 (_45439 : int) : (term497 _45439) = term133.
Proof. exact (TRANS (@lem3913433 _45439) (@lem3913434 _45439)). Qed.
Lemma lem3913436 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913437 (_45439 : int) : (term514 _45439) = term175.
Proof. exact (MK_COMB (@lem3913436) (@lem3913435 _45439)). Qed.
Lemma lem3913438 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3913439 (_45439 : int) : (term574 _45439) = term519.
Proof. exact (MK_COMB (@lem3913437 _45439) (@lem3913438)). Qed.
Lemma lem3913440 (_45439 : int) : (term599 _45439) = term519.
Proof. exact (TRANS (@lem3913329 _45439) (@lem3913439 _45439)). Qed.
Lemma lem3913441 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3913442 (_45439 : int) : (term599 _45439) = term199.
Proof. exact (TRANS (@lem3913440 _45439) (@lem3913441)). Qed.
Lemma lem3913443 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3913444 (_45439 : int) : (term600 _45439) = term521.
Proof. exact (MK_COMB (@lem3913443) (@lem3913442 _45439)). Qed.
Lemma lem3913445 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913446 (_45439 : int) : (term598 _45439) = term522.
Proof. exact (MK_COMB (@lem3913444 _45439) (@lem3913445)). Qed.
Lemma lem3913447 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3913446 _45439) (@lem3913328 _45438 _45439 h1)). Qed.
Lemma lem3913449 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3913450 : term522 = term523.
Proof. exact (@lem3913449 term133 term199). Qed.
Lemma lem3913452 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3913453 : term199 = term200.
Proof. exact (@lem3913452 term11). Qed.
Lemma lem3913455 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913456 : term133 = term196.
Proof. exact (@lem3913455 (NUMERAL 0)). Qed.
Lemma lem3913457 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3913458 : term135 = term524.
Proof. exact (MK_COMB (@lem3913457) (@lem3913456)). Qed.
Lemma lem3913459 : term523 = term525.
Proof. exact (MK_COMB (@lem3913458) (@lem3913453)). Qed.
Lemma lem3913460 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3913462 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913463 : term251 = term252.
Proof. exact (@lem3913462 (NUMERAL 0) term11). Qed.
Lemma lem3913464 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913465 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913466 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913465 h1) (fun h1 : term252 = True => @lem3913464)). Qed.
Lemma lem3913467 : term252 = True.
Proof. exact (EQ_MP (@lem3913466) (@lem3913464)). Qed.
Lemma lem3913468 : term251 = True.
Proof. exact (TRANS (@lem3913463) (@lem3913467)). Qed.
Lemma lem3913469 : True = term251.
Proof. exact (SYM (@lem3913468)). Qed.
Lemma lem3913470 : term251.
Proof. exact (EQ_MP (@lem3913469) (@lem0)). Qed.
Lemma lem3913471 : term527.
Proof. exact (@lem3913460 (@lem3913470)). Qed.
Lemma lem3913473 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913474 : term251 = term252.
Proof. exact (@lem3913473 (NUMERAL 0) term11). Qed.
Lemma lem3913475 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913476 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913477 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913476 h1) (fun h1 : term252 = True => @lem3913475)). Qed.
Lemma lem3913478 : term252 = True.
Proof. exact (EQ_MP (@lem3913477) (@lem3913475)). Qed.
Lemma lem3913479 : term251 = True.
Proof. exact (TRANS (@lem3913474) (@lem3913478)). Qed.
Lemma lem3913480 : True = term251.
Proof. exact (SYM (@lem3913479)). Qed.
Lemma lem3913481 : term251.
Proof. exact (EQ_MP (@lem3913480) (@lem0)). Qed.
Lemma lem3913482 : term525 = term528.
Proof. exact (@lem3913471 (@lem3913481)). Qed.
Lemma lem3913484 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3913485 : term225 = term230.
Proof. exact (@lem3913484 term11 term11). Qed.
Lemma lem3913486 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913487 : term211 = term11.
Proof. exact (EQ_MP (@lem3913486) (@lem940073)). Qed.
Lemma lem3913488 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913489 : term209 = term143.
Proof. exact (MK_COMB (@lem3913488) (@lem3913487)). Qed.
Lemma lem3913490 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3913491 : term230 = term199.
Proof. exact (MK_COMB (@lem3913490) (@lem3913489)). Qed.
Lemma lem3913492 : term225 = term199.
Proof. exact (TRANS (@lem3913485) (@lem3913491)). Qed.
Lemma lem3913494 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913495 : term263 = term133.
Proof. exact (@lem3913494 term11). Qed.
Lemma lem3913496 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3913497 : term529 = term135.
Proof. exact (MK_COMB (@lem3913496) (@lem3913495)). Qed.
Lemma lem3913498 : term528 = term523.
Proof. exact (MK_COMB (@lem3913497) (@lem3913492)). Qed.
Lemma lem3913500 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3913501 : term523 = term532.
Proof. exact (@lem3913500 (NUMERAL 0) term11). Qed.
Lemma lem3913502 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913503 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3913504 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913503 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3913502)). Qed.
Lemma lem3913505 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3913504) (@lem3913502)). Qed.
Lemma lem3913506 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3913507 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3913508 : term533 = (and True).
Proof. exact (MK_COMB (@lem3913507) (@lem3913506)). Qed.
Lemma lem3913509 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3913508) (@lem3913505)). Qed.
Lemma lem3913511 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3913512 : term532 = False.
Proof. exact (TRANS (@lem3913509) (@lem3913511)). Qed.
Lemma lem3913513 : term523 = False.
Proof. exact (TRANS (@lem3913501) (@lem3913512)). Qed.
Lemma lem3913514 : term528 = False.
Proof. exact (TRANS (@lem3913498) (@lem3913513)). Qed.
Lemma lem3913515 : term525 = False.
Proof. exact (TRANS (@lem3913482) (@lem3913514)). Qed.
Lemma lem3913516 : term523 = False.
Proof. exact (TRANS (@lem3913459) (@lem3913515)). Qed.
Lemma lem3913517 : term522 = False.
Proof. exact (TRANS (@lem3913450) (@lem3913516)). Qed.
Lemma lem3913518 (_45438 : int) (_45439 : int) (h1 : term615 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3913517) (@lem3913447 _45438 _45439 h1)). Qed.
Lemma lem3913519 (_45438 : int) (_45439 : int) (h1 : term445 _45438 _45439) : False.
Proof. exact (or_elim (@lem3912760 _45438 _45439 h1) (fun h0 : term614 _45438 _45439 => @lem3913164 _45438 _45439 h0) (fun h0 : term615 _45438 _45439 => @lem3913518 _45438 _45439 h0)). Qed.
Lemma lem3913520 (_45438 : int) (_45439 : int) (h1 : term441 _45438 _45439) : term441 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3913521 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term618 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3913522 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term442 _45438 _45439.
Proof. exact (proj2 (@lem3913521 _45438 _45439 h1)). Qed.
Lemma lem3913524 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term393 _45438 _45439.
Proof. exact (proj2 (@lem3913522 _45438 _45439 h1)). Qed.
Lemma lem3913526 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term347 _45439.
Proof. exact (proj2 (@lem3913524 _45438 _45439 h1)). Qed.
Lemma lem3913528 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term293 _45439.
Proof. exact (proj2 (@lem3913526 _45438 _45439 h1)). Qed.
Lemma lem3913529 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (proj1 (@lem3913526 _45438 _45439 h1)). Qed.
Lemma lem3913531 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3913532 : term471 = term251.
Proof. exact (@lem3913531 term133 term143). Qed.
Lemma lem3913534 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913535 : term143 = term224.
Proof. exact (@lem3913534 term11). Qed.
Lemma lem3913537 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913538 : term133 = term196.
Proof. exact (@lem3913537 (NUMERAL 0)). Qed.
Lemma lem3913539 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913540 : term472 = term473.
Proof. exact (MK_COMB (@lem3913539) (@lem3913538)). Qed.
Lemma lem3913541 : term251 = term474.
Proof. exact (MK_COMB (@lem3913540) (@lem3913535)). Qed.
Lemma lem3913542 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3913544 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913545 : term251 = term252.
Proof. exact (@lem3913544 (NUMERAL 0) term11). Qed.
Lemma lem3913546 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913547 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913548 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913547 h1) (fun h1 : term252 = True => @lem3913546)). Qed.
Lemma lem3913549 : term252 = True.
Proof. exact (EQ_MP (@lem3913548) (@lem3913546)). Qed.
Lemma lem3913550 : term251 = True.
Proof. exact (TRANS (@lem3913545) (@lem3913549)). Qed.
Lemma lem3913551 : True = term251.
Proof. exact (SYM (@lem3913550)). Qed.
Lemma lem3913552 : term251.
Proof. exact (EQ_MP (@lem3913551) (@lem0)). Qed.
Lemma lem3913553 : term476.
Proof. exact (@lem3913542 (@lem3913552)). Qed.
Lemma lem3913555 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913556 : term251 = term252.
Proof. exact (@lem3913555 (NUMERAL 0) term11). Qed.
Lemma lem3913557 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913558 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913559 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913558 h1) (fun h1 : term252 = True => @lem3913557)). Qed.
Lemma lem3913560 : term252 = True.
Proof. exact (EQ_MP (@lem3913559) (@lem3913557)). Qed.
Lemma lem3913561 : term251 = True.
Proof. exact (TRANS (@lem3913556) (@lem3913560)). Qed.
Lemma lem3913562 : True = term251.
Proof. exact (SYM (@lem3913561)). Qed.
Lemma lem3913563 : term251.
Proof. exact (EQ_MP (@lem3913562) (@lem0)). Qed.
Lemma lem3913564 : term474 = term477.
Proof. exact (@lem3913553 (@lem3913563)). Qed.
Lemma lem3913566 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913567 : term208 = term209.
Proof. exact (@lem3913566 term11 term11). Qed.
Lemma lem3913568 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913569 : term211 = term11.
Proof. exact (EQ_MP (@lem3913568) (@lem940073)). Qed.
Lemma lem3913570 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913571 : term209 = term143.
Proof. exact (MK_COMB (@lem3913570) (@lem3913569)). Qed.
Lemma lem3913572 : term208 = term143.
Proof. exact (TRANS (@lem3913567) (@lem3913571)). Qed.
Lemma lem3913574 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913575 : term263 = term133.
Proof. exact (@lem3913574 term11). Qed.
Lemma lem3913576 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913577 : term478 = term472.
Proof. exact (MK_COMB (@lem3913576) (@lem3913575)). Qed.
Lemma lem3913578 : term477 = term251.
Proof. exact (MK_COMB (@lem3913577) (@lem3913572)). Qed.
Lemma lem3913580 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913581 : term251 = term252.
Proof. exact (@lem3913580 (NUMERAL 0) term11). Qed.
Lemma lem3913582 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913583 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913584 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913583 h1) (fun h1 : term252 = True => @lem3913582)). Qed.
Lemma lem3913585 : term252 = True.
Proof. exact (EQ_MP (@lem3913584) (@lem3913582)). Qed.
Lemma lem3913586 : term251 = True.
Proof. exact (TRANS (@lem3913581) (@lem3913585)). Qed.
Lemma lem3913587 : term477 = True.
Proof. exact (TRANS (@lem3913578) (@lem3913586)). Qed.
Lemma lem3913588 : term474 = True.
Proof. exact (TRANS (@lem3913564) (@lem3913587)). Qed.
Lemma lem3913589 : term251 = True.
Proof. exact (TRANS (@lem3913541) (@lem3913588)). Qed.
Lemma lem3913590 : term471 = True.
Proof. exact (TRANS (@lem3913532) (@lem3913589)). Qed.
Lemma lem3913591 : True = term471.
Proof. exact (SYM (@lem3913590)). Qed.
Lemma lem3913592 : term471.
Proof. exact (EQ_MP (@lem3913591) (@lem0)). Qed.
Lemma lem3913593 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term606 _45439.
Proof. exact (conj (@lem3913592) (@lem3913528 _45438 _45439 h1)). Qed.
Lemma lem3913595 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3913596 (_45439 : int) : term607 _45439.
Proof. exact (@lem3913595 term143 (term234 _45439)). Qed.
Lemma lem3913597 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term608 _45439.
Proof. exact (@lem3913596 _45439 (@lem3913593 _45438 _45439 h1)). Qed.
Lemma lem3913598 (_45439 : int) : (term594 _45439) = (term234 _45439).
Proof. exact (@lem1982733 (term234 _45439)). Qed.
Lemma lem3913599 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3913600 (_45439 : int) : (term609 _45439) = (term292 _45439).
Proof. exact (MK_COMB (@lem3913599) (@lem3913598 _45439)). Qed.
Lemma lem3913601 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913602 (_45439 : int) : (term608 _45439) = (term293 _45439).
Proof. exact (MK_COMB (@lem3913600 _45439) (@lem3913601)). Qed.
Lemma lem3913603 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term293 _45439.
Proof. exact (EQ_MP (@lem3913602 _45439) (@lem3913597 _45438 _45439 h1)). Qed.
Lemma lem3913605 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3913606 (_45439 : int) : term539 _45439.
Proof. exact (@lem3913605 (real_of_int _45439)). Qed.
Lemma lem3913607 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term540 _45439.
Proof. exact (@lem3913606 _45439 (@lem3913529 _45438 _45439 h1)). Qed.
Lemma lem3913608 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term541 _45439.
Proof. exact (@lem3913607 _45438 _45439 h1 term143). Qed.
Lemma lem3913609 (_45439 : int) : (term541 _45439) = ((term542 _45439) = term133).
Proof. exact (eq_refl (term541 _45439)). Qed.
Lemma lem3913610 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : (term542 _45439) = term133.
Proof. exact (EQ_MP (@lem3913609 _45439) (@lem3913608 _45438 _45439 h1)). Qed.
Lemma lem3913611 (_45439 : int) : (term542 _45439) = (real_of_int _45439).
Proof. exact (@lem1982733 (real_of_int _45439)). Qed.
Lemma lem3913612 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3913613 (_45439 : int) : (term543 _45439) = (term146 _45439).
Proof. exact (MK_COMB (@lem3913612) (@lem3913611 _45439)). Qed.
Lemma lem3913614 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913615 (_45439 : int) : ((term542 _45439) = term133) = ((real_of_int _45439) = term133).
Proof. exact (MK_COMB (@lem3913613 _45439) (@lem3913614)). Qed.
Lemma lem3913616 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (EQ_MP (@lem3913615 _45439) (@lem3913610 _45438 _45439 h1)). Qed.
Lemma lem3913617 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term347 _45439.
Proof. exact (conj (@lem3913616 _45438 _45439 h1) (@lem3913603 _45438 _45439 h1)). Qed.
Lemma lem3913619 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3913620 (_45439 : int) : term610 _45439.
Proof. exact (@lem3913619 (real_of_int _45439) (term234 _45439)). Qed.
Lemma lem3913621 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term611 _45439.
Proof. exact (@lem3913620 _45439 (@lem3913617 _45438 _45439 h1)). Qed.
Lemma lem3913622 (_45439 : int) : (term612 _45439) = (term516 _45439).
Proof. exact (@lem1982763 (real_of_int _45439) (term237 _45439) term199). Qed.
Lemma lem3913623 (_45439 : int) : (term517 _45439) = (term498 _45439).
Proof. exact (@lem1982715 term199 (real_of_int _45439)). Qed.
Lemma lem3913625 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913626 : term143 = term224.
Proof. exact (@lem3913625 term11). Qed.
Lemma lem3913628 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3913629 : term199 = term200.
Proof. exact (@lem3913628 term11). Qed.
Lemma lem3913630 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913631 : term499 = term500.
Proof. exact (MK_COMB (@lem3913630) (@lem3913629)). Qed.
Lemma lem3913632 : term501 = term502.
Proof. exact (MK_COMB (@lem3913631) (@lem3913626)). Qed.
Lemma lem3913633 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3913635 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913636 : term251 = term252.
Proof. exact (@lem3913635 (NUMERAL 0) term11). Qed.
Lemma lem3913637 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913638 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913639 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913638 h1) (fun h1 : term252 = True => @lem3913637)). Qed.
Lemma lem3913640 : term252 = True.
Proof. exact (EQ_MP (@lem3913639) (@lem3913637)). Qed.
Lemma lem3913641 : term251 = True.
Proof. exact (TRANS (@lem3913636) (@lem3913640)). Qed.
Lemma lem3913642 : True = term251.
Proof. exact (SYM (@lem3913641)). Qed.
Lemma lem3913643 : term251.
Proof. exact (EQ_MP (@lem3913642) (@lem0)). Qed.
Lemma lem3913644 : term504.
Proof. exact (@lem3913633 (@lem3913643)). Qed.
Lemma lem3913646 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913647 : term251 = term252.
Proof. exact (@lem3913646 (NUMERAL 0) term11). Qed.
Lemma lem3913648 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913649 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913650 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913649 h1) (fun h1 : term252 = True => @lem3913648)). Qed.
Lemma lem3913651 : term252 = True.
Proof. exact (EQ_MP (@lem3913650) (@lem3913648)). Qed.
Lemma lem3913652 : term251 = True.
Proof. exact (TRANS (@lem3913647) (@lem3913651)). Qed.
Lemma lem3913653 : True = term251.
Proof. exact (SYM (@lem3913652)). Qed.
Lemma lem3913654 : term251.
Proof. exact (EQ_MP (@lem3913653) (@lem0)). Qed.
Lemma lem3913655 : term505.
Proof. exact (@lem3913644 (@lem3913654)). Qed.
Lemma lem3913657 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913658 : term251 = term252.
Proof. exact (@lem3913657 (NUMERAL 0) term11). Qed.
Lemma lem3913659 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913660 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913661 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913660 h1) (fun h1 : term252 = True => @lem3913659)). Qed.
Lemma lem3913662 : term252 = True.
Proof. exact (EQ_MP (@lem3913661) (@lem3913659)). Qed.
Lemma lem3913663 : term251 = True.
Proof. exact (TRANS (@lem3913658) (@lem3913662)). Qed.
Lemma lem3913664 : True = term251.
Proof. exact (SYM (@lem3913663)). Qed.
Lemma lem3913665 : term251.
Proof. exact (EQ_MP (@lem3913664) (@lem0)). Qed.
Lemma lem3913666 : term506.
Proof. exact (@lem3913655 (@lem3913665)). Qed.
Lemma lem3913668 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913669 : term208 = term209.
Proof. exact (@lem3913668 term11 term11). Qed.
Lemma lem3913670 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913671 : term211 = term11.
Proof. exact (EQ_MP (@lem3913670) (@lem940073)). Qed.
Lemma lem3913672 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913673 : term209 = term143.
Proof. exact (MK_COMB (@lem3913672) (@lem3913671)). Qed.
Lemma lem3913674 : term208 = term143.
Proof. exact (TRANS (@lem3913669) (@lem3913673)). Qed.
Lemma lem3913676 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3913677 : term225 = term230.
Proof. exact (@lem3913676 term11 term11). Qed.
Lemma lem3913678 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913679 : term211 = term11.
Proof. exact (EQ_MP (@lem3913678) (@lem940073)). Qed.
Lemma lem3913680 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913681 : term209 = term143.
Proof. exact (MK_COMB (@lem3913680) (@lem3913679)). Qed.
Lemma lem3913682 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3913683 : term230 = term199.
Proof. exact (MK_COMB (@lem3913682) (@lem3913681)). Qed.
Lemma lem3913684 : term225 = term199.
Proof. exact (TRANS (@lem3913677) (@lem3913683)). Qed.
Lemma lem3913685 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913686 : term507 = term499.
Proof. exact (MK_COMB (@lem3913685) (@lem3913684)). Qed.
Lemma lem3913687 : term508 = term501.
Proof. exact (MK_COMB (@lem3913686) (@lem3913674)). Qed.
Lemma lem3913689 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3913690 : term501 = term133.
Proof. exact (@lem3913689 term11). Qed.
Lemma lem3913691 : term508 = term133.
Proof. exact (TRANS (@lem3913687) (@lem3913690)). Qed.
Lemma lem3913692 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3913693 : term510 = term261.
Proof. exact (MK_COMB (@lem3913692) (@lem3913691)). Qed.
Lemma lem3913694 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3913695 : term511 = term263.
Proof. exact (MK_COMB (@lem3913693) (@lem3913694)). Qed.
Lemma lem3913697 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913698 : term263 = term133.
Proof. exact (@lem3913697 term11). Qed.
Lemma lem3913699 : term511 = term133.
Proof. exact (TRANS (@lem3913695) (@lem3913698)). Qed.
Lemma lem3913701 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913702 : term208 = term209.
Proof. exact (@lem3913701 term11 term11). Qed.
Lemma lem3913703 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913704 : term211 = term11.
Proof. exact (EQ_MP (@lem3913703) (@lem940073)). Qed.
Lemma lem3913705 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913706 : term209 = term143.
Proof. exact (MK_COMB (@lem3913705) (@lem3913704)). Qed.
Lemma lem3913707 : term208 = term143.
Proof. exact (TRANS (@lem3913702) (@lem3913706)). Qed.
Lemma lem3913708 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3913709 : term265 = term263.
Proof. exact (MK_COMB (@lem3913708) (@lem3913707)). Qed.
Lemma lem3913711 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913712 : term263 = term133.
Proof. exact (@lem3913711 term11). Qed.
Lemma lem3913713 : term265 = term133.
Proof. exact (TRANS (@lem3913709) (@lem3913712)). Qed.
Lemma lem3913714 : term133 = term265.
Proof. exact (SYM (@lem3913713)). Qed.
Lemma lem3913715 : term511 = term265.
Proof. exact (TRANS (@lem3913699) (@lem3913714)). Qed.
Lemma lem3913716 : term502 = term196.
Proof. exact (@lem3913666 (@lem3913715)). Qed.
Lemma lem3913717 : term501 = term196.
Proof. exact (TRANS (@lem3913632) (@lem3913716)). Qed.
Lemma lem3913719 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3913720 : term196 = term133.
Proof. exact (@lem3913719 term133). Qed.
Lemma lem3913721 : term501 = term133.
Proof. exact (TRANS (@lem3913717) (@lem3913720)). Qed.
Lemma lem3913722 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3913723 : term512 = term261.
Proof. exact (MK_COMB (@lem3913722) (@lem3913721)). Qed.
Lemma lem3913724 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3913725 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3913723) (@lem3913724 _45439)). Qed.
Lemma lem3913726 (_45439 : int) : (term517 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3913623 _45439) (@lem3913725 _45439)). Qed.
Lemma lem3913727 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3913728 (_45439 : int) : (term517 _45439) = term133.
Proof. exact (TRANS (@lem3913726 _45439) (@lem3913727 _45439)). Qed.
Lemma lem3913729 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913730 (_45439 : int) : (term518 _45439) = term175.
Proof. exact (MK_COMB (@lem3913729) (@lem3913728 _45439)). Qed.
Lemma lem3913731 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3913732 (_45439 : int) : (term516 _45439) = term519.
Proof. exact (MK_COMB (@lem3913730 _45439) (@lem3913731)). Qed.
Lemma lem3913733 (_45439 : int) : (term612 _45439) = term519.
Proof. exact (TRANS (@lem3913622 _45439) (@lem3913732 _45439)). Qed.
Lemma lem3913734 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3913735 (_45439 : int) : (term612 _45439) = term199.
Proof. exact (TRANS (@lem3913733 _45439) (@lem3913734)). Qed.
Lemma lem3913736 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3913737 (_45439 : int) : (term613 _45439) = term521.
Proof. exact (MK_COMB (@lem3913736) (@lem3913735 _45439)). Qed.
Lemma lem3913738 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913739 (_45439 : int) : (term611 _45439) = term522.
Proof. exact (MK_COMB (@lem3913737 _45439) (@lem3913738)). Qed.
Lemma lem3913740 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3913739 _45439) (@lem3913621 _45438 _45439 h1)). Qed.
Lemma lem3913742 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3913743 : term522 = term523.
Proof. exact (@lem3913742 term133 term199). Qed.
Lemma lem3913745 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3913746 : term199 = term200.
Proof. exact (@lem3913745 term11). Qed.
Lemma lem3913748 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913749 : term133 = term196.
Proof. exact (@lem3913748 (NUMERAL 0)). Qed.
Lemma lem3913750 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3913751 : term135 = term524.
Proof. exact (MK_COMB (@lem3913750) (@lem3913749)). Qed.
Lemma lem3913752 : term523 = term525.
Proof. exact (MK_COMB (@lem3913751) (@lem3913746)). Qed.
Lemma lem3913753 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3913755 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913756 : term251 = term252.
Proof. exact (@lem3913755 (NUMERAL 0) term11). Qed.
Lemma lem3913757 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913758 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913759 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913758 h1) (fun h1 : term252 = True => @lem3913757)). Qed.
Lemma lem3913760 : term252 = True.
Proof. exact (EQ_MP (@lem3913759) (@lem3913757)). Qed.
Lemma lem3913761 : term251 = True.
Proof. exact (TRANS (@lem3913756) (@lem3913760)). Qed.
Lemma lem3913762 : True = term251.
Proof. exact (SYM (@lem3913761)). Qed.
Lemma lem3913763 : term251.
Proof. exact (EQ_MP (@lem3913762) (@lem0)). Qed.
Lemma lem3913764 : term527.
Proof. exact (@lem3913753 (@lem3913763)). Qed.
Lemma lem3913766 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913767 : term251 = term252.
Proof. exact (@lem3913766 (NUMERAL 0) term11). Qed.
Lemma lem3913768 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913769 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913770 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913769 h1) (fun h1 : term252 = True => @lem3913768)). Qed.
Lemma lem3913771 : term252 = True.
Proof. exact (EQ_MP (@lem3913770) (@lem3913768)). Qed.
Lemma lem3913772 : term251 = True.
Proof. exact (TRANS (@lem3913767) (@lem3913771)). Qed.
Lemma lem3913773 : True = term251.
Proof. exact (SYM (@lem3913772)). Qed.
Lemma lem3913774 : term251.
Proof. exact (EQ_MP (@lem3913773) (@lem0)). Qed.
Lemma lem3913775 : term525 = term528.
Proof. exact (@lem3913764 (@lem3913774)). Qed.
Lemma lem3913777 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3913778 : term225 = term230.
Proof. exact (@lem3913777 term11 term11). Qed.
Lemma lem3913779 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913780 : term211 = term11.
Proof. exact (EQ_MP (@lem3913779) (@lem940073)). Qed.
Lemma lem3913781 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913782 : term209 = term143.
Proof. exact (MK_COMB (@lem3913781) (@lem3913780)). Qed.
Lemma lem3913783 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3913784 : term230 = term199.
Proof. exact (MK_COMB (@lem3913783) (@lem3913782)). Qed.
Lemma lem3913785 : term225 = term199.
Proof. exact (TRANS (@lem3913778) (@lem3913784)). Qed.
Lemma lem3913787 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913788 : term263 = term133.
Proof. exact (@lem3913787 term11). Qed.
Lemma lem3913789 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3913790 : term529 = term135.
Proof. exact (MK_COMB (@lem3913789) (@lem3913788)). Qed.
Lemma lem3913791 : term528 = term523.
Proof. exact (MK_COMB (@lem3913790) (@lem3913785)). Qed.
Lemma lem3913793 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3913794 : term523 = term532.
Proof. exact (@lem3913793 (NUMERAL 0) term11). Qed.
Lemma lem3913795 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913796 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3913797 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913796 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3913795)). Qed.
Lemma lem3913798 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3913797) (@lem3913795)). Qed.
Lemma lem3913799 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3913800 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3913801 : term533 = (and True).
Proof. exact (MK_COMB (@lem3913800) (@lem3913799)). Qed.
Lemma lem3913802 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3913801) (@lem3913798)). Qed.
Lemma lem3913804 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3913805 : term532 = False.
Proof. exact (TRANS (@lem3913802) (@lem3913804)). Qed.
Lemma lem3913806 : term523 = False.
Proof. exact (TRANS (@lem3913794) (@lem3913805)). Qed.
Lemma lem3913807 : term528 = False.
Proof. exact (TRANS (@lem3913791) (@lem3913806)). Qed.
Lemma lem3913808 : term525 = False.
Proof. exact (TRANS (@lem3913775) (@lem3913807)). Qed.
Lemma lem3913809 : term523 = False.
Proof. exact (TRANS (@lem3913752) (@lem3913808)). Qed.
Lemma lem3913810 : term522 = False.
Proof. exact (TRANS (@lem3913743) (@lem3913809)). Qed.
Lemma lem3913811 (_45438 : int) (_45439 : int) (h1 : term618 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3913810) (@lem3913740 _45438 _45439 h1)). Qed.
Lemma lem3913812 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term619 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3913813 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term443 _45438 _45439.
Proof. exact (proj2 (@lem3913812 _45438 _45439 h1)). Qed.
Lemma lem3913815 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term394 _45438 _45439.
Proof. exact (proj2 (@lem3913813 _45438 _45439 h1)). Qed.
Lemma lem3913817 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term347 _45439.
Proof. exact (proj2 (@lem3913815 _45438 _45439 h1)). Qed.
Lemma lem3913821 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term293 _45439.
Proof. exact (proj2 (@lem3913817 _45438 _45439 h1)). Qed.
Lemma lem3913822 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (proj1 (@lem3913817 _45438 _45439 h1)). Qed.
Lemma lem3913824 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3913825 : term471 = term251.
Proof. exact (@lem3913824 term133 term143). Qed.
Lemma lem3913827 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913828 : term143 = term224.
Proof. exact (@lem3913827 term11). Qed.
Lemma lem3913830 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913831 : term133 = term196.
Proof. exact (@lem3913830 (NUMERAL 0)). Qed.
Lemma lem3913832 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913833 : term472 = term473.
Proof. exact (MK_COMB (@lem3913832) (@lem3913831)). Qed.
Lemma lem3913834 : term251 = term474.
Proof. exact (MK_COMB (@lem3913833) (@lem3913828)). Qed.
Lemma lem3913835 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3913837 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913838 : term251 = term252.
Proof. exact (@lem3913837 (NUMERAL 0) term11). Qed.
Lemma lem3913839 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913840 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913841 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913840 h1) (fun h1 : term252 = True => @lem3913839)). Qed.
Lemma lem3913842 : term252 = True.
Proof. exact (EQ_MP (@lem3913841) (@lem3913839)). Qed.
Lemma lem3913843 : term251 = True.
Proof. exact (TRANS (@lem3913838) (@lem3913842)). Qed.
Lemma lem3913844 : True = term251.
Proof. exact (SYM (@lem3913843)). Qed.
Lemma lem3913845 : term251.
Proof. exact (EQ_MP (@lem3913844) (@lem0)). Qed.
Lemma lem3913846 : term476.
Proof. exact (@lem3913835 (@lem3913845)). Qed.
Lemma lem3913848 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913849 : term251 = term252.
Proof. exact (@lem3913848 (NUMERAL 0) term11). Qed.
Lemma lem3913850 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913851 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913852 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913851 h1) (fun h1 : term252 = True => @lem3913850)). Qed.
Lemma lem3913853 : term252 = True.
Proof. exact (EQ_MP (@lem3913852) (@lem3913850)). Qed.
Lemma lem3913854 : term251 = True.
Proof. exact (TRANS (@lem3913849) (@lem3913853)). Qed.
Lemma lem3913855 : True = term251.
Proof. exact (SYM (@lem3913854)). Qed.
Lemma lem3913856 : term251.
Proof. exact (EQ_MP (@lem3913855) (@lem0)). Qed.
Lemma lem3913857 : term474 = term477.
Proof. exact (@lem3913846 (@lem3913856)). Qed.
Lemma lem3913859 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913860 : term208 = term209.
Proof. exact (@lem3913859 term11 term11). Qed.
Lemma lem3913861 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913862 : term211 = term11.
Proof. exact (EQ_MP (@lem3913861) (@lem940073)). Qed.
Lemma lem3913863 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913864 : term209 = term143.
Proof. exact (MK_COMB (@lem3913863) (@lem3913862)). Qed.
Lemma lem3913865 : term208 = term143.
Proof. exact (TRANS (@lem3913860) (@lem3913864)). Qed.
Lemma lem3913867 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913868 : term263 = term133.
Proof. exact (@lem3913867 term11). Qed.
Lemma lem3913869 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3913870 : term478 = term472.
Proof. exact (MK_COMB (@lem3913869) (@lem3913868)). Qed.
Lemma lem3913871 : term477 = term251.
Proof. exact (MK_COMB (@lem3913870) (@lem3913865)). Qed.
Lemma lem3913873 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913874 : term251 = term252.
Proof. exact (@lem3913873 (NUMERAL 0) term11). Qed.
Lemma lem3913875 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913876 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913877 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913876 h1) (fun h1 : term252 = True => @lem3913875)). Qed.
Lemma lem3913878 : term252 = True.
Proof. exact (EQ_MP (@lem3913877) (@lem3913875)). Qed.
Lemma lem3913879 : term251 = True.
Proof. exact (TRANS (@lem3913874) (@lem3913878)). Qed.
Lemma lem3913880 : term477 = True.
Proof. exact (TRANS (@lem3913871) (@lem3913879)). Qed.
Lemma lem3913881 : term474 = True.
Proof. exact (TRANS (@lem3913857) (@lem3913880)). Qed.
Lemma lem3913882 : term251 = True.
Proof. exact (TRANS (@lem3913834) (@lem3913881)). Qed.
Lemma lem3913883 : term471 = True.
Proof. exact (TRANS (@lem3913825) (@lem3913882)). Qed.
Lemma lem3913884 : True = term471.
Proof. exact (SYM (@lem3913883)). Qed.
Lemma lem3913885 : term471.
Proof. exact (EQ_MP (@lem3913884) (@lem0)). Qed.
Lemma lem3913886 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term606 _45439.
Proof. exact (conj (@lem3913885) (@lem3913821 _45438 _45439 h1)). Qed.
Lemma lem3913888 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3913889 (_45439 : int) : term607 _45439.
Proof. exact (@lem3913888 term143 (term234 _45439)). Qed.
Lemma lem3913890 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term608 _45439.
Proof. exact (@lem3913889 _45439 (@lem3913886 _45438 _45439 h1)). Qed.
Lemma lem3913891 (_45439 : int) : (term594 _45439) = (term234 _45439).
Proof. exact (@lem1982733 (term234 _45439)). Qed.
Lemma lem3913892 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3913893 (_45439 : int) : (term609 _45439) = (term292 _45439).
Proof. exact (MK_COMB (@lem3913892) (@lem3913891 _45439)). Qed.
Lemma lem3913894 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913895 (_45439 : int) : (term608 _45439) = (term293 _45439).
Proof. exact (MK_COMB (@lem3913893 _45439) (@lem3913894)). Qed.
Lemma lem3913896 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term293 _45439.
Proof. exact (EQ_MP (@lem3913895 _45439) (@lem3913890 _45438 _45439 h1)). Qed.
Lemma lem3913898 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3913899 (_45439 : int) : term539 _45439.
Proof. exact (@lem3913898 (real_of_int _45439)). Qed.
Lemma lem3913900 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term540 _45439.
Proof. exact (@lem3913899 _45439 (@lem3913822 _45438 _45439 h1)). Qed.
Lemma lem3913901 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term541 _45439.
Proof. exact (@lem3913900 _45438 _45439 h1 term143). Qed.
Lemma lem3913902 (_45439 : int) : (term541 _45439) = ((term542 _45439) = term133).
Proof. exact (eq_refl (term541 _45439)). Qed.
Lemma lem3913903 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : (term542 _45439) = term133.
Proof. exact (EQ_MP (@lem3913902 _45439) (@lem3913901 _45438 _45439 h1)). Qed.
Lemma lem3913904 (_45439 : int) : (term542 _45439) = (real_of_int _45439).
Proof. exact (@lem1982733 (real_of_int _45439)). Qed.
Lemma lem3913905 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3913906 (_45439 : int) : (term543 _45439) = (term146 _45439).
Proof. exact (MK_COMB (@lem3913905) (@lem3913904 _45439)). Qed.
Lemma lem3913907 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3913908 (_45439 : int) : ((term542 _45439) = term133) = ((real_of_int _45439) = term133).
Proof. exact (MK_COMB (@lem3913906 _45439) (@lem3913907)). Qed.
Lemma lem3913909 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (EQ_MP (@lem3913908 _45439) (@lem3913903 _45438 _45439 h1)). Qed.
Lemma lem3913910 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term347 _45439.
Proof. exact (conj (@lem3913909 _45438 _45439 h1) (@lem3913896 _45438 _45439 h1)). Qed.
Lemma lem3913912 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3913913 (_45439 : int) : term610 _45439.
Proof. exact (@lem3913912 (real_of_int _45439) (term234 _45439)). Qed.
Lemma lem3913914 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term611 _45439.
Proof. exact (@lem3913913 _45439 (@lem3913910 _45438 _45439 h1)). Qed.
Lemma lem3913915 (_45439 : int) : (term612 _45439) = (term516 _45439).
Proof. exact (@lem1982763 (real_of_int _45439) (term237 _45439) term199). Qed.
Lemma lem3913916 (_45439 : int) : (term517 _45439) = (term498 _45439).
Proof. exact (@lem1982715 term199 (real_of_int _45439)). Qed.
Lemma lem3913918 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3913919 : term143 = term224.
Proof. exact (@lem3913918 term11). Qed.
Lemma lem3913921 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3913922 : term199 = term200.
Proof. exact (@lem3913921 term11). Qed.
Lemma lem3913923 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913924 : term499 = term500.
Proof. exact (MK_COMB (@lem3913923) (@lem3913922)). Qed.
Lemma lem3913925 : term501 = term502.
Proof. exact (MK_COMB (@lem3913924) (@lem3913919)). Qed.
Lemma lem3913926 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3913928 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913929 : term251 = term252.
Proof. exact (@lem3913928 (NUMERAL 0) term11). Qed.
Lemma lem3913930 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913931 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913932 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913931 h1) (fun h1 : term252 = True => @lem3913930)). Qed.
Lemma lem3913933 : term252 = True.
Proof. exact (EQ_MP (@lem3913932) (@lem3913930)). Qed.
Lemma lem3913934 : term251 = True.
Proof. exact (TRANS (@lem3913929) (@lem3913933)). Qed.
Lemma lem3913935 : True = term251.
Proof. exact (SYM (@lem3913934)). Qed.
Lemma lem3913936 : term251.
Proof. exact (EQ_MP (@lem3913935) (@lem0)). Qed.
Lemma lem3913937 : term504.
Proof. exact (@lem3913926 (@lem3913936)). Qed.
Lemma lem3913939 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913940 : term251 = term252.
Proof. exact (@lem3913939 (NUMERAL 0) term11). Qed.
Lemma lem3913941 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913942 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913943 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913942 h1) (fun h1 : term252 = True => @lem3913941)). Qed.
Lemma lem3913944 : term252 = True.
Proof. exact (EQ_MP (@lem3913943) (@lem3913941)). Qed.
Lemma lem3913945 : term251 = True.
Proof. exact (TRANS (@lem3913940) (@lem3913944)). Qed.
Lemma lem3913946 : True = term251.
Proof. exact (SYM (@lem3913945)). Qed.
Lemma lem3913947 : term251.
Proof. exact (EQ_MP (@lem3913946) (@lem0)). Qed.
Lemma lem3913948 : term505.
Proof. exact (@lem3913937 (@lem3913947)). Qed.
Lemma lem3913950 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3913951 : term251 = term252.
Proof. exact (@lem3913950 (NUMERAL 0) term11). Qed.
Lemma lem3913952 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3913953 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3913954 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3913953 h1) (fun h1 : term252 = True => @lem3913952)). Qed.
Lemma lem3913955 : term252 = True.
Proof. exact (EQ_MP (@lem3913954) (@lem3913952)). Qed.
Lemma lem3913956 : term251 = True.
Proof. exact (TRANS (@lem3913951) (@lem3913955)). Qed.
Lemma lem3913957 : True = term251.
Proof. exact (SYM (@lem3913956)). Qed.
Lemma lem3913958 : term251.
Proof. exact (EQ_MP (@lem3913957) (@lem0)). Qed.
Lemma lem3913959 : term506.
Proof. exact (@lem3913948 (@lem3913958)). Qed.
Lemma lem3913961 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913962 : term208 = term209.
Proof. exact (@lem3913961 term11 term11). Qed.
Lemma lem3913963 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913964 : term211 = term11.
Proof. exact (EQ_MP (@lem3913963) (@lem940073)). Qed.
Lemma lem3913965 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913966 : term209 = term143.
Proof. exact (MK_COMB (@lem3913965) (@lem3913964)). Qed.
Lemma lem3913967 : term208 = term143.
Proof. exact (TRANS (@lem3913962) (@lem3913966)). Qed.
Lemma lem3913969 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3913970 : term225 = term230.
Proof. exact (@lem3913969 term11 term11). Qed.
Lemma lem3913971 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913972 : term211 = term11.
Proof. exact (EQ_MP (@lem3913971) (@lem940073)). Qed.
Lemma lem3913973 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913974 : term209 = term143.
Proof. exact (MK_COMB (@lem3913973) (@lem3913972)). Qed.
Lemma lem3913975 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3913976 : term230 = term199.
Proof. exact (MK_COMB (@lem3913975) (@lem3913974)). Qed.
Lemma lem3913977 : term225 = term199.
Proof. exact (TRANS (@lem3913970) (@lem3913976)). Qed.
Lemma lem3913978 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3913979 : term507 = term499.
Proof. exact (MK_COMB (@lem3913978) (@lem3913977)). Qed.
Lemma lem3913980 : term508 = term501.
Proof. exact (MK_COMB (@lem3913979) (@lem3913967)). Qed.
Lemma lem3913982 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3913983 : term501 = term133.
Proof. exact (@lem3913982 term11). Qed.
Lemma lem3913984 : term508 = term133.
Proof. exact (TRANS (@lem3913980) (@lem3913983)). Qed.
Lemma lem3913985 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3913986 : term510 = term261.
Proof. exact (MK_COMB (@lem3913985) (@lem3913984)). Qed.
Lemma lem3913987 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3913988 : term511 = term263.
Proof. exact (MK_COMB (@lem3913986) (@lem3913987)). Qed.
Lemma lem3913990 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3913991 : term263 = term133.
Proof. exact (@lem3913990 term11). Qed.
Lemma lem3913992 : term511 = term133.
Proof. exact (TRANS (@lem3913988) (@lem3913991)). Qed.
Lemma lem3913994 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3913995 : term208 = term209.
Proof. exact (@lem3913994 term11 term11). Qed.
Lemma lem3913996 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3913997 : term211 = term11.
Proof. exact (EQ_MP (@lem3913996) (@lem940073)). Qed.
Lemma lem3913998 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3913999 : term209 = term143.
Proof. exact (MK_COMB (@lem3913998) (@lem3913997)). Qed.
Lemma lem3914000 : term208 = term143.
Proof. exact (TRANS (@lem3913995) (@lem3913999)). Qed.
Lemma lem3914001 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3914002 : term265 = term263.
Proof. exact (MK_COMB (@lem3914001) (@lem3914000)). Qed.
Lemma lem3914004 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914005 : term263 = term133.
Proof. exact (@lem3914004 term11). Qed.
Lemma lem3914006 : term265 = term133.
Proof. exact (TRANS (@lem3914002) (@lem3914005)). Qed.
Lemma lem3914007 : term133 = term265.
Proof. exact (SYM (@lem3914006)). Qed.
Lemma lem3914008 : term511 = term265.
Proof. exact (TRANS (@lem3913992) (@lem3914007)). Qed.
Lemma lem3914009 : term502 = term196.
Proof. exact (@lem3913959 (@lem3914008)). Qed.
Lemma lem3914010 : term501 = term196.
Proof. exact (TRANS (@lem3913925) (@lem3914009)). Qed.
Lemma lem3914012 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3914013 : term196 = term133.
Proof. exact (@lem3914012 term133). Qed.
Lemma lem3914014 : term501 = term133.
Proof. exact (TRANS (@lem3914010) (@lem3914013)). Qed.
Lemma lem3914015 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914016 : term512 = term261.
Proof. exact (MK_COMB (@lem3914015) (@lem3914014)). Qed.
Lemma lem3914017 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3914018 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3914016) (@lem3914017 _45439)). Qed.
Lemma lem3914019 (_45439 : int) : (term517 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3913916 _45439) (@lem3914018 _45439)). Qed.
Lemma lem3914020 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3914021 (_45439 : int) : (term517 _45439) = term133.
Proof. exact (TRANS (@lem3914019 _45439) (@lem3914020 _45439)). Qed.
Lemma lem3914022 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914023 (_45439 : int) : (term518 _45439) = term175.
Proof. exact (MK_COMB (@lem3914022) (@lem3914021 _45439)). Qed.
Lemma lem3914024 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3914025 (_45439 : int) : (term516 _45439) = term519.
Proof. exact (MK_COMB (@lem3914023 _45439) (@lem3914024)). Qed.
Lemma lem3914026 (_45439 : int) : (term612 _45439) = term519.
Proof. exact (TRANS (@lem3913915 _45439) (@lem3914025 _45439)). Qed.
Lemma lem3914027 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3914028 (_45439 : int) : (term612 _45439) = term199.
Proof. exact (TRANS (@lem3914026 _45439) (@lem3914027)). Qed.
Lemma lem3914029 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3914030 (_45439 : int) : (term613 _45439) = term521.
Proof. exact (MK_COMB (@lem3914029) (@lem3914028 _45439)). Qed.
Lemma lem3914031 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914032 (_45439 : int) : (term611 _45439) = term522.
Proof. exact (MK_COMB (@lem3914030 _45439) (@lem3914031)). Qed.
Lemma lem3914033 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3914032 _45439) (@lem3913914 _45438 _45439 h1)). Qed.
Lemma lem3914035 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3914036 : term522 = term523.
Proof. exact (@lem3914035 term133 term199). Qed.
Lemma lem3914038 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3914039 : term199 = term200.
Proof. exact (@lem3914038 term11). Qed.
Lemma lem3914041 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914042 : term133 = term196.
Proof. exact (@lem3914041 (NUMERAL 0)). Qed.
Lemma lem3914043 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3914044 : term135 = term524.
Proof. exact (MK_COMB (@lem3914043) (@lem3914042)). Qed.
Lemma lem3914045 : term523 = term525.
Proof. exact (MK_COMB (@lem3914044) (@lem3914039)). Qed.
Lemma lem3914046 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3914048 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914049 : term251 = term252.
Proof. exact (@lem3914048 (NUMERAL 0) term11). Qed.
Lemma lem3914050 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914051 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914052 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914051 h1) (fun h1 : term252 = True => @lem3914050)). Qed.
Lemma lem3914053 : term252 = True.
Proof. exact (EQ_MP (@lem3914052) (@lem3914050)). Qed.
Lemma lem3914054 : term251 = True.
Proof. exact (TRANS (@lem3914049) (@lem3914053)). Qed.
Lemma lem3914055 : True = term251.
Proof. exact (SYM (@lem3914054)). Qed.
Lemma lem3914056 : term251.
Proof. exact (EQ_MP (@lem3914055) (@lem0)). Qed.
Lemma lem3914057 : term527.
Proof. exact (@lem3914046 (@lem3914056)). Qed.
Lemma lem3914059 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914060 : term251 = term252.
Proof. exact (@lem3914059 (NUMERAL 0) term11). Qed.
Lemma lem3914061 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914062 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914063 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914062 h1) (fun h1 : term252 = True => @lem3914061)). Qed.
Lemma lem3914064 : term252 = True.
Proof. exact (EQ_MP (@lem3914063) (@lem3914061)). Qed.
Lemma lem3914065 : term251 = True.
Proof. exact (TRANS (@lem3914060) (@lem3914064)). Qed.
Lemma lem3914066 : True = term251.
Proof. exact (SYM (@lem3914065)). Qed.
Lemma lem3914067 : term251.
Proof. exact (EQ_MP (@lem3914066) (@lem0)). Qed.
Lemma lem3914068 : term525 = term528.
Proof. exact (@lem3914057 (@lem3914067)). Qed.
Lemma lem3914070 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3914071 : term225 = term230.
Proof. exact (@lem3914070 term11 term11). Qed.
Lemma lem3914072 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914073 : term211 = term11.
Proof. exact (EQ_MP (@lem3914072) (@lem940073)). Qed.
Lemma lem3914074 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914075 : term209 = term143.
Proof. exact (MK_COMB (@lem3914074) (@lem3914073)). Qed.
Lemma lem3914076 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3914077 : term230 = term199.
Proof. exact (MK_COMB (@lem3914076) (@lem3914075)). Qed.
Lemma lem3914078 : term225 = term199.
Proof. exact (TRANS (@lem3914071) (@lem3914077)). Qed.
Lemma lem3914080 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914081 : term263 = term133.
Proof. exact (@lem3914080 term11). Qed.
Lemma lem3914082 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3914083 : term529 = term135.
Proof. exact (MK_COMB (@lem3914082) (@lem3914081)). Qed.
Lemma lem3914084 : term528 = term523.
Proof. exact (MK_COMB (@lem3914083) (@lem3914078)). Qed.
Lemma lem3914086 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3914087 : term523 = term532.
Proof. exact (@lem3914086 (NUMERAL 0) term11). Qed.
Lemma lem3914088 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914089 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3914090 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914089 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3914088)). Qed.
Lemma lem3914091 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3914090) (@lem3914088)). Qed.
Lemma lem3914092 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3914093 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3914094 : term533 = (and True).
Proof. exact (MK_COMB (@lem3914093) (@lem3914092)). Qed.
Lemma lem3914095 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3914094) (@lem3914091)). Qed.
Lemma lem3914097 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3914098 : term532 = False.
Proof. exact (TRANS (@lem3914095) (@lem3914097)). Qed.
Lemma lem3914099 : term523 = False.
Proof. exact (TRANS (@lem3914087) (@lem3914098)). Qed.
Lemma lem3914100 : term528 = False.
Proof. exact (TRANS (@lem3914084) (@lem3914099)). Qed.
Lemma lem3914101 : term525 = False.
Proof. exact (TRANS (@lem3914068) (@lem3914100)). Qed.
Lemma lem3914102 : term523 = False.
Proof. exact (TRANS (@lem3914045) (@lem3914101)). Qed.
Lemma lem3914103 : term522 = False.
Proof. exact (TRANS (@lem3914036) (@lem3914102)). Qed.
Lemma lem3914104 (_45438 : int) (_45439 : int) (h1 : term619 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3914103) (@lem3914033 _45438 _45439 h1)). Qed.
Lemma lem3914105 (_45438 : int) (_45439 : int) (h1 : term441 _45438 _45439) : False.
Proof. exact (or_elim (@lem3913520 _45438 _45439 h1) (fun h0 : term618 _45438 _45439 => @lem3913811 _45438 _45439 h0) (fun h0 : term619 _45438 _45439 => @lem3914104 _45438 _45439 h0)). Qed.
Lemma lem3914106 (_45438 : int) (_45439 : int) (h1 : term450 _45438 _45439) : False.
Proof. exact (or_elim (@lem3912759 _45438 _45439 h1) (fun h0 : term445 _45438 _45439 => @lem3913519 _45438 _45439 h0) (fun h0 : term441 _45438 _45439 => @lem3914105 _45438 _45439 h0)). Qed.
Lemma lem3914107 (_45438 : int) (_45439 : int) (h1 : term437 _45438 _45439) : term437 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3914108 (_45438 : int) (_45439 : int) (h1 : term432 _45438 _45439) : term432 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3914109 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term620 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3914110 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term433 _45438 _45439.
Proof. exact (proj2 (@lem3914109 _45438 _45439 h1)). Qed.
Lemma lem3914112 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term384 _45438 _45439.
Proof. exact (proj2 (@lem3914110 _45438 _45439 h1)). Qed.
Lemma lem3914114 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term335 _45438 _45439.
Proof. exact (proj2 (@lem3914112 _45438 _45439 h1)). Qed.
Lemma lem3914115 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (proj1 (@lem3914112 _45438 _45439 h1)). Qed.
Lemma lem3914117 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term280 _45438 _45439.
Proof. exact (proj1 (@lem3914114 _45438 _45439 h1)). Qed.
Lemma lem3914119 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3914120 : term471 = term251.
Proof. exact (@lem3914119 term133 term143). Qed.
Lemma lem3914122 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914123 : term143 = term224.
Proof. exact (@lem3914122 term11). Qed.
Lemma lem3914125 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914126 : term133 = term196.
Proof. exact (@lem3914125 (NUMERAL 0)). Qed.
Lemma lem3914127 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914128 : term472 = term473.
Proof. exact (MK_COMB (@lem3914127) (@lem3914126)). Qed.
Lemma lem3914129 : term251 = term474.
Proof. exact (MK_COMB (@lem3914128) (@lem3914123)). Qed.
Lemma lem3914130 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3914132 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914133 : term251 = term252.
Proof. exact (@lem3914132 (NUMERAL 0) term11). Qed.
Lemma lem3914134 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914135 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914136 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914135 h1) (fun h1 : term252 = True => @lem3914134)). Qed.
Lemma lem3914137 : term252 = True.
Proof. exact (EQ_MP (@lem3914136) (@lem3914134)). Qed.
Lemma lem3914138 : term251 = True.
Proof. exact (TRANS (@lem3914133) (@lem3914137)). Qed.
Lemma lem3914139 : True = term251.
Proof. exact (SYM (@lem3914138)). Qed.
Lemma lem3914140 : term251.
Proof. exact (EQ_MP (@lem3914139) (@lem0)). Qed.
Lemma lem3914141 : term476.
Proof. exact (@lem3914130 (@lem3914140)). Qed.
Lemma lem3914143 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914144 : term251 = term252.
Proof. exact (@lem3914143 (NUMERAL 0) term11). Qed.
Lemma lem3914145 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914146 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914147 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914146 h1) (fun h1 : term252 = True => @lem3914145)). Qed.
Lemma lem3914148 : term252 = True.
Proof. exact (EQ_MP (@lem3914147) (@lem3914145)). Qed.
Lemma lem3914149 : term251 = True.
Proof. exact (TRANS (@lem3914144) (@lem3914148)). Qed.
Lemma lem3914150 : True = term251.
Proof. exact (SYM (@lem3914149)). Qed.
Lemma lem3914151 : term251.
Proof. exact (EQ_MP (@lem3914150) (@lem0)). Qed.
Lemma lem3914152 : term474 = term477.
Proof. exact (@lem3914141 (@lem3914151)). Qed.
Lemma lem3914154 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914155 : term208 = term209.
Proof. exact (@lem3914154 term11 term11). Qed.
Lemma lem3914156 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914157 : term211 = term11.
Proof. exact (EQ_MP (@lem3914156) (@lem940073)). Qed.
Lemma lem3914158 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914159 : term209 = term143.
Proof. exact (MK_COMB (@lem3914158) (@lem3914157)). Qed.
Lemma lem3914160 : term208 = term143.
Proof. exact (TRANS (@lem3914155) (@lem3914159)). Qed.
Lemma lem3914162 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914163 : term263 = term133.
Proof. exact (@lem3914162 term11). Qed.
Lemma lem3914164 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914165 : term478 = term472.
Proof. exact (MK_COMB (@lem3914164) (@lem3914163)). Qed.
Lemma lem3914166 : term477 = term251.
Proof. exact (MK_COMB (@lem3914165) (@lem3914160)). Qed.
Lemma lem3914168 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914169 : term251 = term252.
Proof. exact (@lem3914168 (NUMERAL 0) term11). Qed.
Lemma lem3914170 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914171 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914172 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914171 h1) (fun h1 : term252 = True => @lem3914170)). Qed.
Lemma lem3914173 : term252 = True.
Proof. exact (EQ_MP (@lem3914172) (@lem3914170)). Qed.
Lemma lem3914174 : term251 = True.
Proof. exact (TRANS (@lem3914169) (@lem3914173)). Qed.
Lemma lem3914175 : term477 = True.
Proof. exact (TRANS (@lem3914166) (@lem3914174)). Qed.
Lemma lem3914176 : term474 = True.
Proof. exact (TRANS (@lem3914152) (@lem3914175)). Qed.
Lemma lem3914177 : term251 = True.
Proof. exact (TRANS (@lem3914129) (@lem3914176)). Qed.
Lemma lem3914178 : term471 = True.
Proof. exact (TRANS (@lem3914120) (@lem3914177)). Qed.
Lemma lem3914179 : True = term471.
Proof. exact (SYM (@lem3914178)). Qed.
Lemma lem3914180 : term471.
Proof. exact (EQ_MP (@lem3914179) (@lem0)). Qed.
Lemma lem3914181 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term479 _45438 _45439.
Proof. exact (conj (@lem3914180) (@lem3914117 _45438 _45439 h1)). Qed.
Lemma lem3914183 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3914184 (_45438 : int) (_45439 : int) : term481 _45438 _45439.
Proof. exact (@lem3914183 term143 (term277 _45438 _45439)). Qed.
Lemma lem3914185 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term482 _45438 _45439.
Proof. exact (@lem3914184 _45438 _45439 (@lem3914181 _45438 _45439 h1)). Qed.
Lemma lem3914186 (_45438 : int) (_45439 : int) : (term483 _45438 _45439) = (term277 _45438 _45439).
Proof. exact (@lem1982733 (term277 _45438 _45439)). Qed.
Lemma lem3914187 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3914188 (_45438 : int) (_45439 : int) : (term484 _45438 _45439) = (term279 _45438 _45439).
Proof. exact (MK_COMB (@lem3914187) (@lem3914186 _45438 _45439)). Qed.
Lemma lem3914189 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914190 (_45438 : int) (_45439 : int) : (term482 _45438 _45439) = (term280 _45438 _45439).
Proof. exact (MK_COMB (@lem3914188 _45438 _45439) (@lem3914189)). Qed.
Lemma lem3914191 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term280 _45438 _45439.
Proof. exact (EQ_MP (@lem3914190 _45438 _45439) (@lem3914185 _45438 _45439 h1)). Qed.
Lemma lem3914193 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3914194 (_45438 : int) (_45439 : int) : term486 _45438 _45439.
Proof. exact (@lem3914193 (term236 _45438 _45439)). Qed.
Lemma lem3914195 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term487 _45438 _45439.
Proof. exact (@lem3914194 _45438 _45439 (@lem3914115 _45438 _45439 h1)). Qed.
Lemma lem3914196 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term488 _45438 _45439.
Proof. exact (@lem3914195 _45438 _45439 h1 term143). Qed.
Lemma lem3914197 (_45438 : int) (_45439 : int) : (term488 _45438 _45439) = ((term489 _45438 _45439) = term133).
Proof. exact (eq_refl (term488 _45438 _45439)). Qed.
Lemma lem3914198 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : (term489 _45438 _45439) = term133.
Proof. exact (EQ_MP (@lem3914197 _45438 _45439) (@lem3914196 _45438 _45439 h1)). Qed.
Lemma lem3914199 (_45438 : int) (_45439 : int) : (term489 _45438 _45439) = (term236 _45438 _45439).
Proof. exact (@lem1982733 (term236 _45438 _45439)). Qed.
Lemma lem3914200 : (@eq real) = (@eq real).
Proof. exact (eq_refl (@eq real)). Qed.
Lemma lem3914201 (_45438 : int) (_45439 : int) : (term490 _45438 _45439) = (term239 _45438 _45439).
Proof. exact (MK_COMB (@lem3914200) (@lem3914199 _45438 _45439)). Qed.
Lemma lem3914202 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914203 (_45438 : int) (_45439 : int) : ((term489 _45438 _45439) = term133) = ((term236 _45438 _45439) = term133).
Proof. exact (MK_COMB (@lem3914201 _45438 _45439) (@lem3914202)). Qed.
Lemma lem3914204 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : (term236 _45438 _45439) = term133.
Proof. exact (EQ_MP (@lem3914203 _45438 _45439) (@lem3914198 _45438 _45439 h1)). Qed.
Lemma lem3914205 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term491 _45438 _45439.
Proof. exact (conj (@lem3914204 _45438 _45439 h1) (@lem3914191 _45438 _45439 h1)). Qed.
Lemma lem3914207 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3914208 (_45438 : int) (_45439 : int) : term493 _45438 _45439.
Proof. exact (@lem3914207 (term236 _45438 _45439) (term277 _45438 _45439)). Qed.
Lemma lem3914209 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term494 _45438 _45439.
Proof. exact (@lem3914208 _45438 _45439 (@lem3914205 _45438 _45439 h1)). Qed.
Lemma lem3914210 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = (term496 _45438 _45439).
Proof. exact (@lem1982753 (term237 _45438) (real_of_int _45438) (term299 _45439) (term237 _45439)). Qed.
Lemma lem3914211 (_45438 : int) : (term497 _45438) = (term498 _45438).
Proof. exact (@lem1982713 term199 (real_of_int _45438)). Qed.
Lemma lem3914213 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914214 : term143 = term224.
Proof. exact (@lem3914213 term11). Qed.
Lemma lem3914216 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3914217 : term199 = term200.
Proof. exact (@lem3914216 term11). Qed.
Lemma lem3914218 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914219 : term499 = term500.
Proof. exact (MK_COMB (@lem3914218) (@lem3914217)). Qed.
Lemma lem3914220 : term501 = term502.
Proof. exact (MK_COMB (@lem3914219) (@lem3914214)). Qed.
Lemma lem3914221 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3914223 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914224 : term251 = term252.
Proof. exact (@lem3914223 (NUMERAL 0) term11). Qed.
Lemma lem3914225 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914226 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914227 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914226 h1) (fun h1 : term252 = True => @lem3914225)). Qed.
Lemma lem3914228 : term252 = True.
Proof. exact (EQ_MP (@lem3914227) (@lem3914225)). Qed.
Lemma lem3914229 : term251 = True.
Proof. exact (TRANS (@lem3914224) (@lem3914228)). Qed.
Lemma lem3914230 : True = term251.
Proof. exact (SYM (@lem3914229)). Qed.
Lemma lem3914231 : term251.
Proof. exact (EQ_MP (@lem3914230) (@lem0)). Qed.
Lemma lem3914232 : term504.
Proof. exact (@lem3914221 (@lem3914231)). Qed.
Lemma lem3914234 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914235 : term251 = term252.
Proof. exact (@lem3914234 (NUMERAL 0) term11). Qed.
Lemma lem3914236 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914237 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914238 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914237 h1) (fun h1 : term252 = True => @lem3914236)). Qed.
Lemma lem3914239 : term252 = True.
Proof. exact (EQ_MP (@lem3914238) (@lem3914236)). Qed.
Lemma lem3914240 : term251 = True.
Proof. exact (TRANS (@lem3914235) (@lem3914239)). Qed.
Lemma lem3914241 : True = term251.
Proof. exact (SYM (@lem3914240)). Qed.
Lemma lem3914242 : term251.
Proof. exact (EQ_MP (@lem3914241) (@lem0)). Qed.
Lemma lem3914243 : term505.
Proof. exact (@lem3914232 (@lem3914242)). Qed.
Lemma lem3914245 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914246 : term251 = term252.
Proof. exact (@lem3914245 (NUMERAL 0) term11). Qed.
Lemma lem3914247 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914248 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914249 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914248 h1) (fun h1 : term252 = True => @lem3914247)). Qed.
Lemma lem3914250 : term252 = True.
Proof. exact (EQ_MP (@lem3914249) (@lem3914247)). Qed.
Lemma lem3914251 : term251 = True.
Proof. exact (TRANS (@lem3914246) (@lem3914250)). Qed.
Lemma lem3914252 : True = term251.
Proof. exact (SYM (@lem3914251)). Qed.
Lemma lem3914253 : term251.
Proof. exact (EQ_MP (@lem3914252) (@lem0)). Qed.
Lemma lem3914254 : term506.
Proof. exact (@lem3914243 (@lem3914253)). Qed.
Lemma lem3914256 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914257 : term208 = term209.
Proof. exact (@lem3914256 term11 term11). Qed.
Lemma lem3914258 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914259 : term211 = term11.
Proof. exact (EQ_MP (@lem3914258) (@lem940073)). Qed.
Lemma lem3914260 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914261 : term209 = term143.
Proof. exact (MK_COMB (@lem3914260) (@lem3914259)). Qed.
Lemma lem3914262 : term208 = term143.
Proof. exact (TRANS (@lem3914257) (@lem3914261)). Qed.
Lemma lem3914264 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3914265 : term225 = term230.
Proof. exact (@lem3914264 term11 term11). Qed.
Lemma lem3914266 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914267 : term211 = term11.
Proof. exact (EQ_MP (@lem3914266) (@lem940073)). Qed.
Lemma lem3914268 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914269 : term209 = term143.
Proof. exact (MK_COMB (@lem3914268) (@lem3914267)). Qed.
Lemma lem3914270 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3914271 : term230 = term199.
Proof. exact (MK_COMB (@lem3914270) (@lem3914269)). Qed.
Lemma lem3914272 : term225 = term199.
Proof. exact (TRANS (@lem3914265) (@lem3914271)). Qed.
Lemma lem3914273 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914274 : term507 = term499.
Proof. exact (MK_COMB (@lem3914273) (@lem3914272)). Qed.
Lemma lem3914275 : term508 = term501.
Proof. exact (MK_COMB (@lem3914274) (@lem3914262)). Qed.
Lemma lem3914277 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3914278 : term501 = term133.
Proof. exact (@lem3914277 term11). Qed.
Lemma lem3914279 : term508 = term133.
Proof. exact (TRANS (@lem3914275) (@lem3914278)). Qed.
Lemma lem3914280 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914281 : term510 = term261.
Proof. exact (MK_COMB (@lem3914280) (@lem3914279)). Qed.
Lemma lem3914282 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3914283 : term511 = term263.
Proof. exact (MK_COMB (@lem3914281) (@lem3914282)). Qed.
Lemma lem3914285 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914286 : term263 = term133.
Proof. exact (@lem3914285 term11). Qed.
Lemma lem3914287 : term511 = term133.
Proof. exact (TRANS (@lem3914283) (@lem3914286)). Qed.
Lemma lem3914289 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914290 : term208 = term209.
Proof. exact (@lem3914289 term11 term11). Qed.
Lemma lem3914291 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914292 : term211 = term11.
Proof. exact (EQ_MP (@lem3914291) (@lem940073)). Qed.
Lemma lem3914293 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914294 : term209 = term143.
Proof. exact (MK_COMB (@lem3914293) (@lem3914292)). Qed.
Lemma lem3914295 : term208 = term143.
Proof. exact (TRANS (@lem3914290) (@lem3914294)). Qed.
Lemma lem3914296 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3914297 : term265 = term263.
Proof. exact (MK_COMB (@lem3914296) (@lem3914295)). Qed.
Lemma lem3914299 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914300 : term263 = term133.
Proof. exact (@lem3914299 term11). Qed.
Lemma lem3914301 : term265 = term133.
Proof. exact (TRANS (@lem3914297) (@lem3914300)). Qed.
Lemma lem3914302 : term133 = term265.
Proof. exact (SYM (@lem3914301)). Qed.
Lemma lem3914303 : term511 = term265.
Proof. exact (TRANS (@lem3914287) (@lem3914302)). Qed.
Lemma lem3914304 : term502 = term196.
Proof. exact (@lem3914254 (@lem3914303)). Qed.
Lemma lem3914305 : term501 = term196.
Proof. exact (TRANS (@lem3914220) (@lem3914304)). Qed.
Lemma lem3914307 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3914308 : term196 = term133.
Proof. exact (@lem3914307 term133). Qed.
Lemma lem3914309 : term501 = term133.
Proof. exact (TRANS (@lem3914305) (@lem3914308)). Qed.
Lemma lem3914310 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914311 : term512 = term261.
Proof. exact (MK_COMB (@lem3914310) (@lem3914309)). Qed.
Lemma lem3914312 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3914313 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3914311) (@lem3914312 _45438)). Qed.
Lemma lem3914314 (_45438 : int) : (term497 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3914211 _45438) (@lem3914313 _45438)). Qed.
Lemma lem3914315 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3914316 (_45438 : int) : (term497 _45438) = term133.
Proof. exact (TRANS (@lem3914314 _45438) (@lem3914315 _45438)). Qed.
Lemma lem3914317 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914318 (_45438 : int) : (term514 _45438) = term175.
Proof. exact (MK_COMB (@lem3914317) (@lem3914316 _45438)). Qed.
Lemma lem3914319 (_45439 : int) : (term515 _45439) = (term516 _45439).
Proof. exact (@lem1982759 (real_of_int _45439) (term237 _45439) term199). Qed.
Lemma lem3914320 (_45439 : int) : (term517 _45439) = (term498 _45439).
Proof. exact (@lem1982715 term199 (real_of_int _45439)). Qed.
Lemma lem3914322 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914323 : term143 = term224.
Proof. exact (@lem3914322 term11). Qed.
Lemma lem3914325 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3914326 : term199 = term200.
Proof. exact (@lem3914325 term11). Qed.
Lemma lem3914327 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914328 : term499 = term500.
Proof. exact (MK_COMB (@lem3914327) (@lem3914326)). Qed.
Lemma lem3914329 : term501 = term502.
Proof. exact (MK_COMB (@lem3914328) (@lem3914323)). Qed.
Lemma lem3914330 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3914332 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914333 : term251 = term252.
Proof. exact (@lem3914332 (NUMERAL 0) term11). Qed.
Lemma lem3914334 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914335 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914336 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914335 h1) (fun h1 : term252 = True => @lem3914334)). Qed.
Lemma lem3914337 : term252 = True.
Proof. exact (EQ_MP (@lem3914336) (@lem3914334)). Qed.
Lemma lem3914338 : term251 = True.
Proof. exact (TRANS (@lem3914333) (@lem3914337)). Qed.
Lemma lem3914339 : True = term251.
Proof. exact (SYM (@lem3914338)). Qed.
Lemma lem3914340 : term251.
Proof. exact (EQ_MP (@lem3914339) (@lem0)). Qed.
Lemma lem3914341 : term504.
Proof. exact (@lem3914330 (@lem3914340)). Qed.
Lemma lem3914343 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914344 : term251 = term252.
Proof. exact (@lem3914343 (NUMERAL 0) term11). Qed.
Lemma lem3914345 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914346 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914347 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914346 h1) (fun h1 : term252 = True => @lem3914345)). Qed.
Lemma lem3914348 : term252 = True.
Proof. exact (EQ_MP (@lem3914347) (@lem3914345)). Qed.
Lemma lem3914349 : term251 = True.
Proof. exact (TRANS (@lem3914344) (@lem3914348)). Qed.
Lemma lem3914350 : True = term251.
Proof. exact (SYM (@lem3914349)). Qed.
Lemma lem3914351 : term251.
Proof. exact (EQ_MP (@lem3914350) (@lem0)). Qed.
Lemma lem3914352 : term505.
Proof. exact (@lem3914341 (@lem3914351)). Qed.
Lemma lem3914354 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914355 : term251 = term252.
Proof. exact (@lem3914354 (NUMERAL 0) term11). Qed.
Lemma lem3914356 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914357 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914358 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914357 h1) (fun h1 : term252 = True => @lem3914356)). Qed.
Lemma lem3914359 : term252 = True.
Proof. exact (EQ_MP (@lem3914358) (@lem3914356)). Qed.
Lemma lem3914360 : term251 = True.
Proof. exact (TRANS (@lem3914355) (@lem3914359)). Qed.
Lemma lem3914361 : True = term251.
Proof. exact (SYM (@lem3914360)). Qed.
Lemma lem3914362 : term251.
Proof. exact (EQ_MP (@lem3914361) (@lem0)). Qed.
Lemma lem3914363 : term506.
Proof. exact (@lem3914352 (@lem3914362)). Qed.
Lemma lem3914365 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914366 : term208 = term209.
Proof. exact (@lem3914365 term11 term11). Qed.
Lemma lem3914367 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914368 : term211 = term11.
Proof. exact (EQ_MP (@lem3914367) (@lem940073)). Qed.
Lemma lem3914369 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914370 : term209 = term143.
Proof. exact (MK_COMB (@lem3914369) (@lem3914368)). Qed.
Lemma lem3914371 : term208 = term143.
Proof. exact (TRANS (@lem3914366) (@lem3914370)). Qed.
Lemma lem3914373 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3914374 : term225 = term230.
Proof. exact (@lem3914373 term11 term11). Qed.
Lemma lem3914375 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914376 : term211 = term11.
Proof. exact (EQ_MP (@lem3914375) (@lem940073)). Qed.
Lemma lem3914377 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914378 : term209 = term143.
Proof. exact (MK_COMB (@lem3914377) (@lem3914376)). Qed.
Lemma lem3914379 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3914380 : term230 = term199.
Proof. exact (MK_COMB (@lem3914379) (@lem3914378)). Qed.
Lemma lem3914381 : term225 = term199.
Proof. exact (TRANS (@lem3914374) (@lem3914380)). Qed.
Lemma lem3914382 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914383 : term507 = term499.
Proof. exact (MK_COMB (@lem3914382) (@lem3914381)). Qed.
Lemma lem3914384 : term508 = term501.
Proof. exact (MK_COMB (@lem3914383) (@lem3914371)). Qed.
Lemma lem3914386 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3914387 : term501 = term133.
Proof. exact (@lem3914386 term11). Qed.
Lemma lem3914388 : term508 = term133.
Proof. exact (TRANS (@lem3914384) (@lem3914387)). Qed.
Lemma lem3914389 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914390 : term510 = term261.
Proof. exact (MK_COMB (@lem3914389) (@lem3914388)). Qed.
Lemma lem3914391 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3914392 : term511 = term263.
Proof. exact (MK_COMB (@lem3914390) (@lem3914391)). Qed.
Lemma lem3914394 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914395 : term263 = term133.
Proof. exact (@lem3914394 term11). Qed.
Lemma lem3914396 : term511 = term133.
Proof. exact (TRANS (@lem3914392) (@lem3914395)). Qed.
Lemma lem3914398 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914399 : term208 = term209.
Proof. exact (@lem3914398 term11 term11). Qed.
Lemma lem3914400 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914401 : term211 = term11.
Proof. exact (EQ_MP (@lem3914400) (@lem940073)). Qed.
Lemma lem3914402 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914403 : term209 = term143.
Proof. exact (MK_COMB (@lem3914402) (@lem3914401)). Qed.
Lemma lem3914404 : term208 = term143.
Proof. exact (TRANS (@lem3914399) (@lem3914403)). Qed.
Lemma lem3914405 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3914406 : term265 = term263.
Proof. exact (MK_COMB (@lem3914405) (@lem3914404)). Qed.
Lemma lem3914408 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914409 : term263 = term133.
Proof. exact (@lem3914408 term11). Qed.
Lemma lem3914410 : term265 = term133.
Proof. exact (TRANS (@lem3914406) (@lem3914409)). Qed.
Lemma lem3914411 : term133 = term265.
Proof. exact (SYM (@lem3914410)). Qed.
Lemma lem3914412 : term511 = term265.
Proof. exact (TRANS (@lem3914396) (@lem3914411)). Qed.
Lemma lem3914413 : term502 = term196.
Proof. exact (@lem3914363 (@lem3914412)). Qed.
Lemma lem3914414 : term501 = term196.
Proof. exact (TRANS (@lem3914329) (@lem3914413)). Qed.
Lemma lem3914416 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3914417 : term196 = term133.
Proof. exact (@lem3914416 term133). Qed.
Lemma lem3914418 : term501 = term133.
Proof. exact (TRANS (@lem3914414) (@lem3914417)). Qed.
Lemma lem3914419 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914420 : term512 = term261.
Proof. exact (MK_COMB (@lem3914419) (@lem3914418)). Qed.
Lemma lem3914421 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3914422 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3914420) (@lem3914421 _45439)). Qed.
Lemma lem3914423 (_45439 : int) : (term517 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3914320 _45439) (@lem3914422 _45439)). Qed.
Lemma lem3914424 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3914425 (_45439 : int) : (term517 _45439) = term133.
Proof. exact (TRANS (@lem3914423 _45439) (@lem3914424 _45439)). Qed.
Lemma lem3914426 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914427 (_45439 : int) : (term518 _45439) = term175.
Proof. exact (MK_COMB (@lem3914426) (@lem3914425 _45439)). Qed.
Lemma lem3914428 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3914429 (_45439 : int) : (term516 _45439) = term519.
Proof. exact (MK_COMB (@lem3914427 _45439) (@lem3914428)). Qed.
Lemma lem3914430 (_45439 : int) : (term515 _45439) = term519.
Proof. exact (TRANS (@lem3914319 _45439) (@lem3914429 _45439)). Qed.
Lemma lem3914431 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3914432 (_45439 : int) : (term515 _45439) = term199.
Proof. exact (TRANS (@lem3914430 _45439) (@lem3914431)). Qed.
Lemma lem3914433 (_45438 : int) (_45439 : int) : (term496 _45438 _45439) = term519.
Proof. exact (MK_COMB (@lem3914318 _45438) (@lem3914432 _45439)). Qed.
Lemma lem3914434 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = term519.
Proof. exact (TRANS (@lem3914210 _45438 _45439) (@lem3914433 _45438 _45439)). Qed.
Lemma lem3914435 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3914436 (_45438 : int) (_45439 : int) : (term495 _45438 _45439) = term199.
Proof. exact (TRANS (@lem3914434 _45438 _45439) (@lem3914435)). Qed.
Lemma lem3914437 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3914438 (_45438 : int) (_45439 : int) : (term520 _45438 _45439) = term521.
Proof. exact (MK_COMB (@lem3914437) (@lem3914436 _45438 _45439)). Qed.
Lemma lem3914439 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914440 (_45438 : int) (_45439 : int) : (term494 _45438 _45439) = term522.
Proof. exact (MK_COMB (@lem3914438 _45438 _45439) (@lem3914439)). Qed.
Lemma lem3914441 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3914440 _45438 _45439) (@lem3914209 _45438 _45439 h1)). Qed.
Lemma lem3914443 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3914444 : term522 = term523.
Proof. exact (@lem3914443 term133 term199). Qed.
Lemma lem3914446 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3914447 : term199 = term200.
Proof. exact (@lem3914446 term11). Qed.
Lemma lem3914449 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914450 : term133 = term196.
Proof. exact (@lem3914449 (NUMERAL 0)). Qed.
Lemma lem3914451 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3914452 : term135 = term524.
Proof. exact (MK_COMB (@lem3914451) (@lem3914450)). Qed.
Lemma lem3914453 : term523 = term525.
Proof. exact (MK_COMB (@lem3914452) (@lem3914447)). Qed.
Lemma lem3914454 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3914456 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914457 : term251 = term252.
Proof. exact (@lem3914456 (NUMERAL 0) term11). Qed.
Lemma lem3914458 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914459 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914460 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914459 h1) (fun h1 : term252 = True => @lem3914458)). Qed.
Lemma lem3914461 : term252 = True.
Proof. exact (EQ_MP (@lem3914460) (@lem3914458)). Qed.
Lemma lem3914462 : term251 = True.
Proof. exact (TRANS (@lem3914457) (@lem3914461)). Qed.
Lemma lem3914463 : True = term251.
Proof. exact (SYM (@lem3914462)). Qed.
Lemma lem3914464 : term251.
Proof. exact (EQ_MP (@lem3914463) (@lem0)). Qed.
Lemma lem3914465 : term527.
Proof. exact (@lem3914454 (@lem3914464)). Qed.
Lemma lem3914467 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914468 : term251 = term252.
Proof. exact (@lem3914467 (NUMERAL 0) term11). Qed.
Lemma lem3914469 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914470 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914471 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914470 h1) (fun h1 : term252 = True => @lem3914469)). Qed.
Lemma lem3914472 : term252 = True.
Proof. exact (EQ_MP (@lem3914471) (@lem3914469)). Qed.
Lemma lem3914473 : term251 = True.
Proof. exact (TRANS (@lem3914468) (@lem3914472)). Qed.
Lemma lem3914474 : True = term251.
Proof. exact (SYM (@lem3914473)). Qed.
Lemma lem3914475 : term251.
Proof. exact (EQ_MP (@lem3914474) (@lem0)). Qed.
Lemma lem3914476 : term525 = term528.
Proof. exact (@lem3914465 (@lem3914475)). Qed.
Lemma lem3914478 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3914479 : term225 = term230.
Proof. exact (@lem3914478 term11 term11). Qed.
Lemma lem3914480 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914481 : term211 = term11.
Proof. exact (EQ_MP (@lem3914480) (@lem940073)). Qed.
Lemma lem3914482 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914483 : term209 = term143.
Proof. exact (MK_COMB (@lem3914482) (@lem3914481)). Qed.
Lemma lem3914484 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3914485 : term230 = term199.
Proof. exact (MK_COMB (@lem3914484) (@lem3914483)). Qed.
Lemma lem3914486 : term225 = term199.
Proof. exact (TRANS (@lem3914479) (@lem3914485)). Qed.
Lemma lem3914488 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914489 : term263 = term133.
Proof. exact (@lem3914488 term11). Qed.
Lemma lem3914490 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3914491 : term529 = term135.
Proof. exact (MK_COMB (@lem3914490) (@lem3914489)). Qed.
Lemma lem3914492 : term528 = term523.
Proof. exact (MK_COMB (@lem3914491) (@lem3914486)). Qed.
Lemma lem3914494 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3914495 : term523 = term532.
Proof. exact (@lem3914494 (NUMERAL 0) term11). Qed.
Lemma lem3914496 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914497 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3914498 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914497 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3914496)). Qed.
Lemma lem3914499 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3914498) (@lem3914496)). Qed.
Lemma lem3914500 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3914501 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3914502 : term533 = (and True).
Proof. exact (MK_COMB (@lem3914501) (@lem3914500)). Qed.
Lemma lem3914503 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3914502) (@lem3914499)). Qed.
Lemma lem3914505 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3914506 : term532 = False.
Proof. exact (TRANS (@lem3914503) (@lem3914505)). Qed.
Lemma lem3914507 : term523 = False.
Proof. exact (TRANS (@lem3914495) (@lem3914506)). Qed.
Lemma lem3914508 : term528 = False.
Proof. exact (TRANS (@lem3914492) (@lem3914507)). Qed.
Lemma lem3914509 : term525 = False.
Proof. exact (TRANS (@lem3914476) (@lem3914508)). Qed.
Lemma lem3914510 : term523 = False.
Proof. exact (TRANS (@lem3914453) (@lem3914509)). Qed.
Lemma lem3914511 : term522 = False.
Proof. exact (TRANS (@lem3914444) (@lem3914510)). Qed.
Lemma lem3914512 (_45438 : int) (_45439 : int) (h1 : term620 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3914511) (@lem3914441 _45438 _45439 h1)). Qed.
Lemma lem3914513 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term621 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3914514 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term434 _45438 _45439.
Proof. exact (proj2 (@lem3914513 _45438 _45439 h1)). Qed.
Lemma lem3914516 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term385 _45438 _45439.
Proof. exact (proj2 (@lem3914514 _45438 _45439 h1)). Qed.
Lemma lem3914518 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term335 _45438 _45439.
Proof. exact (proj2 (@lem3914516 _45438 _45439 h1)). Qed.
Lemma lem3914519 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term272 _45439 _45438.
Proof. exact (proj1 (@lem3914516 _45438 _45439 h1)). Qed.
Lemma lem3914520 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : (real_of_int _45438) = term133.
Proof. exact (proj2 (@lem3914519 _45438 _45439 h1)). Qed.
Lemma lem3914522 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term302 _45439.
Proof. exact (proj2 (@lem3914518 _45438 _45439 h1)). Qed.
Lemma lem3914523 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term280 _45438 _45439.
Proof. exact (proj1 (@lem3914518 _45438 _45439 h1)). Qed.
Lemma lem3914525 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3914526 : term471 = term251.
Proof. exact (@lem3914525 term133 term143). Qed.
Lemma lem3914528 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914529 : term143 = term224.
Proof. exact (@lem3914528 term11). Qed.
Lemma lem3914531 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914532 : term133 = term196.
Proof. exact (@lem3914531 (NUMERAL 0)). Qed.
Lemma lem3914533 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914534 : term472 = term473.
Proof. exact (MK_COMB (@lem3914533) (@lem3914532)). Qed.
Lemma lem3914535 : term251 = term474.
Proof. exact (MK_COMB (@lem3914534) (@lem3914529)). Qed.
Lemma lem3914536 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3914538 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914539 : term251 = term252.
Proof. exact (@lem3914538 (NUMERAL 0) term11). Qed.
Lemma lem3914540 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914541 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914542 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914541 h1) (fun h1 : term252 = True => @lem3914540)). Qed.
Lemma lem3914543 : term252 = True.
Proof. exact (EQ_MP (@lem3914542) (@lem3914540)). Qed.
Lemma lem3914544 : term251 = True.
Proof. exact (TRANS (@lem3914539) (@lem3914543)). Qed.
Lemma lem3914545 : True = term251.
Proof. exact (SYM (@lem3914544)). Qed.
Lemma lem3914546 : term251.
Proof. exact (EQ_MP (@lem3914545) (@lem0)). Qed.
Lemma lem3914547 : term476.
Proof. exact (@lem3914536 (@lem3914546)). Qed.
Lemma lem3914549 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914550 : term251 = term252.
Proof. exact (@lem3914549 (NUMERAL 0) term11). Qed.
Lemma lem3914551 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914552 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914553 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914552 h1) (fun h1 : term252 = True => @lem3914551)). Qed.
Lemma lem3914554 : term252 = True.
Proof. exact (EQ_MP (@lem3914553) (@lem3914551)). Qed.
Lemma lem3914555 : term251 = True.
Proof. exact (TRANS (@lem3914550) (@lem3914554)). Qed.
Lemma lem3914556 : True = term251.
Proof. exact (SYM (@lem3914555)). Qed.
Lemma lem3914557 : term251.
Proof. exact (EQ_MP (@lem3914556) (@lem0)). Qed.
Lemma lem3914558 : term474 = term477.
Proof. exact (@lem3914547 (@lem3914557)). Qed.
Lemma lem3914560 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914561 : term208 = term209.
Proof. exact (@lem3914560 term11 term11). Qed.
Lemma lem3914562 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914563 : term211 = term11.
Proof. exact (EQ_MP (@lem3914562) (@lem940073)). Qed.
Lemma lem3914564 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914565 : term209 = term143.
Proof. exact (MK_COMB (@lem3914564) (@lem3914563)). Qed.
Lemma lem3914566 : term208 = term143.
Proof. exact (TRANS (@lem3914561) (@lem3914565)). Qed.
Lemma lem3914568 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914569 : term263 = term133.
Proof. exact (@lem3914568 term11). Qed.
Lemma lem3914570 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914571 : term478 = term472.
Proof. exact (MK_COMB (@lem3914570) (@lem3914569)). Qed.
Lemma lem3914572 : term477 = term251.
Proof. exact (MK_COMB (@lem3914571) (@lem3914566)). Qed.
Lemma lem3914574 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914575 : term251 = term252.
Proof. exact (@lem3914574 (NUMERAL 0) term11). Qed.
Lemma lem3914576 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914577 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914578 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914577 h1) (fun h1 : term252 = True => @lem3914576)). Qed.
Lemma lem3914579 : term252 = True.
Proof. exact (EQ_MP (@lem3914578) (@lem3914576)). Qed.
Lemma lem3914580 : term251 = True.
Proof. exact (TRANS (@lem3914575) (@lem3914579)). Qed.
Lemma lem3914581 : term477 = True.
Proof. exact (TRANS (@lem3914572) (@lem3914580)). Qed.
Lemma lem3914582 : term474 = True.
Proof. exact (TRANS (@lem3914558) (@lem3914581)). Qed.
Lemma lem3914583 : term251 = True.
Proof. exact (TRANS (@lem3914535) (@lem3914582)). Qed.
Lemma lem3914584 : term471 = True.
Proof. exact (TRANS (@lem3914526) (@lem3914583)). Qed.
Lemma lem3914585 : True = term471.
Proof. exact (SYM (@lem3914584)). Qed.
Lemma lem3914586 : term471.
Proof. exact (EQ_MP (@lem3914585) (@lem0)). Qed.
Lemma lem3914587 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term551 _45439.
Proof. exact (conj (@lem3914586) (@lem3914522 _45438 _45439 h1)). Qed.
Lemma lem3914589 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3914590 (_45439 : int) : term552 _45439.
Proof. exact (@lem3914589 term143 (term299 _45439)). Qed.
Lemma lem3914591 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term553 _45439.
Proof. exact (@lem3914590 _45439 (@lem3914587 _45438 _45439 h1)). Qed.
Lemma lem3914592 (_45439 : int) : (term554 _45439) = (term299 _45439).
Proof. exact (@lem1982733 (term299 _45439)). Qed.
Lemma lem3914593 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3914594 (_45439 : int) : (term555 _45439) = (term301 _45439).
Proof. exact (MK_COMB (@lem3914593) (@lem3914592 _45439)). Qed.
Lemma lem3914595 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914596 (_45439 : int) : (term553 _45439) = (term302 _45439).
Proof. exact (MK_COMB (@lem3914594 _45439) (@lem3914595)). Qed.
Lemma lem3914597 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term302 _45439.
Proof. exact (EQ_MP (@lem3914596 _45439) (@lem3914591 _45438 _45439 h1)). Qed.
Lemma lem3914599 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3914600 : term471 = term251.
Proof. exact (@lem3914599 term133 term143). Qed.
Lemma lem3914602 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914603 : term143 = term224.
Proof. exact (@lem3914602 term11). Qed.
Lemma lem3914605 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914606 : term133 = term196.
Proof. exact (@lem3914605 (NUMERAL 0)). Qed.
Lemma lem3914607 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914608 : term472 = term473.
Proof. exact (MK_COMB (@lem3914607) (@lem3914606)). Qed.
Lemma lem3914609 : term251 = term474.
Proof. exact (MK_COMB (@lem3914608) (@lem3914603)). Qed.
Lemma lem3914610 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3914612 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914613 : term251 = term252.
Proof. exact (@lem3914612 (NUMERAL 0) term11). Qed.
Lemma lem3914614 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914615 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914616 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914615 h1) (fun h1 : term252 = True => @lem3914614)). Qed.
Lemma lem3914617 : term252 = True.
Proof. exact (EQ_MP (@lem3914616) (@lem3914614)). Qed.
Lemma lem3914618 : term251 = True.
Proof. exact (TRANS (@lem3914613) (@lem3914617)). Qed.
Lemma lem3914619 : True = term251.
Proof. exact (SYM (@lem3914618)). Qed.
Lemma lem3914620 : term251.
Proof. exact (EQ_MP (@lem3914619) (@lem0)). Qed.
Lemma lem3914621 : term476.
Proof. exact (@lem3914610 (@lem3914620)). Qed.
Lemma lem3914623 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914624 : term251 = term252.
Proof. exact (@lem3914623 (NUMERAL 0) term11). Qed.
Lemma lem3914625 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914626 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914627 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914626 h1) (fun h1 : term252 = True => @lem3914625)). Qed.
Lemma lem3914628 : term252 = True.
Proof. exact (EQ_MP (@lem3914627) (@lem3914625)). Qed.
Lemma lem3914629 : term251 = True.
Proof. exact (TRANS (@lem3914624) (@lem3914628)). Qed.
Lemma lem3914630 : True = term251.
Proof. exact (SYM (@lem3914629)). Qed.
Lemma lem3914631 : term251.
Proof. exact (EQ_MP (@lem3914630) (@lem0)). Qed.
Lemma lem3914632 : term474 = term477.
Proof. exact (@lem3914621 (@lem3914631)). Qed.
Lemma lem3914634 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914635 : term208 = term209.
Proof. exact (@lem3914634 term11 term11). Qed.
Lemma lem3914636 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914637 : term211 = term11.
Proof. exact (EQ_MP (@lem3914636) (@lem940073)). Qed.
Lemma lem3914638 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914639 : term209 = term143.
Proof. exact (MK_COMB (@lem3914638) (@lem3914637)). Qed.
Lemma lem3914640 : term208 = term143.
Proof. exact (TRANS (@lem3914635) (@lem3914639)). Qed.
Lemma lem3914642 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914643 : term263 = term133.
Proof. exact (@lem3914642 term11). Qed.
Lemma lem3914644 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914645 : term478 = term472.
Proof. exact (MK_COMB (@lem3914644) (@lem3914643)). Qed.
Lemma lem3914646 : term477 = term251.
Proof. exact (MK_COMB (@lem3914645) (@lem3914640)). Qed.
Lemma lem3914648 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914649 : term251 = term252.
Proof. exact (@lem3914648 (NUMERAL 0) term11). Qed.
Lemma lem3914650 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914651 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914652 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914651 h1) (fun h1 : term252 = True => @lem3914650)). Qed.
Lemma lem3914653 : term252 = True.
Proof. exact (EQ_MP (@lem3914652) (@lem3914650)). Qed.
Lemma lem3914654 : term251 = True.
Proof. exact (TRANS (@lem3914649) (@lem3914653)). Qed.
Lemma lem3914655 : term477 = True.
Proof. exact (TRANS (@lem3914646) (@lem3914654)). Qed.
Lemma lem3914656 : term474 = True.
Proof. exact (TRANS (@lem3914632) (@lem3914655)). Qed.
Lemma lem3914657 : term251 = True.
Proof. exact (TRANS (@lem3914609) (@lem3914656)). Qed.
Lemma lem3914658 : term471 = True.
Proof. exact (TRANS (@lem3914600) (@lem3914657)). Qed.
Lemma lem3914659 : True = term471.
Proof. exact (SYM (@lem3914658)). Qed.
Lemma lem3914660 : term471.
Proof. exact (EQ_MP (@lem3914659) (@lem0)). Qed.
Lemma lem3914661 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term479 _45438 _45439.
Proof. exact (conj (@lem3914660) (@lem3914523 _45438 _45439 h1)). Qed.
Lemma lem3914663 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3914664 (_45438 : int) (_45439 : int) : term481 _45438 _45439.
Proof. exact (@lem3914663 term143 (term277 _45438 _45439)). Qed.
Lemma lem3914665 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term482 _45438 _45439.
Proof. exact (@lem3914664 _45438 _45439 (@lem3914661 _45438 _45439 h1)). Qed.
Lemma lem3914666 (_45438 : int) (_45439 : int) : (term483 _45438 _45439) = (term277 _45438 _45439).
Proof. exact (@lem1982733 (term277 _45438 _45439)). Qed.
Lemma lem3914667 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3914668 (_45438 : int) (_45439 : int) : (term484 _45438 _45439) = (term279 _45438 _45439).
Proof. exact (MK_COMB (@lem3914667) (@lem3914666 _45438 _45439)). Qed.
Lemma lem3914669 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914670 (_45438 : int) (_45439 : int) : (term482 _45438 _45439) = (term280 _45438 _45439).
Proof. exact (MK_COMB (@lem3914668 _45438 _45439) (@lem3914669)). Qed.
Lemma lem3914671 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term280 _45438 _45439.
Proof. exact (EQ_MP (@lem3914670 _45438 _45439) (@lem3914665 _45438 _45439 h1)). Qed.
Lemma lem3914673 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3914674 (_45438 : int) : term539 _45438.
Proof. exact (@lem3914673 (real_of_int _45438)). Qed.
Lemma lem3914675 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term540 _45438.
Proof. exact (@lem3914674 _45438 (@lem3914520 _45438 _45439 h1)). Qed.
Lemma lem3914676 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term556 _45438.
Proof. exact (@lem3914675 _45438 _45439 h1 term199). Qed.
Lemma lem3914677 (_45438 : int) : (term556 _45438) = ((term237 _45438) = term133).
Proof. exact (eq_refl (term556 _45438)). Qed.
Lemma lem3914684 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : (term237 _45438) = term133.
Proof. exact (EQ_MP (@lem3914677 _45438) (@lem3914676 _45438 _45439 h1)). Qed.
Lemma lem3914685 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term557 _45438 _45439.
Proof. exact (conj (@lem3914684 _45438 _45439 h1) (@lem3914671 _45438 _45439 h1)). Qed.
Lemma lem3914687 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3914688 (_45438 : int) (_45439 : int) : term558 _45438 _45439.
Proof. exact (@lem3914687 (term237 _45438) (term277 _45438 _45439)). Qed.
Lemma lem3914689 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term559 _45438 _45439.
Proof. exact (@lem3914688 _45438 _45439 (@lem3914685 _45438 _45439 h1)). Qed.
Lemma lem3914690 (_45438 : int) (_45439 : int) : (term560 _45438 _45439) = (term561 _45438 _45439).
Proof. exact (@lem1982763 (term237 _45438) (real_of_int _45438) (term237 _45439)). Qed.
Lemma lem3914691 (_45438 : int) : (term497 _45438) = (term498 _45438).
Proof. exact (@lem1982713 term199 (real_of_int _45438)). Qed.
Lemma lem3914693 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914694 : term143 = term224.
Proof. exact (@lem3914693 term11). Qed.
Lemma lem3914696 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3914697 : term199 = term200.
Proof. exact (@lem3914696 term11). Qed.
Lemma lem3914698 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914699 : term499 = term500.
Proof. exact (MK_COMB (@lem3914698) (@lem3914697)). Qed.
Lemma lem3914700 : term501 = term502.
Proof. exact (MK_COMB (@lem3914699) (@lem3914694)). Qed.
Lemma lem3914701 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3914703 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914704 : term251 = term252.
Proof. exact (@lem3914703 (NUMERAL 0) term11). Qed.
Lemma lem3914705 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914706 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914707 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914706 h1) (fun h1 : term252 = True => @lem3914705)). Qed.
Lemma lem3914708 : term252 = True.
Proof. exact (EQ_MP (@lem3914707) (@lem3914705)). Qed.
Lemma lem3914709 : term251 = True.
Proof. exact (TRANS (@lem3914704) (@lem3914708)). Qed.
Lemma lem3914710 : True = term251.
Proof. exact (SYM (@lem3914709)). Qed.
Lemma lem3914711 : term251.
Proof. exact (EQ_MP (@lem3914710) (@lem0)). Qed.
Lemma lem3914712 : term504.
Proof. exact (@lem3914701 (@lem3914711)). Qed.
Lemma lem3914714 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914715 : term251 = term252.
Proof. exact (@lem3914714 (NUMERAL 0) term11). Qed.
Lemma lem3914716 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914717 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914718 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914717 h1) (fun h1 : term252 = True => @lem3914716)). Qed.
Lemma lem3914719 : term252 = True.
Proof. exact (EQ_MP (@lem3914718) (@lem3914716)). Qed.
Lemma lem3914720 : term251 = True.
Proof. exact (TRANS (@lem3914715) (@lem3914719)). Qed.
Lemma lem3914721 : True = term251.
Proof. exact (SYM (@lem3914720)). Qed.
Lemma lem3914722 : term251.
Proof. exact (EQ_MP (@lem3914721) (@lem0)). Qed.
Lemma lem3914723 : term505.
Proof. exact (@lem3914712 (@lem3914722)). Qed.
Lemma lem3914725 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914726 : term251 = term252.
Proof. exact (@lem3914725 (NUMERAL 0) term11). Qed.
Lemma lem3914727 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914728 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914729 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914728 h1) (fun h1 : term252 = True => @lem3914727)). Qed.
Lemma lem3914730 : term252 = True.
Proof. exact (EQ_MP (@lem3914729) (@lem3914727)). Qed.
Lemma lem3914731 : term251 = True.
Proof. exact (TRANS (@lem3914726) (@lem3914730)). Qed.
Lemma lem3914732 : True = term251.
Proof. exact (SYM (@lem3914731)). Qed.
Lemma lem3914733 : term251.
Proof. exact (EQ_MP (@lem3914732) (@lem0)). Qed.
Lemma lem3914734 : term506.
Proof. exact (@lem3914723 (@lem3914733)). Qed.
Lemma lem3914736 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914737 : term208 = term209.
Proof. exact (@lem3914736 term11 term11). Qed.
Lemma lem3914738 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914739 : term211 = term11.
Proof. exact (EQ_MP (@lem3914738) (@lem940073)). Qed.
Lemma lem3914740 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914741 : term209 = term143.
Proof. exact (MK_COMB (@lem3914740) (@lem3914739)). Qed.
Lemma lem3914742 : term208 = term143.
Proof. exact (TRANS (@lem3914737) (@lem3914741)). Qed.
Lemma lem3914744 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3914745 : term225 = term230.
Proof. exact (@lem3914744 term11 term11). Qed.
Lemma lem3914746 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914747 : term211 = term11.
Proof. exact (EQ_MP (@lem3914746) (@lem940073)). Qed.
Lemma lem3914748 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914749 : term209 = term143.
Proof. exact (MK_COMB (@lem3914748) (@lem3914747)). Qed.
Lemma lem3914750 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3914751 : term230 = term199.
Proof. exact (MK_COMB (@lem3914750) (@lem3914749)). Qed.
Lemma lem3914752 : term225 = term199.
Proof. exact (TRANS (@lem3914745) (@lem3914751)). Qed.
Lemma lem3914753 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914754 : term507 = term499.
Proof. exact (MK_COMB (@lem3914753) (@lem3914752)). Qed.
Lemma lem3914755 : term508 = term501.
Proof. exact (MK_COMB (@lem3914754) (@lem3914742)). Qed.
Lemma lem3914757 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3914758 : term501 = term133.
Proof. exact (@lem3914757 term11). Qed.
Lemma lem3914759 : term508 = term133.
Proof. exact (TRANS (@lem3914755) (@lem3914758)). Qed.
Lemma lem3914760 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914761 : term510 = term261.
Proof. exact (MK_COMB (@lem3914760) (@lem3914759)). Qed.
Lemma lem3914762 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3914763 : term511 = term263.
Proof. exact (MK_COMB (@lem3914761) (@lem3914762)). Qed.
Lemma lem3914765 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914766 : term263 = term133.
Proof. exact (@lem3914765 term11). Qed.
Lemma lem3914767 : term511 = term133.
Proof. exact (TRANS (@lem3914763) (@lem3914766)). Qed.
Lemma lem3914769 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914770 : term208 = term209.
Proof. exact (@lem3914769 term11 term11). Qed.
Lemma lem3914771 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914772 : term211 = term11.
Proof. exact (EQ_MP (@lem3914771) (@lem940073)). Qed.
Lemma lem3914773 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914774 : term209 = term143.
Proof. exact (MK_COMB (@lem3914773) (@lem3914772)). Qed.
Lemma lem3914775 : term208 = term143.
Proof. exact (TRANS (@lem3914770) (@lem3914774)). Qed.
Lemma lem3914776 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3914777 : term265 = term263.
Proof. exact (MK_COMB (@lem3914776) (@lem3914775)). Qed.
Lemma lem3914779 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914780 : term263 = term133.
Proof. exact (@lem3914779 term11). Qed.
Lemma lem3914781 : term265 = term133.
Proof. exact (TRANS (@lem3914777) (@lem3914780)). Qed.
Lemma lem3914782 : term133 = term265.
Proof. exact (SYM (@lem3914781)). Qed.
Lemma lem3914783 : term511 = term265.
Proof. exact (TRANS (@lem3914767) (@lem3914782)). Qed.
Lemma lem3914784 : term502 = term196.
Proof. exact (@lem3914734 (@lem3914783)). Qed.
Lemma lem3914785 : term501 = term196.
Proof. exact (TRANS (@lem3914700) (@lem3914784)). Qed.
Lemma lem3914787 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3914788 : term196 = term133.
Proof. exact (@lem3914787 term133). Qed.
Lemma lem3914789 : term501 = term133.
Proof. exact (TRANS (@lem3914785) (@lem3914788)). Qed.
Lemma lem3914790 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914791 : term512 = term261.
Proof. exact (MK_COMB (@lem3914790) (@lem3914789)). Qed.
Lemma lem3914792 (_45438 : int) : (real_of_int _45438) = (real_of_int _45438).
Proof. exact (eq_refl (real_of_int _45438)). Qed.
Lemma lem3914793 (_45438 : int) : (term498 _45438) = (term513 _45438).
Proof. exact (MK_COMB (@lem3914791) (@lem3914792 _45438)). Qed.
Lemma lem3914794 (_45438 : int) : (term497 _45438) = (term513 _45438).
Proof. exact (TRANS (@lem3914691 _45438) (@lem3914793 _45438)). Qed.
Lemma lem3914795 (_45438 : int) : (term513 _45438) = term133.
Proof. exact (@lem1982719 (real_of_int _45438)). Qed.
Lemma lem3914796 (_45438 : int) : (term497 _45438) = term133.
Proof. exact (TRANS (@lem3914794 _45438) (@lem3914795 _45438)). Qed.
Lemma lem3914797 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914798 (_45438 : int) : (term514 _45438) = term175.
Proof. exact (MK_COMB (@lem3914797) (@lem3914796 _45438)). Qed.
Lemma lem3914799 (_45439 : int) : (term237 _45439) = (term237 _45439).
Proof. exact (eq_refl (term237 _45439)). Qed.
Lemma lem3914800 (_45438 : int) (_45439 : int) : (term561 _45438 _45439) = (term562 _45439).
Proof. exact (MK_COMB (@lem3914798 _45438) (@lem3914799 _45439)). Qed.
Lemma lem3914801 (_45438 : int) (_45439 : int) : (term560 _45438 _45439) = (term562 _45439).
Proof. exact (TRANS (@lem3914690 _45438 _45439) (@lem3914800 _45438 _45439)). Qed.
Lemma lem3914802 (_45439 : int) : (term562 _45439) = (term237 _45439).
Proof. exact (@lem1982721 (term237 _45439)). Qed.
Lemma lem3914803 (_45438 : int) (_45439 : int) : (term560 _45438 _45439) = (term237 _45439).
Proof. exact (TRANS (@lem3914801 _45438 _45439) (@lem3914802 _45439)). Qed.
Lemma lem3914804 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3914805 (_45438 : int) (_45439 : int) : (term563 _45438 _45439) = (term268 _45439).
Proof. exact (MK_COMB (@lem3914804) (@lem3914803 _45438 _45439)). Qed.
Lemma lem3914806 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914807 (_45438 : int) (_45439 : int) : (term559 _45438 _45439) = (term269 _45439).
Proof. exact (MK_COMB (@lem3914805 _45438 _45439) (@lem3914806)). Qed.
Lemma lem3914808 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term269 _45439.
Proof. exact (EQ_MP (@lem3914807 _45438 _45439) (@lem3914689 _45438 _45439 h1)). Qed.
Lemma lem3914810 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3914811 : term471 = term251.
Proof. exact (@lem3914810 term133 term143). Qed.
Lemma lem3914813 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914814 : term143 = term224.
Proof. exact (@lem3914813 term11). Qed.
Lemma lem3914816 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914817 : term133 = term196.
Proof. exact (@lem3914816 (NUMERAL 0)). Qed.
Lemma lem3914818 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914819 : term472 = term473.
Proof. exact (MK_COMB (@lem3914818) (@lem3914817)). Qed.
Lemma lem3914820 : term251 = term474.
Proof. exact (MK_COMB (@lem3914819) (@lem3914814)). Qed.
Lemma lem3914821 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3914823 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914824 : term251 = term252.
Proof. exact (@lem3914823 (NUMERAL 0) term11). Qed.
Lemma lem3914825 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914826 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914827 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914826 h1) (fun h1 : term252 = True => @lem3914825)). Qed.
Lemma lem3914828 : term252 = True.
Proof. exact (EQ_MP (@lem3914827) (@lem3914825)). Qed.
Lemma lem3914829 : term251 = True.
Proof. exact (TRANS (@lem3914824) (@lem3914828)). Qed.
Lemma lem3914830 : True = term251.
Proof. exact (SYM (@lem3914829)). Qed.
Lemma lem3914831 : term251.
Proof. exact (EQ_MP (@lem3914830) (@lem0)). Qed.
Lemma lem3914832 : term476.
Proof. exact (@lem3914821 (@lem3914831)). Qed.
Lemma lem3914834 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914835 : term251 = term252.
Proof. exact (@lem3914834 (NUMERAL 0) term11). Qed.
Lemma lem3914836 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914837 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914838 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914837 h1) (fun h1 : term252 = True => @lem3914836)). Qed.
Lemma lem3914839 : term252 = True.
Proof. exact (EQ_MP (@lem3914838) (@lem3914836)). Qed.
Lemma lem3914840 : term251 = True.
Proof. exact (TRANS (@lem3914835) (@lem3914839)). Qed.
Lemma lem3914841 : True = term251.
Proof. exact (SYM (@lem3914840)). Qed.
Lemma lem3914842 : term251.
Proof. exact (EQ_MP (@lem3914841) (@lem0)). Qed.
Lemma lem3914843 : term474 = term477.
Proof. exact (@lem3914832 (@lem3914842)). Qed.
Lemma lem3914845 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914846 : term208 = term209.
Proof. exact (@lem3914845 term11 term11). Qed.
Lemma lem3914847 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914848 : term211 = term11.
Proof. exact (EQ_MP (@lem3914847) (@lem940073)). Qed.
Lemma lem3914849 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914850 : term209 = term143.
Proof. exact (MK_COMB (@lem3914849) (@lem3914848)). Qed.
Lemma lem3914851 : term208 = term143.
Proof. exact (TRANS (@lem3914846) (@lem3914850)). Qed.
Lemma lem3914853 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914854 : term263 = term133.
Proof. exact (@lem3914853 term11). Qed.
Lemma lem3914855 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3914856 : term478 = term472.
Proof. exact (MK_COMB (@lem3914855) (@lem3914854)). Qed.
Lemma lem3914857 : term477 = term251.
Proof. exact (MK_COMB (@lem3914856) (@lem3914851)). Qed.
Lemma lem3914859 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914860 : term251 = term252.
Proof. exact (@lem3914859 (NUMERAL 0) term11). Qed.
Lemma lem3914861 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914862 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914863 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914862 h1) (fun h1 : term252 = True => @lem3914861)). Qed.
Lemma lem3914864 : term252 = True.
Proof. exact (EQ_MP (@lem3914863) (@lem3914861)). Qed.
Lemma lem3914865 : term251 = True.
Proof. exact (TRANS (@lem3914860) (@lem3914864)). Qed.
Lemma lem3914866 : term477 = True.
Proof. exact (TRANS (@lem3914857) (@lem3914865)). Qed.
Lemma lem3914867 : term474 = True.
Proof. exact (TRANS (@lem3914843) (@lem3914866)). Qed.
Lemma lem3914868 : term251 = True.
Proof. exact (TRANS (@lem3914820) (@lem3914867)). Qed.
Lemma lem3914869 : term471 = True.
Proof. exact (TRANS (@lem3914811) (@lem3914868)). Qed.
Lemma lem3914870 : True = term471.
Proof. exact (SYM (@lem3914869)). Qed.
Lemma lem3914871 : term471.
Proof. exact (EQ_MP (@lem3914870) (@lem0)). Qed.
Lemma lem3914872 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term564 _45439.
Proof. exact (conj (@lem3914871) (@lem3914808 _45438 _45439 h1)). Qed.
Lemma lem3914874 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3914875 (_45439 : int) : term565 _45439.
Proof. exact (@lem3914874 term143 (term237 _45439)). Qed.
Lemma lem3914876 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term566 _45439.
Proof. exact (@lem3914875 _45439 (@lem3914872 _45438 _45439 h1)). Qed.
Lemma lem3914877 (_45439 : int) : (term567 _45439) = (term237 _45439).
Proof. exact (@lem1982733 (term237 _45439)). Qed.
Lemma lem3914878 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3914879 (_45439 : int) : (term568 _45439) = (term268 _45439).
Proof. exact (MK_COMB (@lem3914878) (@lem3914877 _45439)). Qed.
Lemma lem3914880 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3914881 (_45439 : int) : (term566 _45439) = (term269 _45439).
Proof. exact (MK_COMB (@lem3914879 _45439) (@lem3914880)). Qed.
Lemma lem3914882 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term269 _45439.
Proof. exact (EQ_MP (@lem3914881 _45439) (@lem3914876 _45438 _45439 h1)). Qed.
Lemma lem3914883 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term569 _45439.
Proof. exact (conj (@lem3914882 _45438 _45439 h1) (@lem3914597 _45438 _45439 h1)). Qed.
Lemma lem3914885 (x : real) (y : real) : term570 x y.
Proof. exact (proj1 (@lem1988342 x y)). Qed.
Lemma lem3914886 (_45439 : int) : term571 _45439.
Proof. exact (@lem3914885 (term237 _45439) (term299 _45439)). Qed.
Lemma lem3914887 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term572 _45439.
Proof. exact (@lem3914886 _45439 (@lem3914883 _45438 _45439 h1)). Qed.
Lemma lem3914888 (_45439 : int) : (term573 _45439) = (term574 _45439).
Proof. exact (@lem1982763 (term237 _45439) (real_of_int _45439) term199). Qed.
Lemma lem3914889 (_45439 : int) : (term497 _45439) = (term498 _45439).
Proof. exact (@lem1982713 term199 (real_of_int _45439)). Qed.
Lemma lem3914891 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3914892 : term143 = term224.
Proof. exact (@lem3914891 term11). Qed.
Lemma lem3914894 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3914895 : term199 = term200.
Proof. exact (@lem3914894 term11). Qed.
Lemma lem3914896 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914897 : term499 = term500.
Proof. exact (MK_COMB (@lem3914896) (@lem3914895)). Qed.
Lemma lem3914898 : term501 = term502.
Proof. exact (MK_COMB (@lem3914897) (@lem3914892)). Qed.
Lemma lem3914899 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3914901 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914902 : term251 = term252.
Proof. exact (@lem3914901 (NUMERAL 0) term11). Qed.
Lemma lem3914903 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914904 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914905 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914904 h1) (fun h1 : term252 = True => @lem3914903)). Qed.
Lemma lem3914906 : term252 = True.
Proof. exact (EQ_MP (@lem3914905) (@lem3914903)). Qed.
Lemma lem3914907 : term251 = True.
Proof. exact (TRANS (@lem3914902) (@lem3914906)). Qed.
Lemma lem3914908 : True = term251.
Proof. exact (SYM (@lem3914907)). Qed.
Lemma lem3914909 : term251.
Proof. exact (EQ_MP (@lem3914908) (@lem0)). Qed.
Lemma lem3914910 : term504.
Proof. exact (@lem3914899 (@lem3914909)). Qed.
Lemma lem3914912 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914913 : term251 = term252.
Proof. exact (@lem3914912 (NUMERAL 0) term11). Qed.
Lemma lem3914914 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914915 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914916 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914915 h1) (fun h1 : term252 = True => @lem3914914)). Qed.
Lemma lem3914917 : term252 = True.
Proof. exact (EQ_MP (@lem3914916) (@lem3914914)). Qed.
Lemma lem3914918 : term251 = True.
Proof. exact (TRANS (@lem3914913) (@lem3914917)). Qed.
Lemma lem3914919 : True = term251.
Proof. exact (SYM (@lem3914918)). Qed.
Lemma lem3914920 : term251.
Proof. exact (EQ_MP (@lem3914919) (@lem0)). Qed.
Lemma lem3914921 : term505.
Proof. exact (@lem3914910 (@lem3914920)). Qed.
Lemma lem3914923 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3914924 : term251 = term252.
Proof. exact (@lem3914923 (NUMERAL 0) term11). Qed.
Lemma lem3914925 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3914926 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3914927 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3914926 h1) (fun h1 : term252 = True => @lem3914925)). Qed.
Lemma lem3914928 : term252 = True.
Proof. exact (EQ_MP (@lem3914927) (@lem3914925)). Qed.
Lemma lem3914929 : term251 = True.
Proof. exact (TRANS (@lem3914924) (@lem3914928)). Qed.
Lemma lem3914930 : True = term251.
Proof. exact (SYM (@lem3914929)). Qed.
Lemma lem3914931 : term251.
Proof. exact (EQ_MP (@lem3914930) (@lem0)). Qed.
Lemma lem3914932 : term506.
Proof. exact (@lem3914921 (@lem3914931)). Qed.
Lemma lem3914934 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914935 : term208 = term209.
Proof. exact (@lem3914934 term11 term11). Qed.
Lemma lem3914936 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914937 : term211 = term11.
Proof. exact (EQ_MP (@lem3914936) (@lem940073)). Qed.
Lemma lem3914938 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914939 : term209 = term143.
Proof. exact (MK_COMB (@lem3914938) (@lem3914937)). Qed.
Lemma lem3914940 : term208 = term143.
Proof. exact (TRANS (@lem3914935) (@lem3914939)). Qed.
Lemma lem3914942 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3914943 : term225 = term230.
Proof. exact (@lem3914942 term11 term11). Qed.
Lemma lem3914944 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914945 : term211 = term11.
Proof. exact (EQ_MP (@lem3914944) (@lem940073)). Qed.
Lemma lem3914946 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914947 : term209 = term143.
Proof. exact (MK_COMB (@lem3914946) (@lem3914945)). Qed.
Lemma lem3914948 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3914949 : term230 = term199.
Proof. exact (MK_COMB (@lem3914948) (@lem3914947)). Qed.
Lemma lem3914950 : term225 = term199.
Proof. exact (TRANS (@lem3914943) (@lem3914949)). Qed.
Lemma lem3914951 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914952 : term507 = term499.
Proof. exact (MK_COMB (@lem3914951) (@lem3914950)). Qed.
Lemma lem3914953 : term508 = term501.
Proof. exact (MK_COMB (@lem3914952) (@lem3914940)). Qed.
Lemma lem3914955 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3914956 : term501 = term133.
Proof. exact (@lem3914955 term11). Qed.
Lemma lem3914957 : term508 = term133.
Proof. exact (TRANS (@lem3914953) (@lem3914956)). Qed.
Lemma lem3914958 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914959 : term510 = term261.
Proof. exact (MK_COMB (@lem3914958) (@lem3914957)). Qed.
Lemma lem3914960 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3914961 : term511 = term263.
Proof. exact (MK_COMB (@lem3914959) (@lem3914960)). Qed.
Lemma lem3914963 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914964 : term263 = term133.
Proof. exact (@lem3914963 term11). Qed.
Lemma lem3914965 : term511 = term133.
Proof. exact (TRANS (@lem3914961) (@lem3914964)). Qed.
Lemma lem3914967 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3914968 : term208 = term209.
Proof. exact (@lem3914967 term11 term11). Qed.
Lemma lem3914969 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3914970 : term211 = term11.
Proof. exact (EQ_MP (@lem3914969) (@lem940073)). Qed.
Lemma lem3914971 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3914972 : term209 = term143.
Proof. exact (MK_COMB (@lem3914971) (@lem3914970)). Qed.
Lemma lem3914973 : term208 = term143.
Proof. exact (TRANS (@lem3914968) (@lem3914972)). Qed.
Lemma lem3914974 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3914975 : term265 = term263.
Proof. exact (MK_COMB (@lem3914974) (@lem3914973)). Qed.
Lemma lem3914977 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3914978 : term263 = term133.
Proof. exact (@lem3914977 term11). Qed.
Lemma lem3914979 : term265 = term133.
Proof. exact (TRANS (@lem3914975) (@lem3914978)). Qed.
Lemma lem3914980 : term133 = term265.
Proof. exact (SYM (@lem3914979)). Qed.
Lemma lem3914981 : term511 = term265.
Proof. exact (TRANS (@lem3914965) (@lem3914980)). Qed.
Lemma lem3914982 : term502 = term196.
Proof. exact (@lem3914932 (@lem3914981)). Qed.
Lemma lem3914983 : term501 = term196.
Proof. exact (TRANS (@lem3914898) (@lem3914982)). Qed.
Lemma lem3914985 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3914986 : term196 = term133.
Proof. exact (@lem3914985 term133). Qed.
Lemma lem3914987 : term501 = term133.
Proof. exact (TRANS (@lem3914983) (@lem3914986)). Qed.
Lemma lem3914988 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3914989 : term512 = term261.
Proof. exact (MK_COMB (@lem3914988) (@lem3914987)). Qed.
Lemma lem3914990 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3914991 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3914989) (@lem3914990 _45439)). Qed.
Lemma lem3914992 (_45439 : int) : (term497 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3914889 _45439) (@lem3914991 _45439)). Qed.
Lemma lem3914993 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3914994 (_45439 : int) : (term497 _45439) = term133.
Proof. exact (TRANS (@lem3914992 _45439) (@lem3914993 _45439)). Qed.
Lemma lem3914995 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3914996 (_45439 : int) : (term514 _45439) = term175.
Proof. exact (MK_COMB (@lem3914995) (@lem3914994 _45439)). Qed.
Lemma lem3914997 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3914998 (_45439 : int) : (term574 _45439) = term519.
Proof. exact (MK_COMB (@lem3914996 _45439) (@lem3914997)). Qed.
Lemma lem3914999 (_45439 : int) : (term573 _45439) = term519.
Proof. exact (TRANS (@lem3914888 _45439) (@lem3914998 _45439)). Qed.
Lemma lem3915000 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3915001 (_45439 : int) : (term573 _45439) = term199.
Proof. exact (TRANS (@lem3914999 _45439) (@lem3915000)). Qed.
Lemma lem3915002 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3915003 (_45439 : int) : (term575 _45439) = term521.
Proof. exact (MK_COMB (@lem3915002) (@lem3915001 _45439)). Qed.
Lemma lem3915004 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3915005 (_45439 : int) : (term572 _45439) = term522.
Proof. exact (MK_COMB (@lem3915003 _45439) (@lem3915004)). Qed.
Lemma lem3915006 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3915005 _45439) (@lem3914887 _45438 _45439 h1)). Qed.
Lemma lem3915008 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3915009 : term522 = term523.
Proof. exact (@lem3915008 term133 term199). Qed.
Lemma lem3915011 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3915012 : term199 = term200.
Proof. exact (@lem3915011 term11). Qed.
Lemma lem3915014 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915015 : term133 = term196.
Proof. exact (@lem3915014 (NUMERAL 0)). Qed.
Lemma lem3915016 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3915017 : term135 = term524.
Proof. exact (MK_COMB (@lem3915016) (@lem3915015)). Qed.
Lemma lem3915018 : term523 = term525.
Proof. exact (MK_COMB (@lem3915017) (@lem3915012)). Qed.
Lemma lem3915019 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3915021 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915022 : term251 = term252.
Proof. exact (@lem3915021 (NUMERAL 0) term11). Qed.
Lemma lem3915023 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915024 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915025 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915024 h1) (fun h1 : term252 = True => @lem3915023)). Qed.
Lemma lem3915026 : term252 = True.
Proof. exact (EQ_MP (@lem3915025) (@lem3915023)). Qed.
Lemma lem3915027 : term251 = True.
Proof. exact (TRANS (@lem3915022) (@lem3915026)). Qed.
Lemma lem3915028 : True = term251.
Proof. exact (SYM (@lem3915027)). Qed.
Lemma lem3915029 : term251.
Proof. exact (EQ_MP (@lem3915028) (@lem0)). Qed.
Lemma lem3915030 : term527.
Proof. exact (@lem3915019 (@lem3915029)). Qed.
Lemma lem3915032 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915033 : term251 = term252.
Proof. exact (@lem3915032 (NUMERAL 0) term11). Qed.
Lemma lem3915034 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915035 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915036 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915035 h1) (fun h1 : term252 = True => @lem3915034)). Qed.
Lemma lem3915037 : term252 = True.
Proof. exact (EQ_MP (@lem3915036) (@lem3915034)). Qed.
Lemma lem3915038 : term251 = True.
Proof. exact (TRANS (@lem3915033) (@lem3915037)). Qed.
Lemma lem3915039 : True = term251.
Proof. exact (SYM (@lem3915038)). Qed.
Lemma lem3915040 : term251.
Proof. exact (EQ_MP (@lem3915039) (@lem0)). Qed.
Lemma lem3915041 : term525 = term528.
Proof. exact (@lem3915030 (@lem3915040)). Qed.
Lemma lem3915043 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3915044 : term225 = term230.
Proof. exact (@lem3915043 term11 term11). Qed.
Lemma lem3915045 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915046 : term211 = term11.
Proof. exact (EQ_MP (@lem3915045) (@lem940073)). Qed.
Lemma lem3915047 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915048 : term209 = term143.
Proof. exact (MK_COMB (@lem3915047) (@lem3915046)). Qed.
Lemma lem3915049 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3915050 : term230 = term199.
Proof. exact (MK_COMB (@lem3915049) (@lem3915048)). Qed.
Lemma lem3915051 : term225 = term199.
Proof. exact (TRANS (@lem3915044) (@lem3915050)). Qed.
Lemma lem3915053 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915054 : term263 = term133.
Proof. exact (@lem3915053 term11). Qed.
Lemma lem3915055 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3915056 : term529 = term135.
Proof. exact (MK_COMB (@lem3915055) (@lem3915054)). Qed.
Lemma lem3915057 : term528 = term523.
Proof. exact (MK_COMB (@lem3915056) (@lem3915051)). Qed.
Lemma lem3915059 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3915060 : term523 = term532.
Proof. exact (@lem3915059 (NUMERAL 0) term11). Qed.
Lemma lem3915061 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915062 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3915063 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915062 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3915061)). Qed.
Lemma lem3915064 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3915063) (@lem3915061)). Qed.
Lemma lem3915065 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3915066 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915067 : term533 = (and True).
Proof. exact (MK_COMB (@lem3915066) (@lem3915065)). Qed.
Lemma lem3915068 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3915067) (@lem3915064)). Qed.
Lemma lem3915070 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3915071 : term532 = False.
Proof. exact (TRANS (@lem3915068) (@lem3915070)). Qed.
Lemma lem3915072 : term523 = False.
Proof. exact (TRANS (@lem3915060) (@lem3915071)). Qed.
Lemma lem3915073 : term528 = False.
Proof. exact (TRANS (@lem3915057) (@lem3915072)). Qed.
Lemma lem3915074 : term525 = False.
Proof. exact (TRANS (@lem3915041) (@lem3915073)). Qed.
Lemma lem3915075 : term523 = False.
Proof. exact (TRANS (@lem3915018) (@lem3915074)). Qed.
Lemma lem3915076 : term522 = False.
Proof. exact (TRANS (@lem3915009) (@lem3915075)). Qed.
Lemma lem3915077 (_45438 : int) (_45439 : int) (h1 : term621 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3915076) (@lem3915006 _45438 _45439 h1)). Qed.
Lemma lem3915078 (_45438 : int) (_45439 : int) (h1 : term432 _45438 _45439) : False.
Proof. exact (or_elim (@lem3914108 _45438 _45439 h1) (fun h0 : term620 _45438 _45439 => @lem3914512 _45438 _45439 h0) (fun h0 : term621 _45438 _45439 => @lem3915077 _45438 _45439 h0)). Qed.
Lemma lem3915079 (_45438 : int) (_45439 : int) (h1 : term428 _45438 _45439) : term428 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3915080 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term622 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3915081 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term429 _45438 _45439.
Proof. exact (proj2 (@lem3915080 _45438 _45439 h1)). Qed.
Lemma lem3915083 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term380 _45438 _45439.
Proof. exact (proj2 (@lem3915081 _45438 _45439 h1)). Qed.
Lemma lem3915085 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term336 _45439.
Proof. exact (proj2 (@lem3915083 _45438 _45439 h1)). Qed.
Lemma lem3915087 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term302 _45439.
Proof. exact (proj2 (@lem3915085 _45438 _45439 h1)). Qed.
Lemma lem3915088 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (proj1 (@lem3915085 _45438 _45439 h1)). Qed.
Lemma lem3915090 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3915091 : term471 = term251.
Proof. exact (@lem3915090 term133 term143). Qed.
Lemma lem3915093 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915094 : term143 = term224.
Proof. exact (@lem3915093 term11). Qed.
Lemma lem3915096 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915097 : term133 = term196.
Proof. exact (@lem3915096 (NUMERAL 0)). Qed.
Lemma lem3915098 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3915099 : term472 = term473.
Proof. exact (MK_COMB (@lem3915098) (@lem3915097)). Qed.
Lemma lem3915100 : term251 = term474.
Proof. exact (MK_COMB (@lem3915099) (@lem3915094)). Qed.
Lemma lem3915101 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3915103 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915104 : term251 = term252.
Proof. exact (@lem3915103 (NUMERAL 0) term11). Qed.
Lemma lem3915105 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915106 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915107 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915106 h1) (fun h1 : term252 = True => @lem3915105)). Qed.
Lemma lem3915108 : term252 = True.
Proof. exact (EQ_MP (@lem3915107) (@lem3915105)). Qed.
Lemma lem3915109 : term251 = True.
Proof. exact (TRANS (@lem3915104) (@lem3915108)). Qed.
Lemma lem3915110 : True = term251.
Proof. exact (SYM (@lem3915109)). Qed.
Lemma lem3915111 : term251.
Proof. exact (EQ_MP (@lem3915110) (@lem0)). Qed.
Lemma lem3915112 : term476.
Proof. exact (@lem3915101 (@lem3915111)). Qed.
Lemma lem3915114 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915115 : term251 = term252.
Proof. exact (@lem3915114 (NUMERAL 0) term11). Qed.
Lemma lem3915116 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915117 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915118 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915117 h1) (fun h1 : term252 = True => @lem3915116)). Qed.
Lemma lem3915119 : term252 = True.
Proof. exact (EQ_MP (@lem3915118) (@lem3915116)). Qed.
Lemma lem3915120 : term251 = True.
Proof. exact (TRANS (@lem3915115) (@lem3915119)). Qed.
Lemma lem3915121 : True = term251.
Proof. exact (SYM (@lem3915120)). Qed.
Lemma lem3915122 : term251.
Proof. exact (EQ_MP (@lem3915121) (@lem0)). Qed.
Lemma lem3915123 : term474 = term477.
Proof. exact (@lem3915112 (@lem3915122)). Qed.
Lemma lem3915125 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3915126 : term208 = term209.
Proof. exact (@lem3915125 term11 term11). Qed.
Lemma lem3915127 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915128 : term211 = term11.
Proof. exact (EQ_MP (@lem3915127) (@lem940073)). Qed.
Lemma lem3915129 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915130 : term209 = term143.
Proof. exact (MK_COMB (@lem3915129) (@lem3915128)). Qed.
Lemma lem3915131 : term208 = term143.
Proof. exact (TRANS (@lem3915126) (@lem3915130)). Qed.
Lemma lem3915133 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915134 : term263 = term133.
Proof. exact (@lem3915133 term11). Qed.
Lemma lem3915135 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3915136 : term478 = term472.
Proof. exact (MK_COMB (@lem3915135) (@lem3915134)). Qed.
Lemma lem3915137 : term477 = term251.
Proof. exact (MK_COMB (@lem3915136) (@lem3915131)). Qed.
Lemma lem3915139 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915140 : term251 = term252.
Proof. exact (@lem3915139 (NUMERAL 0) term11). Qed.
Lemma lem3915141 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915142 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915143 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915142 h1) (fun h1 : term252 = True => @lem3915141)). Qed.
Lemma lem3915144 : term252 = True.
Proof. exact (EQ_MP (@lem3915143) (@lem3915141)). Qed.
Lemma lem3915145 : term251 = True.
Proof. exact (TRANS (@lem3915140) (@lem3915144)). Qed.
Lemma lem3915146 : term477 = True.
Proof. exact (TRANS (@lem3915137) (@lem3915145)). Qed.
Lemma lem3915147 : term474 = True.
Proof. exact (TRANS (@lem3915123) (@lem3915146)). Qed.
Lemma lem3915148 : term251 = True.
Proof. exact (TRANS (@lem3915100) (@lem3915147)). Qed.
Lemma lem3915149 : term471 = True.
Proof. exact (TRANS (@lem3915091) (@lem3915148)). Qed.
Lemma lem3915150 : True = term471.
Proof. exact (SYM (@lem3915149)). Qed.
Lemma lem3915151 : term471.
Proof. exact (EQ_MP (@lem3915150) (@lem0)). Qed.
Lemma lem3915152 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term551 _45439.
Proof. exact (conj (@lem3915151) (@lem3915087 _45438 _45439 h1)). Qed.
Lemma lem3915154 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3915155 (_45439 : int) : term552 _45439.
Proof. exact (@lem3915154 term143 (term299 _45439)). Qed.
Lemma lem3915156 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term553 _45439.
Proof. exact (@lem3915155 _45439 (@lem3915152 _45438 _45439 h1)). Qed.
Lemma lem3915157 (_45439 : int) : (term554 _45439) = (term299 _45439).
Proof. exact (@lem1982733 (term299 _45439)). Qed.
Lemma lem3915158 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3915159 (_45439 : int) : (term555 _45439) = (term301 _45439).
Proof. exact (MK_COMB (@lem3915158) (@lem3915157 _45439)). Qed.
Lemma lem3915160 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3915161 (_45439 : int) : (term553 _45439) = (term302 _45439).
Proof. exact (MK_COMB (@lem3915159 _45439) (@lem3915160)). Qed.
Lemma lem3915162 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term302 _45439.
Proof. exact (EQ_MP (@lem3915161 _45439) (@lem3915156 _45438 _45439 h1)). Qed.
Lemma lem3915164 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3915165 (_45439 : int) : term539 _45439.
Proof. exact (@lem3915164 (real_of_int _45439)). Qed.
Lemma lem3915166 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term540 _45439.
Proof. exact (@lem3915165 _45439 (@lem3915088 _45438 _45439 h1)). Qed.
Lemma lem3915167 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term556 _45439.
Proof. exact (@lem3915166 _45438 _45439 h1 term199). Qed.
Lemma lem3915168 (_45439 : int) : (term556 _45439) = ((term237 _45439) = term133).
Proof. exact (eq_refl (term556 _45439)). Qed.
Lemma lem3915175 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : (term237 _45439) = term133.
Proof. exact (EQ_MP (@lem3915168 _45439) (@lem3915167 _45438 _45439 h1)). Qed.
Lemma lem3915176 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term623 _45439.
Proof. exact (conj (@lem3915175 _45438 _45439 h1) (@lem3915162 _45438 _45439 h1)). Qed.
Lemma lem3915178 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3915179 (_45439 : int) : term624 _45439.
Proof. exact (@lem3915178 (term237 _45439) (term299 _45439)). Qed.
Lemma lem3915180 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term572 _45439.
Proof. exact (@lem3915179 _45439 (@lem3915176 _45438 _45439 h1)). Qed.
Lemma lem3915181 (_45439 : int) : (term573 _45439) = (term574 _45439).
Proof. exact (@lem1982763 (term237 _45439) (real_of_int _45439) term199). Qed.
Lemma lem3915182 (_45439 : int) : (term497 _45439) = (term498 _45439).
Proof. exact (@lem1982713 term199 (real_of_int _45439)). Qed.
Lemma lem3915184 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915185 : term143 = term224.
Proof. exact (@lem3915184 term11). Qed.
Lemma lem3915187 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3915188 : term199 = term200.
Proof. exact (@lem3915187 term11). Qed.
Lemma lem3915189 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3915190 : term499 = term500.
Proof. exact (MK_COMB (@lem3915189) (@lem3915188)). Qed.
Lemma lem3915191 : term501 = term502.
Proof. exact (MK_COMB (@lem3915190) (@lem3915185)). Qed.
Lemma lem3915192 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3915194 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915195 : term251 = term252.
Proof. exact (@lem3915194 (NUMERAL 0) term11). Qed.
Lemma lem3915196 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915197 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915198 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915197 h1) (fun h1 : term252 = True => @lem3915196)). Qed.
Lemma lem3915199 : term252 = True.
Proof. exact (EQ_MP (@lem3915198) (@lem3915196)). Qed.
Lemma lem3915200 : term251 = True.
Proof. exact (TRANS (@lem3915195) (@lem3915199)). Qed.
Lemma lem3915201 : True = term251.
Proof. exact (SYM (@lem3915200)). Qed.
Lemma lem3915202 : term251.
Proof. exact (EQ_MP (@lem3915201) (@lem0)). Qed.
Lemma lem3915203 : term504.
Proof. exact (@lem3915192 (@lem3915202)). Qed.
Lemma lem3915205 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915206 : term251 = term252.
Proof. exact (@lem3915205 (NUMERAL 0) term11). Qed.
Lemma lem3915207 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915208 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915209 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915208 h1) (fun h1 : term252 = True => @lem3915207)). Qed.
Lemma lem3915210 : term252 = True.
Proof. exact (EQ_MP (@lem3915209) (@lem3915207)). Qed.
Lemma lem3915211 : term251 = True.
Proof. exact (TRANS (@lem3915206) (@lem3915210)). Qed.
Lemma lem3915212 : True = term251.
Proof. exact (SYM (@lem3915211)). Qed.
Lemma lem3915213 : term251.
Proof. exact (EQ_MP (@lem3915212) (@lem0)). Qed.
Lemma lem3915214 : term505.
Proof. exact (@lem3915203 (@lem3915213)). Qed.
Lemma lem3915216 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915217 : term251 = term252.
Proof. exact (@lem3915216 (NUMERAL 0) term11). Qed.
Lemma lem3915218 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915219 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915220 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915219 h1) (fun h1 : term252 = True => @lem3915218)). Qed.
Lemma lem3915221 : term252 = True.
Proof. exact (EQ_MP (@lem3915220) (@lem3915218)). Qed.
Lemma lem3915222 : term251 = True.
Proof. exact (TRANS (@lem3915217) (@lem3915221)). Qed.
Lemma lem3915223 : True = term251.
Proof. exact (SYM (@lem3915222)). Qed.
Lemma lem3915224 : term251.
Proof. exact (EQ_MP (@lem3915223) (@lem0)). Qed.
Lemma lem3915225 : term506.
Proof. exact (@lem3915214 (@lem3915224)). Qed.
Lemma lem3915227 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3915228 : term208 = term209.
Proof. exact (@lem3915227 term11 term11). Qed.
Lemma lem3915229 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915230 : term211 = term11.
Proof. exact (EQ_MP (@lem3915229) (@lem940073)). Qed.
Lemma lem3915231 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915232 : term209 = term143.
Proof. exact (MK_COMB (@lem3915231) (@lem3915230)). Qed.
Lemma lem3915233 : term208 = term143.
Proof. exact (TRANS (@lem3915228) (@lem3915232)). Qed.
Lemma lem3915235 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3915236 : term225 = term230.
Proof. exact (@lem3915235 term11 term11). Qed.
Lemma lem3915237 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915238 : term211 = term11.
Proof. exact (EQ_MP (@lem3915237) (@lem940073)). Qed.
Lemma lem3915239 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915240 : term209 = term143.
Proof. exact (MK_COMB (@lem3915239) (@lem3915238)). Qed.
Lemma lem3915241 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3915242 : term230 = term199.
Proof. exact (MK_COMB (@lem3915241) (@lem3915240)). Qed.
Lemma lem3915243 : term225 = term199.
Proof. exact (TRANS (@lem3915236) (@lem3915242)). Qed.
Lemma lem3915244 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3915245 : term507 = term499.
Proof. exact (MK_COMB (@lem3915244) (@lem3915243)). Qed.
Lemma lem3915246 : term508 = term501.
Proof. exact (MK_COMB (@lem3915245) (@lem3915233)). Qed.
Lemma lem3915248 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3915249 : term501 = term133.
Proof. exact (@lem3915248 term11). Qed.
Lemma lem3915250 : term508 = term133.
Proof. exact (TRANS (@lem3915246) (@lem3915249)). Qed.
Lemma lem3915251 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3915252 : term510 = term261.
Proof. exact (MK_COMB (@lem3915251) (@lem3915250)). Qed.
Lemma lem3915253 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3915254 : term511 = term263.
Proof. exact (MK_COMB (@lem3915252) (@lem3915253)). Qed.
Lemma lem3915256 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915257 : term263 = term133.
Proof. exact (@lem3915256 term11). Qed.
Lemma lem3915258 : term511 = term133.
Proof. exact (TRANS (@lem3915254) (@lem3915257)). Qed.
Lemma lem3915260 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3915261 : term208 = term209.
Proof. exact (@lem3915260 term11 term11). Qed.
Lemma lem3915262 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915263 : term211 = term11.
Proof. exact (EQ_MP (@lem3915262) (@lem940073)). Qed.
Lemma lem3915264 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915265 : term209 = term143.
Proof. exact (MK_COMB (@lem3915264) (@lem3915263)). Qed.
Lemma lem3915266 : term208 = term143.
Proof. exact (TRANS (@lem3915261) (@lem3915265)). Qed.
Lemma lem3915267 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3915268 : term265 = term263.
Proof. exact (MK_COMB (@lem3915267) (@lem3915266)). Qed.
Lemma lem3915270 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915271 : term263 = term133.
Proof. exact (@lem3915270 term11). Qed.
Lemma lem3915272 : term265 = term133.
Proof. exact (TRANS (@lem3915268) (@lem3915271)). Qed.
Lemma lem3915273 : term133 = term265.
Proof. exact (SYM (@lem3915272)). Qed.
Lemma lem3915274 : term511 = term265.
Proof. exact (TRANS (@lem3915258) (@lem3915273)). Qed.
Lemma lem3915275 : term502 = term196.
Proof. exact (@lem3915225 (@lem3915274)). Qed.
Lemma lem3915276 : term501 = term196.
Proof. exact (TRANS (@lem3915191) (@lem3915275)). Qed.
Lemma lem3915278 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3915279 : term196 = term133.
Proof. exact (@lem3915278 term133). Qed.
Lemma lem3915280 : term501 = term133.
Proof. exact (TRANS (@lem3915276) (@lem3915279)). Qed.
Lemma lem3915281 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3915282 : term512 = term261.
Proof. exact (MK_COMB (@lem3915281) (@lem3915280)). Qed.
Lemma lem3915283 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3915284 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3915282) (@lem3915283 _45439)). Qed.
Lemma lem3915285 (_45439 : int) : (term497 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3915182 _45439) (@lem3915284 _45439)). Qed.
Lemma lem3915286 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3915287 (_45439 : int) : (term497 _45439) = term133.
Proof. exact (TRANS (@lem3915285 _45439) (@lem3915286 _45439)). Qed.
Lemma lem3915288 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3915289 (_45439 : int) : (term514 _45439) = term175.
Proof. exact (MK_COMB (@lem3915288) (@lem3915287 _45439)). Qed.
Lemma lem3915290 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3915291 (_45439 : int) : (term574 _45439) = term519.
Proof. exact (MK_COMB (@lem3915289 _45439) (@lem3915290)). Qed.
Lemma lem3915292 (_45439 : int) : (term573 _45439) = term519.
Proof. exact (TRANS (@lem3915181 _45439) (@lem3915291 _45439)). Qed.
Lemma lem3915293 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3915294 (_45439 : int) : (term573 _45439) = term199.
Proof. exact (TRANS (@lem3915292 _45439) (@lem3915293)). Qed.
Lemma lem3915295 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3915296 (_45439 : int) : (term575 _45439) = term521.
Proof. exact (MK_COMB (@lem3915295) (@lem3915294 _45439)). Qed.
Lemma lem3915297 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3915298 (_45439 : int) : (term572 _45439) = term522.
Proof. exact (MK_COMB (@lem3915296 _45439) (@lem3915297)). Qed.
Lemma lem3915299 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3915298 _45439) (@lem3915180 _45438 _45439 h1)). Qed.
Lemma lem3915301 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3915302 : term522 = term523.
Proof. exact (@lem3915301 term133 term199). Qed.
Lemma lem3915304 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3915305 : term199 = term200.
Proof. exact (@lem3915304 term11). Qed.
Lemma lem3915307 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915308 : term133 = term196.
Proof. exact (@lem3915307 (NUMERAL 0)). Qed.
Lemma lem3915309 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3915310 : term135 = term524.
Proof. exact (MK_COMB (@lem3915309) (@lem3915308)). Qed.
Lemma lem3915311 : term523 = term525.
Proof. exact (MK_COMB (@lem3915310) (@lem3915305)). Qed.
Lemma lem3915312 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3915314 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915315 : term251 = term252.
Proof. exact (@lem3915314 (NUMERAL 0) term11). Qed.
Lemma lem3915316 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915317 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915318 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915317 h1) (fun h1 : term252 = True => @lem3915316)). Qed.
Lemma lem3915319 : term252 = True.
Proof. exact (EQ_MP (@lem3915318) (@lem3915316)). Qed.
Lemma lem3915320 : term251 = True.
Proof. exact (TRANS (@lem3915315) (@lem3915319)). Qed.
Lemma lem3915321 : True = term251.
Proof. exact (SYM (@lem3915320)). Qed.
Lemma lem3915322 : term251.
Proof. exact (EQ_MP (@lem3915321) (@lem0)). Qed.
Lemma lem3915323 : term527.
Proof. exact (@lem3915312 (@lem3915322)). Qed.
Lemma lem3915325 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915326 : term251 = term252.
Proof. exact (@lem3915325 (NUMERAL 0) term11). Qed.
Lemma lem3915327 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915328 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915329 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915328 h1) (fun h1 : term252 = True => @lem3915327)). Qed.
Lemma lem3915330 : term252 = True.
Proof. exact (EQ_MP (@lem3915329) (@lem3915327)). Qed.
Lemma lem3915331 : term251 = True.
Proof. exact (TRANS (@lem3915326) (@lem3915330)). Qed.
Lemma lem3915332 : True = term251.
Proof. exact (SYM (@lem3915331)). Qed.
Lemma lem3915333 : term251.
Proof. exact (EQ_MP (@lem3915332) (@lem0)). Qed.
Lemma lem3915334 : term525 = term528.
Proof. exact (@lem3915323 (@lem3915333)). Qed.
Lemma lem3915336 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3915337 : term225 = term230.
Proof. exact (@lem3915336 term11 term11). Qed.
Lemma lem3915338 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915339 : term211 = term11.
Proof. exact (EQ_MP (@lem3915338) (@lem940073)). Qed.
Lemma lem3915340 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915341 : term209 = term143.
Proof. exact (MK_COMB (@lem3915340) (@lem3915339)). Qed.
Lemma lem3915342 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3915343 : term230 = term199.
Proof. exact (MK_COMB (@lem3915342) (@lem3915341)). Qed.
Lemma lem3915344 : term225 = term199.
Proof. exact (TRANS (@lem3915337) (@lem3915343)). Qed.
Lemma lem3915346 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915347 : term263 = term133.
Proof. exact (@lem3915346 term11). Qed.
Lemma lem3915348 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3915349 : term529 = term135.
Proof. exact (MK_COMB (@lem3915348) (@lem3915347)). Qed.
Lemma lem3915350 : term528 = term523.
Proof. exact (MK_COMB (@lem3915349) (@lem3915344)). Qed.
Lemma lem3915352 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3915353 : term523 = term532.
Proof. exact (@lem3915352 (NUMERAL 0) term11). Qed.
Lemma lem3915354 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915355 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3915356 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915355 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3915354)). Qed.
Lemma lem3915357 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3915356) (@lem3915354)). Qed.
Lemma lem3915358 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3915359 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915360 : term533 = (and True).
Proof. exact (MK_COMB (@lem3915359) (@lem3915358)). Qed.
Lemma lem3915361 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3915360) (@lem3915357)). Qed.
Lemma lem3915363 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3915364 : term532 = False.
Proof. exact (TRANS (@lem3915361) (@lem3915363)). Qed.
Lemma lem3915365 : term523 = False.
Proof. exact (TRANS (@lem3915353) (@lem3915364)). Qed.
Lemma lem3915366 : term528 = False.
Proof. exact (TRANS (@lem3915350) (@lem3915365)). Qed.
Lemma lem3915367 : term525 = False.
Proof. exact (TRANS (@lem3915334) (@lem3915366)). Qed.
Lemma lem3915368 : term523 = False.
Proof. exact (TRANS (@lem3915311) (@lem3915367)). Qed.
Lemma lem3915369 : term522 = False.
Proof. exact (TRANS (@lem3915302) (@lem3915368)). Qed.
Lemma lem3915370 (_45438 : int) (_45439 : int) (h1 : term622 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3915369) (@lem3915299 _45438 _45439 h1)). Qed.
Lemma lem3915371 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term625 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3915372 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term430 _45438 _45439.
Proof. exact (proj2 (@lem3915371 _45438 _45439 h1)). Qed.
Lemma lem3915374 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term381 _45438 _45439.
Proof. exact (proj2 (@lem3915372 _45438 _45439 h1)). Qed.
Lemma lem3915376 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term336 _45439.
Proof. exact (proj2 (@lem3915374 _45438 _45439 h1)). Qed.
Lemma lem3915380 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term302 _45439.
Proof. exact (proj2 (@lem3915376 _45438 _45439 h1)). Qed.
Lemma lem3915381 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : (real_of_int _45439) = term133.
Proof. exact (proj1 (@lem3915376 _45438 _45439 h1)). Qed.
Lemma lem3915383 (y : real) (x : real) : (real_gt x y) = (real_lt y x).
Proof. exact (EQ_MP (@lem1980266 y x) (@lem1980265 y x)). Qed.
Lemma lem3915384 : term471 = term251.
Proof. exact (@lem3915383 term133 term143). Qed.
Lemma lem3915386 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915387 : term143 = term224.
Proof. exact (@lem3915386 term11). Qed.
Lemma lem3915389 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915390 : term133 = term196.
Proof. exact (@lem3915389 (NUMERAL 0)). Qed.
Lemma lem3915391 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3915392 : term472 = term473.
Proof. exact (MK_COMB (@lem3915391) (@lem3915390)). Qed.
Lemma lem3915393 : term251 = term474.
Proof. exact (MK_COMB (@lem3915392) (@lem3915387)). Qed.
Lemma lem3915394 : term475.
Proof. exact (@lem1980255 term133 term143 term143 term143). Qed.
Lemma lem3915396 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915397 : term251 = term252.
Proof. exact (@lem3915396 (NUMERAL 0) term11). Qed.
Lemma lem3915398 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915399 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915400 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915399 h1) (fun h1 : term252 = True => @lem3915398)). Qed.
Lemma lem3915401 : term252 = True.
Proof. exact (EQ_MP (@lem3915400) (@lem3915398)). Qed.
Lemma lem3915402 : term251 = True.
Proof. exact (TRANS (@lem3915397) (@lem3915401)). Qed.
Lemma lem3915403 : True = term251.
Proof. exact (SYM (@lem3915402)). Qed.
Lemma lem3915404 : term251.
Proof. exact (EQ_MP (@lem3915403) (@lem0)). Qed.
Lemma lem3915405 : term476.
Proof. exact (@lem3915394 (@lem3915404)). Qed.
Lemma lem3915407 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915408 : term251 = term252.
Proof. exact (@lem3915407 (NUMERAL 0) term11). Qed.
Lemma lem3915409 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915410 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915411 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915410 h1) (fun h1 : term252 = True => @lem3915409)). Qed.
Lemma lem3915412 : term252 = True.
Proof. exact (EQ_MP (@lem3915411) (@lem3915409)). Qed.
Lemma lem3915413 : term251 = True.
Proof. exact (TRANS (@lem3915408) (@lem3915412)). Qed.
Lemma lem3915414 : True = term251.
Proof. exact (SYM (@lem3915413)). Qed.
Lemma lem3915415 : term251.
Proof. exact (EQ_MP (@lem3915414) (@lem0)). Qed.
Lemma lem3915416 : term474 = term477.
Proof. exact (@lem3915405 (@lem3915415)). Qed.
Lemma lem3915418 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3915419 : term208 = term209.
Proof. exact (@lem3915418 term11 term11). Qed.
Lemma lem3915420 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915421 : term211 = term11.
Proof. exact (EQ_MP (@lem3915420) (@lem940073)). Qed.
Lemma lem3915422 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915423 : term209 = term143.
Proof. exact (MK_COMB (@lem3915422) (@lem3915421)). Qed.
Lemma lem3915424 : term208 = term143.
Proof. exact (TRANS (@lem3915419) (@lem3915423)). Qed.
Lemma lem3915426 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915427 : term263 = term133.
Proof. exact (@lem3915426 term11). Qed.
Lemma lem3915428 : real_lt = real_lt.
Proof. exact (eq_refl real_lt). Qed.
Lemma lem3915429 : term478 = term472.
Proof. exact (MK_COMB (@lem3915428) (@lem3915427)). Qed.
Lemma lem3915430 : term477 = term251.
Proof. exact (MK_COMB (@lem3915429) (@lem3915424)). Qed.
Lemma lem3915432 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915433 : term251 = term252.
Proof. exact (@lem3915432 (NUMERAL 0) term11). Qed.
Lemma lem3915434 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915435 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915436 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915435 h1) (fun h1 : term252 = True => @lem3915434)). Qed.
Lemma lem3915437 : term252 = True.
Proof. exact (EQ_MP (@lem3915436) (@lem3915434)). Qed.
Lemma lem3915438 : term251 = True.
Proof. exact (TRANS (@lem3915433) (@lem3915437)). Qed.
Lemma lem3915439 : term477 = True.
Proof. exact (TRANS (@lem3915430) (@lem3915438)). Qed.
Lemma lem3915440 : term474 = True.
Proof. exact (TRANS (@lem3915416) (@lem3915439)). Qed.
Lemma lem3915441 : term251 = True.
Proof. exact (TRANS (@lem3915393) (@lem3915440)). Qed.
Lemma lem3915442 : term471 = True.
Proof. exact (TRANS (@lem3915384) (@lem3915441)). Qed.
Lemma lem3915443 : True = term471.
Proof. exact (SYM (@lem3915442)). Qed.
Lemma lem3915444 : term471.
Proof. exact (EQ_MP (@lem3915443) (@lem0)). Qed.
Lemma lem3915445 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term551 _45439.
Proof. exact (conj (@lem3915444) (@lem3915380 _45438 _45439 h1)). Qed.
Lemma lem3915447 (x : real) (y : real) : term480 x y.
Proof. exact (proj1 (@lem1988332 x y)). Qed.
Lemma lem3915448 (_45439 : int) : term552 _45439.
Proof. exact (@lem3915447 term143 (term299 _45439)). Qed.
Lemma lem3915449 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term553 _45439.
Proof. exact (@lem3915448 _45439 (@lem3915445 _45438 _45439 h1)). Qed.
Lemma lem3915450 (_45439 : int) : (term554 _45439) = (term299 _45439).
Proof. exact (@lem1982733 (term299 _45439)). Qed.
Lemma lem3915451 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3915452 (_45439 : int) : (term555 _45439) = (term301 _45439).
Proof. exact (MK_COMB (@lem3915451) (@lem3915450 _45439)). Qed.
Lemma lem3915453 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3915454 (_45439 : int) : (term553 _45439) = (term302 _45439).
Proof. exact (MK_COMB (@lem3915452 _45439) (@lem3915453)). Qed.
Lemma lem3915455 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term302 _45439.
Proof. exact (EQ_MP (@lem3915454 _45439) (@lem3915449 _45438 _45439 h1)). Qed.
Lemma lem3915457 (y : real) : term485 y.
Proof. exact (EQ_MP (@lem1396750 y) (@lem0)). Qed.
Lemma lem3915458 (_45439 : int) : term539 _45439.
Proof. exact (@lem3915457 (real_of_int _45439)). Qed.
Lemma lem3915459 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term540 _45439.
Proof. exact (@lem3915458 _45439 (@lem3915381 _45438 _45439 h1)). Qed.
Lemma lem3915460 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term556 _45439.
Proof. exact (@lem3915459 _45438 _45439 h1 term199). Qed.
Lemma lem3915461 (_45439 : int) : (term556 _45439) = ((term237 _45439) = term133).
Proof. exact (eq_refl (term556 _45439)). Qed.
Lemma lem3915468 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : (term237 _45439) = term133.
Proof. exact (EQ_MP (@lem3915461 _45439) (@lem3915460 _45438 _45439 h1)). Qed.
Lemma lem3915469 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term623 _45439.
Proof. exact (conj (@lem3915468 _45438 _45439 h1) (@lem3915455 _45438 _45439 h1)). Qed.
Lemma lem3915471 (x : real) (y : real) : term492 x y.
Proof. exact (proj1 (@lem1988336 x y)). Qed.
Lemma lem3915472 (_45439 : int) : term624 _45439.
Proof. exact (@lem3915471 (term237 _45439) (term299 _45439)). Qed.
Lemma lem3915473 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term572 _45439.
Proof. exact (@lem3915472 _45439 (@lem3915469 _45438 _45439 h1)). Qed.
Lemma lem3915474 (_45439 : int) : (term573 _45439) = (term574 _45439).
Proof. exact (@lem1982763 (term237 _45439) (real_of_int _45439) term199). Qed.
Lemma lem3915475 (_45439 : int) : (term497 _45439) = (term498 _45439).
Proof. exact (@lem1982713 term199 (real_of_int _45439)). Qed.
Lemma lem3915477 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915478 : term143 = term224.
Proof. exact (@lem3915477 term11). Qed.
Lemma lem3915480 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3915481 : term199 = term200.
Proof. exact (@lem3915480 term11). Qed.
Lemma lem3915482 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3915483 : term499 = term500.
Proof. exact (MK_COMB (@lem3915482) (@lem3915481)). Qed.
Lemma lem3915484 : term501 = term502.
Proof. exact (MK_COMB (@lem3915483) (@lem3915478)). Qed.
Lemma lem3915485 : term503.
Proof. exact (@lem1981473 term199 term143 term143 term143 term133 term143). Qed.
Lemma lem3915487 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915488 : term251 = term252.
Proof. exact (@lem3915487 (NUMERAL 0) term11). Qed.
Lemma lem3915489 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915490 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915491 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915490 h1) (fun h1 : term252 = True => @lem3915489)). Qed.
Lemma lem3915492 : term252 = True.
Proof. exact (EQ_MP (@lem3915491) (@lem3915489)). Qed.
Lemma lem3915493 : term251 = True.
Proof. exact (TRANS (@lem3915488) (@lem3915492)). Qed.
Lemma lem3915494 : True = term251.
Proof. exact (SYM (@lem3915493)). Qed.
Lemma lem3915495 : term251.
Proof. exact (EQ_MP (@lem3915494) (@lem0)). Qed.
Lemma lem3915496 : term504.
Proof. exact (@lem3915485 (@lem3915495)). Qed.
Lemma lem3915498 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915499 : term251 = term252.
Proof. exact (@lem3915498 (NUMERAL 0) term11). Qed.
Lemma lem3915500 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915501 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915502 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915501 h1) (fun h1 : term252 = True => @lem3915500)). Qed.
Lemma lem3915503 : term252 = True.
Proof. exact (EQ_MP (@lem3915502) (@lem3915500)). Qed.
Lemma lem3915504 : term251 = True.
Proof. exact (TRANS (@lem3915499) (@lem3915503)). Qed.
Lemma lem3915505 : True = term251.
Proof. exact (SYM (@lem3915504)). Qed.
Lemma lem3915506 : term251.
Proof. exact (EQ_MP (@lem3915505) (@lem0)). Qed.
Lemma lem3915507 : term505.
Proof. exact (@lem3915496 (@lem3915506)). Qed.
Lemma lem3915509 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915510 : term251 = term252.
Proof. exact (@lem3915509 (NUMERAL 0) term11). Qed.
Lemma lem3915511 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915512 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915513 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915512 h1) (fun h1 : term252 = True => @lem3915511)). Qed.
Lemma lem3915514 : term252 = True.
Proof. exact (EQ_MP (@lem3915513) (@lem3915511)). Qed.
Lemma lem3915515 : term251 = True.
Proof. exact (TRANS (@lem3915510) (@lem3915514)). Qed.
Lemma lem3915516 : True = term251.
Proof. exact (SYM (@lem3915515)). Qed.
Lemma lem3915517 : term251.
Proof. exact (EQ_MP (@lem3915516) (@lem0)). Qed.
Lemma lem3915518 : term506.
Proof. exact (@lem3915507 (@lem3915517)). Qed.
Lemma lem3915520 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3915521 : term208 = term209.
Proof. exact (@lem3915520 term11 term11). Qed.
Lemma lem3915522 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915523 : term211 = term11.
Proof. exact (EQ_MP (@lem3915522) (@lem940073)). Qed.
Lemma lem3915524 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915525 : term209 = term143.
Proof. exact (MK_COMB (@lem3915524) (@lem3915523)). Qed.
Lemma lem3915526 : term208 = term143.
Proof. exact (TRANS (@lem3915521) (@lem3915525)). Qed.
Lemma lem3915528 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3915529 : term225 = term230.
Proof. exact (@lem3915528 term11 term11). Qed.
Lemma lem3915530 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915531 : term211 = term11.
Proof. exact (EQ_MP (@lem3915530) (@lem940073)). Qed.
Lemma lem3915532 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915533 : term209 = term143.
Proof. exact (MK_COMB (@lem3915532) (@lem3915531)). Qed.
Lemma lem3915534 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3915535 : term230 = term199.
Proof. exact (MK_COMB (@lem3915534) (@lem3915533)). Qed.
Lemma lem3915536 : term225 = term199.
Proof. exact (TRANS (@lem3915529) (@lem3915535)). Qed.
Lemma lem3915537 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3915538 : term507 = term499.
Proof. exact (MK_COMB (@lem3915537) (@lem3915536)). Qed.
Lemma lem3915539 : term508 = term501.
Proof. exact (MK_COMB (@lem3915538) (@lem3915526)). Qed.
Lemma lem3915541 (m : nat) : (term509 m) = term133.
Proof. exact (proj1 (@lem1367303 m)). Qed.
Lemma lem3915542 : term501 = term133.
Proof. exact (@lem3915541 term11). Qed.
Lemma lem3915543 : term508 = term133.
Proof. exact (TRANS (@lem3915539) (@lem3915542)). Qed.
Lemma lem3915544 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3915545 : term510 = term261.
Proof. exact (MK_COMB (@lem3915544) (@lem3915543)). Qed.
Lemma lem3915546 : term143 = term143.
Proof. exact (eq_refl term143). Qed.
Lemma lem3915547 : term511 = term263.
Proof. exact (MK_COMB (@lem3915545) (@lem3915546)). Qed.
Lemma lem3915549 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915550 : term263 = term133.
Proof. exact (@lem3915549 term11). Qed.
Lemma lem3915551 : term511 = term133.
Proof. exact (TRANS (@lem3915547) (@lem3915550)). Qed.
Lemma lem3915553 (m : nat) (n : nat) : (term206 m n) = (term207 m n).
Proof. exact (proj1 (@lem1367248 m n)). Qed.
Lemma lem3915554 : term208 = term209.
Proof. exact (@lem3915553 term11 term11). Qed.
Lemma lem3915555 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915556 : term211 = term11.
Proof. exact (EQ_MP (@lem3915555) (@lem940073)). Qed.
Lemma lem3915557 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915558 : term209 = term143.
Proof. exact (MK_COMB (@lem3915557) (@lem3915556)). Qed.
Lemma lem3915559 : term208 = term143.
Proof. exact (TRANS (@lem3915554) (@lem3915558)). Qed.
Lemma lem3915560 : term261 = term261.
Proof. exact (eq_refl term261). Qed.
Lemma lem3915561 : term265 = term263.
Proof. exact (MK_COMB (@lem3915560) (@lem3915559)). Qed.
Lemma lem3915563 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915564 : term263 = term133.
Proof. exact (@lem3915563 term11). Qed.
Lemma lem3915565 : term265 = term133.
Proof. exact (TRANS (@lem3915561) (@lem3915564)). Qed.
Lemma lem3915566 : term133 = term265.
Proof. exact (SYM (@lem3915565)). Qed.
Lemma lem3915567 : term511 = term265.
Proof. exact (TRANS (@lem3915551) (@lem3915566)). Qed.
Lemma lem3915568 : term502 = term196.
Proof. exact (@lem3915518 (@lem3915567)). Qed.
Lemma lem3915569 : term501 = term196.
Proof. exact (TRANS (@lem3915484) (@lem3915568)). Qed.
Lemma lem3915571 (x : real) : (term215 x) = x.
Proof. exact (EQ_MP (@lem1981475 x) (@lem1981474 x)). Qed.
Lemma lem3915572 : term196 = term133.
Proof. exact (@lem3915571 term133). Qed.
Lemma lem3915573 : term501 = term133.
Proof. exact (TRANS (@lem3915569) (@lem3915572)). Qed.
Lemma lem3915574 : real_mul = real_mul.
Proof. exact (eq_refl real_mul). Qed.
Lemma lem3915575 : term512 = term261.
Proof. exact (MK_COMB (@lem3915574) (@lem3915573)). Qed.
Lemma lem3915576 (_45439 : int) : (real_of_int _45439) = (real_of_int _45439).
Proof. exact (eq_refl (real_of_int _45439)). Qed.
Lemma lem3915577 (_45439 : int) : (term498 _45439) = (term513 _45439).
Proof. exact (MK_COMB (@lem3915575) (@lem3915576 _45439)). Qed.
Lemma lem3915578 (_45439 : int) : (term497 _45439) = (term513 _45439).
Proof. exact (TRANS (@lem3915475 _45439) (@lem3915577 _45439)). Qed.
Lemma lem3915579 (_45439 : int) : (term513 _45439) = term133.
Proof. exact (@lem1982719 (real_of_int _45439)). Qed.
Lemma lem3915580 (_45439 : int) : (term497 _45439) = term133.
Proof. exact (TRANS (@lem3915578 _45439) (@lem3915579 _45439)). Qed.
Lemma lem3915581 : real_add = real_add.
Proof. exact (eq_refl real_add). Qed.
Lemma lem3915582 (_45439 : int) : (term514 _45439) = term175.
Proof. exact (MK_COMB (@lem3915581) (@lem3915580 _45439)). Qed.
Lemma lem3915583 : term199 = term199.
Proof. exact (eq_refl term199). Qed.
Lemma lem3915584 (_45439 : int) : (term574 _45439) = term519.
Proof. exact (MK_COMB (@lem3915582 _45439) (@lem3915583)). Qed.
Lemma lem3915585 (_45439 : int) : (term573 _45439) = term519.
Proof. exact (TRANS (@lem3915474 _45439) (@lem3915584 _45439)). Qed.
Lemma lem3915586 : term519 = term199.
Proof. exact (@lem1982721 term199). Qed.
Lemma lem3915587 (_45439 : int) : (term573 _45439) = term199.
Proof. exact (TRANS (@lem3915585 _45439) (@lem3915586)). Qed.
Lemma lem3915588 : real_ge = real_ge.
Proof. exact (eq_refl real_ge). Qed.
Lemma lem3915589 (_45439 : int) : (term575 _45439) = term521.
Proof. exact (MK_COMB (@lem3915588) (@lem3915587 _45439)). Qed.
Lemma lem3915590 : term133 = term133.
Proof. exact (eq_refl term133). Qed.
Lemma lem3915591 (_45439 : int) : (term572 _45439) = term522.
Proof. exact (MK_COMB (@lem3915589 _45439) (@lem3915590)). Qed.
Lemma lem3915592 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : term522.
Proof. exact (EQ_MP (@lem3915591 _45439) (@lem3915473 _45438 _45439 h1)). Qed.
Lemma lem3915594 (y : real) (x : real) : (real_ge x y) = (real_le y x).
Proof. exact (EQ_MP (@lem1980260 y x) (@lem1980259 y x)). Qed.
Lemma lem3915595 : term522 = term523.
Proof. exact (@lem3915594 term133 term199). Qed.
Lemma lem3915597 (x : nat) : (term197 x) = (term198 x).
Proof. exact (proj1 (@lem1980011 x (@el nat))). Qed.
Lemma lem3915598 : term199 = term200.
Proof. exact (@lem3915597 term11). Qed.
Lemma lem3915600 (x : nat) : (real_of_num x) = (term195 x).
Proof. exact (proj1 (@lem1980010 x (@el nat))). Qed.
Lemma lem3915601 : term133 = term196.
Proof. exact (@lem3915600 (NUMERAL 0)). Qed.
Lemma lem3915602 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3915603 : term135 = term524.
Proof. exact (MK_COMB (@lem3915602) (@lem3915601)). Qed.
Lemma lem3915604 : term523 = term525.
Proof. exact (MK_COMB (@lem3915603) (@lem3915598)). Qed.
Lemma lem3915605 : term526.
Proof. exact (@lem1980026 term133 term143 term199 term143). Qed.
Lemma lem3915607 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915608 : term251 = term252.
Proof. exact (@lem3915607 (NUMERAL 0) term11). Qed.
Lemma lem3915609 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915610 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915611 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915610 h1) (fun h1 : term252 = True => @lem3915609)). Qed.
Lemma lem3915612 : term252 = True.
Proof. exact (EQ_MP (@lem3915611) (@lem3915609)). Qed.
Lemma lem3915613 : term251 = True.
Proof. exact (TRANS (@lem3915608) (@lem3915612)). Qed.
Lemma lem3915614 : True = term251.
Proof. exact (SYM (@lem3915613)). Qed.
Lemma lem3915615 : term251.
Proof. exact (EQ_MP (@lem3915614) (@lem0)). Qed.
Lemma lem3915616 : term527.
Proof. exact (@lem3915605 (@lem3915615)). Qed.
Lemma lem3915618 (m : nat) (n : nat) : (term250 m n) = (Peano.lt m n).
Proof. exact (proj1 (@lem1365721 m n)). Qed.
Lemma lem3915619 : term251 = term252.
Proof. exact (@lem3915618 (NUMERAL 0) term11). Qed.
Lemma lem3915620 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915621 (h1 : term253 = (BIT1 0)) : term252 = True.
Proof. exact (@lem1009824 0 0 (BIT1 0) h1). Qed.
Lemma lem3915622 : (term253 = (BIT1 0)) = (term252 = True).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915621 h1) (fun h1 : term252 = True => @lem3915620)). Qed.
Lemma lem3915623 : term252 = True.
Proof. exact (EQ_MP (@lem3915622) (@lem3915620)). Qed.
Lemma lem3915624 : term251 = True.
Proof. exact (TRANS (@lem3915619) (@lem3915623)). Qed.
Lemma lem3915625 : True = term251.
Proof. exact (SYM (@lem3915624)). Qed.
Lemma lem3915626 : term251.
Proof. exact (EQ_MP (@lem3915625) (@lem0)). Qed.
Lemma lem3915627 : term525 = term528.
Proof. exact (@lem3915616 (@lem3915626)). Qed.
Lemma lem3915629 (m : nat) (n : nat) : (term228 m n) = (term229 m n).
Proof. exact (proj1 (@lem1367247 m n)). Qed.
Lemma lem3915630 : term225 = term230.
Proof. exact (@lem3915629 term11 term11). Qed.
Lemma lem3915631 : (term210 = (BIT1 0)) = (term211 = term11).
Proof. exact (@lem1008952 (BIT1 0) (BIT1 0)). Qed.
Lemma lem3915632 : term211 = term11.
Proof. exact (EQ_MP (@lem3915631) (@lem940073)). Qed.
Lemma lem3915633 : real_of_num = real_of_num.
Proof. exact (eq_refl real_of_num). Qed.
Lemma lem3915634 : term209 = term143.
Proof. exact (MK_COMB (@lem3915633) (@lem3915632)). Qed.
Lemma lem3915635 : real_neg = real_neg.
Proof. exact (eq_refl real_neg). Qed.
Lemma lem3915636 : term230 = term199.
Proof. exact (MK_COMB (@lem3915635) (@lem3915634)). Qed.
Lemma lem3915637 : term225 = term199.
Proof. exact (TRANS (@lem3915630) (@lem3915636)). Qed.
Lemma lem3915639 (x : nat) : (term264 x) = term133.
Proof. exact (proj1 (@lem1367111 x)). Qed.
Lemma lem3915640 : term263 = term133.
Proof. exact (@lem3915639 term11). Qed.
Lemma lem3915641 : real_le = real_le.
Proof. exact (eq_refl real_le). Qed.
Lemma lem3915642 : term529 = term135.
Proof. exact (MK_COMB (@lem3915641) (@lem3915640)). Qed.
Lemma lem3915643 : term528 = term523.
Proof. exact (MK_COMB (@lem3915642) (@lem3915637)). Qed.
Lemma lem3915645 (m : nat) (n : nat) : (term530 m n) = (term531 m n).
Proof. exact (proj2 (@lem1365406 m n)). Qed.
Lemma lem3915646 : term523 = term532.
Proof. exact (@lem3915645 (NUMERAL 0) term11). Qed.
Lemma lem3915647 : term253 = (BIT1 0).
Proof. exact (@lem912739). Qed.
Lemma lem3915648 (h1 : term253 = (BIT1 0)) : (term11 = (NUMERAL 0)) = False.
Proof. exact (@lem1013352 0 0 (BIT1 0) h1). Qed.
Lemma lem3915649 : (term253 = (BIT1 0)) = ((term11 = (NUMERAL 0)) = False).
Proof. exact (prop_ext (fun h1 : term253 = (BIT1 0) => @lem3915648 h1) (fun h1 : (term11 = (NUMERAL 0)) = False => @lem3915647)). Qed.
Lemma lem3915650 : (term11 = (NUMERAL 0)) = False.
Proof. exact (EQ_MP (@lem3915649) (@lem3915647)). Qed.
Lemma lem3915651 : ((NUMERAL 0) = (NUMERAL 0)) = True.
Proof. exact (@lem1013364 0). Qed.
Lemma lem3915652 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915653 : term533 = (and True).
Proof. exact (MK_COMB (@lem3915652) (@lem3915651)). Qed.
Lemma lem3915654 : term532 = (True /\ False).
Proof. exact (MK_COMB (@lem3915653) (@lem3915650)). Qed.
Lemma lem3915656 : (True /\ False) = False.
Proof. exact (proj1 (@lem1365106)). Qed.
Lemma lem3915657 : term532 = False.
Proof. exact (TRANS (@lem3915654) (@lem3915656)). Qed.
Lemma lem3915658 : term523 = False.
Proof. exact (TRANS (@lem3915646) (@lem3915657)). Qed.
Lemma lem3915659 : term528 = False.
Proof. exact (TRANS (@lem3915643) (@lem3915658)). Qed.
Lemma lem3915660 : term525 = False.
Proof. exact (TRANS (@lem3915627) (@lem3915659)). Qed.
Lemma lem3915661 : term523 = False.
Proof. exact (TRANS (@lem3915604) (@lem3915660)). Qed.
Lemma lem3915662 : term522 = False.
Proof. exact (TRANS (@lem3915595) (@lem3915661)). Qed.
Lemma lem3915663 (_45438 : int) (_45439 : int) (h1 : term625 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3915662) (@lem3915592 _45438 _45439 h1)). Qed.
Lemma lem3915664 (_45438 : int) (_45439 : int) (h1 : term428 _45438 _45439) : False.
Proof. exact (or_elim (@lem3915079 _45438 _45439 h1) (fun h0 : term622 _45438 _45439 => @lem3915370 _45438 _45439 h0) (fun h0 : term625 _45438 _45439 => @lem3915663 _45438 _45439 h0)). Qed.
Lemma lem3915665 (_45438 : int) (_45439 : int) (h1 : term437 _45438 _45439) : False.
Proof. exact (or_elim (@lem3914107 _45438 _45439 h1) (fun h0 : term432 _45438 _45439 => @lem3915078 _45438 _45439 h0) (fun h0 : term428 _45438 _45439 => @lem3915664 _45438 _45439 h0)). Qed.
Lemma lem3915666 (_45438 : int) (_45439 : int) (h1 : term453 _45438 _45439) : False.
Proof. exact (or_elim (@lem3912758 _45438 _45439 h1) (fun h0 : term450 _45438 _45439 => @lem3914106 _45438 _45439 h0) (fun h0 : term437 _45438 _45439 => @lem3915665 _45438 _45439 h0)). Qed.
Lemma lem3915667 (_45438 : int) (_45439 : int) (h1 : term469 _45438 _45439) : False.
Proof. exact (or_elim (@lem3910557 _45438 _45439 h1) (fun h0 : term466 _45438 _45439 => @lem3912757 _45438 _45439 h0) (fun h0 : term453 _45438 _45439 => @lem3915666 _45438 _45439 h0)). Qed.
Lemma lem3915669 (_45438 : int) (_45439 : int) (h1 : term469 _45438 _45439) : term469 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3915670 (_45438 : int) (_45439 : int) (h1 : term469 _45438 _45439) : (term469 _45438 _45439) = False.
Proof. exact (prop_ext (fun h2 : term469 _45438 _45439 => @lem3915667 _45438 _45439 h1) (fun h2 : False => @lem3915669 _45438 _45439 h1)). Qed.
Lemma lem3915671 (_45438 : int) (_45439 : int) (h1 : term469 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3915670 _45438 _45439 h1) (@lem3915669 _45438 _45439 h1)). Qed.
Lemma lem3915672 (_45438 : int) (_45439 : int) (h1 : term191 _45438 _45439) : term191 _45438 _45439.
Proof. exact (h1). Qed.
Lemma lem3915673 (_45438 : int) (_45439 : int) (h1 : term191 _45438 _45439) : term469 _45438 _45439.
Proof. exact (EQ_MP (@lem3910487 _45438 _45439) (@lem3915672 _45438 _45439 h1)). Qed.
Lemma lem3915674 (_45438 : int) (_45439 : int) (h1 : term191 _45438 _45439) : (term469 _45438 _45439) = False.
Proof. exact (prop_ext (fun h2 : term469 _45438 _45439 => @lem3915671 _45438 _45439 h2) (fun h2 : False => @lem3915673 _45438 _45439 h1)). Qed.
Lemma lem3915675 (_45438 : int) (_45439 : int) (h1 : term191 _45438 _45439) : False.
Proof. exact (EQ_MP (@lem3915674 _45438 _45439 h1) (@lem3915673 _45438 _45439 h1)). Qed.
Lemma lem3915676 (_45438 : int) (_45439 : int) : term626 _45438 _45439.
Proof. exact (fun h0 : term191 _45438 _45439 => @lem3915675 _45438 _45439 h0). Qed.
Lemma lem3915677 (_45438 : int) (_45439 : int) : term627 _45438 _45439.
Proof. exact (@lem1386578 (term628 _45438 _45439)). Qed.
Lemma lem3915680 (_45438 : int) (_45439 : int) : term628 _45438 _45439.
Proof. exact (@lem3915677 _45438 _45439 (@lem3915676 _45438 _45439)). Qed.
Lemma lem3915681 (_45438 : int) (_45439 : int) : (term189 _45438 _45439) = (term127 _45438 _45439).
Proof. exact (SYM (@lem3909426 _45438 _45439)). Qed.
Lemma lem3915682 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3915683 (_45438 : int) (_45439 : int) : (term628 _45438 _45439) = (term73 _45438 _45439).
Proof. exact (MK_COMB (@lem3915682) (@lem3915681 _45438 _45439)). Qed.
Lemma lem3915684 (_45438 : int) (_45439 : int) : term73 _45438 _45439.
Proof. exact (EQ_MP (@lem3915683 _45438 _45439) (@lem3915680 _45438 _45439)). Qed.
Lemma lem3915685 (_45438 : int) (_45439 : int) : term74 _45438 _45439.
Proof. exact (EQ_MP (@lem3909113 _45438 _45439) (@lem3915684 _45438 _45439)). Qed.
Lemma lem3915686 (d : nat) (n : nat) : term629 d n.
Proof. exact (@lem3915685 (int_of_num d) (int_of_num n)). Qed.
Lemma lem3915687 (d : nat) (n : nat) : term630 d n.
Proof. exact (@lem3915686 d n (@lem3909109 d)). Qed.
Lemma lem3915688 (d : nat) (n : nat) : term68 d n.
Proof. exact (@lem3915687 d n (@lem3909112 n)). Qed.
Lemma lem3915689 (n : nat) : term70 n.
Proof. exact (fun d : nat => @lem3915688 d n). Qed.
Lemma lem3915690 (n : nat) : (term70 n) = ((term7 n) = (term8 n)).
Proof. exact (SYM (@lem3909106 n)). Qed.
Lemma lem3915692 (h1 : term631) : term631.
Proof. exact (h1). Qed.
Lemma lem3915693 (m : nat) (h1 : term631) : term632 m.
Proof. exact (@lem3915692 h1 m). Qed.
Lemma lem3915694 (m : nat) : (term632 m) = (term633 m).
Proof. exact (eq_refl (term632 m)). Qed.
Lemma lem3915695 (m : nat) (h1 : term631) : term633 m.
Proof. exact (EQ_MP (@lem3915694 m) (@lem3915693 m h1)). Qed.
Lemma lem3915696 (m : nat) (n : nat) (h1 : term631) : term634 m n.
Proof. exact (@lem3915695 m h1 n). Qed.
Lemma lem3915697 (n : nat) (m : nat) : (term634 m n) = (term635 n m).
Proof. exact (eq_refl (term634 m n)). Qed.
Lemma lem3915698 (n : nat) (m : nat) (h1 : term631) : term635 n m.
Proof. exact (EQ_MP (@lem3915697 n m) (@lem3915696 m n h1)). Qed.
Lemma lem3915699 (n : nat) (m : nat) (p : nat) (h1 : term631) : term636 n m p.
Proof. exact (@lem3915698 n m h1 p). Qed.
Lemma lem3915700 (n : nat) (m : nat) (p : nat) : (term636 n m p) = (term637 n m p).
Proof. exact (eq_refl (term636 n m p)). Qed.
Lemma lem3915701 (n : nat) (m : nat) (p : nat) (h1 : term631) : term637 n m p.
Proof. exact (EQ_MP (@lem3915700 n m p) (@lem3915699 n m p h1)). Qed.
Lemma lem3915702 (m : nat) (n : nat) (p : nat) (h1 : term638 m n p) : term638 m n p.
Proof. exact (h1). Qed.
Lemma lem3915703 (m : nat) (n : nat) (p : nat) (h1 : term631) (h2 : term638 m n p) : Peano.lt m p.
Proof. exact (@lem3915701 n m p h1 (@lem3915702 m n p h2)). Qed.
Lemma lem3915704 (m : nat) (n : nat) (p : nat) (h1 : term638 m n p) : term639 m p.
Proof. exact (fun h0 : term631 => @lem3915703 m n p h0 h1). Qed.
Lemma lem3915705 (m : nat) (p : nat) (h1 : term640 m p) : term640 m p.
Proof. exact (h1). Qed.
Lemma lem3915706 (m : nat) (p : nat) (h1 : term640 m p) : term639 m p.
Proof. exact (ex_elim (@lem3915705 m p h1) (fun n : nat => fun h0 : term641 m p n => @lem3915704 m n p h0)). Qed.
Lemma lem3915707 (h1 : term631) : term631.
Proof. exact (h1). Qed.
Lemma lem3915708 (m : nat) (p : nat) (h1 : term631) (h2 : term640 m p) : Peano.lt m p.
Proof. exact (@lem3915706 m p h2 (@lem3915707 h1)). Qed.
Lemma lem3915709 (m : nat) (p : nat) (h1 : term631) : term642 m p.
Proof. exact (fun h0 : term640 m p => @lem3915708 m p h1 h0). Qed.
Lemma lem3915710 (m : nat) (h1 : term631) : term643 m.
Proof. exact (fun p : nat => @lem3915709 m p h1). Qed.
Lemma lem3915711 (h1 : term631) : term644.
Proof. exact (fun m : nat => @lem3915710 m h1). Qed.
Lemma lem3915712 : term645.
Proof. exact (fun h0 : term631 => @lem3915711 h0). Qed.
Lemma lem3915713 : term644.
Proof. exact (@lem3915712 (@lem95173)). Qed.
Lemma lem3915714 (m : nat) : term646 m.
Proof. exact (@lem3915713 m). Qed.
Lemma lem3915715 (m : nat) : (term646 m) = (term643 m).
Proof. exact (eq_refl (term646 m)). Qed.
Lemma lem3915716 (m : nat) : term643 m.
Proof. exact (EQ_MP (@lem3915715 m) (@lem3915714 m)). Qed.
Lemma lem3915717 (m : nat) (p : nat) : term647 m p.
Proof. exact (@lem3915716 m p). Qed.
Lemma lem3915718 (m : nat) (p : nat) : (term647 m p) = (term642 m p).
Proof. exact (eq_refl (term647 m p)). Qed.
Lemma lem3915735 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@PSUBSET A s t) = (term648 A s t).
Proof. exact (EQ_MP (@lem3211745 A s t) (@lem3211744 A s t)). Qed.
Lemma lem3915736 {_100908 : Type'} (s : _100908 -> Prop) (t : _100908 -> Prop) : (@PSUBSET _100908 s t) = (term648 _100908 s t).
Proof. exact (@lem3915735 _100908 s t). Qed.
Lemma lem3915737 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (@PSUBSET _100908 a b) = (term648 _100908 a b).
Proof. exact (@lem3915736 _100908 a b). Qed.
Lemma lem3915741 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term649 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3915742 {_100908 : Type'} (s : _100908 -> Prop) (t : _100908 -> Prop) : (@SUBSET _100908 s t) = (term649 _100908 s t).
Proof. exact (@lem3915741 _100908 s t). Qed.
Lemma lem3915743 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (@SUBSET _100908 a b) = (term649 _100908 a b).
Proof. exact (@lem3915742 _100908 a b). Qed.
Lemma lem3915750 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915751 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term650 _100908 a b) = (term651 _100908 a b).
Proof. exact (MK_COMB (@lem3915750) (@lem3915743 _100908 a b)). Qed.
Lemma lem3915755 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (s = t) = (term652 A s t).
Proof. exact (EQ_MP (@lem3211757 A s t) (@lem3211756 A s t)). Qed.
Lemma lem3915756 {_100908 : Type'} (s : _100908 -> Prop) (t : _100908 -> Prop) : (s = t) = (term652 _100908 s t).
Proof. exact (@lem3915755 _100908 s t). Qed.
Lemma lem3915757 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (a = b) = (term652 _100908 a b).
Proof. exact (@lem3915756 _100908 a b). Qed.
Lemma lem3915766 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3915767 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term653 _100908 a b) = (term654 _100908 a b).
Proof. exact (MK_COMB (@lem3915766) (@lem3915757 _100908 a b)). Qed.
Lemma lem3915768 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term648 _100908 a b) = (term655 _100908 a b).
Proof. exact (MK_COMB (@lem3915751 _100908 a b) (@lem3915767 _100908 a b)). Qed.
Lemma lem3915771 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (@PSUBSET _100908 a b) = (term655 _100908 a b).
Proof. exact (TRANS (@lem3915737 _100908 a b) (@lem3915768 _100908 a b)). Qed.
Lemma lem3915772 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3915773 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term656 _100908 a b) = (term657 _100908 a b).
Proof. exact (MK_COMB (@lem3915772) (@lem3915771 _100908 a b)). Qed.
Lemma lem3915783 {A : Type'} (s : A -> Prop) (t : A -> Prop) : (@SUBSET A s t) = (term649 A s t).
Proof. exact (EQ_MP (@lem3211751 A s t) (@lem3211750 A s t)). Qed.
Lemma lem3915784 {_100908 : Type'} (s : _100908 -> Prop) (t : _100908 -> Prop) : (@SUBSET _100908 s t) = (term649 _100908 s t).
Proof. exact (@lem3915783 _100908 s t). Qed.
Lemma lem3915785 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term658 _100908 a b x) = (term659 _100908 a b x).
Proof. exact (@lem3915784 _100908 a (@DELETE _100908 b x)). Qed.
Lemma lem3915792 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) : (term660 _100908 x a) = (term660 _100908 x a).
Proof. exact (eq_refl (term660 _100908 x a)). Qed.
Lemma lem3915793 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term661 _100908 a b x) = (term662 _100908 a b x).
Proof. exact (MK_COMB (@lem3915792 _100908 x a) (@lem3915785 _100908 a b x)). Qed.
Lemma lem3915796 {_100908 : Type'} (x : _100908) (b : _100908 -> Prop) : (term663 _100908 x b) = (term663 _100908 x b).
Proof. exact (eq_refl (term663 _100908 x b)). Qed.
Lemma lem3915797 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term664 _100908 a b x) = (term665 _100908 a b x).
Proof. exact (MK_COMB (@lem3915796 _100908 x b) (@lem3915793 _100908 a b x)). Qed.
Lemma lem3915800 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term666 _100908 a b) = (term667 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3915797 _100908 a b x)). Qed.
Lemma lem3915801 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3915802 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term668 _100908 a b) = (term669 _100908 a b).
Proof. exact (MK_COMB (@lem3915801 _100908) (@lem3915800 _100908 a b)). Qed.
Lemma lem3915807 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((@PSUBSET _100908 a b) = (term668 _100908 a b)) = ((term655 _100908 a b) = (term669 _100908 a b)).
Proof. exact (MK_COMB (@lem3915773 _100908 a b) (@lem3915802 _100908 a b)). Qed.
Lemma lem3915812 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term655 _100908 a b) = (term669 _100908 a b)) = ((@PSUBSET _100908 a b) = (term668 _100908 a b)).
Proof. exact (SYM (@lem3915807 _100908 a b)). Qed.
Lemma lem3915824 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915825 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915824 _100908 P x). Qed.
Lemma lem3915826 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (@IN _100908 x a) = (a x).
Proof. exact (@lem3915825 _100908 a x). Qed.
Lemma lem3915827 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3915828 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term670 _100908 x a) = (term671 _100908 a x).
Proof. exact (MK_COMB (@lem3915827) (@lem3915826 _100908 a x)). Qed.
Lemma lem3915830 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915831 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915830 _100908 P x). Qed.
Lemma lem3915832 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (@IN _100908 x b) = (b x).
Proof. exact (@lem3915831 _100908 b x). Qed.
Lemma lem3915833 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term672 _100908 a x b) = (term673 _100908 a b x).
Proof. exact (MK_COMB (@lem3915828 _100908 a x) (@lem3915832 _100908 b x)). Qed.
Lemma lem3915836 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term674 _100908 a b) = (term675 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3915833 _100908 a b x)). Qed.
Lemma lem3915837 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3915838 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term649 _100908 a b) = (term676 _100908 a b).
Proof. exact (MK_COMB (@lem3915837 _100908) (@lem3915836 _100908 a b)). Qed.
Lemma lem3915843 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915844 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term651 _100908 a b) = (term677 _100908 a b).
Proof. exact (MK_COMB (@lem3915843) (@lem3915838 _100908 a b)). Qed.
Lemma lem3915852 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915853 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915852 _100908 P x). Qed.
Lemma lem3915854 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (@IN _100908 x a) = (a x).
Proof. exact (@lem3915853 _100908 a x). Qed.
Lemma lem3915855 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3915856 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term678 _100908 x a) = (term679 _100908 a x).
Proof. exact (MK_COMB (@lem3915855) (@lem3915854 _100908 a x)). Qed.
Lemma lem3915858 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915859 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915858 _100908 P x). Qed.
Lemma lem3915860 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (@IN _100908 x b) = (b x).
Proof. exact (@lem3915859 _100908 b x). Qed.
Lemma lem3915861 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : ((@IN _100908 x a) = (@IN _100908 x b)) = ((a x) = (b x)).
Proof. exact (MK_COMB (@lem3915856 _100908 a x) (@lem3915860 _100908 b x)). Qed.
Lemma lem3915864 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term680 _100908 a b) = (term681 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3915861 _100908 a b x)). Qed.
Lemma lem3915865 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3915866 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term652 _100908 a b) = (term682 _100908 a b).
Proof. exact (MK_COMB (@lem3915865 _100908) (@lem3915864 _100908 a b)). Qed.
Lemma lem3915871 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3915872 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term654 _100908 a b) = (term683 _100908 a b).
Proof. exact (MK_COMB (@lem3915871) (@lem3915866 _100908 a b)). Qed.
Lemma lem3915873 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term655 _100908 a b) = (term684 _100908 a b).
Proof. exact (MK_COMB (@lem3915844 _100908 a b) (@lem3915872 _100908 a b)). Qed.
Lemma lem3915876 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3915877 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term657 _100908 a b) = (term685 _100908 a b).
Proof. exact (MK_COMB (@lem3915876) (@lem3915873 _100908 a b)). Qed.
Lemma lem3915885 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915886 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915885 _100908 P x). Qed.
Lemma lem3915887 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (@IN _100908 x b) = (b x).
Proof. exact (@lem3915886 _100908 b x). Qed.
Lemma lem3915888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915889 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term663 _100908 x b) = (term686 _100908 b x).
Proof. exact (MK_COMB (@lem3915888) (@lem3915887 _100908 b x)). Qed.
Lemma lem3915893 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915894 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915893 _100908 P x). Qed.
Lemma lem3915895 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (@IN _100908 x a) = (a x).
Proof. exact (@lem3915894 _100908 a x). Qed.
Lemma lem3915896 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3915897 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term687 _100908 x a) = (term688 _100908 a x).
Proof. exact (MK_COMB (@lem3915896) (@lem3915895 _100908 a x)). Qed.
Lemma lem3915898 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915899 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term660 _100908 x a) = (term689 _100908 a x).
Proof. exact (MK_COMB (@lem3915898) (@lem3915897 _100908 a x)). Qed.
Lemma lem3915907 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915908 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915907 _100908 P x). Qed.
Lemma lem3915909 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908) : (@IN _100908 x' a) = (a x').
Proof. exact (@lem3915908 _100908 a x'). Qed.
Lemma lem3915910 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3915911 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908) : (term670 _100908 x' a) = (term671 _100908 a x').
Proof. exact (MK_COMB (@lem3915910) (@lem3915909 _100908 a x')). Qed.
Lemma lem3915913 {A : Type'} (s : A -> Prop) (x : A) (y : A) : (term690 A x s y) = (term691 A s x y).
Proof. exact (EQ_MP (@lem3211684 A s x y) (@lem3211683 A s x y)). Qed.
Lemma lem3915914 {_100908 : Type'} (s : _100908 -> Prop) (x : _100908) (y : _100908) : (term690 _100908 x s y) = (term691 _100908 s x y).
Proof. exact (@lem3915913 _100908 s x y). Qed.
Lemma lem3915915 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term690 _100908 x' b x) = (term691 _100908 b x' x).
Proof. exact (@lem3915914 _100908 b x' x). Qed.
Lemma lem3915919 {A : Type'} (P : A -> Prop) (x : A) : (@IN A x P) = (P x).
Proof. exact (EQ_MP (@lem3211610 A P x) (@lem3211609 A P x)). Qed.
Lemma lem3915920 {_100908 : Type'} (P : _100908 -> Prop) (x : _100908) : (@IN _100908 x P) = (P x).
Proof. exact (@lem3915919 _100908 P x). Qed.
Lemma lem3915921 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) : (@IN _100908 x' b) = (b x').
Proof. exact (@lem3915920 _100908 b x'). Qed.
Lemma lem3915922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3915923 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) : (term663 _100908 x' b) = (term686 _100908 b x').
Proof. exact (MK_COMB (@lem3915922) (@lem3915921 _100908 b x')). Qed.
Lemma lem3915926 {_100908 : Type'} (x' : _100908) (x : _100908) : (term692 _100908 x' x) = (term692 _100908 x' x).
Proof. exact (eq_refl (term692 _100908 x' x)). Qed.
Lemma lem3915927 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term691 _100908 b x' x) = (term693 _100908 b x' x).
Proof. exact (MK_COMB (@lem3915923 _100908 b x') (@lem3915926 _100908 x' x)). Qed.
Lemma lem3915930 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term690 _100908 x' b x) = (term693 _100908 b x' x).
Proof. exact (TRANS (@lem3915915 _100908 b x' x) (@lem3915927 _100908 b x' x)). Qed.
Lemma lem3915931 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term694 _100908 a x' b x) = (term695 _100908 a b x' x).
Proof. exact (MK_COMB (@lem3915911 _100908 a x') (@lem3915930 _100908 b x' x)). Qed.
Lemma lem3915934 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term696 _100908 a b x) = (term697 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3915931 _100908 a b x' x)). Qed.
Lemma lem3915935 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3915936 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term659 _100908 a b x) = (term698 _100908 a b x).
Proof. exact (MK_COMB (@lem3915935 _100908) (@lem3915934 _100908 a b x)). Qed.
Lemma lem3915941 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term662 _100908 a b x) = (term699 _100908 a b x).
Proof. exact (MK_COMB (@lem3915899 _100908 a x) (@lem3915936 _100908 a b x)). Qed.
Lemma lem3915944 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term665 _100908 a b x) = (term700 _100908 a b x).
Proof. exact (MK_COMB (@lem3915889 _100908 b x) (@lem3915941 _100908 a b x)). Qed.
Lemma lem3915947 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term667 _100908 a b) = (term701 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3915944 _100908 a b x)). Qed.
Lemma lem3915948 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3915949 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term669 _100908 a b) = (term702 _100908 a b).
Proof. exact (MK_COMB (@lem3915948 _100908) (@lem3915947 _100908 a b)). Qed.
Lemma lem3915954 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term655 _100908 a b) = (term669 _100908 a b)) = ((term684 _100908 a b) = (term702 _100908 a b)).
Proof. exact (MK_COMB (@lem3915877 _100908 a b) (@lem3915949 _100908 a b)). Qed.
Lemma lem3915957 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term684 _100908 a b) = (term702 _100908 a b)) = ((term655 _100908 a b) = (term669 _100908 a b)).
Proof. exact (SYM (@lem3915954 _100908 a b)). Qed.
Lemma lem3915959 (p : Prop) : p = (term703 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3915960 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term684 _100908 a b) = (term702 _100908 a b)) = (term704 _100908 a b).
Proof. exact (@lem3915959 ((term684 _100908 a b) = (term702 _100908 a b))). Qed.
Lemma lem3915961 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term704 _100908 a b) = ((term684 _100908 a b) = (term702 _100908 a b)).
Proof. exact (SYM (@lem3915960 _100908 a b)). Qed.
Lemma lem3915962 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : term705 _100908 a b.
Proof. exact (h1). Qed.
Lemma lem3915965 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term704 _100908 a b) : term704 _100908 a b.
Proof. exact (h1). Qed.
Lemma lem3915966 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term706 _100908 a b.
Proof. exact (fun h0 : term704 _100908 a b => @lem3915965 _100908 a b h0). Qed.
Lemma lem3915967 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term706 _100908 a b) : term706 _100908 a b.
Proof. exact (h1). Qed.
Lemma lem3915968 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term704 _100908 a b) : term704 _100908 a b.
Proof. exact (h1). Qed.
Lemma lem3915969 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term704 _100908 a b) (h2 : term706 _100908 a b) : term704 _100908 a b.
Proof. exact (@lem3915967 _100908 a b h2 (@lem3915968 _100908 a b h1)). Qed.
Lemma lem3915970 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term704 _100908 a b) : term707 _100908 a b.
Proof. exact (fun h0 : term706 _100908 a b => @lem3915969 _100908 a b h1 h0). Qed.
Lemma lem3915971 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term706 _100908 a b) : term706 _100908 a b.
Proof. exact (h1). Qed.
Lemma lem3915972 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term704 _100908 a b) (h2 : term706 _100908 a b) : term704 _100908 a b.
Proof. exact (@lem3915970 _100908 a b h1 (@lem3915971 _100908 a b h2)). Qed.
Lemma lem3915973 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term706 _100908 a b) : term706 _100908 a b.
Proof. exact (fun h0 : term704 _100908 a b => @lem3915972 _100908 a b h0 h1). Qed.
Lemma lem3915974 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term708 _100908 a b.
Proof. exact (fun h0 : term706 _100908 a b => @lem3915973 _100908 a b h0). Qed.
Lemma lem3915977 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term706 _100908 a b.
Proof. exact (@lem3915974 _100908 a b (@lem3915966 _100908 a b)). Qed.
Lemma lem3915978 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term706 _100908 a b.
Proof. exact (@lem3915977 _100908 a b). Qed.
Lemma lem3915988 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3915989 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term704 _100908 a b) = (term709 _100908 a b).
Proof. exact (@lem3915988 (term705 _100908 a b)). Qed.
Lemma lem3915991 (t : Prop) : (term190 t) = t.
Proof. exact (EQ_MP (@lem16507 t) (@lem16506 t)). Qed.
Lemma lem3915992 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term709 _100908 a b) = ((term684 _100908 a b) = (term702 _100908 a b)).
Proof. exact (@lem3915991 ((term684 _100908 a b) = (term702 _100908 a b))). Qed.
Lemma lem3915993 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term704 _100908 a b) = ((term684 _100908 a b) = (term702 _100908 a b)).
Proof. exact (TRANS (@lem3915989 _100908 a b) (@lem3915992 _100908 a b)). Qed.
Lemma lem3916046 {_100908 : Type'} (b : _100908 -> Prop) : (term710 _100908 b) = (term711 _100908 b).
Proof. exact (fun_ext (fun a : _100908 -> Prop => @lem3915993 _100908 a b)). Qed.
Lemma lem3916047 {_100908 : Type'} : (@all (_100908 -> Prop)) = (@all (_100908 -> Prop)).
Proof. exact (eq_refl (@all (_100908 -> Prop))). Qed.
Lemma lem3916048 {_100908 : Type'} (b : _100908 -> Prop) : (term712 _100908 b) = (term713 _100908 b).
Proof. exact (MK_COMB (@lem3916047 _100908) (@lem3916046 _100908 b)). Qed.
Lemma lem3916053 {_100908 : Type'} : (term714 _100908) = (term715 _100908).
Proof. exact (fun_ext (fun b : _100908 -> Prop => @lem3916048 _100908 b)). Qed.
Lemma lem3916054 {_100908 : Type'} : (@all (_100908 -> Prop)) = (@all (_100908 -> Prop)).
Proof. exact (eq_refl (@all (_100908 -> Prop))). Qed.
Lemma lem3916063 {_100908 : Type'} : (term716 _100908) = (term717 _100908).
Proof. exact (MK_COMB (@lem3916054 _100908) (@lem3916053 _100908)). Qed.
Lemma lem3916074 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term695 _100908 a b x' x) = (term695 _100908 a b x' x).
Proof. exact (eq_refl (term695 _100908 a b x' x)). Qed.
Lemma lem3916075 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term697 _100908 a b x) = (term697 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916074 _100908 a b x' x)). Qed.
Lemma lem3916076 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916077 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term698 _100908 a b x) = (term698 _100908 a b x).
Proof. exact (MK_COMB (@lem3916076 _100908) (@lem3916075 _100908 a b x)). Qed.
Lemma lem3916082 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term689 _100908 a x) = (term689 _100908 a x).
Proof. exact (eq_refl (term689 _100908 a x)). Qed.
Lemma lem3916083 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term699 _100908 a b x) = (term699 _100908 a b x).
Proof. exact (MK_COMB (@lem3916082 _100908 a x) (@lem3916077 _100908 a b x)). Qed.
Lemma lem3916086 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term686 _100908 b x) = (term686 _100908 b x).
Proof. exact (eq_refl (term686 _100908 b x)). Qed.
Lemma lem3916087 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term700 _100908 a b x) = (term700 _100908 a b x).
Proof. exact (MK_COMB (@lem3916086 _100908 b x) (@lem3916083 _100908 a b x)). Qed.
Lemma lem3916088 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term701 _100908 a b) = (term701 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916087 _100908 a b x)). Qed.
Lemma lem3916089 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916090 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term702 _100908 a b) = (term702 _100908 a b).
Proof. exact (MK_COMB (@lem3916089 _100908) (@lem3916088 _100908 a b)). Qed.
Lemma lem3916095 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : ((a x) = (b x)) = ((a x) = (b x)).
Proof. exact (eq_refl ((a x) = (b x))). Qed.
Lemma lem3916096 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term681 _100908 a b) = (term681 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916095 _100908 a b x)). Qed.
Lemma lem3916097 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916098 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term682 _100908 a b) = (term682 _100908 a b).
Proof. exact (MK_COMB (@lem3916097 _100908) (@lem3916096 _100908 a b)). Qed.
Lemma lem3916099 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3916100 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term683 _100908 a b) = (term683 _100908 a b).
Proof. exact (MK_COMB (@lem3916099) (@lem3916098 _100908 a b)). Qed.
Lemma lem3916105 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term673 _100908 a b x) = (term673 _100908 a b x).
Proof. exact (eq_refl (term673 _100908 a b x)). Qed.
Lemma lem3916106 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term675 _100908 a b) = (term675 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916105 _100908 a b x)). Qed.
Lemma lem3916107 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916108 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term676 _100908 a b) = (term676 _100908 a b).
Proof. exact (MK_COMB (@lem3916107 _100908) (@lem3916106 _100908 a b)). Qed.
Lemma lem3916109 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916110 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term677 _100908 a b) = (term677 _100908 a b).
Proof. exact (MK_COMB (@lem3916109) (@lem3916108 _100908 a b)). Qed.
Lemma lem3916111 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term684 _100908 a b) = (term684 _100908 a b).
Proof. exact (MK_COMB (@lem3916110 _100908 a b) (@lem3916100 _100908 a b)). Qed.
Lemma lem3916112 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916113 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term685 _100908 a b) = (term685 _100908 a b).
Proof. exact (MK_COMB (@lem3916112) (@lem3916111 _100908 a b)). Qed.
Lemma lem3916114 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term684 _100908 a b) = (term702 _100908 a b)) = ((term684 _100908 a b) = (term702 _100908 a b)).
Proof. exact (MK_COMB (@lem3916113 _100908 a b) (@lem3916090 _100908 a b)). Qed.
Lemma lem3916115 {_100908 : Type'} (b : _100908 -> Prop) : (term711 _100908 b) = (term711 _100908 b).
Proof. exact (fun_ext (fun a : _100908 -> Prop => @lem3916114 _100908 a b)). Qed.
Lemma lem3916116 {_100908 : Type'} : (@all (_100908 -> Prop)) = (@all (_100908 -> Prop)).
Proof. exact (eq_refl (@all (_100908 -> Prop))). Qed.
Lemma lem3916117 {_100908 : Type'} (b : _100908 -> Prop) : (term713 _100908 b) = (term713 _100908 b).
Proof. exact (MK_COMB (@lem3916116 _100908) (@lem3916115 _100908 b)). Qed.
Lemma lem3916118 {_100908 : Type'} : (term715 _100908) = (term715 _100908).
Proof. exact (fun_ext (fun b : _100908 -> Prop => @lem3916117 _100908 b)). Qed.
Lemma lem3916119 {_100908 : Type'} : (@all (_100908 -> Prop)) = (@all (_100908 -> Prop)).
Proof. exact (eq_refl (@all (_100908 -> Prop))). Qed.
Lemma lem3916120 {_100908 : Type'} : (term717 _100908) = (term717 _100908).
Proof. exact (MK_COMB (@lem3916119 _100908) (@lem3916118 _100908)). Qed.
Lemma lem3916171 {_100908 : Type'} : (term716 _100908) = (term717 _100908).
Proof. exact (TRANS (@lem3916063 _100908) (@lem3916120 _100908)). Qed.
Lemma lem3916172 {_100908 : Type'} : (term717 _100908) = (term716 _100908).
Proof. exact (SYM (@lem3916171 _100908)). Qed.
Lemma lem3916174 (p : Prop) : p = (term703 p).
Proof. exact (EQ_MP (@lem10578 p) (@lem10597 p)). Qed.
Lemma lem3916175 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term684 _100908 a b) = (term702 _100908 a b)) = (term704 _100908 a b).
Proof. exact (@lem3916174 ((term684 _100908 a b) = (term702 _100908 a b))). Qed.
Lemma lem3916176 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term704 _100908 a b) = ((term684 _100908 a b) = (term702 _100908 a b)).
Proof. exact (SYM (@lem3916175 _100908 a b)). Qed.
Lemma lem3916177 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : term705 _100908 a b.
Proof. exact (h1). Qed.
Lemma lem3916186 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term718 _100908 a b x) = (term719 _100908 a b x).
Proof. exact (@lem17362 (a x) (b x)). Qed.
Lemma lem3916191 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term673 _100908 a b x) = (term720 _100908 a b x).
Proof. exact (@lem17265 (a x) (b x)). Qed.
Lemma lem3916192 {_100908 : Type'} (P : _100908 -> Prop) : (term721 _100908 P) = (term722 _100908 P).
Proof. exact (@lem18392 _100908 P). Qed.
Lemma lem3916193 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term723 _100908 a b) = (term724 _100908 a b).
Proof. exact (@lem3916192 _100908 (term675 _100908 a b)). Qed.
Lemma lem3916194 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term725 _100908 a b x) = (term673 _100908 a b x).
Proof. exact (eq_refl (term725 _100908 a b x)). Qed.
Lemma lem3916195 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3916196 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term726 _100908 a b x) = (term718 _100908 a b x).
Proof. exact (MK_COMB (@lem3916195) (@lem3916194 _100908 a b x)). Qed.
Lemma lem3916197 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term726 _100908 a b x) = (term719 _100908 a b x).
Proof. exact (TRANS (@lem3916196 _100908 a b x) (@lem3916186 _100908 a b x)). Qed.
Lemma lem3916198 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term727 _100908 a b) = (term728 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916197 _100908 a b x)). Qed.
Lemma lem3916199 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916200 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term724 _100908 a b) = (term729 _100908 a b).
Proof. exact (MK_COMB (@lem3916199 _100908) (@lem3916198 _100908 a b)). Qed.
Lemma lem3916201 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term723 _100908 a b) = (term729 _100908 a b).
Proof. exact (TRANS (@lem3916193 _100908 a b) (@lem3916200 _100908 a b)). Qed.
Lemma lem3916202 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term675 _100908 a b) = (term730 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916191 _100908 a b x)). Qed.
Lemma lem3916203 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916204 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term676 _100908 a b) = (term731 _100908 a b).
Proof. exact (MK_COMB (@lem3916203 _100908) (@lem3916202 _100908 a b)). Qed.
Lemma lem3916219 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term732 _100908 a b x) = (term733 _100908 a b x).
Proof. exact (@lem17930 (a x) (b x)). Qed.
Lemma lem3916230 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : ((a x) = (b x)) = (term734 _100908 a b x).
Proof. exact (@lem17784 (a x) (b x)). Qed.
Lemma lem3916231 {_100908 : Type'} (P : _100908 -> Prop) : (term721 _100908 P) = (term722 _100908 P).
Proof. exact (@lem18392 _100908 P). Qed.
Lemma lem3916232 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term683 _100908 a b) = (term735 _100908 a b).
Proof. exact (@lem3916231 _100908 (term681 _100908 a b)). Qed.
Lemma lem3916233 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term736 _100908 a b x) = ((a x) = (b x)).
Proof. exact (eq_refl (term736 _100908 a b x)). Qed.
Lemma lem3916234 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3916235 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term737 _100908 a b x) = (term732 _100908 a b x).
Proof. exact (MK_COMB (@lem3916234) (@lem3916233 _100908 a b x)). Qed.
Lemma lem3916236 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term737 _100908 a b x) = (term733 _100908 a b x).
Proof. exact (TRANS (@lem3916235 _100908 a b x) (@lem3916219 _100908 a b x)). Qed.
Lemma lem3916237 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term738 _100908 a b) = (term739 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916236 _100908 a b x)). Qed.
Lemma lem3916238 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916239 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term735 _100908 a b) = (term740 _100908 a b).
Proof. exact (MK_COMB (@lem3916238 _100908) (@lem3916237 _100908 a b)). Qed.
Lemma lem3916240 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term683 _100908 a b) = (term740 _100908 a b).
Proof. exact (TRANS (@lem3916232 _100908 a b) (@lem3916239 _100908 a b)). Qed.
Lemma lem3916241 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term681 _100908 a b) = (term741 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916230 _100908 a b x)). Qed.
Lemma lem3916242 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916243 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term682 _100908 a b) = (term742 _100908 a b).
Proof. exact (MK_COMB (@lem3916242 _100908) (@lem3916241 _100908 a b)). Qed.
Lemma lem3916244 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term743 _100908 a b) = (term682 _100908 a b).
Proof. exact (@lem16933 (term682 _100908 a b)). Qed.
Lemma lem3916245 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term743 _100908 a b) = (term742 _100908 a b).
Proof. exact (TRANS (@lem3916244 _100908 a b) (@lem3916243 _100908 a b)). Qed.
Lemma lem3916246 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916247 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term744 _100908 a b) = (term745 _100908 a b).
Proof. exact (MK_COMB (@lem3916246) (@lem3916201 _100908 a b)). Qed.
Lemma lem3916248 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term746 _100908 a b) = (term747 _100908 a b).
Proof. exact (MK_COMB (@lem3916247 _100908 a b) (@lem3916245 _100908 a b)). Qed.
Lemma lem3916249 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term748 _100908 a b) = (term746 _100908 a b).
Proof. exact (@lem17045 (term676 _100908 a b) (term683 _100908 a b)). Qed.
Lemma lem3916250 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term748 _100908 a b) = (term747 _100908 a b).
Proof. exact (TRANS (@lem3916249 _100908 a b) (@lem3916248 _100908 a b)). Qed.
Lemma lem3916251 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916252 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term677 _100908 a b) = (term749 _100908 a b).
Proof. exact (MK_COMB (@lem3916251) (@lem3916204 _100908 a b)). Qed.
Lemma lem3916253 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term684 _100908 a b) = (term750 _100908 a b).
Proof. exact (MK_COMB (@lem3916252 _100908 a b) (@lem3916240 _100908 a b)). Qed.
Lemma lem3916259 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term751 _100908 a x) = (a x).
Proof. exact (@lem16933 (a x)). Qed.
Lemma lem3916267 {_100908 : Type'} (x' : _100908) (x : _100908) : (term752 _100908 x' x) = (x' = x).
Proof. exact (@lem16933 (x' = x)). Qed.
Lemma lem3916269 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) : (term753 _100908 b x') = (term753 _100908 b x').
Proof. exact (eq_refl (term753 _100908 b x')). Qed.
Lemma lem3916270 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term754 _100908 b x' x) = (term755 _100908 b x' x).
Proof. exact (MK_COMB (@lem3916269 _100908 b x') (@lem3916267 _100908 x' x)). Qed.
Lemma lem3916271 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term756 _100908 b x' x) = (term754 _100908 b x' x).
Proof. exact (@lem17045 (b x') (term692 _100908 x' x)). Qed.
Lemma lem3916272 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term756 _100908 b x' x) = (term755 _100908 b x' x).
Proof. exact (TRANS (@lem3916271 _100908 b x' x) (@lem3916270 _100908 b x' x)). Qed.
Lemma lem3916277 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908) : (term686 _100908 a x') = (term686 _100908 a x').
Proof. exact (eq_refl (term686 _100908 a x')). Qed.
Lemma lem3916278 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term757 _100908 a b x' x) = (term758 _100908 a b x' x).
Proof. exact (MK_COMB (@lem3916277 _100908 a x') (@lem3916272 _100908 b x' x)). Qed.
Lemma lem3916279 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term759 _100908 a b x' x) = (term757 _100908 a b x' x).
Proof. exact (@lem17362 (a x') (term693 _100908 b x' x)). Qed.
Lemma lem3916280 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term759 _100908 a b x' x) = (term758 _100908 a b x' x).
Proof. exact (TRANS (@lem3916279 _100908 a b x' x) (@lem3916278 _100908 a b x' x)). Qed.
Lemma lem3916285 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term695 _100908 a b x' x) = (term760 _100908 a b x' x).
Proof. exact (@lem17265 (a x') (term693 _100908 b x' x)). Qed.
Lemma lem3916286 {_100908 : Type'} (P : _100908 -> Prop) : (term721 _100908 P) = (term722 _100908 P).
Proof. exact (@lem18392 _100908 P). Qed.
Lemma lem3916287 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term761 _100908 a b x) = (term762 _100908 a b x).
Proof. exact (@lem3916286 _100908 (term697 _100908 a b x)). Qed.
Lemma lem3916288 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term763 _100908 a b x x') = (term695 _100908 a b x' x).
Proof. exact (eq_refl (term763 _100908 a b x x')). Qed.
Lemma lem3916289 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3916290 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term764 _100908 a b x x') = (term759 _100908 a b x' x).
Proof. exact (MK_COMB (@lem3916289) (@lem3916288 _100908 a b x' x)). Qed.
Lemma lem3916291 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term764 _100908 a b x x') = (term758 _100908 a b x' x).
Proof. exact (TRANS (@lem3916290 _100908 a b x' x) (@lem3916280 _100908 a b x' x)). Qed.
Lemma lem3916292 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term765 _100908 a b x) = (term766 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916291 _100908 a b x' x)). Qed.
Lemma lem3916293 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916294 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term762 _100908 a b x) = (term767 _100908 a b x).
Proof. exact (MK_COMB (@lem3916293 _100908) (@lem3916292 _100908 a b x)). Qed.
Lemma lem3916295 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term761 _100908 a b x) = (term767 _100908 a b x).
Proof. exact (TRANS (@lem3916287 _100908 a b x) (@lem3916294 _100908 a b x)). Qed.
Lemma lem3916296 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term697 _100908 a b x) = (term768 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916285 _100908 a b x' x)). Qed.
Lemma lem3916297 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916298 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term698 _100908 a b x) = (term769 _100908 a b x).
Proof. exact (MK_COMB (@lem3916297 _100908) (@lem3916296 _100908 a b x)). Qed.
Lemma lem3916299 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916300 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term770 _100908 a x) = (term771 _100908 a x).
Proof. exact (MK_COMB (@lem3916299) (@lem3916259 _100908 a x)). Qed.
Lemma lem3916301 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term772 _100908 a b x) = (term773 _100908 a b x).
Proof. exact (MK_COMB (@lem3916300 _100908 a x) (@lem3916295 _100908 a b x)). Qed.
Lemma lem3916302 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term774 _100908 a b x) = (term772 _100908 a b x).
Proof. exact (@lem17045 (term688 _100908 a x) (term698 _100908 a b x)). Qed.
Lemma lem3916303 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term774 _100908 a b x) = (term773 _100908 a b x).
Proof. exact (TRANS (@lem3916302 _100908 a b x) (@lem3916301 _100908 a b x)). Qed.
Lemma lem3916305 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term689 _100908 a x) = (term689 _100908 a x).
Proof. exact (eq_refl (term689 _100908 a x)). Qed.
Lemma lem3916306 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term699 _100908 a b x) = (term775 _100908 a b x).
Proof. exact (MK_COMB (@lem3916305 _100908 a x) (@lem3916298 _100908 a b x)). Qed.
Lemma lem3916308 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term753 _100908 b x) = (term753 _100908 b x).
Proof. exact (eq_refl (term753 _100908 b x)). Qed.
Lemma lem3916309 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term776 _100908 a b x) = (term777 _100908 a b x).
Proof. exact (MK_COMB (@lem3916308 _100908 b x) (@lem3916303 _100908 a b x)). Qed.
Lemma lem3916310 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term778 _100908 a b x) = (term776 _100908 a b x).
Proof. exact (@lem17045 (b x) (term699 _100908 a b x)). Qed.
Lemma lem3916311 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term778 _100908 a b x) = (term777 _100908 a b x).
Proof. exact (TRANS (@lem3916310 _100908 a b x) (@lem3916309 _100908 a b x)). Qed.
Lemma lem3916313 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term686 _100908 b x) = (term686 _100908 b x).
Proof. exact (eq_refl (term686 _100908 b x)). Qed.
Lemma lem3916314 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term700 _100908 a b x) = (term779 _100908 a b x).
Proof. exact (MK_COMB (@lem3916313 _100908 b x) (@lem3916306 _100908 a b x)). Qed.
Lemma lem3916315 {_100908 : Type'} (P : _100908 -> Prop) : (term780 _100908 P) = (term781 _100908 P).
Proof. exact (@lem18394 _100908 P). Qed.
Lemma lem3916316 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term782 _100908 a b) = (term783 _100908 a b).
Proof. exact (@lem3916315 _100908 (term701 _100908 a b)). Qed.
Lemma lem3916317 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term784 _100908 a b x) = (term700 _100908 a b x).
Proof. exact (eq_refl (term784 _100908 a b x)). Qed.
Lemma lem3916318 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3916319 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term785 _100908 a b x) = (term778 _100908 a b x).
Proof. exact (MK_COMB (@lem3916318) (@lem3916317 _100908 a b x)). Qed.
Lemma lem3916320 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term785 _100908 a b x) = (term777 _100908 a b x).
Proof. exact (TRANS (@lem3916319 _100908 a b x) (@lem3916311 _100908 a b x)). Qed.
Lemma lem3916321 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term786 _100908 a b) = (term787 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916320 _100908 a b x)). Qed.
Lemma lem3916322 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916323 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term783 _100908 a b) = (term788 _100908 a b).
Proof. exact (MK_COMB (@lem3916322 _100908) (@lem3916321 _100908 a b)). Qed.
Lemma lem3916324 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term782 _100908 a b) = (term788 _100908 a b).
Proof. exact (TRANS (@lem3916316 _100908 a b) (@lem3916323 _100908 a b)). Qed.
Lemma lem3916325 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term701 _100908 a b) = (term789 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916314 _100908 a b x)). Qed.
Lemma lem3916326 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916327 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term702 _100908 a b) = (term790 _100908 a b).
Proof. exact (MK_COMB (@lem3916326 _100908) (@lem3916325 _100908 a b)). Qed.
Lemma lem3916328 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916329 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term791 _100908 a b) = (term792 _100908 a b).
Proof. exact (MK_COMB (@lem3916328) (@lem3916250 _100908 a b)). Qed.
Lemma lem3916330 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term793 _100908 a b) = (term794 _100908 a b).
Proof. exact (MK_COMB (@lem3916329 _100908 a b) (@lem3916327 _100908 a b)). Qed.
Lemma lem3916331 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916332 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term795 _100908 a b) = (term796 _100908 a b).
Proof. exact (MK_COMB (@lem3916331) (@lem3916253 _100908 a b)). Qed.
Lemma lem3916333 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term797 _100908 a b) = (term798 _100908 a b).
Proof. exact (MK_COMB (@lem3916332 _100908 a b) (@lem3916324 _100908 a b)). Qed.
Lemma lem3916334 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916335 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term799 _100908 a b) = (term800 _100908 a b).
Proof. exact (MK_COMB (@lem3916334) (@lem3916333 _100908 a b)). Qed.
Lemma lem3916336 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term801 _100908 a b) = (term802 _100908 a b).
Proof. exact (MK_COMB (@lem3916335 _100908 a b) (@lem3916330 _100908 a b)). Qed.
Lemma lem3916337 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term705 _100908 a b) = (term801 _100908 a b).
Proof. exact (@lem17646 (term684 _100908 a b) (term702 _100908 a b)). Qed.
Lemma lem3916338 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term705 _100908 a b) = (term802 _100908 a b).
Proof. exact (TRANS (@lem3916337 _100908 a b) (@lem3916336 _100908 a b)). Qed.
Lemma lem3916524 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term803 A P Q) = (term804 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3916525 {_100908 : Type'} (P : _100908 -> Prop) (Q : _100908 -> Prop) : (term803 _100908 P Q) = (term804 _100908 P Q).
Proof. exact (@lem3916524 _100908 P Q). Qed.
Lemma lem3916526 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term805 _100908 a b) = (term806 _100908 a b).
Proof. exact (@lem3916525 _100908 (term807 _100908 a b) (term730 _100908 a b)). Qed.
Lemma lem3916527 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term808 _100908 a b x) = (term809 _100908 a b x).
Proof. exact (eq_refl (term808 _100908 a b x)). Qed.
Lemma lem3916528 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916529 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term810 _100908 a b x) = (term811 _100908 a b x).
Proof. exact (MK_COMB (@lem3916528) (@lem3916527 _100908 a b x)). Qed.
Lemma lem3916530 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term812 _100908 a b x) = (term720 _100908 a b x).
Proof. exact (eq_refl (term812 _100908 a b x)). Qed.
Lemma lem3916531 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term813 _100908 a b x) = (term734 _100908 a b x).
Proof. exact (MK_COMB (@lem3916529 _100908 a b x) (@lem3916530 _100908 a b x)). Qed.
Lemma lem3916532 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term814 _100908 a b) = (term741 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916531 _100908 a b x)). Qed.
Lemma lem3916533 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916534 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term805 _100908 a b) = (term742 _100908 a b).
Proof. exact (MK_COMB (@lem3916533 _100908) (@lem3916532 _100908 a b)). Qed.
Lemma lem3916535 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916536 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term815 _100908 a b) = (term816 _100908 a b).
Proof. exact (MK_COMB (@lem3916535) (@lem3916534 _100908 a b)). Qed.
Lemma lem3916537 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term808 _100908 a b x) = (term809 _100908 a b x).
Proof. exact (eq_refl (term808 _100908 a b x)). Qed.
Lemma lem3916538 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term817 _100908 a b) = (term807 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916537 _100908 a b x)). Qed.
Lemma lem3916539 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916540 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term818 _100908 a b) = (term819 _100908 a b).
Proof. exact (MK_COMB (@lem3916539 _100908) (@lem3916538 _100908 a b)). Qed.
Lemma lem3916541 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916542 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term820 _100908 a b) = (term821 _100908 a b).
Proof. exact (MK_COMB (@lem3916541) (@lem3916540 _100908 a b)). Qed.
Lemma lem3916543 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term812 _100908 a b x) = (term720 _100908 a b x).
Proof. exact (eq_refl (term812 _100908 a b x)). Qed.
Lemma lem3916544 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term822 _100908 a b) = (term730 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916543 _100908 a b x)). Qed.
Lemma lem3916545 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916546 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term823 _100908 a b) = (term731 _100908 a b).
Proof. exact (MK_COMB (@lem3916545 _100908) (@lem3916544 _100908 a b)). Qed.
Lemma lem3916547 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term806 _100908 a b) = (term824 _100908 a b).
Proof. exact (MK_COMB (@lem3916542 _100908 a b) (@lem3916546 _100908 a b)). Qed.
Lemma lem3916548 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term805 _100908 a b) = (term806 _100908 a b)) = ((term742 _100908 a b) = (term824 _100908 a b)).
Proof. exact (MK_COMB (@lem3916536 _100908 a b) (@lem3916547 _100908 a b)). Qed.
Lemma lem3916549 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term742 _100908 a b) = (term824 _100908 a b).
Proof. exact (EQ_MP (@lem3916548 _100908 a b) (@lem3916526 _100908 a b)). Qed.
Lemma lem3916610 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term745 _100908 a b) = (term745 _100908 a b).
Proof. exact (eq_refl (term745 _100908 a b)). Qed.
Lemma lem3916611 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term747 _100908 a b) = (term825 _100908 a b).
Proof. exact (MK_COMB (@lem3916610 _100908 a b) (@lem3916549 _100908 a b)). Qed.
Lemma lem3916612 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916613 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term792 _100908 a b) = (term826 _100908 a b).
Proof. exact (MK_COMB (@lem3916612) (@lem3916611 _100908 a b)). Qed.
Lemma lem3916690 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term790 _100908 a b) = (term790 _100908 a b).
Proof. exact (eq_refl (term790 _100908 a b)). Qed.
Lemma lem3916691 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term794 _100908 a b) = (term827 _100908 a b).
Proof. exact (MK_COMB (@lem3916613 _100908 a b) (@lem3916690 _100908 a b)). Qed.
Lemma lem3916692 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term800 _100908 a b) = (term800 _100908 a b).
Proof. exact (eq_refl (term800 _100908 a b)). Qed.
Lemma lem3916693 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term802 _100908 a b) = (term828 _100908 a b).
Proof. exact (MK_COMB (@lem3916692 _100908 a b) (@lem3916691 _100908 a b)). Qed.
Lemma lem3916695 {A : Type'} (P : Prop) (Q : A -> Prop) : (term829 A P Q) = (term830 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3916696 {_100908 : Type'} (P : Prop) (Q : _100908 -> Prop) : (term829 _100908 P Q) = (term830 _100908 P Q).
Proof. exact (@lem3916695 _100908 P Q). Qed.
Lemma lem3916697 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term831 _100908 a b) = (term832 _100908 a b).
Proof. exact (@lem3916696 _100908 (term731 _100908 a b) (term739 _100908 a b)). Qed.
Lemma lem3916698 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term833 _100908 a b x) = (term733 _100908 a b x).
Proof. exact (eq_refl (term833 _100908 a b x)). Qed.
Lemma lem3916699 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term834 _100908 a b) = (term739 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916698 _100908 a b x)). Qed.
Lemma lem3916700 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916701 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term835 _100908 a b) = (term740 _100908 a b).
Proof. exact (MK_COMB (@lem3916700 _100908) (@lem3916699 _100908 a b)). Qed.
Lemma lem3916702 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term749 _100908 a b) = (term749 _100908 a b).
Proof. exact (eq_refl (term749 _100908 a b)). Qed.
Lemma lem3916703 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term831 _100908 a b) = (term750 _100908 a b).
Proof. exact (MK_COMB (@lem3916702 _100908 a b) (@lem3916701 _100908 a b)). Qed.
Lemma lem3916704 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916705 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term836 _100908 a b) = (term837 _100908 a b).
Proof. exact (MK_COMB (@lem3916704) (@lem3916703 _100908 a b)). Qed.
Lemma lem3916706 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term833 _100908 a b x) = (term733 _100908 a b x).
Proof. exact (eq_refl (term833 _100908 a b x)). Qed.
Lemma lem3916707 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term749 _100908 a b) = (term749 _100908 a b).
Proof. exact (eq_refl (term749 _100908 a b)). Qed.
Lemma lem3916708 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term838 _100908 a b x) = (term839 _100908 a b x).
Proof. exact (MK_COMB (@lem3916707 _100908 a b) (@lem3916706 _100908 a b x)). Qed.
Lemma lem3916709 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term840 _100908 a b) = (term841 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916708 _100908 a b x)). Qed.
Lemma lem3916710 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916711 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term832 _100908 a b) = (term842 _100908 a b).
Proof. exact (MK_COMB (@lem3916710 _100908) (@lem3916709 _100908 a b)). Qed.
Lemma lem3916712 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term831 _100908 a b) = (term832 _100908 a b)) = ((term750 _100908 a b) = (term842 _100908 a b)).
Proof. exact (MK_COMB (@lem3916705 _100908 a b) (@lem3916711 _100908 a b)). Qed.
Lemma lem3916713 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term750 _100908 a b) = (term842 _100908 a b).
Proof. exact (EQ_MP (@lem3916712 _100908 a b) (@lem3916697 _100908 a b)). Qed.
Lemma lem3916714 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916715 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term796 _100908 a b) = (term843 _100908 a b).
Proof. exact (MK_COMB (@lem3916714) (@lem3916713 _100908 a b)). Qed.
Lemma lem3916717 {A : Type'} (P : Prop) (Q : A -> Prop) : (term844 A P Q) = (term845 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3916718 {_100908 : Type'} (P : Prop) (Q : _100908 -> Prop) : (term844 _100908 P Q) = (term845 _100908 P Q).
Proof. exact (@lem3916717 _100908 P Q). Qed.
Lemma lem3916719 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term846 _100908 a b x) = (term847 _100908 a b x).
Proof. exact (@lem3916718 _100908 (a x) (term766 _100908 a b x)). Qed.
Lemma lem3916720 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term848 _100908 a b x x') = (term758 _100908 a b x' x).
Proof. exact (eq_refl (term848 _100908 a b x x')). Qed.
Lemma lem3916721 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term849 _100908 a b x) = (term766 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916720 _100908 a b x' x)). Qed.
Lemma lem3916722 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916723 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term850 _100908 a b x) = (term767 _100908 a b x).
Proof. exact (MK_COMB (@lem3916722 _100908) (@lem3916721 _100908 a b x)). Qed.
Lemma lem3916724 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term771 _100908 a x) = (term771 _100908 a x).
Proof. exact (eq_refl (term771 _100908 a x)). Qed.
Lemma lem3916725 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term846 _100908 a b x) = (term773 _100908 a b x).
Proof. exact (MK_COMB (@lem3916724 _100908 a x) (@lem3916723 _100908 a b x)). Qed.
Lemma lem3916726 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916727 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term851 _100908 a b x) = (term852 _100908 a b x).
Proof. exact (MK_COMB (@lem3916726) (@lem3916725 _100908 a b x)). Qed.
Lemma lem3916728 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term848 _100908 a b x x') = (term758 _100908 a b x' x).
Proof. exact (eq_refl (term848 _100908 a b x x')). Qed.
Lemma lem3916729 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term771 _100908 a x) = (term771 _100908 a x).
Proof. exact (eq_refl (term771 _100908 a x)). Qed.
Lemma lem3916730 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term853 _100908 a b x x') = (term854 _100908 a b x' x).
Proof. exact (MK_COMB (@lem3916729 _100908 a x) (@lem3916728 _100908 a b x' x)). Qed.
Lemma lem3916731 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term855 _100908 a b x) = (term856 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916730 _100908 a b x' x)). Qed.
Lemma lem3916732 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916733 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term847 _100908 a b x) = (term857 _100908 a b x).
Proof. exact (MK_COMB (@lem3916732 _100908) (@lem3916731 _100908 a b x)). Qed.
Lemma lem3916734 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : ((term846 _100908 a b x) = (term847 _100908 a b x)) = ((term773 _100908 a b x) = (term857 _100908 a b x)).
Proof. exact (MK_COMB (@lem3916727 _100908 a b x) (@lem3916733 _100908 a b x)). Qed.
Lemma lem3916735 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term773 _100908 a b x) = (term857 _100908 a b x).
Proof. exact (EQ_MP (@lem3916734 _100908 a b x) (@lem3916719 _100908 a b x)). Qed.
Lemma lem3916736 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term753 _100908 b x) = (term753 _100908 b x).
Proof. exact (eq_refl (term753 _100908 b x)). Qed.
Lemma lem3916737 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term777 _100908 a b x) = (term858 _100908 a b x).
Proof. exact (MK_COMB (@lem3916736 _100908 b x) (@lem3916735 _100908 a b x)). Qed.
Lemma lem3916739 {A : Type'} (P : Prop) (Q : A -> Prop) : (term844 A P Q) = (term845 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3916740 {_100908 : Type'} (P : Prop) (Q : _100908 -> Prop) : (term844 _100908 P Q) = (term845 _100908 P Q).
Proof. exact (@lem3916739 _100908 P Q). Qed.
Lemma lem3916741 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term859 _100908 a b x) = (term860 _100908 a b x).
Proof. exact (@lem3916740 _100908 (term688 _100908 b x) (term856 _100908 a b x)). Qed.
Lemma lem3916742 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term861 _100908 a b x x') = (term854 _100908 a b x' x).
Proof. exact (eq_refl (term861 _100908 a b x x')). Qed.
Lemma lem3916743 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term862 _100908 a b x) = (term856 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916742 _100908 a b x' x)). Qed.
Lemma lem3916744 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916745 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term863 _100908 a b x) = (term857 _100908 a b x).
Proof. exact (MK_COMB (@lem3916744 _100908) (@lem3916743 _100908 a b x)). Qed.
Lemma lem3916746 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term753 _100908 b x) = (term753 _100908 b x).
Proof. exact (eq_refl (term753 _100908 b x)). Qed.
Lemma lem3916747 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term859 _100908 a b x) = (term858 _100908 a b x).
Proof. exact (MK_COMB (@lem3916746 _100908 b x) (@lem3916745 _100908 a b x)). Qed.
Lemma lem3916748 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916749 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term864 _100908 a b x) = (term865 _100908 a b x).
Proof. exact (MK_COMB (@lem3916748) (@lem3916747 _100908 a b x)). Qed.
Lemma lem3916750 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term861 _100908 a b x x') = (term854 _100908 a b x' x).
Proof. exact (eq_refl (term861 _100908 a b x x')). Qed.
Lemma lem3916751 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term753 _100908 b x) = (term753 _100908 b x).
Proof. exact (eq_refl (term753 _100908 b x)). Qed.
Lemma lem3916752 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term866 _100908 a b x x') = (term867 _100908 a b x' x).
Proof. exact (MK_COMB (@lem3916751 _100908 b x) (@lem3916750 _100908 a b x' x)). Qed.
Lemma lem3916753 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term868 _100908 a b x) = (term869 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916752 _100908 a b x' x)). Qed.
Lemma lem3916754 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916755 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term860 _100908 a b x) = (term870 _100908 a b x).
Proof. exact (MK_COMB (@lem3916754 _100908) (@lem3916753 _100908 a b x)). Qed.
Lemma lem3916756 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : ((term859 _100908 a b x) = (term860 _100908 a b x)) = ((term858 _100908 a b x) = (term870 _100908 a b x)).
Proof. exact (MK_COMB (@lem3916749 _100908 a b x) (@lem3916755 _100908 a b x)). Qed.
Lemma lem3916757 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term858 _100908 a b x) = (term870 _100908 a b x).
Proof. exact (EQ_MP (@lem3916756 _100908 a b x) (@lem3916741 _100908 a b x)). Qed.
Lemma lem3916758 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term777 _100908 a b x) = (term870 _100908 a b x).
Proof. exact (TRANS (@lem3916737 _100908 a b x) (@lem3916757 _100908 a b x)). Qed.
Lemma lem3916759 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term787 _100908 a b) = (term871 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916758 _100908 a b x)). Qed.
Lemma lem3916760 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916761 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term788 _100908 a b) = (term872 _100908 a b).
Proof. exact (MK_COMB (@lem3916760 _100908) (@lem3916759 _100908 a b)). Qed.
Lemma lem3916763 {A B : Type'} (P : type1413 A B) : (term873 A B P) = (term874 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3916764 {_100908 : Type'} (P : type1402 _100908) : (term875 _100908 P) = (term876 _100908 P).
Proof. exact (@lem3916763 _100908 _100908 P). Qed.
Lemma lem3916765 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term877 _100908 a b) = (term878 _100908 a b).
Proof. exact (@lem3916764 _100908 (term879 _100908 a b)). Qed.
Lemma lem3916766 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term880 _100908 a b x) = (term869 _100908 a b x).
Proof. exact (eq_refl (term880 _100908 a b x)). Qed.
Lemma lem3916767 {_100908 : Type'} (x' : _100908) : x' = x'.
Proof. exact (eq_refl x'). Qed.
Lemma lem3916768 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (x' : _100908) : (term881 _100908 a b x x') = (term882 _100908 a b x x').
Proof. exact (MK_COMB (@lem3916766 _100908 a b x) (@lem3916767 _100908 x')). Qed.
Lemma lem3916769 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term882 _100908 a b x x') = (term867 _100908 a b x' x).
Proof. exact (eq_refl (term882 _100908 a b x x')). Qed.
Lemma lem3916770 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) (x : _100908) : (term881 _100908 a b x x') = (term867 _100908 a b x' x).
Proof. exact (TRANS (@lem3916768 _100908 a b x x') (@lem3916769 _100908 a b x' x)). Qed.
Lemma lem3916771 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term883 _100908 a b x) = (term869 _100908 a b x).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916770 _100908 a b x' x)). Qed.
Lemma lem3916772 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916773 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term884 _100908 a b x) = (term870 _100908 a b x).
Proof. exact (MK_COMB (@lem3916772 _100908) (@lem3916771 _100908 a b x)). Qed.
Lemma lem3916774 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term885 _100908 a b) = (term871 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916773 _100908 a b x)). Qed.
Lemma lem3916775 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916776 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term877 _100908 a b) = (term872 _100908 a b).
Proof. exact (MK_COMB (@lem3916775 _100908) (@lem3916774 _100908 a b)). Qed.
Lemma lem3916777 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916778 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term886 _100908 a b) = (term887 _100908 a b).
Proof. exact (MK_COMB (@lem3916777) (@lem3916776 _100908 a b)). Qed.
Lemma lem3916779 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term880 _100908 a b x) = (term869 _100908 a b x).
Proof. exact (eq_refl (term880 _100908 a b x)). Qed.
Lemma lem3916780 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) : (x' x) = (x' x).
Proof. exact (eq_refl (x' x)). Qed.
Lemma lem3916781 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term888 _100908 a b x' x) = (term889 _100908 a b x' x).
Proof. exact (MK_COMB (@lem3916779 _100908 a b x) (@lem3916780 _100908 x' x)). Qed.
Lemma lem3916782 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term889 _100908 a b x' x) = (term890 _100908 a b x' x).
Proof. exact (eq_refl (term889 _100908 a b x' x)). Qed.
Lemma lem3916783 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term888 _100908 a b x' x) = (term890 _100908 a b x' x).
Proof. exact (TRANS (@lem3916781 _100908 a b x' x) (@lem3916782 _100908 a b x' x)). Qed.
Lemma lem3916784 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term891 _100908 a b x') = (term892 _100908 a b x').
Proof. exact (fun_ext (fun x : _100908 => @lem3916783 _100908 a b x' x)). Qed.
Lemma lem3916785 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3916786 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term893 _100908 a b x') = (term894 _100908 a b x').
Proof. exact (MK_COMB (@lem3916785 _100908) (@lem3916784 _100908 a b x')). Qed.
Lemma lem3916787 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term895 _100908 a b) = (term896 _100908 a b).
Proof. exact (fun_ext (fun x' : _100908 -> _100908 => @lem3916786 _100908 a b x')). Qed.
Lemma lem3916788 {_100908 : Type'} : (@ex (_100908 -> _100908)) = (@ex (_100908 -> _100908)).
Proof. exact (eq_refl (@ex (_100908 -> _100908))). Qed.
Lemma lem3916789 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term878 _100908 a b) = (term897 _100908 a b).
Proof. exact (MK_COMB (@lem3916788 _100908) (@lem3916787 _100908 a b)). Qed.
Lemma lem3916790 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term877 _100908 a b) = (term878 _100908 a b)) = ((term872 _100908 a b) = (term897 _100908 a b)).
Proof. exact (MK_COMB (@lem3916778 _100908 a b) (@lem3916789 _100908 a b)). Qed.
Lemma lem3916791 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term872 _100908 a b) = (term897 _100908 a b).
Proof. exact (EQ_MP (@lem3916790 _100908 a b) (@lem3916765 _100908 a b)). Qed.
Lemma lem3916792 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term788 _100908 a b) = (term897 _100908 a b).
Proof. exact (TRANS (@lem3916761 _100908 a b) (@lem3916791 _100908 a b)). Qed.
Lemma lem3916793 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term798 _100908 a b) = (term898 _100908 a b).
Proof. exact (MK_COMB (@lem3916715 _100908 a b) (@lem3916792 _100908 a b)). Qed.
Lemma lem3916795 {A : Type'} (P : A -> Prop) (Q : Prop) : (term899 A P Q) = (term900 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3916796 {_100908 : Type'} (P : _100908 -> Prop) (Q : Prop) : (term899 _100908 P Q) = (term900 _100908 P Q).
Proof. exact (@lem3916795 _100908 P Q). Qed.
Lemma lem3916797 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term901 _100908 a b) = (term902 _100908 a b).
Proof. exact (@lem3916796 _100908 (term841 _100908 a b) (term897 _100908 a b)). Qed.
Lemma lem3916798 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term903 _100908 a b x) = (term839 _100908 a b x).
Proof. exact (eq_refl (term903 _100908 a b x)). Qed.
Lemma lem3916799 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term904 _100908 a b) = (term841 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916798 _100908 a b x)). Qed.
Lemma lem3916800 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916801 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term905 _100908 a b) = (term842 _100908 a b).
Proof. exact (MK_COMB (@lem3916800 _100908) (@lem3916799 _100908 a b)). Qed.
Lemma lem3916802 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916803 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term906 _100908 a b) = (term843 _100908 a b).
Proof. exact (MK_COMB (@lem3916802) (@lem3916801 _100908 a b)). Qed.
Lemma lem3916804 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term897 _100908 a b) = (term897 _100908 a b).
Proof. exact (eq_refl (term897 _100908 a b)). Qed.
Lemma lem3916805 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term901 _100908 a b) = (term898 _100908 a b).
Proof. exact (MK_COMB (@lem3916803 _100908 a b) (@lem3916804 _100908 a b)). Qed.
Lemma lem3916806 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916807 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term907 _100908 a b) = (term908 _100908 a b).
Proof. exact (MK_COMB (@lem3916806) (@lem3916805 _100908 a b)). Qed.
Lemma lem3916808 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term903 _100908 a b x) = (term839 _100908 a b x).
Proof. exact (eq_refl (term903 _100908 a b x)). Qed.
Lemma lem3916809 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916810 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term909 _100908 a b x) = (term910 _100908 a b x).
Proof. exact (MK_COMB (@lem3916809) (@lem3916808 _100908 a b x)). Qed.
Lemma lem3916811 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term897 _100908 a b) = (term897 _100908 a b).
Proof. exact (eq_refl (term897 _100908 a b)). Qed.
Lemma lem3916812 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term911 _100908 x a b) = (term912 _100908 x a b).
Proof. exact (MK_COMB (@lem3916810 _100908 a b x) (@lem3916811 _100908 a b)). Qed.
Lemma lem3916813 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term913 _100908 a b) = (term914 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916812 _100908 x a b)). Qed.
Lemma lem3916814 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916815 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term902 _100908 a b) = (term915 _100908 a b).
Proof. exact (MK_COMB (@lem3916814 _100908) (@lem3916813 _100908 a b)). Qed.
Lemma lem3916816 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term901 _100908 a b) = (term902 _100908 a b)) = ((term898 _100908 a b) = (term915 _100908 a b)).
Proof. exact (MK_COMB (@lem3916807 _100908 a b) (@lem3916815 _100908 a b)). Qed.
Lemma lem3916817 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term898 _100908 a b) = (term915 _100908 a b).
Proof. exact (EQ_MP (@lem3916816 _100908 a b) (@lem3916797 _100908 a b)). Qed.
Lemma lem3916819 {A : Type'} (P : Prop) (Q : A -> Prop) : (term829 A P Q) = (term830 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3916820 {_100908 : Type'} (P : Prop) (Q : type488 _100908) : (term916 _100908 P Q) = (term917 _100908 P Q).
Proof. exact (@lem3916819 (_100908 -> _100908) P Q). Qed.
Lemma lem3916821 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term918 _100908 x a b) = (term919 _100908 x a b).
Proof. exact (@lem3916820 _100908 (term839 _100908 a b x) (term896 _100908 a b)). Qed.
Lemma lem3916822 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term920 _100908 a b x') = (term894 _100908 a b x').
Proof. exact (eq_refl (term920 _100908 a b x')). Qed.
Lemma lem3916823 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term921 _100908 a b) = (term896 _100908 a b).
Proof. exact (fun_ext (fun x' : _100908 -> _100908 => @lem3916822 _100908 a b x')). Qed.
Lemma lem3916824 {_100908 : Type'} : (@ex (_100908 -> _100908)) = (@ex (_100908 -> _100908)).
Proof. exact (eq_refl (@ex (_100908 -> _100908))). Qed.
Lemma lem3916825 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term922 _100908 a b) = (term897 _100908 a b).
Proof. exact (MK_COMB (@lem3916824 _100908) (@lem3916823 _100908 a b)). Qed.
Lemma lem3916826 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term910 _100908 a b x) = (term910 _100908 a b x).
Proof. exact (eq_refl (term910 _100908 a b x)). Qed.
Lemma lem3916827 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term918 _100908 x a b) = (term912 _100908 x a b).
Proof. exact (MK_COMB (@lem3916826 _100908 a b x) (@lem3916825 _100908 a b)). Qed.
Lemma lem3916828 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916829 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term923 _100908 x a b) = (term924 _100908 x a b).
Proof. exact (MK_COMB (@lem3916828) (@lem3916827 _100908 x a b)). Qed.
Lemma lem3916830 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term920 _100908 a b x') = (term894 _100908 a b x').
Proof. exact (eq_refl (term920 _100908 a b x')). Qed.
Lemma lem3916831 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term910 _100908 a b x) = (term910 _100908 a b x).
Proof. exact (eq_refl (term910 _100908 a b x)). Qed.
Lemma lem3916832 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term925 _100908 x a b x') = (term926 _100908 x a b x').
Proof. exact (MK_COMB (@lem3916831 _100908 a b x) (@lem3916830 _100908 a b x')). Qed.
Lemma lem3916833 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term927 _100908 x a b) = (term928 _100908 x a b).
Proof. exact (fun_ext (fun x' : _100908 -> _100908 => @lem3916832 _100908 x a b x')). Qed.
Lemma lem3916834 {_100908 : Type'} : (@ex (_100908 -> _100908)) = (@ex (_100908 -> _100908)).
Proof. exact (eq_refl (@ex (_100908 -> _100908))). Qed.
Lemma lem3916835 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term919 _100908 x a b) = (term929 _100908 x a b).
Proof. exact (MK_COMB (@lem3916834 _100908) (@lem3916833 _100908 x a b)). Qed.
Lemma lem3916836 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term918 _100908 x a b) = (term919 _100908 x a b)) = ((term912 _100908 x a b) = (term929 _100908 x a b)).
Proof. exact (MK_COMB (@lem3916829 _100908 x a b) (@lem3916835 _100908 x a b)). Qed.
Lemma lem3916837 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term912 _100908 x a b) = (term929 _100908 x a b).
Proof. exact (EQ_MP (@lem3916836 _100908 x a b) (@lem3916821 _100908 x a b)). Qed.
Lemma lem3916838 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term914 _100908 a b) = (term930 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916837 _100908 x a b)). Qed.
Lemma lem3916839 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916840 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term915 _100908 a b) = (term931 _100908 a b).
Proof. exact (MK_COMB (@lem3916839 _100908) (@lem3916838 _100908 a b)). Qed.
Lemma lem3916841 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term898 _100908 a b) = (term931 _100908 a b).
Proof. exact (TRANS (@lem3916817 _100908 a b) (@lem3916840 _100908 a b)). Qed.
Lemma lem3916842 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term798 _100908 a b) = (term931 _100908 a b).
Proof. exact (TRANS (@lem3916793 _100908 a b) (@lem3916841 _100908 a b)). Qed.
Lemma lem3916843 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916844 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term800 _100908 a b) = (term932 _100908 a b).
Proof. exact (MK_COMB (@lem3916843) (@lem3916842 _100908 a b)). Qed.
Lemma lem3916846 {A : Type'} (P : A -> Prop) (Q : Prop) : (term933 A P Q) = (term934 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3916847 {_100908 : Type'} (P : _100908 -> Prop) (Q : Prop) : (term933 _100908 P Q) = (term934 _100908 P Q).
Proof. exact (@lem3916846 _100908 P Q). Qed.
Lemma lem3916848 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term935 _100908 a b) = (term936 _100908 a b).
Proof. exact (@lem3916847 _100908 (term728 _100908 a b) (term824 _100908 a b)). Qed.
Lemma lem3916849 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term937 _100908 a b x) = (term719 _100908 a b x).
Proof. exact (eq_refl (term937 _100908 a b x)). Qed.
Lemma lem3916850 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term938 _100908 a b) = (term728 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916849 _100908 a b x)). Qed.
Lemma lem3916851 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916852 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term939 _100908 a b) = (term729 _100908 a b).
Proof. exact (MK_COMB (@lem3916851 _100908) (@lem3916850 _100908 a b)). Qed.
Lemma lem3916853 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916854 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term940 _100908 a b) = (term745 _100908 a b).
Proof. exact (MK_COMB (@lem3916853) (@lem3916852 _100908 a b)). Qed.
Lemma lem3916855 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term824 _100908 a b) = (term824 _100908 a b).
Proof. exact (eq_refl (term824 _100908 a b)). Qed.
Lemma lem3916856 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term935 _100908 a b) = (term825 _100908 a b).
Proof. exact (MK_COMB (@lem3916854 _100908 a b) (@lem3916855 _100908 a b)). Qed.
Lemma lem3916857 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916858 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term941 _100908 a b) = (term942 _100908 a b).
Proof. exact (MK_COMB (@lem3916857) (@lem3916856 _100908 a b)). Qed.
Lemma lem3916859 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term937 _100908 a b x) = (term719 _100908 a b x).
Proof. exact (eq_refl (term937 _100908 a b x)). Qed.
Lemma lem3916860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916861 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term943 _100908 a b x) = (term944 _100908 a b x).
Proof. exact (MK_COMB (@lem3916860) (@lem3916859 _100908 a b x)). Qed.
Lemma lem3916862 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term824 _100908 a b) = (term824 _100908 a b).
Proof. exact (eq_refl (term824 _100908 a b)). Qed.
Lemma lem3916863 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term945 _100908 x a b) = (term946 _100908 x a b).
Proof. exact (MK_COMB (@lem3916861 _100908 a b x) (@lem3916862 _100908 a b)). Qed.
Lemma lem3916864 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term947 _100908 a b) = (term948 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916863 _100908 x a b)). Qed.
Lemma lem3916865 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916866 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term936 _100908 a b) = (term949 _100908 a b).
Proof. exact (MK_COMB (@lem3916865 _100908) (@lem3916864 _100908 a b)). Qed.
Lemma lem3916867 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term935 _100908 a b) = (term936 _100908 a b)) = ((term825 _100908 a b) = (term949 _100908 a b)).
Proof. exact (MK_COMB (@lem3916858 _100908 a b) (@lem3916866 _100908 a b)). Qed.
Lemma lem3916868 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term825 _100908 a b) = (term949 _100908 a b).
Proof. exact (EQ_MP (@lem3916867 _100908 a b) (@lem3916848 _100908 a b)). Qed.
Lemma lem3916869 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916870 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term826 _100908 a b) = (term950 _100908 a b).
Proof. exact (MK_COMB (@lem3916869) (@lem3916868 _100908 a b)). Qed.
Lemma lem3916871 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term790 _100908 a b) = (term790 _100908 a b).
Proof. exact (eq_refl (term790 _100908 a b)). Qed.
Lemma lem3916872 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term827 _100908 a b) = (term951 _100908 a b).
Proof. exact (MK_COMB (@lem3916870 _100908 a b) (@lem3916871 _100908 a b)). Qed.
Lemma lem3916874 {A : Type'} (P : A -> Prop) (Q : Prop) : (term899 A P Q) = (term900 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3916875 {_100908 : Type'} (P : _100908 -> Prop) (Q : Prop) : (term899 _100908 P Q) = (term900 _100908 P Q).
Proof. exact (@lem3916874 _100908 P Q). Qed.
Lemma lem3916876 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term952 _100908 a b) = (term953 _100908 a b).
Proof. exact (@lem3916875 _100908 (term948 _100908 a b) (term790 _100908 a b)). Qed.
Lemma lem3916877 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term954 _100908 a b x) = (term946 _100908 x a b).
Proof. exact (eq_refl (term954 _100908 a b x)). Qed.
Lemma lem3916878 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term955 _100908 a b) = (term948 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916877 _100908 x a b)). Qed.
Lemma lem3916879 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916880 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term956 _100908 a b) = (term949 _100908 a b).
Proof. exact (MK_COMB (@lem3916879 _100908) (@lem3916878 _100908 a b)). Qed.
Lemma lem3916881 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916882 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term957 _100908 a b) = (term950 _100908 a b).
Proof. exact (MK_COMB (@lem3916881) (@lem3916880 _100908 a b)). Qed.
Lemma lem3916883 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term790 _100908 a b) = (term790 _100908 a b).
Proof. exact (eq_refl (term790 _100908 a b)). Qed.
Lemma lem3916884 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term952 _100908 a b) = (term951 _100908 a b).
Proof. exact (MK_COMB (@lem3916882 _100908 a b) (@lem3916883 _100908 a b)). Qed.
Lemma lem3916885 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916886 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term958 _100908 a b) = (term959 _100908 a b).
Proof. exact (MK_COMB (@lem3916885) (@lem3916884 _100908 a b)). Qed.
Lemma lem3916887 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term954 _100908 a b x) = (term946 _100908 x a b).
Proof. exact (eq_refl (term954 _100908 a b x)). Qed.
Lemma lem3916888 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3916889 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term960 _100908 a b x) = (term961 _100908 x a b).
Proof. exact (MK_COMB (@lem3916888) (@lem3916887 _100908 x a b)). Qed.
Lemma lem3916890 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term790 _100908 a b) = (term790 _100908 a b).
Proof. exact (eq_refl (term790 _100908 a b)). Qed.
Lemma lem3916891 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term962 _100908 x a b) = (term963 _100908 x a b).
Proof. exact (MK_COMB (@lem3916889 _100908 x a b) (@lem3916890 _100908 a b)). Qed.
Lemma lem3916892 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term964 _100908 a b) = (term965 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916891 _100908 x a b)). Qed.
Lemma lem3916893 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916894 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term953 _100908 a b) = (term966 _100908 a b).
Proof. exact (MK_COMB (@lem3916893 _100908) (@lem3916892 _100908 a b)). Qed.
Lemma lem3916895 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term952 _100908 a b) = (term953 _100908 a b)) = ((term951 _100908 a b) = (term966 _100908 a b)).
Proof. exact (MK_COMB (@lem3916886 _100908 a b) (@lem3916894 _100908 a b)). Qed.
Lemma lem3916896 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term951 _100908 a b) = (term966 _100908 a b).
Proof. exact (EQ_MP (@lem3916895 _100908 a b) (@lem3916876 _100908 a b)). Qed.
Lemma lem3916898 {A : Type'} (P : Prop) (Q : A -> Prop) : (term829 A P Q) = (term830 A P Q).
Proof. exact (EQ_MP (@lem18929 A P Q) (@lem18928 A P Q)). Qed.
Lemma lem3916899 {_100908 : Type'} (P : Prop) (Q : _100908 -> Prop) : (term829 _100908 P Q) = (term830 _100908 P Q).
Proof. exact (@lem3916898 _100908 P Q). Qed.
Lemma lem3916900 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term967 _100908 x a b) = (term968 _100908 x a b).
Proof. exact (@lem3916899 _100908 (term946 _100908 x a b) (term789 _100908 a b)). Qed.
Lemma lem3916901 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term969 _100908 a b x) = (term779 _100908 a b x).
Proof. exact (eq_refl (term969 _100908 a b x)). Qed.
Lemma lem3916902 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term970 _100908 a b) = (term789 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916901 _100908 a b x)). Qed.
Lemma lem3916903 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916904 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term971 _100908 a b) = (term790 _100908 a b).
Proof. exact (MK_COMB (@lem3916903 _100908) (@lem3916902 _100908 a b)). Qed.
Lemma lem3916905 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term961 _100908 x a b) = (term961 _100908 x a b).
Proof. exact (eq_refl (term961 _100908 x a b)). Qed.
Lemma lem3916906 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term967 _100908 x a b) = (term963 _100908 x a b).
Proof. exact (MK_COMB (@lem3916905 _100908 x a b) (@lem3916904 _100908 a b)). Qed.
Lemma lem3916907 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916908 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term972 _100908 x a b) = (term973 _100908 x a b).
Proof. exact (MK_COMB (@lem3916907) (@lem3916906 _100908 x a b)). Qed.
Lemma lem3916909 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) : (term969 _100908 a b x') = (term779 _100908 a b x').
Proof. exact (eq_refl (term969 _100908 a b x')). Qed.
Lemma lem3916910 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term961 _100908 x a b) = (term961 _100908 x a b).
Proof. exact (eq_refl (term961 _100908 x a b)). Qed.
Lemma lem3916911 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) : (term974 _100908 x a b x') = (term975 _100908 x a b x').
Proof. exact (MK_COMB (@lem3916910 _100908 x a b) (@lem3916909 _100908 a b x')). Qed.
Lemma lem3916912 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term976 _100908 x a b) = (term977 _100908 x a b).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916911 _100908 x a b x')). Qed.
Lemma lem3916913 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916914 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term968 _100908 x a b) = (term978 _100908 x a b).
Proof. exact (MK_COMB (@lem3916913 _100908) (@lem3916912 _100908 x a b)). Qed.
Lemma lem3916915 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term967 _100908 x a b) = (term968 _100908 x a b)) = ((term963 _100908 x a b) = (term978 _100908 x a b)).
Proof. exact (MK_COMB (@lem3916908 _100908 x a b) (@lem3916914 _100908 x a b)). Qed.
Lemma lem3916916 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term963 _100908 x a b) = (term978 _100908 x a b).
Proof. exact (EQ_MP (@lem3916915 _100908 x a b) (@lem3916900 _100908 x a b)). Qed.
Lemma lem3916917 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term965 _100908 a b) = (term979 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916916 _100908 x a b)). Qed.
Lemma lem3916918 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916919 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term966 _100908 a b) = (term980 _100908 a b).
Proof. exact (MK_COMB (@lem3916918 _100908) (@lem3916917 _100908 a b)). Qed.
Lemma lem3916920 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term951 _100908 a b) = (term980 _100908 a b).
Proof. exact (TRANS (@lem3916896 _100908 a b) (@lem3916919 _100908 a b)). Qed.
Lemma lem3916921 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term827 _100908 a b) = (term980 _100908 a b).
Proof. exact (TRANS (@lem3916872 _100908 a b) (@lem3916920 _100908 a b)). Qed.
Lemma lem3916922 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term828 _100908 a b) = (term981 _100908 a b).
Proof. exact (MK_COMB (@lem3916844 _100908 a b) (@lem3916921 _100908 a b)). Qed.
Lemma lem3916924 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term982 A P Q) = (term983 A P Q).
Proof. exact (EQ_MP (@lem18917 A P Q) (@lem18916 A P Q)). Qed.
Lemma lem3916925 {_100908 : Type'} (P : _100908 -> Prop) (Q : _100908 -> Prop) : (term982 _100908 P Q) = (term983 _100908 P Q).
Proof. exact (@lem3916924 _100908 P Q). Qed.
Lemma lem3916926 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term984 _100908 a b) = (term985 _100908 a b).
Proof. exact (@lem3916925 _100908 (term930 _100908 a b) (term979 _100908 a b)). Qed.
Lemma lem3916927 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term986 _100908 a b x) = (term929 _100908 x a b).
Proof. exact (eq_refl (term986 _100908 a b x)). Qed.
Lemma lem3916928 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term987 _100908 a b) = (term930 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916927 _100908 x a b)). Qed.
Lemma lem3916929 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916930 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term988 _100908 a b) = (term931 _100908 a b).
Proof. exact (MK_COMB (@lem3916929 _100908) (@lem3916928 _100908 a b)). Qed.
Lemma lem3916931 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916932 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term989 _100908 a b) = (term932 _100908 a b).
Proof. exact (MK_COMB (@lem3916931) (@lem3916930 _100908 a b)). Qed.
Lemma lem3916933 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term990 _100908 a b x) = (term978 _100908 x a b).
Proof. exact (eq_refl (term990 _100908 a b x)). Qed.
Lemma lem3916934 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term991 _100908 a b) = (term979 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916933 _100908 x a b)). Qed.
Lemma lem3916935 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916936 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term992 _100908 a b) = (term980 _100908 a b).
Proof. exact (MK_COMB (@lem3916935 _100908) (@lem3916934 _100908 a b)). Qed.
Lemma lem3916937 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term984 _100908 a b) = (term981 _100908 a b).
Proof. exact (MK_COMB (@lem3916932 _100908 a b) (@lem3916936 _100908 a b)). Qed.
Lemma lem3916938 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916939 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term993 _100908 a b) = (term994 _100908 a b).
Proof. exact (MK_COMB (@lem3916938) (@lem3916937 _100908 a b)). Qed.
Lemma lem3916940 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term986 _100908 a b x) = (term929 _100908 x a b).
Proof. exact (eq_refl (term986 _100908 a b x)). Qed.
Lemma lem3916941 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916942 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term995 _100908 a b x) = (term996 _100908 x a b).
Proof. exact (MK_COMB (@lem3916941) (@lem3916940 _100908 x a b)). Qed.
Lemma lem3916943 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term990 _100908 a b x) = (term978 _100908 x a b).
Proof. exact (eq_refl (term990 _100908 a b x)). Qed.
Lemma lem3916944 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term997 _100908 a b x) = (term998 _100908 x a b).
Proof. exact (MK_COMB (@lem3916942 _100908 x a b) (@lem3916943 _100908 x a b)). Qed.
Lemma lem3916945 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term999 _100908 a b) = (term1000 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916944 _100908 x a b)). Qed.
Lemma lem3916946 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916947 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term985 _100908 a b) = (term1001 _100908 a b).
Proof. exact (MK_COMB (@lem3916946 _100908) (@lem3916945 _100908 a b)). Qed.
Lemma lem3916948 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term984 _100908 a b) = (term985 _100908 a b)) = ((term981 _100908 a b) = (term1001 _100908 a b)).
Proof. exact (MK_COMB (@lem3916939 _100908 a b) (@lem3916947 _100908 a b)). Qed.
Lemma lem3916949 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term981 _100908 a b) = (term1001 _100908 a b).
Proof. exact (EQ_MP (@lem3916948 _100908 a b) (@lem3916926 _100908 a b)). Qed.
Lemma lem3916953 {A : Type'} (P : A -> Prop) (Q : Prop) : (term933 A P Q) = (term934 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3916954 {_100908 : Type'} (P : type488 _100908) (Q : Prop) : (term1002 _100908 P Q) = (term1003 _100908 P Q).
Proof. exact (@lem3916953 (_100908 -> _100908) P Q). Qed.
Lemma lem3916955 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1004 _100908 x a b) = (term1005 _100908 x a b).
Proof. exact (@lem3916954 _100908 (term928 _100908 x a b) (term978 _100908 x a b)). Qed.
Lemma lem3916956 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term1006 _100908 x a b x') = (term926 _100908 x a b x').
Proof. exact (eq_refl (term1006 _100908 x a b x')). Qed.
Lemma lem3916957 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1007 _100908 x a b) = (term928 _100908 x a b).
Proof. exact (fun_ext (fun x' : _100908 -> _100908 => @lem3916956 _100908 x a b x')). Qed.
Lemma lem3916958 {_100908 : Type'} : (@ex (_100908 -> _100908)) = (@ex (_100908 -> _100908)).
Proof. exact (eq_refl (@ex (_100908 -> _100908))). Qed.
Lemma lem3916959 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1008 _100908 x a b) = (term929 _100908 x a b).
Proof. exact (MK_COMB (@lem3916958 _100908) (@lem3916957 _100908 x a b)). Qed.
Lemma lem3916960 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916961 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1009 _100908 x a b) = (term996 _100908 x a b).
Proof. exact (MK_COMB (@lem3916960) (@lem3916959 _100908 x a b)). Qed.
Lemma lem3916962 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term978 _100908 x a b) = (term978 _100908 x a b).
Proof. exact (eq_refl (term978 _100908 x a b)). Qed.
Lemma lem3916963 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1004 _100908 x a b) = (term998 _100908 x a b).
Proof. exact (MK_COMB (@lem3916961 _100908 x a b) (@lem3916962 _100908 x a b)). Qed.
Lemma lem3916964 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916965 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1010 _100908 x a b) = (term1011 _100908 x a b).
Proof. exact (MK_COMB (@lem3916964) (@lem3916963 _100908 x a b)). Qed.
Lemma lem3916966 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term1006 _100908 x a b x') = (term926 _100908 x a b x').
Proof. exact (eq_refl (term1006 _100908 x a b x')). Qed.
Lemma lem3916967 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3916968 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term1012 _100908 x a b x') = (term1013 _100908 x a b x').
Proof. exact (MK_COMB (@lem3916967) (@lem3916966 _100908 x a b x')). Qed.
Lemma lem3916969 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term978 _100908 x a b) = (term978 _100908 x a b).
Proof. exact (eq_refl (term978 _100908 x a b)). Qed.
Lemma lem3916970 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1014 _100908 x' x a b) = (term1015 _100908 x' x a b).
Proof. exact (MK_COMB (@lem3916968 _100908 x a b x') (@lem3916969 _100908 x a b)). Qed.
Lemma lem3916971 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1016 _100908 x a b) = (term1017 _100908 x a b).
Proof. exact (fun_ext (fun x' : _100908 -> _100908 => @lem3916970 _100908 x' x a b)). Qed.
Lemma lem3916972 {_100908 : Type'} : (@ex (_100908 -> _100908)) = (@ex (_100908 -> _100908)).
Proof. exact (eq_refl (@ex (_100908 -> _100908))). Qed.
Lemma lem3916973 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1005 _100908 x a b) = (term1018 _100908 x a b).
Proof. exact (MK_COMB (@lem3916972 _100908) (@lem3916971 _100908 x a b)). Qed.
Lemma lem3916974 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term1004 _100908 x a b) = (term1005 _100908 x a b)) = ((term998 _100908 x a b) = (term1018 _100908 x a b)).
Proof. exact (MK_COMB (@lem3916965 _100908 x a b) (@lem3916973 _100908 x a b)). Qed.
Lemma lem3916975 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term998 _100908 x a b) = (term1018 _100908 x a b).
Proof. exact (EQ_MP (@lem3916974 _100908 x a b) (@lem3916955 _100908 x a b)). Qed.
Lemma lem3916977 {A : Type'} (P : Prop) (Q : A -> Prop) : (term844 A P Q) = (term845 A P Q).
Proof. exact (EQ_MP (@lem18911 A P Q) (@lem18910 A P Q)). Qed.
Lemma lem3916978 {_100908 : Type'} (P : Prop) (Q : _100908 -> Prop) : (term844 _100908 P Q) = (term845 _100908 P Q).
Proof. exact (@lem3916977 _100908 P Q). Qed.
Lemma lem3916979 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1019 _100908 x' x a b) = (term1020 _100908 x' x a b).
Proof. exact (@lem3916978 _100908 (term926 _100908 x a b x') (term977 _100908 x a b)). Qed.
Lemma lem3916980 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) : (term1021 _100908 x a b x') = (term975 _100908 x a b x').
Proof. exact (eq_refl (term1021 _100908 x a b x')). Qed.
Lemma lem3916981 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1022 _100908 x a b) = (term977 _100908 x a b).
Proof. exact (fun_ext (fun x' : _100908 => @lem3916980 _100908 x a b x')). Qed.
Lemma lem3916982 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916983 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1023 _100908 x a b) = (term978 _100908 x a b).
Proof. exact (MK_COMB (@lem3916982 _100908) (@lem3916981 _100908 x a b)). Qed.
Lemma lem3916984 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term1013 _100908 x a b x') = (term1013 _100908 x a b x').
Proof. exact (eq_refl (term1013 _100908 x a b x')). Qed.
Lemma lem3916985 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1019 _100908 x' x a b) = (term1015 _100908 x' x a b).
Proof. exact (MK_COMB (@lem3916984 _100908 x a b x') (@lem3916983 _100908 x a b)). Qed.
Lemma lem3916986 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3916987 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1024 _100908 x' x a b) = (term1025 _100908 x' x a b).
Proof. exact (MK_COMB (@lem3916986) (@lem3916985 _100908 x' x a b)). Qed.
Lemma lem3916988 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908) : (term1021 _100908 x a b x') = (term975 _100908 x a b x').
Proof. exact (eq_refl (term1021 _100908 x a b x')). Qed.
Lemma lem3916989 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term1013 _100908 x a b x') = (term1013 _100908 x a b x').
Proof. exact (eq_refl (term1013 _100908 x a b x')). Qed.
Lemma lem3916990 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) : (term1026 _100908 x' x a b x'') = (term1027 _100908 x' x a b x'').
Proof. exact (MK_COMB (@lem3916989 _100908 x a b x') (@lem3916988 _100908 x a b x'')). Qed.
Lemma lem3916991 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1028 _100908 x' x a b) = (term1029 _100908 x' x a b).
Proof. exact (fun_ext (fun x'' : _100908 => @lem3916990 _100908 x' x a b x'')). Qed.
Lemma lem3916992 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3916993 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1020 _100908 x' x a b) = (term1030 _100908 x' x a b).
Proof. exact (MK_COMB (@lem3916992 _100908) (@lem3916991 _100908 x' x a b)). Qed.
Lemma lem3916994 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : ((term1019 _100908 x' x a b) = (term1020 _100908 x' x a b)) = ((term1015 _100908 x' x a b) = (term1030 _100908 x' x a b)).
Proof. exact (MK_COMB (@lem3916987 _100908 x' x a b) (@lem3916993 _100908 x' x a b)). Qed.
Lemma lem3916995 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1015 _100908 x' x a b) = (term1030 _100908 x' x a b).
Proof. exact (EQ_MP (@lem3916994 _100908 x' x a b) (@lem3916979 _100908 x' x a b)). Qed.
Lemma lem3916996 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1017 _100908 x a b) = (term1031 _100908 x a b).
Proof. exact (fun_ext (fun x' : _100908 -> _100908 => @lem3916995 _100908 x' x a b)). Qed.
Lemma lem3916997 {_100908 : Type'} : (@ex (_100908 -> _100908)) = (@ex (_100908 -> _100908)).
Proof. exact (eq_refl (@ex (_100908 -> _100908))). Qed.
Lemma lem3916998 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1018 _100908 x a b) = (term1032 _100908 x a b).
Proof. exact (MK_COMB (@lem3916997 _100908) (@lem3916996 _100908 x a b)). Qed.
Lemma lem3916999 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term998 _100908 x a b) = (term1032 _100908 x a b).
Proof. exact (TRANS (@lem3916975 _100908 x a b) (@lem3916998 _100908 x a b)). Qed.
Lemma lem3917000 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1000 _100908 a b) = (term1033 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3916999 _100908 x a b)). Qed.
Lemma lem3917001 {_100908 : Type'} : (@ex _100908) = (@ex _100908).
Proof. exact (eq_refl (@ex _100908)). Qed.
Lemma lem3917002 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1001 _100908 a b) = (term1034 _100908 a b).
Proof. exact (MK_COMB (@lem3917001 _100908) (@lem3917000 _100908 a b)). Qed.
Lemma lem3917003 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term981 _100908 a b) = (term1034 _100908 a b).
Proof. exact (TRANS (@lem3916949 _100908 a b) (@lem3917002 _100908 a b)). Qed.
Lemma lem3917004 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term828 _100908 a b) = (term1034 _100908 a b).
Proof. exact (TRANS (@lem3916922 _100908 a b) (@lem3917003 _100908 a b)). Qed.
Lemma lem3917005 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term802 _100908 a b) = (term1034 _100908 a b).
Proof. exact (TRANS (@lem3916693 _100908 a b) (@lem3917004 _100908 a b)). Qed.
Lemma lem3917006 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term705 _100908 a b) = (term1034 _100908 a b).
Proof. exact (TRANS (@lem3916338 _100908 a b) (@lem3917005 _100908 a b)). Qed.
Lemma lem3917007 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : term1034 _100908 a b.
Proof. exact (EQ_MP (@lem3917006 _100908 a b) (@lem3916177 _100908 a b h1)). Qed.
Lemma lem3917008 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term1032 _100908 x a b) : term1032 _100908 x a b.
Proof. exact (h1). Qed.
Lemma lem3917009 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term1030 _100908 x' x a b) : term1030 _100908 x' x a b.
Proof. exact (h1). Qed.
Lemma lem3917010 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term1027 _100908 x' x a b x'') : term1027 _100908 x' x a b x''.
Proof. exact (h1). Qed.
Lemma lem3917031 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x''' : _100908) (x'' : _100908) : (term760 _100908 a b x''' x'') = (term760 _100908 a b x''' x'').
Proof. exact (eq_refl (term760 _100908 a b x''' x'')). Qed.
Lemma lem3917032 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) : (term768 _100908 a b x'') = (term768 _100908 a b x'').
Proof. exact (fun_ext (fun x''' : _100908 => @lem3917031 _100908 a b x''' x'')). Qed.
Lemma lem3917033 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917034 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) : (term769 _100908 a b x'') = (term769 _100908 a b x'').
Proof. exact (MK_COMB (@lem3917033 _100908) (@lem3917032 _100908 a b x'')). Qed.
Lemma lem3917041 {_100908 : Type'} (a : _100908 -> Prop) (x'' : _100908) : (term689 _100908 a x'') = (term689 _100908 a x'').
Proof. exact (eq_refl (term689 _100908 a x'')). Qed.
Lemma lem3917042 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) : (term775 _100908 a b x'') = (term775 _100908 a b x'').
Proof. exact (MK_COMB (@lem3917041 _100908 a x'') (@lem3917034 _100908 a b x'')). Qed.
Lemma lem3917047 {_100908 : Type'} (b : _100908 -> Prop) (x'' : _100908) : (term686 _100908 b x'') = (term686 _100908 b x'').
Proof. exact (eq_refl (term686 _100908 b x'')). Qed.
Lemma lem3917048 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) : (term779 _100908 a b x'') = (term779 _100908 a b x'').
Proof. exact (MK_COMB (@lem3917047 _100908 b x'') (@lem3917042 _100908 a b x'')). Qed.
Lemma lem3917059 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term720 _100908 a b x) = (term720 _100908 a b x).
Proof. exact (eq_refl (term720 _100908 a b x)). Qed.
Lemma lem3917060 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term730 _100908 a b) = (term730 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3917059 _100908 a b x)). Qed.
Lemma lem3917061 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917062 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term731 _100908 a b) = (term731 _100908 a b).
Proof. exact (MK_COMB (@lem3917061 _100908) (@lem3917060 _100908 a b)). Qed.
Lemma lem3917073 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term809 _100908 a b x) = (term809 _100908 a b x).
Proof. exact (eq_refl (term809 _100908 a b x)). Qed.
Lemma lem3917074 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term807 _100908 a b) = (term807 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3917073 _100908 a b x)). Qed.
Lemma lem3917075 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917076 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term819 _100908 a b) = (term819 _100908 a b).
Proof. exact (MK_COMB (@lem3917075 _100908) (@lem3917074 _100908 a b)). Qed.
Lemma lem3917077 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3917078 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term821 _100908 a b) = (term821 _100908 a b).
Proof. exact (MK_COMB (@lem3917077) (@lem3917076 _100908 a b)). Qed.
Lemma lem3917079 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term824 _100908 a b) = (term824 _100908 a b).
Proof. exact (MK_COMB (@lem3917078 _100908 a b) (@lem3917062 _100908 a b)). Qed.
Lemma lem3917092 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term944 _100908 a b x) = (term944 _100908 a b x).
Proof. exact (eq_refl (term944 _100908 a b x)). Qed.
Lemma lem3917093 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term946 _100908 x a b) = (term946 _100908 x a b).
Proof. exact (MK_COMB (@lem3917092 _100908 a b x) (@lem3917079 _100908 a b)). Qed.
Lemma lem3917094 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3917095 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) : (term961 _100908 x a b) = (term961 _100908 x a b).
Proof. exact (MK_COMB (@lem3917094) (@lem3917093 _100908 x a b)). Qed.
Lemma lem3917096 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) : (term975 _100908 x a b x'') = (term975 _100908 x a b x'').
Proof. exact (MK_COMB (@lem3917095 _100908 x a b) (@lem3917048 _100908 a b x'')). Qed.
Lemma lem3917135 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term890 _100908 a b x' x) = (term890 _100908 a b x' x).
Proof. exact (eq_refl (term890 _100908 a b x' x)). Qed.
Lemma lem3917136 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term892 _100908 a b x') = (term892 _100908 a b x').
Proof. exact (fun_ext (fun x : _100908 => @lem3917135 _100908 a b x' x)). Qed.
Lemma lem3917137 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917138 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term894 _100908 a b x') = (term894 _100908 a b x').
Proof. exact (MK_COMB (@lem3917137 _100908) (@lem3917136 _100908 a b x')). Qed.
Lemma lem3917163 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term733 _100908 a b x) = (term733 _100908 a b x).
Proof. exact (eq_refl (term733 _100908 a b x)). Qed.
Lemma lem3917174 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term720 _100908 a b x) = (term720 _100908 a b x).
Proof. exact (eq_refl (term720 _100908 a b x)). Qed.
Lemma lem3917175 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term730 _100908 a b) = (term730 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3917174 _100908 a b x)). Qed.
Lemma lem3917176 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917177 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term731 _100908 a b) = (term731 _100908 a b).
Proof. exact (MK_COMB (@lem3917176 _100908) (@lem3917175 _100908 a b)). Qed.
Lemma lem3917178 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3917179 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term749 _100908 a b) = (term749 _100908 a b).
Proof. exact (MK_COMB (@lem3917178) (@lem3917177 _100908 a b)). Qed.
Lemma lem3917180 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term839 _100908 a b x) = (term839 _100908 a b x).
Proof. exact (MK_COMB (@lem3917179 _100908 a b) (@lem3917163 _100908 a b x)). Qed.
Lemma lem3917181 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3917182 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term910 _100908 a b x) = (term910 _100908 a b x).
Proof. exact (MK_COMB (@lem3917181) (@lem3917180 _100908 a b x)). Qed.
Lemma lem3917183 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term926 _100908 x a b x') = (term926 _100908 x a b x').
Proof. exact (MK_COMB (@lem3917182 _100908 a b x) (@lem3917138 _100908 a b x')). Qed.
Lemma lem3917184 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3917185 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term1013 _100908 x a b x') = (term1013 _100908 x a b x').
Proof. exact (MK_COMB (@lem3917184) (@lem3917183 _100908 x a b x')). Qed.
Lemma lem3917186 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) : (term1027 _100908 x' x a b x'') = (term1027 _100908 x' x a b x'').
Proof. exact (MK_COMB (@lem3917185 _100908 x a b x') (@lem3917096 _100908 x a b x'')). Qed.
Lemma lem3917187 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term1027 _100908 x' x a b x'') : term1027 _100908 x' x a b x''.
Proof. exact (EQ_MP (@lem3917186 _100908 x' x a b x'') (@lem3917010 _100908 x' x a b x'' h1)). Qed.
Lemma lem3917188 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term926 _100908 x a b x'.
Proof. exact (h1). Qed.
Lemma lem3917189 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term975 _100908 x a b x''.
Proof. exact (h1). Qed.
Lemma lem3917190 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term894 _100908 a b x'.
Proof. exact (proj2 (@lem3917188 _100908 x a b x' h1)). Qed.
Lemma lem3917191 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term839 _100908 a b x.
Proof. exact (proj1 (@lem3917188 _100908 x a b x' h1)). Qed.
Lemma lem3917192 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term733 _100908 a b x.
Proof. exact (proj2 (@lem3917191 _100908 x a b x' h1)). Qed.
Lemma lem3917193 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term731 _100908 a b.
Proof. exact (proj1 (@lem3917191 _100908 x a b x' h1)). Qed.
Lemma lem3917194 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1035 _100908 a b x.
Proof. exact (proj2 (@lem3917192 _100908 x a b x' h1)). Qed.
Lemma lem3917195 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1036 _100908 a b x.
Proof. exact (proj1 (@lem3917192 _100908 x a b x' h1)). Qed.
Lemma lem3917202 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term779 _100908 a b x''.
Proof. exact (proj2 (@lem3917189 _100908 x a b x'' h1)). Qed.
Lemma lem3917203 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term946 _100908 x a b.
Proof. exact (proj1 (@lem3917189 _100908 x a b x'' h1)). Qed.
Lemma lem3917204 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term775 _100908 a b x''.
Proof. exact (proj2 (@lem3917202 _100908 x a b x'' h1)). Qed.
Lemma lem3917206 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term769 _100908 a b x''.
Proof. exact (proj2 (@lem3917204 _100908 x a b x'' h1)). Qed.
Lemma lem3917208 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (h1 : term719 _100908 a b x) : term719 _100908 a b x.
Proof. exact (h1). Qed.
Lemma lem3917209 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term824 _100908 a b.
Proof. exact (h1). Qed.
Lemma lem3917213 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term819 _100908 a b.
Proof. exact (proj1 (@lem3917209 _100908 a b h1)). Qed.
Lemma lem3917271 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (h1). Qed.
Lemma lem3917275 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3917299 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term1037 _100908 a b x' x) = (term1038 _100908 a b x' x).
Proof. exact (@lem19490 (term1039 _100908 a x' x) (a x) (term1040 _100908 b x' x)). Qed.
Lemma lem3917302 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term753 _100908 b x) = (term753 _100908 b x).
Proof. exact (eq_refl (term753 _100908 b x)). Qed.
Lemma lem3917303 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term890 _100908 a b x' x) = (term1041 _100908 a b x' x).
Proof. exact (MK_COMB (@lem3917302 _100908 b x) (@lem3917299 _100908 a b x' x)). Qed.
Lemma lem3917310 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term1041 _100908 a b x' x) = (term1042 _100908 a b x' x).
Proof. exact (@lem19490 (term1043 _100908 a x' x) (term688 _100908 b x) (term1044 _100908 a b x' x)). Qed.
Lemma lem3917311 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term890 _100908 a b x' x) = (term1042 _100908 a b x' x).
Proof. exact (TRANS (@lem3917303 _100908 a b x' x) (@lem3917310 _100908 a b x' x)). Qed.
Lemma lem3917312 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term892 _100908 a b x') = (term1045 _100908 a b x').
Proof. exact (fun_ext (fun x : _100908 => @lem3917311 _100908 a b x' x)). Qed.
Lemma lem3917313 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917315 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) : (term894 _100908 a b x') = (term1046 _100908 a b x').
Proof. exact (MK_COMB (@lem3917313 _100908) (@lem3917312 _100908 a b x')). Qed.
Lemma lem3917316 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1046 _100908 a b x'.
Proof. exact (EQ_MP (@lem3917315 _100908 a b x') (@lem3917190 _100908 x a b x' h1)). Qed.
Lemma lem3917324 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term720 _100908 a b x) = (term720 _100908 a b x).
Proof. exact (eq_refl (term720 _100908 a b x)). Qed.
Lemma lem3917325 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term730 _100908 a b) = (term730 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3917324 _100908 a b x)). Qed.
Lemma lem3917326 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917328 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term731 _100908 a b) = (term731 _100908 a b).
Proof. exact (MK_COMB (@lem3917326 _100908) (@lem3917325 _100908 a b)). Qed.
Lemma lem3917329 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term731 _100908 a b.
Proof. exact (EQ_MP (@lem3917328 _100908 a b) (@lem3917193 _100908 x a b x' h1)). Qed.
Lemma lem3917333 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (h1). Qed.
Lemma lem3917337 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3917386 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term720 _100908 a b x) = (term720 _100908 a b x).
Proof. exact (eq_refl (term720 _100908 a b x)). Qed.
Lemma lem3917387 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term730 _100908 a b) = (term730 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3917386 _100908 a b x)). Qed.
Lemma lem3917388 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917390 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term731 _100908 a b) = (term731 _100908 a b).
Proof. exact (MK_COMB (@lem3917388 _100908) (@lem3917387 _100908 a b)). Qed.
Lemma lem3917391 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term731 _100908 a b.
Proof. exact (EQ_MP (@lem3917390 _100908 a b) (@lem3917193 _100908 x a b x' h1)). Qed.
Lemma lem3917395 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) : term688 _100908 b x.
Proof. exact (h1). Qed.
Lemma lem3917399 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3917457 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) : term688 _100908 b x.
Proof. exact (h1). Qed.
Lemma lem3917461 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3917487 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x''' : _100908) (x'' : _100908) : (term760 _100908 a b x''' x'') = (term1047 _100908 b a x''' x'').
Proof. exact (@lem19490 (b x''') (term688 _100908 a x''') (term692 _100908 x''' x'')). Qed.
Lemma lem3917488 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x'' : _100908) : (term768 _100908 a b x'') = (term1048 _100908 b a x'').
Proof. exact (fun_ext (fun x''' : _100908 => @lem3917487 _100908 b a x''' x'')). Qed.
Lemma lem3917489 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917491 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x'' : _100908) : (term769 _100908 a b x'') = (term1049 _100908 b a x'').
Proof. exact (MK_COMB (@lem3917489 _100908) (@lem3917488 _100908 b a x'')). Qed.
Lemma lem3917492 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term1049 _100908 b a x''.
Proof. exact (EQ_MP (@lem3917491 _100908 b a x'') (@lem3917206 _100908 x a b x'' h1)). Qed.
Lemma lem3917539 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) : (term809 _100908 a b x) = (term809 _100908 a b x).
Proof. exact (eq_refl (term809 _100908 a b x)). Qed.
Lemma lem3917540 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term807 _100908 a b) = (term807 _100908 a b).
Proof. exact (fun_ext (fun x : _100908 => @lem3917539 _100908 a b x)). Qed.
Lemma lem3917541 {_100908 : Type'} : (@all _100908) = (@all _100908).
Proof. exact (eq_refl (@all _100908)). Qed.
Lemma lem3917543 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term819 _100908 a b) = (term819 _100908 a b).
Proof. exact (MK_COMB (@lem3917541 _100908) (@lem3917540 _100908 a b)). Qed.
Lemma lem3917544 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term819 _100908 a b.
Proof. exact (EQ_MP (@lem3917543 _100908 a b) (@lem3917213 _100908 a b h1)). Qed.
Lemma lem3917564 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1050 _100908 a b x' _45444.
Proof. exact (@lem3917316 _100908 x a b x' h1 _45444). Qed.
Lemma lem3917565 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1050 _100908 a b x' _45444) = (term1042 _100908 a b x' _45444).
Proof. exact (eq_refl (term1050 _100908 a b x' _45444)). Qed.
Lemma lem3917566 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1042 _100908 a b x' _45444.
Proof. exact (EQ_MP (@lem3917565 _100908 a b x' _45444) (@lem3917564 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3917567 {_100908 : Type'} (_45445 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term812 _100908 a b _45445.
Proof. exact (@lem3917329 _100908 x a b x' h1 _45445). Qed.
Lemma lem3917568 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45445 : _100908) : (term812 _100908 a b _45445) = (term720 _100908 a b _45445).
Proof. exact (eq_refl (term812 _100908 a b _45445)). Qed.
Lemma lem3917573 {_100908 : Type'} (_45447 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term812 _100908 a b _45447.
Proof. exact (@lem3917391 _100908 x a b x' h1 _45447). Qed.
Lemma lem3917574 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45447 : _100908) : (term812 _100908 a b _45447) = (term720 _100908 a b _45447).
Proof. exact (eq_refl (term812 _100908 a b _45447)). Qed.
Lemma lem3917582 {_100908 : Type'} (_45450 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term1051 _100908 b a x'' _45450.
Proof. exact (@lem3917492 _100908 x a b x'' h1 _45450). Qed.
Lemma lem3917583 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) (x'' : _100908) : (term1051 _100908 b a x'' _45450) = (term1047 _100908 b a _45450 x'').
Proof. exact (eq_refl (term1051 _100908 b a x'' _45450)). Qed.
Lemma lem3917584 {_100908 : Type'} (_45450 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term1047 _100908 b a _45450 x''.
Proof. exact (EQ_MP (@lem3917583 _100908 b a _45450 x'') (@lem3917582 _100908 _45450 x a b x'' h1)). Qed.
Lemma lem3917588 {_100908 : Type'} (_45452 : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term808 _100908 a b _45452.
Proof. exact (@lem3917544 _100908 a b h1 _45452). Qed.
Lemma lem3917589 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45452 : _100908) : (term808 _100908 a b _45452) = (term809 _100908 a b _45452).
Proof. exact (eq_refl (term808 _100908 a b _45452)). Qed.
Lemma lem3917613 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (h1). Qed.
Lemma lem3917615 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3917645 {_100908 : Type'} (_45445 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term720 _100908 a b _45445.
Proof. exact (EQ_MP (@lem3917568 _100908 a b _45445) (@lem3917567 _100908 _45445 x a b x' h1)). Qed.
Lemma lem3917647 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (h1). Qed.
Lemma lem3917649 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3917659 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1052 _100908 b a x' _45444.
Proof. exact (proj1 (@lem3917566 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3917673 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1053 _100908 a b x' _45444.
Proof. exact (proj2 (@lem3917566 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3917679 {_100908 : Type'} (_45447 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term720 _100908 a b _45447.
Proof. exact (EQ_MP (@lem3917574 _100908 a b _45447) (@lem3917573 _100908 _45447 x a b x' h1)). Qed.
Lemma lem3917681 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) : term688 _100908 b x.
Proof. exact (h1). Qed.
Lemma lem3917683 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3917715 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) : term688 _100908 b x.
Proof. exact (h1). Qed.
Lemma lem3917717 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3917749 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (h1 : term719 _100908 a b x) : term688 _100908 b x.
Proof. exact (proj2 (@lem3917208 _100908 a b x h1)). Qed.
Lemma lem3917755 {_100908 : Type'} (_45450 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term720 _100908 a b _45450.
Proof. exact (proj1 (@lem3917584 _100908 _45450 x a b x'' h1)). Qed.
Lemma lem3917765 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term688 _100908 a x''.
Proof. exact (proj1 (@lem3917204 _100908 x a b x'' h1)). Qed.
Lemma lem3917771 {_100908 : Type'} (_45452 : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term809 _100908 a b _45452.
Proof. exact (EQ_MP (@lem3917589 _100908 a b _45452) (@lem3917588 _100908 _45452 a b h1)). Qed.
Lemma lem3917825 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3917826 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : term1054 _100908 a x.
Proof. exact (fun h0 : term688 _100908 a x => @lem3917825 _100908 a x h1). Qed.
Lemma lem3917828 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3917829 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term1054 _100908 a x) = (a x).
Proof. exact (@lem3917828 (a x)). Qed.
Lemma lem3917830 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem3917829 _100908 a x) (@lem3917826 _100908 a x h1)). Qed.
Lemma lem3917833 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3917835 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term688 _100908 a x) = (term1056 _100908 a x).
Proof. exact (@lem3917833 (a x)). Qed.
Lemma lem3917838 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term1056 _100908 a x.
Proof. exact (EQ_MP (@lem3917835 _100908 a x) (@lem3917613 _100908 a x h1)). Qed.
Lemma lem3917841 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (@lem3917838 _100908 a x h1 (@lem3917830 _100908 a x h2)). Qed.
Lemma lem3917842 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : term1057.
Proof. exact (fun h0 : ~ False => @lem3917841 _100908 a x h1 h2). Qed.
Lemma lem3917844 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3917845 : term1057 = False.
Proof. exact (@lem3917844 False). Qed.
Lemma lem3917846 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem3917845) (@lem3917842 _100908 a x h1 h2)). Qed.
Lemma lem3917847 {_100908 : Type'} (a : _100908 -> Prop) : a = a.
Proof. exact (eq_refl a). Qed.
Lemma lem3917848 {_100908 : Type'} (_45460 : _100908) (_45461 : _100908) (h1 : _45460 = _45461) : _45460 = _45461.
Proof. exact (h1). Qed.
Lemma lem3917849 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) (_45461 : _100908) (h1 : _45460 = _45461) : (a _45460) = (a _45461).
Proof. exact (MK_COMB (@lem3917847 _100908 a) (@lem3917848 _100908 _45460 _45461 h1)). Qed.
Lemma lem3917851 (b : Prop) (a : Prop) : term1058 b a.
Proof. exact (EQ_MP (@lem21501 b a) (@lem21598 b a)). Qed.
Lemma lem3917852 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : term1059 _100908 _45461 a _45460.
Proof. exact (@lem3917851 (a _45461) (a _45460)). Qed.
Lemma lem3917853 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) (_45461 : _100908) (h1 : _45460 = _45461) : term1060 _100908 _45461 a _45460.
Proof. exact (@lem3917852 _100908 _45461 a _45460 (@lem3917849 _100908 a _45460 _45461 h1)). Qed.
Lemma lem3917854 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : term1061 _100908 _45461 a _45460.
Proof. exact (fun h0 : _45460 = _45461 => @lem3917853 _100908 a _45460 _45461 h0). Qed.
Lemma lem3917856 (a : Prop) (b : Prop) : (a -> b) = (term1062 a b).
Proof. exact (EQ_MP (@lem21394 a b) (@lem21490 a b)). Qed.
Lemma lem3917857 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : (term1061 _100908 _45461 a _45460) = (term1063 _100908 _45461 a _45460).
Proof. exact (@lem3917856 (_45460 = _45461) (term1060 _100908 _45461 a _45460)). Qed.
Lemma lem3917858 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : term1063 _100908 _45461 a _45460.
Proof. exact (EQ_MP (@lem3917857 _100908 _45461 a _45460) (@lem3917854 _100908 _45461 a _45460)). Qed.
Lemma lem3917882 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3917883 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : term1054 _100908 b x.
Proof. exact (fun h0 : term688 _100908 b x => @lem3917882 _100908 b x h1). Qed.
Lemma lem3917885 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3917886 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term1054 _100908 b x) = (b x).
Proof. exact (@lem3917885 (b x)). Qed.
Lemma lem3917887 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem3917886 _100908 b x) (@lem3917883 _100908 b x h1)). Qed.
Lemma lem3917889 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3917890 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : term1054 _100908 b x.
Proof. exact (fun h0 : term688 _100908 b x => @lem3917889 _100908 b x h1). Qed.
Lemma lem3917892 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3917893 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term1054 _100908 b x) = (b x).
Proof. exact (@lem3917892 (b x)). Qed.
Lemma lem3917894 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem3917893 _100908 b x) (@lem3917890 _100908 b x h1)). Qed.
Lemma lem3917897 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (h1). Qed.
Lemma lem3917898 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term1064 _100908 a x.
Proof. exact (fun h0 : a x => @lem3917897 _100908 a x h1). Qed.
Lemma lem3917900 (p : Prop) : (term1065 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3917901 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term1064 _100908 a x) = (term688 _100908 a x).
Proof. exact (@lem3917900 (a x)). Qed.
Lemma lem3917902 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (EQ_MP (@lem3917901 _100908 a x) (@lem3917898 _100908 a x h1)). Qed.
Lemma lem3917905 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (h1). Qed.
Lemma lem3917906 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term1064 _100908 a x.
Proof. exact (fun h0 : a x => @lem3917905 _100908 a x h1). Qed.
Lemma lem3917908 (p : Prop) : (term1065 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3917909 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term1064 _100908 a x) = (term688 _100908 a x).
Proof. exact (@lem3917908 (a x)). Qed.
Lemma lem3917910 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (EQ_MP (@lem3917909 _100908 a x) (@lem3917906 _100908 a x h1)). Qed.
Lemma lem3917912 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3917913 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : term1054 _100908 b x.
Proof. exact (fun h0 : term688 _100908 b x => @lem3917912 _100908 b x h1). Qed.
Lemma lem3917915 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3917916 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term1054 _100908 b x) = (b x).
Proof. exact (@lem3917915 (b x)). Qed.
Lemma lem3917917 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem3917916 _100908 b x) (@lem3917913 _100908 b x h1)). Qed.
Lemma lem3917920 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (h1). Qed.
Lemma lem3917921 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term1064 _100908 a x.
Proof. exact (fun h0 : a x => @lem3917920 _100908 a x h1). Qed.
Lemma lem3917923 (p : Prop) : (term1065 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3917924 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term1064 _100908 a x) = (term688 _100908 a x).
Proof. exact (@lem3917923 (a x)). Qed.
Lemma lem3917925 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term688 _100908 a x.
Proof. exact (EQ_MP (@lem3917924 _100908 a x) (@lem3917921 _100908 a x h1)). Qed.
Lemma lem3917931 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3917932 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1052 _100908 b a x' _45444) = (term1067 _100908 b a x' _45444).
Proof. exact (@lem3917931 (a _45444) (term688 _100908 b _45444) (term1039 _100908 a x' _45444)). Qed.
Lemma lem3917946 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3917947 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1068 _100908 b a x' _45444) = (term1069 _100908 a x' b _45444).
Proof. exact (@lem3917946 (term1039 _100908 a x' _45444) (term688 _100908 b _45444)). Qed.
Lemma lem3917953 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (term771 _100908 a _45444) = (term771 _100908 a _45444).
Proof. exact (eq_refl (term771 _100908 a _45444)). Qed.
Lemma lem3917954 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1067 _100908 b a x' _45444) = (term1070 _100908 a x' b _45444).
Proof. exact (MK_COMB (@lem3917953 _100908 a _45444) (@lem3917947 _100908 a x' b _45444)). Qed.
Lemma lem3917965 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1052 _100908 b a x' _45444) = (term1070 _100908 a x' b _45444).
Proof. exact (TRANS (@lem3917932 _100908 b a x' _45444) (@lem3917954 _100908 a x' b _45444)). Qed.
Lemma lem3917966 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3917967 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1071 _100908 b a x' _45444) = (term1072 _100908 a x' b _45444).
Proof. exact (MK_COMB (@lem3917966) (@lem3917965 _100908 a x' b _45444)). Qed.
Lemma lem3917981 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3917982 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45444 : _100908) : (term720 _100908 b a _45444) = (term809 _100908 a b _45444).
Proof. exact (@lem3917981 (a _45444) (term688 _100908 b _45444)). Qed.
Lemma lem3917988 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1073 _100908 a x' _45444) = (term1073 _100908 a x' _45444).
Proof. exact (eq_refl (term1073 _100908 a x' _45444)). Qed.
Lemma lem3917989 {_100908 : Type'} (x' : _100908 -> _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (_45444 : _100908) : (term1074 _100908 x' b a _45444) = (term1075 _100908 x' a b _45444).
Proof. exact (MK_COMB (@lem3917988 _100908 a x' _45444) (@lem3917982 _100908 a b _45444)). Qed.
Lemma lem3917993 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3917994 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1075 _100908 x' a b _45444) = (term1070 _100908 a x' b _45444).
Proof. exact (@lem3917993 (a _45444) (term1039 _100908 a x' _45444) (term688 _100908 b _45444)). Qed.
Lemma lem3918010 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1074 _100908 x' b a _45444) = (term1070 _100908 a x' b _45444).
Proof. exact (TRANS (@lem3917989 _100908 x' a b _45444) (@lem3917994 _100908 a x' b _45444)). Qed.
Lemma lem3918011 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : ((term1052 _100908 b a x' _45444) = (term1074 _100908 x' b a _45444)) = ((term1070 _100908 a x' b _45444) = (term1070 _100908 a x' b _45444)).
Proof. exact (MK_COMB (@lem3917967 _100908 a x' b _45444) (@lem3918010 _100908 a x' b _45444)). Qed.
Lemma lem3918013 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3918014 (x : Prop) : (x = x) = True.
Proof. exact (@lem3918013 Prop x). Qed.
Lemma lem3918015 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : ((term1070 _100908 a x' b _45444) = (term1070 _100908 a x' b _45444)) = True.
Proof. exact (@lem3918014 (term1070 _100908 a x' b _45444)). Qed.
Lemma lem3918016 {_100908 : Type'} (x' : _100908 -> _100908) (b : _100908 -> Prop) (a : _100908 -> Prop) (_45444 : _100908) : ((term1052 _100908 b a x' _45444) = (term1074 _100908 x' b a _45444)) = True.
Proof. exact (TRANS (@lem3918011 _100908 a x' b _45444) (@lem3918015 _100908 a x' b _45444)). Qed.
Lemma lem3918017 {_100908 : Type'} (x' : _100908 -> _100908) (b : _100908 -> Prop) (a : _100908 -> Prop) (_45444 : _100908) : True = ((term1052 _100908 b a x' _45444) = (term1074 _100908 x' b a _45444)).
Proof. exact (SYM (@lem3918016 _100908 x' b a _45444)). Qed.
Lemma lem3918018 {_100908 : Type'} (x' : _100908 -> _100908) (b : _100908 -> Prop) (a : _100908 -> Prop) (_45444 : _100908) : (term1052 _100908 b a x' _45444) = (term1074 _100908 x' b a _45444).
Proof. exact (EQ_MP (@lem3918017 _100908 x' b a _45444) (@lem0)). Qed.
Lemma lem3918019 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1074 _100908 x' b a _45444.
Proof. exact (EQ_MP (@lem3918018 _100908 x' b a _45444) (@lem3917659 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3918021 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918022 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1074 _100908 x' b a _45444) = (term1077 _100908 b a x' _45444).
Proof. exact (@lem3918021 (term720 _100908 b a _45444) (term1039 _100908 a x' _45444)). Qed.
Lemma lem3918024 (a : Prop) (b : Prop) : (term1078 a b) = (term1079 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3918025 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45444 : _100908) : (term1080 _100908 b a _45444) = (term1081 _100908 b a _45444).
Proof. exact (@lem3918024 (term688 _100908 b _45444) (a _45444)). Qed.
Lemma lem3918027 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3918028 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term751 _100908 b _45444) = (b _45444).
Proof. exact (@lem3918027 (b _45444)). Qed.
Lemma lem3918029 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3918030 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term1082 _100908 b _45444) = (term686 _100908 b _45444).
Proof. exact (MK_COMB (@lem3918029) (@lem3918028 _100908 b _45444)). Qed.
Lemma lem3918031 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (term688 _100908 a _45444) = (term688 _100908 a _45444).
Proof. exact (eq_refl (term688 _100908 a _45444)). Qed.
Lemma lem3918032 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45444 : _100908) : (term1081 _100908 b a _45444) = (term719 _100908 b a _45444).
Proof. exact (MK_COMB (@lem3918030 _100908 b _45444) (@lem3918031 _100908 a _45444)). Qed.
Lemma lem3918033 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45444 : _100908) : (term1080 _100908 b a _45444) = (term719 _100908 b a _45444).
Proof. exact (TRANS (@lem3918025 _100908 b a _45444) (@lem3918032 _100908 b a _45444)). Qed.
Lemma lem3918034 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918035 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45444 : _100908) : (term1083 _100908 b a _45444) = (term1084 _100908 b a _45444).
Proof. exact (MK_COMB (@lem3918034) (@lem3918033 _100908 b a _45444)). Qed.
Lemma lem3918036 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1039 _100908 a x' _45444) = (term1039 _100908 a x' _45444).
Proof. exact (eq_refl (term1039 _100908 a x' _45444)). Qed.
Lemma lem3918037 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1077 _100908 b a x' _45444) = (term1085 _100908 b a x' _45444).
Proof. exact (MK_COMB (@lem3918035 _100908 b a _45444) (@lem3918036 _100908 a x' _45444)). Qed.
Lemma lem3918038 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1074 _100908 x' b a _45444) = (term1085 _100908 b a x' _45444).
Proof. exact (TRANS (@lem3918022 _100908 b a x' _45444) (@lem3918037 _100908 b a x' _45444)). Qed.
Lemma lem3918040 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : b x) : term719 _100908 b a x.
Proof. exact (conj (@lem3917917 _100908 b x h2) (@lem3917925 _100908 a x h1)). Qed.
Lemma lem3918042 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1085 _100908 b a x' _45444.
Proof. exact (EQ_MP (@lem3918038 _100908 b a x' _45444) (@lem3918019 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3918043 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1085 _100908 b a x' _45444.
Proof. exact (@lem3918042 _100908 _45444 x a b x' h1). Qed.
Lemma lem3918044 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1085 _100908 b a x' x.
Proof. exact (@lem3918043 _100908 x x a b x' h1). Qed.
Lemma lem3918047 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1039 _100908 a x' x.
Proof. exact (@lem3918044 _100908 x a b x' h3 (@lem3918040 _100908 a b x h1 h2)). Qed.
Lemma lem3918048 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1086 _100908 a x' x.
Proof. exact (fun h0 : term1087 _100908 a x' x => @lem3918047 _100908 x a b x' h1 h2 h3). Qed.
Lemma lem3918050 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918051 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term1086 _100908 a x' x) = (term1039 _100908 a x' x).
Proof. exact (@lem3918050 (term1039 _100908 a x' x)). Qed.
Lemma lem3918052 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1039 _100908 a x' x.
Proof. exact (EQ_MP (@lem3918051 _100908 a x' x) (@lem3918048 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918054 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918055 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) (_45461 : _100908) : (term1063 _100908 _45461 a _45460) = (term1088 _100908 a _45460 _45461).
Proof. exact (@lem3918054 (term1060 _100908 _45461 a _45460) (term692 _100908 _45460 _45461)). Qed.
Lemma lem3918057 (a : Prop) (b : Prop) : (term1078 a b) = (term1079 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3918058 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : (term1089 _100908 _45461 a _45460) = (term1090 _100908 _45461 a _45460).
Proof. exact (@lem3918057 (a _45461) (term688 _100908 a _45460)). Qed.
Lemma lem3918060 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3918061 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) : (term751 _100908 a _45460) = (a _45460).
Proof. exact (@lem3918060 (a _45460)). Qed.
Lemma lem3918062 {_100908 : Type'} (a : _100908 -> Prop) (_45461 : _100908) : (term689 _100908 a _45461) = (term689 _100908 a _45461).
Proof. exact (eq_refl (term689 _100908 a _45461)). Qed.
Lemma lem3918063 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : (term1090 _100908 _45461 a _45460) = (term1091 _100908 _45461 a _45460).
Proof. exact (MK_COMB (@lem3918062 _100908 a _45461) (@lem3918061 _100908 a _45460)). Qed.
Lemma lem3918064 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : (term1089 _100908 _45461 a _45460) = (term1091 _100908 _45461 a _45460).
Proof. exact (TRANS (@lem3918058 _100908 _45461 a _45460) (@lem3918063 _100908 _45461 a _45460)). Qed.
Lemma lem3918065 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918066 {_100908 : Type'} (_45461 : _100908) (a : _100908 -> Prop) (_45460 : _100908) : (term1092 _100908 _45461 a _45460) = (term1093 _100908 _45461 a _45460).
Proof. exact (MK_COMB (@lem3918065) (@lem3918064 _100908 _45461 a _45460)). Qed.
Lemma lem3918067 {_100908 : Type'} (_45460 : _100908) (_45461 : _100908) : (term692 _100908 _45460 _45461) = (term692 _100908 _45460 _45461).
Proof. exact (eq_refl (term692 _100908 _45460 _45461)). Qed.
Lemma lem3918068 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) (_45461 : _100908) : (term1088 _100908 a _45460 _45461) = (term1094 _100908 a _45460 _45461).
Proof. exact (MK_COMB (@lem3918066 _100908 _45461 a _45460) (@lem3918067 _100908 _45460 _45461)). Qed.
Lemma lem3918069 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) (_45461 : _100908) : (term1063 _100908 _45461 a _45460) = (term1094 _100908 a _45460 _45461).
Proof. exact (TRANS (@lem3918055 _100908 a _45460 _45461) (@lem3918068 _100908 a _45460 _45461)). Qed.
Lemma lem3918071 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1095 _100908 a x' x.
Proof. exact (conj (@lem3917910 _100908 a x h1) (@lem3918052 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918073 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) (_45461 : _100908) : term1094 _100908 a _45460 _45461.
Proof. exact (EQ_MP (@lem3918069 _100908 a _45460 _45461) (@lem3917858 _100908 _45461 a _45460)). Qed.
Lemma lem3918074 {_100908 : Type'} (a : _100908 -> Prop) (_45460 : _100908) (_45461 : _100908) : term1094 _100908 a _45460 _45461.
Proof. exact (@lem3918073 _100908 a _45460 _45461). Qed.
Lemma lem3918075 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : term1096 _100908 a x' x.
Proof. exact (@lem3918074 _100908 a (x' x) x). Qed.
Lemma lem3918078 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1097 _100908 x' x.
Proof. exact (@lem3918075 _100908 a x' x (@lem3918071 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918079 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1098 _100908 x' x.
Proof. exact (fun h0 : (x' x) = x => @lem3918078 _100908 x a b x' h1 h2 h3). Qed.
Lemma lem3918081 (p : Prop) : (term1065 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3918082 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) : (term1098 _100908 x' x) = (term1097 _100908 x' x).
Proof. exact (@lem3918081 ((x' x) = x)). Qed.
Lemma lem3918083 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1097 _100908 x' x.
Proof. exact (EQ_MP (@lem3918082 _100908 x' x) (@lem3918079 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918089 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3918090 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1053 _100908 a b x' _45444) = (term1099 _100908 a b x' _45444).
Proof. exact (@lem3918089 (a _45444) (term688 _100908 b _45444) (term1040 _100908 b x' _45444)). Qed.
Lemma lem3918114 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3918115 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1040 _100908 b x' _45444) = (term1100 _100908 b x' _45444).
Proof. exact (@lem3918114 ((x' _45444) = _45444) (term1087 _100908 b x' _45444)). Qed.
Lemma lem3918123 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term753 _100908 b _45444) = (term753 _100908 b _45444).
Proof. exact (eq_refl (term753 _100908 b _45444)). Qed.
Lemma lem3918124 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1101 _100908 b x' _45444) = (term1102 _100908 b x' _45444).
Proof. exact (MK_COMB (@lem3918123 _100908 b _45444) (@lem3918115 _100908 b x' _45444)). Qed.
Lemma lem3918128 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3918129 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1102 _100908 b x' _45444) = (term1103 _100908 b x' _45444).
Proof. exact (@lem3918128 ((x' _45444) = _45444) (term688 _100908 b _45444) (term1087 _100908 b x' _45444)). Qed.
Lemma lem3918147 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1101 _100908 b x' _45444) = (term1103 _100908 b x' _45444).
Proof. exact (TRANS (@lem3918124 _100908 b x' _45444) (@lem3918129 _100908 b x' _45444)). Qed.
Lemma lem3918148 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (term771 _100908 a _45444) = (term771 _100908 a _45444).
Proof. exact (eq_refl (term771 _100908 a _45444)). Qed.
Lemma lem3918149 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1099 _100908 a b x' _45444) = (term1104 _100908 a b x' _45444).
Proof. exact (MK_COMB (@lem3918148 _100908 a _45444) (@lem3918147 _100908 b x' _45444)). Qed.
Lemma lem3918160 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1053 _100908 a b x' _45444) = (term1104 _100908 a b x' _45444).
Proof. exact (TRANS (@lem3918090 _100908 a b x' _45444) (@lem3918149 _100908 a b x' _45444)). Qed.
Lemma lem3918161 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3918162 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1105 _100908 a b x' _45444) = (term1106 _100908 a b x' _45444).
Proof. exact (MK_COMB (@lem3918161) (@lem3918160 _100908 a b x' _45444)). Qed.
Lemma lem3918166 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3918167 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1107 _100908 b a x' _45444) = (term1108 _100908 b a x' _45444).
Proof. exact (@lem3918166 (term688 _100908 b _45444) (term1087 _100908 b x' _45444) (term1109 _100908 a x' _45444)). Qed.
Lemma lem3918181 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3918182 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1110 _100908 b a x' _45444) = (term1044 _100908 a b x' _45444).
Proof. exact (@lem3918181 (a _45444) (term1087 _100908 b x' _45444) ((x' _45444) = _45444)). Qed.
Lemma lem3918196 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3918197 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1040 _100908 b x' _45444) = (term1100 _100908 b x' _45444).
Proof. exact (@lem3918196 ((x' _45444) = _45444) (term1087 _100908 b x' _45444)). Qed.
Lemma lem3918205 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (term771 _100908 a _45444) = (term771 _100908 a _45444).
Proof. exact (eq_refl (term771 _100908 a _45444)). Qed.
Lemma lem3918206 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1044 _100908 a b x' _45444) = (term1111 _100908 a b x' _45444).
Proof. exact (MK_COMB (@lem3918205 _100908 a _45444) (@lem3918197 _100908 b x' _45444)). Qed.
Lemma lem3918217 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1110 _100908 b a x' _45444) = (term1111 _100908 a b x' _45444).
Proof. exact (TRANS (@lem3918182 _100908 a b x' _45444) (@lem3918206 _100908 a b x' _45444)). Qed.
Lemma lem3918218 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term753 _100908 b _45444) = (term753 _100908 b _45444).
Proof. exact (eq_refl (term753 _100908 b _45444)). Qed.
Lemma lem3918219 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1108 _100908 b a x' _45444) = (term1112 _100908 a b x' _45444).
Proof. exact (MK_COMB (@lem3918218 _100908 b _45444) (@lem3918217 _100908 a b x' _45444)). Qed.
Lemma lem3918223 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3918224 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1112 _100908 a b x' _45444) = (term1113 _100908 a b x' _45444).
Proof. exact (@lem3918223 (a _45444) (term688 _100908 b _45444) (term1100 _100908 b x' _45444)). Qed.
Lemma lem3918238 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3918239 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1102 _100908 b x' _45444) = (term1103 _100908 b x' _45444).
Proof. exact (@lem3918238 ((x' _45444) = _45444) (term688 _100908 b _45444) (term1087 _100908 b x' _45444)). Qed.
Lemma lem3918257 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (term771 _100908 a _45444) = (term771 _100908 a _45444).
Proof. exact (eq_refl (term771 _100908 a _45444)). Qed.
Lemma lem3918258 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1113 _100908 a b x' _45444) = (term1104 _100908 a b x' _45444).
Proof. exact (MK_COMB (@lem3918257 _100908 a _45444) (@lem3918239 _100908 b x' _45444)). Qed.
Lemma lem3918269 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1112 _100908 a b x' _45444) = (term1104 _100908 a b x' _45444).
Proof. exact (TRANS (@lem3918224 _100908 a b x' _45444) (@lem3918258 _100908 a b x' _45444)). Qed.
Lemma lem3918270 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1108 _100908 b a x' _45444) = (term1104 _100908 a b x' _45444).
Proof. exact (TRANS (@lem3918219 _100908 a b x' _45444) (@lem3918269 _100908 a b x' _45444)). Qed.
Lemma lem3918271 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1107 _100908 b a x' _45444) = (term1104 _100908 a b x' _45444).
Proof. exact (TRANS (@lem3918167 _100908 b a x' _45444) (@lem3918270 _100908 a b x' _45444)). Qed.
Lemma lem3918272 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : ((term1053 _100908 a b x' _45444) = (term1107 _100908 b a x' _45444)) = ((term1104 _100908 a b x' _45444) = (term1104 _100908 a b x' _45444)).
Proof. exact (MK_COMB (@lem3918162 _100908 a b x' _45444) (@lem3918271 _100908 a b x' _45444)). Qed.
Lemma lem3918274 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3918275 (x : Prop) : (x = x) = True.
Proof. exact (@lem3918274 Prop x). Qed.
Lemma lem3918276 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : ((term1104 _100908 a b x' _45444) = (term1104 _100908 a b x' _45444)) = True.
Proof. exact (@lem3918275 (term1104 _100908 a b x' _45444)). Qed.
Lemma lem3918277 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : ((term1053 _100908 a b x' _45444) = (term1107 _100908 b a x' _45444)) = True.
Proof. exact (TRANS (@lem3918272 _100908 a b x' _45444) (@lem3918276 _100908 a b x' _45444)). Qed.
Lemma lem3918278 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : True = ((term1053 _100908 a b x' _45444) = (term1107 _100908 b a x' _45444)).
Proof. exact (SYM (@lem3918277 _100908 b a x' _45444)). Qed.
Lemma lem3918279 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1053 _100908 a b x' _45444) = (term1107 _100908 b a x' _45444).
Proof. exact (EQ_MP (@lem3918278 _100908 b a x' _45444) (@lem0)). Qed.
Lemma lem3918280 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1107 _100908 b a x' _45444.
Proof. exact (EQ_MP (@lem3918279 _100908 b a x' _45444) (@lem3917673 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3918282 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918283 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1107 _100908 b a x' _45444) = (term1114 _100908 a b x' _45444).
Proof. exact (@lem3918282 (term1115 _100908 b a x' _45444) (term1087 _100908 b x' _45444)). Qed.
Lemma lem3918285 (a : Prop) (b : Prop) : (term1078 a b) = (term1079 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3918286 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1116 _100908 b a x' _45444) = (term1117 _100908 b a x' _45444).
Proof. exact (@lem3918285 (term688 _100908 b _45444) (term1109 _100908 a x' _45444)). Qed.
Lemma lem3918288 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3918289 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term751 _100908 b _45444) = (b _45444).
Proof. exact (@lem3918288 (b _45444)). Qed.
Lemma lem3918290 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3918291 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term1082 _100908 b _45444) = (term686 _100908 b _45444).
Proof. exact (MK_COMB (@lem3918290) (@lem3918289 _100908 b _45444)). Qed.
Lemma lem3918293 (a : Prop) (b : Prop) : (term1078 a b) = (term1079 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3918294 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1118 _100908 a x' _45444) = (term1119 _100908 a x' _45444).
Proof. exact (@lem3918293 (a _45444) ((x' _45444) = _45444)). Qed.
Lemma lem3918295 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1117 _100908 b a x' _45444) = (term1120 _100908 b a x' _45444).
Proof. exact (MK_COMB (@lem3918291 _100908 b _45444) (@lem3918294 _100908 a x' _45444)). Qed.
Lemma lem3918296 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1116 _100908 b a x' _45444) = (term1120 _100908 b a x' _45444).
Proof. exact (TRANS (@lem3918286 _100908 b a x' _45444) (@lem3918295 _100908 b a x' _45444)). Qed.
Lemma lem3918297 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918298 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1121 _100908 b a x' _45444) = (term1122 _100908 b a x' _45444).
Proof. exact (MK_COMB (@lem3918297) (@lem3918296 _100908 b a x' _45444)). Qed.
Lemma lem3918299 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1087 _100908 b x' _45444) = (term1087 _100908 b x' _45444).
Proof. exact (eq_refl (term1087 _100908 b x' _45444)). Qed.
Lemma lem3918300 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1114 _100908 a b x' _45444) = (term1123 _100908 a b x' _45444).
Proof. exact (MK_COMB (@lem3918298 _100908 b a x' _45444) (@lem3918299 _100908 b x' _45444)). Qed.
Lemma lem3918301 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1107 _100908 b a x' _45444) = (term1123 _100908 a b x' _45444).
Proof. exact (TRANS (@lem3918283 _100908 a b x' _45444) (@lem3918300 _100908 a b x' _45444)). Qed.
Lemma lem3918303 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1119 _100908 a x' x.
Proof. exact (conj (@lem3917902 _100908 a x h1) (@lem3918083 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918304 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1120 _100908 b a x' x.
Proof. exact (conj (@lem3917894 _100908 b x h2) (@lem3918303 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918306 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1123 _100908 a b x' _45444.
Proof. exact (EQ_MP (@lem3918301 _100908 a b x' _45444) (@lem3918280 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3918307 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1123 _100908 a b x' _45444.
Proof. exact (@lem3918306 _100908 _45444 x a b x' h1). Qed.
Lemma lem3918308 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1123 _100908 a b x' x.
Proof. exact (@lem3918307 _100908 x x a b x' h1). Qed.
Lemma lem3918311 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1087 _100908 b x' x.
Proof. exact (@lem3918308 _100908 x a b x' h3 (@lem3918304 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918312 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1124 _100908 b x' x.
Proof. exact (fun h0 : term1039 _100908 b x' x => @lem3918311 _100908 x a b x' h1 h2 h3). Qed.
Lemma lem3918314 (p : Prop) : (term1065 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3918315 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term1124 _100908 b x' x) = (term1087 _100908 b x' x).
Proof. exact (@lem3918314 (term1039 _100908 b x' x)). Qed.
Lemma lem3918316 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1087 _100908 b x' x.
Proof. exact (EQ_MP (@lem3918315 _100908 b x' x) (@lem3918312 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918318 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918321 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45445 : _100908) : (term720 _100908 a b _45445) = (term1125 _100908 b a _45445).
Proof. exact (@lem3918318 (b _45445) (term688 _100908 a _45445)). Qed.
Lemma lem3918324 {_100908 : Type'} (_45445 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1125 _100908 b a _45445.
Proof. exact (EQ_MP (@lem3918321 _100908 b a _45445) (@lem3917645 _100908 _45445 x a b x' h1)). Qed.
Lemma lem3918325 {_100908 : Type'} (_45445 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1125 _100908 b a _45445.
Proof. exact (@lem3918324 _100908 _45445 x a b x' h1). Qed.
Lemma lem3918326 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1126 _100908 b a x' x.
Proof. exact (@lem3918325 _100908 (x' x) x a b x' h1). Qed.
Lemma lem3918329 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1087 _100908 a x' x.
Proof. exact (@lem3918326 _100908 x a b x' h3 (@lem3918316 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918330 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1124 _100908 a x' x.
Proof. exact (fun h0 : term1039 _100908 a x' x => @lem3918329 _100908 x a b x' h1 h2 h3). Qed.
Lemma lem3918332 (p : Prop) : (term1065 p) = (~ p).
Proof. exact (EQ_MP (@lem21028 p) (@lem21107 p)). Qed.
Lemma lem3918333 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (x : _100908) : (term1124 _100908 a x' x) = (term1087 _100908 a x' x).
Proof. exact (@lem3918332 (term1039 _100908 a x' x)). Qed.
Lemma lem3918334 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1087 _100908 a x' x.
Proof. exact (EQ_MP (@lem3918333 _100908 a x' x) (@lem3918330 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918340 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3918341 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1052 _100908 b a x' _45444) = (term1067 _100908 b a x' _45444).
Proof. exact (@lem3918340 (a _45444) (term688 _100908 b _45444) (term1039 _100908 a x' _45444)). Qed.
Lemma lem3918355 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3918356 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1068 _100908 b a x' _45444) = (term1069 _100908 a x' b _45444).
Proof. exact (@lem3918355 (term1039 _100908 a x' _45444) (term688 _100908 b _45444)). Qed.
Lemma lem3918362 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (term771 _100908 a _45444) = (term771 _100908 a _45444).
Proof. exact (eq_refl (term771 _100908 a _45444)). Qed.
Lemma lem3918363 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1067 _100908 b a x' _45444) = (term1070 _100908 a x' b _45444).
Proof. exact (MK_COMB (@lem3918362 _100908 a _45444) (@lem3918356 _100908 a x' b _45444)). Qed.
Lemma lem3918374 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1052 _100908 b a x' _45444) = (term1070 _100908 a x' b _45444).
Proof. exact (TRANS (@lem3918341 _100908 b a x' _45444) (@lem3918363 _100908 a x' b _45444)). Qed.
Lemma lem3918375 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3918376 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1071 _100908 b a x' _45444) = (term1072 _100908 a x' b _45444).
Proof. exact (MK_COMB (@lem3918375) (@lem3918374 _100908 a x' b _45444)). Qed.
Lemma lem3918390 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3918391 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1068 _100908 b a x' _45444) = (term1069 _100908 a x' b _45444).
Proof. exact (@lem3918390 (term1039 _100908 a x' _45444) (term688 _100908 b _45444)). Qed.
Lemma lem3918397 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (term771 _100908 a _45444) = (term771 _100908 a _45444).
Proof. exact (eq_refl (term771 _100908 a _45444)). Qed.
Lemma lem3918398 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : (term1067 _100908 b a x' _45444) = (term1070 _100908 a x' b _45444).
Proof. exact (MK_COMB (@lem3918397 _100908 a _45444) (@lem3918391 _100908 a x' b _45444)). Qed.
Lemma lem3918409 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : ((term1052 _100908 b a x' _45444) = (term1067 _100908 b a x' _45444)) = ((term1070 _100908 a x' b _45444) = (term1070 _100908 a x' b _45444)).
Proof. exact (MK_COMB (@lem3918376 _100908 a x' b _45444) (@lem3918398 _100908 a x' b _45444)). Qed.
Lemma lem3918411 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3918412 (x : Prop) : (x = x) = True.
Proof. exact (@lem3918411 Prop x). Qed.
Lemma lem3918413 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (b : _100908 -> Prop) (_45444 : _100908) : ((term1070 _100908 a x' b _45444) = (term1070 _100908 a x' b _45444)) = True.
Proof. exact (@lem3918412 (term1070 _100908 a x' b _45444)). Qed.
Lemma lem3918414 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : ((term1052 _100908 b a x' _45444) = (term1067 _100908 b a x' _45444)) = True.
Proof. exact (TRANS (@lem3918409 _100908 a x' b _45444) (@lem3918413 _100908 a x' b _45444)). Qed.
Lemma lem3918415 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : True = ((term1052 _100908 b a x' _45444) = (term1067 _100908 b a x' _45444)).
Proof. exact (SYM (@lem3918414 _100908 b a x' _45444)). Qed.
Lemma lem3918416 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1052 _100908 b a x' _45444) = (term1067 _100908 b a x' _45444).
Proof. exact (EQ_MP (@lem3918415 _100908 b a x' _45444) (@lem0)). Qed.
Lemma lem3918417 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1067 _100908 b a x' _45444.
Proof. exact (EQ_MP (@lem3918416 _100908 b a x' _45444) (@lem3917659 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3918419 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918420 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (a : _100908 -> Prop) (_45444 : _100908) : (term1067 _100908 b a x' _45444) = (term1127 _100908 b x' a _45444).
Proof. exact (@lem3918419 (term1068 _100908 b a x' _45444) (a _45444)). Qed.
Lemma lem3918422 (a : Prop) (b : Prop) : (term1078 a b) = (term1079 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3918423 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1128 _100908 b a x' _45444) = (term1129 _100908 b a x' _45444).
Proof. exact (@lem3918422 (term688 _100908 b _45444) (term1039 _100908 a x' _45444)). Qed.
Lemma lem3918425 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3918426 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term751 _100908 b _45444) = (b _45444).
Proof. exact (@lem3918425 (b _45444)). Qed.
Lemma lem3918427 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3918428 {_100908 : Type'} (b : _100908 -> Prop) (_45444 : _100908) : (term1082 _100908 b _45444) = (term686 _100908 b _45444).
Proof. exact (MK_COMB (@lem3918427) (@lem3918426 _100908 b _45444)). Qed.
Lemma lem3918429 {_100908 : Type'} (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1087 _100908 a x' _45444) = (term1087 _100908 a x' _45444).
Proof. exact (eq_refl (term1087 _100908 a x' _45444)). Qed.
Lemma lem3918430 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1129 _100908 b a x' _45444) = (term1130 _100908 b a x' _45444).
Proof. exact (MK_COMB (@lem3918428 _100908 b _45444) (@lem3918429 _100908 a x' _45444)). Qed.
Lemma lem3918431 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1128 _100908 b a x' _45444) = (term1130 _100908 b a x' _45444).
Proof. exact (TRANS (@lem3918423 _100908 b a x' _45444) (@lem3918430 _100908 b a x' _45444)). Qed.
Lemma lem3918432 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918433 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (x' : _100908 -> _100908) (_45444 : _100908) : (term1131 _100908 b a x' _45444) = (term1132 _100908 b a x' _45444).
Proof. exact (MK_COMB (@lem3918432) (@lem3918431 _100908 b a x' _45444)). Qed.
Lemma lem3918434 {_100908 : Type'} (a : _100908 -> Prop) (_45444 : _100908) : (a _45444) = (a _45444).
Proof. exact (eq_refl (a _45444)). Qed.
Lemma lem3918435 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (a : _100908 -> Prop) (_45444 : _100908) : (term1127 _100908 b x' a _45444) = (term1133 _100908 b x' a _45444).
Proof. exact (MK_COMB (@lem3918433 _100908 b a x' _45444) (@lem3918434 _100908 a _45444)). Qed.
Lemma lem3918436 {_100908 : Type'} (b : _100908 -> Prop) (x' : _100908 -> _100908) (a : _100908 -> Prop) (_45444 : _100908) : (term1067 _100908 b a x' _45444) = (term1133 _100908 b x' a _45444).
Proof. exact (TRANS (@lem3918420 _100908 b x' a _45444) (@lem3918435 _100908 b x' a _45444)). Qed.
Lemma lem3918438 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1130 _100908 b a x' x.
Proof. exact (conj (@lem3917887 _100908 b x h2) (@lem3918334 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918440 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1133 _100908 b x' a _45444.
Proof. exact (EQ_MP (@lem3918436 _100908 b x' a _45444) (@lem3918417 _100908 _45444 x a b x' h1)). Qed.
Lemma lem3918441 {_100908 : Type'} (_45444 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1133 _100908 b x' a _45444.
Proof. exact (@lem3918440 _100908 _45444 x a b x' h1). Qed.
Lemma lem3918442 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term1133 _100908 b x' a x.
Proof. exact (@lem3918441 _100908 x x a b x' h1). Qed.
Lemma lem3918445 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : a x.
Proof. exact (@lem3918442 _100908 x a b x' h3 (@lem3918438 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918446 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : b x) (h2 : term926 _100908 x a b x') : term1054 _100908 a x.
Proof. exact (fun h0 : term688 _100908 a x => @lem3918445 _100908 x a b x' h0 h1 h2). Qed.
Lemma lem3918448 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918449 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term1054 _100908 a x) = (a x).
Proof. exact (@lem3918448 (a x)). Qed.
Lemma lem3918450 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : b x) (h2 : term926 _100908 x a b x') : a x.
Proof. exact (EQ_MP (@lem3918449 _100908 a x) (@lem3918446 _100908 x a b x' h1 h2)). Qed.
Lemma lem3918453 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3918455 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term688 _100908 a x) = (term1056 _100908 a x).
Proof. exact (@lem3918453 (a x)). Qed.
Lemma lem3918458 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) : term1056 _100908 a x.
Proof. exact (EQ_MP (@lem3918455 _100908 a x) (@lem3917647 _100908 a x h1)). Qed.
Lemma lem3918461 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (@lem3918458 _100908 a x h1 (@lem3918450 _100908 x a b x' h2 h3)). Qed.
Lemma lem3918462 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : term1057.
Proof. exact (fun h0 : ~ False => @lem3918461 _100908 x a b x' h1 h2 h3). Qed.
Lemma lem3918464 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918465 : term1057 = False.
Proof. exact (@lem3918464 False). Qed.
Lemma lem3918466 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918465) (@lem3918462 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918502 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (h1). Qed.
Lemma lem3918503 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : term1054 _100908 a x.
Proof. exact (fun h0 : term688 _100908 a x => @lem3918502 _100908 a x h1). Qed.
Lemma lem3918505 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918506 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term1054 _100908 a x) = (a x).
Proof. exact (@lem3918505 (a x)). Qed.
Lemma lem3918507 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : a x) : a x.
Proof. exact (EQ_MP (@lem3918506 _100908 a x) (@lem3918503 _100908 a x h1)). Qed.
Lemma lem3918513 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3918514 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : (term720 _100908 a b _45447) = (term809 _100908 b a _45447).
Proof. exact (@lem3918513 (b _45447) (term688 _100908 a _45447)). Qed.
Lemma lem3918520 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3918521 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : (term1134 _100908 a b _45447) = (term1135 _100908 b a _45447).
Proof. exact (MK_COMB (@lem3918520) (@lem3918514 _100908 b a _45447)). Qed.
Lemma lem3918527 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : (term809 _100908 b a _45447) = (term809 _100908 b a _45447).
Proof. exact (eq_refl (term809 _100908 b a _45447)). Qed.
Lemma lem3918528 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : ((term720 _100908 a b _45447) = (term809 _100908 b a _45447)) = ((term809 _100908 b a _45447) = (term809 _100908 b a _45447)).
Proof. exact (MK_COMB (@lem3918521 _100908 b a _45447) (@lem3918527 _100908 b a _45447)). Qed.
Lemma lem3918530 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3918531 (x : Prop) : (x = x) = True.
Proof. exact (@lem3918530 Prop x). Qed.
Lemma lem3918532 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : ((term809 _100908 b a _45447) = (term809 _100908 b a _45447)) = True.
Proof. exact (@lem3918531 (term809 _100908 b a _45447)). Qed.
Lemma lem3918533 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : ((term720 _100908 a b _45447) = (term809 _100908 b a _45447)) = True.
Proof. exact (TRANS (@lem3918528 _100908 b a _45447) (@lem3918532 _100908 b a _45447)). Qed.
Lemma lem3918534 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : True = ((term720 _100908 a b _45447) = (term809 _100908 b a _45447)).
Proof. exact (SYM (@lem3918533 _100908 b a _45447)). Qed.
Lemma lem3918535 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45447 : _100908) : (term720 _100908 a b _45447) = (term809 _100908 b a _45447).
Proof. exact (EQ_MP (@lem3918534 _100908 b a _45447) (@lem0)). Qed.
Lemma lem3918536 {_100908 : Type'} (_45447 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term809 _100908 b a _45447.
Proof. exact (EQ_MP (@lem3918535 _100908 b a _45447) (@lem3917679 _100908 _45447 x a b x' h1)). Qed.
Lemma lem3918538 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918539 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45447 : _100908) : (term809 _100908 b a _45447) = (term1136 _100908 a b _45447).
Proof. exact (@lem3918538 (term688 _100908 a _45447) (b _45447)). Qed.
Lemma lem3918541 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3918542 {_100908 : Type'} (a : _100908 -> Prop) (_45447 : _100908) : (term751 _100908 a _45447) = (a _45447).
Proof. exact (@lem3918541 (a _45447)). Qed.
Lemma lem3918543 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918544 {_100908 : Type'} (a : _100908 -> Prop) (_45447 : _100908) : (term1137 _100908 a _45447) = (term671 _100908 a _45447).
Proof. exact (MK_COMB (@lem3918543) (@lem3918542 _100908 a _45447)). Qed.
Lemma lem3918545 {_100908 : Type'} (b : _100908 -> Prop) (_45447 : _100908) : (b _45447) = (b _45447).
Proof. exact (eq_refl (b _45447)). Qed.
Lemma lem3918546 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45447 : _100908) : (term1136 _100908 a b _45447) = (term673 _100908 a b _45447).
Proof. exact (MK_COMB (@lem3918544 _100908 a _45447) (@lem3918545 _100908 b _45447)). Qed.
Lemma lem3918547 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45447 : _100908) : (term809 _100908 b a _45447) = (term673 _100908 a b _45447).
Proof. exact (TRANS (@lem3918539 _100908 a b _45447) (@lem3918546 _100908 a b _45447)). Qed.
Lemma lem3918550 {_100908 : Type'} (_45447 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term673 _100908 a b _45447.
Proof. exact (EQ_MP (@lem3918547 _100908 a b _45447) (@lem3918536 _100908 _45447 x a b x' h1)). Qed.
Lemma lem3918551 {_100908 : Type'} (_45447 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term673 _100908 a b _45447.
Proof. exact (@lem3918550 _100908 _45447 x a b x' h1). Qed.
Lemma lem3918552 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : term673 _100908 a b x.
Proof. exact (@lem3918551 _100908 x x a b x' h1). Qed.
Lemma lem3918555 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : a x) (h2 : term926 _100908 x a b x') : b x.
Proof. exact (@lem3918552 _100908 x a b x' h2 (@lem3918507 _100908 a x h1)). Qed.
Lemma lem3918556 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : a x) (h2 : term926 _100908 x a b x') : term1054 _100908 b x.
Proof. exact (fun h0 : term688 _100908 b x => @lem3918555 _100908 x a b x' h1 h2). Qed.
Lemma lem3918558 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918559 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term1054 _100908 b x) = (b x).
Proof. exact (@lem3918558 (b x)). Qed.
Lemma lem3918560 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : a x) (h2 : term926 _100908 x a b x') : b x.
Proof. exact (EQ_MP (@lem3918559 _100908 b x) (@lem3918556 _100908 x a b x' h1 h2)). Qed.
Lemma lem3918563 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3918565 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term688 _100908 b x) = (term1056 _100908 b x).
Proof. exact (@lem3918563 (b x)). Qed.
Lemma lem3918568 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) : term1056 _100908 b x.
Proof. exact (EQ_MP (@lem3918565 _100908 b x) (@lem3917681 _100908 b x h1)). Qed.
Lemma lem3918571 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (@lem3918568 _100908 b x h1 (@lem3918560 _100908 x a b x' h2 h3)). Qed.
Lemma lem3918572 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : term1057.
Proof. exact (fun h0 : ~ False => @lem3918571 _100908 x a b x' h1 h2 h3). Qed.
Lemma lem3918574 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918575 : term1057 = False.
Proof. exact (@lem3918574 False). Qed.
Lemma lem3918576 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918575) (@lem3918572 _100908 x a b x' h1 h2 h3)). Qed.
Lemma lem3918612 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (h1). Qed.
Lemma lem3918613 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : term1054 _100908 b x.
Proof. exact (fun h0 : term688 _100908 b x => @lem3918612 _100908 b x h1). Qed.
Lemma lem3918615 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918616 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term1054 _100908 b x) = (b x).
Proof. exact (@lem3918615 (b x)). Qed.
Lemma lem3918617 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : b x) : b x.
Proof. exact (EQ_MP (@lem3918616 _100908 b x) (@lem3918613 _100908 b x h1)). Qed.
Lemma lem3918620 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3918622 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term688 _100908 b x) = (term1056 _100908 b x).
Proof. exact (@lem3918620 (b x)). Qed.
Lemma lem3918625 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) : term1056 _100908 b x.
Proof. exact (EQ_MP (@lem3918622 _100908 b x) (@lem3917715 _100908 b x h1)). Qed.
Lemma lem3918628 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (@lem3918625 _100908 b x h1 (@lem3918617 _100908 b x h2)). Qed.
Lemma lem3918629 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : term1057.
Proof. exact (fun h0 : ~ False => @lem3918628 _100908 b x h1 h2). Qed.
Lemma lem3918631 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918632 : term1057 = False.
Proof. exact (@lem3918631 False). Qed.
Lemma lem3918633 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem3918632) (@lem3918629 _100908 b x h1 h2)). Qed.
Lemma lem3918661 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (h1 : term719 _100908 a b x) : a x.
Proof. exact (proj1 (@lem3917208 _100908 a b x h1)). Qed.
Lemma lem3918662 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (h1 : term719 _100908 a b x) : term1054 _100908 a x.
Proof. exact (fun h0 : term688 _100908 a x => @lem3918661 _100908 a b x h1). Qed.
Lemma lem3918664 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918665 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) : (term1054 _100908 a x) = (a x).
Proof. exact (@lem3918664 (a x)). Qed.
Lemma lem3918666 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (h1 : term719 _100908 a b x) : a x.
Proof. exact (EQ_MP (@lem3918665 _100908 a x) (@lem3918662 _100908 a b x h1)). Qed.
Lemma lem3918672 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3918673 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : (term720 _100908 a b _45450) = (term809 _100908 b a _45450).
Proof. exact (@lem3918672 (b _45450) (term688 _100908 a _45450)). Qed.
Lemma lem3918679 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3918680 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : (term1134 _100908 a b _45450) = (term1135 _100908 b a _45450).
Proof. exact (MK_COMB (@lem3918679) (@lem3918673 _100908 b a _45450)). Qed.
Lemma lem3918686 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : (term809 _100908 b a _45450) = (term809 _100908 b a _45450).
Proof. exact (eq_refl (term809 _100908 b a _45450)). Qed.
Lemma lem3918687 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : ((term720 _100908 a b _45450) = (term809 _100908 b a _45450)) = ((term809 _100908 b a _45450) = (term809 _100908 b a _45450)).
Proof. exact (MK_COMB (@lem3918680 _100908 b a _45450) (@lem3918686 _100908 b a _45450)). Qed.
Lemma lem3918689 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3918690 (x : Prop) : (x = x) = True.
Proof. exact (@lem3918689 Prop x). Qed.
Lemma lem3918691 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : ((term809 _100908 b a _45450) = (term809 _100908 b a _45450)) = True.
Proof. exact (@lem3918690 (term809 _100908 b a _45450)). Qed.
Lemma lem3918692 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : ((term720 _100908 a b _45450) = (term809 _100908 b a _45450)) = True.
Proof. exact (TRANS (@lem3918687 _100908 b a _45450) (@lem3918691 _100908 b a _45450)). Qed.
Lemma lem3918693 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : True = ((term720 _100908 a b _45450) = (term809 _100908 b a _45450)).
Proof. exact (SYM (@lem3918692 _100908 b a _45450)). Qed.
Lemma lem3918694 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45450 : _100908) : (term720 _100908 a b _45450) = (term809 _100908 b a _45450).
Proof. exact (EQ_MP (@lem3918693 _100908 b a _45450) (@lem0)). Qed.
Lemma lem3918695 {_100908 : Type'} (_45450 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term809 _100908 b a _45450.
Proof. exact (EQ_MP (@lem3918694 _100908 b a _45450) (@lem3917755 _100908 _45450 x a b x'' h1)). Qed.
Lemma lem3918697 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918698 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45450 : _100908) : (term809 _100908 b a _45450) = (term1136 _100908 a b _45450).
Proof. exact (@lem3918697 (term688 _100908 a _45450) (b _45450)). Qed.
Lemma lem3918700 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3918701 {_100908 : Type'} (a : _100908 -> Prop) (_45450 : _100908) : (term751 _100908 a _45450) = (a _45450).
Proof. exact (@lem3918700 (a _45450)). Qed.
Lemma lem3918702 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918703 {_100908 : Type'} (a : _100908 -> Prop) (_45450 : _100908) : (term1137 _100908 a _45450) = (term671 _100908 a _45450).
Proof. exact (MK_COMB (@lem3918702) (@lem3918701 _100908 a _45450)). Qed.
Lemma lem3918704 {_100908 : Type'} (b : _100908 -> Prop) (_45450 : _100908) : (b _45450) = (b _45450).
Proof. exact (eq_refl (b _45450)). Qed.
Lemma lem3918705 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45450 : _100908) : (term1136 _100908 a b _45450) = (term673 _100908 a b _45450).
Proof. exact (MK_COMB (@lem3918703 _100908 a _45450) (@lem3918704 _100908 b _45450)). Qed.
Lemma lem3918706 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (_45450 : _100908) : (term809 _100908 b a _45450) = (term673 _100908 a b _45450).
Proof. exact (TRANS (@lem3918698 _100908 a b _45450) (@lem3918705 _100908 a b _45450)). Qed.
Lemma lem3918709 {_100908 : Type'} (_45450 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term673 _100908 a b _45450.
Proof. exact (EQ_MP (@lem3918706 _100908 a b _45450) (@lem3918695 _100908 _45450 x a b x'' h1)). Qed.
Lemma lem3918710 {_100908 : Type'} (_45450 : _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term673 _100908 a b _45450.
Proof. exact (@lem3918709 _100908 _45450 x a b x'' h1). Qed.
Lemma lem3918711 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term673 _100908 a b x.
Proof. exact (@lem3918710 _100908 x x a b x'' h1). Qed.
Lemma lem3918714 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term719 _100908 a b x) (h2 : term975 _100908 x a b x'') : b x.
Proof. exact (@lem3918711 _100908 x a b x'' h2 (@lem3918666 _100908 a b x h1)). Qed.
Lemma lem3918715 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term719 _100908 a b x) (h2 : term975 _100908 x a b x'') : term1054 _100908 b x.
Proof. exact (fun h0 : term688 _100908 b x => @lem3918714 _100908 x a b x'' h1 h2). Qed.
Lemma lem3918717 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918718 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term1054 _100908 b x) = (b x).
Proof. exact (@lem3918717 (b x)). Qed.
Lemma lem3918719 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term719 _100908 a b x) (h2 : term975 _100908 x a b x'') : b x.
Proof. exact (EQ_MP (@lem3918718 _100908 b x) (@lem3918715 _100908 x a b x'' h1 h2)). Qed.
Lemma lem3918722 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3918724 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) : (term688 _100908 b x) = (term1056 _100908 b x).
Proof. exact (@lem3918722 (b x)). Qed.
Lemma lem3918727 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (x : _100908) (h1 : term719 _100908 a b x) : term1056 _100908 b x.
Proof. exact (EQ_MP (@lem3918724 _100908 b x) (@lem3917749 _100908 a b x h1)). Qed.
Lemma lem3918730 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term719 _100908 a b x) (h2 : term975 _100908 x a b x'') : False.
Proof. exact (@lem3918727 _100908 a b x h1 (@lem3918719 _100908 x a b x'' h1 h2)). Qed.
Lemma lem3918731 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term719 _100908 a b x) (h2 : term975 _100908 x a b x'') : term1057.
Proof. exact (fun h0 : ~ False => @lem3918730 _100908 x a b x'' h1 h2). Qed.
Lemma lem3918733 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918734 : term1057 = False.
Proof. exact (@lem3918733 False). Qed.
Lemma lem3918735 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term719 _100908 a b x) (h2 : term975 _100908 x a b x'') : False.
Proof. exact (EQ_MP (@lem3918734) (@lem3918731 _100908 x a b x'' h1 h2)). Qed.
Lemma lem3918763 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : b x''.
Proof. exact (proj1 (@lem3917202 _100908 x a b x'' h1)). Qed.
Lemma lem3918764 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term1054 _100908 b x''.
Proof. exact (fun h0 : term688 _100908 b x'' => @lem3918763 _100908 x a b x'' h1). Qed.
Lemma lem3918766 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918767 {_100908 : Type'} (b : _100908 -> Prop) (x'' : _100908) : (term1054 _100908 b x'') = (b x'').
Proof. exact (@lem3918766 (b x'')). Qed.
Lemma lem3918768 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : b x''.
Proof. exact (EQ_MP (@lem3918767 _100908 b x'') (@lem3918764 _100908 x a b x'' h1)). Qed.
Lemma lem3918770 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3918771 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45452 : _100908) : (term809 _100908 a b _45452) = (term1136 _100908 b a _45452).
Proof. exact (@lem3918770 (term688 _100908 b _45452) (a _45452)). Qed.
Lemma lem3918773 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3918774 {_100908 : Type'} (b : _100908 -> Prop) (_45452 : _100908) : (term751 _100908 b _45452) = (b _45452).
Proof. exact (@lem3918773 (b _45452)). Qed.
Lemma lem3918775 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918776 {_100908 : Type'} (b : _100908 -> Prop) (_45452 : _100908) : (term1137 _100908 b _45452) = (term671 _100908 b _45452).
Proof. exact (MK_COMB (@lem3918775) (@lem3918774 _100908 b _45452)). Qed.
Lemma lem3918777 {_100908 : Type'} (a : _100908 -> Prop) (_45452 : _100908) : (a _45452) = (a _45452).
Proof. exact (eq_refl (a _45452)). Qed.
Lemma lem3918778 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45452 : _100908) : (term1136 _100908 b a _45452) = (term673 _100908 b a _45452).
Proof. exact (MK_COMB (@lem3918776 _100908 b _45452) (@lem3918777 _100908 a _45452)). Qed.
Lemma lem3918779 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) (_45452 : _100908) : (term809 _100908 a b _45452) = (term673 _100908 b a _45452).
Proof. exact (TRANS (@lem3918771 _100908 b a _45452) (@lem3918778 _100908 b a _45452)). Qed.
Lemma lem3918782 {_100908 : Type'} (_45452 : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term673 _100908 b a _45452.
Proof. exact (EQ_MP (@lem3918779 _100908 b a _45452) (@lem3917771 _100908 _45452 a b h1)). Qed.
Lemma lem3918783 {_100908 : Type'} (_45452 : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term673 _100908 b a _45452.
Proof. exact (@lem3918782 _100908 _45452 a b h1). Qed.
Lemma lem3918784 {_100908 : Type'} (x'' : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term824 _100908 a b) : term673 _100908 b a x''.
Proof. exact (@lem3918783 _100908 x'' a b h1). Qed.
Lemma lem3918787 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term824 _100908 a b) (h2 : term975 _100908 x a b x'') : a x''.
Proof. exact (@lem3918784 _100908 x'' a b h1 (@lem3918768 _100908 x a b x'' h2)). Qed.
Lemma lem3918788 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term824 _100908 a b) (h2 : term975 _100908 x a b x'') : term1054 _100908 a x''.
Proof. exact (fun h0 : term688 _100908 a x'' => @lem3918787 _100908 x a b x'' h1 h2). Qed.
Lemma lem3918790 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918791 {_100908 : Type'} (a : _100908 -> Prop) (x'' : _100908) : (term1054 _100908 a x'') = (a x'').
Proof. exact (@lem3918790 (a x'')). Qed.
Lemma lem3918792 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term824 _100908 a b) (h2 : term975 _100908 x a b x'') : a x''.
Proof. exact (EQ_MP (@lem3918791 _100908 a x'') (@lem3918788 _100908 x a b x'' h1 h2)). Qed.
Lemma lem3918795 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3918797 {_100908 : Type'} (a : _100908 -> Prop) (x'' : _100908) : (term688 _100908 a x'') = (term1056 _100908 a x'').
Proof. exact (@lem3918795 (a x'')). Qed.
Lemma lem3918800 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : term1056 _100908 a x''.
Proof. exact (EQ_MP (@lem3918797 _100908 a x'') (@lem3917765 _100908 x a b x'' h1)). Qed.
Lemma lem3918803 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term824 _100908 a b) (h2 : term975 _100908 x a b x'') : False.
Proof. exact (@lem3918800 _100908 x a b x'' h2 (@lem3918792 _100908 x a b x'' h1 h2)). Qed.
Lemma lem3918804 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term824 _100908 a b) (h2 : term975 _100908 x a b x'') : term1057.
Proof. exact (fun h0 : ~ False => @lem3918803 _100908 x a b x'' h1 h2). Qed.
Lemma lem3918806 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3918807 : term1057 = False.
Proof. exact (@lem3918806 False). Qed.
Lemma lem3918808 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term824 _100908 a b) (h2 : term975 _100908 x a b x'') : False.
Proof. exact (EQ_MP (@lem3918807) (@lem3918804 _100908 x a b x'' h1 h2)). Qed.
Lemma lem3918809 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem3918633 _100908 b x h1 h2) (fun h3 : False => @lem3917717 _100908 b x h2)). Qed.
Lemma lem3918810 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem3918809 _100908 b x h1 h2) (@lem3917717 _100908 b x h2)). Qed.
Lemma lem3918811 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : (term688 _100908 b x) = False.
Proof. exact (prop_ext (fun h3 : term688 _100908 b x => @lem3918810 _100908 b x h1 h2) (fun h3 : False => @lem3917715 _100908 b x h1)). Qed.
Lemma lem3918812 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem3918811 _100908 b x h1 h2) (@lem3917715 _100908 b x h1)). Qed.
Lemma lem3918813 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3918576 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917683 _100908 a x h2)). Qed.
Lemma lem3918814 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918813 _100908 x a b x' h1 h2 h3) (@lem3917683 _100908 a x h2)). Qed.
Lemma lem3918815 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : (term688 _100908 b x) = False.
Proof. exact (prop_ext (fun h4 : term688 _100908 b x => @lem3918814 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917681 _100908 b x h1)). Qed.
Lemma lem3918816 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918815 _100908 x a b x' h1 h2 h3) (@lem3917681 _100908 b x h1)). Qed.
Lemma lem3918817 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : (b x) = False.
Proof. exact (prop_ext (fun h4 : b x => @lem3918466 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917649 _100908 b x h2)). Qed.
Lemma lem3918818 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918817 _100908 x a b x' h1 h2 h3) (@lem3917649 _100908 b x h2)). Qed.
Lemma lem3918819 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : (term688 _100908 a x) = False.
Proof. exact (prop_ext (fun h4 : term688 _100908 a x => @lem3918818 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917647 _100908 a x h1)). Qed.
Lemma lem3918820 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918819 _100908 x a b x' h1 h2 h3) (@lem3917647 _100908 a x h1)). Qed.
Lemma lem3918821 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3917846 _100908 a x h1 h2) (fun h3 : False => @lem3917615 _100908 a x h2)). Qed.
Lemma lem3918822 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem3918821 _100908 a x h1 h2) (@lem3917615 _100908 a x h2)). Qed.
Lemma lem3918823 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : (term688 _100908 a x) = False.
Proof. exact (prop_ext (fun h3 : term688 _100908 a x => @lem3918822 _100908 a x h1 h2) (fun h3 : False => @lem3917613 _100908 a x h1)). Qed.
Lemma lem3918824 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem3918823 _100908 a x h1 h2) (@lem3917613 _100908 a x h1)). Qed.
Lemma lem3918825 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem3918812 _100908 b x h1 h2) (fun h3 : False => @lem3917461 _100908 b x h2)). Qed.
Lemma lem3918826 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem3918825 _100908 b x h1 h2) (@lem3917461 _100908 b x h2)). Qed.
Lemma lem3918827 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : (term688 _100908 b x) = False.
Proof. exact (prop_ext (fun h3 : term688 _100908 b x => @lem3918826 _100908 b x h1 h2) (fun h3 : False => @lem3917457 _100908 b x h1)). Qed.
Lemma lem3918828 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem3918827 _100908 b x h1 h2) (@lem3917457 _100908 b x h1)). Qed.
Lemma lem3918829 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3918816 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917399 _100908 a x h2)). Qed.
Lemma lem3918830 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918829 _100908 x a b x' h1 h2 h3) (@lem3917399 _100908 a x h2)). Qed.
Lemma lem3918831 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : (term688 _100908 b x) = False.
Proof. exact (prop_ext (fun h4 : term688 _100908 b x => @lem3918830 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917395 _100908 b x h1)). Qed.
Lemma lem3918832 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918831 _100908 x a b x' h1 h2 h3) (@lem3917395 _100908 b x h1)). Qed.
Lemma lem3918833 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : (b x) = False.
Proof. exact (prop_ext (fun h4 : b x => @lem3918820 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917337 _100908 b x h2)). Qed.
Lemma lem3918834 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918833 _100908 x a b x' h1 h2 h3) (@lem3917337 _100908 b x h2)). Qed.
Lemma lem3918835 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : (term688 _100908 a x) = False.
Proof. exact (prop_ext (fun h4 : term688 _100908 a x => @lem3918834 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917333 _100908 a x h1)). Qed.
Lemma lem3918836 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918835 _100908 x a b x' h1 h2 h3) (@lem3917333 _100908 a x h1)). Qed.
Lemma lem3918837 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3918824 _100908 a x h1 h2) (fun h3 : False => @lem3917275 _100908 a x h2)). Qed.
Lemma lem3918838 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem3918837 _100908 a x h1 h2) (@lem3917275 _100908 a x h2)). Qed.
Lemma lem3918839 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : (term688 _100908 a x) = False.
Proof. exact (prop_ext (fun h3 : term688 _100908 a x => @lem3918838 _100908 a x h1 h2) (fun h3 : False => @lem3917271 _100908 a x h1)). Qed.
Lemma lem3918840 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem3918839 _100908 a x h1 h2) (@lem3917271 _100908 a x h1)). Qed.
Lemma lem3918841 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : (b x) = False.
Proof. exact (prop_ext (fun h3 : b x => @lem3918828 _100908 b x h1 h2) (fun h3 : False => @lem3917461 _100908 b x h2)). Qed.
Lemma lem3918842 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem3918841 _100908 b x h1 h2) (@lem3917461 _100908 b x h2)). Qed.
Lemma lem3918843 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : (term688 _100908 b x) = False.
Proof. exact (prop_ext (fun h3 : term688 _100908 b x => @lem3918842 _100908 b x h1 h2) (fun h3 : False => @lem3917457 _100908 b x h1)). Qed.
Lemma lem3918844 {_100908 : Type'} (b : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 b x) (h2 : b x) : False.
Proof. exact (EQ_MP (@lem3918843 _100908 b x h1 h2) (@lem3917457 _100908 b x h1)). Qed.
Lemma lem3918845 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : (a x) = False.
Proof. exact (prop_ext (fun h4 : a x => @lem3918832 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917399 _100908 a x h2)). Qed.
Lemma lem3918846 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918845 _100908 x a b x' h1 h2 h3) (@lem3917399 _100908 a x h2)). Qed.
Lemma lem3918847 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : (term688 _100908 b x) = False.
Proof. exact (prop_ext (fun h4 : term688 _100908 b x => @lem3918846 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917395 _100908 b x h1)). Qed.
Lemma lem3918848 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : a x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918847 _100908 x a b x' h1 h2 h3) (@lem3917395 _100908 b x h1)). Qed.
Lemma lem3918849 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : (b x) = False.
Proof. exact (prop_ext (fun h4 : b x => @lem3918836 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917337 _100908 b x h2)). Qed.
Lemma lem3918850 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918849 _100908 x a b x' h1 h2 h3) (@lem3917337 _100908 b x h2)). Qed.
Lemma lem3918851 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : (term688 _100908 a x) = False.
Proof. exact (prop_ext (fun h4 : term688 _100908 a x => @lem3918850 _100908 x a b x' h1 h2 h3) (fun h4 : False => @lem3917333 _100908 a x h1)). Qed.
Lemma lem3918852 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : b x) (h3 : term926 _100908 x a b x') : False.
Proof. exact (EQ_MP (@lem3918851 _100908 x a b x' h1 h2 h3) (@lem3917333 _100908 a x h1)). Qed.
Lemma lem3918853 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : (a x) = False.
Proof. exact (prop_ext (fun h3 : a x => @lem3918840 _100908 a x h1 h2) (fun h3 : False => @lem3917275 _100908 a x h2)). Qed.
Lemma lem3918854 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem3918853 _100908 a x h1 h2) (@lem3917275 _100908 a x h2)). Qed.
Lemma lem3918855 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : (term688 _100908 a x) = False.
Proof. exact (prop_ext (fun h3 : term688 _100908 a x => @lem3918854 _100908 a x h1 h2) (fun h3 : False => @lem3917271 _100908 a x h1)). Qed.
Lemma lem3918856 {_100908 : Type'} (a : _100908 -> Prop) (x : _100908) (h1 : term688 _100908 a x) (h2 : a x) : False.
Proof. exact (EQ_MP (@lem3918855 _100908 a x h1 h2) (@lem3917271 _100908 a x h1)). Qed.
Lemma lem3918857 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term975 _100908 x a b x'') : False.
Proof. exact (or_elim (@lem3917203 _100908 x a b x'' h1) (fun h0 : term719 _100908 a b x => @lem3918735 _100908 x a b x'' h0 h1) (fun h0 : term824 _100908 a b => @lem3918808 _100908 x a b x'' h0 h1)). Qed.
Lemma lem3918858 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 b x) (h2 : term926 _100908 x a b x') : False.
Proof. exact (or_elim (@lem3917195 _100908 x a b x' h2) (fun h0 : a x => @lem3918848 _100908 x a b x' h1 h0 h2) (fun h0 : b x => @lem3918844 _100908 b x h1 h0)). Qed.
Lemma lem3918859 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term688 _100908 a x) (h2 : term926 _100908 x a b x') : False.
Proof. exact (or_elim (@lem3917195 _100908 x a b x' h2) (fun h0 : a x => @lem3918856 _100908 a x h1 h0) (fun h0 : b x => @lem3918852 _100908 x a b x' h1 h0 h2)). Qed.
Lemma lem3918860 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x' : _100908 -> _100908) (h1 : term926 _100908 x a b x') : False.
Proof. exact (or_elim (@lem3917194 _100908 x a b x' h1) (fun h0 : term688 _100908 a x => @lem3918859 _100908 x a b x' h0 h1) (fun h0 : term688 _100908 b x => @lem3918858 _100908 x a b x' h0 h1)). Qed.
Lemma lem3918861 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term1027 _100908 x' x a b x'') : False.
Proof. exact (or_elim (@lem3917187 _100908 x' x a b x'' h1) (fun h0 : term926 _100908 x a b x' => @lem3918860 _100908 x a b x' h0) (fun h0 : term975 _100908 x a b x'' => @lem3918857 _100908 x a b x'' h0)). Qed.
Lemma lem3918862 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term1027 _100908 x' x a b x'') : (term1027 _100908 x' x a b x'') = False.
Proof. exact (prop_ext (fun h2 : term1027 _100908 x' x a b x'' => @lem3918861 _100908 x' x a b x'' h1) (fun h2 : False => @lem3917187 _100908 x' x a b x'' h1)). Qed.
Lemma lem3918863 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (x'' : _100908) (h1 : term1027 _100908 x' x a b x'') : False.
Proof. exact (EQ_MP (@lem3918862 _100908 x' x a b x'' h1) (@lem3917187 _100908 x' x a b x'' h1)). Qed.
Lemma lem3918864 {_100908 : Type'} (x' : _100908 -> _100908) (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term1030 _100908 x' x a b) : False.
Proof. exact (ex_elim (@lem3917009 _100908 x' x a b h1) (fun x'' : _100908 => fun h0 : term1029 _100908 x' x a b x'' => @lem3918863 _100908 x' x a b x'' h0)). Qed.
Lemma lem3918865 {_100908 : Type'} (x : _100908) (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term1032 _100908 x a b) : False.
Proof. exact (ex_elim (@lem3917008 _100908 x a b h1) (fun x' : _100908 -> _100908 => fun h0 : term1031 _100908 x a b x' => @lem3918864 _100908 x' x a b h0)). Qed.
Lemma lem3918866 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : False.
Proof. exact (ex_elim (@lem3917007 _100908 a b h1) (fun x : _100908 => fun h0 : term1033 _100908 a b x => @lem3918865 _100908 x a b h0)). Qed.
Lemma lem3918867 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : (term705 _100908 a b) = False.
Proof. exact (prop_ext (fun h2 : term705 _100908 a b => @lem3918866 _100908 a b h1) (fun h2 : False => @lem3916177 _100908 a b h1)). Qed.
Lemma lem3918868 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : False.
Proof. exact (EQ_MP (@lem3918867 _100908 a b h1) (@lem3916177 _100908 a b h1)). Qed.
Lemma lem3918869 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term704 _100908 a b.
Proof. exact (fun h0 : term705 _100908 a b => @lem3918868 _100908 a b h0). Qed.
Lemma lem3918870 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term684 _100908 a b) = (term702 _100908 a b).
Proof. exact (EQ_MP (@lem3916176 _100908 a b) (@lem3918869 _100908 a b)). Qed.
Lemma lem3918875 {_100908 : Type'} (b : _100908 -> Prop) : term713 _100908 b.
Proof. exact (fun a : _100908 -> Prop => @lem3918870 _100908 a b). Qed.
Lemma lem3918880 {_100908 : Type'} : term717 _100908.
Proof. exact (fun b : _100908 -> Prop => @lem3918875 _100908 b). Qed.
Lemma lem3918881 {_100908 : Type'} : term716 _100908.
Proof. exact (EQ_MP (@lem3916172 _100908) (@lem3918880 _100908)). Qed.
Lemma lem3918882 {_100908 : Type'} (b : _100908 -> Prop) : term1138 _100908 b.
Proof. exact (@lem3918881 _100908 b). Qed.
Lemma lem3918883 {_100908 : Type'} (b : _100908 -> Prop) : (term1138 _100908 b) = (term712 _100908 b).
Proof. exact (eq_refl (term1138 _100908 b)). Qed.
Lemma lem3918884 {_100908 : Type'} (b : _100908 -> Prop) : term712 _100908 b.
Proof. exact (EQ_MP (@lem3918883 _100908 b) (@lem3918882 _100908 b)). Qed.
Lemma lem3918885 {_100908 : Type'} (b : _100908 -> Prop) (a : _100908 -> Prop) : term1139 _100908 b a.
Proof. exact (@lem3918884 _100908 b a). Qed.
Lemma lem3918886 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term1139 _100908 b a) = (term704 _100908 a b).
Proof. exact (eq_refl (term1139 _100908 b a)). Qed.
Lemma lem3918887 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term704 _100908 a b.
Proof. exact (EQ_MP (@lem3918886 _100908 a b) (@lem3918885 _100908 b a)). Qed.
Lemma lem3918889 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term704 _100908 a b.
Proof. exact (@lem3915978 _100908 a b (@lem3918887 _100908 a b)). Qed.
Lemma lem3918890 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : False.
Proof. exact (@lem3918889 _100908 a b (@lem3915962 _100908 a b h1)). Qed.
Lemma lem3918891 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : (term705 _100908 a b) = False.
Proof. exact (prop_ext (fun h2 : term705 _100908 a b => @lem3918890 _100908 a b h1) (fun h2 : False => @lem3915962 _100908 a b h1)). Qed.
Lemma lem3918892 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) (h1 : term705 _100908 a b) : False.
Proof. exact (EQ_MP (@lem3918891 _100908 a b h1) (@lem3915962 _100908 a b h1)). Qed.
Lemma lem3918893 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : term704 _100908 a b.
Proof. exact (fun h0 : term705 _100908 a b => @lem3918892 _100908 a b h0). Qed.
Lemma lem3918894 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term684 _100908 a b) = (term702 _100908 a b).
Proof. exact (EQ_MP (@lem3915961 _100908 a b) (@lem3918893 _100908 a b)). Qed.
Lemma lem3918895 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (term655 _100908 a b) = (term669 _100908 a b).
Proof. exact (EQ_MP (@lem3915957 _100908 a b) (@lem3918894 _100908 a b)). Qed.
Lemma lem3918902 {_100908 : Type'} (a : _100908 -> Prop) (b : _100908 -> Prop) : (@PSUBSET _100908 a b) = (term668 _100908 a b).
Proof. exact (EQ_MP (@lem3915812 _100908 a b) (@lem3918895 _100908 a b)). Qed.
Lemma lem3918903 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (@PSUBSET A a b) = (term668 A a b).
Proof. exact (@lem3918902 A a b). Qed.
Lemma lem3918912 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3918913 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1140 A a b) = (term1141 A a b).
Proof. exact (MK_COMB (@lem3918912) (@lem3918903 A a b)). Qed.
Lemma lem3918914 {A : Type'} (b : A -> Prop) : (@FINITE A b) = (@FINITE A b).
Proof. exact (eq_refl (@FINITE A b)). Qed.
Lemma lem3918915 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1142 A a b) = (term1143 A a b).
Proof. exact (MK_COMB (@lem3918913 A a b) (@lem3918914 A b)). Qed.
Lemma lem3918918 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3918919 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1144 A a b) = (term1145 A a b).
Proof. exact (MK_COMB (@lem3918918) (@lem3918915 A a b)). Qed.
Lemma lem3918920 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1146 A a b) = (term1146 A a b).
Proof. exact (eq_refl (term1146 A a b)). Qed.
Lemma lem3918921 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1147 A a b) = (term1148 A a b).
Proof. exact (MK_COMB (@lem3918919 A a b) (@lem3918920 A a b)). Qed.
Lemma lem3918924 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1148 A a b) = (term1147 A a b).
Proof. exact (SYM (@lem3918921 A a b)). Qed.
Lemma lem3918925 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1143 A a b) : term1143 A a b.
Proof. exact (h1). Qed.
Lemma lem3918926 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3918927 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term668 A a b) : term668 A a b.
Proof. exact (h1). Qed.
Lemma lem3918928 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term668 A a b) : term668 A a b.
Proof. exact (h1). Qed.
Lemma lem3918929 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term664 A a b x) : term664 A a b x.
Proof. exact (h1). Qed.
Lemma lem3918930 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term661 A a b x) : term661 A a b x.
Proof. exact (h1). Qed.
Lemma lem3918931 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : @IN A x b.
Proof. exact (h1). Qed.
Lemma lem3918932 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term658 A a b x) : term658 A a b x.
Proof. exact (h1). Qed.
Lemma lem3918933 {A : Type'} (x : A) (a : A -> Prop) (h1 : term687 A x a) : term687 A x a.
Proof. exact (h1). Qed.
Lemma lem3918935 (m : nat) (p : nat) : term642 m p.
Proof. exact (EQ_MP (@lem3915718 m p) (@lem3915717 m p)). Qed.
Lemma lem3918936 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term1149 A a b.
Proof. exact (@lem3918935 (@CARD A a) (@CARD A b)). Qed.
Lemma lem3918937 {A : Type'} (s : A -> Prop) : term1150 A s.
Proof. exact (@lem3610594 A s). Qed.
Lemma lem3918938 {A : Type'} (s : A -> Prop) : (term1150 A s) = (term1151 A s).
Proof. exact (eq_refl (term1150 A s)). Qed.
Lemma lem3918939 {A : Type'} (s : A -> Prop) : term1151 A s.
Proof. exact (EQ_MP (@lem3918938 A s) (@lem3918937 A s)). Qed.
Lemma lem3918940 {A : Type'} (s : A -> Prop) (x : A) : term1152 A s x.
Proof. exact (@lem3918939 A s x). Qed.
Lemma lem3918941 {A : Type'} (x : A) (s : A -> Prop) : (term1152 A s x) = ((term1153 A s x) = (@FINITE A s)).
Proof. exact (eq_refl (term1152 A s x)). Qed.
Lemma lem3918943 {A : Type'} (a : A -> Prop) : term1154 A a.
Proof. exact (@lem3902682 A a). Qed.
Lemma lem3918944 {A : Type'} (a : A -> Prop) : (term1154 A a) = (term1155 A a).
Proof. exact (eq_refl (term1154 A a)). Qed.
Lemma lem3918945 {A : Type'} (a : A -> Prop) : term1155 A a.
Proof. exact (EQ_MP (@lem3918944 A a) (@lem3918943 A a)). Qed.
Lemma lem3918946 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term1156 A a b.
Proof. exact (@lem3918945 A a b). Qed.
Lemma lem3918947 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1156 A a b) = (term1157 A a b).
Proof. exact (eq_refl (term1156 A a b)). Qed.
Lemma lem3918948 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term1157 A a b.
Proof. exact (EQ_MP (@lem3918947 A a b) (@lem3918946 A a b)). Qed.
Lemma lem3918949 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1158 A a b) : term1158 A a b.
Proof. exact (h1). Qed.
Lemma lem3918950 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1158 A a b) : term1159 A a b.
Proof. exact (@lem3918948 A a b (@lem3918949 A a b h1)). Qed.
Lemma lem3918951 {A : Type'} (a : A -> Prop) (b : A -> Prop) : (term1159 A a b) = ((term1159 A a b) = True).
Proof. exact (@lem7 (term1159 A a b)). Qed.
Lemma lem3918952 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1158 A a b) : (term1159 A a b) = True.
Proof. exact (EQ_MP (@lem3918951 A a b) (@lem3918950 A a b h1)). Qed.
Lemma lem3918958 {A : Type'} (b : A -> Prop) : (@FINITE A b) = ((@FINITE A b) = True).
Proof. exact (@lem7 (@FINITE A b)). Qed.
Lemma lem3918964 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term658 A a b x) = ((term658 A a b x) = True).
Proof. exact (@lem7 (term658 A a b x)). Qed.
Lemma lem3918969 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term1160 A a b.
Proof. exact (fun h0 : term1158 A a b => @lem3918952 A a b h0). Qed.
Lemma lem3918970 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term1160 A a b.
Proof. exact (@lem3918969 A a b). Qed.
Lemma lem3918971 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : term1161 A a b x.
Proof. exact (@lem3918970 A a (@DELETE A b x)). Qed.
Lemma lem3918975 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term658 A a b x) : (term658 A a b x) = True.
Proof. exact (EQ_MP (@lem3918964 A a b x) (@lem3918932 A a b x h1)). Qed.
Lemma lem3918976 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3918977 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term658 A a b x) : (term1162 A a b x) = (and True).
Proof. exact (MK_COMB (@lem3918976) (@lem3918975 A a b x h1)). Qed.
Lemma lem3918979 {A : Type'} (x : A) (s : A -> Prop) : (term1153 A s x) = (@FINITE A s).
Proof. exact (EQ_MP (@lem3918941 A x s) (@lem3918940 A s x)). Qed.
Lemma lem3918980 {A : Type'} (x : A) (s : A -> Prop) : (term1153 A s x) = (@FINITE A s).
Proof. exact (@lem3918979 A x s). Qed.
Lemma lem3918981 {A : Type'} (x : A) (b : A -> Prop) : (term1153 A b x) = (@FINITE A b).
Proof. exact (@lem3918980 A x b). Qed.
Lemma lem3918983 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (@FINITE A b) = True.
Proof. exact (EQ_MP (@lem3918958 A b) (@lem3918926 A b h1)). Qed.
Lemma lem3918984 {A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) : (term1153 A b x) = True.
Proof. exact (TRANS (@lem3918981 A x b) (@lem3918983 A b h1)). Qed.
Lemma lem3918985 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : (term1163 A a b x) = (True /\ True).
Proof. exact (MK_COMB (@lem3918977 A a b x h2) (@lem3918984 A x b h1)). Qed.
Lemma lem3918987 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3918988 : (True /\ True) = True.
Proof. exact (@lem3918987 True). Qed.
Lemma lem3918989 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : (term1163 A a b x) = True.
Proof. exact (TRANS (@lem3918985 A a b x h1 h2) (@lem3918988)). Qed.
Lemma lem3918990 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : True = (term1163 A a b x).
Proof. exact (SYM (@lem3918989 A a b x h1 h2)). Qed.
Lemma lem3918991 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : term1163 A a b x.
Proof. exact (EQ_MP (@lem3918990 A a b x h1 h2) (@lem0)). Qed.
Lemma lem3918992 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : (term1164 A a b x) = True.
Proof. exact (@lem3918971 A a b x (@lem3918991 A a b x h1 h2)). Qed.
Lemma lem3918993 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3918994 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : (term1165 A a b x) = (and True).
Proof. exact (MK_COMB (@lem3918993) (@lem3918992 A a b x h1 h2)). Qed.
Lemma lem3918995 {A : Type'} (x : A) (b : A -> Prop) : (term1166 A x b) = (term1166 A x b).
Proof. exact (eq_refl (term1166 A x b)). Qed.
Lemma lem3918996 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : (term1167 A a x b) = (term1168 A x b).
Proof. exact (MK_COMB (@lem3918994 A a b x h1 h2) (@lem3918995 A x b)). Qed.
Lemma lem3918998 (t : Prop) : (True /\ t) = t.
Proof. exact (proj1 (@lem1842 t)). Qed.
Lemma lem3918999 {A : Type'} (x : A) (b : A -> Prop) : (term1168 A x b) = (term1166 A x b).
Proof. exact (@lem3918998 (term1166 A x b)). Qed.
Lemma lem3919000 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : (term1167 A a x b) = (term1166 A x b).
Proof. exact (TRANS (@lem3918996 A a b x h1 h2) (@lem3918999 A x b)). Qed.
Lemma lem3919001 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term658 A a b x) : (term1166 A x b) = (term1167 A a x b).
Proof. exact (SYM (@lem3919000 A a b x h1 h2)). Qed.
Lemma lem3919002 {A : Type'} (x : A) : term1169 A x.
Proof. exact (@lem3845383 A x). Qed.
Lemma lem3919003 {A : Type'} (x : A) : (term1169 A x) = (term1170 A x).
Proof. exact (eq_refl (term1169 A x)). Qed.
Lemma lem3919004 {A : Type'} (x : A) : term1170 A x.
Proof. exact (EQ_MP (@lem3919003 A x) (@lem3919002 A x)). Qed.
Lemma lem3919005 {A : Type'} (x : A) (s : A -> Prop) : term1171 A x s.
Proof. exact (@lem3919004 A x s). Qed.
Lemma lem3919006 {A : Type'} (x : A) (s : A -> Prop) : (term1171 A x s) = (term1172 A x s).
Proof. exact (eq_refl (term1171 A x s)). Qed.
Lemma lem3919007 {A : Type'} (x : A) (s : A -> Prop) : term1172 A x s.
Proof. exact (EQ_MP (@lem3919006 A x s) (@lem3919005 A x s)). Qed.
Lemma lem3919008 {A : Type'} (s : A -> Prop) (h1 : @FINITE A s) : @FINITE A s.
Proof. exact (h1). Qed.
Lemma lem3919009 {A : Type'} (x : A) (s : A -> Prop) (h1 : @FINITE A s) : (term1173 A s x) = (term1174 A x s).
Proof. exact (@lem3919007 A x s (@lem3919008 A s h1)). Qed.
Lemma lem3919015 {A : Type'} (b : A -> Prop) : (@FINITE A b) = ((@FINITE A b) = True).
Proof. exact (@lem7 (@FINITE A b)). Qed.
Lemma lem3919017 {A : Type'} (x : A) (b : A -> Prop) : (@IN A x b) = ((@IN A x b) = True).
Proof. exact (@lem7 (@IN A x b)). Qed.
Lemma lem3919024 {A : Type'} (x : A) (s : A -> Prop) : term1172 A x s.
Proof. exact (fun h0 : @FINITE A s => @lem3919009 A x s h0). Qed.
Lemma lem3919025 {A : Type'} (x : A) (s : A -> Prop) : term1172 A x s.
Proof. exact (@lem3919024 A x s). Qed.
Lemma lem3919026 {A : Type'} (x : A) (b : A -> Prop) : term1172 A x b.
Proof. exact (@lem3919025 A x b). Qed.
Lemma lem3919028 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : (@FINITE A b) = True.
Proof. exact (EQ_MP (@lem3919015 A b) (@lem3918926 A b h1)). Qed.
Lemma lem3919029 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : True = (@FINITE A b).
Proof. exact (SYM (@lem3919028 A b h1)). Qed.
Lemma lem3919030 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (EQ_MP (@lem3919029 A b h1) (@lem0)). Qed.
Lemma lem3919031 {A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) : (term1173 A b x) = (term1174 A x b).
Proof. exact (@lem3919026 A x b (@lem3919030 A b h1)). Qed.
Lemma lem3919033 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) (e' : _2963) : term1175 _2963 g t e g' t' e'.
Proof. exact (EQ_MP (@lem14781 _2963 g t e g' t' e') (@lem15222 _2963 g t e g' t' e')). Qed.
Lemma lem3919034 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) (t' : _2963) : term1176 _2963 g t e g' t'.
Proof. exact (fun e' : _2963 => @lem3919033 _2963 g t e g' t' e'). Qed.
Lemma lem3919035 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) (g' : Prop) : term1177 _2963 g t e g'.
Proof. exact (fun t' : _2963 => @lem3919034 _2963 g t e g' t'). Qed.
Lemma lem3919036 {_2963 : Type'} (g : Prop) (t : _2963) (e : _2963) : term1178 _2963 g t e.
Proof. exact (fun g' : Prop => @lem3919035 _2963 g t e g'). Qed.
Lemma lem3919037 (g : Prop) (t : nat) (e : nat) : term1179 g t e.
Proof. exact (@lem3919036 nat g t e). Qed.
Lemma lem3919038 {A : Type'} (x : A) (b : A -> Prop) : term1180 A x b.
Proof. exact (@lem3919037 (@IN A x b) (term1181 A b) (@CARD A b)). Qed.
Lemma lem3919039 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) : term1182 A x b g'.
Proof. exact (@lem3919038 A x b g'). Qed.
Lemma lem3919040 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) : (term1182 A x b g') = (term1183 A x b g').
Proof. exact (eq_refl (term1182 A x b g')). Qed.
Lemma lem3919041 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) : term1183 A x b g'.
Proof. exact (EQ_MP (@lem3919040 A x b g') (@lem3919039 A x b g')). Qed.
Lemma lem3919042 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) (t' : nat) : term1184 A x b g' t'.
Proof. exact (@lem3919041 A x b g' t'). Qed.
Lemma lem3919043 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) (t' : nat) : (term1184 A x b g' t') = (term1185 A x b g' t').
Proof. exact (eq_refl (term1184 A x b g' t')). Qed.
Lemma lem3919044 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) (t' : nat) : term1185 A x b g' t'.
Proof. exact (EQ_MP (@lem3919043 A x b g' t') (@lem3919042 A x b g' t')). Qed.
Lemma lem3919045 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term1186 A x b g' t' e'.
Proof. exact (@lem3919044 A x b g' t' e'). Qed.
Lemma lem3919046 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : (term1186 A x b g' t' e') = (term1187 A x b g' t' e').
Proof. exact (eq_refl (term1186 A x b g' t' e')). Qed.
Lemma lem3919047 {A : Type'} (x : A) (b : A -> Prop) (g' : Prop) (t' : nat) (e' : nat) : term1187 A x b g' t' e'.
Proof. exact (EQ_MP (@lem3919046 A x b g' t' e') (@lem3919045 A x b g' t' e')). Qed.
Lemma lem3919049 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : (@IN A x b) = True.
Proof. exact (EQ_MP (@lem3919017 A x b) (@lem3918931 A x b h1)). Qed.
Lemma lem3919050 {A : Type'} (x : A) (b : A -> Prop) (t' : nat) (e' : nat) : term1188 A x b t' e'.
Proof. exact (@lem3919047 A x b True t' e'). Qed.
Lemma lem3919051 {A : Type'} (t' : nat) (e' : nat) (x : A) (b : A -> Prop) (h1 : @IN A x b) : term1189 A x b t' e'.
Proof. exact (@lem3919050 A x b t' e' (@lem3919049 A x b h1)). Qed.
Lemma lem3919057 {A : Type'} (b : A -> Prop) : (term1181 A b) = (term1181 A b).
Proof. exact (eq_refl (term1181 A b)). Qed.
Lemma lem3919058 {A : Type'} (b : A -> Prop) : term1190 A b.
Proof. exact (fun h0 : True => @lem3919057 A b). Qed.
Lemma lem3919059 {A : Type'} (e' : nat) (x : A) (b : A -> Prop) (h1 : @IN A x b) : term1191 A x b e'.
Proof. exact (@lem3919051 A (term1181 A b) e' x b h1). Qed.
Lemma lem3919060 {A : Type'} (e' : nat) (x : A) (b : A -> Prop) (h1 : @IN A x b) : term1192 A x b e'.
Proof. exact (@lem3919059 A e' x b h1 (@lem3919058 A b)). Qed.
Lemma lem3919064 {A : Type'} (b : A -> Prop) : (@CARD A b) = (@CARD A b).
Proof. exact (eq_refl (@CARD A b)). Qed.
Lemma lem3919065 {A : Type'} (b : A -> Prop) : term1193 A b.
Proof. exact (fun h0 : ~ True => @lem3919064 A b). Qed.
Lemma lem3919066 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : term1194 A x b.
Proof. exact (@lem3919060 A (@CARD A b) x b h1). Qed.
Lemma lem3919067 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : (term1174 A x b) = (term1195 A b).
Proof. exact (@lem3919066 A x b h1 (@lem3919065 A b)). Qed.
Lemma lem3919069 {A : Type'} (t2 : A) (t1 : A) : (@COND A True t1 t2) = t1.
Proof. exact (proj1 (@lem12653 A t1 t2)). Qed.
Lemma lem3919070 (t2 : nat) (t1 : nat) : (@COND nat True t1 t2) = t1.
Proof. exact (@lem3919069 nat t2 t1). Qed.
Lemma lem3919071 {A : Type'} (b : A -> Prop) : (term1195 A b) = (term1181 A b).
Proof. exact (@lem3919070 (@CARD A b) (term1181 A b)). Qed.
Lemma lem3919072 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : (term1174 A x b) = (term1181 A b).
Proof. exact (TRANS (@lem3919067 A x b h1) (@lem3919071 A b)). Qed.
Lemma lem3919073 {A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : (term1173 A b x) = (term1181 A b).
Proof. exact (TRANS (@lem3919031 A x b h1) (@lem3919072 A x b h2)). Qed.
Lemma lem3919074 : Peano.lt = Peano.lt.
Proof. exact (eq_refl Peano.lt). Qed.
Lemma lem3919075 {A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : (term1196 A b x) = (term1197 A b).
Proof. exact (MK_COMB (@lem3919074) (@lem3919073 A x b h1 h2)). Qed.
Lemma lem3919076 {A : Type'} (b : A -> Prop) : (@CARD A b) = (@CARD A b).
Proof. exact (eq_refl (@CARD A b)). Qed.
Lemma lem3919077 {A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : (term1166 A x b) = (term1198 A b).
Proof. exact (MK_COMB (@lem3919075 A x b h1 h2) (@lem3919076 A b)). Qed.
Lemma lem3919079 (n : nat) : (term7 n) = (term8 n).
Proof. exact (EQ_MP (@lem3915690 n) (@lem3915689 n)). Qed.
Lemma lem3919080 {A : Type'} (b : A -> Prop) : (term1198 A b) = (term1199 A b).
Proof. exact (@lem3919079 (@CARD A b)). Qed.
Lemma lem3919083 {A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : (term1166 A x b) = (term1199 A b).
Proof. exact (TRANS (@lem3919077 A x b h1 h2) (@lem3919080 A b)). Qed.
Lemma lem3919084 {A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : (term1199 A b) = (term1166 A x b).
Proof. exact (SYM (@lem3919083 A x b h1 h2)). Qed.
Lemma lem3919085 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : (@CARD A b) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3919086 {A : Type'} : term1200 A.
Proof. exact (@lem3854502 A). Qed.
Lemma lem3919088 {A : Type'} : term1201 A.
Proof. exact (@lem3216368 A). Qed.
Lemma lem3919090 {_99911 : Type'} : term1201 _99911.
Proof. exact (@lem3216368 _99911). Qed.
Lemma lem3919095 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1202 _99911 A a x b) : term1202 _99911 A a x b.
Proof. exact (h1). Qed.
Lemma lem3919096 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : term1203 _99911 A a x b.
Proof. exact (fun h0 : term1202 _99911 A a x b => @lem3919095 _99911 A a x b h0). Qed.
Lemma lem3919097 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1203 _99911 A a x b) : term1203 _99911 A a x b.
Proof. exact (h1). Qed.
Lemma lem3919098 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1202 _99911 A a x b) : term1202 _99911 A a x b.
Proof. exact (h1). Qed.
Lemma lem3919099 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1202 _99911 A a x b) (h2 : term1203 _99911 A a x b) : term1202 _99911 A a x b.
Proof. exact (@lem3919097 _99911 A a x b h2 (@lem3919098 _99911 A a x b h1)). Qed.
Lemma lem3919100 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1202 _99911 A a x b) : term1204 _99911 A a x b.
Proof. exact (fun h0 : term1203 _99911 A a x b => @lem3919099 _99911 A a x b h1 h0). Qed.
Lemma lem3919101 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1203 _99911 A a x b) : term1203 _99911 A a x b.
Proof. exact (h1). Qed.
Lemma lem3919102 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1202 _99911 A a x b) (h2 : term1203 _99911 A a x b) : term1202 _99911 A a x b.
Proof. exact (@lem3919100 _99911 A a x b h1 (@lem3919101 _99911 A a x b h2)). Qed.
Lemma lem3919103 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : term1203 _99911 A a x b) : term1203 _99911 A a x b.
Proof. exact (fun h0 : term1202 _99911 A a x b => @lem3919102 _99911 A a x b h0 h1). Qed.
Lemma lem3919104 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : term1205 _99911 A a x b.
Proof. exact (fun h0 : term1203 _99911 A a x b => @lem3919103 _99911 A a x b h0). Qed.
Lemma lem3919107 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : term1203 _99911 A a x b.
Proof. exact (@lem3919104 _99911 A a x b (@lem3919096 _99911 A a x b)). Qed.
Lemma lem3919108 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : term1203 _99911 A a x b.
Proof. exact (@lem3919107 _99911 A a x b). Qed.
Lemma lem3919160 (t : Prop) : (t -> False) = (~ t).
Proof. exact (proj2 (@lem16474 t)). Qed.
Lemma lem3919161 {A : Type'} : (term1206 A) = (term1207 A).
Proof. exact (@lem3919160 (term1200 A)). Qed.
Lemma lem3919168 {_99911 : Type'} : (term1208 _99911) = (term1208 _99911).
Proof. exact (eq_refl (term1208 _99911)). Qed.
Lemma lem3919169 {_99911 A : Type'} : (term1209 _99911 A) = (term1210 _99911 A).
Proof. exact (MK_COMB (@lem3919168 _99911) (@lem3919161 A)). Qed.
Lemma lem3919172 {A : Type'} : (term1211 A) = (term1211 A).
Proof. exact (eq_refl (term1211 A)). Qed.
Lemma lem3919173 {_99911 A : Type'} : (term1212 _99911 A) = (term1213 _99911 A).
Proof. exact (MK_COMB (@lem3919172 A) (@lem3919169 _99911 A)). Qed.
Lemma lem3919176 {_99911 : Type'} : (term1211 _99911) = (term1211 _99911).
Proof. exact (eq_refl (term1211 _99911)). Qed.
Lemma lem3919177 {_99911 A : Type'} : (term1214 _99911 A) = (term1215 _99911 A).
Proof. exact (MK_COMB (@lem3919176 _99911) (@lem3919173 _99911 A)). Qed.
Lemma lem3919180 {A : Type'} (b : A -> Prop) : (term1216 A b) = (term1216 A b).
Proof. exact (eq_refl (term1216 A b)). Qed.
Lemma lem3919181 {_99911 A : Type'} (b : A -> Prop) : (term1217 _99911 A b) = (term1218 _99911 A b).
Proof. exact (MK_COMB (@lem3919180 A b) (@lem3919177 _99911 A)). Qed.
Lemma lem3919184 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term1219 A a b x) = (term1219 A a b x).
Proof. exact (eq_refl (term1219 A a b x)). Qed.
Lemma lem3919185 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1220 _99911 A a x b) = (term1221 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919184 A a b x) (@lem3919181 _99911 A b)). Qed.
Lemma lem3919188 {A : Type'} (x : A) (a : A -> Prop) : (term1222 A x a) = (term1222 A x a).
Proof. exact (eq_refl (term1222 A x a)). Qed.
Lemma lem3919189 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1223 _99911 A a x b) = (term1224 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919188 A x a) (@lem3919185 _99911 A a x b)). Qed.
Lemma lem3919192 {A : Type'} (x : A) (b : A -> Prop) : (term670 A x b) = (term670 A x b).
Proof. exact (eq_refl (term670 A x b)). Qed.
Lemma lem3919193 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1225 _99911 A a x b) = (term1226 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919192 A x b) (@lem3919189 _99911 A a x b)). Qed.
Lemma lem3919196 {A : Type'} (b : A -> Prop) : (term1227 A b) = (term1227 A b).
Proof. exact (eq_refl (term1227 A b)). Qed.
Lemma lem3919197 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1202 _99911 A a x b) = (term1228 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919196 A b) (@lem3919193 _99911 A a x b)). Qed.
Lemma lem3919200 {_99911 A : Type'} (x : A) (b : A -> Prop) : (term1229 _99911 A x b) = (term1230 _99911 A x b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3919197 _99911 A a x b)). Qed.
Lemma lem3919201 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919202 {_99911 A : Type'} (x : A) (b : A -> Prop) : (term1231 _99911 A x b) = (term1232 _99911 A x b).
Proof. exact (MK_COMB (@lem3919201 A) (@lem3919200 _99911 A x b)). Qed.
Lemma lem3919207 {_99911 A : Type'} (b : A -> Prop) : (term1233 _99911 A b) = (term1234 _99911 A b).
Proof. exact (fun_ext (fun x : A => @lem3919202 _99911 A x b)). Qed.
Lemma lem3919208 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3919209 {_99911 A : Type'} (b : A -> Prop) : (term1235 _99911 A b) = (term1236 _99911 A b).
Proof. exact (MK_COMB (@lem3919208 A) (@lem3919207 _99911 A b)). Qed.
Lemma lem3919214 {_99911 A : Type'} : (term1237 _99911 A) = (term1238 _99911 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3919209 _99911 A b)). Qed.
Lemma lem3919215 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919224 {_99911 A : Type'} : (term1239 _99911 A) = (term1240 _99911 A).
Proof. exact (MK_COMB (@lem3919215 A) (@lem3919214 _99911 A)). Qed.
Lemma lem3919233 {A : Type'} (s : A -> Prop) : (term1241 A s) = (term1241 A s).
Proof. exact (eq_refl (term1241 A s)). Qed.
Lemma lem3919234 {A : Type'} : (term1242 A) = (term1242 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919233 A s)). Qed.
Lemma lem3919235 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919236 {A : Type'} : (term1200 A) = (term1200 A).
Proof. exact (MK_COMB (@lem3919235 A) (@lem3919234 A)). Qed.
Lemma lem3919237 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3919238 {A : Type'} : (term1207 A) = (term1207 A).
Proof. exact (MK_COMB (@lem3919237) (@lem3919236 A)). Qed.
Lemma lem3919247 {_99911 : Type'} (s : _99911 -> Prop) : (term1241 _99911 s) = (term1241 _99911 s).
Proof. exact (eq_refl (term1241 _99911 s)). Qed.
Lemma lem3919248 {_99911 : Type'} : (term1242 _99911) = (term1242 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919247 _99911 s)). Qed.
Lemma lem3919249 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919250 {_99911 : Type'} : (term1200 _99911) = (term1200 _99911).
Proof. exact (MK_COMB (@lem3919249 _99911) (@lem3919248 _99911)). Qed.
Lemma lem3919251 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3919252 {_99911 : Type'} : (term1208 _99911) = (term1208 _99911).
Proof. exact (MK_COMB (@lem3919251) (@lem3919250 _99911)). Qed.
Lemma lem3919253 {_99911 A : Type'} : (term1210 _99911 A) = (term1210 _99911 A).
Proof. exact (MK_COMB (@lem3919252 _99911) (@lem3919238 A)). Qed.
Lemma lem3919256 {A : Type'} (s : A -> Prop) : (term1243 A s) = (term1243 A s).
Proof. exact (eq_refl (term1243 A s)). Qed.
Lemma lem3919257 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem3919258 {A : Type'} (s : A -> Prop) : (term1244 A s) = (term1244 A s).
Proof. exact (fun_ext (fun x : A => @lem3919257 A x s)). Qed.
Lemma lem3919259 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3919260 {A : Type'} (s : A -> Prop) : (term1245 A s) = (term1245 A s).
Proof. exact (MK_COMB (@lem3919259 A) (@lem3919258 A s)). Qed.
Lemma lem3919261 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919262 {A : Type'} (s : A -> Prop) : (term1246 A s) = (term1246 A s).
Proof. exact (MK_COMB (@lem3919261) (@lem3919260 A s)). Qed.
Lemma lem3919263 {A : Type'} (s : A -> Prop) : ((term1245 A s) = (term1243 A s)) = ((term1245 A s) = (term1243 A s)).
Proof. exact (MK_COMB (@lem3919262 A s) (@lem3919256 A s)). Qed.
Lemma lem3919264 {A : Type'} : (term1247 A) = (term1247 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919263 A s)). Qed.
Lemma lem3919265 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919266 {A : Type'} : (term1201 A) = (term1201 A).
Proof. exact (MK_COMB (@lem3919265 A) (@lem3919264 A)). Qed.
Lemma lem3919267 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3919268 {A : Type'} : (term1211 A) = (term1211 A).
Proof. exact (MK_COMB (@lem3919267) (@lem3919266 A)). Qed.
Lemma lem3919269 {_99911 A : Type'} : (term1213 _99911 A) = (term1213 _99911 A).
Proof. exact (MK_COMB (@lem3919268 A) (@lem3919253 _99911 A)). Qed.
Lemma lem3919272 {_99911 : Type'} (s : _99911 -> Prop) : (term1243 _99911 s) = (term1243 _99911 s).
Proof. exact (eq_refl (term1243 _99911 s)). Qed.
Lemma lem3919273 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (@IN _99911 x s) = (@IN _99911 x s).
Proof. exact (eq_refl (@IN _99911 x s)). Qed.
Lemma lem3919274 {_99911 : Type'} (s : _99911 -> Prop) : (term1244 _99911 s) = (term1244 _99911 s).
Proof. exact (fun_ext (fun x : _99911 => @lem3919273 _99911 x s)). Qed.
Lemma lem3919275 {_99911 : Type'} : (@ex _99911) = (@ex _99911).
Proof. exact (eq_refl (@ex _99911)). Qed.
Lemma lem3919276 {_99911 : Type'} (s : _99911 -> Prop) : (term1245 _99911 s) = (term1245 _99911 s).
Proof. exact (MK_COMB (@lem3919275 _99911) (@lem3919274 _99911 s)). Qed.
Lemma lem3919277 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919278 {_99911 : Type'} (s : _99911 -> Prop) : (term1246 _99911 s) = (term1246 _99911 s).
Proof. exact (MK_COMB (@lem3919277) (@lem3919276 _99911 s)). Qed.
Lemma lem3919279 {_99911 : Type'} (s : _99911 -> Prop) : ((term1245 _99911 s) = (term1243 _99911 s)) = ((term1245 _99911 s) = (term1243 _99911 s)).
Proof. exact (MK_COMB (@lem3919278 _99911 s) (@lem3919272 _99911 s)). Qed.
Lemma lem3919280 {_99911 : Type'} : (term1247 _99911) = (term1247 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919279 _99911 s)). Qed.
Lemma lem3919281 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919282 {_99911 : Type'} : (term1201 _99911) = (term1201 _99911).
Proof. exact (MK_COMB (@lem3919281 _99911) (@lem3919280 _99911)). Qed.
Lemma lem3919283 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3919284 {_99911 : Type'} : (term1211 _99911) = (term1211 _99911).
Proof. exact (MK_COMB (@lem3919283) (@lem3919282 _99911)). Qed.
Lemma lem3919285 {_99911 A : Type'} : (term1215 _99911 A) = (term1215 _99911 A).
Proof. exact (MK_COMB (@lem3919284 _99911) (@lem3919269 _99911 A)). Qed.
Lemma lem3919288 {A : Type'} (b : A -> Prop) : (term1216 A b) = (term1216 A b).
Proof. exact (eq_refl (term1216 A b)). Qed.
Lemma lem3919289 {_99911 A : Type'} (b : A -> Prop) : (term1218 _99911 A b) = (term1218 _99911 A b).
Proof. exact (MK_COMB (@lem3919288 A b) (@lem3919285 _99911 A)). Qed.
Lemma lem3919292 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) : (term1219 A a b x) = (term1219 A a b x).
Proof. exact (eq_refl (term1219 A a b x)). Qed.
Lemma lem3919293 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1221 _99911 A a x b) = (term1221 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919292 A a b x) (@lem3919289 _99911 A b)). Qed.
Lemma lem3919298 {A : Type'} (x : A) (a : A -> Prop) : (term1222 A x a) = (term1222 A x a).
Proof. exact (eq_refl (term1222 A x a)). Qed.
Lemma lem3919299 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1224 _99911 A a x b) = (term1224 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919298 A x a) (@lem3919293 _99911 A a x b)). Qed.
Lemma lem3919302 {A : Type'} (x : A) (b : A -> Prop) : (term670 A x b) = (term670 A x b).
Proof. exact (eq_refl (term670 A x b)). Qed.
Lemma lem3919303 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1226 _99911 A a x b) = (term1226 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919302 A x b) (@lem3919299 _99911 A a x b)). Qed.
Lemma lem3919306 {A : Type'} (b : A -> Prop) : (term1227 A b) = (term1227 A b).
Proof. exact (eq_refl (term1227 A b)). Qed.
Lemma lem3919307 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1228 _99911 A a x b) = (term1228 _99911 A a x b).
Proof. exact (MK_COMB (@lem3919306 A b) (@lem3919303 _99911 A a x b)). Qed.
Lemma lem3919308 {_99911 A : Type'} (x : A) (b : A -> Prop) : (term1230 _99911 A x b) = (term1230 _99911 A x b).
Proof. exact (fun_ext (fun a : A -> Prop => @lem3919307 _99911 A a x b)). Qed.
Lemma lem3919309 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919310 {_99911 A : Type'} (x : A) (b : A -> Prop) : (term1232 _99911 A x b) = (term1232 _99911 A x b).
Proof. exact (MK_COMB (@lem3919309 A) (@lem3919308 _99911 A x b)). Qed.
Lemma lem3919311 {_99911 A : Type'} (b : A -> Prop) : (term1234 _99911 A b) = (term1234 _99911 A b).
Proof. exact (fun_ext (fun x : A => @lem3919310 _99911 A x b)). Qed.
Lemma lem3919312 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3919313 {_99911 A : Type'} (b : A -> Prop) : (term1236 _99911 A b) = (term1236 _99911 A b).
Proof. exact (MK_COMB (@lem3919312 A) (@lem3919311 _99911 A b)). Qed.
Lemma lem3919314 {_99911 A : Type'} : (term1238 _99911 A) = (term1238 _99911 A).
Proof. exact (fun_ext (fun b : A -> Prop => @lem3919313 _99911 A b)). Qed.
Lemma lem3919315 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919316 {_99911 A : Type'} : (term1240 _99911 A) = (term1240 _99911 A).
Proof. exact (MK_COMB (@lem3919315 A) (@lem3919314 _99911 A)). Qed.
Lemma lem3919393 {_99911 A : Type'} : (term1239 _99911 A) = (term1240 _99911 A).
Proof. exact (TRANS (@lem3919224 _99911 A) (@lem3919316 _99911 A)). Qed.
Lemma lem3919394 {_99911 A : Type'} : (term1240 _99911 A) = (term1239 _99911 A).
Proof. exact (SYM (@lem3919393 _99911 A)). Qed.
Lemma lem3919400 {_99911 : Type'} (h1 : term1201 _99911) : term1201 _99911.
Proof. exact (h1). Qed.
Lemma lem3919401 {A : Type'} (h1 : term1201 A) : term1201 A.
Proof. exact (h1). Qed.
Lemma lem3919403 {A : Type'} (h1 : term1200 A) : term1200 A.
Proof. exact (h1). Qed.
Lemma lem3919409 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3919415 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : @IN A x b.
Proof. exact (h1). Qed.
Lemma lem3919433 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : (@CARD A b) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3919435 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (@IN _99911 x s) = (@IN _99911 x s).
Proof. exact (eq_refl (@IN _99911 x s)). Qed.
Lemma lem3919436 {_99911 : Type'} (P : _99911 -> Prop) : (term780 _99911 P) = (term781 _99911 P).
Proof. exact (@lem18394 _99911 P). Qed.
Lemma lem3919437 {_99911 : Type'} (s : _99911 -> Prop) : (term1248 _99911 s) = (term1249 _99911 s).
Proof. exact (@lem3919436 _99911 (term1244 _99911 s)). Qed.
Lemma lem3919438 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1250 _99911 s x) = (@IN _99911 x s).
Proof. exact (eq_refl (term1250 _99911 s x)). Qed.
Lemma lem3919439 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3919441 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1251 _99911 s x) = (term687 _99911 x s).
Proof. exact (MK_COMB (@lem3919439) (@lem3919438 _99911 x s)). Qed.
Lemma lem3919442 {_99911 : Type'} (s : _99911 -> Prop) : (term1252 _99911 s) = (term1253 _99911 s).
Proof. exact (fun_ext (fun x : _99911 => @lem3919441 _99911 x s)). Qed.
Lemma lem3919443 {_99911 : Type'} : (@all _99911) = (@all _99911).
Proof. exact (eq_refl (@all _99911)). Qed.
Lemma lem3919444 {_99911 : Type'} (s : _99911 -> Prop) : (term1249 _99911 s) = (term1254 _99911 s).
Proof. exact (MK_COMB (@lem3919443 _99911) (@lem3919442 _99911 s)). Qed.
Lemma lem3919445 {_99911 : Type'} (s : _99911 -> Prop) : (term1248 _99911 s) = (term1254 _99911 s).
Proof. exact (TRANS (@lem3919437 _99911 s) (@lem3919444 _99911 s)). Qed.
Lemma lem3919446 {_99911 : Type'} (s : _99911 -> Prop) : (term1244 _99911 s) = (term1244 _99911 s).
Proof. exact (fun_ext (fun x : _99911 => @lem3919435 _99911 x s)). Qed.
Lemma lem3919447 {_99911 : Type'} : (@ex _99911) = (@ex _99911).
Proof. exact (eq_refl (@ex _99911)). Qed.
Lemma lem3919448 {_99911 : Type'} (s : _99911 -> Prop) : (term1245 _99911 s) = (term1245 _99911 s).
Proof. exact (MK_COMB (@lem3919447 _99911) (@lem3919446 _99911 s)). Qed.
Lemma lem3919449 {_99911 : Type'} (s : _99911 -> Prop) : (term1243 _99911 s) = (term1243 _99911 s).
Proof. exact (eq_refl (term1243 _99911 s)). Qed.
Lemma lem3919452 {_99911 : Type'} (s : _99911 -> Prop) : (term1255 _99911 s) = (s = (@EMPTY _99911)).
Proof. exact (@lem16933 (s = (@EMPTY _99911))). Qed.
Lemma lem3919453 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919454 {_99911 : Type'} (s : _99911 -> Prop) : (term1256 _99911 s) = (term1257 _99911 s).
Proof. exact (MK_COMB (@lem3919453) (@lem3919445 _99911 s)). Qed.
Lemma lem3919455 {_99911 : Type'} (s : _99911 -> Prop) : (term1258 _99911 s) = (term1259 _99911 s).
Proof. exact (MK_COMB (@lem3919454 _99911 s) (@lem3919449 _99911 s)). Qed.
Lemma lem3919456 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919457 {_99911 : Type'} (s : _99911 -> Prop) : (term1260 _99911 s) = (term1260 _99911 s).
Proof. exact (MK_COMB (@lem3919456) (@lem3919448 _99911 s)). Qed.
Lemma lem3919458 {_99911 : Type'} (s : _99911 -> Prop) : (term1261 _99911 s) = (term1262 _99911 s).
Proof. exact (MK_COMB (@lem3919457 _99911 s) (@lem3919452 _99911 s)). Qed.
Lemma lem3919459 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919460 {_99911 : Type'} (s : _99911 -> Prop) : (term1263 _99911 s) = (term1264 _99911 s).
Proof. exact (MK_COMB (@lem3919459) (@lem3919458 _99911 s)). Qed.
Lemma lem3919461 {_99911 : Type'} (s : _99911 -> Prop) : (term1265 _99911 s) = (term1266 _99911 s).
Proof. exact (MK_COMB (@lem3919460 _99911 s) (@lem3919455 _99911 s)). Qed.
Lemma lem3919462 {_99911 : Type'} (s : _99911 -> Prop) : ((term1245 _99911 s) = (term1243 _99911 s)) = (term1265 _99911 s).
Proof. exact (@lem17784 (term1245 _99911 s) (term1243 _99911 s)). Qed.
Lemma lem3919463 {_99911 : Type'} (s : _99911 -> Prop) : ((term1245 _99911 s) = (term1243 _99911 s)) = (term1266 _99911 s).
Proof. exact (TRANS (@lem3919462 _99911 s) (@lem3919461 _99911 s)). Qed.
Lemma lem3919464 {_99911 : Type'} : (term1247 _99911) = (term1267 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919463 _99911 s)). Qed.
Lemma lem3919465 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919466 {_99911 : Type'} : (term1201 _99911) = (term1268 _99911).
Proof. exact (MK_COMB (@lem3919465 _99911) (@lem3919464 _99911)). Qed.
Lemma lem3919468 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term803 A P Q) = (term804 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3919469 {_99911 : Type'} (P : type686 _99911) (Q : type686 _99911) : (term1269 _99911 P Q) = (term1270 _99911 P Q).
Proof. exact (@lem3919468 (_99911 -> Prop) P Q). Qed.
Lemma lem3919470 {_99911 : Type'} : (term1271 _99911) = (term1272 _99911).
Proof. exact (@lem3919469 _99911 (term1273 _99911) (term1274 _99911)). Qed.
Lemma lem3919471 {_99911 : Type'} (s : _99911 -> Prop) : (term1275 _99911 s) = (term1262 _99911 s).
Proof. exact (eq_refl (term1275 _99911 s)). Qed.
Lemma lem3919472 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919473 {_99911 : Type'} (s : _99911 -> Prop) : (term1276 _99911 s) = (term1264 _99911 s).
Proof. exact (MK_COMB (@lem3919472) (@lem3919471 _99911 s)). Qed.
Lemma lem3919474 {_99911 : Type'} (s : _99911 -> Prop) : (term1277 _99911 s) = (term1259 _99911 s).
Proof. exact (eq_refl (term1277 _99911 s)). Qed.
Lemma lem3919475 {_99911 : Type'} (s : _99911 -> Prop) : (term1278 _99911 s) = (term1266 _99911 s).
Proof. exact (MK_COMB (@lem3919473 _99911 s) (@lem3919474 _99911 s)). Qed.
Lemma lem3919476 {_99911 : Type'} : (term1279 _99911) = (term1267 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919475 _99911 s)). Qed.
Lemma lem3919477 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919478 {_99911 : Type'} : (term1271 _99911) = (term1268 _99911).
Proof. exact (MK_COMB (@lem3919477 _99911) (@lem3919476 _99911)). Qed.
Lemma lem3919479 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919480 {_99911 : Type'} : (term1280 _99911) = (term1281 _99911).
Proof. exact (MK_COMB (@lem3919479) (@lem3919478 _99911)). Qed.
Lemma lem3919481 {_99911 : Type'} (s : _99911 -> Prop) : (term1275 _99911 s) = (term1262 _99911 s).
Proof. exact (eq_refl (term1275 _99911 s)). Qed.
Lemma lem3919482 {_99911 : Type'} : (term1282 _99911) = (term1273 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919481 _99911 s)). Qed.
Lemma lem3919483 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919484 {_99911 : Type'} : (term1283 _99911) = (term1284 _99911).
Proof. exact (MK_COMB (@lem3919483 _99911) (@lem3919482 _99911)). Qed.
Lemma lem3919485 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919486 {_99911 : Type'} : (term1285 _99911) = (term1286 _99911).
Proof. exact (MK_COMB (@lem3919485) (@lem3919484 _99911)). Qed.
Lemma lem3919487 {_99911 : Type'} (s : _99911 -> Prop) : (term1277 _99911 s) = (term1259 _99911 s).
Proof. exact (eq_refl (term1277 _99911 s)). Qed.
Lemma lem3919488 {_99911 : Type'} : (term1287 _99911) = (term1274 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919487 _99911 s)). Qed.
Lemma lem3919489 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919490 {_99911 : Type'} : (term1288 _99911) = (term1289 _99911).
Proof. exact (MK_COMB (@lem3919489 _99911) (@lem3919488 _99911)). Qed.
Lemma lem3919491 {_99911 : Type'} : (term1272 _99911) = (term1290 _99911).
Proof. exact (MK_COMB (@lem3919486 _99911) (@lem3919490 _99911)). Qed.
Lemma lem3919492 {_99911 : Type'} : ((term1271 _99911) = (term1272 _99911)) = ((term1268 _99911) = (term1290 _99911)).
Proof. exact (MK_COMB (@lem3919480 _99911) (@lem3919491 _99911)). Qed.
Lemma lem3919493 {_99911 : Type'} : (term1268 _99911) = (term1290 _99911).
Proof. exact (EQ_MP (@lem3919492 _99911) (@lem3919470 _99911)). Qed.
Lemma lem3919599 {A : Type'} (P : A -> Prop) (Q : Prop) : (term933 A P Q) = (term934 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3919600 {_99911 : Type'} (P : _99911 -> Prop) (Q : Prop) : (term933 _99911 P Q) = (term934 _99911 P Q).
Proof. exact (@lem3919599 _99911 P Q). Qed.
Lemma lem3919601 {_99911 : Type'} (s : _99911 -> Prop) : (term1291 _99911 s) = (term1292 _99911 s).
Proof. exact (@lem3919600 _99911 (term1244 _99911 s) (s = (@EMPTY _99911))). Qed.
Lemma lem3919602 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1250 _99911 s x) = (@IN _99911 x s).
Proof. exact (eq_refl (term1250 _99911 s x)). Qed.
Lemma lem3919603 {_99911 : Type'} (s : _99911 -> Prop) : (term1293 _99911 s) = (term1244 _99911 s).
Proof. exact (fun_ext (fun x : _99911 => @lem3919602 _99911 x s)). Qed.
Lemma lem3919604 {_99911 : Type'} : (@ex _99911) = (@ex _99911).
Proof. exact (eq_refl (@ex _99911)). Qed.
Lemma lem3919605 {_99911 : Type'} (s : _99911 -> Prop) : (term1294 _99911 s) = (term1245 _99911 s).
Proof. exact (MK_COMB (@lem3919604 _99911) (@lem3919603 _99911 s)). Qed.
Lemma lem3919606 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919607 {_99911 : Type'} (s : _99911 -> Prop) : (term1295 _99911 s) = (term1260 _99911 s).
Proof. exact (MK_COMB (@lem3919606) (@lem3919605 _99911 s)). Qed.
Lemma lem3919608 {_99911 : Type'} (s : _99911 -> Prop) : (s = (@EMPTY _99911)) = (s = (@EMPTY _99911)).
Proof. exact (eq_refl (s = (@EMPTY _99911))). Qed.
Lemma lem3919609 {_99911 : Type'} (s : _99911 -> Prop) : (term1291 _99911 s) = (term1262 _99911 s).
Proof. exact (MK_COMB (@lem3919607 _99911 s) (@lem3919608 _99911 s)). Qed.
Lemma lem3919610 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919611 {_99911 : Type'} (s : _99911 -> Prop) : (term1296 _99911 s) = (term1297 _99911 s).
Proof. exact (MK_COMB (@lem3919610) (@lem3919609 _99911 s)). Qed.
Lemma lem3919612 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1250 _99911 s x) = (@IN _99911 x s).
Proof. exact (eq_refl (term1250 _99911 s x)). Qed.
Lemma lem3919613 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919614 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1298 _99911 s x) = (term1299 _99911 x s).
Proof. exact (MK_COMB (@lem3919613) (@lem3919612 _99911 x s)). Qed.
Lemma lem3919615 {_99911 : Type'} (s : _99911 -> Prop) : (s = (@EMPTY _99911)) = (s = (@EMPTY _99911)).
Proof. exact (eq_refl (s = (@EMPTY _99911))). Qed.
Lemma lem3919616 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1300 _99911 x s) = (term1301 _99911 x s).
Proof. exact (MK_COMB (@lem3919614 _99911 x s) (@lem3919615 _99911 s)). Qed.
Lemma lem3919617 {_99911 : Type'} (s : _99911 -> Prop) : (term1302 _99911 s) = (term1303 _99911 s).
Proof. exact (fun_ext (fun x : _99911 => @lem3919616 _99911 x s)). Qed.
Lemma lem3919618 {_99911 : Type'} : (@ex _99911) = (@ex _99911).
Proof. exact (eq_refl (@ex _99911)). Qed.
Lemma lem3919619 {_99911 : Type'} (s : _99911 -> Prop) : (term1292 _99911 s) = (term1304 _99911 s).
Proof. exact (MK_COMB (@lem3919618 _99911) (@lem3919617 _99911 s)). Qed.
Lemma lem3919620 {_99911 : Type'} (s : _99911 -> Prop) : ((term1291 _99911 s) = (term1292 _99911 s)) = ((term1262 _99911 s) = (term1304 _99911 s)).
Proof. exact (MK_COMB (@lem3919611 _99911 s) (@lem3919619 _99911 s)). Qed.
Lemma lem3919621 {_99911 : Type'} (s : _99911 -> Prop) : (term1262 _99911 s) = (term1304 _99911 s).
Proof. exact (EQ_MP (@lem3919620 _99911 s) (@lem3919601 _99911 s)). Qed.
Lemma lem3919622 {_99911 : Type'} : (term1273 _99911) = (term1305 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919621 _99911 s)). Qed.
Lemma lem3919623 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919624 {_99911 : Type'} : (term1284 _99911) = (term1306 _99911).
Proof. exact (MK_COMB (@lem3919623 _99911) (@lem3919622 _99911)). Qed.
Lemma lem3919626 {A B : Type'} (P : type1413 A B) : (term873 A B P) = (term874 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3919627 {_99911 : Type'} (P : type672 _99911) : (term1307 _99911 P) = (term1308 _99911 P).
Proof. exact (@lem3919626 (_99911 -> Prop) _99911 P). Qed.
Lemma lem3919628 {_99911 : Type'} : (term1309 _99911) = (term1310 _99911).
Proof. exact (@lem3919627 _99911 (term1311 _99911)). Qed.
Lemma lem3919629 {_99911 : Type'} (s : _99911 -> Prop) : (term1312 _99911 s) = (term1303 _99911 s).
Proof. exact (eq_refl (term1312 _99911 s)). Qed.
Lemma lem3919630 {_99911 : Type'} (x : _99911) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3919631 {_99911 : Type'} (s : _99911 -> Prop) (x : _99911) : (term1313 _99911 s x) = (term1314 _99911 s x).
Proof. exact (MK_COMB (@lem3919629 _99911 s) (@lem3919630 _99911 x)). Qed.
Lemma lem3919632 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1314 _99911 s x) = (term1301 _99911 x s).
Proof. exact (eq_refl (term1314 _99911 s x)). Qed.
Lemma lem3919633 {_99911 : Type'} (x : _99911) (s : _99911 -> Prop) : (term1313 _99911 s x) = (term1301 _99911 x s).
Proof. exact (TRANS (@lem3919631 _99911 s x) (@lem3919632 _99911 x s)). Qed.
Lemma lem3919634 {_99911 : Type'} (s : _99911 -> Prop) : (term1315 _99911 s) = (term1303 _99911 s).
Proof. exact (fun_ext (fun x : _99911 => @lem3919633 _99911 x s)). Qed.
Lemma lem3919635 {_99911 : Type'} : (@ex _99911) = (@ex _99911).
Proof. exact (eq_refl (@ex _99911)). Qed.
Lemma lem3919636 {_99911 : Type'} (s : _99911 -> Prop) : (term1316 _99911 s) = (term1304 _99911 s).
Proof. exact (MK_COMB (@lem3919635 _99911) (@lem3919634 _99911 s)). Qed.
Lemma lem3919637 {_99911 : Type'} : (term1317 _99911) = (term1305 _99911).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919636 _99911 s)). Qed.
Lemma lem3919638 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919639 {_99911 : Type'} : (term1309 _99911) = (term1306 _99911).
Proof. exact (MK_COMB (@lem3919638 _99911) (@lem3919637 _99911)). Qed.
Lemma lem3919640 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919641 {_99911 : Type'} : (term1318 _99911) = (term1319 _99911).
Proof. exact (MK_COMB (@lem3919640) (@lem3919639 _99911)). Qed.
Lemma lem3919642 {_99911 : Type'} (s : _99911 -> Prop) : (term1312 _99911 s) = (term1303 _99911 s).
Proof. exact (eq_refl (term1312 _99911 s)). Qed.
Lemma lem3919643 {_99911 : Type'} (x : type684 _99911) (s : _99911 -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3919644 {_99911 : Type'} (x : type684 _99911) (s : _99911 -> Prop) : (term1320 _99911 x s) = (term1321 _99911 x s).
Proof. exact (MK_COMB (@lem3919642 _99911 s) (@lem3919643 _99911 x s)). Qed.
Lemma lem3919645 {_99911 : Type'} (x : type684 _99911) (s : _99911 -> Prop) : (term1321 _99911 x s) = (term1322 _99911 x s).
Proof. exact (eq_refl (term1321 _99911 x s)). Qed.
Lemma lem3919646 {_99911 : Type'} (x : type684 _99911) (s : _99911 -> Prop) : (term1320 _99911 x s) = (term1322 _99911 x s).
Proof. exact (TRANS (@lem3919644 _99911 x s) (@lem3919645 _99911 x s)). Qed.
Lemma lem3919647 {_99911 : Type'} (x : type684 _99911) : (term1323 _99911 x) = (term1324 _99911 x).
Proof. exact (fun_ext (fun s : _99911 -> Prop => @lem3919646 _99911 x s)). Qed.
Lemma lem3919648 {_99911 : Type'} : (@all (_99911 -> Prop)) = (@all (_99911 -> Prop)).
Proof. exact (eq_refl (@all (_99911 -> Prop))). Qed.
Lemma lem3919649 {_99911 : Type'} (x : type684 _99911) : (term1325 _99911 x) = (term1326 _99911 x).
Proof. exact (MK_COMB (@lem3919648 _99911) (@lem3919647 _99911 x)). Qed.
Lemma lem3919650 {_99911 : Type'} : (term1327 _99911) = (term1328 _99911).
Proof. exact (fun_ext (fun x : type684 _99911 => @lem3919649 _99911 x)). Qed.
Lemma lem3919651 {_99911 : Type'} : (@ex ((_99911 -> Prop) -> _99911)) = (@ex ((_99911 -> Prop) -> _99911)).
Proof. exact (eq_refl (@ex ((_99911 -> Prop) -> _99911))). Qed.
Lemma lem3919652 {_99911 : Type'} : (term1310 _99911) = (term1329 _99911).
Proof. exact (MK_COMB (@lem3919651 _99911) (@lem3919650 _99911)). Qed.
Lemma lem3919653 {_99911 : Type'} : ((term1309 _99911) = (term1310 _99911)) = ((term1306 _99911) = (term1329 _99911)).
Proof. exact (MK_COMB (@lem3919641 _99911) (@lem3919652 _99911)). Qed.
Lemma lem3919654 {_99911 : Type'} : (term1306 _99911) = (term1329 _99911).
Proof. exact (EQ_MP (@lem3919653 _99911) (@lem3919628 _99911)). Qed.
Lemma lem3919655 {_99911 : Type'} : (term1284 _99911) = (term1329 _99911).
Proof. exact (TRANS (@lem3919624 _99911) (@lem3919654 _99911)). Qed.
Lemma lem3919656 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919657 {_99911 : Type'} : (term1286 _99911) = (term1330 _99911).
Proof. exact (MK_COMB (@lem3919656) (@lem3919655 _99911)). Qed.
Lemma lem3919658 {_99911 : Type'} : (term1289 _99911) = (term1289 _99911).
Proof. exact (eq_refl (term1289 _99911)). Qed.
Lemma lem3919659 {_99911 : Type'} : (term1290 _99911) = (term1331 _99911).
Proof. exact (MK_COMB (@lem3919657 _99911) (@lem3919658 _99911)). Qed.
Lemma lem3919661 {A : Type'} (P : A -> Prop) (Q : Prop) : (term899 A P Q) = (term900 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3919662 {_99911 : Type'} (P : type162 _99911) (Q : Prop) : (term1332 _99911 P Q) = (term1333 _99911 P Q).
Proof. exact (@lem3919661 (type684 _99911) P Q). Qed.
Lemma lem3919663 {_99911 : Type'} : (term1334 _99911) = (term1335 _99911).
Proof. exact (@lem3919662 _99911 (term1328 _99911) (term1289 _99911)). Qed.
Lemma lem3919664 {_99911 : Type'} (x : type684 _99911) : (term1336 _99911 x) = (term1326 _99911 x).
Proof. exact (eq_refl (term1336 _99911 x)). Qed.
Lemma lem3919665 {_99911 : Type'} : (term1337 _99911) = (term1328 _99911).
Proof. exact (fun_ext (fun x : type684 _99911 => @lem3919664 _99911 x)). Qed.
Lemma lem3919666 {_99911 : Type'} : (@ex ((_99911 -> Prop) -> _99911)) = (@ex ((_99911 -> Prop) -> _99911)).
Proof. exact (eq_refl (@ex ((_99911 -> Prop) -> _99911))). Qed.
Lemma lem3919667 {_99911 : Type'} : (term1338 _99911) = (term1329 _99911).
Proof. exact (MK_COMB (@lem3919666 _99911) (@lem3919665 _99911)). Qed.
Lemma lem3919668 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919669 {_99911 : Type'} : (term1339 _99911) = (term1330 _99911).
Proof. exact (MK_COMB (@lem3919668) (@lem3919667 _99911)). Qed.
Lemma lem3919670 {_99911 : Type'} : (term1289 _99911) = (term1289 _99911).
Proof. exact (eq_refl (term1289 _99911)). Qed.
Lemma lem3919671 {_99911 : Type'} : (term1334 _99911) = (term1331 _99911).
Proof. exact (MK_COMB (@lem3919669 _99911) (@lem3919670 _99911)). Qed.
Lemma lem3919672 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919673 {_99911 : Type'} : (term1340 _99911) = (term1341 _99911).
Proof. exact (MK_COMB (@lem3919672) (@lem3919671 _99911)). Qed.
Lemma lem3919674 {_99911 : Type'} (x : type684 _99911) : (term1336 _99911 x) = (term1326 _99911 x).
Proof. exact (eq_refl (term1336 _99911 x)). Qed.
Lemma lem3919675 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919676 {_99911 : Type'} (x : type684 _99911) : (term1342 _99911 x) = (term1343 _99911 x).
Proof. exact (MK_COMB (@lem3919675) (@lem3919674 _99911 x)). Qed.
Lemma lem3919677 {_99911 : Type'} : (term1289 _99911) = (term1289 _99911).
Proof. exact (eq_refl (term1289 _99911)). Qed.
Lemma lem3919678 {_99911 : Type'} (x : type684 _99911) : (term1344 _99911 x) = (term1345 _99911 x).
Proof. exact (MK_COMB (@lem3919676 _99911 x) (@lem3919677 _99911)). Qed.
Lemma lem3919679 {_99911 : Type'} : (term1346 _99911) = (term1347 _99911).
Proof. exact (fun_ext (fun x : type684 _99911 => @lem3919678 _99911 x)). Qed.
Lemma lem3919680 {_99911 : Type'} : (@ex ((_99911 -> Prop) -> _99911)) = (@ex ((_99911 -> Prop) -> _99911)).
Proof. exact (eq_refl (@ex ((_99911 -> Prop) -> _99911))). Qed.
Lemma lem3919681 {_99911 : Type'} : (term1335 _99911) = (term1348 _99911).
Proof. exact (MK_COMB (@lem3919680 _99911) (@lem3919679 _99911)). Qed.
Lemma lem3919682 {_99911 : Type'} : ((term1334 _99911) = (term1335 _99911)) = ((term1331 _99911) = (term1348 _99911)).
Proof. exact (MK_COMB (@lem3919673 _99911) (@lem3919681 _99911)). Qed.
Lemma lem3919683 {_99911 : Type'} : (term1331 _99911) = (term1348 _99911).
Proof. exact (EQ_MP (@lem3919682 _99911) (@lem3919663 _99911)). Qed.
Lemma lem3919684 {_99911 : Type'} : (term1290 _99911) = (term1348 _99911).
Proof. exact (TRANS (@lem3919659 _99911) (@lem3919683 _99911)). Qed.
Lemma lem3919685 {_99911 : Type'} : (term1268 _99911) = (term1348 _99911).
Proof. exact (TRANS (@lem3919493 _99911) (@lem3919684 _99911)). Qed.
Lemma lem3919686 {_99911 : Type'} : (term1201 _99911) = (term1348 _99911).
Proof. exact (TRANS (@lem3919466 _99911) (@lem3919685 _99911)). Qed.
Lemma lem3919687 {_99911 : Type'} (h1 : term1201 _99911) : term1348 _99911.
Proof. exact (EQ_MP (@lem3919686 _99911) (@lem3919400 _99911 h1)). Qed.
Lemma lem3919689 {A : Type'} (x : A) (s : A -> Prop) : (@IN A x s) = (@IN A x s).
Proof. exact (eq_refl (@IN A x s)). Qed.
Lemma lem3919690 {A : Type'} (P : A -> Prop) : (term780 A P) = (term781 A P).
Proof. exact (@lem18394 A P). Qed.
Lemma lem3919691 {A : Type'} (s : A -> Prop) : (term1248 A s) = (term1249 A s).
Proof. exact (@lem3919690 A (term1244 A s)). Qed.
Lemma lem3919692 {A : Type'} (x : A) (s : A -> Prop) : (term1250 A s x) = (@IN A x s).
Proof. exact (eq_refl (term1250 A s x)). Qed.
Lemma lem3919693 : not = not.
Proof. exact (eq_refl not). Qed.
Lemma lem3919695 {A : Type'} (x : A) (s : A -> Prop) : (term1251 A s x) = (term687 A x s).
Proof. exact (MK_COMB (@lem3919693) (@lem3919692 A x s)). Qed.
Lemma lem3919696 {A : Type'} (s : A -> Prop) : (term1252 A s) = (term1253 A s).
Proof. exact (fun_ext (fun x : A => @lem3919695 A x s)). Qed.
Lemma lem3919697 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3919698 {A : Type'} (s : A -> Prop) : (term1249 A s) = (term1254 A s).
Proof. exact (MK_COMB (@lem3919697 A) (@lem3919696 A s)). Qed.
Lemma lem3919699 {A : Type'} (s : A -> Prop) : (term1248 A s) = (term1254 A s).
Proof. exact (TRANS (@lem3919691 A s) (@lem3919698 A s)). Qed.
Lemma lem3919700 {A : Type'} (s : A -> Prop) : (term1244 A s) = (term1244 A s).
Proof. exact (fun_ext (fun x : A => @lem3919689 A x s)). Qed.
Lemma lem3919701 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3919702 {A : Type'} (s : A -> Prop) : (term1245 A s) = (term1245 A s).
Proof. exact (MK_COMB (@lem3919701 A) (@lem3919700 A s)). Qed.
Lemma lem3919703 {A : Type'} (s : A -> Prop) : (term1243 A s) = (term1243 A s).
Proof. exact (eq_refl (term1243 A s)). Qed.
Lemma lem3919706 {A : Type'} (s : A -> Prop) : (term1255 A s) = (s = (@EMPTY A)).
Proof. exact (@lem16933 (s = (@EMPTY A))). Qed.
Lemma lem3919707 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919708 {A : Type'} (s : A -> Prop) : (term1256 A s) = (term1257 A s).
Proof. exact (MK_COMB (@lem3919707) (@lem3919699 A s)). Qed.
Lemma lem3919709 {A : Type'} (s : A -> Prop) : (term1258 A s) = (term1259 A s).
Proof. exact (MK_COMB (@lem3919708 A s) (@lem3919703 A s)). Qed.
Lemma lem3919710 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919711 {A : Type'} (s : A -> Prop) : (term1260 A s) = (term1260 A s).
Proof. exact (MK_COMB (@lem3919710) (@lem3919702 A s)). Qed.
Lemma lem3919712 {A : Type'} (s : A -> Prop) : (term1261 A s) = (term1262 A s).
Proof. exact (MK_COMB (@lem3919711 A s) (@lem3919706 A s)). Qed.
Lemma lem3919713 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919714 {A : Type'} (s : A -> Prop) : (term1263 A s) = (term1264 A s).
Proof. exact (MK_COMB (@lem3919713) (@lem3919712 A s)). Qed.
Lemma lem3919715 {A : Type'} (s : A -> Prop) : (term1265 A s) = (term1266 A s).
Proof. exact (MK_COMB (@lem3919714 A s) (@lem3919709 A s)). Qed.
Lemma lem3919716 {A : Type'} (s : A -> Prop) : ((term1245 A s) = (term1243 A s)) = (term1265 A s).
Proof. exact (@lem17784 (term1245 A s) (term1243 A s)). Qed.
Lemma lem3919717 {A : Type'} (s : A -> Prop) : ((term1245 A s) = (term1243 A s)) = (term1266 A s).
Proof. exact (TRANS (@lem3919716 A s) (@lem3919715 A s)). Qed.
Lemma lem3919718 {A : Type'} : (term1247 A) = (term1267 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919717 A s)). Qed.
Lemma lem3919719 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919720 {A : Type'} : (term1201 A) = (term1268 A).
Proof. exact (MK_COMB (@lem3919719 A) (@lem3919718 A)). Qed.
Lemma lem3919722 {A : Type'} (P : A -> Prop) (Q : A -> Prop) : (term803 A P Q) = (term804 A P Q).
Proof. exact (EQ_MP (@lem18953 A P Q) (@lem18952 A P Q)). Qed.
Lemma lem3919723 {A : Type'} (P : type686 A) (Q : type686 A) : (term1269 A P Q) = (term1270 A P Q).
Proof. exact (@lem3919722 (A -> Prop) P Q). Qed.
Lemma lem3919724 {A : Type'} : (term1271 A) = (term1272 A).
Proof. exact (@lem3919723 A (term1273 A) (term1274 A)). Qed.
Lemma lem3919725 {A : Type'} (s : A -> Prop) : (term1275 A s) = (term1262 A s).
Proof. exact (eq_refl (term1275 A s)). Qed.
Lemma lem3919726 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919727 {A : Type'} (s : A -> Prop) : (term1276 A s) = (term1264 A s).
Proof. exact (MK_COMB (@lem3919726) (@lem3919725 A s)). Qed.
Lemma lem3919728 {A : Type'} (s : A -> Prop) : (term1277 A s) = (term1259 A s).
Proof. exact (eq_refl (term1277 A s)). Qed.
Lemma lem3919729 {A : Type'} (s : A -> Prop) : (term1278 A s) = (term1266 A s).
Proof. exact (MK_COMB (@lem3919727 A s) (@lem3919728 A s)). Qed.
Lemma lem3919730 {A : Type'} : (term1279 A) = (term1267 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919729 A s)). Qed.
Lemma lem3919731 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919732 {A : Type'} : (term1271 A) = (term1268 A).
Proof. exact (MK_COMB (@lem3919731 A) (@lem3919730 A)). Qed.
Lemma lem3919733 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919734 {A : Type'} : (term1280 A) = (term1281 A).
Proof. exact (MK_COMB (@lem3919733) (@lem3919732 A)). Qed.
Lemma lem3919735 {A : Type'} (s : A -> Prop) : (term1275 A s) = (term1262 A s).
Proof. exact (eq_refl (term1275 A s)). Qed.
Lemma lem3919736 {A : Type'} : (term1282 A) = (term1273 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919735 A s)). Qed.
Lemma lem3919737 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919738 {A : Type'} : (term1283 A) = (term1284 A).
Proof. exact (MK_COMB (@lem3919737 A) (@lem3919736 A)). Qed.
Lemma lem3919739 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919740 {A : Type'} : (term1285 A) = (term1286 A).
Proof. exact (MK_COMB (@lem3919739) (@lem3919738 A)). Qed.
Lemma lem3919741 {A : Type'} (s : A -> Prop) : (term1277 A s) = (term1259 A s).
Proof. exact (eq_refl (term1277 A s)). Qed.
Lemma lem3919742 {A : Type'} : (term1287 A) = (term1274 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919741 A s)). Qed.
Lemma lem3919743 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919744 {A : Type'} : (term1288 A) = (term1289 A).
Proof. exact (MK_COMB (@lem3919743 A) (@lem3919742 A)). Qed.
Lemma lem3919745 {A : Type'} : (term1272 A) = (term1290 A).
Proof. exact (MK_COMB (@lem3919740 A) (@lem3919744 A)). Qed.
Lemma lem3919746 {A : Type'} : ((term1271 A) = (term1272 A)) = ((term1268 A) = (term1290 A)).
Proof. exact (MK_COMB (@lem3919734 A) (@lem3919745 A)). Qed.
Lemma lem3919747 {A : Type'} : (term1268 A) = (term1290 A).
Proof. exact (EQ_MP (@lem3919746 A) (@lem3919724 A)). Qed.
Lemma lem3919853 {A : Type'} (P : A -> Prop) (Q : Prop) : (term933 A P Q) = (term934 A P Q).
Proof. exact (EQ_MP (@lem18905 A P Q) (@lem18904 A P Q)). Qed.
Lemma lem3919854 {A : Type'} (P : A -> Prop) (Q : Prop) : (term933 A P Q) = (term934 A P Q).
Proof. exact (@lem3919853 A P Q). Qed.
Lemma lem3919855 {A : Type'} (s : A -> Prop) : (term1291 A s) = (term1292 A s).
Proof. exact (@lem3919854 A (term1244 A s) (s = (@EMPTY A))). Qed.
Lemma lem3919856 {A : Type'} (x : A) (s : A -> Prop) : (term1250 A s x) = (@IN A x s).
Proof. exact (eq_refl (term1250 A s x)). Qed.
Lemma lem3919857 {A : Type'} (s : A -> Prop) : (term1293 A s) = (term1244 A s).
Proof. exact (fun_ext (fun x : A => @lem3919856 A x s)). Qed.
Lemma lem3919858 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3919859 {A : Type'} (s : A -> Prop) : (term1294 A s) = (term1245 A s).
Proof. exact (MK_COMB (@lem3919858 A) (@lem3919857 A s)). Qed.
Lemma lem3919860 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919861 {A : Type'} (s : A -> Prop) : (term1295 A s) = (term1260 A s).
Proof. exact (MK_COMB (@lem3919860) (@lem3919859 A s)). Qed.
Lemma lem3919862 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem3919863 {A : Type'} (s : A -> Prop) : (term1291 A s) = (term1262 A s).
Proof. exact (MK_COMB (@lem3919861 A s) (@lem3919862 A s)). Qed.
Lemma lem3919864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919865 {A : Type'} (s : A -> Prop) : (term1296 A s) = (term1297 A s).
Proof. exact (MK_COMB (@lem3919864) (@lem3919863 A s)). Qed.
Lemma lem3919866 {A : Type'} (x : A) (s : A -> Prop) : (term1250 A s x) = (@IN A x s).
Proof. exact (eq_refl (term1250 A s x)). Qed.
Lemma lem3919867 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3919868 {A : Type'} (x : A) (s : A -> Prop) : (term1298 A s x) = (term1299 A x s).
Proof. exact (MK_COMB (@lem3919867) (@lem3919866 A x s)). Qed.
Lemma lem3919869 {A : Type'} (s : A -> Prop) : (s = (@EMPTY A)) = (s = (@EMPTY A)).
Proof. exact (eq_refl (s = (@EMPTY A))). Qed.
Lemma lem3919870 {A : Type'} (x : A) (s : A -> Prop) : (term1300 A x s) = (term1301 A x s).
Proof. exact (MK_COMB (@lem3919868 A x s) (@lem3919869 A s)). Qed.
Lemma lem3919871 {A : Type'} (s : A -> Prop) : (term1302 A s) = (term1303 A s).
Proof. exact (fun_ext (fun x : A => @lem3919870 A x s)). Qed.
Lemma lem3919872 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3919873 {A : Type'} (s : A -> Prop) : (term1292 A s) = (term1304 A s).
Proof. exact (MK_COMB (@lem3919872 A) (@lem3919871 A s)). Qed.
Lemma lem3919874 {A : Type'} (s : A -> Prop) : ((term1291 A s) = (term1292 A s)) = ((term1262 A s) = (term1304 A s)).
Proof. exact (MK_COMB (@lem3919865 A s) (@lem3919873 A s)). Qed.
Lemma lem3919875 {A : Type'} (s : A -> Prop) : (term1262 A s) = (term1304 A s).
Proof. exact (EQ_MP (@lem3919874 A s) (@lem3919855 A s)). Qed.
Lemma lem3919876 {A : Type'} : (term1273 A) = (term1305 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919875 A s)). Qed.
Lemma lem3919877 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919878 {A : Type'} : (term1284 A) = (term1306 A).
Proof. exact (MK_COMB (@lem3919877 A) (@lem3919876 A)). Qed.
Lemma lem3919880 {A B : Type'} (P : type1413 A B) : (term873 A B P) = (term874 A B P).
Proof. exact (EQ_MP (@lem18899 A B P) (@lem18898 A B P)). Qed.
Lemma lem3919881 {A : Type'} (P : type672 A) : (term1307 A P) = (term1308 A P).
Proof. exact (@lem3919880 (A -> Prop) A P). Qed.
Lemma lem3919882 {A : Type'} : (term1309 A) = (term1310 A).
Proof. exact (@lem3919881 A (term1311 A)). Qed.
Lemma lem3919883 {A : Type'} (s : A -> Prop) : (term1312 A s) = (term1303 A s).
Proof. exact (eq_refl (term1312 A s)). Qed.
Lemma lem3919884 {A : Type'} (x : A) : x = x.
Proof. exact (eq_refl x). Qed.
Lemma lem3919885 {A : Type'} (s : A -> Prop) (x : A) : (term1313 A s x) = (term1314 A s x).
Proof. exact (MK_COMB (@lem3919883 A s) (@lem3919884 A x)). Qed.
Lemma lem3919886 {A : Type'} (x : A) (s : A -> Prop) : (term1314 A s x) = (term1301 A x s).
Proof. exact (eq_refl (term1314 A s x)). Qed.
Lemma lem3919887 {A : Type'} (x : A) (s : A -> Prop) : (term1313 A s x) = (term1301 A x s).
Proof. exact (TRANS (@lem3919885 A s x) (@lem3919886 A x s)). Qed.
Lemma lem3919888 {A : Type'} (s : A -> Prop) : (term1315 A s) = (term1303 A s).
Proof. exact (fun_ext (fun x : A => @lem3919887 A x s)). Qed.
Lemma lem3919889 {A : Type'} : (@ex A) = (@ex A).
Proof. exact (eq_refl (@ex A)). Qed.
Lemma lem3919890 {A : Type'} (s : A -> Prop) : (term1316 A s) = (term1304 A s).
Proof. exact (MK_COMB (@lem3919889 A) (@lem3919888 A s)). Qed.
Lemma lem3919891 {A : Type'} : (term1317 A) = (term1305 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919890 A s)). Qed.
Lemma lem3919892 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919893 {A : Type'} : (term1309 A) = (term1306 A).
Proof. exact (MK_COMB (@lem3919892 A) (@lem3919891 A)). Qed.
Lemma lem3919894 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919895 {A : Type'} : (term1318 A) = (term1319 A).
Proof. exact (MK_COMB (@lem3919894) (@lem3919893 A)). Qed.
Lemma lem3919896 {A : Type'} (s : A -> Prop) : (term1312 A s) = (term1303 A s).
Proof. exact (eq_refl (term1312 A s)). Qed.
Lemma lem3919897 {A : Type'} (x : type684 A) (s : A -> Prop) : (x s) = (x s).
Proof. exact (eq_refl (x s)). Qed.
Lemma lem3919898 {A : Type'} (x : type684 A) (s : A -> Prop) : (term1320 A x s) = (term1321 A x s).
Proof. exact (MK_COMB (@lem3919896 A s) (@lem3919897 A x s)). Qed.
Lemma lem3919899 {A : Type'} (x : type684 A) (s : A -> Prop) : (term1321 A x s) = (term1322 A x s).
Proof. exact (eq_refl (term1321 A x s)). Qed.
Lemma lem3919900 {A : Type'} (x : type684 A) (s : A -> Prop) : (term1320 A x s) = (term1322 A x s).
Proof. exact (TRANS (@lem3919898 A x s) (@lem3919899 A x s)). Qed.
Lemma lem3919901 {A : Type'} (x : type684 A) : (term1323 A x) = (term1324 A x).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3919900 A x s)). Qed.
Lemma lem3919902 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3919903 {A : Type'} (x : type684 A) : (term1325 A x) = (term1326 A x).
Proof. exact (MK_COMB (@lem3919902 A) (@lem3919901 A x)). Qed.
Lemma lem3919904 {A : Type'} : (term1327 A) = (term1328 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3919903 A x)). Qed.
Lemma lem3919905 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3919906 {A : Type'} : (term1310 A) = (term1329 A).
Proof. exact (MK_COMB (@lem3919905 A) (@lem3919904 A)). Qed.
Lemma lem3919907 {A : Type'} : ((term1309 A) = (term1310 A)) = ((term1306 A) = (term1329 A)).
Proof. exact (MK_COMB (@lem3919895 A) (@lem3919906 A)). Qed.
Lemma lem3919908 {A : Type'} : (term1306 A) = (term1329 A).
Proof. exact (EQ_MP (@lem3919907 A) (@lem3919882 A)). Qed.
Lemma lem3919909 {A : Type'} : (term1284 A) = (term1329 A).
Proof. exact (TRANS (@lem3919878 A) (@lem3919908 A)). Qed.
Lemma lem3919910 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919911 {A : Type'} : (term1286 A) = (term1330 A).
Proof. exact (MK_COMB (@lem3919910) (@lem3919909 A)). Qed.
Lemma lem3919912 {A : Type'} : (term1289 A) = (term1289 A).
Proof. exact (eq_refl (term1289 A)). Qed.
Lemma lem3919913 {A : Type'} : (term1290 A) = (term1331 A).
Proof. exact (MK_COMB (@lem3919911 A) (@lem3919912 A)). Qed.
Lemma lem3919915 {A : Type'} (P : A -> Prop) (Q : Prop) : (term899 A P Q) = (term900 A P Q).
Proof. exact (EQ_MP (@lem18923 A P Q) (@lem18922 A P Q)). Qed.
Lemma lem3919916 {A : Type'} (P : type162 A) (Q : Prop) : (term1332 A P Q) = (term1333 A P Q).
Proof. exact (@lem3919915 (type684 A) P Q). Qed.
Lemma lem3919917 {A : Type'} : (term1334 A) = (term1335 A).
Proof. exact (@lem3919916 A (term1328 A) (term1289 A)). Qed.
Lemma lem3919918 {A : Type'} (x : type684 A) : (term1336 A x) = (term1326 A x).
Proof. exact (eq_refl (term1336 A x)). Qed.
Lemma lem3919919 {A : Type'} : (term1337 A) = (term1328 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3919918 A x)). Qed.
Lemma lem3919920 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3919921 {A : Type'} : (term1338 A) = (term1329 A).
Proof. exact (MK_COMB (@lem3919920 A) (@lem3919919 A)). Qed.
Lemma lem3919922 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919923 {A : Type'} : (term1339 A) = (term1330 A).
Proof. exact (MK_COMB (@lem3919922) (@lem3919921 A)). Qed.
Lemma lem3919924 {A : Type'} : (term1289 A) = (term1289 A).
Proof. exact (eq_refl (term1289 A)). Qed.
Lemma lem3919925 {A : Type'} : (term1334 A) = (term1331 A).
Proof. exact (MK_COMB (@lem3919923 A) (@lem3919924 A)). Qed.
Lemma lem3919926 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3919927 {A : Type'} : (term1340 A) = (term1341 A).
Proof. exact (MK_COMB (@lem3919926) (@lem3919925 A)). Qed.
Lemma lem3919928 {A : Type'} (x : type684 A) : (term1336 A x) = (term1326 A x).
Proof. exact (eq_refl (term1336 A x)). Qed.
Lemma lem3919929 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3919930 {A : Type'} (x : type684 A) : (term1342 A x) = (term1343 A x).
Proof. exact (MK_COMB (@lem3919929) (@lem3919928 A x)). Qed.
Lemma lem3919931 {A : Type'} : (term1289 A) = (term1289 A).
Proof. exact (eq_refl (term1289 A)). Qed.
Lemma lem3919932 {A : Type'} (x : type684 A) : (term1344 A x) = (term1345 A x).
Proof. exact (MK_COMB (@lem3919930 A x) (@lem3919931 A)). Qed.
Lemma lem3919933 {A : Type'} : (term1346 A) = (term1347 A).
Proof. exact (fun_ext (fun x : type684 A => @lem3919932 A x)). Qed.
Lemma lem3919934 {A : Type'} : (@ex ((A -> Prop) -> A)) = (@ex ((A -> Prop) -> A)).
Proof. exact (eq_refl (@ex ((A -> Prop) -> A))). Qed.
Lemma lem3919935 {A : Type'} : (term1335 A) = (term1348 A).
Proof. exact (MK_COMB (@lem3919934 A) (@lem3919933 A)). Qed.
Lemma lem3919936 {A : Type'} : ((term1334 A) = (term1335 A)) = ((term1331 A) = (term1348 A)).
Proof. exact (MK_COMB (@lem3919927 A) (@lem3919935 A)). Qed.
Lemma lem3919937 {A : Type'} : (term1331 A) = (term1348 A).
Proof. exact (EQ_MP (@lem3919936 A) (@lem3919917 A)). Qed.
Lemma lem3919938 {A : Type'} : (term1290 A) = (term1348 A).
Proof. exact (TRANS (@lem3919913 A) (@lem3919937 A)). Qed.
Lemma lem3919939 {A : Type'} : (term1268 A) = (term1348 A).
Proof. exact (TRANS (@lem3919747 A) (@lem3919938 A)). Qed.
Lemma lem3919940 {A : Type'} : (term1201 A) = (term1348 A).
Proof. exact (TRANS (@lem3919720 A) (@lem3919939 A)). Qed.
Lemma lem3919941 {A : Type'} (h1 : term1201 A) : term1348 A.
Proof. exact (EQ_MP (@lem3919940 A) (@lem3919401 A h1)). Qed.
Lemma lem3920034 {A : Type'} (s : A -> Prop) : (((@CARD A s) = (NUMERAL 0)) = (s = (@EMPTY A))) = (term1349 A s).
Proof. exact (@lem17784 ((@CARD A s) = (NUMERAL 0)) (s = (@EMPTY A))). Qed.
Lemma lem3920036 {A : Type'} (s : A -> Prop) : (term1350 A s) = (term1350 A s).
Proof. exact (eq_refl (term1350 A s)). Qed.
Lemma lem3920037 {A : Type'} (s : A -> Prop) : (term1351 A s) = (term1352 A s).
Proof. exact (MK_COMB (@lem3920036 A s) (@lem3920034 A s)). Qed.
Lemma lem3920038 {A : Type'} (s : A -> Prop) : (term1241 A s) = (term1351 A s).
Proof. exact (@lem17265 (@FINITE A s) (((@CARD A s) = (NUMERAL 0)) = (s = (@EMPTY A)))). Qed.
Lemma lem3920039 {A : Type'} (s : A -> Prop) : (term1241 A s) = (term1352 A s).
Proof. exact (TRANS (@lem3920038 A s) (@lem3920037 A s)). Qed.
Lemma lem3920040 {A : Type'} : (term1242 A) = (term1353 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3920039 A s)). Qed.
Lemma lem3920041 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3920094 {A : Type'} : (term1200 A) = (term1354 A).
Proof. exact (MK_COMB (@lem3920041 A) (@lem3920040 A)). Qed.
Lemma lem3920095 {A : Type'} (h1 : term1200 A) : term1354 A.
Proof. exact (EQ_MP (@lem3920094 A) (@lem3919403 A h1)). Qed.
Lemma lem3920096 {A : Type'} (x' : type684 A) (h1 : term1345 A x') : term1345 A x'.
Proof. exact (h1). Qed.
Lemma lem3920101 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3920107 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : @IN A x b.
Proof. exact (h1). Qed.
Lemma lem3920135 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : (@CARD A b) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3920237 {A : Type'} (s : A -> Prop) : (term1352 A s) = (term1352 A s).
Proof. exact (eq_refl (term1352 A s)). Qed.
Lemma lem3920238 {A : Type'} : (term1353 A) = (term1353 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3920237 A s)). Qed.
Lemma lem3920239 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3920240 {A : Type'} : (term1354 A) = (term1354 A).
Proof. exact (MK_COMB (@lem3920239 A) (@lem3920238 A)). Qed.
Lemma lem3920241 {A : Type'} (h1 : term1200 A) : term1354 A.
Proof. exact (EQ_MP (@lem3920240 A) (@lem3920095 A h1)). Qed.
Lemma lem3920248 {A : Type'} (s : A -> Prop) : (term1243 A s) = (term1243 A s).
Proof. exact (eq_refl (term1243 A s)). Qed.
Lemma lem3920255 {A : Type'} (x : A) (s : A -> Prop) : (term687 A x s) = (term687 A x s).
Proof. exact (eq_refl (term687 A x s)). Qed.
Lemma lem3920256 {A : Type'} (s : A -> Prop) : (term1253 A s) = (term1253 A s).
Proof. exact (fun_ext (fun x : A => @lem3920255 A x s)). Qed.
Lemma lem3920257 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3920258 {A : Type'} (s : A -> Prop) : (term1254 A s) = (term1254 A s).
Proof. exact (MK_COMB (@lem3920257 A) (@lem3920256 A s)). Qed.
Lemma lem3920259 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3920260 {A : Type'} (s : A -> Prop) : (term1257 A s) = (term1257 A s).
Proof. exact (MK_COMB (@lem3920259) (@lem3920258 A s)). Qed.
Lemma lem3920261 {A : Type'} (s : A -> Prop) : (term1259 A s) = (term1259 A s).
Proof. exact (MK_COMB (@lem3920260 A s) (@lem3920248 A s)). Qed.
Lemma lem3920262 {A : Type'} : (term1274 A) = (term1274 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3920261 A s)). Qed.
Lemma lem3920263 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3920264 {A : Type'} : (term1289 A) = (term1289 A).
Proof. exact (MK_COMB (@lem3920263 A) (@lem3920262 A)). Qed.
Lemma lem3920279 {A : Type'} (x' : type684 A) (s : A -> Prop) : (term1322 A x' s) = (term1322 A x' s).
Proof. exact (eq_refl (term1322 A x' s)). Qed.
Lemma lem3920280 {A : Type'} (x' : type684 A) : (term1324 A x') = (term1324 A x').
Proof. exact (fun_ext (fun s : A -> Prop => @lem3920279 A x' s)). Qed.
Lemma lem3920281 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3920282 {A : Type'} (x' : type684 A) : (term1326 A x') = (term1326 A x').
Proof. exact (MK_COMB (@lem3920281 A) (@lem3920280 A x')). Qed.
Lemma lem3920283 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3920284 {A : Type'} (x' : type684 A) : (term1343 A x') = (term1343 A x').
Proof. exact (MK_COMB (@lem3920283) (@lem3920282 A x')). Qed.
Lemma lem3920285 {A : Type'} (x' : type684 A) : (term1345 A x') = (term1345 A x').
Proof. exact (MK_COMB (@lem3920284 A x') (@lem3920264 A)). Qed.
Lemma lem3920286 {A : Type'} (x' : type684 A) (h1 : term1345 A x') : term1345 A x'.
Proof. exact (EQ_MP (@lem3920285 A x') (@lem3920096 A x' h1)). Qed.
Lemma lem3920334 {A : Type'} (x' : type684 A) (h1 : term1345 A x') : term1289 A.
Proof. exact (proj2 (@lem3920286 A x' h1)). Qed.
Lemma lem3920339 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3920343 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : @IN A x b.
Proof. exact (h1). Qed.
Lemma lem3920355 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : (@CARD A b) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3920420 {A : Type'} (s : A -> Prop) : (term1352 A s) = (term1355 A s).
Proof. exact (@lem19490 (term1356 A s) (term1357 A s) (term1358 A s)). Qed.
Lemma lem3920421 {A : Type'} : (term1353 A) = (term1359 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3920420 A s)). Qed.
Lemma lem3920422 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3920424 {A : Type'} : (term1354 A) = (term1360 A).
Proof. exact (MK_COMB (@lem3920422 A) (@lem3920421 A)). Qed.
Lemma lem3920425 {A : Type'} (h1 : term1200 A) : term1360 A.
Proof. exact (EQ_MP (@lem3920424 A) (@lem3920241 A h1)). Qed.
Lemma lem3920495 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1361 A P Q) = (term1362 A P Q).
Proof. exact (EQ_MP (@lem19013 A P Q) (@lem19012 A P Q)). Qed.
Lemma lem3920496 {A : Type'} (P : A -> Prop) (Q : Prop) : (term1361 A P Q) = (term1362 A P Q).
Proof. exact (@lem3920495 A P Q). Qed.
Lemma lem3920497 {A : Type'} (s : A -> Prop) : (term1363 A s) = (term1364 A s).
Proof. exact (@lem3920496 A (term1253 A s) (term1243 A s)). Qed.
Lemma lem3920498 {A : Type'} (x : A) (s : A -> Prop) : (term1365 A s x) = (term687 A x s).
Proof. exact (eq_refl (term1365 A s x)). Qed.
Lemma lem3920499 {A : Type'} (s : A -> Prop) : (term1366 A s) = (term1253 A s).
Proof. exact (fun_ext (fun x : A => @lem3920498 A x s)). Qed.
Lemma lem3920500 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3920501 {A : Type'} (s : A -> Prop) : (term1367 A s) = (term1254 A s).
Proof. exact (MK_COMB (@lem3920500 A) (@lem3920499 A s)). Qed.
Lemma lem3920502 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3920503 {A : Type'} (s : A -> Prop) : (term1368 A s) = (term1257 A s).
Proof. exact (MK_COMB (@lem3920502) (@lem3920501 A s)). Qed.
Lemma lem3920504 {A : Type'} (s : A -> Prop) : (term1243 A s) = (term1243 A s).
Proof. exact (eq_refl (term1243 A s)). Qed.
Lemma lem3920505 {A : Type'} (s : A -> Prop) : (term1363 A s) = (term1259 A s).
Proof. exact (MK_COMB (@lem3920503 A s) (@lem3920504 A s)). Qed.
Lemma lem3920506 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3920507 {A : Type'} (s : A -> Prop) : (term1369 A s) = (term1370 A s).
Proof. exact (MK_COMB (@lem3920506) (@lem3920505 A s)). Qed.
Lemma lem3920508 {A : Type'} (x : A) (s : A -> Prop) : (term1365 A s x) = (term687 A x s).
Proof. exact (eq_refl (term1365 A s x)). Qed.
Lemma lem3920509 : or = or.
Proof. exact (eq_refl or). Qed.
Lemma lem3920510 {A : Type'} (x : A) (s : A -> Prop) : (term1371 A s x) = (term1372 A x s).
Proof. exact (MK_COMB (@lem3920509) (@lem3920508 A x s)). Qed.
Lemma lem3920511 {A : Type'} (s : A -> Prop) : (term1243 A s) = (term1243 A s).
Proof. exact (eq_refl (term1243 A s)). Qed.
Lemma lem3920512 {A : Type'} (x : A) (s : A -> Prop) : (term1373 A x s) = (term1374 A x s).
Proof. exact (MK_COMB (@lem3920510 A x s) (@lem3920511 A s)). Qed.
Lemma lem3920513 {A : Type'} (s : A -> Prop) : (term1375 A s) = (term1376 A s).
Proof. exact (fun_ext (fun x : A => @lem3920512 A x s)). Qed.
Lemma lem3920514 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3920515 {A : Type'} (s : A -> Prop) : (term1364 A s) = (term1377 A s).
Proof. exact (MK_COMB (@lem3920514 A) (@lem3920513 A s)). Qed.
Lemma lem3920516 {A : Type'} (s : A -> Prop) : ((term1363 A s) = (term1364 A s)) = ((term1259 A s) = (term1377 A s)).
Proof. exact (MK_COMB (@lem3920507 A s) (@lem3920515 A s)). Qed.
Lemma lem3920517 {A : Type'} (s : A -> Prop) : (term1259 A s) = (term1377 A s).
Proof. exact (EQ_MP (@lem3920516 A s) (@lem3920497 A s)). Qed.
Lemma lem3920518 {A : Type'} : (term1274 A) = (term1378 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3920517 A s)). Qed.
Lemma lem3920519 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3920520 {A : Type'} : (term1289 A) = (term1379 A).
Proof. exact (MK_COMB (@lem3920519 A) (@lem3920518 A)). Qed.
Lemma lem3920527 {A : Type'} (x : A) (s : A -> Prop) : (term1374 A x s) = (term1374 A x s).
Proof. exact (eq_refl (term1374 A x s)). Qed.
Lemma lem3920528 {A : Type'} (s : A -> Prop) : (term1376 A s) = (term1376 A s).
Proof. exact (fun_ext (fun x : A => @lem3920527 A x s)). Qed.
Lemma lem3920529 {A : Type'} : (@all A) = (@all A).
Proof. exact (eq_refl (@all A)). Qed.
Lemma lem3920530 {A : Type'} (s : A -> Prop) : (term1377 A s) = (term1377 A s).
Proof. exact (MK_COMB (@lem3920529 A) (@lem3920528 A s)). Qed.
Lemma lem3920531 {A : Type'} : (term1378 A) = (term1378 A).
Proof. exact (fun_ext (fun s : A -> Prop => @lem3920530 A s)). Qed.
Lemma lem3920532 {A : Type'} : (@all (A -> Prop)) = (@all (A -> Prop)).
Proof. exact (eq_refl (@all (A -> Prop))). Qed.
Lemma lem3920533 {A : Type'} : (term1379 A) = (term1379 A).
Proof. exact (MK_COMB (@lem3920532 A) (@lem3920531 A)). Qed.
Lemma lem3920534 {A : Type'} : (term1289 A) = (term1379 A).
Proof. exact (TRANS (@lem3920520 A) (@lem3920533 A)). Qed.
Lemma lem3920535 {A : Type'} (x' : type684 A) (h1 : term1345 A x') : term1379 A.
Proof. exact (EQ_MP (@lem3920534 A) (@lem3920334 A x' h1)). Qed.
Lemma lem3920539 {A : Type'} (_45487 : A -> Prop) (h1 : term1200 A) : term1380 A _45487.
Proof. exact (@lem3920425 A h1 _45487). Qed.
Lemma lem3920540 {A : Type'} (_45487 : A -> Prop) : (term1380 A _45487) = (term1355 A _45487).
Proof. exact (eq_refl (term1380 A _45487)). Qed.
Lemma lem3920541 {A : Type'} (_45487 : A -> Prop) (h1 : term1200 A) : term1355 A _45487.
Proof. exact (EQ_MP (@lem3920540 A _45487) (@lem3920539 A _45487 h1)). Qed.
Lemma lem3920554 {A : Type'} (_45492 : A -> Prop) (x' : type684 A) (h1 : term1345 A x') : term1381 A _45492.
Proof. exact (@lem3920535 A x' h1 _45492). Qed.
Lemma lem3920555 {A : Type'} (_45492 : A -> Prop) : (term1381 A _45492) = (term1377 A _45492).
Proof. exact (eq_refl (term1381 A _45492)). Qed.
Lemma lem3920556 {A : Type'} (_45492 : A -> Prop) (x' : type684 A) (h1 : term1345 A x') : term1377 A _45492.
Proof. exact (EQ_MP (@lem3920555 A _45492) (@lem3920554 A _45492 x' h1)). Qed.
Lemma lem3920557 {A : Type'} (_45492 : A -> Prop) (_45493 : A) (x' : type684 A) (h1 : term1345 A x') : term1382 A _45492 _45493.
Proof. exact (@lem3920556 A _45492 x' h1 _45493). Qed.
Lemma lem3920558 {A : Type'} (_45493 : A) (_45492 : A -> Prop) : (term1382 A _45492 _45493) = (term1374 A _45493 _45492).
Proof. exact (eq_refl (term1382 A _45492 _45493)). Qed.
Lemma lem3920565 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3920567 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : @IN A x b.
Proof. exact (h1). Qed.
Lemma lem3920573 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : (@CARD A b) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3920597 {A : Type'} (_45493 : A) (_45492 : A -> Prop) (x' : type684 A) (h1 : term1345 A x') : term1374 A _45493 _45492.
Proof. exact (EQ_MP (@lem3920558 A _45493 _45492) (@lem3920557 A _45492 _45493 x' h1)). Qed.
Lemma lem3920617 {A : Type'} (_45487 : A -> Prop) (h1 : term1200 A) : term1383 A _45487.
Proof. exact (proj2 (@lem3920541 A _45487 h1)). Qed.
Lemma lem3920785 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : @IN A x b.
Proof. exact (h1). Qed.
Lemma lem3920786 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : term1384 A x b.
Proof. exact (fun h0 : term687 A x b => @lem3920785 A x b h1). Qed.
Lemma lem3920788 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3920789 {A : Type'} (x : A) (b : A -> Prop) : (term1384 A x b) = (@IN A x b).
Proof. exact (@lem3920788 (@IN A x b)). Qed.
Lemma lem3920790 {A : Type'} (x : A) (b : A -> Prop) (h1 : @IN A x b) : @IN A x b.
Proof. exact (EQ_MP (@lem3920789 A x b) (@lem3920786 A x b h1)). Qed.
Lemma lem3920792 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (h1). Qed.
Lemma lem3920793 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : term1385 A b.
Proof. exact (fun h0 : term1357 A b => @lem3920792 A b h1). Qed.
Lemma lem3920795 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3920796 {A : Type'} (b : A -> Prop) : (term1385 A b) = (@FINITE A b).
Proof. exact (@lem3920795 (@FINITE A b)). Qed.
Lemma lem3920797 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) : @FINITE A b.
Proof. exact (EQ_MP (@lem3920796 A b) (@lem3920793 A b h1)). Qed.
Lemma lem3920799 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : (@CARD A b) = (NUMERAL 0).
Proof. exact (h1). Qed.
Lemma lem3920800 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : term1386 A b.
Proof. exact (fun h0 : term1199 A b => @lem3920799 A b h1). Qed.
Lemma lem3920802 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3920803 {A : Type'} (b : A -> Prop) : (term1386 A b) = ((@CARD A b) = (NUMERAL 0)).
Proof. exact (@lem3920802 ((@CARD A b) = (NUMERAL 0))). Qed.
Lemma lem3920804 {A : Type'} (b : A -> Prop) (h1 : (@CARD A b) = (NUMERAL 0)) : (@CARD A b) = (NUMERAL 0).
Proof. exact (EQ_MP (@lem3920803 A b) (@lem3920800 A b h1)). Qed.
Lemma lem3920810 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3920811 {A : Type'} (_45487 : A -> Prop) : (term1383 A _45487) = (term1387 A _45487).
Proof. exact (@lem3920810 (term1199 A _45487) (term1357 A _45487) (_45487 = (@EMPTY A))). Qed.
Lemma lem3920827 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3920828 {A : Type'} (_45487 : A -> Prop) : (term1388 A _45487) = (term1389 A _45487).
Proof. exact (@lem3920827 (_45487 = (@EMPTY A)) (term1357 A _45487)). Qed.
Lemma lem3920836 {A : Type'} (_45487 : A -> Prop) : (term1390 A _45487) = (term1390 A _45487).
Proof. exact (eq_refl (term1390 A _45487)). Qed.
Lemma lem3920837 {A : Type'} (_45487 : A -> Prop) : (term1387 A _45487) = (term1391 A _45487).
Proof. exact (MK_COMB (@lem3920836 A _45487) (@lem3920828 A _45487)). Qed.
Lemma lem3920841 (q : Prop) (p : Prop) (r : Prop) : (term1066 p q r) = (term1066 q p r).
Proof. exact (proj1 (@lem20668 r p q)). Qed.
Lemma lem3920842 {A : Type'} (_45487 : A -> Prop) : (term1391 A _45487) = (term1392 A _45487).
Proof. exact (@lem3920841 (_45487 = (@EMPTY A)) (term1199 A _45487) (term1357 A _45487)). Qed.
Lemma lem3920862 {A : Type'} (_45487 : A -> Prop) : (term1387 A _45487) = (term1392 A _45487).
Proof. exact (TRANS (@lem3920837 A _45487) (@lem3920842 A _45487)). Qed.
Lemma lem3920863 {A : Type'} (_45487 : A -> Prop) : (term1383 A _45487) = (term1392 A _45487).
Proof. exact (TRANS (@lem3920811 A _45487) (@lem3920862 A _45487)). Qed.
Lemma lem3920864 : (@eq Prop) = (@eq Prop).
Proof. exact (eq_refl (@eq Prop)). Qed.
Lemma lem3920865 {A : Type'} (_45487 : A -> Prop) : (term1393 A _45487) = (term1394 A _45487).
Proof. exact (MK_COMB (@lem3920864) (@lem3920863 A _45487)). Qed.
Lemma lem3920881 (q : Prop) (p : Prop) : (p \/ q) = (q \/ p).
Proof. exact (proj1 (@lem827 (@el Prop) p q)). Qed.
Lemma lem3920882 {A : Type'} (_45487 : A -> Prop) : (term1395 A _45487) = (term1396 A _45487).
Proof. exact (@lem3920881 (term1199 A _45487) (term1357 A _45487)). Qed.
Lemma lem3920890 {A : Type'} (_45487 : A -> Prop) : (term1397 A _45487) = (term1397 A _45487).
Proof. exact (eq_refl (term1397 A _45487)). Qed.
Lemma lem3920891 {A : Type'} (_45487 : A -> Prop) : (term1398 A _45487) = (term1392 A _45487).
Proof. exact (MK_COMB (@lem3920890 A _45487) (@lem3920882 A _45487)). Qed.
Lemma lem3920902 {A : Type'} (_45487 : A -> Prop) : ((term1383 A _45487) = (term1398 A _45487)) = ((term1392 A _45487) = (term1392 A _45487)).
Proof. exact (MK_COMB (@lem3920865 A _45487) (@lem3920891 A _45487)). Qed.
Lemma lem3920904 {A : Type'} (x : A) : (x = x) = True.
Proof. exact (EQ_MP (@lem20665 A x) (@lem20664 A x)). Qed.
Lemma lem3920905 (x : Prop) : (x = x) = True.
Proof. exact (@lem3920904 Prop x). Qed.
Lemma lem3920906 {A : Type'} (_45487 : A -> Prop) : ((term1392 A _45487) = (term1392 A _45487)) = True.
Proof. exact (@lem3920905 (term1392 A _45487)). Qed.
Lemma lem3920907 {A : Type'} (_45487 : A -> Prop) : ((term1383 A _45487) = (term1398 A _45487)) = True.
Proof. exact (TRANS (@lem3920902 A _45487) (@lem3920906 A _45487)). Qed.
Lemma lem3920908 {A : Type'} (_45487 : A -> Prop) : True = ((term1383 A _45487) = (term1398 A _45487)).
Proof. exact (SYM (@lem3920907 A _45487)). Qed.
Lemma lem3920909 {A : Type'} (_45487 : A -> Prop) : (term1383 A _45487) = (term1398 A _45487).
Proof. exact (EQ_MP (@lem3920908 A _45487) (@lem0)). Qed.
Lemma lem3920910 {A : Type'} (_45487 : A -> Prop) (h1 : term1200 A) : term1398 A _45487.
Proof. exact (EQ_MP (@lem3920909 A _45487) (@lem3920617 A _45487 h1)). Qed.
Lemma lem3920912 (b : Prop) (a : Prop) : (a \/ b) = (term1076 b a).
Proof. exact (EQ_MP (@lem20682 b a) (@lem20764 b a)). Qed.
Lemma lem3920913 {A : Type'} (_45487 : A -> Prop) : (term1398 A _45487) = (term1399 A _45487).
Proof. exact (@lem3920912 (term1395 A _45487) (_45487 = (@EMPTY A))). Qed.
Lemma lem3920915 (a : Prop) (b : Prop) : (term1078 a b) = (term1079 a b).
Proof. exact (EQ_MP (@lem20789 a b) (@lem20895 a b)). Qed.
Lemma lem3920916 {A : Type'} (_45487 : A -> Prop) : (term1400 A _45487) = (term1401 A _45487).
Proof. exact (@lem3920915 (term1357 A _45487) (term1199 A _45487)). Qed.
Lemma lem3920918 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3920919 {A : Type'} (_45487 : A -> Prop) : (term1402 A _45487) = (@FINITE A _45487).
Proof. exact (@lem3920918 (@FINITE A _45487)). Qed.
Lemma lem3920920 : and = and.
Proof. exact (eq_refl and). Qed.
Lemma lem3920921 {A : Type'} (_45487 : A -> Prop) : (term1403 A _45487) = (term1404 A _45487).
Proof. exact (MK_COMB (@lem3920920) (@lem3920919 A _45487)). Qed.
Lemma lem3920923 (a : Prop) : (term190 a) = a.
Proof. exact (EQ_MP (@lem20780 a) (@lem0)). Qed.
Lemma lem3920924 {A : Type'} (_45487 : A -> Prop) : (term1405 A _45487) = ((@CARD A _45487) = (NUMERAL 0)).
Proof. exact (@lem3920923 ((@CARD A _45487) = (NUMERAL 0))). Qed.
Lemma lem3920925 {A : Type'} (_45487 : A -> Prop) : (term1401 A _45487) = (term1406 A _45487).
Proof. exact (MK_COMB (@lem3920921 A _45487) (@lem3920924 A _45487)). Qed.
Lemma lem3920926 {A : Type'} (_45487 : A -> Prop) : (term1400 A _45487) = (term1406 A _45487).
Proof. exact (TRANS (@lem3920916 A _45487) (@lem3920925 A _45487)). Qed.
Lemma lem3920927 : imp = imp.
Proof. exact (eq_refl imp). Qed.
Lemma lem3920928 {A : Type'} (_45487 : A -> Prop) : (term1407 A _45487) = (term1408 A _45487).
Proof. exact (MK_COMB (@lem3920927) (@lem3920926 A _45487)). Qed.
Lemma lem3920929 {A : Type'} (_45487 : A -> Prop) : (_45487 = (@EMPTY A)) = (_45487 = (@EMPTY A)).
Proof. exact (eq_refl (_45487 = (@EMPTY A))). Qed.
Lemma lem3920930 {A : Type'} (_45487 : A -> Prop) : (term1399 A _45487) = (term1409 A _45487).
Proof. exact (MK_COMB (@lem3920928 A _45487) (@lem3920929 A _45487)). Qed.
Lemma lem3920931 {A : Type'} (_45487 : A -> Prop) : (term1398 A _45487) = (term1409 A _45487).
Proof. exact (TRANS (@lem3920913 A _45487) (@lem3920930 A _45487)). Qed.
Lemma lem3920933 {A : Type'} (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A b) = (NUMERAL 0)) : term1406 A b.
Proof. exact (conj (@lem3920797 A b h1) (@lem3920804 A b h2)). Qed.
Lemma lem3920935 {A : Type'} (_45487 : A -> Prop) (h1 : term1200 A) : term1409 A _45487.
Proof. exact (EQ_MP (@lem3920931 A _45487) (@lem3920910 A _45487 h1)). Qed.
Lemma lem3920936 {A : Type'} (_45487 : A -> Prop) (h1 : term1200 A) : term1409 A _45487.
Proof. exact (@lem3920935 A _45487 h1). Qed.
Lemma lem3920937 {A : Type'} (b : A -> Prop) (h1 : term1200 A) : term1409 A b.
Proof. exact (@lem3920936 A b h1). Qed.
Lemma lem3920940 {A : Type'} (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : (@CARD A b) = (NUMERAL 0)) : b = (@EMPTY A).
Proof. exact (@lem3920937 A b h1 (@lem3920933 A b h2 h3)). Qed.
Lemma lem3920941 {A : Type'} (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : (@CARD A b) = (NUMERAL 0)) : term1410 A b.
Proof. exact (fun h0 : term1243 A b => @lem3920940 A b h1 h2 h3). Qed.
Lemma lem3920943 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3920944 {A : Type'} (b : A -> Prop) : (term1410 A b) = (b = (@EMPTY A)).
Proof. exact (@lem3920943 (b = (@EMPTY A))). Qed.
Lemma lem3920945 {A : Type'} (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : (@CARD A b) = (NUMERAL 0)) : b = (@EMPTY A).
Proof. exact (EQ_MP (@lem3920944 A b) (@lem3920941 A b h1 h2 h3)). Qed.
Lemma lem3920947 (a : Prop) (b : Prop) : (term1411 a b) = (term1412 a b).
Proof. exact (EQ_MP (@lem20904 a b) (@lem21007 a b)). Qed.
Lemma lem3920948 {A : Type'} (_45493 : A) (_45492 : A -> Prop) : (term1374 A _45493 _45492) = (term1413 A _45493 _45492).
Proof. exact (@lem3920947 (@IN A _45493 _45492) (_45492 = (@EMPTY A))). Qed.
Lemma lem3920950 (p : Prop) : (~ p) = (p -> False).
Proof. exact (EQ_MP (@lem21021 p) (@lem0)). Qed.
Lemma lem3920951 {A : Type'} (_45493 : A) (_45492 : A -> Prop) : (term1413 A _45493 _45492) = (term1414 A _45493 _45492).
Proof. exact (@lem3920950 (term1415 A _45493 _45492)). Qed.
Lemma lem3920952 {A : Type'} (_45493 : A) (_45492 : A -> Prop) : (term1374 A _45493 _45492) = (term1414 A _45493 _45492).
Proof. exact (TRANS (@lem3920948 A _45493 _45492) (@lem3920951 A _45493 _45492)). Qed.
Lemma lem3920954 {A : Type'} (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) : term1415 A x b.
Proof. exact (conj (@lem3920790 A x b h4) (@lem3920945 A b h1 h2 h3)). Qed.
Lemma lem3920956 {A : Type'} (_45493 : A) (_45492 : A -> Prop) (x' : type684 A) (h1 : term1345 A x') : term1414 A _45493 _45492.
Proof. exact (EQ_MP (@lem3920952 A _45493 _45492) (@lem3920597 A _45493 _45492 x' h1)). Qed.
Lemma lem3920957 {A : Type'} (_45493 : A) (_45492 : A -> Prop) (x' : type684 A) (h1 : term1345 A x') : term1414 A _45493 _45492.
Proof. exact (@lem3920956 A _45493 _45492 x' h1). Qed.
Lemma lem3920958 {A : Type'} (x : A) (b : A -> Prop) (x' : type684 A) (h1 : term1345 A x') : term1414 A x b.
Proof. exact (@lem3920957 A x b x' h1). Qed.
Lemma lem3920961 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (@lem3920958 A x b x' h3 (@lem3920954 A x b h1 h2 h4 h5)). Qed.
Lemma lem3920962 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : term1057.
Proof. exact (fun h0 : ~ False => @lem3920961 A x' x b h1 h2 h3 h4 h5). Qed.
Lemma lem3920964 (p : Prop) : (term1055 p) = p.
Proof. exact (EQ_MP (@lem21114 p) (@lem21182 p)). Qed.
Lemma lem3920965 : term1057 = False.
Proof. exact (@lem3920964 False). Qed.
Lemma lem3920966 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920965) (@lem3920962 A x' x b h1 h2 h3 h4 h5)). Qed.
Lemma lem3920967 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : ((@CARD A b) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : (@CARD A b) = (NUMERAL 0) => @lem3920966 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920573 A b h4)). Qed.
Lemma lem3920968 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920967 A x' x b h1 h2 h3 h4 h5) (@lem3920573 A b h4)). Qed.
Lemma lem3920969 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@IN A x b) = False.
Proof. exact (prop_ext (fun h6 : @IN A x b => @lem3920968 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920567 A x b h5)). Qed.
Lemma lem3920970 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920969 A x' x b h1 h2 h3 h4 h5) (@lem3920567 A x b h5)). Qed.
Lemma lem3920971 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A b => @lem3920970 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920565 A b h2)). Qed.
Lemma lem3920972 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920971 A x' x b h1 h2 h3 h4 h5) (@lem3920565 A b h2)). Qed.
Lemma lem3920973 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : ((@CARD A b) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : (@CARD A b) = (NUMERAL 0) => @lem3920972 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920355 A b h4)). Qed.
Lemma lem3920974 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920973 A x' x b h1 h2 h3 h4 h5) (@lem3920355 A b h4)). Qed.
Lemma lem3920975 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@IN A x b) = False.
Proof. exact (prop_ext (fun h6 : @IN A x b => @lem3920974 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920343 A x b h5)). Qed.
Lemma lem3920976 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920975 A x' x b h1 h2 h3 h4 h5) (@lem3920343 A x b h5)). Qed.
Lemma lem3920977 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A b => @lem3920976 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920339 A b h2)). Qed.
Lemma lem3920978 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920977 A x' x b h1 h2 h3 h4 h5) (@lem3920339 A b h2)). Qed.
Lemma lem3920979 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : ((@CARD A b) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : (@CARD A b) = (NUMERAL 0) => @lem3920978 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920355 A b h4)). Qed.
Lemma lem3920980 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920979 A x' x b h1 h2 h3 h4 h5) (@lem3920355 A b h4)). Qed.
Lemma lem3920981 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@IN A x b) = False.
Proof. exact (prop_ext (fun h6 : @IN A x b => @lem3920980 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920343 A x b h5)). Qed.
Lemma lem3920982 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920981 A x' x b h1 h2 h3 h4 h5) (@lem3920343 A x b h5)). Qed.
Lemma lem3920983 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A b => @lem3920982 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920339 A b h2)). Qed.
Lemma lem3920984 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920983 A x' x b h1 h2 h3 h4 h5) (@lem3920339 A b h2)). Qed.
Lemma lem3920985 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (term1345 A x') = False.
Proof. exact (prop_ext (fun h6 : term1345 A x' => @lem3920984 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920286 A x' h3)). Qed.
Lemma lem3920986 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920985 A x' x b h1 h2 h3 h4 h5) (@lem3920286 A x' h3)). Qed.
Lemma lem3920987 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : ((@CARD A b) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : (@CARD A b) = (NUMERAL 0) => @lem3920986 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920135 A b h4)). Qed.
Lemma lem3920988 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920987 A x' x b h1 h2 h3 h4 h5) (@lem3920135 A b h4)). Qed.
Lemma lem3920989 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@IN A x b) = False.
Proof. exact (prop_ext (fun h6 : @IN A x b => @lem3920988 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920107 A x b h5)). Qed.
Lemma lem3920990 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920989 A x' x b h1 h2 h3 h4 h5) (@lem3920107 A x b h5)). Qed.
Lemma lem3920991 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h6 : @FINITE A b => @lem3920990 A x' x b h1 h2 h3 h4 h5) (fun h6 : False => @lem3920101 A b h2)). Qed.
Lemma lem3920992 {A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1200 A) (h2 : @FINITE A b) (h3 : term1345 A x') (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920991 A x' x b h1 h2 h3 h4 h5) (@lem3920101 A b h2)). Qed.
Lemma lem3920993 {_99911 A : Type'} (x' : type684 A) (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1200 A) (h3 : @FINITE A b) (h4 : term1345 A x') (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : False.
Proof. exact (ex_elim (@lem3919687 _99911 h1) (fun x'' : type684 _99911 => fun h0 : term1347 _99911 x'' => @lem3920992 A x' x b h2 h3 h4 h5 h6)). Qed.
Lemma lem3920994 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : term1200 A) (h4 : @FINITE A b) (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : False.
Proof. exact (ex_elim (@lem3919941 A h2) (fun x' : type684 A => fun h0 : term1347 A x' => @lem3920993 _99911 A x' x b h1 h3 h4 h0 h5 h6)). Qed.
Lemma lem3920995 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : term1200 A) (h4 : @FINITE A b) (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : ((@CARD A b) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h7 : (@CARD A b) = (NUMERAL 0) => @lem3920994 _99911 A x b h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3919433 A b h5)). Qed.
Lemma lem3920996 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : term1200 A) (h4 : @FINITE A b) (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920995 _99911 A x b h1 h2 h3 h4 h5 h6) (@lem3919433 A b h5)). Qed.
Lemma lem3920997 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : term1200 A) (h4 : @FINITE A b) (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : (@IN A x b) = False.
Proof. exact (prop_ext (fun h7 : @IN A x b => @lem3920996 _99911 A x b h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3919415 A x b h6)). Qed.
Lemma lem3920998 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : term1200 A) (h4 : @FINITE A b) (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920997 _99911 A x b h1 h2 h3 h4 h5 h6) (@lem3919415 A x b h6)). Qed.
Lemma lem3920999 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : term1200 A) (h4 : @FINITE A b) (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : (@FINITE A b) = False.
Proof. exact (prop_ext (fun h7 : @FINITE A b => @lem3920998 _99911 A x b h1 h2 h3 h4 h5 h6) (fun h7 : False => @lem3919409 A b h4)). Qed.
Lemma lem3921000 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : term1200 A) (h4 : @FINITE A b) (h5 : (@CARD A b) = (NUMERAL 0)) (h6 : @IN A x b) : False.
Proof. exact (EQ_MP (@lem3920999 _99911 A x b h1 h2 h3 h4 h5 h6) (@lem3919409 A b h4)). Qed.
Lemma lem3921001 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : @FINITE A b) (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : term1206 A.
Proof. exact (fun h0 : term1200 A => @lem3921000 _99911 A x b h1 h2 h0 h3 h4 h5). Qed.
Lemma lem3921002 {A : Type'} : (term1206 A) = (term1207 A).
Proof. exact (@lem69 (term1200 A)). Qed.
Lemma lem3921003 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : @FINITE A b) (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : term1207 A.
Proof. exact (EQ_MP (@lem3921002 A) (@lem3921001 _99911 A x b h1 h2 h3 h4 h5)). Qed.
Lemma lem3921004 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : term1201 A) (h3 : @FINITE A b) (h4 : (@CARD A b) = (NUMERAL 0)) (h5 : @IN A x b) : term1210 _99911 A.
Proof. exact (fun h0 : term1200 _99911 => @lem3921003 _99911 A x b h1 h2 h3 h4 h5). Qed.
Lemma lem3921005 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : term1201 _99911) (h2 : @FINITE A b) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) : term1213 _99911 A.
Proof. exact (fun h0 : term1201 A => @lem3921004 _99911 A x b h1 h0 h2 h3 h4). Qed.
Lemma lem3921006 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : (@CARD A b) = (NUMERAL 0)) (h3 : @IN A x b) : term1215 _99911 A.
Proof. exact (fun h0 : term1201 _99911 => @lem3921005 _99911 A x b h0 h1 h2 h3). Qed.
Lemma lem3921007 {_99911 A : Type'} (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : term1218 _99911 A b.
Proof. exact (fun h0 : (@CARD A b) = (NUMERAL 0) => @lem3921006 _99911 A x b h1 h0 h2). Qed.
Lemma lem3921008 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : term1221 _99911 A a x b.
Proof. exact (fun h0 : term658 A a b x => @lem3921007 _99911 A x b h1 h2). Qed.
Lemma lem3921009 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : term1224 _99911 A a x b.
Proof. exact (fun h0 : term687 A x a => @lem3921008 _99911 A a x b h1 h2). Qed.
Lemma lem3921010 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) : term1226 _99911 A a x b.
Proof. exact (fun h0 : @IN A x b => @lem3921009 _99911 A a x b h1 h0). Qed.
Lemma lem3921011 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : term1228 _99911 A a x b.
Proof. exact (fun h0 : @FINITE A b => @lem3921010 _99911 A a x b h0). Qed.
Lemma lem3921016 {_99911 A : Type'} (x : A) (b : A -> Prop) : term1232 _99911 A x b.
Proof. exact (fun a : A -> Prop => @lem3921011 _99911 A a x b). Qed.
Lemma lem3921021 {_99911 A : Type'} (b : A -> Prop) : term1236 _99911 A b.
Proof. exact (fun x : A => @lem3921016 _99911 A x b). Qed.
Lemma lem3921026 {_99911 A : Type'} : term1240 _99911 A.
Proof. exact (fun b : A -> Prop => @lem3921021 _99911 A b). Qed.
Lemma lem3921027 {_99911 A : Type'} : term1239 _99911 A.
Proof. exact (EQ_MP (@lem3919394 _99911 A) (@lem3921026 _99911 A)). Qed.
Lemma lem3921028 {_99911 A : Type'} (b : A -> Prop) : term1416 _99911 A b.
Proof. exact (@lem3921027 _99911 A b). Qed.
Lemma lem3921029 {_99911 A : Type'} (b : A -> Prop) : (term1416 _99911 A b) = (term1235 _99911 A b).
Proof. exact (eq_refl (term1416 _99911 A b)). Qed.
Lemma lem3921030 {_99911 A : Type'} (b : A -> Prop) : term1235 _99911 A b.
Proof. exact (EQ_MP (@lem3921029 _99911 A b) (@lem3921028 _99911 A b)). Qed.
Lemma lem3921031 {_99911 A : Type'} (b : A -> Prop) (x : A) : term1417 _99911 A b x.
Proof. exact (@lem3921030 _99911 A b x). Qed.
Lemma lem3921032 {_99911 A : Type'} (x : A) (b : A -> Prop) : (term1417 _99911 A b x) = (term1231 _99911 A x b).
Proof. exact (eq_refl (term1417 _99911 A b x)). Qed.
Lemma lem3921033 {_99911 A : Type'} (x : A) (b : A -> Prop) : term1231 _99911 A x b.
Proof. exact (EQ_MP (@lem3921032 _99911 A x b) (@lem3921031 _99911 A b x)). Qed.
Lemma lem3921034 {_99911 A : Type'} (x : A) (b : A -> Prop) (a : A -> Prop) : term1418 _99911 A x b a.
Proof. exact (@lem3921033 _99911 A x b a). Qed.
Lemma lem3921035 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : (term1418 _99911 A x b a) = (term1202 _99911 A a x b).
Proof. exact (eq_refl (term1418 _99911 A x b a)). Qed.
Lemma lem3921036 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : term1202 _99911 A a x b.
Proof. exact (EQ_MP (@lem3921035 _99911 A a x b) (@lem3921034 _99911 A x b a)). Qed.
Lemma lem3921038 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) : term1202 _99911 A a x b.
Proof. exact (@lem3919108 _99911 A a x b (@lem3921036 _99911 A a x b)). Qed.
Lemma lem3921039 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) : term1225 _99911 A a x b.
Proof. exact (@lem3921038 _99911 A a x b (@lem3918926 A b h1)). Qed.
Lemma lem3921040 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : @IN A x b) : term1223 _99911 A a x b.
Proof. exact (@lem3921039 _99911 A a x b h1 (@lem3918931 A x b h2)). Qed.
Lemma lem3921041 {_99911 A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) : term1220 _99911 A a x b.
Proof. exact (@lem3921040 _99911 A a x b h1 h3 (@lem3918933 A x a h2)). Qed.
Lemma lem3921042 {_99911 A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1217 _99911 A b.
Proof. exact (@lem3921041 _99911 A a x b h1 h2 h3 (@lem3918932 A a b x h4)). Qed.
Lemma lem3921043 {_99911 A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) (h5 : term658 A a b x) : term1214 _99911 A.
Proof. exact (@lem3921042 _99911 A a b x h1 h2 h4 h5 (@lem3919085 A b h3)). Qed.
Lemma lem3921044 {_99911 A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) (h5 : term658 A a b x) : term1212 _99911 A.
Proof. exact (@lem3921043 _99911 A a b x h1 h2 h3 h4 h5 (@lem3919090 _99911)). Qed.
Lemma lem3921045 {_99911 A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) (h5 : term658 A a b x) : term1209 _99911 A.
Proof. exact (@lem3921044 _99911 A a b x h1 h2 h3 h4 h5 (@lem3919088 A)). Qed.
Lemma lem3921046 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) (h5 : term658 A a b x) : term1206 A.
Proof. exact (@lem3921045 Prop A a b x h1 h2 h3 h4 h5 (@lem3854502 Prop)). Qed.
Lemma lem3921047 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) (h5 : term658 A a b x) : False.
Proof. exact (@lem3921046 A a b x h1 h2 h3 h4 h5 (@lem3919086 A)). Qed.
Lemma lem3921048 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) (h5 : term658 A a b x) : ((@CARD A b) = (NUMERAL 0)) = False.
Proof. exact (prop_ext (fun h6 : (@CARD A b) = (NUMERAL 0) => @lem3921047 A a b x h1 h2 h3 h4 h5) (fun h6 : False => @lem3919085 A b h3)). Qed.
Lemma lem3921049 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : (@CARD A b) = (NUMERAL 0)) (h4 : @IN A x b) (h5 : term658 A a b x) : False.
Proof. exact (EQ_MP (@lem3921048 A a b x h1 h2 h3 h4 h5) (@lem3919085 A b h3)). Qed.
Lemma lem3921050 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1419 A b.
Proof. exact (fun h0 : (@CARD A b) = (NUMERAL 0) => @lem3921049 A a b x h1 h2 h0 h3 h4). Qed.
Lemma lem3921051 {A : Type'} (b : A -> Prop) : (term1419 A b) = (term1199 A b).
Proof. exact (@lem69 ((@CARD A b) = (NUMERAL 0))). Qed.
Lemma lem3921052 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1199 A b.
Proof. exact (EQ_MP (@lem3921051 A b) (@lem3921050 A a b x h1 h2 h3 h4)). Qed.
Lemma lem3921053 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1166 A x b.
Proof. exact (EQ_MP (@lem3919084 A x b h1 h3) (@lem3921052 A a b x h1 h2 h3 h4)). Qed.
Lemma lem3921054 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1167 A a x b.
Proof. exact (EQ_MP (@lem3919001 A a b x h1 h4) (@lem3921053 A a b x h1 h2 h3 h4)). Qed.
Lemma lem3921055 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1420 A a b.
Proof. exact (ex_intro (term1421 A a b) (term1173 A b x) (@lem3921054 A a b x h1 h2 h3 h4)). Qed.
Lemma lem3921056 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1146 A a b.
Proof. exact (@lem3918936 A a b (@lem3921055 A a b x h1 h2 h3 h4)). Qed.
Lemma lem3921057 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term664 A a b x) : term661 A a b x.
Proof. exact (proj2 (@lem3918929 A a b x h1)). Qed.
Lemma lem3921058 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term664 A a b x) : @IN A x b.
Proof. exact (proj1 (@lem3918929 A a b x h1)). Qed.
Lemma lem3921059 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term661 A a b x) : term658 A a b x.
Proof. exact (proj2 (@lem3918930 A a b x h1)). Qed.
Lemma lem3921060 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : term661 A a b x) : term687 A x a.
Proof. exact (proj1 (@lem3918930 A a b x h1)). Qed.
Lemma lem3921061 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : (term658 A a b x) = (term1146 A a b).
Proof. exact (prop_ext (fun h5 : term658 A a b x => @lem3921056 A a b x h1 h2 h3 h4) (fun h5 : term1146 A a b => @lem3918932 A a b x h4)). Qed.
Lemma lem3921062 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921061 A a b x h1 h2 h3 h4) (@lem3918932 A a b x h4)). Qed.
Lemma lem3921063 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : (term687 A x a) = (term1146 A a b).
Proof. exact (prop_ext (fun h5 : term687 A x a => @lem3921062 A a b x h1 h2 h3 h4) (fun h5 : term1146 A a b => @lem3918933 A x a h2)). Qed.
Lemma lem3921064 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : @IN A x b) (h4 : term658 A a b x) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921063 A a b x h1 h2 h3 h4) (@lem3918933 A x a h2)). Qed.
Lemma lem3921065 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : term661 A a b x) (h4 : @IN A x b) : (term658 A a b x) = (term1146 A a b).
Proof. exact (prop_ext (fun h5 : term658 A a b x => @lem3921064 A a b x h1 h2 h4 h5) (fun h5 : term1146 A a b => @lem3921059 A a b x h3)). Qed.
Lemma lem3921066 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term687 A x a) (h3 : term661 A a b x) (h4 : @IN A x b) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921065 A a x b h1 h2 h3 h4) (@lem3921059 A a b x h3)). Qed.
Lemma lem3921067 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term661 A a b x) (h3 : @IN A x b) : (term687 A x a) = (term1146 A a b).
Proof. exact (prop_ext (fun h4 : term687 A x a => @lem3921066 A a x b h1 h4 h2 h3) (fun h4 : term1146 A a b => @lem3921060 A a b x h2)). Qed.
Lemma lem3921068 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term661 A a b x) (h3 : @IN A x b) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921067 A a x b h1 h2 h3) (@lem3921060 A a b x h2)). Qed.
Lemma lem3921069 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term661 A a b x) (h3 : @IN A x b) : (@IN A x b) = (term1146 A a b).
Proof. exact (prop_ext (fun h4 : @IN A x b => @lem3921068 A a x b h1 h2 h3) (fun h4 : term1146 A a b => @lem3918931 A x b h3)). Qed.
Lemma lem3921070 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term661 A a b x) (h3 : @IN A x b) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921069 A a x b h1 h2 h3) (@lem3918931 A x b h3)). Qed.
Lemma lem3921071 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term664 A a b x) (h3 : @IN A x b) : (term661 A a b x) = (term1146 A a b).
Proof. exact (prop_ext (fun h4 : term661 A a b x => @lem3921070 A a x b h1 h4 h3) (fun h4 : term1146 A a b => @lem3921057 A a b x h2)). Qed.
Lemma lem3921072 {A : Type'} (a : A -> Prop) (x : A) (b : A -> Prop) (h1 : @FINITE A b) (h2 : term664 A a b x) (h3 : @IN A x b) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921071 A a x b h1 h2 h3) (@lem3921057 A a b x h2)). Qed.
Lemma lem3921073 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term664 A a b x) : (@IN A x b) = (term1146 A a b).
Proof. exact (prop_ext (fun h3 : @IN A x b => @lem3921072 A a x b h1 h2 h3) (fun h3 : term1146 A a b => @lem3921058 A a b x h2)). Qed.
Lemma lem3921074 {A : Type'} (a : A -> Prop) (b : A -> Prop) (x : A) (h1 : @FINITE A b) (h2 : term664 A a b x) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921073 A a b x h1 h2) (@lem3921058 A a b x h2)). Qed.
Lemma lem3921075 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term668 A a b) (h2 : @FINITE A b) : term1146 A a b.
Proof. exact (ex_elim (@lem3918928 A a b h1) (fun x : A => fun h0 : term666 A a b x => @lem3921074 A a b x h2 h0)). Qed.
Lemma lem3921076 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term1422 A a b.
Proof. exact (fun h0 : term668 A a b => @lem3921075 A a b h0 h1). Qed.
Lemma lem3921077 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1143 A a b) : @FINITE A b.
Proof. exact (proj2 (@lem3918925 A a b h1)). Qed.
Lemma lem3921078 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1143 A a b) : term668 A a b.
Proof. exact (proj1 (@lem3918925 A a b h1)). Qed.
Lemma lem3921079 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : (@FINITE A b) = (term1422 A a b).
Proof. exact (prop_ext (fun h2 : @FINITE A b => @lem3921076 A a b h1) (fun h2 : term1422 A a b => @lem3918926 A b h1)). Qed.
Lemma lem3921080 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : @FINITE A b) : term1422 A a b.
Proof. exact (EQ_MP (@lem3921079 A a b h1) (@lem3918926 A b h1)). Qed.
Lemma lem3921081 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term668 A a b) (h2 : @FINITE A b) : term1146 A a b.
Proof. exact (@lem3921080 A a b h2 (@lem3918927 A a b h1)). Qed.
Lemma lem3921082 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term668 A a b) (h2 : term1143 A a b) : (@FINITE A b) = (term1146 A a b).
Proof. exact (prop_ext (fun h3 : @FINITE A b => @lem3921081 A a b h1 h3) (fun h3 : term1146 A a b => @lem3921077 A a b h2)). Qed.
Lemma lem3921083 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term668 A a b) (h2 : term1143 A a b) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921082 A a b h1 h2) (@lem3921077 A a b h2)). Qed.
Lemma lem3921084 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1143 A a b) : (term668 A a b) = (term1146 A a b).
Proof. exact (prop_ext (fun h2 : term668 A a b => @lem3921083 A a b h2 h1) (fun h2 : term1146 A a b => @lem3921078 A a b h1)). Qed.
Lemma lem3921085 {A : Type'} (a : A -> Prop) (b : A -> Prop) (h1 : term1143 A a b) : term1146 A a b.
Proof. exact (EQ_MP (@lem3921084 A a b h1) (@lem3921078 A a b h1)). Qed.
Lemma lem3921086 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term1148 A a b.
Proof. exact (fun h0 : term1143 A a b => @lem3921085 A a b h0). Qed.
Lemma lem3921087 {A : Type'} (a : A -> Prop) (b : A -> Prop) : term1147 A a b.
Proof. exact (EQ_MP (@lem3918924 A a b) (@lem3921086 A a b)). Qed.
Lemma lem3921092 {A : Type'} (a : A -> Prop) : term1423 A a.
Proof. exact (fun b : A -> Prop => @lem3921087 A a b). Qed.
Lemma lem3921097 {A : Type'} : term1424 A.
Proof. exact (fun a : A -> Prop => @lem3921092 A a). Qed.
